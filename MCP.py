import os
import json
import re
import subprocess
import sys
import time
from pathlib import Path
import PIL.Image
import PIL.ImageOps
from google import genai
from mcp.server.fastmcp import FastMCP  # type: ignore[import-not-found]


def load_dotenv_file(path: str = ".env") -> None:
    if not os.path.exists(path):
        return
    try:
        with open(path, "r", encoding="utf-8") as f:
            for line in f:
                stripped = line.strip()
                if not stripped or stripped.startswith("#"):
                    continue
                if stripped.startswith("export "):
                    stripped = stripped[len("export "):].strip()
                if "=" not in stripped:
                    continue
                key, value = stripped.split("=", 1)
                key = key.strip()
                if not key:
                    continue
                value = value.strip().strip('"').strip("'")
                os.environ.setdefault(key, value)
    except OSError:
        return


load_dotenv_file()

# ==========================================
# 1. 初始化 FastMCP 伺服器與 Gemini 客戶端
# ==========================================
# 建立一個名為 Airplane VLM 的 MCP Server
mcp = FastMCP("Airplane_VLM_Server")

# 透過環境變數載入 API Key，避免硬編碼外流
GOOGLE_API_KEY = os.environ.get("GEMINI_API_KEY") or os.environ.get("GOOGLE_API_KEY")
if not GOOGLE_API_KEY:
    raise EnvironmentError("Missing GEMINI_API_KEY/GOOGLE_API_KEY. Please set one of them before running Airplane_MCP.py")
client = genai.Client(api_key=GOOGLE_API_KEY)
VLM_MAX_IMAGE_EDGE = int(os.environ.get("VLM_MAX_IMAGE_EDGE", "1024"))
VLM_MODEL_PRIMARY = os.environ.get("VLM_MODEL_PRIMARY", "gemini-2.5-flash").strip() or "gemini-2.5-flash"
VLM_MODEL_BACKUP = os.environ.get("VLM_MODEL_BACKUP", "gemini-3-flash").strip() or "gemini-3-flash"
VLM_RETRY_ATTEMPTS = max(1, int(os.environ.get("VLM_RETRY_ATTEMPTS", "4")))
VLM_RETRY_BASE_SECONDS = float(os.environ.get("VLM_RETRY_BASE_SECONDS", "1.0"))
VLM_RETRY_MAX_SECONDS = float(os.environ.get("VLM_RETRY_MAX_SECONDS", "8.0"))
# Temporarily hard-disable OCR in MCP to avoid Paddle native crashes (SIGSEGV)
# causing repeated MCP transport failures.
OCR_ENABLED = False
OCR_YOLO_WEIGHTS = os.environ.get("OCR_YOLO_WEIGHTS", "")
OCR_PADDING_RATIO = float(os.environ.get("OCR_PADDING_RATIO", "0.08"))
OCR_SUBPROCESS_ENABLED = os.environ.get("OCR_SUBPROCESS_ENABLED", "1") == "1"
OCR_SUBPROCESS_TIMEOUT_SECONDS = int(os.environ.get("OCR_SUBPROCESS_TIMEOUT_SECONDS", "45"))
OCR_PYTHON_EXECUTABLE = os.environ.get("OCR_PYTHON_EXECUTABLE", "").strip()
PROJECT_ROOT = Path(__file__).resolve().parent
OCR_PIPELINE_SCRIPT = PROJECT_ROOT / "ocr_pipeline.py"

# ==========================================
# 2. 定義 MCP Tool (Agent 會看到並呼叫這個工具)
# ==========================================
DEFAULT_PROMPT_TEXT = """
You are a professional aviation photography analysis assistant. Please observe this airplane photo and provide the following information as much as possible:
1. Registration Number: Usually located under the tail. If it's unclear, please provide any partial string you can barely recognize.
2. Airline/Livery: Please identify this based on the text on the fuselage or the tail logo.
3. Aircraft Type: Infer the base aircraft type (e.g., Boeing 777, Airbus A320, etc.) through engine features, landing gear, and fuselage shape.

Please return the result STRICTLY in JSON format as follows:
{
    "callsign": "string or null",
    "registration_number": "string or null",
    "airline": "airline name",
    "aircraft_type": "aircraft type"
}
"""


def _clean_value(value: object) -> str:
    if value is None:
        return ""
    return str(value).strip()


def _try_parse_json_dict(raw_text: str) -> dict | None:
    raw = _clean_value(raw_text)
    if not raw:
        return None

    try:
        parsed = json.loads(raw)
        if isinstance(parsed, dict):
            return parsed
    except json.JSONDecodeError:
        pass

    no_fence = re.sub(r"```(?:json)?", "", raw, flags=re.IGNORECASE).replace("```", "").strip()
    if no_fence:
        try:
            parsed = json.loads(no_fence)
            if isinstance(parsed, dict):
                return parsed
        except json.JSONDecodeError:
            pass

    match = re.search(r"\{.*\}", no_fence or raw, re.DOTALL)
    if match:
        extracted = match.group(0).strip()
        try:
            parsed = json.loads(extracted)
            if isinstance(parsed, dict):
                return parsed
        except json.JSONDecodeError:
            pass

    return None


def _build_prompt_with_ocr_hint(prompt_text: str, ocr_registration: str | None) -> str:
    reg = _clean_value(ocr_registration)
    if not reg:
        return prompt_text

    return (
        f"{prompt_text.strip()}\n\n"
        "Additional hint from local OCR subsystem:\n"
        f"- Candidate registration from fuselage text: {reg}\n"
        "- This OCR hint can be noisy; if visual evidence strongly conflicts, ignore it.\n"
    )


def _is_quota_error(error_text: str) -> bool:
    normalized = error_text.upper()
    return "RESOURCE_EXHAUSTED" in normalized or "QUOTA" in normalized or "429" in normalized


def _is_server_side_error(error_text: str) -> bool:
    normalized = error_text.upper()
    server_tokens = (
        " 500",
        " 502",
        " 503",
        " 504",
        "UNAVAILABLE",
        "INTERNAL",
        "SERVICE UNAVAILABLE",
        "DEADLINE_EXCEEDED",
        "SERVER ERROR",
        "MODEL IS CURRENTLY EXPERIENCING HIGH DEMAND",
    )
    return any(token in normalized for token in server_tokens)


def _retry_backoff_seconds(retry_index: int) -> float:
    delay = VLM_RETRY_BASE_SECONDS * (2 ** retry_index)
    return min(delay, VLM_RETRY_MAX_SECONDS)


def _cross_vlm_model_for_retry(retry_index: int) -> str:
    if not VLM_MODEL_BACKUP or VLM_MODEL_BACKUP == VLM_MODEL_PRIMARY:
        return VLM_MODEL_PRIMARY
    return VLM_MODEL_PRIMARY if retry_index % 2 == 0 else VLM_MODEL_BACKUP


def _generate_content_with_cross_fallback(contents: list[object]) -> tuple[object, str]:
    last_error: Exception | None = None

    for attempt in range(1, VLM_RETRY_ATTEMPTS + 1):
        model_name = _cross_vlm_model_for_retry(attempt - 1)
        try:
            response = client.models.generate_content(model=model_name, contents=contents)
            return response, model_name
        except Exception as exc:
            last_error = exc
            error_text = _clean_value(exc)
            retryable = _is_server_side_error(error_text) or _is_quota_error(error_text)
            if retryable and attempt < VLM_RETRY_ATTEMPTS:
                wait_seconds = _retry_backoff_seconds(attempt - 1)
                next_model = _cross_vlm_model_for_retry(attempt)
                print(
                    f"[VLM retry] model={model_name} attempt={attempt}/{VLM_RETRY_ATTEMPTS} "
                    f"cross-fallback->{next_model} backoff={wait_seconds:.1f}s error={error_text}"
                )
                time.sleep(wait_seconds)
                continue
            raise

    raise RuntimeError(str(last_error) if last_error else "VLM request failed")


def _extract_registration_with_local_ocr(
    image_path: str,
    yolo_weights_path: str | None = None,
    padding_ratio: float | None = None,
) -> tuple[str | None, str | None]:
    """
    Returns:
        (registration_number, error_message)
    """
    def _resolve_ocr_python_executable() -> str:
        if OCR_PYTHON_EXECUTABLE:
            override = Path(OCR_PYTHON_EXECUTABLE)
            if override.exists():
                return str(override)

        preferred = [
            PROJECT_ROOT / ".venv312/bin/python",
            PROJECT_ROOT / ".venv/bin/python",
        ]
        for candidate in preferred:
            if candidate.exists():
                return str(candidate)

        return sys.executable

    weights = _clean_value(yolo_weights_path) or OCR_YOLO_WEIGHTS
    pad = OCR_PADDING_RATIO if padding_ratio is None else padding_ratio

    if OCR_SUBPROCESS_ENABLED:
        if not OCR_PIPELINE_SCRIPT.exists():
            return None, f"OCR script not found: {OCR_PIPELINE_SCRIPT}"

        command = [
            _resolve_ocr_python_executable(),
            str(OCR_PIPELINE_SCRIPT),
            "--image",
            image_path,
            "--padding",
            str(pad),
        ]
        if weights:
            command.extend(["--weights", weights])

        sub_env = os.environ.copy()
        sub_env.setdefault("OMP_NUM_THREADS", "1")
        sub_env.setdefault("OPENBLAS_NUM_THREADS", "1")
        sub_env.setdefault("MKL_NUM_THREADS", "1")
        sub_env.setdefault("NUMEXPR_NUM_THREADS", "1")
        sub_env.setdefault("VECLIB_MAXIMUM_THREADS", "1")

        try:
            completed = subprocess.run(
                command,
                capture_output=True,
                text=True,
                timeout=OCR_SUBPROCESS_TIMEOUT_SECONDS,
                cwd=str(PROJECT_ROOT),
                env=sub_env,
            )
        except subprocess.TimeoutExpired:
            return None, f"OCR subprocess timeout after {OCR_SUBPROCESS_TIMEOUT_SECONDS}s"
        except Exception as e:
            return None, f"OCR subprocess launch failed: {e}"

        combined_output = "\n".join(
            part.strip() for part in [completed.stdout or "", completed.stderr or ""] if part and part.strip()
        )
        if completed.returncode != 0:
            if completed.returncode < 0:
                signal_number = -completed.returncode
                return None, f"OCR subprocess crashed with signal {signal_number}"
            error_lines = (completed.stderr or "").splitlines()
            tail = " | ".join(error_lines[-3:]).strip()
            if tail:
                return None, f"OCR subprocess exited with code {completed.returncode}: {tail}"
            return None, f"OCR subprocess exited with code {completed.returncode}"

        for raw_line in reversed(combined_output.splitlines()):
            line = raw_line.strip()
            if not line.startswith("Registration Mark:"):
                continue
            value = _clean_value(line.split(":", 1)[1]).upper().replace("*", "")
            if value and value != "NONE":
                return value, None
            return None, "OCR found no registration text"

        return None, "OCR subprocess returned no registration marker"

    try:
        from OCR import extract_registration_mark
    except Exception as e:
        return None, f"OCR module import failed: {e}"

    try:
        reg = extract_registration_mark(
            image_path=image_path,
            yolo_weights_path=weights,
            padding_ratio=pad,
        )
        if reg:
            return reg, None
        return None, "OCR found no registration text"
    except Exception as e:
        return None, str(e)


@mcp.tool()
def extract_registration_ocr(
    image_path: str,
    yolo_weights_path: str | None = None,
    padding_ratio: float = OCR_PADDING_RATIO,
) -> str:
    """
    Run local YOLO+PaddleOCR pipeline and return registration text only.
    """
    if not os.path.exists(image_path):
        return json.dumps({"error": f"找不到圖片檔案：{image_path}"})

    if not OCR_ENABLED:
        return json.dumps({"error": "OCR is disabled by OCR_ENABLED=0"})

    reg, error = _extract_registration_with_local_ocr(
        image_path=image_path,
        yolo_weights_path=yolo_weights_path,
        padding_ratio=padding_ratio,
    )

    if reg:
        return json.dumps(
            {
                "registration_number": reg,
                "source": "local_ocr",
            },
            ensure_ascii=False,
        )

    return json.dumps(
        {
            "registration_number": None,
            "warning": error or "OCR found no text",
            "source": "local_ocr",
        },
        ensure_ascii=False,
    )


@mcp.tool()
def analyze_airplane_image(image_path: str, prompt_text: str | None = None) -> str:
    """
    Analyze an airplane photo to extract its registration number, airline, and aircraft type.
    Agent 應該在無法從雷達資料確認飛機身分時(Route B)，傳入照片的路徑來呼叫此工具。
    
    Args:
        image_path: 本地端飛機照片的檔案路徑 (例如: "test/294A9723.jpg")
        
    Returns:
        回傳 JSON 格式的字串，包含 registration_number, airline, aircraft_type。
    """
    
    # 檢查檔案是否存在
    if not os.path.exists(image_path):
        return json.dumps({"error": f"找不到圖片檔案：{image_path}"})

    active_prompt = (prompt_text or "").strip() or DEFAULT_PROMPT_TEXT
    ocr_registration: str | None = None
    ocr_warning: str | None = None

    if OCR_ENABLED:
        ocr_registration, ocr_warning = _extract_registration_with_local_ocr(image_path)
        active_prompt = _build_prompt_with_ocr_hint(active_prompt, ocr_registration)

    def _prepare_vlm_image(path: str) -> PIL.Image.Image:
        with PIL.Image.open(path) as src:
            oriented = PIL.ImageOps.exif_transpose(src)
            prepared = oriented.copy()

        if VLM_MAX_IMAGE_EDGE > 0:
            resampling = getattr(PIL.Image, "Resampling", PIL.Image)
            prepared.thumbnail((VLM_MAX_IMAGE_EDGE, VLM_MAX_IMAGE_EDGE), resampling.LANCZOS)

        return prepared
    
    try:
        # 載入圖片並呼叫 Gemini 2.0 Flash
        img = _prepare_vlm_image(image_path)
        try:
            response, used_model = _generate_content_with_cross_fallback([active_prompt, img])
        finally:
            try:
                img.close()
            except Exception:
                pass
        
        # 清理並回傳純 JSON 字串給 Agent
        result_text = response.text.strip().removeprefix('```json').removesuffix('```').strip()
        parsed = _try_parse_json_dict(result_text)

        if isinstance(parsed, dict):
            if ocr_registration:
                parsed["ocr_registration_number"] = ocr_registration
                reg = _clean_value(parsed.get("registration_number"))
                raw_reg = _clean_value(parsed.get("raw_registration"))
                if not reg and not raw_reg:
                    parsed["registration_number"] = ocr_registration

            if ocr_warning and not ocr_registration:
                parsed["ocr_warning"] = ocr_warning

            parsed["vlm_model"] = used_model

            return json.dumps(parsed, ensure_ascii=False)

        if ocr_registration:
            return json.dumps(
                {
                    "callsign": None,
                    "registration_number": ocr_registration,
                    "airline": None,
                    "aircraft_type": None,
                    "ocr_registration_number": ocr_registration,
                    "warning": "VLM returned non-JSON payload; fallback to OCR registration only",
                },
                ensure_ascii=False,
            )

        return result_text
        
    except Exception as e:
        return json.dumps({"error": str(e)})

# ==========================================
# 3. 啟動伺服器 (使用標準輸入輸出 Stdio 模式)
# ==========================================
if __name__ == "__main__":
    # MCP Server 預設以 stdio 方式執行，方便外層的 Agent 直接串接溝通
    mcp.run()