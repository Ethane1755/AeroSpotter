from __future__ import annotations

# Main orchestration CLI for radar, OCR, and VLM-based aircraft identification.
import asyncio
import concurrent.futures
import csv
import gzip
import hashlib
import importlib
import json
import math
import os
import re
import sys
import threading
import time
import webbrowser
from dataclasses import dataclass
from datetime import datetime, timedelta, timezone
from html import unescape
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path

import exifread
import piexif
import piexif.helper
import questionary
from rich.console import Console
from questionary import Style
from timezonefinder import TimezoneFinder
from typing import Any
from zoneinfo import ZoneInfo

import requests
import typer

from OCR import extract_registration_marks
YOLO_WEIGHTS_PATH = os.environ.get("YOLO_WEIGHTS_PATH", "yolo_weights/best.pt")

def _load_dotenv_file(env_path: Path) -> None:
    if not env_path.exists():
        return

    try:
        for line in env_path.read_text(encoding="utf-8").splitlines():
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


def _get_gemini_api_key() -> str:
    return os.environ.get("GEMINI_API_KEY") or os.environ.get("GOOGLE_API_KEY") or ""


def _is_traffic_supported_python() -> bool:
    # traffic+pandas stack is not stable yet on bleeding-edge Python builds.
    return sys.version_info < (3, 13)


def _traffic_python_hint() -> str:
    current = f"{sys.version_info.major}.{sys.version_info.minor}"
    return f"目前 Python={current}；建議切換到 Python 3.12 後再啟用 traffic"


# Application setup and shared configuration.
app = typer.Typer(help="AeroSpotter CLI (Home Lab NAS Edition)")
console = Console()

_load_dotenv_file(Path(__file__).parent / ".env")

NAS_API_URL = "http://100.109.73.11:5000/api/adsb/bbox"
BUFFER_MINUTES = 5

AIRLINE_PREFIXES = {
}

AIRCRAFT_MODEL_MAP = {
    "A20N": "Airbus A320neo",
    "A21N": "Airbus A321neo",
    "A320": "Airbus A320-200",
    "A321": "Airbus A321-200",
    "A332": "Airbus A330-200",
    "A333": "Airbus A330-300",
    "A359": "Airbus A350-900",
    "A35K": "Airbus A350-1000",
    "B738": "Boeing 737-800",
    "B38M": "Boeing 737 MAX 8",
    "B77W": "Boeing 777-300ER",
    "B789": "Boeing 787-9",
    "B78X": "Boeing 787-10",
    "B744": "Boeing 747-400",
    "GLF4": "Gulfstream IV",
    "AT76": "ATR 72-600",
    "ZZZC": "Unknown Type (ZZZC)",
}

_EXTS = [".jpg", ".jpeg", ".png", ".cr2", ".nef", ".arw", ".dng", ".raf"]
SUPPORTED_EXTENSIONS = {ext.lower() for ext in _EXTS} | {ext.upper() for ext in _EXTS}
RAW_EXTENSIONS = {ext for ext in SUPPORTED_EXTENSIONS if ext.lower() not in [".jpg", ".jpeg", ".png"]}
_TIMEZONE_FINDER = TimezoneFinder(in_memory=True)

live_ac_cache = {}
known_hints_by_icao: dict[str, dict[str, str]] = {}
known_hints_by_callsign: dict[str, dict[str, str]] = {}
known_hints_by_reg: dict[str, dict[str, str]] = {}
traffic_db_cache_by_icao: dict[str, dict[str, str]] = {}
traffic_db_cache_by_reg: dict[str, dict[str, str]] = {}
traffic_db_missing: set[str] = set()
traffic_db_reg_missing: set[str] = set()
traffic_db_disabled = False
traffic_db_initialized = False
traffic_import_attempted = False
traffic_import_error: str | None = None
traffic_aircraft: Any | None = None
traffic_db_frame: Any | None = None
traffic_db_lock = threading.Lock()
local_db_cache_by_icao: dict[str, dict[str, str]] = {}
local_db_cache_by_reg: dict[str, dict[str, str]] = {}
local_db_missing: set[str] = set()
local_db_reg_missing: set[str] = set()
local_db_disabled = False
local_db_field_limit_set = False
local_db_lock = threading.Lock()
airline_map_loaded = False
airline_map_lock = threading.Lock()

TILE_CACHE_ROOT = Path.home() / ".cache" / "aerospotter" / "osm_tiles"
DB_DIR = Path(__file__).parent / "database"
AIRLINE_MAP_PATH = DB_DIR / "iata_airlines.csv"
LOCAL_DB_GZ_PATH = DB_DIR / "aircraft-database-complete-2025-08.csv.gz"
LOCAL_DB_CSV_FALLBACK_PATH = DB_DIR / "aircraft-database-complete-2025-08.csv"
LOG_DIR = Path(__file__).parent / "logs"
DECISION_LOG_PATH = LOG_DIR / "vlm_decision.log"
VLM_CACHE_PATH = LOG_DIR / "vlm_cache.json"
MCP_SERVER_SCRIPT = Path(__file__).parent / "MCP.py"
VLM_TOOL_NAME = "analyze_airplane_image"
VLM_MIN_SCORE = int(os.environ.get("VLM_MIN_SCORE", "4"))
VLM_SCORE_MARGIN = int(os.environ.get("VLM_SCORE_MARGIN", "2"))
VLM_MCP_TIMEOUT_SECONDS = int(os.environ.get("VLM_MCP_TIMEOUT_SECONDS", "20"))
VLM_DIRECT_TIMEOUT_SECONDS = int(os.environ.get("VLM_DIRECT_TIMEOUT_SECONDS", "60"))
VLM_DIRECT_TIMEOUT_GRACE_SECONDS = float(os.environ.get("VLM_DIRECT_TIMEOUT_GRACE_SECONDS", "8"))
VLM_MAX_IMAGE_EDGE = int(os.environ.get("VLM_MAX_IMAGE_EDGE", "1024"))
VLM_ALLOW_LOW_CONF_AIRLINE_EXACT = os.environ.get("VLM_ALLOW_LOW_CONF_AIRLINE_EXACT", "1") == "1"
VLM_SERVER_RETRY_ATTEMPTS = max(1, int(os.environ.get("VLM_SERVER_RETRY_ATTEMPTS", "3")))
VLM_SERVER_RETRY_BASE_SECONDS = float(os.environ.get("VLM_SERVER_RETRY_BASE_SECONDS", "1.0"))
VLM_SERVER_RETRY_MAX_SECONDS = float(os.environ.get("VLM_SERVER_RETRY_MAX_SECONDS", "8.0"))
VLM_MODEL_PRIMARY = os.environ.get("VLM_MODEL_PRIMARY", "gemini-2.5-flash").strip() or "gemini-2.5-flash"
VLM_MODEL_BACKUP = os.environ.get("VLM_MODEL_BACKUP", "gemini-3-flash").strip() or "gemini-3-flash"
VLM_PROMPT_TEXT = """
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

Rules:
- Output JSON only.
- Do not include any explanation.
- Do not wrap with markdown code fences.
- Your response must start with "{" and end with "}".
"""
UNKNOWN_TOKENS = {
    "",
    "N/A",
    "N/A (?)",
    "NONE",
    "NULL",
    "UNKNOWN",
    "UNKNOWN (?)",
    "NAN",
}
SUMMARY_PATTERN = re.compile(
    r"AeroSpotter:\\s*(?P<callsign>.*?)\\s*\\|\\s*Reg:\\s*(?P<reg>.*?)\\s*\\|\\s*Model:\\s*(?P<model>.*?)\\s*\\|\\s*Airline:\\s*(?P<owner>[^<\\r\\n]+)",
    re.IGNORECASE,
)

custom_style = Style([
    ('qmark', 'fg:#00ffff bold'),
    ('question', 'bold'),
    ('answer', 'fg:#00ff00 bold'),
    ('pointer', 'fg:#ff00ff bold'),
    ('highlighted', 'fg:#00ffff bold'),
    ('selected', 'fg:#cc5454'),
    ('instruction', 'fg:#888888 italic')
])


class _RetryableVLMServerError(Exception):
    pass


def _looks_like_taskgroup_wrapper(text: str) -> bool:
    normalized = _clean_value(text).lower()
    if not normalized:
        return False
    return "taskgroup" in normalized or "task group" in normalized


def _iter_nested_exceptions(error: BaseException) -> list[BaseException]:
    stack: list[BaseException] = [error]
    nested: list[BaseException] = []
    seen: set[int] = set()

    while stack:
        current = stack.pop()
        marker = id(current)
        if marker in seen:
            continue
        seen.add(marker)
        nested.append(current)

        group_items = getattr(current, "exceptions", None)
        if isinstance(group_items, (list, tuple)):
            for item in group_items:
                if isinstance(item, BaseException):
                    stack.append(item)

        cause = getattr(current, "__cause__", None)
        if isinstance(cause, BaseException):
            stack.append(cause)

        context = getattr(current, "__context__", None)
        if isinstance(context, BaseException):
            stack.append(context)

    return nested


def _extract_exception_summary(error: BaseException) -> str:
    # Python 3.11+ ExceptionGroup/TaskGroup errors often hide the real leaf error.
    specifics: list[str] = []
    generic_wrappers: list[str] = []

    for item in _iter_nested_exceptions(error):
        class_name = item.__class__.__name__
        message = _clean_value(str(item))

        if message:
            summary = f"{class_name}: {message}"
        else:
            summary = class_name

        if _looks_like_taskgroup_wrapper(message):
            generic_wrappers.append(summary)
            continue

        specifics.append(summary)

    picked = specifics if specifics else generic_wrappers
    if not picked:
        picked = [error.__class__.__name__]

    seen: set[str] = set()
    unique: list[str] = []
    for part in picked:
        if part in seen:
            continue
        seen.add(part)
        unique.append(part)
    return " | ".join(unique[:4])


def _is_taskgroup_exception(error: BaseException) -> bool:
    for item in _iter_nested_exceptions(error):
        if "exceptiongroup" in item.__class__.__name__.lower():
            return True
        if _looks_like_taskgroup_wrapper(str(item)):
            return True
    return False

# Data models used to carry image and location metadata.
@dataclass(slots=True)
class LocationContext:
    latitude: float
    longitude: float
    timezone_name: str
    source: str

@dataclass(slots=True)
class ExifMetadata:
    image_path: Path
    captured_at_local: datetime | None
    raw_datetime: str | None
    offset_time: str | None
    latitude: float | None
    longitude: float | None

    @property
    def has_gps(self) -> bool:
        return self.latitude is not None and self.longitude is not None

# Network lookups and candidate enrichment.

def _is_unknown(value: str | None) -> bool:
    normalized = _clean_value(value)
    if not normalized:
        return True
    return normalized.upper() in UNKNOWN_TOKENS


def _clean_value(value: str | None) -> str:
    if value is None:
        return ""

    cleaned = str(value).strip()
    while len(cleaned) >= 2 and cleaned[0] == cleaned[-1] and cleaned[0] in {"'", '"'}:
        cleaned = cleaned[1:-1].strip()
    return cleaned


def _normalize_icao(value: str | None) -> str:
    normalized = _clean_value(value).lower()
    if not normalized:
        return "N/A"
    return normalized if normalized else "N/A"


def _normalize_reg(value: str | None) -> str:
    cleaned = _clean_value(value)
    if not cleaned:
        return ""
    return cleaned.replace("*", "").strip().upper()


def _prefer_known(current: str, fallback: str | None) -> str:
    if _is_unknown(current) and not _is_unknown(fallback):
        return _clean_value(fallback)
    return current


def _merge_hint_values(reg: str, model: str, owner: str, hint: dict[str, str]) -> tuple[str, str, str]:
    """Apply one hint dict onto current values, keeping existing known fields."""
    reg = _prefer_known(reg, hint.get("reg"))
    model = _prefer_known(model, hint.get("model"))
    owner = _prefer_known(owner, hint.get("owner"))
    return reg, model, owner


def _normalize_compare_text(value: str | None) -> str:
    return re.sub(r"[^a-z0-9]", "", _clean_value(value).lower())


def _decision_log(message: str, image_path: Path | None = None, level: str = "INFO") -> None:
    timestamp = datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
    image_name = image_path.name if image_path else "-"
    normalized_level = level.upper()
    line = f"{timestamp} [{normalized_level}] [{image_name}] {message}"

    try:
        LOG_DIR.mkdir(parents=True, exist_ok=True)
        with DECISION_LOG_PATH.open("a", encoding="utf-8") as log_file:
            log_file.write(line + "\n")
    except OSError:
        pass

    style_by_level = {
        "DEBUG": "cyan",
        "INFO": "dim",
        "WARN": "yellow",
        "WARNING": "yellow",
        "ERROR": "bold red",
        "CRITICAL": "bold white on red",
    }
    style = style_by_level.get(normalized_level, "dim")
    console.print(f"  [{style}]{line}[/{style}]")


def _build_vlm_candidate_text(candidates: list[dict], max_items: int = 15) -> str:
    lines = ["當時空域有以下航班："]
    for candidate in candidates[:max_items]:
        callsign = _clean_value(str(candidate.get("callsign") or "N/A")) or "N/A"
        model = _clean_value(str(candidate.get("model") or "N/A")) or "N/A"
        owner = _clean_value(str(candidate.get("owner") or "N/A")) or "N/A"
        reg = _clean_value(str(candidate.get("reg") or "N/A")) or "N/A"
        lines.append(f"- {callsign} (機型: {model}, 航空: {owner}, 機身碼: {reg})")
    return "\n".join(lines)


def _build_vlm_prompt(candidates: list[dict] | None = None) -> str:
    if not candidates:
        return VLM_PROMPT_TEXT

    candidate_text = _build_vlm_candidate_text(candidates)
    return f"""
請幫我辨識這張照片裡的飛機。
請注意，這台飛機必定是下面名單中的其中一台，絕對不可猜名單以外的飛機。
{candidate_text}

請回傳 JSON，格式如下：
{{
    "status": "MATCH 或 NOT_IN_RADAR 或 BLURRY",
    "selected_callsign": "如果是 MATCH，填寫你選中的 callsign，否則填 null",
    "raw_registration": "肉眼讀到的機身碼，若看不清填 null",
    "reason": "簡短說明原因",
    "callsign": "與 selected_callsign 相同，若非 MATCH 則填 null",
    "registration_number": "與 raw_registration 相同，若看不清填 null",
  "airline": "airline name",
  "aircraft_type": "aircraft type"
}}

【最高指導原則 - 違反將導致系統崩潰】
- 絕對禁止輸出任何問候語、推理過程或解釋。
- 絕對禁止使用 ```json 或任何 Markdown 標記包裝。
- 回應必須直接從 {{ 開始，並以 }} 結束，除此之外不能有任何多餘字元。
""".strip()


def _build_vlm_cache_key(image_path: Path, prompt_text: str | None = None) -> str:
    try:
        stat = image_path.stat()
        base = f"{image_path.resolve()}::{stat.st_mtime_ns}:{stat.st_size}"
    except OSError:
        base = str(image_path)

    prompt_hash_source = prompt_text or ""
    prompt_hash = hashlib.sha256(prompt_hash_source.encode("utf-8")).hexdigest()[:16]
    return f"{base}::prompt={prompt_hash}"


def _read_vlm_cache() -> dict[str, dict[str, str]]:
    try:
        if not VLM_CACHE_PATH.exists():
            return {}
        loaded = json.loads(VLM_CACHE_PATH.read_text(encoding="utf-8"))
        if isinstance(loaded, dict):
            return loaded
    except (OSError, json.JSONDecodeError):
        pass
    return {}


def _write_vlm_cache(cache: dict[str, dict[str, str]]) -> None:
    try:
        LOG_DIR.mkdir(parents=True, exist_ok=True)
        VLM_CACHE_PATH.write_text(json.dumps(cache, ensure_ascii=True, indent=2), encoding="utf-8")
    except OSError:
        pass


def _get_cached_vlm_result(image_path: Path, prompt_text: str | None = None) -> dict[str, str] | None:
    cache = _read_vlm_cache()
    key = _build_vlm_cache_key(image_path, prompt_text)
    cached = cache.get(key)
    if isinstance(cached, dict):
        normalized = _normalize_vlm_result(cached)
        if normalized:
            _decision_log("use cached VLM result", image_path)
            return normalized
    return None


def _set_cached_vlm_result(
    image_path: Path,
    result: dict[str, str],
    source: str,
    prompt_text: str | None = None,
) -> None:
    cache = _read_vlm_cache()
    key = _build_vlm_cache_key(image_path, prompt_text)
    cache[key] = {
        "callsign": _clean_value(result.get("callsign")),
        "registration_number": _clean_value(result.get("registration_number")),
        "airline": _clean_value(result.get("airline")),
        "aircraft_type": _clean_value(result.get("aircraft_type")),
    }
    _write_vlm_cache(cache)
    _decision_log(f"cached VLM result source={source}", image_path)


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
    # retry_index is zero-based (0, 1, 2, ...)
    delay = VLM_SERVER_RETRY_BASE_SECONDS * (2 ** retry_index)
    return min(delay, VLM_SERVER_RETRY_MAX_SECONDS)


def _cross_vlm_model_for_retry(retry_index: int) -> str:
    if not VLM_MODEL_BACKUP or VLM_MODEL_BACKUP == VLM_MODEL_PRIMARY:
        return VLM_MODEL_PRIMARY
    return VLM_MODEL_PRIMARY if retry_index % 2 == 0 else VLM_MODEL_BACKUP


def _try_parse_json_dict(text: str) -> dict[str, Any] | None:
    try:
        parsed = json.loads(text)
    except (TypeError, json.JSONDecodeError):
        return None
    if isinstance(parsed, dict):
        return parsed
    return None


def _parse_vlm_json_payload(raw_text: str, image_path: Path, source: str) -> dict[str, Any] | None:
    raw = _clean_value(raw_text)
    if not raw:
        return None

    direct = _try_parse_json_dict(raw)
    if direct:
        return direct

    no_fence = re.sub(r"```(?:json)?", "", raw, flags=re.IGNORECASE).replace("```", "").strip()
    if no_fence and no_fence != raw:
        direct_no_fence = _try_parse_json_dict(no_fence)
        if direct_no_fence:
            _decision_log(f"{source} payload recovered by removing markdown fences", image_path)
            return direct_no_fence

    match = re.search(r"\{.*\}", no_fence or raw, re.DOTALL)
    if match:
        extracted = match.group(0).strip()
        parsed_regex = _try_parse_json_dict(extracted)
        if parsed_regex:
            _decision_log(f"{source} payload recovered by regex JSON extraction", image_path)
            return parsed_regex

    decoder = json.JSONDecoder()
    scan_text = no_fence or raw
    for index, char in enumerate(scan_text):
        if char != "{":
            continue
        try:
            parsed, _ = decoder.raw_decode(scan_text[index:])
        except json.JSONDecodeError:
            continue
        if isinstance(parsed, dict):
            _decision_log(f"{source} payload recovered by JSON decoder scan", image_path)
            return parsed

    return None


def _normalize_vlm_result(parsed: dict[str, Any]) -> dict[str, str] | None:
    if not isinstance(parsed, dict):
        return None

    if parsed.get("error"):
        return None

    status = _clean_value(parsed.get("status")).upper()
    selected_callsign = _clean_value(parsed.get("selected_callsign"))
    callsign = _clean_value(parsed.get("callsign")) or selected_callsign
    if status and status != "MATCH" and not _clean_value(parsed.get("callsign")):
        callsign = ""

    registration_number = _clean_value(parsed.get("registration_number"))
    raw_registration = _clean_value(parsed.get("raw_registration"))
    if not registration_number:
        registration_number = raw_registration

    return {
        "callsign": callsign,
        "registration_number": registration_number,
        "airline": _clean_value(parsed.get("airline")),
        "aircraft_type": _clean_value(parsed.get("aircraft_type")),
    }


def _extract_aircraft_family(value: str | None) -> str:
    text = _clean_value(value).upper()
    if not text:
        return ""

    # A320 / A321 / A330 / A350 ...
    m = re.search(r"\bA\s*(\d{3,4})\b", text)
    if m:
        return f"A{m.group(1)[:3]}"

    # B737 / B747 / B777 / B787 ...
    m = re.search(r"\bB\s*(\d{3,4})\b", text)
    if m:
        return f"B{m.group(1)[:3]}"

    # Boeing 747-400 / Airbus A320neo styles without leading A/B token.
    m = re.search(r"\bBOEING\s*(\d{3,4})\b", text)
    if m:
        return f"B{m.group(1)[:3]}"

    m = re.search(r"\bAIRBUS\s*A?\s*(\d{3,4})\b", text)
    if m:
        return f"A{m.group(1)[:3]}"

    return ""


def _prepare_vlm_image_for_model(image_path: Path) -> Any:
    import PIL.Image  # type: ignore[import-not-found]
    import PIL.ImageOps  # type: ignore[import-not-found]

    with PIL.Image.open(image_path) as src:
        oriented = PIL.ImageOps.exif_transpose(src)
        prepared = oriented.copy()

    if VLM_MAX_IMAGE_EDGE > 0:
        original_size = prepared.size
        longest = max(original_size)
        if longest > VLM_MAX_IMAGE_EDGE:
            resampling = getattr(PIL.Image, "Resampling", PIL.Image)
            prepared.thumbnail((VLM_MAX_IMAGE_EDGE, VLM_MAX_IMAGE_EDGE), resampling.LANCZOS)
            _decision_log(
                f"VLM image downscaled {original_size[0]}x{original_size[1]} -> {prepared.width}x{prepared.height}",
                image_path,
            )

    return prepared


def _safe_call_direct_vlm(image_path: Path, candidates: list[dict] | None = None) -> dict[str, str] | None:
    _decision_log("start direct Gemini VLM call (MCP fallback)", image_path)
    vlm_prompt = _build_vlm_prompt(candidates)
    worker_cancelled = threading.Event()

    cached = _get_cached_vlm_result(image_path, vlm_prompt)
    if cached:
        return cached

    api_key = _get_gemini_api_key()
    if not api_key:
        _decision_log("direct VLM skipped: missing GEMINI_API_KEY/GOOGLE_API_KEY", image_path, level="WARN")
        return None

    try:
        import PIL.Image  # type: ignore[import-not-found]
        from google import genai  # type: ignore[import-not-found]
    except Exception:
        _decision_log("direct VLM skipped: missing google-genai or Pillow", image_path, level="WARN")
        return None

    def _run_direct_call() -> dict[str, str] | None:
        for attempt in range(1, VLM_SERVER_RETRY_ATTEMPTS + 1):
            if worker_cancelled.is_set():
                return None

            try:
                img = _prepare_vlm_image_for_model(image_path)
                client = genai.Client(api_key=api_key)
                model_name = _cross_vlm_model_for_retry(attempt - 1)
                try:
                    response = client.models.generate_content(
                        model=model_name,
                        contents=[vlm_prompt, img],
                    )
                finally:
                    try:
                        img.close()
                    except Exception:
                        pass

                if worker_cancelled.is_set():
                    return None

                result_text = _clean_value(getattr(response, "text", ""))
                _decision_log(f"direct VLM raw response model={model_name}: {result_text[:240]}", image_path)
                parsed = _parse_vlm_json_payload(result_text, image_path, source="direct")
                if not parsed:
                    _decision_log("direct VLM returned unusable payload", image_path, level="WARN")
                    return None
                normalized = _normalize_vlm_result(parsed)
                if not normalized:
                    _decision_log("direct VLM normalized payload is empty", image_path, level="WARN")
                    return None

                if worker_cancelled.is_set():
                    return None

                _set_cached_vlm_result(image_path, normalized, source="direct", prompt_text=vlm_prompt)
                _decision_log(
                    f"direct VLM normalized model={model_name} callsign={normalized['callsign'] or 'N/A'}, reg={normalized['registration_number'] or 'N/A'}, airline={normalized['airline'] or 'N/A'}, type={normalized['aircraft_type'] or 'N/A'}",
                    image_path,
                )
                return normalized
            except Exception as e:
                error_text = str(e)
                if (_is_server_side_error(error_text) or _is_quota_error(error_text)) and attempt < VLM_SERVER_RETRY_ATTEMPTS:
                    if worker_cancelled.is_set():
                        return None
                    wait_seconds = _retry_backoff_seconds(attempt - 1)
                    next_model = _cross_vlm_model_for_retry(attempt)
                    _decision_log(
                        f"direct VLM retryable error model={_cross_vlm_model_for_retry(attempt - 1)} attempt={attempt}/{VLM_SERVER_RETRY_ATTEMPTS}; cross-fallback -> {next_model}; retry in {wait_seconds:.1f}s; error={error_text}",
                        image_path,
                        level="WARN",
                    )
                    time.sleep(wait_seconds)
                    continue
                raise
        return None

    try:
        executor = concurrent.futures.ThreadPoolExecutor(max_workers=1)
        future = executor.submit(_run_direct_call)
        timed_out = False
        try:
            return future.result(timeout=VLM_DIRECT_TIMEOUT_SECONDS)
        except concurrent.futures.TimeoutError:
            if VLM_DIRECT_TIMEOUT_GRACE_SECONDS > 0:
                _decision_log(
                    f"direct VLM reached {VLM_DIRECT_TIMEOUT_SECONDS}s; waiting additional grace {VLM_DIRECT_TIMEOUT_GRACE_SECONDS:.1f}s",
                    image_path,
                    level="WARN",
                )
                try:
                    recovered = future.result(timeout=VLM_DIRECT_TIMEOUT_GRACE_SECONDS)
                    if recovered:
                        _decision_log("direct VLM completed during grace window", image_path)
                    return recovered
                except concurrent.futures.TimeoutError:
                    pass

            timed_out = True
            worker_cancelled.set()
            future.cancel()
            executor.shutdown(wait=False, cancel_futures=True)
            _decision_log("direct VLM worker detached after timeout", image_path, level="WARN")
            raise
        finally:
            if not timed_out:
                executor.shutdown(wait=True, cancel_futures=False)
    except concurrent.futures.TimeoutError:
        _decision_log(
            f"direct VLM timeout after {VLM_DIRECT_TIMEOUT_SECONDS}s (+{VLM_DIRECT_TIMEOUT_GRACE_SECONDS:.1f}s grace)",
            image_path,
            level="WARN",
        )
        return None
    except Exception as e:
        error_text = str(e)
        _decision_log(f"direct VLM call exception: {error_text}", image_path, level="WARN")
        return None


def _safe_call_mcp_vlm(image_path: Path, candidates: list[dict] | None = None) -> dict[str, str] | None:
    _decision_log("start MCP VLM call", image_path)
    vlm_prompt = _build_vlm_prompt(candidates)

    cached = _get_cached_vlm_result(image_path, vlm_prompt)
    if cached:
        return cached

    try:
        from mcp import ClientSession, StdioServerParameters  # type: ignore[import-not-found]
        from mcp.client.stdio import stdio_client  # type: ignore[import-not-found]
    except Exception:
        _decision_log("MCP client package not installed", image_path, level="WARN")
        console.print("[yellow]未安裝 MCP client 套件，改用 direct VLM fallback。[/yellow]")
        return _safe_call_direct_vlm(image_path, candidates)

    if not MCP_SERVER_SCRIPT.exists():
        _decision_log(f"MCP server script missing: {MCP_SERVER_SCRIPT}", image_path, level="WARN")
        console.print(f"[yellow]找不到 MCP Server: {MCP_SERVER_SCRIPT}，改用 direct VLM fallback。[/yellow]")
        return _safe_call_direct_vlm(image_path, candidates)

    if not _get_gemini_api_key():
        _decision_log("missing GEMINI_API_KEY/GOOGLE_API_KEY", image_path, level="WARN")
        console.print("[yellow]尚未設定 GEMINI_API_KEY/GOOGLE_API_KEY，略過 VLM 自動判斷。[/yellow]")
        return None

    async def _run() -> dict[str, str] | None:
        server_params = StdioServerParameters(
            command=sys.executable,
            args=[str(MCP_SERVER_SCRIPT)],
        )

        async with stdio_client(server_params) as (read, write):
            async with ClientSession(read, write) as session:
                await asyncio.wait_for(session.initialize(), timeout=VLM_MCP_TIMEOUT_SECONDS)
                result = await asyncio.wait_for(
                    session.call_tool(
                        VLM_TOOL_NAME,
                        arguments={"image_path": str(image_path), "prompt_text": vlm_prompt},
                    ),
                    timeout=VLM_MCP_TIMEOUT_SECONDS,
                )

                content = getattr(result, "content", []) or []
                text_chunks = [item.text for item in content if getattr(item, "text", None)]
                if not text_chunks:
                    _decision_log("MCP tool returned empty content", image_path, level="WARN")
                    return None

                raw = "\n".join(text_chunks).strip()
                _decision_log(f"MCP raw response: {raw[:240]}", image_path)
                parsed = _parse_vlm_json_payload(raw, image_path, source="mcp")
                if not parsed:
                    _decision_log("VLM response is not valid JSON", image_path, level="WARN")
                    console.print(f"[yellow]VLM 回傳非 JSON，略過：{raw[:120]}[/yellow]")
                    return None

                if parsed.get("error"):
                    error_text = str(parsed.get("error"))
                    _decision_log(f"VLM tool error: {error_text}", image_path, level="WARN")
                    if _is_server_side_error(error_text):
                        raise _RetryableVLMServerError(error_text)
                    if _is_quota_error(error_text):
                        _decision_log("Gemini quota exhausted; VLM auto-selection unavailable until quota resets", image_path, level="WARN")
                    console.print(f"[yellow]VLM 工具錯誤：{parsed.get('error')}[/yellow]")
                    return None

                normalized = _normalize_vlm_result(parsed)
                if not normalized:
                    _decision_log("VLM response JSON is not usable after normalization", image_path, level="WARN")
                    return None
                _set_cached_vlm_result(image_path, normalized, source="mcp", prompt_text=vlm_prompt)
                _decision_log(
                    f"normalized VLM fields callsign={normalized['callsign'] or 'N/A'}, reg={normalized['registration_number'] or 'N/A'}, airline={normalized['airline'] or 'N/A'}, type={normalized['aircraft_type'] or 'N/A'}",
                    image_path,
                )
                return normalized

    for attempt in range(1, VLM_SERVER_RETRY_ATTEMPTS + 1):
        try:
            return asyncio.run(_run())
        except asyncio.TimeoutError:
            _decision_log(
                f"MCP VLM timeout after {VLM_MCP_TIMEOUT_SECONDS}s",
                image_path,
                level="WARN",
            )
            console.print(f"[yellow]VLM MCP timeout，改用 direct VLM fallback。[/yellow]")
            return _safe_call_direct_vlm(image_path, candidates)
        except _RetryableVLMServerError as e:
            error_text = str(e)
            if attempt < VLM_SERVER_RETRY_ATTEMPTS:
                wait_seconds = _retry_backoff_seconds(attempt - 1)
                _decision_log(
                    f"MCP VLM server-side error attempt={attempt}/{VLM_SERVER_RETRY_ATTEMPTS}; retry in {wait_seconds:.1f}s; error={error_text}",
                    image_path,
                    level="WARN",
                )
                time.sleep(wait_seconds)
                continue
            _decision_log(f"MCP VLM server-side retries exhausted: {error_text}", image_path, level="WARN")
            console.print("[yellow]VLM MCP 伺服器忙碌，重試後仍失敗，改用 direct VLM fallback。[/yellow]")
            return _safe_call_direct_vlm(image_path, candidates)
        except Exception as e:
            error_text = _extract_exception_summary(e)
            if _is_server_side_error(error_text) and attempt < VLM_SERVER_RETRY_ATTEMPTS:
                wait_seconds = _retry_backoff_seconds(attempt - 1)
                _decision_log(
                    f"MCP VLM call exception (retryable) attempt={attempt}/{VLM_SERVER_RETRY_ATTEMPTS}; retry in {wait_seconds:.1f}s; error={error_text}",
                    image_path,
                    level="WARN",
                )
                time.sleep(wait_seconds)
                continue
            if _is_taskgroup_exception(e):
                _decision_log(f"MCP VLM transport exception: {error_text}", image_path, level="WARN")
                console.print("[yellow]VLM MCP 通道異常，改用 direct VLM fallback。[/yellow]")
            else:
                _decision_log(f"MCP VLM call exception: {error_text}", image_path, level="WARN")
                console.print(f"[yellow]VLM MCP 呼叫失敗，改用 direct VLM fallback：{error_text}[/yellow]")
            return _safe_call_direct_vlm(image_path, candidates)

    return _safe_call_direct_vlm(image_path, candidates)


def _score_candidate_with_vlm(candidate: dict, vlm_result: dict[str, str]) -> tuple[int, list[str]]:
    score = 0
    reasons: list[str] = []

    vlm_callsign = _normalize_compare_text(vlm_result.get("callsign"))
    candidate_callsign = _normalize_compare_text(candidate.get("callsign"))
    if vlm_callsign and candidate_callsign:
        if vlm_callsign == candidate_callsign:
            score += 8
            reasons.append("callsign exact")
        elif vlm_callsign in candidate_callsign or candidate_callsign in vlm_callsign:
            score += 4
            reasons.append("callsign partial")

    vlm_reg = _normalize_reg(vlm_result.get("registration_number"))
    candidate_reg = _normalize_reg(candidate.get("reg"))
    if vlm_reg and candidate_reg:
        if vlm_reg == candidate_reg:
            score += 6
            reasons.append("registration exact")
        elif vlm_reg in candidate_reg or candidate_reg in vlm_reg:
            score += 3
            reasons.append("registration partial")
        else:
            common_prefix_len = 0
            for a, b in zip(vlm_reg, candidate_reg):
                if a != b:
                    break
                common_prefix_len += 1

            # Partial registrations can miss trailing characters,
            # but short prefixes like "B-18" are too broad.
            if common_prefix_len >= 5:
                score += 2
                reasons.append("registration prefix")

    vlm_airline = _normalize_compare_text(vlm_result.get("airline"))
    candidate_airline = _normalize_compare_text(candidate.get("owner"))
    if vlm_airline and candidate_airline:
        if vlm_airline == candidate_airline:
            score += 3
            reasons.append("airline exact")
        elif vlm_airline in candidate_airline or candidate_airline in vlm_airline:
            score += 2
            reasons.append("airline partial")

    vlm_type = _normalize_compare_text(vlm_result.get("aircraft_type"))
    candidate_type = _normalize_compare_text(candidate.get("model"))
    if vlm_type and candidate_type:
        if vlm_type == candidate_type:
            score += 2
            reasons.append("type exact")
        elif vlm_type in candidate_type or candidate_type in vlm_type:
            score += 1
            reasons.append("type partial")

    vlm_family = _extract_aircraft_family(vlm_result.get("aircraft_type"))
    candidate_family = _extract_aircraft_family(candidate.get("model"))
    if vlm_family and candidate_family and vlm_family == candidate_family:
        score += 1
        reasons.append("type family")

    return score, reasons


def _select_candidate_by_vlm(candidates: list[dict], image_path: Path) -> dict | None:
    vlm_result = _safe_call_mcp_vlm(image_path, candidates)
    if not vlm_result:
        _decision_log("no usable VLM result for candidate scoring", image_path, level="WARN")
        return None

    vlm_callsign = _normalize_compare_text(vlm_result.get("callsign"))
    if vlm_callsign:
        exact_callsign_matches = [
            candidate
            for candidate in candidates
            if _normalize_compare_text(candidate.get("callsign")) == vlm_callsign
        ]
        if len(exact_callsign_matches) == 1:
            picked = exact_callsign_matches[0]
            _decision_log(
                f"auto selected by callsign match callsign={picked.get('callsign')}",
                image_path,
            )
            console.print(f"[cyan]VLM 自動選定(名單 callsign 直選): {picked['callsign']}[/cyan]")
            return picked

    scored: list[tuple[int, list[str], dict]] = []
    for candidate in candidates:
        score, reasons = _score_candidate_with_vlm(candidate, vlm_result)
        reason_text = ",".join(reasons) if reasons else "none"
        _decision_log(
            f"candidate score callsign={candidate.get('callsign')} reg={candidate.get('reg')} model={candidate.get('model')} owner={candidate.get('owner')} score={score} reasons={reason_text}",
            image_path,
        )
        scored.append((score, reasons, candidate))

    scored.sort(key=lambda item: item[0], reverse=True)
    best_score, best_reasons, best_candidate = scored[0]
    second_score = scored[1][0] if len(scored) > 1 else -1
    second_reasons = scored[1][1] if len(scored) > 1 else []
    airline_exact_count = sum(1 for _, reasons, _ in scored if "airline exact" in reasons)

    def _reason_rank(reasons: list[str]) -> int:
        rank = 0
        if "registration exact" in reasons:
            rank += 6
        elif "registration partial" in reasons:
            rank += 4
        elif "registration prefix" in reasons:
            rank += 2

        if "type exact" in reasons:
            rank += 3
        elif "type partial" in reasons:
            rank += 2
        elif "type family" in reasons:
            rank += 1

        if "airline exact" in reasons:
            rank += 2
        elif "airline partial" in reasons:
            rank += 1

        return rank

    best_rank = _reason_rank(best_reasons)
    second_rank = _reason_rank(second_reasons)
    _decision_log(
        f"best_score={best_score}, second_score={second_score}, best_rank={best_rank}, second_rank={second_rank}, airline_exact_count={airline_exact_count}, threshold_min={VLM_MIN_SCORE}, threshold_margin={VLM_SCORE_MARGIN}",
        image_path,
    )

    if best_score < VLM_MIN_SCORE:
        if (
            VLM_ALLOW_LOW_CONF_AIRLINE_EXACT
            and best_score == (VLM_MIN_SCORE - 1)
            and second_score <= 1
            and "airline exact" in best_reasons
            and airline_exact_count == 1
        ):
            reason_text = ", ".join(best_reasons) if best_reasons else "feature match"
            _decision_log(
                f"auto selected by low-conf airline-exact rule callsign={best_candidate.get('callsign')} score={best_score} reasons={reason_text}",
                image_path,
            )
            console.print(
                f"[cyan]VLM 自動選定(低信心放行): {best_candidate['callsign']} (score={best_score}, reason={reason_text})[/cyan]"
            )
            return best_candidate

        _decision_log("fallback to manual selection: best score below minimum", image_path, level="WARN")
        console.print("[yellow]VLM 判斷分數不足，改由人工選擇。[/yellow]")
        return None

    if (best_score - second_score) < VLM_SCORE_MARGIN:
        # If scores are close, allow stronger semantic match signals to break ties.
        if best_score >= VLM_MIN_SCORE and best_rank > second_rank:
            reason_text = ", ".join(best_reasons) if best_reasons else "feature match"
            _decision_log(
                f"auto selected by tie-break callsign={best_candidate.get('callsign')} score={best_score} rank={best_rank}>{second_rank} reasons={reason_text}",
                image_path,
            )
            console.print(
                f"[cyan]VLM 自動選定(近分決勝): {best_candidate['callsign']} (score={best_score}, reason={reason_text})[/cyan]"
            )
            return best_candidate

        _decision_log("fallback to manual selection: score gap below margin", image_path, level="WARN")
        console.print("[yellow]VLM 判斷不夠明確，改由人工選擇。[/yellow]")
        return None

    reason_text = ", ".join(best_reasons) if best_reasons else "feature match"
    _decision_log(
        f"auto selected by VLM callsign={best_candidate.get('callsign')} score={best_score} reasons={reason_text}",
        image_path,
    )
    console.print(
        f"[cyan]VLM 自動選定: {best_candidate['callsign']} (score={best_score}, reason={reason_text})[/cyan]"
    )
    return best_candidate


def _build_vlm_only_candidate(vlm_result: dict[str, str]) -> dict | None:
    reg = _normalize_reg(vlm_result.get("registration_number"))
    owner = _clean_value(vlm_result.get("airline"))
    model = _clean_value(vlm_result.get("aircraft_type"))

    reg = "N/A" if _is_unknown(reg) else reg
    owner = "N/A" if _is_unknown(owner) else owner
    model = "N/A" if _is_unknown(model) else model

    if reg == "N/A" and owner == "N/A" and model == "N/A":
        return None

    callsign = "N/A"
    return {
        "icao": "N/A",
        "callsign": callsign,
        "reg": reg,
        "model": model,
        "owner": owner,
        "display": f"{callsign:<8} | Reg: {reg:<8} | Model: {model:<28} | Airline: {owner}",
    }


def _upsert_known_hint(icao: str, callsign: str, reg: str, model: str, owner: str) -> None:
    fact = {
        "callsign": callsign.strip(),
        "reg": reg.strip(),
        "model": model.strip(),
        "owner": owner.strip(),
    }

    if icao and icao != "N/A":
        bucket = known_hints_by_icao.setdefault(icao, {})
        for key, value in fact.items():
            if key not in bucket or _is_unknown(bucket.get(key)):
                if not _is_unknown(value):
                    bucket[key] = value

    if not _is_unknown(callsign):
        callsign_key = callsign.strip().upper()
        bucket = known_hints_by_callsign.setdefault(callsign_key, {})
        for key, value in fact.items():
            if key not in bucket or _is_unknown(bucket.get(key)):
                if not _is_unknown(value):
                    bucket[key] = value

    reg_key = _normalize_reg(reg)
    if reg_key:
        bucket = known_hints_by_reg.setdefault(reg_key, {})
        for key, value in fact.items():
            if key not in bucket or _is_unknown(bucket.get(key)):
                if not _is_unknown(value):
                    bucket[key] = value


def _extract_facts_from_text(content: str) -> list[dict[str, str]]:
    facts: list[dict[str, str]] = []
    for match in SUMMARY_PATTERN.finditer(content):
        facts.append(
            {
                "callsign": unescape(match.group("callsign")).strip(),
                "reg": unescape(match.group("reg")).strip(),
                "model": unescape(match.group("model")).strip(),
                "owner": unescape(match.group("owner")).strip(),
            }
        )
    return facts


def _load_local_hints(search_root: Path, recursive: bool) -> int:
    loaded = 0
    paths = search_root.rglob("*") if recursive else search_root.iterdir()
    for path in paths:
        if path.suffix.lower() not in {".xmp", ".md"}:
            continue
        try:
            content = path.read_text(encoding="utf-8", errors="ignore")
        except OSError:
            continue

        for fact in _extract_facts_from_text(content):
            _upsert_known_hint("N/A", fact["callsign"], fact["reg"], fact["model"], fact["owner"])
            loaded += 1
    return loaded


def _build_batch_hints(raw_results: list[dict]) -> dict[str, dict[str, str]]:
    hints: dict[str, dict[str, str]] = {}
    for flight in raw_results:
        icao = _normalize_icao(flight.get("hex", "N/A"))
        if icao == "N/A":
            continue
        bucket = hints.setdefault(icao, {})
        candidate_fact = {
            "callsign": str(flight.get("flight") or "N/A").strip(),
            "reg": str(flight.get("registration") or "N/A").strip(),
            "model": str(flight.get("typecode") or "N/A").strip(),
            "owner": str(flight.get("owner") or "N/A").strip(),
        }
        for key, value in candidate_fact.items():
            if key not in bucket or _is_unknown(bucket.get(key)):
                if not _is_unknown(value):
                    bucket[key] = value
    return hints


def _load_airline_prefixes() -> None:
    global airline_map_loaded

    if airline_map_loaded:
        return

    with airline_map_lock:
        if airline_map_loaded:
            return

        if AIRLINE_MAP_PATH.exists():
            try:
                with AIRLINE_MAP_PATH.open("r", encoding="utf-8", errors="ignore", newline="") as csv_file:
                    reader = csv.DictReader(csv_file, delimiter="^")
                    for row in reader:
                        icao_code = _clean_value(row.get("icao_code")).upper()
                        name = _clean_value(row.get("name"))
                        if len(icao_code) == 3 and not _is_unknown(name):
                            AIRLINE_PREFIXES.setdefault(icao_code, name)
            except OSError:
                pass

        airline_map_loaded = True


def _extract_callsign_prefix(callsign: str) -> str:
    letters = [ch for ch in callsign if ch.isalpha()]
    if len(letters) < 3:
        return ""
    return "".join(letters[:3]).upper()


def _infer_airline(callsign: str, airline: str) -> str:
    if not _is_unknown(airline):
        return airline

    _load_airline_prefixes()
    prefix = _extract_callsign_prefix(callsign)
    if prefix and prefix in AIRLINE_PREFIXES:
        return AIRLINE_PREFIXES[prefix]

    return "Private / Unknown Operator"


def _expand_model(model: str) -> str:
    normalized = _clean_value(model)
    if not normalized:
        return model
    return AIRCRAFT_MODEL_MAP.get(normalized.upper(), normalized)


def _ensure_local_db_field_limit() -> None:
    global local_db_field_limit_set

    if local_db_field_limit_set:
        return

    try:
        csv.field_size_limit(16 * 1024 * 1024)
    except (OverflowError, ValueError):
        pass

    local_db_field_limit_set = True


def _local_hint_from_row(row: dict[str, Any]) -> dict[str, str]:
    reg = _clean_value(row.get("registration") or "N/A")
    model = _clean_value(row.get("model") or row.get("typecode") or "N/A")
    owner = _clean_value(row.get("owner") or row.get("operator") or row.get("operatorIcao") or "N/A")
    return {"reg": reg, "model": model, "owner": owner}


def _resolve_local_db_path() -> Path | None:
    if LOCAL_DB_GZ_PATH.exists():
        return LOCAL_DB_GZ_PATH
    if LOCAL_DB_CSV_FALLBACK_PATH.exists():
        return LOCAL_DB_CSV_FALLBACK_PATH
    return None


def _scan_local_db(
    unresolved_icaos: set[str],
    unresolved_regs: set[str],
) -> tuple[set[str], set[str]]:
    local_db_path = _resolve_local_db_path()
    if local_db_path is None:
        return unresolved_icaos, unresolved_regs

    if local_db_path.suffix == ".gz":
        csv_stream = gzip.open(local_db_path, "rt", encoding="utf-8", errors="ignore", newline="")
    else:
        csv_stream = local_db_path.open("r", encoding="utf-8", errors="ignore", newline="")

    with csv_stream as csv_file:
        reader = csv.DictReader(csv_file, quotechar="'", skipinitialspace=False)
        for row in reader:
            icao = _normalize_icao(row.get("icao24", "N/A"))
            hint = _local_hint_from_row(row)
            reg_key = _normalize_reg(hint.get("reg"))

            if icao in unresolved_icaos:
                local_db_cache_by_icao[icao] = hint
                unresolved_icaos.remove(icao)

            if reg_key and reg_key in unresolved_regs:
                local_db_cache_by_reg[reg_key] = hint
                unresolved_regs.remove(reg_key)

            if not unresolved_icaos and not unresolved_regs:
                break

    return unresolved_icaos, unresolved_regs


def _lookup_local_db_for_icaos(icaos: set[str]) -> None:
    global local_db_disabled

    with local_db_lock:
        if local_db_disabled:
            return

        unresolved_icaos = {
            icao
            for icao in icaos
            if icao != "N/A" and icao not in local_db_cache_by_icao and icao not in local_db_missing
        }
        if not unresolved_icaos or _resolve_local_db_path() is None:
            return

        try:
            _ensure_local_db_field_limit()
            unresolved_icaos, _ = _scan_local_db(unresolved_icaos, set())
        except csv.Error as e:
            local_db_disabled = True
            console.print(f"[yellow]本地 CSV 讀取失敗，略過離線補值: {e}[/yellow]")
            return
        except OSError:
            return

        local_db_missing.update(unresolved_icaos)


def _lookup_local_db_for_regs(regs: set[str]) -> None:
    global local_db_disabled

    normalized_regs = {_normalize_reg(reg) for reg in regs}

    with local_db_lock:
        if local_db_disabled:
            return

        unresolved_regs = {
            reg
            for reg in normalized_regs
            if reg and reg not in local_db_cache_by_reg and reg not in local_db_reg_missing
        }
        if not unresolved_regs or _resolve_local_db_path() is None:
            return

        try:
            _ensure_local_db_field_limit()
            _, unresolved_regs = _scan_local_db(set(), unresolved_regs)
        except csv.Error as e:
            local_db_disabled = True
            console.print(f"[yellow]本地 CSV 讀取失敗，略過離線補值: {e}[/yellow]")
            return
        except OSError:
            return

        local_db_reg_missing.update(unresolved_regs)


def _init_traffic_db() -> Any | None:
    global traffic_import_attempted
    global traffic_import_error
    global traffic_aircraft
    global traffic_db_initialized
    global traffic_db_disabled
    global traffic_db_frame

    if traffic_db_disabled:
        return None

    if not _is_traffic_supported_python():
        traffic_db_disabled = True
        console.print(
            f"[yellow]偵測到不受支援的 Python 版本，略過 traffic 離線補值。{_traffic_python_hint()}[/yellow]"
        )
        return None

    if traffic_db_initialized:
        return traffic_db_frame

    traffic_db_initialized = True
    if not traffic_import_attempted:
        traffic_import_attempted = True
        try:
            traffic_data = importlib.import_module("traffic.data")
            traffic_aircraft = getattr(traffic_data, "aircraft", None)
            traffic_import_error = None
        except Exception as e:
            traffic_aircraft = None
            traffic_import_error = str(e)

    if traffic_aircraft is None:
        traffic_db_disabled = True
        detail = f" ({traffic_import_error})" if traffic_import_error else ""
        console.print(
            "[yellow]無法載入 traffic，略過 traffic 離線補值。"
            f"請確認已安裝相依套件: pip install traffic pandas。{_traffic_python_hint()}{detail}[/yellow]"
        )
        return None

    try:
        console.print("[dim]初始化 traffic aircraft 資料庫（首次可能會自動下載並快取）...[/dim]")
        traffic_db_frame = traffic_aircraft.data
        return traffic_db_frame
    except Exception as e:
        traffic_db_disabled = True
        console.print(f"[yellow]traffic 資料庫初始化失敗，略過離線補值: {e}[/yellow]")
        return None


def _traffic_hint_from_row(row: Any) -> dict[str, str]:
    reg = _clean_value(row.get("registration") or row.get("regid") or row.get("tailnumber") or "N/A")
    model = _clean_value(row.get("model") or row.get("typecode") or row.get("icaoAircraftType") or "N/A")
    owner = _clean_value(
        row.get("owner")
        or row.get("operator")
        or row.get("operatoricao")
        or row.get("operatorIcao")
        or "N/A"
    )
    return {"reg": reg, "model": model, "owner": owner}


def _lookup_traffic_db_for_icaos(icaos: set[str]) -> None:
    with traffic_db_lock:
        unresolved_icaos = {
            icao
            for icao in icaos
            if icao != "N/A" and icao not in traffic_db_cache_by_icao and icao not in traffic_db_missing
        }
        if not unresolved_icaos:
            return

        db = _init_traffic_db()
        if db is None:
            return

        if "icao24" not in db.columns:
            traffic_db_missing.update(unresolved_icaos)
            return

        try:
            filtered = db[db["icao24"].astype(str).str.strip().str.lower().isin(unresolved_icaos)]
            for _, row in filtered.iterrows():
                icao = _normalize_icao(row.get("icao24", "N/A"))
                if icao in unresolved_icaos:
                    hint = _traffic_hint_from_row(row)
                    traffic_db_cache_by_icao[icao] = hint
                    reg_key = _normalize_reg(hint.get("reg"))
                    if reg_key:
                        traffic_db_cache_by_reg.setdefault(reg_key, hint)
                    unresolved_icaos.remove(icao)
        except Exception:
            pass

        traffic_db_missing.update(unresolved_icaos)


def _lookup_traffic_db_for_regs(regs: set[str]) -> None:
    normalized_regs = {_normalize_reg(reg) for reg in regs}

    with traffic_db_lock:
        unresolved_regs = {
            reg
            for reg in normalized_regs
            if reg and reg not in traffic_db_cache_by_reg and reg not in traffic_db_reg_missing
        }
        if not unresolved_regs:
            return

        db = _init_traffic_db()
        if db is None:
            return

        if "registration" not in db.columns:
            traffic_db_reg_missing.update(unresolved_regs)
            return

        try:
            reg_series = db["registration"].astype(str).str.replace("*", "", regex=False).str.strip().str.upper()
            filtered = db[reg_series.isin(unresolved_regs)]
            for _, row in filtered.iterrows():
                hint = _traffic_hint_from_row(row)
                reg_key = _normalize_reg(hint.get("reg"))
                if reg_key and reg_key in unresolved_regs:
                    traffic_db_cache_by_reg[reg_key] = hint
                    unresolved_regs.remove(reg_key)
        except Exception:
            pass

        traffic_db_reg_missing.update(unresolved_regs)

def _empty_aircraft_info() -> dict:
    return {"reg": "N/A", "type": "N/A", "airline": "N/A", "mfr": "", "year": ""}

def get_live_aircraft_info(icao: str) -> dict:
    if icao in live_ac_cache:
        return live_ac_cache[icao]
    try:
        url = f"https://hexdb.io/api/v1/aircraft/{icao}"
        res = requests.get(url, timeout=3)
        if res.status_code == 200:
            data = res.json()
            info = {
                "reg": data.get("Registration", "N/A") or "N/A",
                "type": data.get("Type", "N/A") or "N/A",
                "airline": data.get("Operator", "N/A") or "N/A",
                "mfr": data.get("Manufacturer", "") or "",
                "year": data.get("YearBuilt", "") or ""
            }
            live_ac_cache[icao] = info
            return info
    except Exception:
        pass
    return _empty_aircraft_info()


def _enrich_candidate(flight: dict, batch_hints: dict[str, dict[str, str]]) -> dict:
    icao = _normalize_icao(flight.get("hex", "N/A"))
    callsign = str(flight.get("flight") or "N/A").strip()
    reg = str(flight.get("registration") or "N/A").strip()
    model = str(flight.get("typecode") or "N/A").strip()
    owner = str(flight.get("owner") or "N/A").strip()

    batch_hint = batch_hints.get(icao, {})
    callsign = _prefer_known(callsign, batch_hint.get("callsign"))
    reg, model, owner = _merge_hint_values(reg, model, owner, batch_hint)

    icao_hint = known_hints_by_icao.get(icao, {})
    callsign_hint = known_hints_by_callsign.get(callsign.upper(), {}) if not _is_unknown(callsign) else {}
    reg_hint = known_hints_by_reg.get(_normalize_reg(reg), {}) if not _is_unknown(reg) else {}
    for hint in (icao_hint, reg_hint, callsign_hint):
        reg, model, owner = _merge_hint_values(reg, model, owner, hint)

    db_hint = traffic_db_cache_by_icao.get(icao, {})
    reg, model, owner = _merge_hint_values(reg, model, owner, db_hint)

    local_hint = local_db_cache_by_icao.get(icao, {})
    reg, model, owner = _merge_hint_values(reg, model, owner, local_hint)

    reg_key = _normalize_reg(reg)
    if reg_key and (_is_unknown(owner) or _is_unknown(model)):
        _lookup_traffic_db_for_regs({reg_key})
        reg_db_hint = traffic_db_cache_by_reg.get(reg_key, {})
        reg, model, owner = _merge_hint_values(reg, model, owner, reg_db_hint)

        _lookup_local_db_for_regs({reg_key})
        local_reg_db_hint = local_db_cache_by_reg.get(reg_key, {})
        reg, model, owner = _merge_hint_values(reg, model, owner, local_reg_db_hint)

    if _is_unknown(reg) or _is_unknown(model):
        live = get_live_aircraft_info(icao)
        if live["reg"] != "N/A":
            reg = _prefer_known(reg, f"{live['reg']}*")
            owner = _prefer_known(owner, live["airline"])
            live_model = f"{live['mfr']} {live['type']}".strip()
            if live["year"]:
                live_model += f" ({live['year']})"
            model = _prefer_known(model, live_model)

    if not _is_unknown(model):
        model = _expand_model(model)

    owner = _infer_airline(callsign, owner)

    callsign = "N/A" if _is_unknown(callsign) else callsign
    reg = "N/A" if _is_unknown(reg) else reg
    model = "N/A" if _is_unknown(model) else model
    owner = "N/A" if _is_unknown(owner) else owner

    return {
        "icao": icao,
        "callsign": callsign,
        "reg": reg,
        "model": model,
        "owner": owner,
        "display": f"{callsign:<8} | Reg: {reg:<8} | Model: {model:<28} | Airline: {owner}",
    }

def query_nas_history(latitude: float, longitude: float, time_utc: datetime) -> list[dict]:
    delta_lat = 15.0 / 111.0
    delta_lon = 15.0 / (111.0 * math.cos(math.radians(latitude)))
    bbox = f"{longitude-delta_lon:.4f},{latitude-delta_lat:.4f},{longitude+delta_lon:.4f},{latitude+delta_lat:.4f}"
    
    start_time = (time_utc - timedelta(minutes=BUFFER_MINUTES)).strftime("%Y-%m-%dT%H:%M:%SZ")
    end_time = (time_utc + timedelta(minutes=BUFFER_MINUTES)).strftime("%Y-%m-%dT%H:%M:%SZ")

    try:
        resp = requests.get(NAS_API_URL, params={"bbox": bbox, "start_time": start_time, "end_time": end_time}, timeout=10)
        resp.raise_for_status()
        raw_results = resp.json().get("results", [])

        batch_hints = _build_batch_hints(raw_results)
        _lookup_traffic_db_for_icaos(set(batch_hints.keys()))
        _lookup_local_db_for_icaos(set(batch_hints.keys()))

        def enrich_with_hints(flight: dict) -> dict:
            return _enrich_candidate(flight, batch_hints)

        with concurrent.futures.ThreadPoolExecutor(max_workers=10) as executor:
            candidates = list(executor.map(enrich_with_hints, raw_results))

        candidates.sort(key=lambda x: (x['callsign'] == 'N/A', x['reg'] == 'N/A', x['callsign']))
        return candidates
    except Exception as e:
        console.print(f"[red]NAS 查詢失敗: {e}[/red]")
        return []

# EXIF parsing and metadata writing.

def _ratio_to_float(value: Any) -> float:
    return float(value.num) / float(value.den)


def _collect_image_paths(target: Path, recursive: bool) -> list[Path]:
    if target.is_file():
        return [target]

    paths = target.rglob("*") if recursive else target.iterdir()
    return sorted(path for path in paths if path.suffix in SUPPORTED_EXTENSIONS)


def _select_coordinates_from_map(timeout_seconds: int = 300) -> tuple[float, float]:
    TILE_PROXY_UA = "AeroSpotter-LocalTileProxy/1.0"
    tile_cache_dir = TILE_CACHE_ROOT
    tile_cache_dir.mkdir(parents=True, exist_ok=True)

    html = """<!doctype html>
<html lang="zh-Hant">
<head>
    <meta charset="utf-8" />
    <meta name="viewport" content="width=device-width, initial-scale=1" />
    <title>Select Coordinates</title>
    <link rel="preconnect" href="https://tile.openstreetmap.org" crossorigin />
    <link rel="stylesheet" href="https://cdn.jsdelivr.net/npm/leaflet@1.9.4/dist/leaflet.css" />
    <style>
        html, body { margin: 0; padding: 0; font-family: -apple-system, BlinkMacSystemFont, sans-serif; background: #f5f7fb; }
        .container { max-width: 1100px; margin: 0 auto; padding: 14px; }
        .card { background: #fff; border: 1px solid #dde4ee; border-radius: 12px; padding: 12px; }
        .top { display: flex; flex-wrap: wrap; gap: 10px; align-items: end; margin-bottom: 10px; }
        .field { display: flex; flex-direction: column; gap: 6px; }
        input[type="number"] { width: 170px; padding: 8px; border: 1px solid #c9d5e3; border-radius: 8px; }
        button { border: 0; border-radius: 8px; padding: 9px 14px; cursor: pointer; font-size: 14px; }
        #sync { background: #0f766e; color: #fff; }
        #confirm { background: #1d4ed8; color: #fff; }
        #map { height: 560px; border-radius: 10px; border: 1px solid #d0dae8; }
        .hint { color: #475569; font-size: 13px; margin-top: 8px; white-space: pre-line; }
    </style>
</head>
<body>
    <div class="container">
        <div class="card">
            <div class="top">
                <div class="field">
                    <label for="lat">緯度 (Latitude)</label>
                    <input id="lat" type="number" step="0.000001" value="25.033000" />
                </div>
                <div class="field">
                    <label for="lng">經度 (Longitude)</label>
                    <input id="lng" type="number" step="0.000001" value="121.565400" />
                </div>
                <div class="field">
                    <label for="zoom">縮放 (1-19)</label>
                    <input id="zoom" type="number" min="1" max="19" step="1" value="7" />
                </div>
                <button id="sync">移動地圖</button>
                <button id="confirm">確認座標</button>
            </div>

            <div id="map"></div>
            <div class="hint" id="status">載入 OpenStreetMap 中... 使用本機快取圖磚，縮放會更穩定。</div>
            <div class="hint">備援：<a href="https://www.openstreetmap.org" target="_blank" rel="noopener">openstreetmap.org</a></div>
        </div>
    </div>

    <script src="https://cdn.jsdelivr.net/npm/leaflet@1.9.4/dist/leaflet.js"></script>
    <script>
        const latInput = document.getElementById('lat');
        const lngInput = document.getElementById('lng');
        const zoomInput = document.getElementById('zoom');
        const status = document.getElementById('status');
        const syncButton = document.getElementById('sync');
        const confirmButton = document.getElementById('confirm');

        function clamp(v, min, max) {
            return Math.max(min, Math.min(max, v));
        }

        function getInputState() {
            const lat = clamp(Number(latInput.value) || 0, -85, 85);
            const lng = clamp(Number(lngInput.value) || 0, -180, 180);
            const zoom = clamp(Math.round(Number(zoomInput.value) || 7), 1, 19);
            latInput.value = lat.toFixed(6);
            lngInput.value = lng.toFixed(6);
            zoomInput.value = zoom;
            return { lat, lng, zoom };
        }

        let map = null;
        let marker = null;

        function updateInputs(lat, lng, zoom) {
            latInput.value = lat.toFixed(6);
            lngInput.value = lng.toFixed(6);
            if (Number.isFinite(zoom)) {
                zoomInput.value = zoom;
            }
        }

        function ensureMarker(lat, lng) {
            if (!marker) {
                marker = L.marker([lat, lng]).addTo(map);
            } else {
                marker.setLatLng([lat, lng]);
            }
        }

        function initMap() {
            if (typeof L === 'undefined') {
                status.textContent = 'Leaflet 載入失敗，請手動輸入座標後按確認。';
                return;
            }

            const { lat, lng, zoom } = getInputState();
            map = L.map('map', {
                zoomControl: true,
                preferCanvas: true,
                fadeAnimation: false,
                zoomAnimation: false,
                markerZoomAnimation: false,
            }).setView([lat, lng], zoom);

            L.tileLayer('/tiles/{z}/{x}/{y}.png', {
                maxZoom: 19,
                maxNativeZoom: 17,
                detectRetina: false,
                attribution: '&copy; OpenStreetMap contributors',
                keepBuffer: 1,
                updateWhenIdle: true,
                updateWhenZooming: false,
            }).addTo(map);

            ensureMarker(lat, lng);
            status.textContent = 'OpenStreetMap 已載入，點地圖即可選座標。';

            map.on('click', (event) => {
                const selected = event.latlng;
                ensureMarker(selected.lat, selected.lng);
                updateInputs(selected.lat, selected.lng, map.getZoom());
                status.textContent = `已選擇: 緯度 ${latInput.value}, 經度 ${lngInput.value}`;
            });

            map.on('moveend', () => {
                const center = map.getCenter();
                updateInputs(center.lat, center.lng, map.getZoom());
            });
        }

        syncButton.addEventListener('click', () => {
            const { lat, lng, zoom } = getInputState();
            if (map) {
                map.setView([lat, lng], zoom, { animate: false });
                ensureMarker(lat, lng);
                status.textContent = '地圖已移動到輸入位置。';
            } else {
                status.textContent = '地圖尚未載入，仍可直接按確認送出。';
            }
        });

        async function submitSelection() {
            const { lat, lng } = getInputState();
            confirmButton.disabled = true;
            try {
                const response = await fetch('/select', {
                    method: 'POST',
                    headers: { 'Content-Type': 'application/json' },
                    body: JSON.stringify({ lat, lng })
                });
                if (!response.ok) {
                    throw new Error('Failed to submit coordinates');
                }
                status.textContent = '座標已送出，請回到 CLI。';
            } catch (error) {
                status.textContent = '送出失敗，請重試。';
                confirmButton.disabled = false;
            }
        }

        confirmButton.addEventListener('click', submitSelection);
        initMap();
    </script>
</body>
</html>
"""

    selected = threading.Event()
    coordinate: dict[str, float] = {}

    def _tile_cache_path(z: int, x: int, y: int) -> Path:
        return tile_cache_dir / str(z) / str(x) / f"{y}.png"

    def _read_cached_tile(z: int, x: int, y: int) -> bytes | None:
        path = _tile_cache_path(z, x, y)
        try:
            if path.exists():
                return path.read_bytes()
        except OSError:
            return None
        return None

    def _fetch_remote_tile(z: int, x: int, y: int) -> bytes | None:
        url = f"https://tile.openstreetmap.org/{z}/{x}/{y}.png"
        try:
            response = requests.get(url, timeout=10, headers={"User-Agent": TILE_PROXY_UA})
            if response.status_code != 200:
                return None
            tile_bytes = response.content
        except requests.RequestException:
            return None

        cache_path = _tile_cache_path(z, x, y)
        try:
            cache_path.parent.mkdir(parents=True, exist_ok=True)
            cache_path.write_bytes(tile_bytes)
        except OSError:
            pass
        return tile_bytes

    def _parse_tile_request(path: str) -> tuple[int, int, int] | None:
        tile_path = path.split("?", 1)[0]
        parts = tile_path.strip("/").split("/")
        if len(parts) != 4 or parts[0] != "tiles" or not parts[3].endswith(".png"):
            return None

        z_text, x_text = parts[1], parts[2]
        y_text = parts[3][:-4]

        if not (z_text.isdigit() and x_text.isdigit() and y_text.isdigit()):
            return None

        z, x, y = int(z_text), int(x_text), int(y_text)
        if z < 0 or z > 19:
            return None

        max_index = (1 << z) - 1
        if x < 0 or y < 0 or x > max_index or y > max_index:
            return None

        return z, x, y

    class MapHandler(BaseHTTPRequestHandler):
        def _send_bytes(self, body: bytes, content_type: str, cache_control: str | None = None) -> None:
            try:
                self.send_response(200)
                self.send_header("Content-Type", content_type)
                if cache_control:
                    self.send_header("Cache-Control", cache_control)
                self.send_header("Content-Length", str(len(body)))
                self.end_headers()
                self.wfile.write(body)
            except (BrokenPipeError, ConnectionResetError):
                # Browser may cancel in-flight tile requests while zooming/panning.
                return

        def do_GET(self) -> None:
            if self.path == "/":
                encoded = html.encode("utf-8")
                self._send_bytes(encoded, "text/html; charset=utf-8")
                return

            tile_request = _parse_tile_request(self.path)
            if tile_request is None:
                self.send_error(404)
                return

            z, x, y = tile_request
            tile_bytes = _read_cached_tile(z, x, y)
            if tile_bytes is None:
                tile_bytes = _fetch_remote_tile(z, x, y)

            if tile_bytes is None:
                self.send_error(502, "Tile fetch failed")
                return

            self._send_bytes(tile_bytes, "image/png", cache_control="public, max-age=86400")

        def do_POST(self) -> None:
            if self.path != "/select":
                self.send_error(404)
                return

            content_length = int(self.headers.get("Content-Length", "0"))
            raw_body = self.rfile.read(content_length)
            try:
                payload = json.loads(raw_body.decode("utf-8"))
                coordinate["lat"] = float(payload["lat"])
                coordinate["lng"] = float(payload["lng"])
            except (ValueError, KeyError, json.JSONDecodeError):
                self.send_error(400, "Invalid coordinate payload")
                return

            selected.set()
            self._send_bytes(b'{"ok": true}', "application/json")

        def log_message(self, format: str, *args: object) -> None:
            return

    server = ThreadingHTTPServer(("127.0.0.1", 0), MapHandler)
    server_thread = threading.Thread(target=server.serve_forever, daemon=True)
    server_thread.start()

    url = f"http://127.0.0.1:{server.server_address[1]}"
    console.print(f"[cyan]請在地圖視窗點選座標，網址: {url}[/cyan]")
    webbrowser.open(url)

    try:
        if not selected.wait(timeout=timeout_seconds):
            raise TimeoutError("Timed out waiting for map coordinate selection")
        return coordinate["lat"], coordinate["lng"]
    finally:
        server.shutdown()
        server.server_close()
        server_thread.join(timeout=1)

def read_exif_metadata(image_path: Path) -> ExifMetadata:
    with image_path.open("rb") as f:
        tags = exifread.process_file(f, details=False)

    dt_tag = tags.get("EXIF DateTimeOriginal") or tags.get("Image DateTime")
    raw_dt = str(getattr(dt_tag, "values", "")).strip() if dt_tag else None
    cap_local = None
    if raw_dt:
        try: cap_local = datetime.strptime(raw_dt, "%Y:%m:%d %H:%M:%S")
        except: pass

    off_tag = tags.get("EXIF OffsetTimeOriginal") or tags.get("EXIF OffsetTime")
    offset_time = str(getattr(off_tag, "values", "")).strip() if off_tag else None

    lat_tag, lat_ref = tags.get("GPS GPSLatitude"), tags.get("GPS GPSLatitudeRef")
    lon_tag, lon_ref = tags.get("GPS GPSLongitude"), tags.get("GPS GPSLongitudeRef")
    
    lat, lon = None, None
    if all([lat_tag, lat_ref, lon_tag, lon_ref]):
        lat = _ratio_to_float(lat_tag.values[0]) + _ratio_to_float(lat_tag.values[1]) / 60 + _ratio_to_float(lat_tag.values[2]) / 3600
        if str(lat_ref.values).upper() == 'S': lat *= -1
        lon = _ratio_to_float(lon_tag.values[0]) + _ratio_to_float(lon_tag.values[1]) / 60 + _ratio_to_float(lon_tag.values[2]) / 3600
        if str(lon_ref.values).upper() == 'W': lon *= -1

    return ExifMetadata(image_path, cap_local, raw_dt, offset_time, lat, lon)

def write_metadata(image_path: Path, plane: dict):
    summary = f"AeroSpotter: {plane['display']}"
    if image_path.suffix.lower() in RAW_EXTENSIONS:
        xmp_path = image_path.with_suffix('.xmp')
        with open(xmp_path, 'w', encoding='utf-8') as f:
            f.write(f'<?xpacket begin="" id="W5M0MpCehiHzreSzNTczkc9d"?><x:xmpmeta xmlns:x="adobe:ns:meta/"><rdf:RDF xmlns:rdf="http://www.w3.org/1999/02/22-rdf-syntax-ns#"><rdf:Description rdf:about="" xmlns:dc="http://purl.org/dc/elements/1.1/"><dc:description><rdf:Alt><rdf:li xml:lang="x-default">{summary}</rdf:li></rdf:Alt></dc:description></rdf:Description></rdf:RDF></x:xmpmeta><?xpacket end="w"?>')
    else:
        exif_dict = piexif.load(str(image_path))
        comment = piexif.helper.UserComment.dump(summary, encoding='unicode')
        exif_dict['Exif'][piexif.ExifIFD.UserComment] = comment
        exif_dict['0th'][piexif.ImageIFD.ImageDescription] = summary.encode('utf-8')
        piexif.insert(piexif.dump(exif_dict), str(image_path))


def write_sidecar_json(image_path: Path, payload: dict[str, Any]) -> None:
    """Always write per-image JSON result next to the image file."""
    sidecar_path = image_path.with_suffix('.json')
    try:
        sidecar_path.write_text(
            json.dumps(payload, ensure_ascii=False, indent=2),
            encoding="utf-8",
        )
    except OSError as e:
        _decision_log(f"failed to write sidecar json: {e}", image_path, level="WARN")
        return
    _decision_log(f"sidecar json written: {sidecar_path.name}", image_path)


def _remember_selected_candidate(candidate: dict) -> None:
    _upsert_known_hint(
        _normalize_icao(candidate.get("icao", "N/A")),
        str(candidate.get("callsign") or "N/A"),
        str(candidate.get("reg") or "N/A"),
        str(candidate.get("model") or "N/A"),
        str(candidate.get("owner") or "N/A"),
    )

def _resolve_location_context(exif: ExifMetadata, cached_loc: LocationContext | None) -> LocationContext:
    if exif.has_gps:
        tz = _TIMEZONE_FINDER.timezone_at(lat=exif.latitude, lng=exif.longitude)
        return LocationContext(exif.latitude, exif.longitude, tz, "GPS")

    if cached_loc:
        return cached_loc

    lat, lon = _select_coordinates_from_map()
    tz = _TIMEZONE_FINDER.timezone_at(lat=lat, lng=lon)
    if not tz:
        raise ValueError("Unable to determine timezone from selected coordinates")
    return LocationContext(lat, lon, tz, "MapSelection")


def _to_utc(exif: ExifMetadata, timezone_name: str) -> datetime:
    if exif.captured_at_local is None:
        raise ValueError(f"Missing capture time in {exif.image_path.name}")

    return exif.captured_at_local.replace(tzinfo=ZoneInfo(timezone_name)).astimezone(timezone.utc)


def _prompt_candidate(candidates: list[dict], image_name: str, image_path: Path | None = None) -> dict | None:
    _decision_log(f"manual prompt opened with {len(candidates)} candidates", image_path)
    selected = questionary.select(
        f"請為 {image_name} 選擇正確航班：",
        choices=[questionary.Choice(candidate['display'], value=candidate) for candidate in candidates] + [questionary.Separator(), questionary.Choice("跳過此照片", value="__SKIP__")],
        style=custom_style,
    ).ask()

    if isinstance(selected, dict):
        _decision_log(
            f"manual prompt selected callsign={selected.get('callsign')} reg={selected.get('reg')}",
            image_path,
        )
        return selected
    _decision_log("manual prompt returned skip", image_path, level="WARN")
    return None


@app.command("refresh-aircraft-db")
def refresh_aircraft_db() -> None:
    """Force-download the latest traffic aircraft database into local cache."""
    global traffic_db_disabled
    global traffic_db_initialized
    global traffic_db_frame

    if not _is_traffic_supported_python():
        console.print(
            f"[red]目前 Python 版本不建議使用 traffic。{_traffic_python_hint()}[/red]"
        )
        raise typer.Exit(code=1)

    try:
        traffic_data = importlib.import_module("traffic.data")
        aircraft_obj = getattr(traffic_data, "aircraft", None)
    except Exception as e:
        console.print(f"[red]無法載入 traffic: {e}[/red]")
        aircraft_obj = None

    if aircraft_obj is None:
        console.print("[red]traffic 未安裝，請先執行: pip install traffic pandas[/red]")
        raise typer.Exit(code=1)

    try:
        console.print("[cyan]正在下載最新版 traffic aircraft 資料庫...[/cyan]")
        if hasattr(aircraft_obj, "download"):
            aircraft_obj.download()
        elif hasattr(aircraft_obj, "download_opensky"):
            aircraft_obj.download_opensky()
        else:
            raise RuntimeError("Installed traffic version does not provide a download API")
        traffic_db_frame = aircraft_obj.data
        traffic_db_disabled = False
        traffic_db_initialized = True
        traffic_db_cache_by_icao.clear()
        traffic_db_cache_by_reg.clear()
        traffic_db_missing.clear()
        traffic_db_reg_missing.clear()
        console.print(f"[green]完成。可用筆數: {len(traffic_db_frame)}[/green]")
    except Exception as e:
        console.print(f"[red]更新 traffic 資料庫失敗: {e}[/red]")
        raise typer.Exit(code=1)


@app.command()
def process(target: Path = typer.Argument(...), recursive: bool = False):
    """Process one file or a folder of images and write aircraft metadata."""
    files = _collect_image_paths(target, recursive)

    hint_root = target.parent if target.is_file() else target
    loaded_hints = _load_local_hints(hint_root, recursive)
    if loaded_hints:
        console.print(f"  [dim]已載入本地標註提示: {loaded_hints} 筆[/dim]")

    cached_loc = None
    for idx, img in enumerate(files, 1):
        console.rule(f"[bold blue]({idx}/{len(files)}) {img.name}")
        _decision_log(f"start processing image ({idx}/{len(files)})", img)
        exif = read_exif_metadata(img)
        branch = "unknown"

        cached_loc = _resolve_location_context(exif, cached_loc)
        utc_time = _to_utc(exif, cached_loc.timezone_name)
        console.print(f"  [dim]時區: {cached_loc.timezone_name} | UTC: {utc_time.strftime('%Y-%m-%d %H:%M:%S')}[/dim]")
        _decision_log(
            f"location lat={cached_loc.latitude:.5f}, lon={cached_loc.longitude:.5f}, tz={cached_loc.timezone_name}, utc={utc_time.strftime('%Y-%m-%dT%H:%M:%SZ')}",
            img,
        )

        candidates = query_nas_history(cached_loc.latitude, cached_loc.longitude, utc_time)
        _decision_log(f"radar candidate count={len(candidates)}", img)

        selected: dict | None = None

        if not candidates:
            branch = "no-candidate"
            _decision_log("branch=no-candidate; trying VLM-only", img)
            console.print("  [yellow]try VLM[/yellow]")
            vlm_result = _safe_call_mcp_vlm(img)
            if vlm_result:
                selected = _build_vlm_only_candidate(vlm_result)
                if selected:
                    _decision_log("VLM-only candidate built successfully", img)
                    console.print("  [cyan]VLM hit[/cyan]")
            if not selected:
                _decision_log("no-candidate branch failed to resolve by VLM", img, level="WARN")
                console.print("  [yellow]VLM miss, skip[/yellow]")
                write_sidecar_json(
                    img,
                    {
                        "status": "skipped",
                        "reason": "no_candidate_and_vlm_unresolved",
                        "image": str(img),
                        "captured_at_local": exif.raw_datetime,
                        "utc_time": utc_time.strftime("%Y-%m-%dT%H:%M:%SZ"),
                        "location": {
                            "lat": cached_loc.latitude,
                            "lon": cached_loc.longitude,
                            "timezone": cached_loc.timezone_name,
                        },
                        "candidate_count": 0,
                        "branch": branch,
                        "generated_at_utc": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
                    },
                )
                continue
        elif len(candidates) == 1:
            branch = "single-candidate"
            selected = candidates[0]
            _decision_log(f"branch=single-candidate; auto-selected {selected.get('callsign')}", img)
            console.print(f"  [cyan]單一候選，自動選定: {selected['callsign']}[/cyan]")
        else:
            branch = "multi-candidate"
            
            console.print("  [dim]啟動本機 Edge OCR 嘗試快速配對...[/dim]")
            ocr_marks = extract_registration_marks(str(img), YOLO_WEIGHTS_PATH)
            
            if ocr_marks:
                _decision_log(f"local OCR found marks: {ocr_marks}", img)
                for mark in ocr_marks:
                    normalized_mark = _normalize_reg(mark)
                    for candidate in candidates:
                        if _normalize_reg(candidate.get("reg")) == normalized_mark:
                            selected = candidate
                            _decision_log(f"auto selected by local OCR match reg={normalized_mark}", img)
                            console.print(f"  [cyan]OCR: {selected['callsign']} (Reg: {normalized_mark})[/cyan]")
                            break
                    if selected:
                        break

            if not selected:
                _decision_log("branch=multi-candidate; local OCR missed, trying VLM scoring", img)
                console.print("  [dim]OCR missed, VLM selecting...[/dim]")
                selected = _select_candidate_by_vlm(candidates, img)
                
            if not selected:
                selected = _prompt_candidate(candidates, img.name, img)

        if selected:
            _remember_selected_candidate(selected)
            write_metadata(img, selected)
            write_sidecar_json(
                img,
                {
                    "status": "selected",
                    "image": str(img),
                    "captured_at_local": exif.raw_datetime,
                    "utc_time": utc_time.strftime("%Y-%m-%dT%H:%M:%SZ"),
                    "location": {
                        "lat": cached_loc.latitude,
                        "lon": cached_loc.longitude,
                        "timezone": cached_loc.timezone_name,
                    },
                    "candidate_count": len(candidates),
                    "branch": branch,
                    "selected": {
                        "icao": selected.get("icao"),
                        "callsign": selected.get("callsign"),
                        "registration": selected.get("reg"),
                        "aircraft_type": selected.get("model"),
                        "airline": selected.get("owner"),
                        "display": selected.get("display"),
                    },
                    "generated_at_utc": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
                },
            )
            _decision_log(
                f"metadata written callsign={selected.get('callsign')} reg={selected.get('reg')} model={selected.get('model')} owner={selected.get('owner')}",
                img,
            )
            console.print(f"  [green]✅ 已標註: {selected['callsign']}[/green]")
        else:
            write_sidecar_json(
                img,
                {
                    "status": "skipped",
                    "reason": "manual_skip_or_unresolved",
                    "image": str(img),
                    "captured_at_local": exif.raw_datetime,
                    "utc_time": utc_time.strftime("%Y-%m-%dT%H:%M:%SZ"),
                    "location": {
                        "lat": cached_loc.latitude,
                        "lon": cached_loc.longitude,
                        "timezone": cached_loc.timezone_name,
                    },
                    "candidate_count": len(candidates),
                    "branch": branch,
                    "generated_at_utc": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
                },
            )

if __name__ == "__main__":
    app()