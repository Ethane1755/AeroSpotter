import os
import json
import time
import PIL.Image
from google import genai

# Legacy standalone Gemini batch VLM testing script.

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


# 1. Initialization Settings
GOOGLE_API_KEY = os.environ.get("GEMINI_API_KEY") or os.environ.get("GOOGLE_API_KEY")
if not GOOGLE_API_KEY:
    raise EnvironmentError("Missing GEMINI_API_KEY/GOOGLE_API_KEY. Please set one of them before running VLM.py")
client = genai.Client(api_key=GOOGLE_API_KEY)
VLM_MODEL_PRIMARY = os.environ.get("VLM_MODEL_PRIMARY", "gemini-2.5-flash").strip() or "gemini-2.5-flash"
VLM_MODEL_BACKUP = os.environ.get("VLM_MODEL_BACKUP", "gemini-3-flash").strip() or "gemini-3-flash"
VLM_RETRY_ATTEMPTS = max(1, int(os.environ.get("VLM_RETRY_ATTEMPTS", "4")))
VLM_RETRY_BASE_SECONDS = float(os.environ.get("VLM_RETRY_BASE_SECONDS", "1.0"))
VLM_RETRY_MAX_SECONDS = float(os.environ.get("VLM_RETRY_MAX_SECONDS", "8.0"))


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


def _generate_content_with_cross_fallback(client_obj: genai.Client, contents: list[object]) -> tuple[object, str]:
    last_error: Exception | None = None

    for attempt in range(1, VLM_RETRY_ATTEMPTS + 1):
        model_name = _cross_vlm_model_for_retry(attempt - 1)
        try:
            response = client_obj.models.generate_content(model=model_name, contents=contents)
            return response, model_name
        except Exception as exc:
            last_error = exc
            error_text = str(exc)
            retryable = _is_server_side_error(error_text) or _is_quota_error(error_text)
            if retryable and attempt < VLM_RETRY_ATTEMPTS:
                wait_seconds = _retry_backoff_seconds(attempt - 1)
                next_model = _cross_vlm_model_for_retry(attempt)
                print(
                    f" Retryable VLM error on {model_name} ({attempt}/{VLM_RETRY_ATTEMPTS}); "
                    f"cross-fallback -> {next_model}; retry in {wait_seconds:.1f}s. Error: {error_text}"
                )
                time.sleep(wait_seconds)
                continue
            raise

    raise RuntimeError(str(last_error) if last_error else "VLM request failed")

# 2. Set Folder Path and Prompt
folder_path = "test"  # The folder name where your images are stored

prompt_text = """
You are a professional aviation photography analysis assistant. Please observe this airplane photo and provide the following information as much as possible:
1. Registration Number: Usually located under the tail. If it's unclear, please provide any partial string you can barely recognize.
2. Airline/Livery: Please identify this based on the text on the fuselage or the tail logo.
3. Aircraft Type: Infer the base aircraft type (e.g., Boeing 777, Airbus A320, etc.) through engine features, landing gear, and fuselage shape.

Please return the result STRICTLY in JSON format as follows:
{
  "registration_number": "string or null",
  "airline": "airline name",
  "aircraft_type": "aircraft type"
}
"""

# 3. Batch Processing
if not os.path.exists(folder_path):
    print(f"Error: Cannot find the folder '{folder_path}'. Please make sure it is in the same directory as this python script.")
else:
    # Get all .jpg, .jpeg, or .png files in the folder
    valid_extensions = ('.jpg', '.jpeg', '.png')
    image_files = [f for f in os.listdir(folder_path) if f.lower().endswith(valid_extensions)]
    
    if not image_files:
        print(f"No images found in the '{folder_path}' folder.")
    else:
        print(
            f"Found {len(image_files)} images. Starting batch processing with cross fallback "
            f"({VLM_MODEL_PRIMARY} <-> {VLM_MODEL_BACKUP})...\n"
        )
        
        # Process each image using a for loop
        for image_name in image_files:
            image_path = os.path.join(folder_path, image_name)
            print("-" * 50)
            print(f" Analyzing image: {image_name}")
            
            try:
                # Load the image
                img = PIL.Image.open(image_path)
                try:
                    # Send the request
                    response, used_model = _generate_content_with_cross_fallback(client, [prompt_text, img])

                    # Clean and extract the JSON string
                    result_text = response.text.strip().removeprefix('```json').removesuffix('```').strip()

                    # Parse into a Dictionary
                    result_dict = json.loads(result_text)

                    # Print the results nicely
                    print(f" Analysis successful!")
                    print(f"   Model Used: {used_model}")
                    print(f"   Airline: {result_dict.get('airline')}")
                    print(f"   Aircraft Type: {result_dict.get('aircraft_type')}")
                    print(f"   Registration Number: {result_dict.get('registration_number')}\n")
                finally:
                    try:
                        img.close()
                    except Exception:
                        pass
                
            except Exception as e:
                # If an image fails or the API disconnects, print the error but continue running
                print(f" Error processing {image_name}: {e}\n")
        
        print("-" * 50)
        print(" All images processed!")