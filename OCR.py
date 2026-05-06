import argparse
import os
import re
import warnings
from typing import List

# Detector-first OCR pipeline for extracting aircraft registration marks.
warnings.filterwarnings("ignore", category=DeprecationWarning)

import cv2
from paddleocr import PaddleOCR
from ultralytics import YOLO

def create_paddle_ocr_engine() -> PaddleOCR:
    """Initialize PaddleOCR with backward-compatible kwargs across versions."""
    os.environ.update({"PADDLE_PDX_DISABLE_MODEL_SOURCE_CHECK": "True", "OMP_NUM_THREADS": "1"})
    
    # Try different combinations to bypass strict kwarg validation in newer PaddleOCR versions
    candidate_kwargs = [
        {"lang": "en", "use_textline_orientation": False, "show_log": False},
        {"lang": "en", "use_textline_orientation": False},
        {"lang": "en", "show_log": False},
        {"lang": "en"}
    ]

    for kwargs in candidate_kwargs:
        try:
            return PaddleOCR(**kwargs)
        except ValueError as e:
            if "Unknown argument" in str(e):
                continue
            raise e
            
    raise RuntimeError("Failed to initialize PaddleOCR with any standard argument combinations.")

def detect_and_crop(image, yolo_model: YOLO, padding: float = 0.08, conf: float = 0.03) -> list:
    """Crop potential targets found by YOLO"""
    results = yolo_model.predict(source=image, conf=conf, imgsz=1280, verbose=False)
    crops = []
    
    if not results or not results[0].boxes:
        return crops

    h, w = image.shape[:2]
    # Sort by confidence, keep top 8
    boxes = sorted(results[0].boxes, key=lambda b: b.conf.item(), reverse=True)[:8]

    for box in boxes:
        x1, y1, x2, y2 = map(int, box.xyxy[0].tolist())
        box_w, box_h = max(1, x2 - x1), max(1, y2 - y1)
        pad_x, pad_y = int(box_w * padding), int(box_h * padding)

        nx1, ny1 = max(0, x1 - pad_x), max(0, y1 - pad_y)
        nx2, ny2 = min(w, x2 + pad_x), min(h, y2 + pad_y)
        
        crop = image[ny1:ny2, nx1:nx2]
        if crop.size > 0:
            if max(crop.shape) < 300:
                crop = cv2.resize(crop, None, fx=2.0, fy=2.0, interpolation=cv2.INTER_CUBIC)
            crops.append(crop)
            
    return crops

def extract_registration_marks(image_path: str, weights_path: str) -> List[str]:
    if not os.path.exists(weights_path):
        print(f"[Error] YOLO weight file does not exist: {weights_path}")
        return []
        
    image = cv2.imread(image_path)
    if image is None:
        print(f"[Error] can't read file: {image_path}")
        return []

    yolo_model = YOLO(weights_path)
    ocr_engine = create_paddle_ocr_engine()
    crops = detect_and_crop(image, yolo_model)
    
    found_marks = set() 
    
    for crop in crops:
        try:
            # Prefer predict(), fallback to ocr()
            if hasattr(ocr_engine, 'predict'):
                ocr_res = ocr_engine.predict(crop)
            else:
                ocr_res = ocr_engine.ocr(crop, cls=False)
        except Exception:
            continue
            
        if not ocr_res or not ocr_res[0]:
            continue
            
        # Extract text blocks
        try:
            # Handle different output structures between PaddleOCR versions
            if isinstance(ocr_res[0], dict) and 'rec_texts' in ocr_res[0]:
                merged_text = "".join([str(t) for t in ocr_res[0]['rec_texts'] if t])
            else:
                merged_text = "".join([item[1][0] for item in ocr_res[0] if item and len(item) > 1])
        except Exception:
            continue

        normalized = re.sub(r"\s+", "", merged_text.upper().replace("_", "-").replace("—", "-"))
        
        # Regex to find XX-XXXX patterns
        matches = re.findall(r'[A-Z0-9]{1,3}-[A-Z0-9]{3,5}', normalized)
        for match in matches:
            found_marks.add(match)

    return list(found_marks)

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="AeroSpotter local OCR pipeline")
    parser.add_argument("--image", required=True, help="Path to input image")
    parser.add_argument("--weights", required=True, help="Path to YOLO weights (.pt)")
    args = parser.parse_args()

    marks = extract_registration_marks(args.image, args.weights)
    
    if marks:
        print(f"Registration Marks: {', '.join(marks)}")
    else:
        print("Registration Marks: None")