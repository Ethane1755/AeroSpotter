from ultralytics import YOLO

# YOLO training script for the local OCR detector.
model = YOLO('yolov8n.pt')

results = model.train(
    data='training/data.yaml',
    imgsz=640,         
    batch=16,          
    device='mps',      
    project='AeroSpotter_YOLO',
    name='my_local_model'
)

print("training done.")
