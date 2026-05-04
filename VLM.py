import os
import json
import PIL.Image
from google import genai


# 1. Initialization Settings
GOOGLE_API_KEY = "AIzaSyBJeYzSrdNnJBx8ApjViYBv4__9GdP9yuU" 
client = genai.Client(api_key=GOOGLE_API_KEY)

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
        print(f"Found {len(image_files)} images. Starting batch processing with Gemini 2.5 Flash model...\n")
        
        # Process each image using a for loop
        for image_name in image_files:
            image_path = os.path.join(folder_path, image_name)
            print("-" * 50)
            print(f" Analyzing image: {image_name}")
            
            try:
                # Load the image
                img = PIL.Image.open(image_path)
                
                # Send the request
                response = client.models.generate_content(
                    model='gemini-2.5-flash',
                    contents=[prompt_text, img]
                )
                
                # Clean and extract the JSON string
                result_text = response.text.strip().removeprefix('```json').removesuffix('```').strip()
                
                # Parse into a Dictionary
                result_dict = json.loads(result_text)
                
                # Print the results nicely
                print(f" Analysis successful!")
                print(f"   Airline: {result_dict.get('airline')}")
                print(f"   Aircraft Type: {result_dict.get('aircraft_type')}")
                print(f"   Registration Number: {result_dict.get('registration_number')}\n")
                
            except Exception as e:
                # If an image fails or the API disconnects, print the error but continue running
                print(f" Error processing {image_name}: {e}\n")
        
        print("-" * 50)
        print(" All images processed!")