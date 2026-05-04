import os
import json
import PIL.Image
from google import genai
from mcp.server.fastmcp import FastMCP

# ==========================================
# 1. 初始化 FastMCP 伺服器與 Gemini 客戶端
# ==========================================
# 建立一個名為 Airplane VLM 的 MCP Server
mcp = FastMCP("Airplane_VLM_Server")

# 這裡建議將 API Key 設為環境變數，若要直接貼上請記得不要外流
GOOGLE_API_KEY = os.environ.get("GEMINI_API_KEY", "AIzaSyBJeYzSrdNnJBx8ApjViYBv4__9GdP9yuU") 
client = genai.Client(api_key=GOOGLE_API_KEY)

# ==========================================
# 2. 定義 MCP Tool (Agent 會看到並呼叫這個工具)
# ==========================================
@mcp.tool()
def analyze_airplane_image(image_path: str) -> str:
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
    
    try:
        # 載入圖片並呼叫 Gemini 2.0 Flash
        img = PIL.Image.open(image_path)
        response = client.models.generate_content(
            model='gemini-2.5-flash',
            contents=[prompt_text, img]
        )
        
        # 清理並回傳純 JSON 字串給 Agent
        result_text = response.text.strip().removeprefix('```json').removesuffix('```').strip()
        return result_text
        
    except Exception as e:
        return json.dumps({"error": str(e)})

# ==========================================
# 3. 啟動伺服器 (使用標準輸入輸出 Stdio 模式)
# ==========================================
if __name__ == "__main__":
    # MCP Server 預設以 stdio 方式執行，方便外層的 Agent 直接串接溝通
    mcp.run()