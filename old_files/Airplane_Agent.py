import autogen
import asyncio
import os
from mcp import ClientSession, StdioServerParameters
from mcp.client.stdio import stdio_client

# Legacy AutoGen batch workflow for aircraft summarization.
# ==========================================
# 1. Setup the Brain (phi4-mini)
# ==========================================
my_llm_config = {
    "config_list": [
        {
            "model": "phi4-mini:latest",
            "api_key": "no-key-needed",
            "base_url": "http://localhost:11434/v1" 
        }
    ]
}

agent = autogen.AssistantAgent(
    name="Aviation_Analyst_Agent",
    llm_config=my_llm_config,
    system_message="""You are an enthusiastic aviation analyst!
    The user will provide you with JSON data containing airplane information.
    Please summarize this data professionally in English. Keep it concise.
    Only use provided data.
    Do NOT make up anything."""
)

user_proxy = autogen.UserProxyAgent(
    name="User",
    human_input_mode="NEVER", 
    max_consecutive_auto_reply=1, 
    code_execution_config={"use_docker": False} 
)

# ==========================================
# 2. Batch process photos via MCP
# ==========================================
async def run_mcp_batch_workflow(image_folder: str):
    print(f"Starting batch airplane image recognition system (Target folder: {image_folder})...\n")
    
    # Get all jpg or png images in the folder
    if not os.path.exists(image_folder):
        print(f"❌ Folder not found: {image_folder}")
        return
        
    image_files = [f for f in os.listdir(image_folder) if f.lower().endswith(('.png', '.jpg', '.jpeg'))]
    
    if not image_files:
        print("❌ No images found in the folder!")
        return

    server_params = StdioServerParameters(
        command="python",
        args=["Airplane_MCP.py"]
    )

    print("🔌 Connecting to MCP Server (Airplane_VLM_Server)...")
    
    async with stdio_client(server_params) as (read, write):
        async with ClientSession(read, write) as session:
            await session.initialize()
            print(f"✅ Successfully connected! Ready to process {len(image_files)} images.\n")
            
            # Start looping through each image
            for img_name in image_files:
                target_image = os.path.join(image_folder, img_name)
                print("="*50)
                print(f"⏳ [Analyzing] {target_image} ...")
                
                try:
                    # Call MCP tool
                    result = await session.call_tool(
                        "analyze_airplane_image", 
                        arguments={"image_path": target_image}
                    )
                    vlm_result = result.content[0].text
                    print(f"✅ [MCP Server Response]:\n{vlm_result}\n")
                    
                    await user_proxy.a_initiate_chat(
                        agent,
                        message=f"Here is the data for image {img_name}:\n{vlm_result}\nPlease briefly tell me what airplane this is!",
                        clear_history=True # [CRITICAL] Clear history so it doesn't mix up airplanes!
                    )
                    
                    await asyncio.sleep(4)
                    
                except Exception as e:
                    print(f"❌ Error processing {target_image}: {e}")

# ==========================================
# 3. Execute main program
# ==========================================
if __name__ == "__main__":

    target_folder = "test" 
    
    asyncio.run(run_mcp_batch_workflow(target_folder))