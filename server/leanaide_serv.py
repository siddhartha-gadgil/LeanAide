import multiprocessing
import os
import signal
import socket
import subprocess
import sys
import time
from pathlib import Path

STREAMLIT_PORT = 8501
FASTAPI_PORT = 7654

serv_dir = str(Path(__file__).resolve().parent)
STREAMLIT_FILE = os.path.join(serv_dir, "streamlit_ui.py") 
FASTAPI_FILE = os.path.join(serv_dir, "fast_api.py").split("/")[-1].split(".")[0] # fast_api

def is_port_in_use(port: int) -> bool:
    """Check if a port is already in use"""
    with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as s:
        return s.connect_ex(('localhost', port)) == 0

def run_fastapi():
    """Run FastAPI server using uvicorn"""
    # This requires `fast_api.py` in the same directory, and `fast_api` name as is.
    subprocess.run([sys.executable, "-m", "uvicorn", f"{FASTAPI_FILE}:app", "--reload", "--port", str(FASTAPI_PORT)])

def run_streamlit():
    """Run Streamlit app on port STREAMLIT_PORT only"""
    # STREAMLIT_PORT is used by our main Streamlit, this prevents another instance of same streamlit being made
    if is_port_in_use(STREAMLIT_PORT):
        # print("❌ Port STREAMLIT_PORT is already in use! Close other Streamlit instances first.")
        return
    
    # Force Streamlit to use only port STREAMLIT_PORT
    subprocess.run([
        sys.executable, "-m",
        "streamlit", "run", STREAMLIT_FILE,
        f"--server.port={STREAMLIT_PORT}",
        "--server.headless=true",
        "--browser.gatherUsageStats=false"
    ])

def signal_handler(sig, frame):
    """Handle Ctrl+C to terminate both processes"""
    print("\nShutting down servers...")
    sys.exit(0)

if __name__ == "__main__":
    # Set up signal handler
    signal.signal(signal.SIGINT, signal_handler)

    print("\n\033[1;34mStarting servers (single-port mode)\033[0m\n")
    print(f"\033[1;34mFastAPI:\033[0m http://localhost:{FASTAPI_PORT}")
    print(f"\033[1;34mStreamlit:\033[0m http://localhost:{STREAMLIT_PORT}\n")

    # Start processes
    fastapi_process = multiprocessing.Process(target=run_fastapi)
    streamlit_process = multiprocessing.Process(target=run_streamlit)

    fastapi_process.start()
    time.sleep(0.5)  # Brief delay to ensure FastAPI starts first
    streamlit_process.start()

    try:
        # Keep main process alive
        while True:
            pass
    except KeyboardInterrupt:
        print("\nShutting down...")
        fastapi_process.terminate()
        streamlit_process.terminate()
        fastapi_process.join()
        streamlit_process.join()
