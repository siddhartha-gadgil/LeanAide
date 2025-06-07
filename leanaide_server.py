import multiprocessing
import os
import pkgutil
import signal
import socket
import subprocess
import sys
import time
from pathlib import Path

STREAMLIT_PORT = 8501
LEANAIDE_PORT = int(os.environ.get("LEANAIDE_PORT", 7654))

home_dir = str(Path(__file__).resolve().parent)
serv_dir = os.path.join(home_dir, "server")

STREAMLIT_FILE = os.path.join(serv_dir, "streamlit_ui.py")
SERVER_FILE = os.path.join(serv_dir, "api_server.py")

def is_port_in_use(port: int) -> bool:
    """Check if a port is already in use"""
    with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as s:
        return s.connect_ex(('localhost', port)) == 0

def run_server_api():
    """Run Server server using uvicorn"""
    subprocess.run([sys.executable, SERVER_FILE])

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

def check_dependencies():
    """Check if required packages for streamlit are installed"""
    required_packages = {
        'streamlit',
        'pyperclip',
        'pillow',
        'python-dotenv',
        'requests'
    }
    
    missing_packages = []
    for package in required_packages:
        if not pkgutil.find_loader(package):
            missing_packages.append(package)
    
    return

if __name__ == "__main__":
    # Set up signal handler
    signal.signal(signal.SIGINT, signal_handler)

    # Parse command line arguments
    run_ui = "--ui" in sys.argv

    if run_ui:
        # Check dependencies
        missing = check_dependencies()
        if missing:
            print(f"\n\033[1;31mMissing required packages: {', '.join(missing)}\033[0m")
            print("\033[1;34mCheck out server/README.md for installation instructions and running the web streamlit server.\033[0m")
            sys.exit(1)

    print("\n\033[1;34mStarting servers\033[0m\n")
    print(f"\033[1;34mAPI Server:\033[0m http://{os.environ.get('HOST', 'localhost')}:{LEANAIDE_PORT}")
    
    # Start API server process
    serv_process = multiprocessing.Process(target=run_server_api)
    streamlit_process = None
    serv_process.start()
    
    if run_ui:
        time.sleep(0.5)  # Brief delay to ensure server starts first
        streamlit_process = multiprocessing.Process(target=run_streamlit)
        streamlit_process.start()
    else:
        print("\nRunning in API-only mode (no UI)")

    try:
        # Keep main process alive
        while True:
            pass
    except KeyboardInterrupt:
        print("\nShutting down...")
        serv_process.terminate()
        if run_ui:
            streamlit_process.terminate()
            streamlit_process.join()
        serv_process.join()
