import multiprocessing
import os
import importlib.util
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
    required_packages = []
    try:
        with open(os.path.join(str(serv_dir), "requirements.txt"), "r") as f:
            required_packages = f.read().splitlines()
        # Clean up package names (remove version specifiers and comments)
        required_packages = [
            pkg.split('==')[0].split('>')[0].split('<')[0].split('[')[0].strip()
            for pkg in required_packages
            if pkg.strip() and not pkg.strip().startswith('#')
        ]
    except Exception as e:
        print(f"Error reading requirements.txt: {e}")
    
    missing_packages = []
    for package in required_packages:
        if "dotenv" in package:
            package = "dotenv"
        spec = importlib.util.find_spec(package)
        if spec is None:
            missing_packages.append(package)
    
    return missing_packages

if __name__ == "__main__":
    # Set up signal handler
    signal.signal(signal.SIGINT, signal_handler)

    # Parse command line arguments
    if len(sys.argv) > 1:
        if sys.argv[1] in ["--help", "-h"]:
            print(f"Usage: {sys.executable} leanaide_server.py [--ui] [--no-server | --ns] [--help | -h]")
            print("Options:")
            print("  --ui                   Run the Streamlit UI (default: API server only)")
            print("  --no-server | --ns     Don't run the backend server (use with --ui)")
            print("  --help | -h            Show this help message")
            sys.exit(0)
        elif sys.argv[1] not in ["--ui", "-h", "--help", "--no-server", "--ns"]:
            print(f"Unknown argument: {sys.argv[1]}")
            print("Use --help for usage information.")
            sys.exit(1)
    
    run_ui = "--ui" in sys.argv
    run_server = "--no-server" not in sys.argv and "--ns" not in sys.argv
    missing_st = True

    if run_ui:
        print("\nRunning Streamlit UI.")
        # Check dependencies
        if missing_packages := check_dependencies():
            print(f"\033[1;31mMissing required packages:\033[0m {', '.join(missing_packages)}")
            print("Check out \033[1;34mserver/README.md \033[0m for installation instructions and running the web streamlit server.")
            print("Skipping Streamlit UI...")
        else:
            missing_st = False
            print("\033[1;32mDependencies satisfied. Streamlit UI can be run.\033[0m")

    print("\n\033[1;34mStarting servers:\033[0m")
    
    # Start processes
    serv_process = None
    streamlit_process = None
    
    if run_server:
        print(f"\033[1;34mAPI Server:\033[0m http://{os.environ.get('HOST', 'localhost')}:{LEANAIDE_PORT}\n")
        serv_process = multiprocessing.Process(target=run_server_api)
        serv_process.start()
    else:
        print("\033[1;34mRunning without API server\033[0m\n")

    if run_ui and not missing_st:
        if run_server:
            time.sleep(0.5)  # Brief delay to ensure server starts first
        streamlit_process = multiprocessing.Process(target=run_streamlit)
        streamlit_process.start()
    elif not run_server and not run_ui:
        print("\033[1;33mWarning: No services specified. Use --ui and/or don't use --no-server\033[0m")
        sys.exit(0)

    try:
        # Keep main process alive
        while True:
            pass
    except KeyboardInterrupt:
        print("\nShutting down...")
        if serv_process:
            serv_process.terminate()
            serv_process.join()
        if streamlit_process:
            streamlit_process.terminate()
            streamlit_process.join()