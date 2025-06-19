import importlib.util
import multiprocessing
import os
import signal
import socket
import subprocess
import sys
import time
from pathlib import Path
from server.logging_utils import log_write, filter_logs, create_env_file, delete_env_file

STREAMLIT_PORT = 8501
LEANAIDE_PORT = int(os.environ.get("LEANAIDE_PORT", 7654))

home_dir = str(Path(__file__).resolve().parent)
serv_dir = os.path.join(home_dir, "server")

STREAMLIT_FILE = os.path.join(serv_dir, "streamlit_ui.py")
SERVER_FILE = os.path.join(serv_dir, "api_server.py")
COMMAND = os.environ.get("LEANAIDE_COMMAND", "lake exe leanaide_process")

for arg in sys.argv[1:]:
    if arg not in ["--ui", "--no-server", "--ns", "--help", "-h"]:
        COMMAND += " " + arg

# Ensure the environment file exists
create_env_file(fresh=True)

def is_port_in_use(port: int) -> bool:
    """Check if a port is already in use"""
    with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as s:
        return s.connect_ex(('localhost', port)) == 0

def run_server_api():
    """Run Server server using uvicorn"""
    process = subprocess.Popen(
        [sys.executable, SERVER_FILE, COMMAND],
        stderr=subprocess.PIPE,
        text=True
    )

    # Log stderr
    if process.stdout:
        for line in process.stdout:
            line = filter_logs(line.strip())
            print(line)
            log_write("Server Stdout", line, True)

    if process.stderr:
        for line in process.stderr:
            line = filter_logs(line.strip()) 
            print(line)
            log_write("Server Stderr", line, True)

def run_streamlit():
    """Run Streamlit app on port STREAMLIT_PORT only"""
    if is_port_in_use(STREAMLIT_PORT):
        return

    process = subprocess.Popen([
        sys.executable, "-m",
        "streamlit", "run", STREAMLIT_FILE,
        f"--server.port={STREAMLIT_PORT}",
        "--server.headless=true",
        "--browser.gatherUsageStats=false"
    ], stderr=subprocess.PIPE, text=True)

    # Write stderr to a file that Streamlit can read
    for line in process.stderr:
        line = filter_logs(line.strip())
        print("Streamlit Stderr", line)
        log_write("Streamlit Stderr", line, log_file=True)

    # Force Streamlit to use only port STREAMLIT_PORT
    subprocess.run([
        sys.executable, "-m",
        "streamlit", "run", STREAMLIT_FILE,
        f"--server.port={STREAMLIT_PORT}",
        "--server.headless=true",
        "--browser.gatherUsageStats=false"
    ])
    if process.stdout:
        for line in process.stdout:
            line = filter_logs(line.strip())
            print("Streamlit Stdout", line)
            log_write("Streamlit Stdout", line, log_file=True)

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
        required_packages = [pkg.replace('-', '_') for pkg in required_packages]
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
            print("Usage: leanaide_server.py [--ui] [--no-server | --ns] [--help | -h] [additional arguments]")
            print("Options:")
            print("  --ui                   Run the Streamlit UI (default: API server only)")
            print("  --no-server | --ns     Don't run the backend server (use with --ui)")
            print("  --help | -h            Show this help message")
            print("Any other argument will be passed on to the process `lake exe leanaide_process` as it is. Check out `lake exe leanaide_process --help` for more details.")
            sys.exit(0)

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

    delete_env_file()  # Clean up environment file