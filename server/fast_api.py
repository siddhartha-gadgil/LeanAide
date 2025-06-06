import json
import os
import queue
import subprocess
import sys
import threading

from fastapi import FastAPI, HTTPException, Request

app = FastAPI()

# Configuration from environment variables
PORT = int(os.environ.get("LEANAIDE_PORT", 7654))
HOST = os.environ.get("HOST", "localhost") 
COMMAND = os.environ.get("LEANAIDE_COMMAND", "lake exe leanaide_process")
for arg in sys.argv[1:]:
    COMMAND += " " + arg

print(f"Starting server with command: {COMMAND}")

# Process management
process = None
process_lock = threading.Lock()
output_queue = queue.Queue()

def process_reader(process, output_queue):
    """Read stdout from the process and put into queue"""
    while True:
        line = process.stdout.readline()
        if not line:  # Process terminated
            break
        output_queue.put(line.strip())

def process_error_reader(process):
    """Read stderr from the process and log it"""
    while True:
        line = process.stderr.readline()
        if not line:  # Process terminated
            break
        print(f"Process stderr: {line.strip()}", file=sys.stderr)

def start_process():
    """Start the subprocess with proper pipes"""
    global process
    try:
        process = subprocess.Popen(
            COMMAND.split(),
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            bufsize=1,  # Line buffering
            universal_newlines=True
        )
        # Start reader threads
        threading.Thread(
            target=process_reader,
            args=(process, output_queue),
            daemon=True
        ).start()
        threading.Thread(
            target=process_error_reader,
            args=(process,),
            daemon=True
        ).start()
        return True
    except FileNotFoundError:
        return False

@app.post("/")
async def handle_request(request: Request):
    """Handle POST requests from Streamlit frontend"""
    global process
    
    # Get JSON payload
    try:
        request_payload = await request.json()
    except json.JSONDecodeError:
        raise HTTPException(status_code=400, detail="Invalid JSON payload")
    
    # Process management
    with process_lock:
        if process is None or process.poll() is not None:
            if not start_process():
                raise HTTPException(
                    status_code=500,
                    detail=f"Failed to start process: {COMMAND}"
                )
    
    # Send data to process and get response
    try:
        process.stdin.write(json.dumps(request_payload) + '\n')
        process.stdin.flush()
        
        try:
            output = output_queue.get(timeout=60)  # 60 second timeout
            return output
        except queue.Empty:
            raise HTTPException(status_code=504, detail="Process timeout")
            
    except BrokenPipeError:
        with process_lock:
            process = None
        raise HTTPException(status_code=500, detail="Process terminated unexpectedly")
    except Exception as e:
        raise HTTPException(status_code=500, detail=str(e))

@app.get("/health")
async def health_check():
    """Health check endpoint"""
    return {
        "status": "running",
        "command": COMMAND,
        "process_alive": process is not None and process.poll() is None
    }

@app.on_event("shutdown")
def shutdown_event():
    """Cleanup on server shutdown"""
    if process:
        process.terminate()
        process.wait()
        print("Process terminated during shutdown")
