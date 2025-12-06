import http.server
import json
import os
import queue
import subprocess
import sys
import threading
from socketserver import ThreadingMixIn

import torch
from sentence_transformers import SentenceTransformer

sys.path.insert(0, "SimilaritySearch/")
import similarity_search

from logging_utils import (delete_env_file, filter_logs, get_env, log_write,
                           post_env)

# from huggingface_hub import login

# login()


PORT = int(os.environ.get("LEANAIDE_PORT", 7654))
HOST = os.environ.get("HOST", "0.0.0.0")
COMMAND = os.environ.get("LEANAIDE_COMMAND", "lake exe leanaide_process")
for arg in sys.argv[1:]:
    COMMAND = " " + arg

# Config model
MODEL_NAME = "BAAI/bge-base-en-v1.5"

# Lazy load model - will be loaded in background after server starts
MODEL = None
MODEL_LOAD_LOCK = threading.Lock()

def lazy_load_model():
    """Lazy load the model on first use"""
    global MODEL
    if MODEL is None:
        with MODEL_LOAD_LOCK:
            if MODEL is None:  # Double-check locking
                device = torch.device('cuda') if torch.cuda.is_available() else torch.device('cpu')
                print(f"Loading model: {MODEL_NAME} on {device}")
                MODEL = SentenceTransformer(MODEL_NAME, device=device, model_kwargs={"dtype": torch.bfloat16})
                print("Model loaded!")
                # Check and create indexes after model loads
                model_name_safe = MODEL_NAME.replace('/', '-')
                similarity_search.run_checks(MODEL, model_name_safe)
    return MODEL

def init_model_bg():
    """Start loading model in background thread"""
    def load():
        lazy_load_model()
    threading.Thread(target=load, daemon=True).start()
    print(f"Model {MODEL_NAME} will load in background...")

def get_env_args():
    """Get environment variables for the server, mainly LLM details"""
    env_args = {}
    for key, value in get_env().items():
        if key.startswith("LEANAIDE_") and key not in ["LEANAIDE_COMMAND", "LEANAIDE_PORT", "LEANAIDE_PROVIDER"]:
            key = key.replace("LEANAIDE_", "").lower()
            env_args[key] = value
        elif key.endswith("API_KEY"):
            provider = get_env("LEANAIDE_PROVIDER", "openai").lower()
            if provider == "openai" and key == "OPENAI_API_KEY":
                env_args["auth_key"] = value
            elif provider == "gemini" and key == "GEMINI_API_KEY":
                env_args["auth_key"] = value
            elif provider == "openrouter" and key == "OPENROUTER_API_KEY":
                env_args["auth_key"] = value
            elif provider == "deepinfra" and key == "DEEPINFRA_API_KEY":
                env_args["auth_key"] = value
                 
        else:
            pass # Ignore others

    return env_args

def updated_leanaide_command():
    COMMAND = "lake exe leanaide_process" # Make Fresh command
    existing_flags = set(COMMAND.split())
    for key, value in get_env_args().items():
        flag = f"--{key}"
        if value:
            if flag not in existing_flags:
                COMMAND += f" {flag} {value}"
            else:
                COMMAND = COMMAND.replace(f"{flag} {existing_flags.intersection({value}).pop()}", f"{flag} {value}")

    post_env("LEANAIDE_COMMAND", COMMAND)
    return COMMAND


def hide_sensitive_command():
    # Hide auth_key value for security
    command = updated_leanaide_command()
    if "--auth_key" in command:
        auth_key_part = command.split("--auth_key ")[1].split()[0]
        hidden_key = auth_key_part[:6] + "...key_hidden..." if len(auth_key_part) > 6 else auth_key_part
        command = command.replace(auth_key_part, hidden_key)

    return command

command = hide_sensitive_command()

print(f"Command: {command}")
log_write("Server command", command, log_file=True)
process = None
process_lock = threading.Lock()
output_queue = queue.Queue()

def process_reader(process, output_queue, request_logs=None):
    """Read stdout and optionally capture to request_logs"""
    while True:
        line = process.stdout.readline()
        if not line:
            break  # Process terminated
        output_queue.put(line.strip())
        line_filtered = filter_logs(line.strip())
        print(f"process stdout: {line_filtered}")
        log_write("Server stdout", line_filtered, log_file=True)
        if request_logs is not None and line_filtered:
            request_logs.append(f"[stdout] {line_filtered}")

def process_error_reader(process, request_logs=None):
    """Read stderr and optionally capture to request_logs"""
    while True:
        line = process.stderr.readline()
        if not line:
            break  # Process terminated
        line_filtered = filter_logs(line.strip())
        print(f"process stderr: {line_filtered}")
        log_write("Server stderr", line_filtered, log_file=True)
        if request_logs is not None and line_filtered:
            # Skip the "Server ready" spam
            if "Server ready. Waiting for input" not in line_filtered:
                request_logs.append(f"[stderr] {line_filtered}")

class ThreadingHTTPServer(ThreadingMixIn, http.server.HTTPServer):
    # Handle requests in a separate thread.
    pass

class Handler(http.server.BaseHTTPRequestHandler):
    def do_POST(self):

        # PATH TO SIMILARITY SEARCH
        if self.path == '/run-sim-search':
            try:
                content_length = int(self.headers['Content-Length'])
                post_data = self.rfile.read(content_length).decode('utf-8')
                data = json.loads(post_data)
                print(f"Received similarity search request: {data}", file=sys.stderr)
                if not all(k in data for k in ['num', 'query', 'descField']):
                    self.send_response(400)
                    self.send_header('Content-type', 'application/json')
                    self.end_headers()
                    error_msg = "error : Missing parameters. Required: 'num', 'query', 'descField'"
                    self.wfile.write(error_msg.encode('utf-8'))
                    print(f"ERROR: 400 Bad Request - {error_msg}", file=sys.stderr)
                    return # Exit after handling

                # Load model if not already loaded
                model = lazy_load_model()
                model_name_safe = MODEL_NAME.replace('/', '-')
                
                # Call the main function from similarity_search
                result = similarity_search.run_similarity_search(model, model_name_safe, data['num'], data['query'], data['descField'])

                self.send_response(200)
                self.send_header('Content-type', 'application/json')
                self.end_headers()
                response_body = {"status": "success", "output": result}
                self.wfile.write(json.dumps(response_body).encode('utf-8'))
            
            except Exception as e:
                self.send_response(500)
                self.send_header('Content-type', 'application/json')
                self.end_headers()
                error_msg = f"error: {str(e)}"
                self.wfile.write(error_msg.encode('utf-8'))
                print(f"ERROR: 500 Internal Server Error - {error_msg}", file=sys.stderr)

            return

        # NORMAL SERVER CODE BELOW
        global process, process_lock
        content_length = int(self.headers['Content-Length'])
        post_data = self.rfile.read(content_length).decode('utf-8')
        
        # Per-request log capture (simple list of strings)
        request_logs = []

        try:
            with process_lock:
                if process is None or process.poll() is not None:
                    try:
                        request_logs.append("[info] Starting new process")
                        process = subprocess.Popen(
                            updated_leanaide_command().split(),
                            stdin=subprocess.PIPE,
                            stdout=subprocess.PIPE,
                            stderr=subprocess.PIPE,
                            text=True,
                            bufsize=1 # Line buffering
                        )
                        threading.Thread(target=process_reader, args=(process, output_queue, request_logs), daemon=True).start()
                        threading.Thread(target=process_error_reader, args=(process, request_logs), daemon=True).start()
                    except FileNotFoundError:
                        request_logs.append(f"[error] Command not found: {updated_leanaide_command()}")
                        self.send_response(500)
                        self.send_header('Content-type', 'application/json')
                        self.end_headers()
                        error_response = {
                            "error": f"Command not found: {updated_leanaide_command()}",
                            "logs": "\n".join(request_logs)
                        }
                        self.wfile.write(json.dumps(error_response).encode())
                        return
            try:
                json_data = json.loads(post_data)
                
                request_logs.append("[info] Sending request to process")
                process.stdin.write(json.dumps(json_data) + '\n')
                process.stdin.flush()

                try:
                    output = output_queue.get(timeout=6000)  # Timeout after 6000 seconds
                    request_logs.append("[info] Received response from process")
                    self.send_response(200)
                    self.send_header('Content-type', 'application/json')
                    self.end_headers()
                    
                    # Parse the output and wrap with logs
                    try:
                        result_data = json.loads(output)
                    except json.JSONDecodeError:
                        result_data = output
                    
                    response = {
                        "result": result_data,
                        "logs": "\n".join(request_logs)
                    }
                    
                    self.wfile.write(json.dumps(response).encode())
                except queue.Empty:
                    request_logs.append("[error] Process timed out after 600s")
                    self.send_response(504)
                    self.send_header('Content-type', 'application/json')
                    self.end_headers()
                    error_response = {
                        "error": "Process timed out",
                        "logs": "\n".join(request_logs)
                    }
                    self.wfile.write(json.dumps(error_response).encode())
            except json.JSONDecodeError:
                request_logs.append("[error] Invalid JSON in request")
                self.send_response(400)
                self.send_header('Content-type', 'application/json')
                self.end_headers()
                error_response = {
                    "error": "Invalid JSON",
                    "logs": "\n".join(request_logs)
                }
                self.wfile.write(json.dumps(error_response).encode())
            except BrokenPipeError:
                request_logs.append("[error] Process crashed (broken pipe)")
                with process_lock:
                    process = None
                self.send_response(500)
                self.send_header('Content-type', 'application/json')
                self.end_headers()
                error_response = {
                    "error": "Process crashed",
                    "logs": "\n".join(request_logs)
                }
                self.wfile.write(json.dumps(error_response).encode())
        except Exception as e:
            request_logs.append(f"[error] Exception: {str(e)}")
            self.send_response(500)
            self.send_header('Content-type', 'application/json')
            self.end_headers()
            error_response = {
                "error": str(e),
                "logs": "\n".join(request_logs)
            }
            self.wfile.write(json.dumps(error_response).encode())

    def do_GET(self):
        self.send_response(200)
        self.send_header('Content-type', 'text/plain')
        self.end_headers()
        self.wfile.write("Send a POST request with JSON to interact with the process.".encode())


def run(server_class=http.server.HTTPServer, handler_class=Handler, port=PORT, host=HOST):
    server_address = (host, port) # Use the host
    ThreadingHTTPServer.allow_reuse_address = True
    httpd = ThreadingHTTPServer(server_address, handler_class)
    print(f"Starting httpd on port {port}, command: {hide_sensitive_command()}")
    
    # Start loading model in background after server is ready
    init_model_bg()
    print("\nServer is ready...\n")
    
    try:
        httpd.serve_forever()
    except KeyboardInterrupt:
        delete_env_file()
        print("Stopping server...")
    finally:
        global process
        if process:
            process.terminate()
            process.wait()
            delete_env_file()
            print("Process terminated.")

if __name__ == "__main__":
    run(host=HOST)
