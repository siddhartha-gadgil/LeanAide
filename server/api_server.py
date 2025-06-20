# Code from Gemini 2.0 Flash Experimental
#
import http.server
import json
import os
import queue
import subprocess
import sys
import threading

from logging_utils import log_write, filter_logs, get_env, post_env, delete_env_file

PORT = int(os.environ.get("LEANAIDE_PORT", 7654))
HOST = os.environ.get("HOST", "localhost")
COMMAND = os.environ.get("LEANAIDE_COMMAND", "lake exe leanaide_process")
for arg in sys.argv[1:]:
    COMMAND = " " + arg

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

command = updated_leanaide_command()
# Hide auth_key value for security
if "--auth_key" in command:
    auth_key_part = command.split("--auth_key ")[1].split()[0]
    hidden_key = auth_key_part[:6] + "...key_hidden..." if len(auth_key_part) > 6 else auth_key_part
    command = command.replace(auth_key_part, hidden_key)
print(f"Command: {command}")
log_write("Server command", command, log_file=True)
process = None
process_lock = threading.Lock()
output_queue = queue.Queue()

def process_reader(process, output_queue):
    while True:
        line = process.stdout.readline()
        if not line:
            break  # Process terminated
        output_queue.put(line.strip())
        line = filter_logs(line.strip())
        print(f"process stdout: {line.strip()}")
        log_write("Server stdout", line.strip(), log_file=True)

def process_error_reader(process):  # New function for stderr
    while True:
        line = process.stderr.readline()
        if not line:
            break  # Process terminated
        line = filter_logs(line.strip())
        print(f"process stderr: {line.strip()}")
        log_write("Server stderr", line.strip(), log_file=True)

class Handler(http.server.BaseHTTPRequestHandler):
    def do_POST(self):
        global process, process_lock
        content_length = int(self.headers['Content-Length'])
        post_data = self.rfile.read(content_length).decode('utf-8')

        try:
            with process_lock:
                if process is None or process.poll() is not None:
                    try:
                        process = subprocess.Popen(
                            updated_leanaide_command().split(),
                            stdin=subprocess.PIPE,
                            stdout=subprocess.PIPE,
                            stderr=subprocess.PIPE,
                            text=True,
                            bufsize=1 # Line buffering
                        )
                        threading.Thread(target=process_reader, args=(process, output_queue), daemon=True).start()
                        threading.Thread(target=process_error_reader, args=(process,), daemon=True).start()  # Start stderr thread
                    except FileNotFoundError:
                        self.send_response(500)
                        self.send_header('Content-type', 'text/plain')
                        self.end_headers()
                        self.wfile.write(f"Command not found: {updated_leanaide_command()}".encode())
                        return
            try:
                json_data = json.loads(post_data)
                process.stdin.write(json.dumps(json_data) + '\n')
                process.stdin.flush()

                try:
                    output = output_queue.get(timeout=600)  # Timeout after 600 seconds
                    self.send_response(200)
                    self.send_header('Content-type', 'application/json')
                    self.end_headers()
                    self.wfile.write(output.encode())
                except queue.Empty:
                    self.send_response(504)  # Gateway Timeout
                    self.send_header('Content-type', 'text/plain')
                    self.end_headers()
                    self.wfile.write("Process timed out".encode())
            except json.JSONDecodeError:
                self.send_response(400)
                self.send_header('Content-type', 'text/plain')
                self.end_headers()
                self.wfile.write("Invalid JSON".encode())
            except BrokenPipeError:
                with process_lock:
                    process = None
                self.send_response(500)
                self.send_header('Content-type', 'text/plain')
                self.end_headers()
                self.wfile.write("Process crashed".encode())
        except Exception as e:
            self.send_response(500)
            self.send_header('Content-type', 'text/plain')
            self.end_headers()
            self.wfile.write(str(e).encode())

    def do_GET(self):
        self.send_response(200)
        self.send_header('Content-type', 'text/plain')
        self.end_headers()
        self.wfile.write("Send a POST request with JSON to interact with the process.".encode())


def run(server_class=http.server.HTTPServer, handler_class=Handler, port=PORT, host=HOST):
    server_address = (host, port) # Use the host
    httpd = server_class(server_address, handler_class)
    print(f"Starting httpd on port {port}, command: {updated_leanaide_command()}")
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
