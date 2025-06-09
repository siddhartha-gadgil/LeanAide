# Code from Gemini 2.0 Flash Experimental
#
import http.server
import subprocess
import json
import os
import threading
import queue
import sys
import tempfile

PORT = int(os.environ.get("LEANAIDE_PORT", 7654))
HOST = os.environ.get("HOST", "localhost")  
COMMAND = os.environ.get("LEANAIDE_COMMAND", "lake exe leanaide_process")
for arg in sys.argv[1:]:
    COMMAND += " " + arg

LOG_FILE = os.path.join(tempfile.gettempdir(), "leanaide_streamlit_server.log")

print(f"Command: {COMMAND}")
process = None
process_lock = threading.Lock()
output_queue = queue.Queue()

def process_reader(process, output_queue):
    while True:
        line = process.stdout.readline()
        if not line:
            break  # Process terminated
        output_queue.put(line.strip())

def process_error_reader(process):  # New function for stderr
    while True:
        line = process.stderr.readline()
        if not line:
            break  # Process terminated
        print(f"Process stderr: {line.strip()}", file=sys.stderr)  # Print to server's stderr
        with open(LOG_FILE, "a") as f:  # Append to log file
            f.write(f"[Server stderr] {line.strip()}\n")
            f.flush()

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
                            COMMAND.split(),
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
                        self.wfile.write(f"Command not found: {COMMAND}".encode())
                        return
            try:
                json_data = json.loads(post_data)
                process.stdin.write(json.dumps(json_data) + '\n')
                process.stdin.flush()

                try:
                    output = output_queue.get(timeout=6000)  # Timeout after 6000 seconds
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
    print(f"Starting httpd on port {port}, command: {COMMAND}")
    try:
        httpd.serve_forever()
    except KeyboardInterrupt:
        print("Stopping server...")
    finally:
        global process
        if process:
            process.terminate()
            process.wait()
            print("Process terminated.")

if __name__ == "__main__":
    run(host=HOST)
