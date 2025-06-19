import logging
from collections import deque
import tempfile
import os
import time
import json
from pathlib import Path

# In-memory log storage with max size (1000 lines by default)
LOG_BUFFER_LINES = 1000
LOG_BUFFER = deque(maxlen=LOG_BUFFER_LINES)
LEANAIDE_LOG_FILE = tempfile.gettempdir() + "/leanaide.log"
MAX_FILE_LINES = 10000

## Environment File
HOMEDIR = str(Path(__file__).resolve().parent.parent) # LeanAide root
ENV_FILE = os.path.join(HOMEDIR, "server", "private", "env_vars.json")

# Custom log handler that writes to LOG_BUFFER
class LogBufferHandler(logging.Handler):
    def __init__(self, log_buffer):
        super().__init__()
        self.log_buffer = log_buffer

    def emit(self, record):
        try:
            log_entry = self.format(record)
            self.log_buffer.append(log_entry + "\n")
            # Append to file
            self._write_to_file(log_entry)
        except Exception:
            self.handleError(record)

    def _write_to_file(self, log_entry):
        """Handle file writing with rotation"""
        try:
            # Check if file exists and count lines
            line_count = 0
            if os.path.exists(LEANAIDE_LOG_FILE):
                with open(LEANAIDE_LOG_FILE, 'r') as f:
                    line_count = sum(1 for _ in f)
            
            # Rotate if needed
            if line_count >= MAX_FILE_LINES:
                rotated_file = f"{LEANAIDE_LOG_FILE}.{int(time.time())}"
                os.rename(LEANAIDE_LOG_FILE, rotated_file)

            # Write new entry
            with open(LEANAIDE_LOG_FILE, 'a') as f:
                f.write(log_entry + "\n")
        except Exception as e:
            logging.error(f"Error writing to log file: {e}")

def setup_logger(name: str):
    """Setup logger that writes to LOG_BUFFER"""
    logger = logging.getLogger(name)
    logger.setLevel(logging.INFO)

    # Remove existing handlers to avoid duplicates
    logger.handlers.clear()

    # Add our custom handler
    handler = LogBufferHandler(LOG_BUFFER)
    formatter = logging.Formatter('[%(asctime)s] [%(name)s] %(message)s')
    handler.setFormatter(formatter)
    logger.addHandler(handler)

    return logger

def filter_logs(msg: str):
    redacted_msg = msg
    for sensitive_word in ["api_key", "auth_key", "authorization"]:
        if sensitive_word in msg.lower():
            # Find the position of the sensitive word
            pos = msg.lower().find(sensitive_word)
            allow_char = 10  # Give some characters of allowing
            
            # Detect till "--" for redaction
            start_redact = pos + len(sensitive_word) + allow_char
            next_param_pos = msg.find("--", start_redact)
            
            if next_param_pos != -1:
                redacted_msg = msg[:start_redact] + "***REDACTED***" + msg[next_param_pos - 1:]
            else:
                redacted_msg = msg[:start_redact] + "***REDACTED***"
            break
    
    return redacted_msg

def log_write(proc_name: str, msg: str, log_file: bool = False):
    msg = filter_logs(msg)
    logger = setup_logger(proc_name)
    if log_file:
        # Directly write to file when file=True is specified
        with open(LEANAIDE_LOG_FILE, 'a') as f:
            if "Server ready. Waiting for input".lower() in msg.lower():
                f.write(f"[{time.strftime('%Y-%m-%d %H:%M:%S')}] [{proc_name}] {"#"*len(msg)}\n")
                f.write(f"[{time.strftime('%Y-%m-%d %H:%M:%S')}] [{proc_name}] {msg}\n")
                f.write(f"[{time.strftime('%Y-%m-%d %H:%M:%S')}] [{proc_name}] {"#"*len(msg)}\n")
            else: 
                f.write(f"[{time.strftime('%Y-%m-%d %H:%M:%S')}] [{proc_name}] {msg}\n")
    else:
        logger.error(msg)

def log_buffer_clean(log_file: bool = False):
    if log_file:
        try:
            if os.path.exists(LEANAIDE_LOG_FILE):
                with open(LEANAIDE_LOG_FILE, 'w') as f:
                    f.write("")
        except Exception as e:
            log_write("log_clean", f"Error removing log file: {e}")
    else:
        try:
            LOG_BUFFER.clear()
        except Exception as e:
            log_write("log_clean", f"Error clearing log buffer: {e}")

def log_server(log_file: bool = False, order: bool = True):
    """
    Read from the in-memory log buffer and file in reverse order
    Args:
        log_file (bool): If True, read from the log file instead of in-memory buffer.
        order (bool): If True, return logs in reverse order (newest first).
    """
    # First get in-memory logs
    log_content = []
    if not log_file:
        if LOG_BUFFER:
            if order:
                log_content.extend(reversed(LOG_BUFFER))
            else:
                log_content.extend(LOG_BUFFER)
 
    else:
        # Then get file logs if they exist
        if os.path.exists(LEANAIDE_LOG_FILE):
            try:
                with open(LEANAIDE_LOG_FILE, 'r') as f:
                    file_lines = f.readlines()
                    # Take last 1000 lines from file
                    recent_lines = file_lines[-LOG_BUFFER_LINES:]
                    if order:
                        log_content.extend(reversed(recent_lines))
                    else:
                        log_content.extend(recent_lines)
            except Exception as e:
                log_write("log_server", f"Error reading log file: {e}")

    if not log_content:
        return "No logs available yet."

    return "".join(log_content)

## These are not related to logging, but Environment variables based functions
def create_env_file(fresh: bool = False):
    """
    Create the env_vars.json file if it does not exist.
    """
    # Create the directory if it doesn't exist
    os.makedirs(os.path.dirname(ENV_FILE), exist_ok=True)
    initial_data = {
        "LEANAIDE_COMMAND": "lake exe leanaide_process",
        "LEANAIDE_PORT": "7654",
    }
    if fresh:
        with open(ENV_FILE, 'w') as f:
            json.dump(initial_data, f, indent=4)
    
    else:
        if not os.path.exists(ENV_FILE):
            with open(ENV_FILE, 'w') as f:
                json.dump(initial_data, f, indent=4)

def get_env(var:str = "", default=None):
    """
    Get environment variable with a default value.
    """
    create_env_file()
    with open(ENV_FILE, 'r') as f:
        env_vars = json.load(f)
    if var:
        return env_vars.get(var, default)
    else:
        return env_vars

def post_env(var: str, value: str):
    """
    Post environment variable to the env_vars.json file.
    """
    create_env_file()
    with open(ENV_FILE, 'r') as f:
        env_vars = json.load(f) 
    env_vars[var] = value 
    with open(ENV_FILE, 'w') as f:
        json.dump(env_vars, f, indent=4) 

def post_env_args(provider: str, auth_key: str, **kwargs):
    """
    Kwargs:
    - model: str, the model to use for the provider
    - temperature: float, the temperature for the model
    """
    if provider.lower() == "gemini":
        post_env("GEMINI_API_KEY", auth_key)
        post_env("LEANAIDE_PROVIDER", "gemini")
    elif provider.lower() == "openrouter":
        post_env("OPENROUTER_API_KEY", auth_key)
        post_env("LEANAIDE_PROVIDER", "openrouter")
    elif provider.lower() == "deepinfra":
        post_env("DEEPINFRA_API_KEY", auth_key)
        post_env("LEANAIDE_PROVIDER", "deepinfra")
    else: # In case of "openai" and default
        post_env("OPENAI_API_KEY", auth_key)
        post_env("LEANAIDE_PROVIDER", "openai")

    for key, value in kwargs.items():
        post_env(f"LEANAIDE_{key.upper()}", value)

def delete_env_file():
    """
    Delete the env_vars.json file.
    """
    if os.path.exists(ENV_FILE):
        os.remove(ENV_FILE)
        log_write("delete_env_file", "Environment file deleted successfully.")
    else:
        log_write("delete_env_file", "Environment file does not exist.")