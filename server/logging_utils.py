import logging
from collections import deque
import tempfile
import os
import time

# In-memory log storage with max size (1000 lines by default)
LOG_BUFFER_LINES = 1000
LOG_BUFFER = deque(maxlen=LOG_BUFFER_LINES)
LEANAIDE_LOG_FILE = tempfile.gettempdir() + "/leanaide.log"
MAX_FILE_LINES = 10000

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
    formatter = logging.Formatter('[%(name)s] %(message)s')
    handler.setFormatter(formatter)
    logger.addHandler(handler)

    return logger

def log_write(proc_name: str, msg: str, log_file: bool = False):
    logger = setup_logger(proc_name)
    if log_file:
        # Directly write to file when file=True is specified
        with open(LEANAIDE_LOG_FILE, 'a') as f:
            f.write(f"[{proc_name}] {msg}\n")
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