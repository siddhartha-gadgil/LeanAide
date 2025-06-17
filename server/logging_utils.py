import logging
from collections import deque
# In-memory log storage with max size (1000 lines by default)
LOG_BUFFER = deque(maxlen=1000) 

# Custom log handler that writes to LOG_BUFFER
class LogBufferHandler(logging.Handler):
    def __init__(self, log_buffer):
        super().__init__()
        self.log_buffer = log_buffer
    
    def emit(self, record):
        try:
            log_entry = self.format(record)
            self.log_buffer.append(log_entry + "\n")
        except Exception:
            self.handleError(record)

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

def log_write(proc_name: str, msg: str):
    logger = setup_logger(proc_name)
    logger.error(msg)  

def log_buffer_clean():
    try:
        LOG_BUFFER.clear()
    except Exception as e:
        log_write("log_clean", f"Error clearing log buffer: {e}")

def log_server():
    """Read from the in-memory log buffer"""
    if not LOG_BUFFER:
        return "No logs available yet."
    return "".join(reversed(LOG_BUFFER))