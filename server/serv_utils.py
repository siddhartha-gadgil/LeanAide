import ast
import os
from pathlib import Path
import json
import shlex
from typing import Any, Tuple, Type
import streamlit as st
from st_copy import copy_button
from collections import deque

HOST = os.environ.get("HOST", "localhost")  
HOMEDIR = str(Path(__file__).resolve().parent.parent) # LeanAide root
schema_path = os.path.join(str(HOMEDIR), "resources", "PaperStructure.json")
SCHEMA_JSON = json.load(open(schema_path, "r", encoding="utf-8"))

# Lean Checker Tasks
TASKS = {
    "Echo": {
        "task_name": "echo",
        "input": {"data": "String"},
        "output": {"data": "String"}
    },
    "Translate Theorem": {
        "task_name": "translate_thm",
        "input": {"text": "String"},
        "output": {"theorem": "String"},
        "parameters": {
            "greedy": "Bool (default: true)",
            "fallback": "Bool (default: true)",
        },
    },
    "Translate Definition": {
        "task_name": "translate_def",
        "input": {"text": "String"},
        "output": {"definition": "String"},
        "parameters": {"fallback": "Bool (default: true)"},
    },
    "Documentation for a Theorem": {
        "task_name": "theorem_doc",
        "input": {"name": "String", "command": "String"},
        "output": {"doc": "String"},
    },
    "Documentation for a Definition": {
        "task_name": "def_doc",
        "input": {"name": "String", "command": "String"},
        "output": {"doc": "String"},
    },
    "Theorem Name": {
        "task_name": "theorem_name",
        "input": {"text": "String"},
        "output": {"name": "String"}
    },
    "Prove": {
        "task_name": "prove",
        "input": {"theorem": "String"},
        "output": {"proof": "String"}
    },
    "Structured JSON Proof": {
        "task_name": "structured_json_proof",
        "input": {"theorem": "String", "proof": "String"},
        "output": {"json_structured": "Json"},
    },
    "Lean from JSON Structured": {
        "task_name": "lean_from_json_structured",
        "input": {"json_structured": "Json"},
        "output": {
            "lean_code": "String",
            "declarations": "List String",
            "top_code": "String",
        },
    },
    "Elaborate Lean Code": {
        "task_name": "elaborate",
        "input": {"lean_code": "String", "declarations": "List Name"},
        "output": {"logs": "List String", "sorries": "List Json"},
        "parameters": {
            "top_code": 'String (default: "")',
            "describe_sorries": "Bool (default: false)",
        },
    },
}

def button_clicked(button_arg):
    def protector():
        """This function does not allow value to become True until the button is clicked."""
        st.session_state[button_arg] = True
    return protector

def get_actual_input(input_str: str) -> Tuple[Type, Any]:
    """
    Convert a string representation of a Python literal into its corresponding type.
    Returns a tuple of (type, parsed_value).
    """
    try:
        json_input = json.loads(input_str) # Check if the input is valid JSON
        return (type(json_input), json_input)
    except json.JSONDecodeError:
        try:
            # If not JSON, check if if it is a list
            literal_input = ast.literal_eval(input_str)
            return (type(literal_input), literal_input)
        except (ValueError, SyntaxError):
            # If all else fails, return as string
            return (str, input_str)

def validate_input_type(input_type: Any, expected_type: str) -> bool:
    """
    Validate if the input value matches the expected type.
    Returns True if it matches, False otherwise.
    """
    exp = expected_type.lower().split()
    if "json" in exp:
        if input_type.__name__.lower() == "dict":
            return True
    elif "list" in exp:
        if input_type.__name__.lower() == "list":
            return True
    elif "string" in exp or "str" in exp:
        if input_type.__name__.lower() == "str":
            return True
    elif "int" in exp:
        if input_type.__name__.lower() == "int":
            return True
    elif "bool" in exp or "boolean" in exp:
        if input_type.__name__.lower() == "bool":
            return True
    return False

# In-memory log storage with max size (1000 lines by default)
LOG_BUFFER = deque(maxlen=1000) 

def log_server():
    """Read from the in-memory log buffer"""
    if not LOG_BUFFER:
        return "No logs available yet."
    return "".join(reversed(LOG_BUFFER))

def log_write(proc_name: str, log_message: str):
    """
    Write a message to the in-memory log buffer
    Format: "[proc_name] log_message"
    """
    try:
        log_entry = f"[{proc_name}] {log_message}\n"
        LOG_BUFFER.append(log_entry)
    except Exception as e:
        print(f"Error writing to log buffer: {e}")

def log_buffer_clean():
    try:
        LOG_BUFFER.clear()
    except Exception as e:
        log_write("log_clean", f"Error clearing log buffer: {e}")

def download_file(file_content, file_name):
    # match mime
    mime = "text/plain"
    match file_name.split(".")[-1].lower():
        case "json":
            mime = "application/json"
        case "txt":
            mime = "text/plain"
        case "md":
            mime = "text/markdown"
        case "html":
            mime = "text/html"
        case "csv":
            mime = "text/csv"
        case _:
            pass  # Keep default text/plain for other extensions
    st.download_button(
        label="Download File", data=file_content, file_name=file_name, mime=mime, help = "Click to download the file with the above text content.",
    )

# Function to copy text to clipboard and show confirmation
def copy_to_clipboard(text):
    try:
        copy_button(
            text,
            tooltip="Copy to Clipboard",
            copied_label = "Copied!",
            icon=":material/content_copy:",
        )
    except Exception as e:
        st.warning(f"Failed to copy: {e}", icon="⚠️")

def action_copy_download(key: str, filename: str, copy_text: str = ""):
    """Helper function to copy text to clipboard and download as a file."""
    col1, col2 = st.columns(2)
    text = st.session_state[key]
    if copy_text:
        text = copy_text
    with col1:
        copy_to_clipboard(text)
    with col2:
        download_file(text, filename)

def preview_text(key: str, default_text: str = ""):
    """
    Display a preview of the text in a text area with a copy and download button.
    """
    with st.expander(f"Preview Text {key.capitalize()}", expanded=False):
        lang = st.radio("Language", ["Markdown", "Text"], horizontal = True, key = f"preview_{key}").lower()
        if lang == "markdown":
            st.markdown(st.session_state[key] if st.session_state[key] else default_text)
        else:
            st.code(st.session_state[key] if st.session_state[key] else default_text, wrap_lines = True)