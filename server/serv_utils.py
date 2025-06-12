import ast
from pathlib import Path
import json
import shlex
from typing import Any, Tuple, Type
import streamlit as st
from st_copy import copy_button

from api_server import HOST, LOG_FILE

HOMEDIR = str(Path(__file__).resolve().parent.parent) # LeanAide root

# Lean Checker Tasks
TASKS = {
    "echo": {
        "name" : "Echo",
        "input": {"data": "String"},
        "output": {"data": "String"}
    },
    "translate_thm": {
        "name": "Translate Theorem",
        "input": {"text": "String"},
        "output": {"theorem": "String"},
        "parameters": {
            "greedy": "Bool (default: true)",
            "fallback": "Bool (default: true)",
        },
    },
    "translate_def": {
        "name": "Translate Definition",
        "input": {"text": "String"},
        "output": {"definition": "String"},
        "parameters": {"fallback": "Bool (default: true)"},
    },
    "theorem_doc": {
        "name": "Documentation for a Theorem",
        "input": {"name": "String", "command": "String"},
        "output": {"doc": "String"},
    },
    "def_doc": {
        "name": "Documentation for a Definition",
        "input": {"name": "String", "command": "String"},
        "output": {"doc": "String"},
    },
    "theorem_name": {
        "name": "Theorem Name",
        "input": {"text": "String"},
        "output": {"name": "String"}
    },
    "prove": {
        "name": "Prove Theorem",
        "input": {"theorem": "String"},
        "output": {"proof": "String"}
    },
    "structured_json_proof": {
        "name": "Structured JSON Proof",
        "input": {"theorem": "String", "proof": "String"},
        "output": {"json_structured": "Json"},
    },
    "lean_from_json_structured": {
        "name": "Lean from JSON Structured",
        "input": {"json_structured": "Json"},
        "output": {
            "lean_code": "String",
            "declarations": "List String",
            "top_code": "String",
        },
    },
    "elaborate": {
        "name": "Elaborate Lean Code",
        "input": {"lean_code": "String", "declarations": "List Name"},
        "output": {"logs": "List String", "sorries": "List Json"},
        "parameters": {
            "top_code": 'String (default: "")',
            "describe_sorries": "Bool (default: false)",
        },
    },
}

def get_names_by_tasks():
    list_tasks = []
    for task in TASKS:
        if "name" in TASKS[task]:
            list_tasks.append(TASKS[task]["name"])
        else:
            list_tasks.append(task)
    return list_tasks

def get_task_by_name(name):
    for task in TASKS:
        if "name" in TASKS[task] and TASKS[task]["name"] == name:
            return task
    return None

def get_task_list_by_name(list_names):
    """
    Given a list of task names, return a list of tasks that match those names.
    If a name does not match any task, it is ignored.
    """
    task_list = []
    for name in list_names:
        if task := get_task_by_name(name):
            task_list.append(task)
    return task_list

def parse_curl(curl_cmd, ignore_curl_ip_port):
    args = shlex.split(curl_cmd)
    out = {"method": "POST", "url_ip": "", "port": "", "headers": {}, "data": {}}
    i = 0
    while i < len(args):
        match args[i]:
            case "curl":
                i += 1
            case "-X":
                out["method"] = args[i + 1]
                i += 2
            case "-H":
                k, v = args[i + 1].split(":", 1)
                out["headers"][k.strip()] = v.strip()
                i += 2
            case "--data" | "-d":
                try:
                    out["data"] = json.loads(args[i + 1])
                except Exception:
                    out["data"] = args[i + 1]
                i += 2
            case x if x.startswith("http"):
                x = x.split("://", 1)[1].split(":", 1)
                if ignore_curl_ip_port:
                    out["url_ip"] = st.session_state.get("api_host", HOST)
                    out["port"] = st.session_state.get("api_port", "7654")
                else:
                    out["url_ip"] = x[0]
                    out["port"] = x[1]
                i += 1
            case _:
                i += 1
    return out


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


def log_server():
    """Read from the log file"""
    try:
        with open(LOG_FILE, "r") as f:
            # Efficiently get last n lines
            lines = []
            for line in f:
                lines.append(line)
            return "".join(lines)
    except FileNotFoundError:
        return "No log file found yet."

def log_write(proc_name: str, log_message: str):
    """
    Write a message to the log file, in format "[proc_name] log_message".
    proc_name: "Server stderr" or "Streamlit" are standard. You can use any name.
    log_message: The message to log.
    """
    try:
        with open(LOG_FILE, "a") as f:
            f.write(f"[{proc_name}] {log_message}" + "\n")
    except Exception as e:
        print(f"Error writing to log file: {e}")

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
        label="Download File", data=file_content, file_name=file_name, mime=mime, help = "Click to download the file. "
    )

# Function to copy text to clipboard and show confirmation
def copy_to_clipboard(text):
    copy_button(
        text,
        icon='st',  # default, use 'st' as alternative
        tooltip='Copy to Clipboard',  # defaults to 'Copy'
        copied_label='Copied Successfully!',  # defaults to 'Copied!'
        # key="key",  # If omitted, a random key will be generated
)