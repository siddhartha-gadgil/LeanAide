import ast
import json
import os
import sys
from pathlib import Path
from typing import Any, Tuple, Type

import streamlit as st
import st.session_state as sts
from st_copy import copy_button

from logging_utils import log_server, log_buffer_clean

HOST = os.environ.get("HOST", "localhost")
HOMEDIR = str(Path(__file__).resolve().parent.parent) # LeanAide root
sys.path.append(HOMEDIR)
schema_path = os.path.join(str(HOMEDIR), "resources", "PaperStructure.json")
SCHEMA_JSON = json.load(open(schema_path, "r", encoding="utf-8"))

# Lean Checker Tasks
TASKS = {
    "Echo": {
        "task_name": "echo",
        "input": {"data": "String"},
        "output": {"data": "String"}
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
    "Translate Theorem Detailed": {
        "task_name": "translate_thm_detailed",
        "input": {"text": "String"},
        "output": {
            "theorem": "String",
            "name": "String",
            "proved": "Bool",
            "statement": "String",
            "definitions_used": "String"
        },
        "parameters": {
            "greedy": "Bool (default: true)",
            "fallback": "Bool (default: true)",
        },
    },
    "Structured JSON Proof": {
        "task_name": "structured_json_proof",
        "input": {"theorem": "String", "proof": "String"},
        "output": {"json_structured": "Json"},
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
    "Lean from JSON Structured": {
        "task_name": "lean_from_json_structured",
        "input": {"json_structured": "Json"},
        "output": {
            "lean_code": "String",
            "declarations": "List String",
            "top_code": "String",
        },
    },
}

def button_clicked(button_arg):
    def protector():
        """This function does not allow value to become True until the button is clicked."""
        sts[button_arg] = True
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

def download_file(file_content, file_name, key:str = "", usage:str = ""):
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
        label="Download File", data=file_content, file_name=file_name, mime=mime, help = "Click to download the file with the above text content.", key = f"download_{key}_{usage}",
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

def action_copy_download(key: str, filename: str, copy_text: str = "", usage: str = ""):
    """Helper function to copy text to clipboard and download as a file."""
    col1, col2 = st.columns(2)
    text = sts[key]
    if copy_text:
        text = copy_text
    with col1:
        copy_to_clipboard(text)
    with col2:
        download_file(text, filename, key= key, usage=usage)

def preview_text(key: str, default_text: str = "", usage: str = ""):
    """
    Display a preview of the text in a text area with a copy and download button.
    """
    with st.expander(f"Preview Text {key.capitalize()}", expanded=False):
        lang = st.radio("Language", ["Markdown", "Text"], horizontal = True, key = f"preview_{key}_{usage}").lower()
        if lang == "markdown":
            st.markdown(sts[key] if sts[key] else default_text)
        else:
            st.code(sts[key] if sts[key] else default_text, wrap_lines = True)

def log_section():
    st.subheader("Server Website Stdout/Stderr", help = "Logs are written to LeanAide-Streamlit-Server Local buffer and new logs are updated after SUBMIT REQUEST button is clicked.")
    with st.expander("Click to view Server-Streamlit logs.", expanded=False):
        if log_out := log_server():
            height = 500 if len(log_out) > 1000 else 150
            st.write("Server logs:")
            st.code(
                log_out if not sts.log_cleaned else "No logs available yet.",
                language = "log",
                height= height,
                wrap_lines =True,
                line_numbers=True,
            )

        else:
            st.code("No logs available yet.", language="plaintext")

        with st.popover("Clean Server Logs", help="Click and select Yes to clean the server logs. This will delete all the logs in the Log Buffer for Streamlit."):
            st.write("Are you sure you want to clean the server logs? This will delete all the logs in the server.")
            if st.button("Yes"):
                try:
                    sts.log_cleaned = True
                    log_buffer_clean()
                    st.success("Server logs cleaned successfully! Please UNCHECK THE BOX to avoid cleaning again.")
                    st.rerun()
                except Exception as e:
                    st.error(f"Error cleaning server logs: {e}")
            if st.button("No"):
                pass
            sts.log_cleaned = False
            st.info("Press Escape to close this popover.")
