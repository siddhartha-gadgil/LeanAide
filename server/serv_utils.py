import ast
import json
import os
import re
import socket
import sys
import urllib.parse
from pathlib import Path
from typing import Any, Tuple, Type

import requests
import streamlit as st
from st_copy import copy_button
from streamlit import session_state as sts

from api_server import HOST
from logging_utils import (LEANAIDE_HOMEDIR, log_buffer_clean, log_server,
                           log_write)

HOMEDIR = str(Path(__file__).resolve().parent.parent) # LeanAide root
sys.path.append(HOMEDIR)
schema_path = os.path.join(str(HOMEDIR), "resources", "PaperStructure.json")
SCHEMA_JSON = json.load(open(schema_path, "r", encoding="utf-8"))

TOKEN_JSON_FILE = f"{LEANAIDE_HOMEDIR}/.leanaide_cache/tasks/token_status.json"

# Lean Checker Tasks
TASKS = {
    "Echo": {
        "task_name": "echo",
        "input": {"data": "String"},
        "output": {"data": "String"},
        "commonly_used": False,
    },
    "Documentation for a Theorem": {
        "task_name": "theorem_doc",
        "input": {"theorem_name": "String", "theorem_statement": "String"},
        "output": {"theorem_doc": "String"},
        "commonly_used": False,
    },
    "Documentation for a Definition": {
        "task_name": "def_doc",
        "input": {"definition_name": "String", "definition_code": "String"},
        "output": {"definition_doc": "String"},
        "commonly_used": False,
    },
    "Translate Theorem": {
        "task_name": "translate_thm",
        "input": {"theorem_text": "String"},
        "output": {"theorem_code": "String"},
        "parameters": {
            "greedy": "Bool (default: true)",
            "fallback": "Bool (default: true)",
        },
        "commonly_used": False,
    },
    "Translate Definition": {
        "task_name": "translate_def",
        "input": {"definition_text": "String"},
        "output": {"definition_code": "String"},
        "parameters": {"fallback": "Bool (default: true)"},
        "commonly_used": False,
    },
    "Theorem Name": {
        "task_name": "theorem_name",
        "input": {"theorem_text": "String"},
        "output": {"theorem_name": "String"},
        "commonly_used": False,
    },
    "Prove": {
        "task_name": "prove",
        "input": {"theorem_text": "String"},
        "output": {"proof_text": "String"},
        "commonly_used": False,
    },
    "Translate Theorem Detailed": {
        "task_name": "translate_thm_detailed",
        "input": {"theorem_text": "String"},
        "output": {
            "theorem_code": "String",
            "theorem_name": "String",
            "proved": "Bool",
            "theorem_statement": "String",
            "definitions_used": "String"
        },
        "parameters": {
            "greedy": "Bool (default: true)",
            "fallback": "Bool (default: true)",
        },
        "commonly_used": True,
    },
    "Structured JSON Proof": {
        "task_name": "structured_json_proof",
        "input": {"theorem_text": "String", "proof_text": "String"},
        "output": {"document_json": "Json"},
        "commonly_used": False,
    },
    "Elaborate Lean Code": {
        "task_name": "elaborate",
        "input": {"document_code": "String", "declarations": "List Name"},
        "output": {"logs": "List String", "sorries": "List Json"},
        "parameters": {
            "top_code": 'String (default: "")',
            "describe_sorries": "Bool (default: false)",
        },
        "commonly_used": True,
    },
    "Lean from JSON Structured": {
        "task_name": "lean_from_json_structured",
        "input": {"document_json": "Json"},
        "output": {
            "document_code": "String",
            "declarations": "List String",
            "top_code": "String",
        },
        "commonly_used": True,
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
            icon="material_symbols",
        )
    except Exception as e:
        st.warning(f"Failed to copy: {e}", icon="⚠️")

def action_copy_download(key: str, filename: str, copy_text: str = "", usage: str = ""):
    """Helper function to copy text to clipboard and download as a file."""
    col1, col2 = st.columns(2)
    text = sts[key]
    if copy_text:
        text = copy_text
    
    # Decode unicode escape sequences (e.g., \u2208 -> ∈, \u03a8 -> Ψ)
    if isinstance(text, str):
        try:
            text = text.encode('utf-8').decode('unicode_escape')
        except (UnicodeDecodeError, AttributeError):
            # If decoding fails, keep original text
            pass
            # Handle LaTeX syntax: ensure even number of backslashes before commands
            if isinstance(text, str):
                def fix_latex_backslashes(text: str) -> str:
                    def repl(m):
                        slashes = m.group(1)
                        cmd = m.group(2)
                        # if odd number of backslashes → make it even
                        if len(slashes) % 2 == 1:
                            slashes += "\\"
                        return slashes + cmd

                    return re.sub(r'(\\+)([a-zA-Z]+)', repl, text)
                text = fix_latex_backslashes(text)
    
    with col1:
        copy_to_clipboard(text)
    with col2:
        download_file(text, filename, key= key, usage=usage)

def preview_text(key: str, default_text: str = "", caption = "", usage: str = ""):
    """
    Display a preview of the text in a text area with a copy and download button.
    """
    if not caption:
        caption = key
    with st.expander(f"Preview Text {caption.capitalize()}", expanded=False):
        lang = st.radio("Language", ["Markdown", "Text"], horizontal = True, key = f"preview_{key}_{usage}").lower()
        
        # Decode unicode escape sequences for display
        display_text = sts[key] if sts[key] else default_text
        if isinstance(display_text, str):
            try:
                display_text = display_text.encode('utf-8').decode('unicode_escape')
            except (UnicodeDecodeError, AttributeError):
                pass
        
        if lang == "markdown":
            st.markdown(display_text)
        else:
            st.code(display_text, wrap_lines = True)
            
def lean_code_cleanup(lean_code: str, elaborate: bool = False) -> str:
    """
    Cleans up the error texts in the lean code.
    """          
    final_code = []
    keywords_to_remove = ["#check", "trace", "Error: codegen:"]
    keywords_to_remove += ["import"] if elaborate else []
    for line in lean_code.splitlines():
        if not any(keyword in line for keyword in keywords_to_remove):
            final_code.append(line)

    if elaborate:
        return "\n".join(final_code).strip()
    return "import Mathlib\n" + "\n".join(final_code) if "import Mathlib" not in lean_code else "\n".join(final_code)

def lean_code_button(result_global_key: str, key: str, task: str): 
    code = sts[result_global_key].get(key, "-- No Lean code available")
    if code not in ["-- No Lean code available", "No data available."]:
        col_1, col_2 = st.columns([1, 3])
        with col_1:
            code = f"import Mathlib\n{code.strip()}" if "import Mathlib" not in code else code
            st.link_button("Open Lean Web IDE", help="Open the Lean code in the Lean Web IDE.", url = f"https://live.lean-lang.org/#code={urllib.parse.quote(code)}")

        with col_2:
            if st.button("Cleanup Lean Code", help="Cleanup the Lean code to remove extra error messages and add Mathlib import in the beginning. This will not affect the performance of code", key=f"cleanup_{task}"):
                try:
                    sts[result_global_key][key] = lean_code_cleanup(code)
                    st.rerun()
                    log_write("Streamlit", "Lean Code Cleanup: Success")
                except Exception as e:
                    st.error(f"Error while cleaning up Lean code: {e}")
                    log_write("Streamlit", f"Lean Code Cleanup Error: {e}")

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

def request_server(request_payload: dict, task_header: str, success_key: str, result_key: str):
    with st.spinner("Request sent. Check the server logs for activity. Please wait for short while...", show_time = True): 
        log_write(task_header, f"Request Payload: {request_payload}")
        response = requests.post(
            f"http://{sts.api_host}:{sts.api_port}", json=request_payload
        )

    if response.status_code == 200:
        # Get the result
        st.success("Response sent and received successfully!")
        sts[result_key] = response.json()
        
        # Decode unicode escape sequences in the response
        def decode_unicode_in_dict(obj):
            """Recursively decode unicode escape sequences in dict/list/str"""
            if isinstance(obj, dict):
                return {k: decode_unicode_in_dict(v) for k, v in obj.items()}
            elif isinstance(obj, list):
                return [decode_unicode_in_dict(item) for item in obj]
            elif isinstance(obj, str):
                try:
                    return obj.encode('utf-8').decode('unicode_escape')
                except (UnicodeDecodeError, AttributeError):
                    return obj
            return obj
        
        sts[result_key] = decode_unicode_in_dict(sts[result_key])
        log_write(task_header, f"Response: {sts[result_key]}")

        try:
            if sts[result_key]["result"] == "success":
                sts[success_key] = True
                st.success("Request processed successfully!")
            else: # result = "error"
                sts[success_key] = False
                st.error("Error in processing the request. Please check the input and try again.")
                st.write("Error (String):")
                st.code(sts[result_key]["error"])
            log_write("Streamlit", "Server Output: Success")
        except Exception as e:
            sts[success_key] = False
            st.error(f"Error in processing the request: {e}")
            st.write("Response (String):")
            st.code(str(sts[result_key]))
            log_write(task_header, f"Server Output: Error - {e}")

    else:
        sts[success_key] = False
        st.error(f"Error: {response.status_code}, {response.text}")
        log_write(task_header, f"Server Response Error: {response.status_code} - {response.text}")
        # Handle the output for each tasks


def host_information():
    localhost_serv = st.checkbox(
        "Your backend server is running on localhost", value=False, help="Check this if you want to call the backend API running on localhost.",
    )

    if not localhost_serv:
        local_ip = socket.gethostbyname(socket.gethostname())
        local_ip = "localhost" if str(local_ip).strip().startswith("127.") else local_ip
        api_host = st.text_input(
            "Backend API Host: (default: HOST or localhost IP)",
            value= HOST if not HOST.strip().startswith("127.") else local_ip,
            help="Specify the hostname or IP address where the proof server is running. Default is localhost.",
        )
        sts.api_host = api_host
    api_port = st.text_input(
        "API Port:",
        value="7654",
        help="Specify the port number where the proof server is running. Default is 7654.",
    )
    sts.api_port = api_port

def get_async_response(token):
    """
    Get and manage the asynchronous response from the server or cache.
    """
    cached_response_file = f"{LEANAIDE_HOMEDIR}/.leanaide_cache/tasks/response_{token}.json"
    if os.path.exists(cached_response_file):
        with open(cached_response_file, "r", encoding="utf-8") as f:
            response_data = json.load(f)
        return 0, response_data
    else:
        # request server in lookup mode
        request_payload = {
            "mode": "lookup",
            "token": token
        }
        try:
            response = requests.post(
                f"http://{sts.api_host}:{sts.api_port}", json=request_payload
            )
            if response.status_code == 200:
                err_code, response_data = process_lookup_response(response.json())
                return err_code, response_data
            else:
                return 2, {"result": "error", "error": f"Error: {response.status_code}, {response.text}"}
        except Exception as e:
            return 2, {"result": "error", "error": str(e)}



def process_lookup_response(lookup_response):
    """
    Process the lookup response from the server.
    0 : Job is completed by the server(what the response is, success or error, is independent)
    1 : Job is still running
    2 : Error in lookup
    """
    lookup_status = lookup_response.get("status", {})
    lookup_result = lookup_response.get("result", "error")

    if lookup_result != "success":
        # wrong token or similar
        return 2, lookup_response

    # This is for when job was successfully submitted
    if "completed" in lookup_status.keys():
        return 0, lookup_status["completed"]
    elif "running" in lookup_status:
        return 1, lookup_status["running"]
    else:
        return 3, lookup_response

def store_token_responses(token: str, status: str):
    """
    Store the token responses in session state.
    """
    if not int(token) and int(token)> 0:
        return
     # Ensure the directory exists
    if os.path.exists(TOKEN_JSON_FILE):
        with open(TOKEN_JSON_FILE, "r", encoding="utf-8") as f:
            token_data = json.load(f)

        token_data[token] = status
        with open(TOKEN_JSON_FILE, "w", encoding="utf-8") as f:
            json.dump(token_data, f, indent=4)
    else:
        token_data = {token: status}
        with open(TOKEN_JSON_FILE, "w", encoding="utf-8") as f:
            json.dump(token_data, f, indent=4)


def show_response(show_input: bool = False, async_response: bool = False):  
    def show_util(val_type, key, input_data, task):
        if "json" in val_type.lower().split():
            st.write(f"{key.capitalize()} ({val_type}):")
            json_in = input_data.get(key) or {}
            st.json(json_in)
            copy_to_clipboard(str(json_in))
        else:
            st.write(f"{key.capitalize()} ({val_type}):")
            st.code(
                input_data.get(key) or "No data available.", language="plaintext", wrap_lines = True
            )
            if "lean_code" in key.lower():
                lean_code_button("input", key, task)

    if async_response:
        st.subheader("Job Token Response", divider =True)
        if show_input:
            if sts.result.get("status", "") == "background":
                st.sucess("The task is sent to background processing. Use the below token to check for the response.")
                st.code(st.result.get("token", "No token available."), language="plaintext", wrap_lines = True)
            else:
                st.error("Error occurred while sending task to background processing.")
                st.error(f"Error: {st.result.get('error', 'No error details available.')}")

    else:
        for task in sts.selected_tasks:
            st.subheader(task + " Output", divider =True)
            if "elaborate" in task.lower().strip():
                if sts.result["result"] == "success":
                    st.success("Successful Elaboration => Lean Code is **Correct**.")
                else:
                    st.error("Elaboration failed. The Lean code produced may be **incorrect**.")

            for key, val_type in TASKS[task]["output"].items():
                show_util(val_type, key, sts.result, task)

            st.divider()
            if show_input:
                st.subheader(task + " Input", divider =True)
                input_data = {key: sts.val_input.get(key, "No data available.") for key in TASKS[task].get("input", {}).keys()}

                for key, val_type in TASKS[task].get("input", {}).items():
                    show_util(val_type, key, input_data, task)

