import json
import os
import shlex
import sys
from pathlib import Path

import pyperclip
import requests
import streamlit as st
from dotenv import load_dotenv
import socket
from api_server import HOST, PORT

load_dotenv()

homedir = str(Path(__file__).resolve().parent.parent)
src_dir = os.path.join(homedir, "src")
sys.path.insert(0, str(src_dir))

st.title("LeanAide Server")

if "api_host" not in st.session_state:
    st.session_state.api_host = HOST
if "api_port" not in st.session_state:
    st.session_state.api_port = PORT

# Host Information Section
with st.expander("Host Information"):
    localhost_serv = st.checkbox(
        "Your backend server is running on localhost", value=False, help="Check this if you want to call the backend API running on localhost.",
    )

    if not localhost_serv:
        local_ip = socket.gethostbyname(socket.gethostname())
        api_host = st.text_input(
            "Backend API Host: (default: HOST or localhost IP)",
            value= HOST if HOST != "localhost" else local_ip,
            help="Specify the hostname or IP address where the proof server is running. Default is localhost.",
        )
        st.session_state.api_host = api_host
    api_port = st.text_input(
        "API Port:",
        value="7654",
        help="Specify the port number where the proof server is running. Default is 7654.",
    )
    st.session_state.api_port = api_port

# Function to copy text to clipboard and show confirmation
def copy_to_clipboard(text):
    try:
        pyperclip.copy(text)
        st.toast("Copied to clipboard!", icon="✔️")
    except Exception as e:
        st.warning(f"Failed to copy: {e}")

# Lean Checker Tasks
tasks = {
    "echo": {"input": {"data": "Json"}, "output": {"data": "Json"}},
    "translate_thm": {
        "input": {"text": "String"},
        "output": {"theorem": "String"},
        "parameters": {
            "greedy": "Bool (default: true)",
            "fallback": "Bool (default: true)",
        },
    },
    "translate_def": {
        "input": {"text": "String"},
        "output": {"definition": "String"},
        "parameters": {"fallback": "Bool (default: true)"},
    },
    "theorem_doc": {
        "input": {"name": "String", "command": "String"},
        "output": {"doc": "String"},
    },
    "def_doc": {
        "input": {"name": "String", "command": "String"},
        "output": {"doc": "String"},
    },
    "theorem_name": {"input": {"text": "String"}, "output": {"name": "String"}},
    "prove": {"input": {"theorem": "String"}, "output": {"proof": "String"}},
    "structured_json_proof": {
        "input": {"theorem": "String", "proof": "String"},
        "output": {"json_structured": "Json"},
    },
    "lean_from_json_structured": {
        "input": {"json_structured": "String"},
        "output": {
            "lean_code": "String",
            "declarations": "List String",
            "top_code": "String",
        },
    },
    "elaborate": {
        "input": {"lean_code": "String", "declarations": "List Name"},
        "output": {"logs": "List String", "sorries": "List Json"},
        "parameters": {
            "top_code": 'String (default: "")',
            "describe_sorries": "Bool (default: false)",
        },
    },
}

## Initialize session state variables
for key in ["parsed_curl", "manual_selection", "curl_selection", "sel_inputs", "sel_params", "selected_tasks", "result"]:
    if key not in st.session_state:
        st.session_state[key] = None
for key in ["curl_botton", "request_button", "ignore_curl_ip_port"]:
    if key not in st.session_state:
        st.session_state[key] = False

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

st.header("Server Request")

# cURL Request Section
st.subheader("Paste cURL Request")
curl_input = st.text_area(
    "Paste your cURL request here:",
    height=150,
    placeholder="Paste cURL command starting with curl -X POST...",
)
if st.checkbox("Ignore above cURL request's host and port, and use the host and port specified in Host Information.", value=False):
    st.session_state.ignore_curl_ip_port = True
else:
    st.session_state.ignore_curl_ip_port = False 

if st.button("Process cURL Request", on_click = button_clicked("curl_botton")) or st.session_state.curl_botton:
    try:
        # Extract JSON payload from curl
        st.session_state.parsed_curl = parsed_curl = parse_curl(curl_input, st.session_state.ignore_curl_ip_port)
        # Update session state with host and port if they exist in the curl
        if not st.session_state.ignore_curl_ip_port:
            if "url_ip" in parsed_curl and parsed_curl["url_ip"]:
                st.session_state.api_host = parsed_curl.get(
                    "url_ip", st.session_state.get("api_host", HOST)
                )
            if "port" in parsed_curl and parsed_curl["port"]:
                st.session_state.api_port = parsed_curl.get(
                    "port", st.session_state.get("api_port", "7654")
                )

        st.success("cURL parsed successfully!")
        st.json(parsed_curl)
        # Update session states
        st.session_state.curl_selection = True
        st.session_state.selected_tasks = list(parsed_curl.get("data", {})["tasks"]) if "data" in parsed_curl else []
    except Exception as e:
        st.session_state.selected_tasks = []
        st.error(f"Error parsing curl: {e}")

st.subheader("Fill Request Manually")
if st.checkbox(
    "To fill request manually, pls check this box. This will ignore any cURL request pasted above.",
    value=False,
):
    st.session_state.manual_selection = True
    st.subheader("Step 1: Select Input Tasks")
    selected_inputs = st.multiselect("Select Input Tasks:", list(tasks.keys()))

    sel_inputs = {}
    sel_params = {}
    if st.button("Give Input"):
        for task in selected_inputs:
            sel_inputs[task] = {}
            for key, value in tasks[task].get("input", {}).items():
                sel_inputs[task][key] = st.text_input(
                    f"{task.capitalize()} - {key} ({value}):"
                )
            for param, param_type in tasks[task].get("parameters", {}).items():
                sel_params[param] = st.checkbox(f"{task} - {param} ({param_type})")

    st.subheader("Step 2: Select Processing Tasks")
    selected_tasks = [task for task in tasks.keys() if task not in selected_inputs]
    selected_tasks = st.multiselect("Select Processing Tasks:", selected_tasks)

    # update to session state
    st.session_state.selected_tasks = selected_tasks
    st.session_state.sel_inputs = sel_inputs
    st.session_state.sel_params = sel_params


# Submit Request Section. Common to Curl and Manual Selection
if st.button("Submit Request", on_click= button_clicked("request_button")) or st.session_state.request_button:
    if not st.session_state.curl_selection and not st.session_state.manual_selection:
        st.warning("Please either paste a cURL request or select tasks manually.")
        st.stop()
    if st.session_state.manual_selection: # Makes the request payload from manual selection
        request_payload = {"tasks": st.session_state.selected_tasks, **st.session_state.sel_inputs, **st.session_state.sel_params}
    else: # Makes the request payload from cURL
        request_payload = st.session_state.parsed_curl.get("data", {})
        print(f"Request Payload: {request_payload}")
        if not request_payload:
            st.warning(
                "No data found in the cURL request. Please check the cURL command."
            )
            st.stop()
    with st.spinner("Request sent. Please wait for a short while..."):
        response = requests.post(
            f"http://{st.session_state.api_host}:{st.session_state.api_port}", json=request_payload
        )

    if response.status_code == 200:
        # Get the result
        st.success("Response received successfully!")
        st.session_state.result = response.json()
        print(f"Selected Tasks: {st.session_state.selected_tasks}")
        print(f"Response: {st.session_state.result}")
  
        # Handle the output for each task
        for task in st.session_state.selected_tasks:
            st.subheader(task.capitalize() + " Output", divider =True)
            for key, value in tasks[task]["output"].items():
                if "json" in value.lower().split():
                    st.write(f"{key.capitalize()} ({value}):")
                    st.json(st.session_state.result.get(key, "No data available."))
                else:
                    st.write(f"{key.capitalize()} ({value}):")
                    st.code(
                        st.session_state.result.get(key, "No data available."), language="plaintext"
                    )
    else:
        st.error(f"Error: {response.status_code}, {response.text}")

