import os
import socket
import sys
from pathlib import Path

import requests
import streamlit as st
from dotenv import load_dotenv

from api_server import HOST, PORT
from serv_utils import (button_clicked, get_actual_input, parse_curl, tasks,
                        validate_input_type)

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

## Initialize session state variables
for key in ["parsed_curl", "selected_inputs", "manual_selection", "curl_selection", "val_input", "selected_tasks", "result"]:
    if key not in st.session_state:
        st.session_state[key] = None
for key in ["curl_botton", "request_button", "manual_input_button", "ignore_curl_ip_port", "server_output_success", "valid_manual_input"]:
    if key not in st.session_state:
        st.session_state[key] = False

st.header("Server Request", divider = True, help = "You can either paste a cURL request or fill the request manually. The request will be sent to the backend server specified by you.")

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

st.subheader("Fill Request Manually", help = "Select the tasks you want to perform and provide the necessary inputs.")
if st.checkbox(
    "To fill request manually, pls check this box. This will ignore any cURL request pasted above.",
    value=False,
):
    st.session_state.manual_selection = True
    st.subheader("Step 1: Select Input Tasks")
    st.session_state.selected_inputs = st.multiselect("Select Input Tasks:", list(tasks.keys()))

    st.session_state.val_input = {}
    if st.button("Give Input", help = "Provide inputs to the your selected tasks. Note: It is not compulsary to fill all of them.") or st.session_state.manual_input_button:
        st.session_state.manual_input_button = True
        for task in st.session_state.selected_inputs:
            # Get input for each task
            for key, val_type in tasks[task].get("input", {}).items():
                help = f"Please provide input for `{key}` of type `{val_type}`."
                if "json" in key.lower():
                    help += " Just paste your `json` object here."
                # While the expected type of input and actual input type do not match, keep asking for input
                val_in = st.text_input(f"{task.capitalize()} - {key} ({val_type}):", help = help)
                if val_in:
                    inp_type, st.session_state.val_input[key] = get_actual_input(val_in)
                    if validate_input_type(inp_type, val_type):
                        st.session_state.valid_manual_input = True
                    else:
                        st.warning(
                            f"Invalid input type for {key}. Expected `{val_type}`, got `{inp_type.__name__}`. See help for each input for more info. Please try again."
                        )
                        st.session_state.valid_manual_input = False

            for param, param_type in tasks[task].get("parameters", {}).items():
                if "boolean" in param_type.lower() or "bool" in param_type.lower():
                    if param_in := st.checkbox(f"{task.capitalize()} - {param} ({param_type})", help = "Check this box if you want to change the default Boolean value"):
                        st.session_state.val_input[param] = param_in
                else:
                    help = f"Please provide a value for `{param}` of type `{param_type}`. If you want to skip this parameter, just leave it unchecked."
                    if param_in := st.text_input(f"{task.capitalize()} - {param} ({param_type}):", help=help):
                        st.session_state.val_input[param] = param_in

    st.subheader("Step 2: Select Processing Tasks")

    st.session_state.selected_tasks = st.session_state.selected_inputs.copy()
    # update to session state
    st.session_state.selected_tasks = st.multiselect("Select Processing Tasks:", [task for task in tasks.keys()] , default=st.session_state.selected_tasks)

# Submit Request Section. Common to Curl and Manual Selection
st.header("Submit your Request.", divider=True, help = "For both cURL and manual selection, you can submit your request here. The request will be sent to the backend server specified in the Host Information section.")
if st.button("Submit Request", on_click= button_clicked("request_button")) or st.session_state.request_button:
    if not st.session_state.curl_selection and not st.session_state.manual_selection:
        st.warning("Please either paste a cURL request or select tasks manually.")
        st.stop()
    if st.session_state.manual_selection: # Makes the request payload from manual selection
        request_payload = {"tasks": st.session_state.selected_tasks, **st.session_state.val_input}
    else: # Makes the request payload from cURL
        request_payload = st.session_state.parsed_curl.get("data", {})
        if not request_payload:
            st.warning(
                "No data found in the cURL request. Please check the cURL command."
            )
            st.stop()
    with st.spinner("Request sent. Please wait for a short while..."):
        print(f"Request Payload: {request_payload}")
        response = requests.post(
            f"http://{st.session_state.api_host}:{st.session_state.api_port}", json=request_payload
        )

    if response.status_code == 200:
        # Get the result
        st.success("Response sent and received successfully! Request method: {}".format("cURL" if st.session_state.curl_selection else "Manual Selection"))
        st.session_state.result = response.json()
        print(f"Selected Tasks: {st.session_state.selected_tasks}")
        print(f"Response: {st.session_state.result}")

        if st.session_state.result["result"] == "success":
            st.session_state.server_output_success = True
            st.success("Request processed successfully!")
        else: # result = "error"
            st.session_state.server_output_success = False
            st.error("Error in processing the request. Please check the input and try again.")
            st.write("Error (String):")
            st.code(st.session_state.result["error"])
        # Handle the output for each task
        for task in st.session_state.selected_tasks:
            st.subheader(task.capitalize() + " Output", divider =True)
            for key, val_type in tasks[task]["output"].items():
                if "json" in val_type.lower().split():
                    st.write(f"{key.capitalize()} ({val_type}):")
                    st.json(st.session_state.result.get(key, "No data available."))
                else:
                    st.write(f"{key.capitalize()} ({val_type}):")
                    st.code(
                        st.session_state.result.get(key, "No data available."), language="plaintext"
                    )
    else:
        st.error(f"Error: {response.status_code}, {response.text}")
