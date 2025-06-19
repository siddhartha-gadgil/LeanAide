import socket
import urllib
import json

import requests
import streamlit as st
from dotenv import load_dotenv

from api_server import HOST, PORT
from serv_utils import TASKS, get_actual_input, validate_input_type, copy_to_clipboard, log_section, button_clicked
from logging_utils import log_write, get_env

load_dotenv()

st.title("LeanAide: Server Response")
st.write(
    "Here you can send requests to the backend server and view the responses."
)
st.info("Ensure the Host information of the backend server to query is correct. Check out the sidebar for host information settings.")

if "api_host" not in st.session_state:
    st.session_state.api_host = HOST
if "api_port" not in st.session_state:
    st.session_state.api_port = PORT
if "task_tbd" not in st.session_state:
    st.session_state.task_tbd = []

if not st.session_state.val_input:
    st.session_state.val_input = {}

# Host Information Section
with st.sidebar:
    st.header("Server Response", divider = True)
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

st.header("Server Request", divider = True, help = "For your input request, this request will be sent to the backend server specified by you.")

with st.expander("Load input Conversation from JSON"):
    st.write("You can fill autofill inputs with your JSON file. This will overwrite any existing input(and ). Note: You can always rewrite them and generate new output with `Submit Button`")
    uploaded_file = st.file_uploader(
        "Upload a JSON file with input conversation",
        type="json",
        help="Upload a JSON file containing the input conversation. The file should be in valid JSON format.",
    )
    if uploaded_file:
        try:
            json_data = json.load(uploaded_file)
            st.session_state.val_input = json_data["input"]
            st.session_state.task_tbd = json_data["tasks"]
            st.session_state.temp_structured_json = json_data["input"]["json_structured"] if "json_structured" in json_data["input"] else {}
            st.session_state.self_input_button = True
            st.session_state.valid_input = True
            try:
                st.session_state.result = json_data["output"]
                st.session_state.request_button = True
                st.session_state.server_output_success = True
            except Exception as e:
                log_write("Streamlit", f"Error loading 'output' from JSON: {e}. Skipping")
                st.warning("No 'output' found in the JSON file(Skipping). You can still fill inputs and generate new output.")
 
            st.success("Input conversation loaded successfully.")
            log_write("Streamlit", "Input Conversation Loaded: Success")
        except json.JSONDecodeError as e:
            st.error(f"Invalid JSON format: {e}")
            log_write("Streamlit", f"Input Conversation Loaded: Error - {e}")

    if st.checkbox("View Format. This includes all possible inputs, tasks and outputs. Your input JSON should have only a subset of these."):
        format_data = {
            "input": {task: {**TASKS[task].get("input", {}), **TASKS[task].get("parameters", {})} for task in TASKS},
            "tasks": list(TASKS.keys()),
            "output": {task: TASKS[task]["output"] for task in TASKS}
        }
        st.json(format_data, expanded=False)

st.subheader("Structured Input: Select Tasks", help = "Select the tasks you want to perform and provide the necessary inputs.")

st.session_state._task_tbd = st.session_state.task_tbd
# list of tasks, each task has "name" field. use that
st.multiselect("Select task(s) to be performed:", list(reversed(list(TASKS.keys()))), help = "Select the tasks to be performed by the backend server. You can select multiple tasks.", key = "_task_tbd", on_change=lambda: setattr(st.session_state, "task_tbd", st.session_state._task_tbd))
st.session_state.selected_tasks = st.session_state.task_tbd

## Multiselect box color set
st.markdown("""
<style>
span[data-baseweb="tag"] {
  color: white;
  font-size: 17px;
  background-color: #4CAF50; /* Green background */
}

</style>

""", unsafe_allow_html=True)

if st.button("Build Query", help = "Provide inputs to the your selected tasks. Note: It is not compulsary to fill all of them.", type = "primary") or st.session_state.self_input_button:
    st.session_state.self_input_button = True
    for task in st.session_state.selected_tasks:
        # Get input for each task
        for key, val_type in TASKS[task].get("input",{}).items():
            help = f"Please provide input for `{key}` of type `{val_type}`."
            # Special case for input being "json_structured"
            if key.lower() == "json_structured":
                help += " Just paste your `json` object here."
                if st.button("Use Structured JSON generated", help = "Use the structured JSON generated in the `Structured Json` page of LeanAide website.", key = f"use_structured_json_{task}"):
                    if structured_json := st.session_state.get("structured_proof", {}):
                        st.session_state.temp_structured_json = structured_json 
                    else:
                        st.warning("No structured JSON found. Please generate it first in the 'Structured Json' page.")
 
                val_in = st.text_area(f"{task.capitalize()} - {key} ({val_type}):", help = help, placeholder = "{'key': 'value'}", value = st.session_state.temp_structured_json)
                st.session_state.temp_structured_json = val_in  # Store the structured JSON input

            # Other cases for input
            elif "json" in key.lower() and key.lower() != "json_structured":
                help += " Just paste your `json` object here."
                val_in = st.text_area(f"{task.capitalize()} - {key} ({val_type}):", help = help, placeholder = "{'key': 'value', etc}", value = st.session_state.val_input.get(key, ""))
            else:
                val_in = st.text_area(f"{task.capitalize()} - {key} ({val_type}):", help = help, value = st.session_state.val_input.get(key, ""))

            if str(val_in).strip() == "":
                st.session_state.val_input[key] = None
            ## Put input value in session state
            if val_in:
                inp_type, st.session_state.val_input[key] = get_actual_input(val_in)
                if validate_input_type(inp_type, val_type):
                    st.session_state.valid_input = True
                else:
                    st.warning(
                        f"Invalid input type for {key}. Expected `{val_type}`, got `{inp_type.__name__}`. See help for each input for more info. Please try again."
                    )
                    st.session_state.valid_input = False
                    st.session_state.val_input[key] = None

        # Parameters for each task
        for param, param_type in TASKS[task].get("parameters", {}).items():
            if "boolean" in param_type.lower() or "bool" in param_type.lower():
                st.session_state.valid_input = True

                # Checked for True, Unchecked for False
                default_val = True if "true" in param_type.lower() else False
                st.session_state.val_input[param] = default_val
                checkbox_state = st.checkbox(
                    f"{task.capitalize()} - {param} (Boolean)",
                    help="Checked box: `True`, Unchecked box: `False`",
                    value=default_val
                )
                st.session_state.val_input[param] = checkbox_state
            else:
                help = f"Please provide a value for `{param}` of type `{param_type}`. If you want to skip this parameter, just leave it unchecked."
                if param_in := st.text_input(f"{task.capitalize()} - {param} ({param_type}):", help=help):
                    st.session_state.val_input[param] = param_in
                    st.session_state.valid_input = True

    if st.session_state.valid_input:
        st.subheader("Query Obtained", help = "Note that default values will be used for any parameters that you did not provide input for.")
        # Remove the values in val_input that are empty strings or None
        st.session_state.val_input = {k: v for k, v in st.session_state.val_input.items() if v not in ["", None]}
        st.json(st.session_state.val_input)
        log_write("Streamlit", "Query Obtained: Success")

st.write("")
# Show Response function
def show_response():
    for task in st.session_state.selected_tasks:
        st.subheader(task + " Output", divider =True)
        for key, val_type in TASKS[task]["output"].items():
            if "json" in val_type.lower().split():
                st.write(f"{key.capitalize()} ({val_type}):")
                json_out = st.session_state.result.get(key) or {}
                st.json(json_out)
                copy_to_clipboard(str(json_out))
            else:
                st.write(f"{key.capitalize()} ({val_type}):")
                st.code(
                    st.session_state.result.get(key) or "No data available.", language="plaintext", wrap_lines = True
                )
                if "lean_code" in key.lower():
                    code = st.session_state.result.get(key, "-- No Lean code available")
                    code = f"import Mathlib\n{code.strip()}" if "import Mathlib" not in code else code
                    if code not in ["-- No Lean code available", "No data available."]:
                        st.link_button("Open Lean Web IDE", help="Open the Lean code in the Lean Web IDE.", url = f"https://live.lean-lang.org/#code={urllib.parse.quote(code)}")

def dummy_request():
    command = get_env("LEANAIDE_COMMAND", "lake exe leanaide_process")
    for flag in ["--auth_key", "--model"]:
        if flag not in command:
            break
    else:
        return
        
    request_payload = {
        "tasks": ["echo"],
        "data": "Dummy Request."
    }
    response = requests.post(
        f"http://{st.session_state.api_host}:{st.session_state.api_port}", json=request_payload
    )

    if response.status_code == 200:
        log_write("Streamlit", "Dummy Request: Success")
    else:
        log_write("Streamlit", f"Dummy Request: Error - {response.status_code} - {response.text}")

    return

# Submit Request Section. 
submit_response_button =  st.button("Submit Request", on_click= button_clicked("request_button"), type = "primary", help = "You can submit your request here. The request will be sent to the backend server specified in the Host Information section.")
if submit_response_button or st.session_state.request_button:
    dummy_request() # Just a dummy request
    request_payload = {}
    if not st.session_state.selected_tasks:
        st.warning("Please Input tasks to be performed.")
        log_write("Streamlit", "Request Payload: Invalid Input")
    elif not st.session_state.valid_input:
        st.warning("Please provide valid inputs for the selected tasks.")
        log_write("Streamlit", "Request Payload: Invalid Input")
    else:
        server_tasks = [TASKS[task]["task_name"] for task in st.session_state.selected_tasks]
        request_payload = {"tasks": server_tasks, **st.session_state.val_input}

        if submit_response_button:
            with st.spinner("Request sent. Please wait for a short while..."): 
                log_write("Streamlit", f"Request Payload: {request_payload}")
                response = requests.post(
                    f"http://{st.session_state.api_host}:{st.session_state.api_port}", json=request_payload
                )

            if response.status_code == 200:
                # Get the result
                st.success("Response sent and received successfully!")
                st.session_state.result = response.json()
                log_write("Streamlit", f"Selected Tasks: {st.session_state.selected_tasks}")
                log_write("Streamlit", f"Response: {st.session_state.result}")

                try:
                    if st.session_state.result["result"] == "success":
                        st.session_state.server_output_success = True
                        st.success("Request processed successfully!")
                    else: # result = "error"
                        st.session_state.server_output_success = False
                        st.error("Error in processing the request. Please check the input and try again.")
                        st.write("Error (String):")
                        st.code(st.session_state.result["error"])
                    log_write("Streamlit", "Server Output: Success")
                except Exception as e:
                    st.session_state.server_output_success = False
                    st.error(f"Error in processing the request: {e}")
                    st.write("Response (String):")
                    st.code(str(st.session_state.result))
                    log_write("Streamlit", f"Server Output: Error - {e}")

            else:
                st.session_state.server_output_success = False
                st.error(f"Error: {response.status_code}, {response.text}")
                log_write("Streamlit", f"Server Response Error: {response.status_code} - {response.text}")
                # Handle the output for each task
        if st.session_state.server_output_success:
            show_response()
        else:
            st.error("No output available. Please check the input and try again.")
            try:
                st.error(st.session_state.result.get("error", "No error message provided."))
            except Exception as e:
                st.error(f"Error retrieving error from server: {e}")
                pass
            log_write("Streamlit", "Server Output: No output available.")


elif st.session_state.request_button:
    show_response()

st.divider()

if st.checkbox("`Download Conversation:` Save your input and output response in a JSON file and download it."):
    if st.session_state.selected_tasks and st.session_state.valid_input:
        conversation_data = {
            "tasks": st.session_state.selected_tasks,
            "input": st.session_state.val_input,
            "output": st.session_state.result if hasattr(st.session_state, 'result') else {}
        }
        st.download_button(
            label="Download Conversation",
            data=json.dumps(conversation_data),
            file_name="conversation.json",
            mime="application/json"
        )
        log_write("Streamlit", "Conversation Downloaded")
    else:
        st.warning("Please provide valid input and output before downloading the conversation.")

log_section()