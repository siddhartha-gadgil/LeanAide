import json

import requests
import streamlit as st
from streamlit import session_state as sts
from dotenv import load_dotenv

from serv_utils import TASKS, lean_code_button, get_actual_input, validate_input_type, copy_to_clipboard, log_section, button_clicked, request_server, host_information, lean_code_cleanup
from logging_utils import log_write, get_env

load_dotenv()

st.title("LeanAide: Server Response")
st.write(
    "Here you can send requests to the backend server and view the responses."
)
st.info("Ensure the Host information of the backend server to query is correct. Check out the sidebar for host information settings.")

if "task_tbd" not in sts:
    sts.task_tbd = []

if not sts.val_input:
    sts.val_input = {}

# Host Information Section
with st.sidebar:
    st.header("Server Response", divider = True)
    with st.expander("Host Information", expanded=False):
        host_information()

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
            sts.val_input = json_data["input"]
            sts.task_tbd = json_data["tasks"]
            sts.temp_structured_json = json_data["input"]["json_structured"] if "json_structured" in json_data["input"] else {}
            sts.proof = json_data.get("proof", "")
            sts.theorem = json_data.get("theorem", "")
            sts.self_input_button = True
            sts.valid_input = True
            try:
                sts.result = json_data["output"]
                sts.request_button = True
                sts.server_output_success = True
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

sts._task_tbd = sts.task_tbd
# list of tasks, each task has "name" field. use that
st.multiselect("Select task(s) to be performed:", list(reversed([task for task in TASKS.keys() if TASKS[task].get("commonly_used", False)])), help = "Select the tasks to be performed by the backend server. You can select multiple tasks.", key = "_task_tbd", on_change=lambda: setattr(sts, "task_tbd", sts._task_tbd))
sts.selected_tasks = sts.task_tbd

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
if sts.self_input_button or sts.selected_tasks:
    sts.self_input_button = True
    
    for task in sts.selected_tasks: 
        # Get input for each task
        for key, val_type in TASKS[task].get("input", {}).items():
            help_text = f"Please provide input for `{key}` of type `{val_type}`."
            
            # Special case for input being "json_structured"
            if key.lower() == "json_structured":
                help_text += " Just paste your `json` object here."
                
                col1, col2 = st.columns([1, 2])
                with col1:
                    if st.button(
                        "Input JSON Yourself", 
                        help="Input your own JSON object for structured input.", 
                        key=f"input_json_{task}"
                    ):
                        sts.temp_structured_json = sts.temp_structured_json or ""
                        
                with col2:
                    if st.button(
                        "Use Generated Structured JSON", 
                        help="Use the structured JSON generated in the 'Structured Json' page of LeanAide website.", 
                        key=f"use_structured_json_{task}"
                    ):
                        if structured_json := sts.get("structured_proof", {}):
                            sts.temp_structured_json = structured_json 
                        else:
                            st.warning("No structured JSON found. Please generate it first in the 'Structured Json' page.")

                val_in = st.text_area(
                    f"{task.capitalize()} - {key} ({val_type}):", 
                    help=help_text, 
                    placeholder="{'key': 'value'}", 
                    value=sts.temp_structured_json,
                    height=150
                )
                sts.temp_structured_json = val_in

            # Other JSON inputs
            elif "json" in key.lower() and key.lower() != "json_structured":
                help_text += " Just paste your `json` object here."
                val_in = st.text_area(
                    f"{task.capitalize()} - {key} ({val_type}):", 
                    help=help_text, 
                    placeholder="{'key': 'value', etc}", 
                    value=sts.val_input.get(key, ""),
                    height=120
                )
            
            # Text inputs
            else:
                val_in = st.text_area(
                    f"{task.capitalize()} - {key} ({val_type}):", 
                    help=help_text, 
                    value=sts.val_input.get(key, ""),
                    height=100
                )

            # Clean lean code if needed
            if key.lower() == "lean_code":
                val_in = lean_code_cleanup(val_in, elaborate=True)

            # Process input value
            if str(val_in).strip() == "":
                sts.val_input[key] = None
            elif val_in:
                inp_type, sts.val_input[key] = get_actual_input(val_in)
                if validate_input_type(inp_type, val_type):
                    sts.valid_input = True
                else:
                    st.error(
                        f"Invalid input type for `{key}`. Expected `{val_type}`, got `{inp_type.__name__}`. "
                        f"See help for each input for more info."
                    )
                    sts.valid_input = False
                    sts.val_input[key] = None

        # Parameters section for each task
        parameters = TASKS[task].get("parameters", {})
        if parameters: 
            for param, param_type in parameters.items():
                if "boolean" in param_type.lower() or "bool" in param_type.lower():
                    sts.valid_input = True
                    default_val = "true" in param_type.lower()
                    
                    checkbox_state = st.checkbox(
                        f"{task.capitalize()} - {param} (Boolean)",
                        help="Checked: `True`, Unchecked: `False`",
                        value=default_val
                    )
                    sts.val_input[param] = checkbox_state
                    
                else:
                    help_text = (
                        f"Please provide a value for `{param}` of type `{param_type}`. "
                        f"Leave empty to use default value."
                    )
                    
                    param_input = st.text_input(
                        f"{task.capitalize()} - {param} ({param_type}):", 
                        help=help_text
                    )
                    
                    if param_input:
                        sts.val_input[param] = param_input
                        sts.valid_input = True

    # Control buttons
    st.divider()
    
    if st.button("🗑️ Clear Current Query", help="Clear the current query and start fresh."):
        sts.val_input = {}
        sts.temp_structured_json = ""
        st.success("Query cleared successfully!")
        st.rerun()

    # Display query results
    if sts.valid_input:
        st.subheader("Query Obtained", divider=True, help="Default values will be used for any parameters not provided.")
        
        # Clean up empty values
        if sts.val_input:
            sts.val_input = {k: v for k, v in sts.val_input.items() if v not in ["", None]}
        
        with st.container():
            st.success("Query successfully validated!")
            st.json(sts.val_input, expanded=True)
            
        log_write("Streamlit", "Query Obtained: Success")


st.write("")
# Show Response function
def show_response():
    for task in sts.selected_tasks:
        st.subheader(task + " Output", divider =True)
        if "elaborate" in task.lower().strip():
            if sts.result["result"] == "success":
                st.success("Successful Elaboration => Lean Code is **Correct**.")
            else:
                st.error("Elaboration failed. The Lean code produced may be **incorrect**.")

        for key, val_type in TASKS[task]["output"].items():
            if "json" in val_type.lower().split():
                st.write(f"{key.capitalize()} ({val_type}):")
                json_out = sts.result.get(key) or {}
                st.json(json_out)
                copy_to_clipboard(str(json_out))
            else:
                st.write(f"{key.capitalize()} ({val_type}):")
                st.code(
                    sts.result.get(key) or "No data available.", language="plaintext", wrap_lines = True
                )
                if "lean_code" in key.lower():
                    lean_code_button("result", key, task)
 
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
        f"http://{sts.api_host}:{sts.api_port}", json=request_payload
    )

    if response.status_code == 200:
        log_write("Streamlit", "Dummy Request: Success")
    else:
        log_write("Streamlit", f"Dummy Request: Error - {response.status_code} - {response.text}")

    return

# Submit Request Section. 
submit_response_button =  st.button("Submit Request", on_click= button_clicked("request_button"), type = "primary", help = "You can submit your request here. The request will be sent to the backend server specified in the Host Information section.")
if submit_response_button or sts.request_button:
    dummy_request() # Just a dummy request
    request_payload = {}
    if not sts.selected_tasks:
        st.warning("Please Input tasks to be performed.")
        log_write("Streamlit", "Request Payload: Invalid Input")
    elif not sts.valid_input:
        st.warning("Please provide valid inputs for the selected tasks.")
        log_write("Streamlit", "Request Payload: Invalid Input")
    else:
        server_tasks = [TASKS[task]["task_name"] for task in sts.selected_tasks]
        request_payload = {"tasks": server_tasks, **sts.val_input}

        if submit_response_button:
            try:
                request_server(request_payload=request_payload, task_header="Streamlit", success_key="server_output_success", result_key="result")
                sts.server_output_success = True
            except Exception as e:
                st.error(f"Error while sending request to server: {e}")
                log_write("Streamlit", f"Request Payload: Error - {e}")
                sts.server_output_success = False
                sts.result = {}

        if sts.server_output_success:
            show_response()
        else:
            # If server itself gives "error" output, it goes here
            st.error("No output available. Please check the input and try again.")
            try:
                st.error(f"Error: {sts.result["error"]}")
            except Exception as e:
                st.error(f"Error retrieving error from server: {e}")
                pass
            log_write("Streamlit", "Server Output: No output available.")


elif sts.request_button:
    show_response()

st.divider()

if st.checkbox("`Download Conversation:` Save your input and output response in a JSON file and download it."):
    if sts.selected_tasks and sts.valid_input:
        conversation_data = {
            "tasks": sts.selected_tasks,
            "input": sts.val_input,
            "output": sts.result if hasattr(sts, 'result') else {},
            "theorem": sts.theorem if hasattr(sts, 'theorem') else "",
            "proof": sts.proof if  hasattr(sts, 'proof') else "",
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