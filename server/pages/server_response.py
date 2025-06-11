import socket
from pathlib import Path
import urllib
import requests
import streamlit as st
from dotenv import load_dotenv

from api_server import HOST, PORT, LOG_FILE
from serv_utils import *

load_dotenv()

st.sidebar.header("Server Response")

st.title("LeanAide: Server Response")
st.write(
    "Here you can send requests to the backend server and view the responses. You can either paste a cURL request or fill the request yourself."
)

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
for key in ["parsed_curl", "selected_tasks", "self_selection", "curl_selection", "val_input", "result"]:
    if key not in st.session_state:
        st.session_state[key] = None
for key in ["curl_botton", "request_button", "self_input_button", "ignore_curl_ip_port", "server_output_success", "valid_self_input"]:
    if key not in st.session_state:
        st.session_state[key] = False

st.header("Server Request", divider = True, help = "You can either paste a cURL request or fill the request yourself. The request will be sent to the backend server specified by you.")

st.subheader("Structured Input: Select Tasks", help = "Select the tasks you want to perform and provide the necessary inputs.")
st.session_state.self_selection = True
# list of tasks, each task has "name" field. use that

st.session_state.selected_tasks = st.multiselect("Select tasks to be performed:", get_names_by_tasks(), help = "Select the tasks to be performed by the backend server. You can select multiple tasks.")
st.session_state.selected_tasks = get_task_list_by_name(st.session_state.selected_tasks)

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

st.session_state.val_input = {}
if st.button("Give Input", help = "Provide inputs to the your selected tasks. Note: It is not compulsary to fill all of them.") or st.session_state.self_input_button:
    st.session_state.self_input_button = True
    for task in st.session_state.selected_tasks:
        # Get input for each task
        for key, val_type in TASKS[task].get("input", {}).items():
            help = f"Please provide input for `{key}` of type `{val_type}`."
            if "json" in key.lower():
                help += " Just paste your `json` object here."
                val_in = st.text_area(f"{task.capitalize()} - {key} ({val_type}):", help = help, placeholder = "{'key': 'value', etc}", height = 68)
            else:
                val_in = st.text_input(f"{task.capitalize()} - {key} ({val_type}):", help = help)
            if val_in:
                inp_type, st.session_state.val_input[key] = get_actual_input(val_in)
                if validate_input_type(inp_type, val_type):
                    st.session_state.valid_self_input = True
                else:
                    st.warning(
                        f"Invalid input type for {key}. Expected `{val_type}`, got `{inp_type.__name__}`. See help for each input for more info. Please try again."
                    )
                    st.session_state.valid_self_input = False

        # Parameters for each task
        for param, param_type in TASKS[task].get("parameters", {}).items():
            if "boolean" in param_type.lower() or "bool" in param_type.lower():
                st.session_state.valid_self_input = True

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
                    st.session_state.valid_self_input = True
            
    if st.session_state.valid_self_input:
        st.subheader("Query Obtained", help = "Note that default values will be used for any parameters that you did not provide input for.")
        st.json(st.session_state.val_input)

## CURL REQUEST SECTION
if st.checkbox(
    "If you have a cURL request you will like to request, pls check this box. This will ignore any your entered inputs in the previous section.",
    value=False,
):
    st.subheader("Raw cURL Request")
    st.session_state.self_selection = False
    # cURL Request Section
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

# Submit Request Section. Common to Curl and self Selection
if st.button("Submit Request", on_click= button_clicked("request_button"), type = "primary", help = "For both cURL and Self input, you can submit your request here. The request will be sent to the backend server specified in the Host Information section.") or st.session_state.request_button:
    if not st.session_state.curl_selection and not st.session_state.self_selection:
        st.warning("Please either paste a cURL request or Input tasks.")
        st.stop()
    if st.session_state.self_selection: # Makes the request payload from self selection
        request_payload = {"tasks": st.session_state.selected_tasks, **st.session_state.val_input}
    else: # Makes the request payload from cURL
        request_payload = st.session_state.parsed_curl.get("data", {})
        if not request_payload:
            st.warning(
                "No data found in the cURL request. Please check the cURL command."
            )
            st.stop()
    with st.spinner("Request sent. Please wait for a short while..."):
        log_write("Streamlit", f"Request Payload: {request_payload}")
        response = requests.post(
            f"http://{st.session_state.api_host}:{st.session_state.api_port}", json=request_payload
        )

    if response.status_code == 200:
        # Get the result
        st.success("Response sent and received successfully! Request method: {}".format("cURL" if st.session_state.curl_selection else "Self Input"))
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
        except Exception as e:
            st.session_state.server_output_success = False
            st.error(f"Error in processing the request: {e}")
            st.write("Response (String):")
            st.code(str(st.session_state.result))
        # Handle the output for each task
        for task in st.session_state.selected_tasks:
            st.subheader(TASKS[task]["name"] + " Output", divider =True)
            for key, val_type in TASKS[task]["output"].items():
                if "json" in val_type.lower().split():
                    st.write(f"{key.capitalize()} ({val_type}):")
                    json_out = st.session_state.result.get(key, {})
                    st.json(json_out)
                    if st.button(f"Copy to Clipboard", key=f"copy_btn_{key}"):
                        copy_to_clipboard(str(json_out))
                else:
                    st.write(f"{key.capitalize()} ({val_type}):")
                    st.code(
                        st.session_state.result.get(key, "No data available."), language="plaintext"
                    )
                    if "lean_code" in key.lower():
                        code = st.session_state.result.get(key, "-- No Lean code available")
                        st.link_button("Open Lean Web IDE", help="Open the Lean code in the Lean Web IDE.", url = f"https://live.lean-lang.org/#code={urllib.parse.quote(code)}")
    else:
        st.error(f"Error: {response.status_code}, {response.text}")

## LOGS SECTION
if "log_cleaned" not in st.session_state:
    st.session_state.log_cleaned = False

st.subheader("Server Stdout/Stderr", help = "Logs are written to LeanAide-Streamlit-Server log file and new logs are updated after SUBMIT REQUEST button is clicked. You might see old logs as well.")
with st.expander("Click to view Server logs", expanded=False):
    if log_out := log_server():
        height = 500 if len(log_out) > 1000 else 300
        st.text_area(
            "Server Logs",
            value=log_out if not st.session_state.log_cleaned else "",
            height= height,
            placeholder="No logs available yet.",
            disabled=True,
            help="This shows the server logs. It is updated after each request is processed.",
        )

    else:
        st.code("No logs available yet.", language="plaintext")
        
    @st.dialog("Confirm Server Log Cleaning")
    def clean_log():
        """Function to clean the server logs."""
        st.write("Are you sure you want to clean the server logs? This will delete all the logs in the server log file.")
        if st.button("Yes"):
            st.session_state.log_cleaned = True
        if st.button("No"):
            st.session_state.log_cleaned = False

        if st.session_state.log_cleaned:
            try:
                with open(LOG_FILE, "w") as f:
                    f.write("")  # Clear the log file
                st.success("Server logs cleaned successfully! Please UNCHECK THE BOX to avoid cleaning again.")
            except Exception as e:
                st.error(f"Error cleaning server logs: {e}")
        
        st.session_state.log_cleaned = False
    if st.checkbox("Clean Server Logs. Read the help text before checking this box", value=st.session_state.log_cleaned, key="clean_log", help="Check this box to clean the server logs. This will delete all the logs in the server log file."):
        clean_log()