import os
import sys
from pathlib import Path

import pyperclip
import requests
import streamlit as st
from dotenv import load_dotenv

load_dotenv()

homedir = Path(".")
prompts_dir = os.path.join(homedir, "prompts")
sys.path.append(prompts_dir)

SERVER_IP = os.getenv("SERVER_IP", "10.134.13.102:7654")

# Streamlit App
st.title("LeanAide - AutoTA")

provider_info = {
    "OPENAI": {
        "name": "OpenAI",
        "default_model": "gpt-4o",
        "default_api_key": os.getenv("OPENAI_API_KEY", ""),
    },
    "Gemini": {
        "name": "Gemini",
        "default_model": "gemini-1.5-pro",
        "default_api_key": os.getenv("GEMINI_API_KEY", ""),
    },
}

# API Credentials Section
with st.expander("Credentials"):
    # Provider selection
    provider = st.selectbox("Select Provider:", list(provider_info.keys()), index=0)

    # Dynamically update API Key and Model fields based on the provider
    selected_provider = provider_info[provider]

    if provider == "Gemini":
        # Warning if Gemini is selected
        st.warning("Gemini API is not yet supported. Please select OpenAI for now.")
    else:
        # API Key Input with masked display
        api_key_placeholder = f"{selected_provider['default_api_key'][:15]}{'*' * (len(selected_provider['default_api_key']) - 15)}" if selected_provider['default_api_key'] else ""
        api_key = st.text_input(
            "API Key:",
            value=api_key_placeholder,
            type="password",
            help="Hover to see the key, edit if needed."
        )

        # Model selection text boxes
        model_image_to_text = st.text_input(
            "Model for Image to Text:",
            value=selected_provider["default_model"],
            help="Specify the model for Image to Text. Check out list of OpenAI Models [↗](https://platform.openai.com/docs/models)"
        )
        model_json_generator = st.text_input(
            "Model for JSON Generator:",
            value=selected_provider["default_model"],
            help="Specify the model for JSON Generator. Check out list of OpenAI Models [↗](https://platform.openai.com/docs/models)"
        )
# Function to copy text to clipboard and show confirmation
def copy_to_clipboard(text):
    try:
        pyperclip.copy(text)
        st.toast("Copied to clipboard!", icon="✔️")
    except Exception as e:
        st.warning(f"Failed to copy: {e}")

# Function to trigger file download
# Create a temporary directory if it doesn't exist
temp_dir = "temp"
def download_file(file_content, file_name):
    st.download_button(label="Download File", data=file_content, file_name=file_name, mime="text/plain")

st.header("Upload Theorem (Markdown File)")
uploaded_theorem = st.file_uploader("Upload a markdown file for the theorem", type="md")

if "theorem" not in st.session_state:
    st.session_state.theorem = ""

if uploaded_theorem:
    try:
        st.session_state.theorem = uploaded_theorem.read().decode("utf-8")
    except Exception as e:
        st.warning(f"Failed to read the theorem file: {e}")

if st.session_state.theorem:
    st.subheader("Theorem Content:")
    theorem_box = st.text_area("Theorem", st.session_state.theorem, height=200, key="theorem_text")
    if st.button("Copy to Clipboard", key="copy_theorem"):
        copy_to_clipboard(st.session_state.theorem)

# Lean Checker Tasks
tasks = {
    "echo": {
        "input": {"data": "Json"},
        "output": {"data": "Json"}
    },
    "translate_thm": {
        "input": {"text": "String"},
        "output": {"theorem": "String"},
        "parameters": {
            "greedy": "Bool (default: true)",
            "fallback": "Bool (default: true)"
        }
    },
    "translate_def": {
        "input": {"text": "String"},
        "output": {"definition": "String"},
        "parameters": {
            "fallback": "Bool (default: true)"
        }
    },
    "theorem_doc": {
        "input": {"name": "String", "command": "String"},
        "output": {"doc": "String"}
    },
    "def_doc": {
        "input": {"name": "String", "command": "String"},
        "output": {"doc": "String"}
    },
    "theorem_name": {
        "input": {"text": "String"},
        "output": {"name": "String"}
    },
    "prove": {
        "input": {"theorem": "String"},
        "output": {"proof": "String"}
    },
    "structured_json_proof": {
        "input": {"theorem": "String", "proof": "String"},
        "output": {"json_structured": "Json"}
    },
    "lean_from_json_structured": {
        "input": {"json_structured": "String"},
        "output": {
            "lean_code": "String",
            "declarations": "List String",
            "top_code": "String"
        }
    },
    "elaborate": {
        "input": {"lean_code": "String", "declarations": "List Name"},
        "output": {
            "logs": "List String",
            "sorries": "List Json"
        },
        "parameters": {
            "top_code": "String (default: \"\")",
            "describe_sorries": "Bool (default: false)"
        }
    }
}

st.header("Drongo Magica")
st.expander("Get Your Theorem Checked here. Don't miss this chance to meet Mr. Drongo!", expanded=False)


st.markdown(
    """
    <style>
    .stMultiSelect [data-baseweb="tag"] {
        background-color: green;
    }
    </style>
    """,
    unsafe_allow_html=True
)
st.subheader("Step 1: Select Input Tasks")
selected_inputs = st.multiselect("Select Input Tasks:", list(tasks.keys()))

inputs = {}
parameters = {}
if st.button("Give Input"):
    for task in selected_inputs:
        inputs[task] = {}
        for key, value in tasks[task].get("input", {}).items():
            inputs[task][key] = st.text_input(f"{task.capitalize()} - {key} ({value}):")
        for param, param_type in tasks[task].get("parameters", {}).items():
            parameters[param] = st.checkbox(f"{task} - {param} ({param_type})")


st.subheader("Step 2: Select Processing Tasks")
selected_tasks = [task for task in tasks.keys() if task not in selected_inputs]
selected_tasks = st.multiselect("Select Processing Tasks:", selected_tasks)


if st.button("Submit Request"):
    request_payload = {"tasks": selected_tasks, **inputs, **parameters}
    response = requests.post(SERVER_IP, json=request_payload)
    
    if response.status_code == 200:
        result = response.json()
        
        for task in selected_tasks:
            if "output" in tasks[task]:
                st.subheader(task.capitalize() + " Output")
                for key, value in tasks[task]["output"].items():
                    if isinstance(result.get(key), list):
                        st.json(result.get(key, "No data available."))
                    else:
                        st.code(result.get(key, "No data available."), language="plaintext")
    else:
        st.error(f"Error: {response.status_code}, {response.text}")


if os.path.exists(temp_dir):
    for file in os.listdir(temp_dir):
        os.remove(os.path.join(temp_dir, file))
    os.rmdir(temp_dir)
