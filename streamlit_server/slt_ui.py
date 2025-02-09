import os
import sys
from pathlib import Path

import pyperclip
import requests
import streamlit as st
from dotenv import load_dotenv

# Load environment variables
load_dotenv()

# Set up directories
homedir = Path(".")
prompts_dir = os.path.join(homedir, "prompts")
sys.path.append(prompts_dir)

# Default server IP
SERVER_IP = os.getenv("SERVER_IP", "http://10.134.13.102:7654")

# Streamlit App Header
st.title("LeanAide - AutoTA")
st.markdown("---")
# Function to copy text to clipboard
def copy_to_clipboard(text):
    try:
        pyperclip.copy(text)
        st.toast("✔️ Copied to clipboard!")
    except Exception as e:
        st.warning(f"⚠️ Failed to copy: {e}")

# Theorem Upload Section
st.header("Upload Theorem (Markdown File)")
uploaded_theorem = st.file_uploader("Upload a markdown file for the theorem", type="md")

if "theorem" not in st.session_state:
    st.session_state.theorem = ""

if uploaded_theorem:
    try:
        st.session_state.theorem = uploaded_theorem.read().decode("utf-8")
    except Exception as e:
        st.warning(f"⚠️ Failed to read the theorem file: {e}")

if st.session_state.theorem:
    st.subheader("Theorem Content:")
    theorem_box = st.text_area("Theorem", st.session_state.theorem, height=200, key="theorem_text")
    if st.button("Copy to Clipboard", key="copy_theorem"):
        copy_to_clipboard(st.session_state.theorem)


tasks = {
    "echo": {
        "input": {"data": "Json"},
        "placeholder": "Enter JSON data here...",
        "output": {"data": "Json"}
    },
    "translate_thm": {
        "input": {"text": "String"},
        "placeholder": "Enter theorem text here...",
        "output": {"theorem": "String"},
        "parameters": {
            "greedy": "Bool (default: true)",
            "fallback": "Bool (default: true)"
        }
    },
    "translate_def": {
        "input": {"text": "String"},
        "placeholder": "Enter definition text here...",
        "output": {"definition": "String"},
        "parameters": {
            "fallback": "Bool (default: true)"
        }
    },
    "theorem_doc": {
        "input": {"name": "String", "command": "String"},
        "placeholder": "Enter theorem here...",
        "output": {"doc": "String"}
    },
    "def_doc": {
        "input": {"name": "String", "command": "String"},
        "placeholder": "Enter definition here...",
        "output": {"doc": "String"}
    },
    "theorem_name": {
        "input": {"text": "String"},
        "placeholder": "Enter theorem text here...",
        "output": {"name": "String"}
    },
    "prove": {
        "input": {"theorem": "String"},
        "placeholder": "Enter theorem here...",
        "output": {"proof": "String"}
    },
    "structured_json_proof": {
        "input": {"theorem": "String", "proof": "String"},
        "placeholder": "Enter theorem here...",
        "output": {"json_structured": "Json"}
    },
    "lean_from_json_structured": {
        "input": {"json_structured": "String"},
        "placeholder": "Enter JSON structured proof here...",
        "output": {
            "lean_code": "String",
            "declarations": "List String",
            "top_code": "String"
        }
    },
    "elaborate": {
        "input": {"lean_code": "String", "declarations": "List Name"},
        "placeholder": "Enter Lean code here...",
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
st.subheader("Input Theorem")

# Input theorem
input_theorem = st.text_area("Theorem", "", placeholder = "Enter theorem text here...", height=100)
# checkbox to use the uploaded theorem
use_uploaded_theorem = st.checkbox("Use uploaded theorem", key="use_uploaded_theorem")
if use_uploaded_theorem:
    input_theorem = st.session_state.theorem

# Adding custom CSS for the multiselect component
st.markdown("""
    <style>
    .stMultiSelect [data-baseweb="tag"] {
        background-color: green !important;
    }
    </style>
    """, unsafe_allow_html=True)


selected_tasks = st.multiselect("Select Tasks:", list(tasks.keys()))

# Submit Request
if st.button("Submit Request"):
    request_payload = {"tasks": selected_tasks, "theorem": input_theorem}
    response = requests.post(SERVER_IP, json=request_payload)
    
    if response.status_code == 200:
        result = response.json()
        
        for task in selected_tasks:
            if "output" in tasks[task]:
                st.subheader(task.capitalize() + ": Output")
                for key, value in tasks[task]["output"].items():
                    st.subheader(key.capitalize())
                    if value.lower() == "json":
                        st.json(result.get(key, "No data available."))
                    else:
                        st.code(result.get(key, "No data available."), language="plaintext")
    else:
        st.error(f"Error: {response.status_code}, {response.text}")
