import streamlit as st
import json
import os
from pathlib import Path

import requests
from dotenv import load_dotenv
from PIL import Image
from streamlit_sortables import sort_items
# from gpt_structured import gen_structure_proof, solution_from_images
from serv_utils import copy_to_clipboard, download_file, HOMEDIR

load_dotenv()

st.title("LeanAide: Structured Json Output")
st.write("Here you can input your theorem-proof/paper, etc. and generate structured JSON output using LeanAide Schema's.")

st.sidebar.header("Structured Json")

provider_info = {
    "OpenAI": {
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
        api_key_placeholder = (
            f"{selected_provider['default_api_key'][:15]}{'*' * (len(selected_provider['default_api_key']) - 15)}"
            if selected_provider["default_api_key"]
            else ""
        )
        api_key = st.text_input(
            "API Key:",
            value=api_key_placeholder,
            type="password",
            help="Hover to see the key, edit if needed.",
        )

        # Model selection text boxes
        model_image_to_text = st.text_input(
            "Model for Image to Text:",
            value=selected_provider["default_model"],
            help="Specify the model for Image to Text. Check out list of OpenAI Models [↗](https://platform.openai.com/docs/models)",
        )
        model_json_generator = st.text_input(
            "Model for JSON Generator:",
            value=selected_provider["default_model"],
            help="Specify the model for JSON Generator. Check out list of OpenAI Models [↗](https://platform.openai.com/docs/models)",
        )

# Create a temporary directory if it doesn't exist
temp_dir = "leanaide_st_temp"

# Create session state variables if they don't exist
for key in ["image_paths", "proof", "theorem", "structured_proof", "pdf_paper"]:
    if key not in st.session_state:
        st.session_state[key] = None

for key in ["input_upload_files", "input_text_content", "input_markdown_file"]:
    if key not in st.session_state:
        st.session_state[key] = False

st.header("Input PDF/Images/Markdown of Paper/Theorem-Proof", divider = True)
# Get input method from user
input_options = ["Upload PDF Paper", "Input Theorem-Proof"] 
input_captions = ["For Research Papers", "For single Theorem-Proof or Problems"]
input_method = st.radio("Choose the input method:", options = input_options)

# PDF upload section
if input_method == input_options[0]:
    st.session_state.input_upload_files = True
    st.subheader("Upload Paper PDF")
    uploaded_pdf = st.file_uploader("Upload a PDF file for the paper", type="pdf")

    if uploaded_pdf:
        try:
            # Save the uploaded PDF to a temporary location
            pdf_path = os.path.join(temp_dir, "pdf_paper.pdf")
            with open(pdf_path, "wb"):
                st.session_state.pdf_paper = uploaded_pdf.read()
            st.success("PDF uploaded successfully.")
        except Exception as e:
            st.warning(f"Failed to upload the PDF file: {e}")

# Helper function for image inputs
def handle_image_input(key: str):
    """Handles image input and reordering. key is the `st.session_state[key]` where output text will be stored."""
    uploaded_images = st.file_uploader(
        "Upload multiple images", type=["png", "jpg", "jpeg"], accept_multiple_files=True
    )
    if uploaded_images:
        st.write("Images uploaded successfully. You can reorder them below:")
        os.makedirs(temp_dir, exist_ok=True)

        # Save uploaded images to the temporary directory
        for uploaded_file in uploaded_images:
            img = Image.open(uploaded_file)
            temp_path = os.path.join(temp_dir, uploaded_file.name)
            img.save(temp_path)
            if temp_path not in st.session_state.image_paths:
                st.session_state.image_paths.append(temp_path)

        # Allow reordering of images using drag-and-drop functionality
        reordered_images = sort_items(
            items=[
                os.path.basename(path) for path in st.session_state.image_paths
            ],  # Display only filenames
            direction="vertical",
        )
        st.session_state.image_paths = [
            os.path.join(temp_dir, filename) for filename in reordered_images
        ]

        if st.button("Generate Image to Text"):
            with st.spinner("Processing reordered images..."):
                try:
                    # st.session_state.proof = solution_from_images(st.session_state.image_paths)
                    st.session_state[key] = f"Sample {key} text generated from images." #TODO:
                except Exception as e:
                    st.warning(f"Failed to process images: {e}")

        if st.session_state.proof:
            st.subheader(f"Generated {key}:")
            st.session_state[key] = st.text_area(
                key.capitalize(), st.session_state.proof, height=200, key=f"{key}_text"
            )
            col1, col2 = st.columns([1, 1])
            with col1:
                if st.button("Copy to Clipboard", key=f"copy_{key}"):
                    copy_to_clipboard(st.session_state[key])
            with col2:
                download_file(st.session_state[key], "proof.txt")

# Helper function for markdown input
def handle_markdown_input(key: str):
    """Handles markdown input. key is the `st.session_state[key]` where output text will be stored."""
    st.subheader("Upload Markdown/Text File")
    uploaded_markdown = st.file_uploader("Upload a markdown file", type=["md", "txt"])
    file_type = "Markdown" if uploaded_markdown and uploaded_markdown.name.endswith(".md") else "Text"
    if uploaded_markdown:
        try:
            st.session_state[key] = uploaded_markdown.read().decode("utf-8")
            st.success(f"{file_type} file uploaded successfully.")
        except Exception as e:
            st.warning(f"Failed to read the {file_type} file: {e}")

    if st.session_state[key]:
        st.subheader(f"{file_type} Content:")
        st.session_state[key] = st.code(f"No {key} text found.", st.session_state[key], height=200)

# Helper function for text input
def handle_text_input(key: str):
    st.session_state.input_text_content = True
    default_text = f"Enter the {key} text here..."
    st.session_state.theorem = st.text_area(
        key.capitalize(),
        value = default_text,
        height=200,
    )
    if st.session_state[key] != default_text or st.session_state[key] != "":
        st.success(f"{key.capitalize()} received successfully.")
    else:
        st.warning(f"Please enter {key.capitalize} text before proceeding.")

# Theorem-Proof section
if input_method == input_options[1]:
    st.session_state.input_upload_files = True
    # Upload Theorem
    st.subheader("Input Theorem")
    thm_opt = st.radio("Choose input method for theorem:", options = ["Upload Images", "Upload Markdown/Text File", "Input Text"],)
    if "image" in thm_opt.lower():
        st.session_state.input_upload_files = True
        handle_image_input("theorem") 
    elif "text" in thm_opt.lower():
        st.session_state.input_markdown_file = True
        handle_markdown_input("theorem")
    else:
        st.session_state.input_text_content = True
        handle_text_input("theorem")

    # Upload Proof
    st.header("Input Proof")
    proof_opt = st.radio("Choose input method for proof:", options = ["Upload Images", "Upload Markdown/Text File", "Input Text"],)
    if "image" in proof_opt.lower():
        st.session_state.input_upload_files = True
        handle_image_input("proof")
    elif "text" in proof_opt.lower():
        st.session_state.input_markdown_file = True
        handle_markdown_input("proof")
    else:
        st.session_state.input_text_content = True
        handle_text_input("proof")

if st.button("Generate Structured Proof"):
    if not st.session_state.input_upload_files and not st.session_state.input_text_content and not st.session_state.input_markdown_file:
        st.warning(
            "Please upload the inputs before generating the structured proof."
        )
    else:
        with st.spinner("Generating structured proof..."):
            try:
                #TODO:
                st.session_state.structured_proof = json.dumps({"theorem": st.session_state.theorem, "proof": st.session_state.proof})
                # st.session_state.structured_proof = gen_structure_proof(
                #     st.session_state.theorem, st.session_state.proof
                # )
            except Exception as e:
                st.warning(f"Failed to generate structured proof: {e}")

if st.session_state.structured_proof:
    st.subheader("Structured Proof Output (JSON):")
    st.write("TEMPORARY OUTPUT")
    try:
        structured_proof_json = json.loads(st.session_state.structured_proof)
        json_str = json.dumps(structured_proof_json, indent=2)
        st.json(json_str)
        col1, col2 = st.columns([1, 1])
        with col1:
            if st.button("Copy to Clipboard", key="copy_structured_proof"):
                copy_to_clipboard(json_str)
        with col2:
            download_file(json_str, "structured_proof.json")
    except Exception as e:
        st.warning(f"Failed to display structured proof: {e}")

# Schema Info
st.subheader("Schema Information", help = "Expand the JSON schema below to see the LeanAide PaperStructure.json schema followed by models.")
schema_path = os.path.join(str(HOMEDIR), "resources", "PaperStructure.json")
ln_schema_json = json.load(open(schema_path, "r"))
st.json(ln_schema_json, expanded=False)

if os.path.exists(temp_dir):
    for file in os.listdir(temp_dir):
        os.remove(os.path.join(temp_dir, file))
    os.rmdir(temp_dir)