import streamlit as st
import json
import os
from pathlib import Path
import shutil

from dotenv import load_dotenv
from PIL import Image
from streamlit_sortables import sort_items
# from gpt_structured import gen_structure_proof, solution_from_images
from serv_utils import copy_to_clipboard, download_file, HOMEDIR

load_dotenv()

st.title("LeanAide: Structured Json Output")
st.write("Here you can input your theorem-proof/paper, etc. and generate Structured JSON output using LeanAide Schema.")

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
TEMP_DIR = "leanaide_st_temp"
os.makedirs(TEMP_DIR, exist_ok=True)

# Create session state variables if they don't exist
for key in ["image_paths", "proof", "theorem", "structured_proof", "paper"]:
    if key not in st.session_state:
        st.session_state[key] = None

for key in ["input_upload_files", "input_text_content", "input_markdown_file", "input_paper", "input_pdf_file"]:
    if key not in st.session_state:
        st.session_state[key] = False

st.header("Input PDF/Images/Markdown of Paper/Theorem-Proof", divider = True)
# Get input method from user
input_options = ["Upload PDF Paper", "Input Theorem-Proof"] 
input_captions = ["For Research Papers", "For single Theorem-Proof or Problems"]
input_method = st.radio("Choose the input method:", options = input_options)

def action_copy_download(key: str, filename: str):
    """Helper function to copy text to clipboard and download as a file."""
    col1, col2 = st.columns(2)
    with col1:
        copy_to_clipboard(st.session_state[key])
    with col2:
        download_file(st.session_state[key], filename)

# Helper function for image inputs
def handle_image_input(key: str):
    """Handles image input and reordering for different sections."""
    # Create unique session state keys for this section
    st.info(f"Note: For the uploaded images, they are sent to LLM's for OCR and processed, so please ensure they are clear and readable. Also make sure to provide LLM Credentials for the same.")
    paths_key = f"{key}_image_paths"
    if paths_key not in st.session_state:
        st.session_state[paths_key] = []
    
    temp_dir = os.path.join(TEMP_DIR, key)
    os.makedirs(temp_dir, exist_ok=True)

    # File uploader with unique key
    uploaded_images = st.file_uploader(
        f"Upload images for {key}",
        type=["png", "jpg", "jpeg"],
        accept_multiple_files=True,
        key=f"file_uploader_{key}"  # Unique key for each uploader
    )

    if uploaded_images:
        st.success(f"Images uploaded successfully for {key}. You can reorder them below:") 
        # Process new uploads
        for uploaded_file in uploaded_images:
            img = Image.open(uploaded_file)
            temp_path = os.path.join(temp_dir, uploaded_file.name)
            img.save(temp_path)
            if temp_path not in st.session_state[paths_key]:
                st.session_state[paths_key].append(temp_path)

        # Display and reorder images
        if st.session_state[paths_key]:
            reordered_images = sort_items(
                items=[os.path.basename(path) for path in st.session_state[paths_key]],
                direction="vertical",
                key=f"sortable_{key}"  # Unique key for sortable list
            )
            
            # Update paths with new order
            st.session_state[paths_key] = [
                os.path.join(temp_dir, filename) for filename in reordered_images
            ]

            # Display image previews in columns
            cols = st.columns(min(3, len(st.session_state[paths_key])))
            for idx, img_path in enumerate(st.session_state[paths_key]):
                with cols[idx % len(cols)]:
                    st.image(img_path, use_column_width=True)

    # Generate text from images
    if st.session_state[paths_key] and st.button(f"Generate {key.capitalize()} text from Images", 
                                              key=f"generate_btn_{key}"):
        with st.spinner(f"Processing images..."):
            try:
                # Replace with your actual image processing function
                generated_text = f"Sample {key} text generated from {len(st.session_state[paths_key])} images."
                st.session_state[key] = generated_text
            except Exception as e:
                st.error(f"Failed to process images: {str(e)}")
                st.session_state[key] = ""

    # Display and manage generated text
    if st.session_state[key]:
        st.subheader(f"Generated {key.capitalize()}:", help = "Generated text from images or manual input. You may see some text previously if you have already filled the value in other sections.")
        st.session_state[key] = st.text_area(
            f"{key.capitalize()} Content",
            st.session_state[key],
            height=200,
            key=f"text_area_{key}"  # Unique key for text area
        )
        
        # Action buttons
        action_copy_download(key, f"{key}.txt")
        

# Helper function for markdown/text file input
def handle_md_file_input(key: str):
    """Handles markdown/text file input for different sections."""
    st.subheader(f"Upload Markdown/Text file for {key.capitalize()}")
 
    # file uploader with unique key
    uploaded_file = st.file_uploader(
        f"Upload {key} file",
        type=["md", "txt"],
        key=f"md_uploader_{key}"  # Unique key for each uploader
    )

    if uploaded_file:
        file_type = "Markdown" if uploaded_file.name.endswith(".md") else "Text"
        try:
            content = uploaded_file.read().decode("utf-8")
            st.session_state[key] = content
            st.success(f"{file_type} file for {key} uploaded successfully.")
        except UnicodeDecodeError:
            try:
                # Fallback to different encoding if utf-8 fails
                content = uploaded_file.read().decode("latin-1")
                st.session_state[key] = content
                st.success(f"{file_type} file for {key} uploaded (using fallback encoding).")
            except Exception as e:
                st.error(f"Failed to read the {file_type} file: {str(e)}")
                st.session_state[key] = ""
        except Exception as e:
            st.error(f"Failed to process {file_type} file: {str(e)}")
            st.session_state[key] = ""

    # Display content if available
    if st.session_state[key]:
        st.subheader(f"{key.capitalize()} Content:", help = "You can edit the content below if needed. You may see some text previously if you have already filled the value in other sections.")
        st.session_state[key] = st.text_area(
            f"Edit {key} content",
            st.session_state[key],
            height=200,
            key=f"md_content_{key}"  # Unique key for text area
        )
        
        # Action buttons
        ext = "md" if uploaded_file.name.endswith(".md") else "txt"
        action_copy_download(key, f"{key}.{ext}")
    else:
        st.warning(f"No {key} content available yet. Upload a file to begin.")

# Helper function for text input
def handle_text_input(key: str):
    st.session_state.input_text_content = True
    default_text = f"Enter the {key} text here..."
    obt_text = st.text_area(
        key.capitalize(),
        value = st.session_state[key] if st.session_state[key] else "",
        placeholder = default_text,
        height=200,
    )
    if obt_text.strip() != "" and obt_text.strip() != default_text:
        st.success(f"{key.capitalize()} received successfully.")
        action_copy_download(key, f"{key}.txt")
        return obt_text
    else:
        st.warning(f"Please enter {key.capitalize()} text before proceeding.")
        return ""

# Helper function for PDF input
def handle_pdf_input(key:str):
    uploaded_pdf = st.file_uploader(f"Upload a PDF file for the {key}", type="pdf", key = f"pdf_uploader_{key}")
    if uploaded_pdf:
        try:
            # Create temp directory if it doesn't exist
            os.makedirs(TEMP_DIR, exist_ok=True)
            
            # Save PDF to temporary file
            pdf_path = os.path.join(TEMP_DIR, f"{key}_{uploaded_pdf.name}")
            with open(pdf_path, "wb") as f:
                f.write(uploaded_pdf.getvalue())
            
            # Store both path and content in session state
            st.session_state[f"{key}_pdf_path"] = pdf_path
            st.session_state[key] = uploaded_pdf.getvalue()
            
            st.success(f"PDF for {key} uploaded successfully.")
            
            # Display PDF info
            st.info(f"File: {uploaded_pdf.name} | Size: {len(uploaded_pdf.getvalue())//1024} KB")
            
        except Exception as e:
            st.error(f"Failed to process PDF for {key}: {str(e)}")
            st.session_state[key] = None
            st.session_state[f"{key}_pdf_path"] = None
    
    if st.session_state[key]:
        st.subheader(f"{key.capitalize()} PDF Content:", help = "You can edit the content below if needed. You may see some text previously if you have already filled the value in other sections.")
        # Display the PDF content (if any)
        try:
            pdf_content = st.text_area(
                f"Edit {key} PDF content",
                value = st.session_state[key].decode("utf-8") if isinstance(st.session_state[key], bytes) else st.session_state[key],
                height=200,
                key=f"pdf_content_{key}"  # Unique key for text area
            )
        except Exception as e:
            st.warning(f"Failed to display PDF content: {str(e)}. **Don't worry,** This can still be passed to LLMs for processing.")
        
        # Action buttons
        action_copy_download(key, f"{uploaded_pdf.name}") # has the extension .pdf

# PDF upload section
if input_method == input_options[0]:
    st.session_state.input_paper = True
    st.subheader("Upload Paper PDF")
    handle_pdf_input("paper")
# Theorem-Proof section
if input_method == input_options[1]:
    st.session_state.input_upload_files = True
    # Upload Theorem
    st.subheader("Input Theorem")
    standard_options = ["Upload Images", "Upload Markdown/Text File", "Input Text", "Upload PDF"]
    thm_opt = st.radio("Choose input method for theorem:", options = standard_options, horizontal = True)
    if "image" in thm_opt.lower():
        st.session_state.input_upload_files = True
        handle_image_input("theorem") 
    elif "markdown" in thm_opt.lower():
        st.session_state.input_markdown_file = True
        handle_md_file_input("theorem")
    elif "pdf" in thm_opt.lower():
        st.session_state.input_pdf_file = True
        handle_pdf_input("theorem")
    else:
        st.session_state.input_text_content = True
        st.session_state.theorem = handle_text_input("theorem")

    # Upload Proof
    st.subheader("Input Proof")
    proof_opt = st.radio("Choose input method for proof:", options = standard_options, horizontal = True)
    if "image" in proof_opt.lower():
        st.session_state.input_upload_files = True
        handle_image_input("proof")
    elif "markdown" in proof_opt.lower():
        st.session_state.input_markdown_file = True
        handle_md_file_input("proof")
    elif "pdf" in proof_opt.lower():
        st.session_state.input_pdf_file = True
        handle_pdf_input("proof")
    else:
        st.session_state.input_text_content = True
        st.session_state.proof = handle_text_input("proof")

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
        action_copy_download("structured_proof", "structured_proof.json")
    except Exception as e:
        st.warning(f"Failed to display structured proof: {e}")

st.divider()

# Schema Info
st.subheader("Schema Information", help = "Expand the JSON schema below to see the LeanAide `PaperStructure.json` schema followed by models.")
schema_path = os.path.join(str(HOMEDIR), "resources", "PaperStructure.json")
ln_schema_json = json.load(open(schema_path, "r"))
st.json(ln_schema_json, expanded=False)

if st.session_state.structured_proof:
    if os.path.exists(TEMP_DIR):
        shutil.rmtree(TEMP_DIR)