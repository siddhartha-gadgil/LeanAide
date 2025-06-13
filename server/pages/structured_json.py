import streamlit as st
import json
import os
import shutil

from dotenv import load_dotenv
from PIL import Image
from streamlit_sortables import sort_items
# from gpt_structured import gen_structure_proof, solution_from_images
from serv_utils import action_copy_download, preview_text, SCHEMA_JSON
from llm_response import *

load_dotenv()

st.title("LeanAide: Structured Json Output")
st.write("Here you can input your theorem-proof/paper, etc. and generate Structured JSON output using LeanAide Schema.")
st.info("Please fill out your API credentials in the sidebar to use the LLM's. Image OCR, Structured Json Generation, etc. will not work without valid API credentials.")

st.sidebar.header("Structured Json")

# Create a temporary directory if it doesn't exist
TEMP_DIR = "leanaide_st_temp"
os.makedirs(TEMP_DIR, exist_ok=True)

# Create session state variables if they don't exist
for key in ["image_paths", "proof", "theorem", "structured_proof", "paper", "model_text", "model_img" , "llm_provider", "llm_list"]:
    if key not in st.session_state:
        st.session_state[key] = None

for key in ["input_pdf", "input_images", "input_markdown", "input_txt", "input_latex", "input_text_content", "input_paper"]:
    if key not in st.session_state:
        st.session_state[key] = False

# For buttons only
for key in ["gen_json_button"]:
    if key not in st.session_state:
        st.session_state[key] = False

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
with st.sidebar:
    with st.expander("Credentials"):
        # Provider selection
        st.session_state.llm_provider = st.selectbox("Select Provider:", list(provider_info.keys()), index=0)

        # Dynamically update API Key and Model fields based on the provider
        selected_provider = provider_info[st.session_state.llm_provider]

        if not st.session_state.llm_list:
            if st.session_state.llm_provider.lower() == "openai":
                st.session_state.llm_list = get_openai_models()

        if st.session_state.llm_provider == "Gemini":
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

            if st.session_state.llm_provider.lower() == "openai":
                st.info("The below options are models supported by your OpenAI API Key.")
            # Model selection text boxes
            default_openai_model_index = st.session_state.llm_list.index(selected_provider["default_model"]) if selected_provider["default_model"] in st.session_state.llm_list else 0
            model_image_to_text = st.selectbox(
                "Model for Image to Text:",
                options = st.session_state.llm_list,
                index = default_openai_model_index,
                help="Specify the model for Image to Text. Check out list of OpenAI Models [↗](https://platform.openai.com/docs/models)",
                accept_new_options = True
            )
            model_json_generator = st.selectbox(
                "Model for JSON Generator:",
                options = get_openai_models(),
                index = default_openai_model_index,
                help="Specify the model for JSON Generator. Check out list of OpenAI Models [↗](https://platform.openai.com/docs/models)",
                accept_new_options = True
            )

st.header("Input your Paper/Theorem-Proof", divider = True)
# Get input method from user
input_options = ["Mathematical Papers", "Theorem-Proofs or Problems"] 
input_captions = ["For Research Papers", "For short Theorem Proofs or Mathematical Problems"]
input_method = st.radio("Choose what you would like to work on:",
    options = input_options,
    captions = input_captions,
    horizontal = True,
    help = "Select what you are inputting. If you are working on a single theorem-proof or problem, select the second option. If you are working on a research paper, select the first option."
)

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
                st.session_state[key] = solution_from_images(st.session_state[paths_key])
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
        preview_text(key) 
        # Action buttons
        action_copy_download(key, f"{key}.txt")
        
# Helper function for markdown/text file input
def handle_textual_file_input(key: str):
    """Handles markdown/text file input for different sections."""
    st.subheader(f"Upload Markdown/Text file for {key.capitalize()}")
    # file uploader with unique key
    uploaded_file = st.file_uploader(
        f"Upload {key} file",
        type=["md", "txt", "tex"],
        key=f"md_uploader_{key}"  # Unique key for each uploader
    )
    extension = uploaded_file.name.split('.')[-1] if uploaded_file else "md"
    if extension not in ["md", "txt", "tex"]:
        st.error(f"Unsupported file type: {extension}. Please upload a .md, .txt, or .tex file.")
        return

    if f"{key}_{extension}_local_key" not in st.session_state:
        st.session_state[f"{key}_{extension}_local_key"] = False

    file_type = "Markdown"
    if extension == "tex":
        file_type = "LaTeX"
    elif extension == "txt":
        file_type = "Text"
    else:
        pass

    if uploaded_file:
        try:
            content = uploaded_file.read().decode("utf-8")
            st.success(f"{file_type} file for {key} uploaded successfully.")
            st.session_state[key] = content
            st.session_state[f"{key}_{extension}_local_key"] = True
        except UnicodeDecodeError:
            try:
                # Fallback to different encoding if utf-8 fails
                content = uploaded_file.read().decode("latin-1")
                st.success(f"{file_type} file for {key} uploaded (using fallback encoding).")
                st.session_state[key] = content
                st.session_state[f"{key}_{extension}_local_key"] = True
            except Exception as e:
                st.error(f"Failed to read the {file_type} file: {str(e)}")
                st.session_state[key] = ""
        except Exception as e:
            st.error(f"Failed to process {file_type} file: {str(e)}")
            st.session_state[key] = ""

    # Display content if available
    if st.session_state[key] and st.session_state[f"{key}_{extension}_local_key"]:
        st.subheader(f"{key.capitalize()} Content:", help = "You can edit the content below if needed. You may see some text previously if you have already filled the value in other sections.")
        st.session_state[key] = st.text_area(
            f"Edit {key} content",
            st.session_state[key],
            height=200,
            key=f"md_content_{key}"  # Unique key for text area
        )
        preview_text(key, f"Enter the {key} text here...")
        
        # Action buttons
        ext = "md" if uploaded_file.name.endswith(".md") else "txt"
        action_copy_download(key, f"{key}.{ext}")
    else:
        st.warning(f"No {key} content available yet. Upload a file to begin.")

# Helper function for text input
def handle_text_input(key: str):
    st.session_state.input_text_content = True
    default_text = f"Enter the {key.capitalize()} text here..."
    obt_text = st.text_area(
        key.capitalize(),
        value = st.session_state[key] if st.session_state[key] else "",
        placeholder = default_text,
        height=200,
        help = "You can type your " + key + " text here. You can even write `LaTeX` code if you want to.",
        key=f"text_input_{key}" 
    ).strip()
    if obt_text != "" and obt_text != default_text:
        _code_suffix = "..." if len(obt_text) > 50 else ""
        st.session_state[key] = obt_text
        # After components
        preview_text(key, default_text)
        st.success(f"{key.capitalize()} received successfully: {obt_text[:50]}" + _code_suffix)
        action_copy_download(key, f"{key}.txt")
    else:
        st.warning(f"Please enter {key.capitalize()} text before proceeding.")
        st.session_state[key] = ""

# Helper function for PDF input
def handle_pdf_input(key:str):
    uploaded_pdf = st.file_uploader(f"Upload a PDF file for the {key}", type="pdf", key = f"pdf_uploader_{key}")
    if f"{key}_local_key" not in st.session_state:
        st.session_state[f"{key}_local_key"] = False
    if uploaded_pdf:
        try:
            # Create temp directory if it doesn't exist
            os.makedirs(TEMP_DIR, exist_ok=True)
            
            # Save PDF to temporary file
            pdf_path = os.path.join(TEMP_DIR, f"{key}_{uploaded_pdf.name}")
            pdf_text = extract_text_from_pdf(uploaded_pdf)
            
            # Store both path and content in session state
            st.session_state[f"{key}_pdf_path"] = pdf_path
            st.session_state[key] = pdf_text 
            st.success(f"PDF for {key} uploaded successfully.")
            
            # Display PDF info
            st.info(f"File: {uploaded_pdf.name} | Size: {len(uploaded_pdf.getvalue())//1024} KB")
            st.session_state[f"{key}_local_key"] = True
            
        except Exception as e:
            st.error(f"Failed to process PDF for {key}: {str(e)}")
            st.session_state[key] = None
            st.session_state[f"{key}_pdf_path"] = None
    
    if st.session_state[key] and st.session_state[f"{key}_local_key"]:
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

# General input handler for theorem, proof, and paper
def handle_general_input(key: str):
    st.subheader(f"Input "+ key.capitalize())
    input_formats = ["Type Input Yourself", "PDF(.pdf)", "Image(.png, .jpg, .jpeg)", "Markdown(.md)", "Text(.txt)" , "Latex(.tex)"]

    format_opt = st.selectbox(
        "Choose input format for the theorem",
        options = input_formats,
        help = f"Select the format in which you want to input the {key}. You may instead type the {key} text directly.",
        placeholder = "Choose input format",
        key = f"input_format_{key}",
        index = 1 if key == "paper" else 0  # Default to PDF for paper, else default to first option
    )
    if "image" in format_opt.lower():
        st.session_state.input_image = True
        handle_image_input(key) 
    elif "markdown" in format_opt.lower():
        st.session_state.input_markdown_file = True
        handle_textual_file_input(key)
    elif "text" in format_opt.lower():
        st.session_state.input_txt = True
        handle_textual_file_input(key)
    elif "latex" in format_opt.lower():
        st.session_state.input_latex = True
        handle_textual_file_input(key)
    elif "pdf" in format_opt.lower():
        st.session_state.input_pdf_file = True
        handle_pdf_input(key)
    else: # Self typed input
        st.session_state.input_text_content = True
        handle_text_input(key) 

# PDF upload section
if input_method == input_options[0]: # Papers
    st.session_state.input_paper = True
    st.info("It is recommended to upload the paper in PDF format for better processing. Though you can choose any other formats as well.")
    handle_general_input("paper")

# Theorem-Proof section
if input_method == input_options[1]: # Theorem-Proofs or Problems
    st.session_state.input_paper = False
    for key in ["theorem", "proof"]:
        handle_general_input(key) 

if st.button("Generate Structured Proof") or st.session_state["gen_json_button"]:
    st.session_state.gen_json_button = True
    if not st.session_state.paper and not (st.session_state.proof and  st.session_state.theorem):
        st.warning(
            "Please upload the inputs before generating the structured proof."
        )
    else:
        with st.spinner("Generating structured proof..."):
            try:
                if st.session_state.input_paper: # For mathematical papers
                    st.session_state.structured_proof = gen_paper_json(st.session_state.paper)
                else: # Theorem Proof based
                    st.session_state.structured_proof = gen_thmpf_json(st.session_state.theorem, st.session_state.proof)
            except Exception as e:
                st.warning(f"Failed to generate structured proof: {e}")
else:
    st.session_state.gen_json_button = False

if st.session_state.structured_proof:
    st.subheader("Structured Proof Output (JSON):")
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
st.json(SCHEMA_JSON, expanded=False)

if st.session_state.structured_proof:
    if os.path.exists(TEMP_DIR):
        shutil.rmtree(TEMP_DIR)