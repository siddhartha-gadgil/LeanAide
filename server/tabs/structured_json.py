import json
import os
import shutil

import streamlit as st
from dotenv import load_dotenv
from PIL import Image
from streamlit_sortables import sort_items

from llm_prompts import proof_thm_task_lean
from llm_response import gen_paper_json, gen_thmpf_json, solution_from_images, get_pdf_id, extract_text_from_pdf, model_response_gen
from serv_utils import SCHEMA_JSON, HOMEDIR, action_copy_download, preview_text, log_section
from logging_utils import log_write, post_env_args

load_dotenv(os.path.join(HOMEDIR, ".env"))

st.title("LeanAide: Structured JSON Output")
st.write("Here you can input your theorem-proof/paper, etc. and generate Structured JSON output using LeanAide Schema.")
st.info("Please fill out your API credentials in the sidebar to use the LLM's. Image OCR, Structured Json Generation, etc. will not work without valid API credentials.")

# Create a temporary directory if it doesn't exist
TEMP_DIR = "leanaide_st_temp"
os.makedirs(TEMP_DIR, exist_ok=True)

# Write to env API KEY
if st.session_state.llm_api_key:
    post_env_args(provider = st.session_state.llm_provider, auth_key = st.session_state.llm_api_key)
 
st.header("Input your Paper/Theorem-Proof", divider = True)
# Get input method from user
input_options = ["Theorem-Proofs or Problems", "Mathematical Papers"] 
input_captions = ["For short Theorem Proofs or Mathematical Problems", "For Research Papers"]
input_index = 1 if st.session_state.input_paper else 0
input_method = st.radio("Choose what you would like to work on:",
    options = input_options,
    captions = input_captions,
    horizontal = True,
    index = input_index,
    help = "Select what you are inputting. If you are working on a single theorem-proof or problem, select the second option. If you are working on a research paper, select the first option."
)

# Helper function for image inputs
def handle_image_input(key: str):
    """Handles image input and reordering for different sections."""
    # Create unique session state keys for this section
    st.info("Note: For the uploaded images, they are sent to LLM's for OCR and processed, so please ensure they are clear and readable. Also make sure to provide LLM Credentials for the same.")
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
                    st.image(img_path, use_container_width=True)

    # Generate text from images
    if st.session_state[paths_key] and st.button(f"Generate {key.capitalize()} text from Images", 
                                              key=f"generate_btn_{key}"):
        with st.spinner("Processing images..."):
            try:
                st.session_state[key] = solution_from_images(st.session_state[paths_key], provider=st.session_state.llm_provider, model = st.session_state.model_img)
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
        st.info(f"Since the text is LLM Generated, you may see unnecessary text or some errors. Since the above test will be used as **{key.capitalize()}**, it is Recommended to edit the text before proceeding.")
        preview_text(key, usage = "imggen") 
        # Action buttons
        action_copy_download(key, f"{key}.txt", usage = "imggen")
        
# Helper function for markdown/text file input
def handle_textual_file_input(key: str, extension: str = "md"):
    """Handles markdown/text file input for different sections."""
    file_type = "Markdown"
    if extension == "tex":
        file_type = "LaTeX"
    elif extension == "txt":
        file_type = "Text"
    else:
        pass

    st.subheader(f"Upload {file_type} file for {key.capitalize()}")
    # file uploader with unique key
    uploaded_file = st.file_uploader(
        f"Upload {key} file",
        type=f".{extension}",
        key=f"md_uploader_{key}"  # Unique key for each uploader
    )
    if extension not in ["md", "txt", "tex"]:
        st.error(f"Unsupported file type: {extension}. Please upload a .md, .txt, or .tex file.")
        return

    if f"{key}_{extension}_local_key" not in st.session_state:
        st.session_state[f"{key}_{extension}_local_key"] = False

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
        preview_text(key, f"Enter the {key} text here...", usage = "filegen")
        
        # Action buttons
        action_copy_download(key, f"{key}.{extension}", usage = "filegen")
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
        preview_text(key, default_text, usage = "textgen")
        st.success(f"{key.capitalize()} received successfully: {obt_text[:50]}" + _code_suffix)
        action_copy_download(key, f"{key}.txt", usage = "textgen")
    else:
        st.warning(f"Please enter {key.capitalize()} text before proceeding.")
        st.session_state[key] = ""

# Helper function for PDF input
def handle_pdf_input(key:str):
    new_uploaded_pdf = st.file_uploader(f"Upload a PDF file for the {key}", type="pdf", key = f"pdf_uploader_{key}")
    if new_uploaded_pdf:
        st.session_state.uploaded_pdf = new_uploaded_pdf
    if f"{key}_local_key" not in st.session_state:
        st.session_state[f"{key}_local_key"] = ""

    if st.session_state.uploaded_pdf:
        try: 
            # Save PDF to temporary file
            if new_uploaded_pdf:
                st.session_state[f"{key}_pdf_path"] = os.path.join(TEMP_DIR, f"{st.session_state.uploaded_pdf.name}")
                shutil.copyfileobj(st.session_state.uploaded_pdf, open(st.session_state[f"{key}_pdf_path"], "wb"))
            # The value of st.session_state[key] will change if pdf paper is uploaded
            st.session_state[f"{key}_local_key"] = extract_text_from_pdf(st.session_state[f"{key}_pdf_path"])
            
            st.session_state[key] = st.session_state[f"{key}_local_key"]
            # if paper is pdf, then store in "paper_pdf" key
            if st.session_state.input_paper and st.session_state["input_pdf_paper"]:
                st.session_state["paper_pdf"] = get_pdf_id(st.session_state[f"{key}_pdf_path"], provider =st.session_state.llm_provider)

            st.success(f"PDF for {key} uploaded successfully.") 
            # Display PDF info
            st.info(f"File: {st.session_state.uploaded_pdf.name} | Size: {len(st.session_state.uploaded_pdf.getvalue())//1024} KB")
            
        except Exception as e:
            st.error(f"Failed to process PDF for {key}: {str(e)}")
            st.session_state[key] = None
            st.session_state[f"{key}_pdf_path"] = None

    if st.session_state[key] and st.session_state[f"{key}_local_key"]:
        # Paper PDF input only
        if st.session_state.input_paper and st.session_state["input_pdf_paper"]:
            st.info("Note: The PDF preview content may not be great, but don't worry, LLM's are given encoded version so they can process it better.")
            st.code(
                st.session_state["paper_local_key"],
                height=200,
            )
        else:
            st.subheader(f"{key.capitalize()} PDF Content:", help = "You can edit the content below if needed. You may see some text previously if you have already filled the value in other sections.")
            # Display the PDF content (if any)
            try:
                st.session_state[key] = st.text_area(
                    f"Edit {key} PDF content",
                    value = st.session_state[key].decode("utf-8") if isinstance(st.session_state[key], bytes) else st.session_state[key],
                    height=200,
                    key=f"pdf_content_{key}"  # Unique key for text area
                )
            except Exception as e:
                st.warning(f"Failed to display PDF content: {str(e)}. **Don't worry,** This can still be passed to LLMs for processing.")
        
        # Action buttons
        action_copy_download(key, f"{st.session_state.uploaded_pdf.name}", st.session_state[f"{key}_local_key"], usage="pdfgen") # has the extension .pdf

# Helper function for AI proof output
def handle_ai_proof_input(key: str, rewrite: bool = False):
    """Handles AI proof generation from theorem input."""
    if rewrite:
        st.subheader("Rewrite Proof using AI")
        if not st.session_state.proof.strip():
            st.warning("Proof has not been inputted yet. Please input the proof first.")
            return

        prompt_guide_thm = st.session_state.prompt_proof_guide
    else:
        st.subheader("Generate AI Proof from Theorem")

        if "theorem" not in st.session_state or not st.session_state.theorem:
            st.warning("Please enter a theorem before generating the proof.")
            return

        # Theorem is given in the prompt HERE.
        prompt_guide_thm = st.session_state.prompt_proof_guide+ "\n\nThe Theorem you have to prove is:\n" + st.session_state.theorem

    with st.expander("Preview: AI Prompt for Generating Proof", expanded = False):
        if st.checkbox("Edit Prompt", value = False):
            st.session_state.prompt_proof_guide = st.text_area(
                "AI Proof Generation Prompt",
                value=prompt_guide_thm,
                height=250,
                help="You can edit the prompt for AI proof generation. It should be more declarative and structured so that it can be converted to Lean code.",
            )
        else:
            st.markdown(prompt_guide_thm, unsafe_allow_html=True)

    gen_ai_proof_button = st.button("Generate AI Proof")
    if gen_ai_proof_button:
        with st.spinner("Generating AI proof. Please wait for a short while..."):
            try:
                st.session_state.proof = model_response_gen(
                    prompt=prompt_guide_thm,
                    task = proof_thm_task_lean() if not rewrite else proof_thm_task_lean(st.session_state.proof, rewrite=True),
                    provider=st.session_state.llm_provider,
                    model=st.session_state.model_text,
                )
                log_write("AI Proof Generation", "Success: Generated AI proof for theorem")
            except Exception as e:
                st.error(f"Failed to generate AI proof: {str(e)}")
                st.session_state.proof = ""
                log_write("AI Proof Generation", f"Error: Failed to generate AI proof: {e}")
                return

    if st.session_state.proof or gen_ai_proof_button:
        st.session_state.proof = st.text_area(
            "AI Generated Proof",
            value=st.session_state.proof,
            height=200,
            help="This is the AI generated proof for the theorem. You can edit it if needed.",
            key=f"ai_proof_text_area_{key}"  # Unique key for text area
        )
        preview_text(key, "No Proof text available yet. Please generate or input the proof text.", usage = f"aigen_{rewrite}")
        st.success(f"{key.capitalize()} received successfully")
        action_copy_download(key, f"{key}.txt", usage = f"aigen_{rewrite}")
    else:
        st.warning(f"No {key} content available yet. Please generate or input the proof text.")
        st.session_state[key] = ""
    
# General input handler for theorem, proof, and paper
def handle_general_input(key: str):
    st.subheader("Input "+ key.capitalize())
    selectbox_text = f"Choose input format for the {key}"
    input_formats = ["Type Input Yourself", "PDF(.pdf)", "Image(.png, .jpg, .jpeg)", "Markdown(.md)", "Text(.txt)" , "Latex(.tex)"]
    if key.lower() == "proof":
        st.info("Input the Proof of your input Theorem, or Generate it using AI below. You may skip this section in the latter case.")

    if not st.session_state.format_index or not st.session_state.input_paper:
        st.session_state.format_index = 1 if key == "paper" else 0

    format_opt = st.selectbox(
        selectbox_text,
        options = input_formats,
        help = f"Select the format in which you want to input the {key}. You may instead type the {key} text directly.",
        placeholder = "Choose input format",
        key = f"input_format_{key}",
        index = st.session_state.format_index  # Default to PDF for paper, else default to first option
    )
    if "image" in format_opt.lower():
        st.session_state[f"input_image_{key}"] = True
        st.session_state.format_index = input_formats.index(format_opt)
        handle_image_input(key) 
    elif "pdf" in format_opt.lower():
        st.session_state.format_index = input_formats.index(format_opt)
        st.session_state[f"input_pdf_{key}"] = True
        handle_pdf_input(key)
    else:
        for _elem in ["theorem", "proof", "paper"]:
            st.session_state[f"input_pdf_{_elem}"] = False
            st.session_state[f"input_image_{_elem}"] = False
        if "markdown" in format_opt.lower():
            st.session_state.format_index = input_formats.index(format_opt)
            handle_textual_file_input(key, extension="md")
        elif "text" in format_opt.lower():
            st.session_state.format_index = input_formats.index(format_opt)
            handle_textual_file_input(key, extension="txt")
        elif "latex" in format_opt.lower():
            st.session_state.format_index = input_formats.index(format_opt)
            handle_textual_file_input(key, extension="tex")
        else: # Self typed input
            st.session_state.format_index = input_formats.index(format_opt)
            handle_text_input(key) 

    if st.session_state[key] and st.session_state[key].strip():
        log_write("Structured JSON Input", f"Input {key} format: {format_opt}")

# Guide prompt for AI
prompt_proof_guide_path = os.path.join(HOMEDIR, "resources", "ProofGuidelines.md")
if not st.session_state.prompt_proof_guide:
    try:
        with open(prompt_proof_guide_path, "r") as file:
            st.session_state.prompt_proof_guide = file.read()
    except FileNotFoundError:
        st.session_state.prompt_proof_guide = "Write a proof for the theorem provided. It should be more declarative and structured so that it can be converted to Lean code."


# Papers section
if input_method == input_options[1]: # Papers
    st.session_state.input_paper = True
    st.info("It is recommended to upload the paper in PDF format for better processing. Though you can choose any other formats as well.")
    handle_general_input("paper")

# Theorem-Proof section
if input_method == input_options[0]: # Theorem-Proofs or Problems
    st.session_state.input_paper = False
    for key in ["theorem", "proof"]:
        handle_general_input(key) 

st.info("**Recommended:** For your input proof, it is advised to rewrite the proof based on our Guidelines for easier conversion to Lean Code. You can also generate the proof using AI based on the theorem you provided(if proof not provided previously).")

if st.button("Generate/Rewrite Proof using AI", type = "primary") or st.session_state.gen_ai_proof:
    st.session_state.gen_ai_proof = True
    if not st.session_state.proof.strip():
        st.success("You have not inputted any proof previously. Let's Generate the Proof!")
        handle_ai_proof_input("proof")
    else:
        st.success("You have inputted a proof previously. Let's Rewrite the Proof!")
        handle_ai_proof_input("proof", rewrite=True)

st.header("Generate Structured JSON Proof", divider = True)
if st.button("Generate Structured Proof", type = "primary"):
    if not st.session_state.paper and not (st.session_state.proof and  st.session_state.theorem):
        st.warning(
            "Please upload the inputs before generating the structured proof."
        )
    else:
        with st.spinner("Generating structured proof..."):
            try:
                if st.session_state.input_paper: # For mathematical papers
                    if not st.session_state.input_pdf_paper:
                        st.session_state.structured_proof = gen_paper_json(st.session_state.paper, pdf_input = st.session_state.input_pdf_paper, provider= st.session_state.llm_provider, model = st.session_state.model_text)
                    else:
                        st.session_state.structured_proof = gen_paper_json(st.session_state.paper_pdf, pdf_input = st.session_state.input_pdf_paper, provider=st.session_state.llm_provider, model = st.session_state.model_text)
                else: # Theorem Proof based
                    # if st.session_state.input_pdf
                    st.session_state.structured_proof = gen_thmpf_json(st.session_state.theorem, st.session_state.proof, provider=st.session_state.llm_provider, model = st.session_state.model_text)
                st.session_state.generation_complete = True
                log_write("Structured JSON Generation", "Structured proof generated successfully.")

            except Exception as e:
                st.warning(f"Failed to generate structured proof: {e}.\nMaybe try another model.")
                st.session_state.generation_complete = False
                log_write("Structured JSON Generation", f"Error: Failed to generate structured proof: {e}")
                log_write("Structured JSON Generation", f"Obtained Structured Proof: {st.session_state.structured_proof}")

def show_str_proof():
    try:
        structured_proof_json = json.loads(st.session_state.structured_proof)
        json_str = json.dumps(structured_proof_json, indent=2)
        st.json(json_str)
        action_copy_download("structured_proof", "structured_proof.json", usage = "strproof")
        log_write("Show Structured Proof", "Structured proof displayed successfully.")
    except Exception as e:
        st.warning(f"Failed to display structured proof: {e}")
        log_write("Show Structured Proof", f"Error: {e}")

if not st.session_state.structured_proof and st.session_state.generation_complete:
    st.subheader("Structured Proof Output (JSON):", help = "The structured proof will be displayed after generation. If you see no output or errors, please try again or try a different model.")
    if st.session_state.get("generation_complete", False) and st.session_state.structured_proof:
        show_str_proof()
    else:
        st.warning("Please generate the structured proof first by clicking the button above.")
elif st.session_state.generation_complete:
    st.subheader("Structured Proof Output (JSON):", help = "The structured proof will be displayed after generation. If you see no output or errors, please try again or try a different model.")
    show_str_proof() 

st.divider()

# Schema Info
st.subheader("Schema Information", help = "Expand the JSON schema below to see the LeanAide `PaperStructure.json` schema followed by models.")
st.json(SCHEMA_JSON, expanded=False)

log_section()

if st.session_state.structured_proof:
    if os.path.exists(TEMP_DIR):
        shutil.rmtree(TEMP_DIR)