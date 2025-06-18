import os
import streamlit as st
from llm_response import get_supported_models
# Initialize session state variables
# Global variables for session state initialization
NONE_INIT_KEYS = [
    "self_selection", "val_input", "result", "temp_structured_json", "prompt_proof_guide",
    "image_paths", "proof", "theorem", "structured_proof", "paper", "paper_pdf", "format_index",
    "model_text", "model_img", "llm_provider", "llm_list", "uploaded_pdf", "llm_api_key"
]

FALSE_INIT_KEYS = [
    "request_button", "self_input_button", "log_server_cleaned",
    "server_output_success", "valid_input", "log_cleaned", "input_paper",
    "generation_complete", "input_image_paper", "input_pdf_paper", "input_image_proof", 
    "input_image_theorem", "input_pdf_proof", "input_pdf_theorem", "gen_ai_proof",
]

# Initialize session state variables
for key in NONE_INIT_KEYS:
    if key not in st.session_state:
        st.session_state[key] = None

for key in FALSE_INIT_KEYS:
    if key not in st.session_state:
        st.session_state[key] = False

if "selected_tasks" not in st.session_state:
    st.session_state.selected_tasks = []

provider_info = {
    "OpenAI": {
        "name": "OpenAI",
        "default_model": "o4-mini",
        "default_api_key": os.getenv("OPENAI_API_KEY", "Key Not Found"),
    },
    "Gemini": {
        "name": "Gemini",
        "default_model": "gemini-1.5-pro",
        "default_api_key": os.getenv("GEMINI_API_KEY", "Key Not Found"),
    },
    "OpenRouter": {
        "name": "OpenRouter",
        "default_model": "gpt-4o",
        "default_api_key": os.getenv("OPENROUTER_API_KEY", "Key Not Found"),
    },
    "DeepInfra": {
        "name": "DeepInfra",
        "default_model": "deepseek-ai/DeepSeek-R1-0528",
        "default_api_key": os.getenv("DEEPINFRA_API_KEY", "Key Not Found"),
    }
}
# API Credentials Section
with st.sidebar:
    st.header("LLM Credentials", divider = "orange")
    with st.expander("Check API Credentials"):
        # Provider selection
        llm_provider = st.selectbox("Select Provider:", list(provider_info.keys()), index=0)
        if llm_provider != st.session_state.get("llm_provider", ""):
            st.session_state.llm_provider = llm_provider
            st.session_state.llm_list = []

        # Dynamically update API Key and Model fields based on the provider
        selected_provider = provider_info[st.session_state.llm_provider]

        if not st.session_state.llm_list:
            st.session_state.llm_list = get_supported_models(provider=st.session_state.llm_provider)

        api_key_placeholder = (
            f"{selected_provider['default_api_key'][:15]}{'*' * (len(selected_provider['default_api_key']) - 15)}"
            if selected_provider["default_api_key"]
            else ""
        )
        st.session_state.llm_api_key = st.text_input(
            "API Key:",
            value=api_key_placeholder,
            type="password",
            help="Hover to see the key, edit if needed.",
        )

        st.info("The below options are models supported by your API Key.")
        # Model selection text boxes
        default_model_index = st.session_state.llm_list.index(selected_provider["default_model"]) if selected_provider["default_model"] in st.session_state.llm_list else 0

        model_list_help = f"Check out the list of {st.session_state.llm_provider} Models [↗](https://platform.openai.com/docs/models)" if st.session_state.llm_provider.lower() == "openai" else f"Check out the list of {st.session_state.llm_provider} Models [↗](https://ai.google.dev/gemini-api/docs/models)"
        st.session_state.model_text = st.selectbox(
            "Model for JSON Generator:",
            options = st.session_state.llm_list,
            index = default_model_index,
            help="Specify the model for JSON Generator. " + model_list_help,
            accept_new_options = True
        )
        st.session_state.model_img = st.selectbox(
            "Model for Image to Text:",
            options = st.session_state.llm_list,
            index = default_model_index,
            help="Specify the model for Image to Text. " + model_list_help,
            accept_new_options = True
        )
    

# Page Setup
intro_page = st.Page(
    page = "tabs/home.py",
    title = "Home",
    icon = ":material/home:",
    default = True,
)

server_response_page = st.Page(
    page = "tabs/server_response.py",
    title = "Server Response",
    icon = ":material/rocket_launch:",
)
structured_json_page = st.Page(
    page = "tabs/structured_json.py",
    title = "Structured Json",
    icon = ":material/code:"
)
logs_page = st.Page(
    page = "tabs/logs_display.py",
    title = "Logs",
    icon = ":material/bug_report:",
)
## Navigation
pg = st.navigation(pages = [
    intro_page,
    server_response_page,
    structured_json_page,
    logs_page
])

for state in (NONE_INIT_KEYS + FALSE_INIT_KEYS + ["selected_tasks"]):
    st.session_state[state] = st.session_state[state]

## Run 
pg.run()

with st.sidebar:
    st.warning("The Website is Under Development.")
    if st.checkbox("Show Session State", value=False, help = "Session State values, used for debugging."):
        st.sidebar.write("Session State:")
        st.sidebar.json(st.session_state)

