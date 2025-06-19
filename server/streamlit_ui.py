import streamlit as st
from llm_response import get_supported_models, provider_info
from logging_utils import post_env_args
# Initialize session state variables
# Global variables for session state initialization

NONE_INIT_KEYS = [
    "self_selection", "val_input", "result", "temp_structured_json", "prompt_proof_guide",
    "image_paths", "proof", "theorem", "structured_proof", "paper", "paper_pdf", "format_index",
    "uploaded_pdf"
]

FALSE_INIT_KEYS = [
    "request_button", "self_input_button", "log_server_cleaned",
    "server_output_success", "valid_input", "log_cleaned", "input_paper",
    "generation_complete", "input_image_paper", "input_pdf_paper", "input_image_proof", 
    "input_image_theorem", "input_pdf_proof", "input_pdf_theorem", "gen_ai_proof",
]

LLM_INIT_KEYS = [
    "llm_provider", "llm_list", "llm_api_key", "model_text", "model_img", "temperature", "llm_url",
    "model_leanaide",
]

# Initialize session state variables
for key in (NONE_INIT_KEYS + LLM_INIT_KEYS):
    if key not in st.session_state:
        st.session_state[key] = None

for key in FALSE_INIT_KEYS:
    if key not in st.session_state:
        st.session_state[key] = False

if "selected_tasks" not in st.session_state:
    st.session_state.selected_tasks = []

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

for state in (NONE_INIT_KEYS + FALSE_INIT_KEYS + LLM_INIT_KEYS + ["selected_tasks"]):
    st.session_state[state] = st.session_state[state]

## Run 
pg.run()

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

        try:
            if not st.session_state.llm_list:
                st.session_state.llm_list = get_supported_models(provider=st.session_state.llm_provider)
        except Exception as e:
            st.error(f"Error fetching models for {st.session_state.llm_provider}: {e}")

        api_key_placeholder = (
            f"{selected_provider['api_key'][:15]}{'*' * (len(selected_provider['api_key']) - 15)}"
            if selected_provider["api_key"]
            else ""
        )

        st.session_state.llm_api_key = selected_provider["api_key"]
        received_api_key = st.text_input(
            "API Key:",
            value=api_key_placeholder,
            type="password",
            help="Hover to see the key, edit if needed.",
        )
        if received_api_key and received_api_key not in [st.session_state.get("llm_api_key", "Key Not Found"), api_key_placeholder]:
            st.session_state.llm_api_key = received_api_key
        

        st.info("The below options are models supported by your API Key.")
        # Model selection text boxes
        default_model_index = st.session_state.llm_list.index(selected_provider["default_model"]) if selected_provider["default_model"] in st.session_state.llm_list else 0

        model_list_help = f"Check out the list of {st.session_state.llm_provider} Models [↗]({selected_provider['models_url']})"

        st.session_state.model_leanaide = st.selectbox(
            "Model for LeanAide Code generation:",
            options = st.session_state.llm_list,
            index = (st.session_state.llm_list.index(selected_provider["default_leanaide_model"]) if selected_provider["default_leanaide_model"] in st.session_state.llm_list else 0),
            help="Specify the model for LeanAide Codegen. " + model_list_help,
            accept_new_options = True
        )
        st.session_state.model_text = st.selectbox(
            "Model for Proof/JSON Generator:",
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

    if st.button("Refresh Page", help="Refresh the page to set changes."):
        st.rerun()

    st.divider()
    st.warning("The Website is Under Development.")
    if st.checkbox("Show Session State", value=False, help = "Session State values, used for debugging."):
        st.sidebar.write("Session State:")
        # Create a copy of session state with masked API keys
        masked_state = {k: (v[:6] + "*" * (len(v) - 6) if "api_key" in k.lower() and isinstance(v, str) and len(v) > 6 else v) for k, v in st.session_state.items()}
        st.sidebar.json(masked_state)

    with st.expander("Other Settings", expanded=False):
        st.info("These are side default settings, you may safely ignore them. More settings on top-right 3-dot menu.")
        st.session_state.temperature = st.slider("Temperature:",
            min_value=0.0, max_value=1.0, value=0.8, step=0.1,
            help="Set the temperature for the model's responses. Default: 0.8",
        )
        st.session_state.llm_url = st.text_input(
            "URL to query (for a local server)",
            help="Specify the URL for the LLM API. Example: `https://api.mistral.ai/v1/chat/completions`"
        )

if st.session_state.llm_api_key and st.session_state.llm_provider:
    # Post environment arguments to the server
    env_kwargs = {}
    if st.session_state.model_leanaide:
        env_kwargs["model"] = st.session_state.model_leanaide
    if st.session_state.temperature is not None and not st.session_state.temperature == 0.8:
        env_kwargs["temperature"] = int(10*st.session_state.temperature)
    if st.session_state.llm_url:
        env_kwargs["url"] = st.session_state.llm_url
    try:
        post_env_args(
            provider = st.session_state.llm_provider,
            auth_key = st.session_state.llm_api_key,
            **env_kwargs,
        )
    except Exception as e:
        st.error(f"Error setting environment variables: {e}")


