import os
import subprocess

import streamlit as st
from streamlit import session_state as sts

from api_server import HOST, PORT
from llm_response import get_supported_models, provider_info
from logging_utils import post_env_args


def get_git_commit_info():
    """Get current git commit information"""
    try:
        sha = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=os.getcwd()).decode('utf-8').strip()
        branch = subprocess.check_output(['git', 'rev-parse', '--abbrev-ref', 'HEAD'], cwd=os.getcwd()).decode('utf-8').strip()
        repository = subprocess.check_output(['git', 'config', 'remote.origin.url'], cwd=os.getcwd()).decode('utf-8').strip().strip(".git")
        html_url = f"{repository}/commit/{sha}"

        return {
            'sha': sha,
            'branch': branch,
            'html_url': html_url
        }
    except Exception:
        return None

# Initialize session state variables
# Global variables for session state initialization

NONE_INIT_KEYS = [
    "self_selection", "val_input", "result", "temp_structured_json", "prompt_proof_guide", "prompt_proof_task",
    "image_paths", "proof", "theorem", "structured_proof", "paper", "paper_pdf", "format_index", "thm_details", 
    "uploaded_pdf", "genai_proof_button",
    # For benchmark
    "bm_input_opt", "bm_json_dataset", "bm_single_thm", "bm_single_proof", "bm_time_taken", "bm_total_problems", "bm_display_table", "bm_evaluator", "bm_status_text", "bm_progress_bar", "bm_results_container", "token_server", "async_mode"
]

FALSE_INIT_KEYS = [
    "request_button", "self_input_button", "log_server_cleaned", "server_output_success",
    "valid_input", "log_cleaned", "input_paper", "generation_complete",
    "input_pdf_paper", "input_pdf_proof", "input_pdf_theorem",
    "gen_ai_proof", "server_thm_details",
    # For benchmark
    "bm_run_button", "bm_started", "bm_result_success"
    
]

LLM_INIT_KEYS = [
    "llm_provider", "llm_list", "llm_api_key", "model_text", "model_img", "temperature", "llm_url",
    "model_leanaide",
]

# Initialize session state variables
for key in (NONE_INIT_KEYS + LLM_INIT_KEYS):
    if key not in sts:
        sts[key] = None

for key in FALSE_INIT_KEYS:
    if key not in sts:
        sts[key] = False

if "selected_tasks" not in sts:
    sts.selected_tasks = []

if "api_host" not in sts:
    sts.api_host = HOST
if "api_port" not in sts:
    sts.api_port = PORT

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
token_page = st.Page(
    page = "tabs/token_response.py",
    title = "Token Response",
    icon = ":material/code:",
)
benchmark_page = st.Page(
    page = "tabs/benchmark.py",
    title = "Benchmark",
    icon = ":material/speed:",
)
## Navigation
pg = st.navigation(pages = [
    intro_page,
    structured_json_page,
    server_response_page,
    logs_page,
    token_page,
    benchmark_page
])

for state in (NONE_INIT_KEYS + FALSE_INIT_KEYS + LLM_INIT_KEYS + ["selected_tasks"]):
    sts[state] = sts[state]

## Run 
pg.run()

# API Credentials Section
with st.sidebar:
    st.header("LLM Credentials", divider = "orange")
    with st.expander("Check API Credentials"):
        # Provider selection
        llm_provider = st.selectbox("Select Provider:", list(provider_info.keys()), index=0)
        if llm_provider != sts.get("llm_provider", ""):
            sts.llm_provider = llm_provider
            sts.llm_list = []

        # Dynamically update API Key and Model fields based on the provider
        selected_provider = provider_info[sts.llm_provider]

        try:
            if not sts.llm_list:
                sts.llm_list = get_supported_models(provider=sts.llm_provider)
        except Exception as e:
            st.error(f"Error fetching models for {sts.llm_provider}: {e}")

        api_key_placeholder = (
            f"{selected_provider['api_key'][:15]}{'*' * (len(selected_provider['api_key']) - 15)}"
            if selected_provider["api_key"]
            else ""
        )

        sts.llm_api_key = selected_provider["api_key"]
        received_api_key = st.text_input(
            "API Key:",
            value=api_key_placeholder,
            type="password",
            help="Hover to see the key, edit if needed.",
        )
        if received_api_key and received_api_key not in [sts.get("llm_api_key", "Key Not Found"), api_key_placeholder]:
            sts.llm_api_key = received_api_key
        

        st.info("The below options are models supported by your API Key.")
        # Model selection text boxes
        default_model_index = sts.llm_list.index(selected_provider["default_model"]) if selected_provider["default_model"] in sts.llm_list else 0

        model_list_help = f"Check out the list of {sts.llm_provider} Models [↗]({selected_provider['models_url']})"

        sts.model_leanaide = st.selectbox(
            "Model for LeanAide Code generation:",
            options = sts.llm_list,
            index = (sts.llm_list.index(selected_provider["default_leanaide_model"]) if selected_provider["default_leanaide_model"] in sts.llm_list else 0),
            help="Specify the model for LeanAide Codegen. " + model_list_help,
            accept_new_options = True
        )
        sts.model_text = st.selectbox(
            "Model for Proof/JSON Generator:",
            options = sts.llm_list,
            index = default_model_index,
            help="Specify the model for JSON Generator. " + model_list_help,
            accept_new_options = True
        )
        sts.model_img = st.selectbox(
            "Model for Image to Text:",
            options = sts.llm_list,
            index = default_model_index,
            help="Specify the model for Image to Text. " + model_list_help,
            accept_new_options = True
        ) 

    if st.button("Refresh Page", help="Refresh the page to set changes."):
        st.rerun()

    st.divider()
    st.warning("The Website is Under Development.")

    # Mention the commit(with link) and branch which the code refers to, by getting it
    commit_info = get_git_commit_info()
    if commit_info:
        st.info(f"Latest Build: [{commit_info['sha'][:7]}]({commit_info['html_url']})")
    else:
        st.warning("Error: Could not fetch commit details.")

    with st.expander("Other LeanAide Settings", expanded=False):
        st.info("These are side default settings, you may safely ignore them. More settings on top-right 3-dot menu.")
        sts.temperature = st.slider("Temperature:",
            min_value=0.0, max_value=1.0, value=0.8, step=0.1,
            help="Set the temperature for the model's responses. Default: 0.8",
        )
        sts.llm_url = st.text_input(
            "URL to query (for a local server)",
            help="Specify the URL for the LLM API. Example: `https://api.mistral.ai/v1/chat/completions`"
        )

    ## Session State visibility
    if st.checkbox("Show Session State", value=False, help = "Session State values, used for debugging."):
        st.sidebar.write("Session State:")
        # session state with masked API keys
        masked_state = {k: (v[:6] + "*" * (len(v) - 6) if "api_key" in k.lower() and isinstance(v, str) and len(v) > 6 else v) for k, v in sts.items()}
        # Hide very long texts
        for k, v in masked_state.items():
            if isinstance(v, str) and len(v) > 400:
                masked_state[k] = f"{v[:150]} ... =**Truncated**= ... {v[-150:]}"
        st.sidebar.json(masked_state)

if sts.llm_api_key and sts.llm_provider:
    # Post environment arguments to the server
    env_kwargs = {}
    if sts.model_leanaide:
        env_kwargs["model"] = sts.model_leanaide
    if sts.temperature is not None and not sts.temperature == 0.8:
        env_kwargs["temperature"] = int(10*sts.temperature)
    if sts.llm_url:
        env_kwargs["url"] = sts.llm_url
    try:
        post_env_args(
            provider = sts.llm_provider,
            auth_key = sts.llm_api_key,
            **env_kwargs,
        )
    except Exception as e:
        st.error(f"Error setting environment variables: {e}")


