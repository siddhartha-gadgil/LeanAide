import streamlit as st

# Initialize session state variables
# Global variables for session state initialization
NONE_INIT_KEYS = [
    "self_selection", "val_input", "result", "temp_structured_json", "prompt_proof_guide",
    "image_paths", "proof", "theorem", "structured_proof", "paper", "paper_pdf", "format_index",
    "model_text", "model_img", "llm_provider", "llm_list", "uploaded_pdf"
]

FALSE_INIT_KEYS = [
    "request_button", "self_input_button", "log_server_cleaned", "log_order",
    "server_output_success", "valid_input", "log_cleaned", "input_paper",
    "generation_complete", "input_image_paper", "input_pdf_paper", "input_image_proof", 
    "input_image_theorem", "input_pdf_proof", "input_pdf_theorem"
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
    if st.checkbox("Show Session State", value=False, help = "Session State values, used for debugging."):
        st.sidebar.write("Session State:")
        st.sidebar.json(st.session_state)

