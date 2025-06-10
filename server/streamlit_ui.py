import streamlit as st

# Page Setup
intro_page = st.Page(
    page = "pages/intro.py",
    title = "Home",
    icon = ":material/home:",
    default = True,
)

server_response_page = st.Page(
    page = "pages/server_response.py",
    title = "Server Response",
    icon = ":material/rocket_launch:",
)
structured_json_page = st.Page(
    page = "pages/structured_json.py",
    title = "Structured Json",
    icon = ":material/code:"
)

## Navigation
pg = st.navigation(pages = [
    intro_page,
    server_response_page,
    structured_json_page,
])

## Run 
pg.run()