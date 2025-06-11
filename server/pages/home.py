import streamlit as st

st.title("LeanAide Server [![Repo](https://badgen.net/badge/icon/LeanAide?icon=github&label)](https://github.com/siddhartha-gadgil/LeanAide)", anchor = "LeanAide Server")

st.sidebar.title("LeanAide Services")
st.sidebar.success("Please select a task page above.")

st.write("LeanAide Streamlit Server provides a user interface for interacting with LeanAide server.")

st.header("Utilities", divider = True, anchor = "Utilities")
st.write(
"""
To use different services, you can visit the different pages in the sidebar.

- `Server Response`: POST requests to the server and get response.
- `Structured Json`: Input your theorem-proof and obtain structured JSON output with LeanAide Schema's.

Visit the official GitHub [LeanAide](https://github.com/siddhartha-gadgil/LeanAide) repository for more information and documentation.
"""
)

st.divider()