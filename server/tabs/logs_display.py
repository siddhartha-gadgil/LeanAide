import streamlit as st
from logging_utils import log_server, log_buffer_clean

st.markdown("<div id='log_top'></div>", unsafe_allow_html=True)    
st.title("LeanAide Logs")

st.subheader("Server Website Stdout/Stderr", help = "Logs are written to LeanAide Server LOGFILE and new logs are updated after SUBMIT REQUEST button is clicked.")
st.info("You can clear all the logs or reverse the order of the logs from the sidebar.")

# Button here otherwise it will be at the far bottom of the page
with st.sidebar:
    st.subheader("Server Logs Options", divider = "green")

    # Reverse order
    st.session_state.log_order = st.checkbox("Reverse Order", value=True, help="Check this box to display the logs in reverse order. Default: Display the new logs at the top.")
    
    st.write("")
    # Clean logs
    with st.popover("Clean Server Logs", help="Click and select Yes to clean the server logs. This will delete all the logs in the server log file."):
        st.write("Are you sure you want to clean the server logs? This will delete all the logs in the server.")
        if st.button("Yes"):
            try:
                st.session_state.log_server_cleaned = True
                log_buffer_clean(log_file=True)
                st.success("Server logs cleaned successfully! Please UNCHECK THE BOX to avoid cleaning again.")
                st.rerun()
            except Exception as e:
                st.error(f"Error cleaning server logs: {e}")
        if st.button("No"):
            pass
        st.session_state.log_server_cleaned = False
        st.info("Press Escape to close this popover.")

    st.divider()
        
if log_out := log_server(log_file=True, order = st.session_state.log_order):
    if st.session_state.log_order:
        st.write("Logs are displayed in newest first order.")
    else:
        st.write("Logs are displayed in oldest first order.")
    st.code(
        log_out if not st.session_state.log_server_cleaned else "No logs available yet.",
        language = "log",
        wrap_lines =True,
        line_numbers=True,
    )
else:
    st.code("No logs available yet.", language="plaintext")

st.markdown("<div id='log_bottom'></div>", unsafe_allow_html=True)    