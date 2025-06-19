import streamlit as st
import st.session_state as sts
from logging_utils import log_server, log_buffer_clean

st.markdown("<div id='log_top'></div>", unsafe_allow_html=True)    
st.title("LeanAide Logs")

st.subheader("Server Website Stdout/Stderr", help = "Logs are written to LeanAide Server LOGFILE and new logs are updated after SUBMIT REQUEST button is clicked.")
st.info("You can clear all the logs, reverse the order or change wrapping of the logs from the sidebar.")

if "log_order" not in sts:
    sts.log_order = True  # Default to reverse order
if "log_wrap" not in sts:
    sts.log_wrap = True  # Default to wrap lines

# Button here otherwise it will be at the far bottom of the page
with st.sidebar:
    st.subheader("Server Logs Options", divider = "green")

    # Reverse order
    sts.log_order = st.checkbox("Reverse Order", value=True, help="Check this box to display the logs in reverse order. Default: Display the new logs at the top.")
    sts.log_wrap = st.checkbox("Wrap Lines", value=True, help="Check this box to wrap the lines in the logs. Default: True")
    
    st.write("")
    # Clean logs
    with st.popover("Clean Server Logs", help="Click and select Yes to clean the server logs. This will delete all the logs in the server log file."):
        st.write("Are you sure you want to clean the server logs? This will delete all the logs in the server.")
        if st.button("Yes"):
            try:
                sts.log_server_cleaned = True
                log_buffer_clean(log_file=True)
                st.success("Server logs cleaned successfully! Please UNCHECK THE BOX to avoid cleaning again.")
                st.rerun()
            except Exception as e:
                st.error(f"Error cleaning server logs: {e}")
        if st.button("No"):
            pass
        sts.log_server_cleaned = False
        st.info("Press Escape to close this popover.")

        
if log_out := log_server(log_file=True, order = sts.log_order):
    if sts.log_order:
        st.write("Logs are displayed in newest first order.")
    else:
        st.write("Logs are displayed in oldest first order.")
    st.code(
        log_out if not sts.log_server_cleaned else "No logs available yet.",
        language = "log",
        wrap_lines=sts.log_wrap,
        line_numbers=True,
    )
else:
    st.code("No logs available yet.", language="plaintext")

st.markdown("<div id='log_bottom'></div>", unsafe_allow_html=True)    