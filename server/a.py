import streamlit as st

col_order = ["time1", "time2"]
table = ["hi", "there"]
# Make a markdown table with col_order
markdown_table = "| " + " | ".join(col_order) + " |\n"
markdown_table += "| " + " | ".join(["---"] * len(col_order)) + " |\n"
markdown_table += "| " + " | ".join(table) + " |\n  "
st.markdown(markdown_table)