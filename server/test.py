import streamlit as st
from code_editor import code_editor

your_code_string = "def hello_world():\n    print('Hello, world!')\n\nhello_world()"

response_dict = code_editor(your_code_string, lang = "" ,shortcuts = "vim")