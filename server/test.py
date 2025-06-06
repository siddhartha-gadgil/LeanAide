import json

import requests
import streamlit as st

from leanaide_serv import FASTAPI_PORT

st.title("Basic Caculator App 🧮")

# taking user inpputs
option = "Addition"
option = st.selectbox('What operation You want to perform?',
                     ('Addition', 'Subtraction', 'Multiplication', 'Division'))
st.write("")
st.write("Select the numbers from slider below 👇")
x = st.slider("X", 0, 100, 20)
y = st.slider("Y", 0, 130, 10)

#converting the inputs into a json format
inputs = {"operation": option,   "x": x,  "y": y}

# when the user clicks on button it will fetch the API
if st.button('Calculate'):
    res = requests.post(url = f"http://127.0.0.1:{FASTAPI_PORT}", data = json.dumps(inputs))
    st.code(inputs)
    st.write(f"Response from API 🚀  =  {res.text}")
