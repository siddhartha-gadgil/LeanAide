# LeanAide Streamlit Server

This is a Streamlit server for the Project.

## About

The LeanAide Streamlit server is designed to provide a user-friendly interface for POSTING and GETTING queries for Autoformalization tasks.
The main backend is powered by the LeanAide tools. The server is buit using Streamlit and FastAPI, allowing users to interact with a simple web interface.

The `leanaide_serv.py` runs two processed, which are `streamlit` and `fastapi`. The Streamlit app is used for the frontend website, which you can interact with, while the FastAPI app is used to handle the API requests. This allows you to use `curl` or any other HTTP client to interact with the server from your terminal, our streamlit app or any other program you write.

## Installation Instructions

1. If you have not cloned the repository, you can do so with the following command:

```bash
git clone https://github.com/siddhartha-gadgil/LeanAide.git
cd LeanAide # go inside LeanAide directory
```

2. Create an environment, either using default Python or [uv](https://docs.astral.sh/uv/)(recommended):

```bash
uv venv --python 3.13
```

3. Install the required packages:

```bash
uv pip install -r requirements.txt
source .venv/bin/activate
```

4. Run the Server:

```bash
python3 leanaide_serv.py
```

This will start the Streamlit server on `http://localhost:8501` and the FastAPI server on `http://localhost:7654`. These ports can be changed in the `leanaide_serv.py` file if needed.
