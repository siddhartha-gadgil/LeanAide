# LeanAide Server Streamlit

This is a web interface made using Streamlit for LeanAide + AutoTA utilities.

## Installation

It is recommended to use python virtual environment to install the dependencies. I would recommend using `[uv](https://docs.astral.sh/uv/)` for the same.

```bash
python3 -m venv venv
source venv/bin/activate
pip install -r requirements.txt
```

Or using `uv`:

```bash
uv init
uv pip install -r requirements.txt
```

## Usage

1. Rename the `.env.example` to `.env` and fill in the required details.(No need for API Keys for this commit atleast)
2. Run the following command to start the server:

```bash
streamlit run slt_ui.py
```

## Future Tasks

- Support interactive feature with theorems and proofs, where user can change text and submit with it.
- Support OpenAI Structured Proof Generations(implemented, will be added if needed).
