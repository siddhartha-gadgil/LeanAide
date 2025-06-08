import ast
import json
import shlex
from typing import Any, Tuple, Type

import streamlit as st

from api_server import HOST

# Lean Checker Tasks
tasks = {
    "echo": {"input": {"data": "Json"}, "output": {"data": "Json"}},
    "translate_thm": {
        "input": {"text": "String"},
        "output": {"theorem": "String"},
        "parameters": {
            "greedy": "Bool (default: true)",
            "fallback": "Bool (default: true)",
        },
    },
    "translate_def": {
        "input": {"text": "String"},
        "output": {"definition": "String"},
        "parameters": {"fallback": "Bool (default: true)"},
    },
    "theorem_doc": {
        "input": {"name": "String", "command": "String"},
        "output": {"doc": "String"},
    },
    "def_doc": {
        "input": {"name": "String", "command": "String"},
        "output": {"doc": "String"},
    },
    "theorem_name": {"input": {"text": "String"}, "output": {"name": "String"}},
    "prove": {"input": {"theorem": "String"}, "output": {"proof": "String"}},
    "structured_json_proof": {
        "input": {"theorem": "String", "proof": "String"},
        "output": {"json_structured": "Json"},
    },
    "lean_from_json_structured": {
        "input": {"json_structured": "Json String"},
        "output": {
            "lean_code": "String",
            "declarations": "List String",
            "top_code": "String",
        },
    },
    "elaborate": {
        "input": {"lean_code": "String", "declarations": "List Name"},
        "output": {"logs": "List String", "sorries": "List Json"},
        "parameters": {
            "top_code": 'String (default: "")',
            "describe_sorries": "Bool (default: false)",
        },
    },
}


def parse_curl(curl_cmd, ignore_curl_ip_port):
    args = shlex.split(curl_cmd)
    out = {"method": "POST", "url_ip": "", "port": "", "headers": {}, "data": {}}
    i = 0
    while i < len(args):
        match args[i]:
            case "curl":
                i += 1
            case "-X":
                out["method"] = args[i + 1]
                i += 2
            case "-H":
                k, v = args[i + 1].split(":", 1)
                out["headers"][k.strip()] = v.strip()
                i += 2
            case "--data" | "-d":
                try:
                    out["data"] = json.loads(args[i + 1])
                except Exception:
                    out["data"] = args[i + 1]
                i += 2
            case x if x.startswith("http"):
                x = x.split("://", 1)[1].split(":", 1)
                if ignore_curl_ip_port:
                    out["url_ip"] = st.session_state.get("api_host", HOST)
                    out["port"] = st.session_state.get("api_port", "7654")
                else:
                    out["url_ip"] = x[0]
                    out["port"] = x[1]
                i += 1
            case _:
                i += 1
    return out


def button_clicked(button_arg):
    def protector():
        """This function does not allow value to become True until the button is clicked."""
        st.session_state[button_arg] = True
    return protector

def get_actual_input(input_str: str) -> Tuple[Type, Any]:
    """
    Convert a string representation of a Python literal into its corresponding type.
    Returns a tuple of (type, parsed_value).
    """
    try:
        json_input = json.loads(input_str) # Check if the input is valid JSON
        return (type(json_input), json_input)
    except json.JSONDecodeError:
        try:
            # If not JSON, check if if it is a list
            literal_input = ast.literal_eval(input_str)
            return (type(literal_input), literal_input)
        except (ValueError, SyntaxError):
            # If all else fails, return as string
            return (str, input_str)

def validate_input_type(input_type: Any, expected_type: str) -> bool:
    """
    Validate if the input value matches the expected type.
    Returns True if it matches, False otherwise.
    """
    exp = expected_type.lower().split()
    if "json" in exp:
        if input_type.__name__.lower() == "dict":
            return True
    elif "list" in exp:
        if input_type.__name__.lower() == "list":
            return True
    elif "string" in exp or "str" in exp:
        if input_type.__name__.lower() == "str":
            return True
    elif "int" in exp:
        if input_type.__name__.lower() == "int":
            return True
    elif "bool" in exp or "boolean" in exp:
        if input_type.__name__.lower() == "bool":
            return True
    return False
