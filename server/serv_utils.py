import json
import shlex

import streamlit as st

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
        "input": {"json_structured": "String"},
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
