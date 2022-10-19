import subprocess
import os
import json
from ratelimit import limits, sleep_and_retry

api_key = os.environ["OPENAI_API_KEY"]

query = {"model": "code-davinci-002", 
         "prompt": "I am an expert Python programmer. Write a function that calculates the max s-t flow in a directed graph.\ndef",
         "temperature": 0.2, 
         "max_tokens": 200, 
         "stop": "\n"
        }

output = subprocess.run(["curl", "--silent", 
                "https://api.openai.com/v1/completions", 
                "-H", "Content-Type: application/json", 
                "-H", f"Authorization: Bearer {api_key}", 
                "-d", json.dumps(query)
                ], 
                capture_output=True
                )

print(output.stdout)
