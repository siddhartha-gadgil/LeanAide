from openai import OpenAI
import jsonlines

# Set OpenAI's API key and API base to use vLLM's API server.
openai_api_key = "EMPTY"
openai_api_base = "http://localhost:8000/v1"

client = OpenAI(
    api_key=openai_api_key,
    base_url=openai_api_base,
)

def get_response(prompt):
    response = client.chat.completions.create(
        model="mistralai/Mistral-7B-Instruct-v0.2",
        messages=[
            {"role": "user", "content": prompt},
        ]
    )
    return response.choices[0].message.content

def prompt (description):
    text = f"""The following is a description of the statement of a theorem in Lean 4.
---
{description}
---
Give a concise, single-sentence mathematical statement of the theorem. Give ONLY the statement
"""
    return text

# Trial version

count = 0
with jsonlines.open("rawdata/premises/ident_pairs/descriptions_docs.jsonl", "r") as reader:
    with jsonlines.open("rawdata/premises/ident_pairs/descs_docs.jsonl", "w") as writer:
        for js in reader:
            name = js["name"]
            print(f"Processing {name}; {count} examples processed.")
            count += 1            
            if "description" in js:
                description = js["description"]
                js['concise-description'] = get_response(prompt(description)) 
            writer.write(js)
