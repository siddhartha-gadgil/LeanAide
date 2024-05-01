import json
import jsonlines
# import openai
from queries import azure_embed

out_lines = []
count = 0

with open("rawdata/mathlib4-descs-embeddings.json", 'w', encoding='utf-8') as out:
    with jsonlines.open("resources/mathlib4-descs.jsonl", "r") as reader:
        for l in reader:
            embedding = azure_embed(l["description"])
            l["description-embedding"] = embedding
            print(l["description"])
            embedding = azure_embed(l["concise-description"])
            l["concise-description-embedding"] = embedding
            print(l["concise-description"])
            count = count + 1
            print(f"Completed {count}")
            out_lines.append(l)
        # write the embeddings to `out`
        json.dump(out_lines, out, indent=4, ensure_ascii=False)
