import json

with open('data/mathlib4-prompts.json', 'r') as f:
    json_data = json.load(f)

with open('rawdata/training-prompts.jsonl', 'w') as wf:
    for entry in json_data:
        pair={"input_text" : "Translate to Lean 4 statement ONLY: \\n/-- "+entry['docString']+ " -/", "output_text" : "theorem : "+ entry['type'] + " := sorry"}
        json.dump(pair, wf, ensure_ascii=False)
        wf.write('\n')
    wf.flush()
    wf.close()
