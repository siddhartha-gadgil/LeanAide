import vertexai
import json
from vertexai.preview.language_models import CodeGenerationModel

filename = 'results/gpt4-20prompts-1choice-temp0/silly-results.json'
with open(filename, 'r') as f:
    js_lines = json.loads(f.read())

vertexai.init(project="882229164", location="us-central1")
parameters = {
    "max_output_tokens": 1024,
    "stop_sequences": [
        ":="
    ],
    "temperature": 0.2
}
model = CodeGenerationModel.from_pretrained("code-bison@001")
model = model.get_tuned_model(
    "projects/882229164/locations/us-central1/models/5188329289661022208")
for js in js_lines:
    print(js['docString'])
    response = model.predict(
        prefix="""Translate to Lean 4 statement ONLY:

        """ + js['prompt_cons'],
        **parameters
    )
    js['bison'] = response.text
    print(js['bison'])
    print('---')

with open(filename, 'w') as f:
    f.write(json.dumps(js_lines, indent=4, ensure_ascii=False))
