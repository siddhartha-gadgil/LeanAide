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

def mkPrompt(js):
    s ='The following are examples of documentation strings and their corresponding Lean 4 statements.\n\n'
    for p in json.loads(js['prompts']):
        s += p['docString'] + '\n'
        s += p['theorem'] + '\n\n'
    s +=  'Translate the following documentation string to a Lean 4 statement ONLY.'
    s += js['docString']
    return s
model = CodeGenerationModel.from_pretrained("code-bison@001")
model = model.get_tuned_model(
    "projects/882229164/locations/us-central1/models/5188329289661022208")
for js in js_lines:
    try:
        print(js['docString'])
        response = model.predict(
            prefix=mkPrompt(js),
            **parameters
        )
        js['bison'] = response.text
        print(js['bison'])
        print('---')
    except Exception as e:
        print(e)
        print('---')
print('Done')
filename = 'results/gpt4-20prompts-1choice-temp0/silly-bison-results.json'
wf = open(filename, 'w', encoding='utf-8')
json.dump(js_lines, wf, ensure_ascii=False, indent=2)
print("json dumped")
wf.close()
