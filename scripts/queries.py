# Note: you need to be using OpenAI Python v0.27.0 for the code below to work
from openai import AzureOpenAI
import os
from pathlib import Path
import json
from string import Template

client = AzureOpenAI(
  azure_endpoint = os.getenv("AZURE_OPENAI_ENDPOINT"), 
  api_key=os.getenv("AZURE_OPENAI_KEY"),  
  api_version="2023-05-15"
)

homedir = Path(".")
if "lakefile.lean"  not in os.listdir(homedir):
    homedir = Path("..")

resources = os.path.join(homedir, "resources")

llm_dir = os.path.join(homedir, "llm_data")

templates = json.load(open(os.path.join(resources, "templates.json")))

with open(os.path.join(resources, "ProofJson.md"), 'r') as f:
    proof_json= f.read()

deployment_name='leanaide-gpt4'

lean_trans_prompt = templates['lean_trans_prompt']

sys_prompt = templates['sys_prompt']

trans_prompt = templates['translate_sys_prompt']

math_prompt=templates['math_sys_prompt']

def azure_completions(query, sys_prompt = sys_prompt, examples = [], n=5, deployment_name = deployment_name):
    messages = [{"role": "system", "content": sys_prompt}] + examples + [{"role": "user", "content": query}]
    completion = client.chat.completions.create(
        model=deployment_name,
        n= n,
        temperature=0.8,
        messages= messages
    )
    # return completion
    return [choice.message.content for choice in completion.choices] 

import subprocess
def nearesest_neighbour(query, n = 10):
    result = subprocess.run(["lake", "exe", "nearest_embeddings_full", query, str(n)], capture_output=True, text=True, cwd=homedir)
    # return completion
    return json.loads(result.stdout)

def math(query, sys_prompt = math_prompt, examples = [], n=3, deployment_name = deployment_name):
    return azure_completions(query, sys_prompt, examples, n, deployment_name)

def doc_string(theorem, n= 3, is_prop = True):
    head = "theorem"
    kind = "theorem"
    if not(is_prop):
        head = "def"
        kind = "definition"
    text = Template(templates['doc_string']).substitute(head = head, theorem = theorem, kind = kind)    
    return azure_completions(text, examples = [], n = n)

def informalize(code, n = 3):
    text = Template(templates['informalize']).substitute(code = code)
    return azure_completions(text, examples = [], n = n)

def math_terms(statement, n = 3):
    text = Template(templates['math_terms']).substitute(statement = statement)
    return math(text, n = n)

def math_synonyms(terms, n = 3):
    text = Template(templates['math_synonyms']).substitute(terms = terms)
    return math(text, n = n)

def gpt4t_completions(query, sys_prompt = sys_prompt, examples = [], n= 3):
    messages = [{"role": "system", "content": sys_prompt}] + examples + [{"role": "user", "content": query}]
    completion = client.chat.completions.create(
        model="gpt-4-1106-preview",
        n= n,
        temperature=0.8,
        messages= messages
    )
    # return completion
    return [choice.message['content'].encode().decode('unicode-escape').encode('latin1').decode('utf-8') for choice in completion.choices]

def summarise(text, sys_prompt = math_prompt, examples = [], n = 3):
    query = Template(templates['summarise']).substitute(text = text)
    return azure_completions(query, sys_prompt, examples, n = n, deployment_name='leanaide-gpt4-32')

# print([choice.message['content'].encode().decode('unicode-escape').encode('latin1').decode('utf-8') for choice in completion.choices])

import re

def escape(s):
    return re.sub(r"(?<=[ ])[\t\r](?=[a-zA-Z])",  r"\\t", re.sub(r"(?<=[ ])[\n\r](?=[a-zA-Z])", r"\\n", s))

def azure_embed(text):
    response = client.embeddings.create(
    input=text,
    model="text-embedding-ada-002"
    )
    return response['data'][0]['embedding']

import time

def repeat_query(query_func, argument, default, steps, delay):
    if steps < 0:
        return default
    else:
        try:
            return query_func(argument)
        except:
            print(f"Error: {steps} steps left. Retrying in {delay} seconds.")
            time.sleep(delay)
            return repeat_query(query_func, argument,  default, steps - 1, delay * 2)
        
def print_all(ss):
    for s in ss:
        print(escape(s))
        print('---------------------------')

json_proof=r'''Write proofs as a JSON list of proof steps

* Each step an object with two fields, "type" and "content"
* The "type" being "definition", "assertion", "assumption", "fix" or "observation"
* An object with type "definition" should be purely a definition, with consequences separated as assertions or observations.
* The content of an observation is a statement that is a simple calculation or other result that needs no justification.
* The "content" of an assertion having fields "claim" and "justification" and a field "using" which is a (possibly empty) list of results used
* Each justification should be a single fairly simple sentence. If a longer justification is needed break the step into smaller steps.
* Each list item in the "using" field should be a name of a theorem/lemmma or short statements giving a well-known or previously proved claim/theorem/lemma. 
* Wherever possible an item in "using" should be broken into smaller statements.
* If required backtrack in a proof going back to the beginning or an earlier stage.

'''

json_schema=r'''First write a detailed mathematical solution is standard style. Then write the proof in a fenced code block as a JSON list of proof steps, each of which is one of the following:

- A single field "definition" with the value being a definition. The definition should be purely a definition, with consequences separated as assertions or observations.
- A single field "assumption" with the value being an assumption.
- A single field "observation" with the value being a statement that is a simple calculation or other result that needs no justification.
- A single field "introduction" with a let statement as the value.
- A single field "theorem" with the statement of a well known result.
- An assertion with three fields:
  - "claim" with the value being a statement that is to be proved.
  - "justification" with the value being a justification for the claim; this should be a single fairly simple sentence; if a longer justification is needed break the step into smaller steps.
  - "using" with the value being a list of results used, with each item one of:
      - name of a theorem/lemmma
      - short statements giving a single well-known or previously proved claim/theorem/lemma (multiple claims should be broken up).
- A single field "goal" stating a claim that will eventually be proved.

'''  