# Note: you need to be using OpenAI Python v0.27.0 for the code below to work
from openai import AzureOpenAI
import os
from pathlib import Path
import json
from string import Template
import subprocess

def nearest_embeddings(query, n = 10):
    result = subprocess.run(["lake", "exe", "nearest_embeddings_full", query, str(n)], capture_output=True, text=True, cwd=homedir)
    # return completion
    return json.loads(result.stdout)

def statement(js):
    if js['isProp']:
        kind = "theorem"
    else:
        kind = "def"
    return f"{kind} {js['name']}: {js['theorem']} := by sorry"


client_azure = AzureOpenAI(
  azure_endpoint = os.getenv("AZURE_OPENAI_ENDPOINT"), 
  api_key=os.getenv("AZURE_OPENAI_KEY"),  
  api_version="2023-05-15"
)

from openai import OpenAI

client_gpt = OpenAI(
  api_key=os.environ['OPENAI_API_KEY'],  # this is also the default, it can be omitted
)

from mistralai.client import MistralClient
from mistralai.models.chat_completion import ChatMessage

api_key = os.environ["MISTRAL_API_KEY"]
model = "mistral-large-latest"

client_mistral = MistralClient(api_key=api_key)

deployment_name='leanaide-gpt4'

homedir = Path(".")
if "lakefile.lean"  not in os.listdir(homedir):
    homedir = Path("..")

resources = os.path.join(homedir, "resources")

llm_dir = os.path.join(homedir, "llm_data")

templates = json.load(open(os.path.join(resources, "templates.json")))

lean_trans_prompt = templates['lean_trans_prompt']

sys_prompt = templates['sys_prompt']

trans_prompt = templates['translate_sys_prompt']

math_prompt=templates['math_sys_prompt']

def split_by_markdown_heading(filename, head = "### "):
  """Splits a markdown document based on second-level headings (##) and includes the heading.

  Args:
      filename: The path to the markdown document.

  Returns:
      A list of strings, where each element is a section of the document including its heading.
  """
  sections = []
  current_section = ""
  with open(filename, "r", encoding="utf-8") as f:
    for line in f:
      if line.startswith(head):
        # New section, add previous section and start a new one
        if current_section:
          sections.append(current_section)
        current_section = line.strip()  # Include the heading without leading/trailing whitespace
      else:
        current_section += line
  # Add the last section after the loop
  if current_section:
    sections.append(current_section)
  return sections


class ChatClient:
    verbose = False

    def set_verbose(self, verbose = True):
        self.verbose = verbose

    def __init__(self, client = client_gpt , model="gpt-4-turbo-preview"):
        self.client = client
        self.model = model
        self.data_path = os.path.join(llm_dir, model)
        os.makedirs(self.data_path, exist_ok=True)

    def dump(self, data, name, task):
        wd = os.path.join(self.data_path, name)
        os.makedirs(wd, exist_ok=True)
        print(wd)
        print(f"Verbose: {self.verbose}")
        if self.verbose:
            print(json.dumps(data, ensure_ascii=False, indent=2))
        with open(os.path.join(wd, task+".json"), 'w') as f:
            json.dump(data, f, ensure_ascii=False, indent=2)

    def choices(self, query, sys_prompt = sys_prompt, examples = [], n= 3):
        messages = [{"role": "system", "content": sys_prompt}] + examples + [{"role": "user", "content": query}]
        completion = self.client.chat.completions.create(
            model=self.model,
            n= n,
            temperature=0.8,
            messages= messages
        )
        return completion.choices

    def choices_json(self, query, sys_prompt = sys_prompt, examples = [], n= 3):
        messages = [{"role": "system", "content": sys_prompt}] + examples + [{"role": "user", "content": query}]
        completion = self.client.chat.completions.create(
            model=self.model,
            n= n,
            temperature=0.8,
            response_format={"type": "json_object"},
            messages= messages
        )
        return completion.choices


    def completions(self, query, sys_prompt = sys_prompt, examples = [], n= 3, ensure_json = False):
        if ensure_json:
            choices = self.choices_json(query, sys_prompt, examples, n)
        else:
            choices = self.choices(query, sys_prompt, examples, n)
        return [choice.message.content for choice in choices]

    def math(self, query, sys_prompt = math_prompt, examples = [], n=3, deployment_name = deployment_name):
        return self.completions(query, sys_prompt, examples, n)

    def prove(self, theorem, n= 3):
        query = Template(templates['prove']).substitute(theorem = theorem)
        return self.math(query, n = n)
        
    def prove_with_outline(self, theorem, label, n= 3):
        query = Template(templates['prove_with_outline']).substitute(theorem = theorem)
        return self.math(query, n = n)
    
    def solve(self, problem, n= 3):
        query = Template(templates['solve']).substitute(problem = problem)
        return self.math(query, n = n)
        
    def solution_to_theory(self, problem, solution, n= 3):
        query = Template(templates['solution_to_theory']).substitute(problem = problem, solution = solution)
        return self.math(query, n = n)

    def make_structured(self, text, n= 3):
        query = Template(templates['make_structured']).substitute(text = text)
        return self.completions(query, n = n)
        
    def doc_string(self, theorem, n= 3, is_prop = True):
        head = "theorem"
        kind = "theorem"
        if not(is_prop):
            head = "def"
            kind = "definition"
        text = Template(templates['doc_string']).substitute(head = head, theorem = theorem, kind = kind)    
        return self.completions(text, examples = [], n = n)

    def informalize(self, code, n = 3):
        text = Template(templates['informalize']).substitute(code = code)
        return self.completions(text, examples = [], n = n)

    def math_terms(self, statement, n = 3):
        text = Template(templates['math_terms']).substitute(statement = statement)
        return self.math(text, n = n)

    def math_synonyms(self, terms, n = 3):
        text = Template(templates['math_synonyms']).substitute(terms = terms)
        return math(text, n = n)

    def add_statements(self, text, n = 3):
        query = Template(templates['add_statements']).substitute(text = text)
        return self.completions(query, n = n)

    def summarize(self, text, sys_prompt = math_prompt, examples = [], n = 3):
        query = Template(templates['summarize']).substitute(text = text)
        return self.completions(query, sys_prompt, examples, n = n, ensure_json = True)
    
    def save_incremental_structure(self, texts, label, n = 1):
        structured_texts = []
        summaries = []
        for text in texts:
            if summaries:
                summary = summaries[-1]
                summary_text = ""
                for s in summary:
                    summary_text += s + "\n-------------\n"
                query = Template(templates['extend_structure']).substitute(text = text, summary = summary)
            else:
                query = Template(templates['make_structured']).substitute(text = text)    
            structured_text = self.completions(query, n = n)
            structured_texts.append(structured_text)
        js = {"texts": texts, "structured_texts": structured_texts}
        if self.verbose:
            print(json.dumps(js, indent=2, ensure_ascii=False))
        json.dump(js, open(os.path.join(self.data_path, label + "-long-structured.json"), "w"), ensure_ascii=False)
        return js
            


class AzureChatClient(ChatClient):
    def __init__(self, deployment_name = deployment_name):
        self.deployment_name = deployment_name
        self.client = client_azure
        self.data_path = os.path.join(llm_dir, "azure", deployment_name)
        os.makedirs(self.data_path, exist_ok=True)

    def choices(self, query, sys_prompt = sys_prompt, examples = [], n= 3):
        messages = [{"role": "system", "content": sys_prompt}] + examples + [{"role": "user", "content": query}]
        completion = client_azure.chat.completions.create(
            model=self.deployment_name,
            n= n,
            temperature=0.8,
            messages= messages
        )
        return completion.choices
    
    def choices_json(self, query, sys_prompt = sys_prompt, examples = [], n= 3):
        messages = [{"role": "system", "content": sys_prompt}] + examples + [{"role": "user", "content": query}]
        completion = client_azure.chat.completions.create(
            model=self.deployment_name,
            n= n,
            temperature=0.8,
            response_format={"type": "json_object"},
            messages= messages
        )
        return completion.choices

default_client = AzureChatClient()
class MistralChatClient(ChatClient):
    def __init__(self):
        self.model = "mistral-large-latest"
        self.client = client_mistral
        self.data_path = os.path.join(llm_dir, "mistral", model)
        os.makedirs(self.data_path, exist_ok=True)    

    def choices(self, query, sys_prompt=sys_prompt,  n=3):
        messages = [ChatMessage(role="user", content=sys_prompt+'\n------\n'+ query)]
        completion = self.client.chat(
            model=self.model,
            temperature=0.8,
            messages=messages
        )
        return completion.choices

def process_problem(client, problem, name, n= 3):
    data = {"problem": problem}
    solutions = client.solve(problem, n)
    data['solutions'] = solutions
    client.dump(data, name, 'solve')
    theories = []
    for sol in solutions:
        theory = client.problem_to_theory(problem, sol, n=1)[0]
        theories.append(theory)
    data['theories'] = theories
    client.dump(data, name, 'solve_theory')
    structured_texts = []
    theory_structureds = ''
    for theory in theories:
        structured = client.make_structured(theory, n = n)
        structured_texts = structured_texts + structured
        theory_structureds.append({"theory": theory, "structured": structured})
    data['structured_texts'] = structured_texts
    client.dump(data, name, 'solve_theory_structured')
    texts_with_statements = []
    for structured in structured_texts:
        with_statements = client.add_statements(structured)
        texts_with_statements = texts_with_statements + with_statements
    data['texts_with_statements'] = texts_with_statements
    client.dump(data, 'solve_with_statements')
    return data

def process_problem_file(filename, client = default_client):
    client.set_verbose()
    print(f"Processing {filename}")
    print(f"Verbose: {client.verbose}")
    sols = []
    with open(os.path.join(resources, filename), encoding='UTF-8') as f:
        kvs = json.load(f)
        for entry in kvs:
            print("Processing", entry['name'])
            solution = process_problem(client, problem=entry['problem'], name=entry['name'])
            sols.append(solution)
    return sols



# The code below is deprecated. One should use the classes above.
def azure_completions(query, sys_prompt = sys_prompt, examples = [], n=5, deployment_name = deployment_name):
    messages = [{"role": "system", "content": sys_prompt}] + examples + [{"role": "user", "content": query}]
    completion = client_azure.chat.completions.create(
        model=deployment_name,
        n= n,
        temperature=0.8,
        messages= messages
    )
    # return completion
    return [choice.message.content for choice in completion.choices] 

def gpt4t_completions(query, sys_prompt = sys_prompt, examples = [], n= 3):
    messages = [{"role": "system", "content": sys_prompt}] + examples + [{"role": "user", "content": query}]
    completion = client_gpt.chat.completions.create(
        model="gpt-4-turbo-preview",
        n= n,
        temperature=0.8,
        messages= messages
    )
    # return completion
    return [choice.message.content for choice in completion.choices]


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

def summarise(text, sys_prompt = math_prompt, examples = [], n = 3):
    query = Template(templates['summarise']).substitute(text = text)
    return azure_completions(query, sys_prompt, examples, n = n, deployment_name='leanaide-gpt4-32')

# print([choice.message['content'].encode().decode('unicode-escape').encode('latin1').decode('utf-8') for choice in completion.choices])

import re

def escape(s):
    return re.sub(r"(?<=[ ])[\t\r](?=[a-zA-Z])",  r"\\t", re.sub(r"(?<=[ ])[\n\r](?=[a-zA-Z])", r"\\n", s))

def azure_embed(text):
    response = client_azure.embeddings.create(
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

