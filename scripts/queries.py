# Note: you need to be using OpenAI Python v0.27.0 for the code below to work
from openai import AzureOpenAI
import os

client = AzureOpenAI(
  azure_endpoint = os.getenv("AZURE_OPENAI_ENDPOINT"), 
  api_key=os.getenv("AZURE_OPENAI_KEY"),  
  api_version="2023-05-15"
)

deployment_name='leanaide-gpt4'

lean_trans_prompt = """You are a coding assistant who translates from natural language to Lean Theorem Prover code following examples. Follow EXACTLY the examples given."""

sys_prompt = """You are a Mathematics, Lean 4 and coding assistant who answers questions about Mathematics and Lean 4, gives hints while coding in Lean 4. You also translates from natural language to Lean Theorem Prover code and vice versa when asked."""

trans_prompt = "  Follow EXACTLY any examples given when generating Lean code."

math_prompt="You are a mathematics assistant for research mathematicians and advanced students. Answer mathematical questions with the level of precision and detail expected in graduate level mathematics courses and in mathematics research papers."

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

def math(query, sys_prompt = math_prompt, examples = [], n=3, deployment_name = deployment_name):
    return azure_completions(query, sys_prompt, examples, n, deployment_name)

def doc_string(theorem, n= 3, is_prop = True):
    head = "theorem"
    kind = "theorem"
    if not(is_prop):
        head = "def"
        kind = "definition"
    text = f"""Describe the following {kind} briefly in natural language, similar to a documentation string. The description should be either a single sentence or a paragraph with 2-3 sentences, and may contain LaTeX mathematics.
    ```lean
    {head} {theorem} := by sorry
    ```
    """
    return azure_completions(text, examples = [], n = n)

def informalize(code, n = 3):
    text = f"""Translate the following Lean 4 code briefly into natural language. The translation can contain LaTeX mathematics. Note that a variable in Lean that has type a proposition can be interpreted as an assumption. Proofs of theorems have been omitted for brevity but all theorems have been proved.

    ```lean
    {code}
    ```
    """
    return azure_completions(text, examples = [], n = n)

def math_terms(statement, n = 3):
    text = f"""List all the mathematical terms in the following statement as a JSON list. Exclude meta-mathematical terms like suppose and prove, variable names and symbols. If there are no mathematical terms, return an empty list.

    {statement}
    """
    return math(text, n = n)

def math_synonyms(terms, n = 3):
    text = f'''For each of the mathematical terms in the following JSON list, give synonyms in JSON format as list of objects with two fields: "term" and "synonyms"

    {terms}
    '''
    return math(text, n = n)

def gpt4t_completions(query, sys_prompt = sys_prompt, examples = []):
    messages = [{"role": "system", "content": sys_prompt}] + examples + [{"role": "user", "content": query}]
    completion = client.chat.completions.create(
        model="gpt-4-1106-preview",
        n= 5,
        temperature=0.8,
        messages= messages
    )
    # return completion
    return [choice.message['content'].encode().decode('unicode-escape').encode('latin1').decode('utf-8') for choice in completion.choices]

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