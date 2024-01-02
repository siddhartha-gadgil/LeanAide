# Note: you need to be using OpenAI Python v0.27.0 for the code below to work
import openai
import os

openai.api_key = os.getenv("AZURE_OPENAI_KEY")
openai.api_base = os.getenv("AZURE_OPENAI_ENDPOINT") 
openai.api_type = 'azure'
openai.api_version = '2023-05-15' # this might change in the future

deployment_name='leanaide-gpt4'

lean_trans_prompt = """You are a coding assistant who translates from natural language to Lean Theorem Prover code following examples. Follow EXACTLY the examples given."""

sys_prompt = """You are a Mathematics, Lean 4 and coding assistant who answers questions about Mathematics and Lean 4, gives hints while coding in Lean 4. You also translates from natural language to Lean Theorem Prover code and vice versa when asked."""

trans_prompt = "  Follow EXACTLY any examples given when generating Lean code."

math_prompt="You are a mathematics assistant for research mathematicians and advanced students. Answer mathematical questions with the level of precision and detail expected in graduate level mathematics courses and in mathematics research papers."

def azure_completions(query, sys_prompt = sys_prompt, examples = [], n=5, deployment_name = deployment_name):
    messages = [{"role": "system", "content": sys_prompt}] + examples + [{"role": "user", "content": query}]
    completion = openai.ChatCompletion.create(
        engine=deployment_name,
        n= n,
        temperature=0.8,
        messages= messages
    )
    # return completion
    return [choice.message['content'].encode().decode('unicode-escape').encode('latin1').decode('utf-8') for choice in completion.choices] 

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
    completion = openai.ChatCompletion.create(
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
    response = openai.Embedding.create(
    input=text,
    engine="leanaide-embed"
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