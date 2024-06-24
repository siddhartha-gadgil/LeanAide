import os
import json
from os.path import join
from pathlib import Path
from string import Template

homedir = Path(".")
if "lakefile.lean"  not in os.listdir(homedir):
    homedir = Path("..")

def proofs():
    pairs = []
    for root, _, files in os.walk(join(homedir,join('llm_data', 'gpt-4-turbo-preview'))):
        for file in files:
            if file == "solve.json":
                filepath = os.path.join(root, file)
                f = open(filepath, 'r')
                js = json.load(f)
                for solution in js['solutions']:
                    pairs.append((js['problem'], solution))
    return pairs

def proof_groups():
    groups = []
    for root, _, files in os.walk(join(homedir,join('llm_data', 'gpt-4-turbo-preview'))):
        for file in files:
            if file == "solve.json":
                filepath = os.path.join(root, file)
                f = open(filepath, 'r')
                js = json.load(f)
                print("Loaded json: " + js['problem'])
                sols = []
                for solution in js['solutions']:
                    sols.append(solution)
                groups.append((js['problem'], sols))
    return groups

def theorem_proof (problem, solution):
    return f"""## Theorem: {problem}
## Proof: 
{solution}
""".replace('\\\\', '\\')


resources = os.path.join(homedir, "resources")

proof_template = open(os.path.join(resources, "JsonTemplate.md")).read()

def proof_queries():
    for problem, solution in proofs():
        statement = theorem_proof(problem, solution)
        yield Template(proof_template).substitute(proof=statement)

def proof_group_queries():
    groups = []
    problems = []
    for problem, solutions in proof_groups():
        queries = []
        problems.append(problem)
        for solution in solutions:
            statement = theorem_proof(problem, solution)
            queries.append(Template(proof_template).substitute(proof=statement))
        groups.append(queries)
    return groups, problems
