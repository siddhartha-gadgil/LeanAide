import os
from os.path import join
from pathlib import Path

import vertexai
from vertexai.generative_models import GenerativeModel, Part

from .queries import ChatClient, extract_json_block

homedir = Path(".")
if "lakefile.lean"  not in os.listdir(homedir):
    homedir = Path("..")

resources = join(homedir, "resources")
results = join(homedir, "results")

project_id = os.environ['PROJECT_ID']

model = GenerativeModel("gemini-1.5-pro-001")

vertexai.init(project=project_id, location="asia-south1")

ocr_rules = """
Follow the below rules while extracting text from the image:
1. Use `$` to enclose LaTeX formulas.
2. If equations are being referred with symbols or numbers, retain the symbols or numbers within the proof.
3. Do not use previously written fractions/expressions as references for upcoming steps for initial proof extraction. Interpret fractions/expressions at each step.
4. The generated proof will be used to CHECK the correctness of the original proof, so DO NOT make corrections or complete proofs, only clean up the language.
"""

def solution_from_image(image_path):
    response = model.generate_content([
          "Extract text with LaTeX from the following mathematics solution.",
          Part.from_uri(f"gs://leanaide/{image_path}", mime_type="image/png"),
          f"Also, rewrite the extracted text as a clean mathematical proof with full sentences, conjuctions etc. {ocr_rules}"])
    return response.text

def solution_from_images(image_paths):
    response = model.generate_content([
          "Extract text with LaTeX from the following mathematics solution."]+ 
          [Part.from_uri(f"gs://leanaide/{image_path}", mime_type="image/png") for image_path in image_paths] +
          [f"Also, rewrite the extracted text as a clean mathematical proof with full sentences, conjuctions etc. {ocr_rules}"])
    return response.text

proof_json = open(join(resources, "ProofJsonShorter.md")).read()

def structure_prompt(thm, pf):
    return f"{proof_json}\n---\n\n## Theorem: {thm}\n\n## Proof: {pf}\n"

def structure_prompt_with_knowns(thm, pf, knowns):
    return f"{proof_json}\n---\n\n## Theorem: {thm}\n\n## Proof: {pf}\n\n---\n\nThe following are known results that can be used without proof, even implicitly. DO NOT report the use of these results as errors or missing steps.\n\n## Known results: \n\n{knowns}\n"

def structured_proof(thm, pf):
    response = model.generate_content([
        structure_prompt(thm, pf)
    ])
    return extract_json_block(response.text)

def structured_proof_with_knowns(thm, pf, knowns):
    response = model.generate_content([
        structure_prompt_with_knowns(thm, pf, knowns)
    ])
    return extract_json_block(response.text)

def structured_proof_from_image(thm, path):
    pf = solution_from_image(path)
    return pf, structured_proof(thm, pf)

def structured_proof_from_images(thm, paths):
    pf = solution_from_images(paths)
    return pf, structured_proof(thm, pf)

def structured_proof_from_images_with_knowns(thm, paths, knowns):
    pf = solution_from_images(paths)
    return pf, structured_proof_with_knowns(thm, pf, knowns)

from google.cloud import storage

client = storage.Client()
bucket = client.bucket('leanaide')
def images_in_gs(prefix):
    blobs = client.list_blobs('leanaide', prefix=prefix)    
    return [blob.name for blob in blobs if blob.content_type == 'image/png']

def solutions_from_images(thm, prefix):
    image_paths = images_in_gs(prefix)
    triples = []
    for path in image_paths:
        pf, structured = structured_proof_from_image(thm, path)
        triples.append((path, pf, structured))
    return triples

import json
import pathlib

gemini_results = join(results, "gemini_results")
pathlib.Path(gemini_results).mkdir(parents=True, exist_ok=True)

def write_structured_proofs_simple(prefix):
    thm_blob = bucket.blob(f"{prefix}theorem.md")
    with thm_blob.open("r") as f:
        thm = f.read()
    triples = solutions_from_images(thm, prefix)
    for triple in triples:
        path, pf, structured = triple
        output_file = Path(join(gemini_results, path + "_sol.json"))
        output_file.parent.mkdir(exist_ok=True, parents=True)
        with open(output_file, "w") as f:
            json.dump(structured, f, ensure_ascii=False, indent=2)
        output_file = Path(join(gemini_results, path + "_sol.md"))
        output_file.parent.mkdir(exist_ok=True, parents=True)
        with open(output_file, "w") as f:
            f.write(f"## Theorem: {thm}\n\n## Proof: {pf}")

chat_client = ChatClient()
import itertools


def write_structured_proofs(prefix):
    thm_blob = bucket.blob(f"{prefix}theorem.md")
    with thm_blob.open("r") as f:
        thm = f.read()
    all_image_paths = images_in_gs(prefix)
    image_path_groups = [(key, list(group)) for key, group in itertools.groupby(all_image_paths, lambda s: s.split("_")[0])]
    for path, image_paths in image_path_groups:
        print(path, image_paths)
        pf, structured = structured_proof_from_images(thm, image_paths)
        output_file = Path(join(gemini_results, path + "_sol.json"))
        output_file.parent.mkdir(exist_ok=True, parents=True)
        with open(output_file, "w") as f:
            json.dump(structured, f, ensure_ascii=False, indent=2)
        prompt = structure_prompt(thm, pf)
        gpt_structured_raw = chat_client.math(prompt)
        gpt_structured = extract_json_block(gpt_structured_raw[0])
        output_file = Path(join(gemini_results, path + "_sol_gpt.json"))
        output_file.parent.mkdir(exist_ok=True, parents=True)
        with open(output_file, "w") as f:
            json.dump(gpt_structured, f, ensure_ascii=False, indent=2)
        output_file = Path(join(gemini_results, path + "_sol.md"))
        output_file.parent.mkdir(exist_ok=True, parents=True)
        with open(output_file, "w") as f:
            f.write(f"## Theorem: {thm}\n\n## Proof: {pf}")


def write_structured_proofs_with_knowns(prefix):
    thm_blob = bucket.blob(f"{prefix}theorem.md")
    with thm_blob.open("r") as f:
        thm = f.read()
    knowns_blob = bucket.blob(f"{prefix}knowns.md")
    with knowns_blob.open("r") as f:
        knowns = f.read()
    all_image_paths = images_in_gs(prefix)
    image_path_groups = [(key, list(group)) for key, group in itertools.groupby(all_image_paths, lambda s: s.split("_")[0])]
    for path, image_paths in image_path_groups:
        print(path, image_paths)
        pf, structured = structured_proof_from_images_with_knowns(thm, image_paths, knowns)
        output_file = Path(join(gemini_results, path + "_sol.json"))
        output_file.parent.mkdir(exist_ok=True, parents=True)
        with open(output_file, "w") as f:
            json.dump(structured, f, ensure_ascii=False, indent=2)
        prompt = structure_prompt_with_knowns(thm, pf, knowns)
        gpt_structured_raw = chat_client.math(prompt)
        gpt_structured = extract_json_block(gpt_structured_raw[0])
        output_file = Path(join(gemini_results, path + "_sol_gpt.json"))
        output_file.parent.mkdir(exist_ok=True, parents=True)
        with open(output_file, "w") as f:
            json.dump(gpt_structured, f, ensure_ascii=False, indent=2)
        output_file = Path(join(gemini_results, path + "_sol.md"))
        output_file.parent.mkdir(exist_ok=True, parents=True)
        with open(output_file, "w") as f:
            f.write(f"## Theorem: {thm}\n\n## Proof: {pf}")

def truly_missing(knowns, s):
    prompt = f"The following are known results that can be used without proof, even implicitly.  \n\n## Known results: \n\n{knowns}\n\n---\n\nThe following was reported as a missing step in a proof:\n {s}\n\nDoes this result follow from the above known results? Answer 'yes' or 'no'."
    response = chat_client.math(prompt)
    return response[0]
