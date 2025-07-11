# File just contains the prompts used in the application.
from serv_utils import SCHEMA_JSON, HOMEDIR
import os

ocr_rules = """
Follow the below rules while extracting text from the image:
1. Use `$` to enclose LaTeX formulas.
2. If equations are being referred with symbols or numbers, retain the symbols or numbers within the proof.
3. Do not use previously written fractions/expressions as references for upcoming steps for initial proof extraction. Interpret fractions/expressions at each step.
4. The generated proof will be used to CHECK the correctness of the original proof, so DO NOT make corrections, add unmentioned reasonings complete proofs, only clean up the language.
"""

def mathpaper_prompt(paper_text: str, pdf_input: bool = False):
    return {
        "prompt": f"The following is a JSON schema for representing mathematical documents ranging from theorems with proofs to papers:\n\n```json\n${SCHEMA_JSON}\n\n.Write the following document in the above schema.\n\n---\n${paper_text}\n---\n\nOutput ONLY the JSON document in the above schema.\n",
        "task": "You are an assistant that converts academic papers into structured JSON. Strictly follow the JSON schema."
    }

def thmpf_prompt(thm, pf):
    return f"The following is a JSON schema for representing mathematical documents ranging from theorems with proofs to papers:\n\njson\n${SCHEMA_JSON}\n\n.Write the following document in the above schema.\n\n---\nTheorem: ${thm}\n\n---\nProof: ${pf}\n---\n\nOutput ONLY the JSON document in the above schema.\n"

def thmpf_reprompt(thm, pf, output, error_msg):
    return f"An incorrect JSON document was received for the following JSON schema for representing mathematical documents ranging from theorems with proofs to papers:\n\njson\n${SCHEMA_JSON}\n\n.The mathematical document is given below.\n\n---\nTheorem: ${thm}\n\n---\nProof: ${pf}\n---\n\nThe incorrect JSON document received is given below.\n\njson\n${output}\n\n The JSON document above does NOT validate with the JSON Schema and results in the following error:\n\nError\n${error_msg}\n\nPlease correct the JSON document so that it validates correctly with the JSON Schema. Output ONLY the complete corrected JSON document.\n"

def soln_from_image_prompt(image_text: str = ""):
    return f"You are proficient in extracting Mathematical text from images. Your task is to rewrite the extracted text as a clean mathematical proof with full sentences, conjuctions etc. \n {ocr_rules}. The extracted text is:\n\n{image_text}. Do not write any extra explanations. Avoid unnecessary causal sentences."

def proof_guidelines_prompt(thm: str, details: dict = {}):
    prompt_proof_guide_path = os.path.join(HOMEDIR, "resources", "ProofGuidelines.md")
    proof_guidelines = open(prompt_proof_guide_path, "r", encoding="utf-8").read()

    if details:
        statement = details.get("statement", "")
        definitions = details.get("definitions_used", "")
        name = details.get("name", "")
    else:
        statement = "sorry"
        definitions = ""
        name = "sorry"

    return f"Your goal is to give a **natural language** proof of a theorem so that the proof can be further processed to generate Lean Code. To facilitate formalisation, follow the following guidelines:\n\n{proof_guidelines}.\n\nThe theorem you need to prove is the following:\n\nTheorem: {thm}\n\n The statement of the theorem (with proof given as sorry) in Lean and some definitions in Lean4 that are involved in the statement of the theorem are below.\n\nLean Theorem:/-- ${name}$--/\n\nStatements:{statement}\n\nDefinitions used:{definitions}\n\n\nGive a proof of the theorem in **natural language** following the **guidelines** and using definitions as in Lean (as given above). The proof can use markdown, which may contain LaTeX mathematics (enclosed in $ signs) and unicode characters for mathematics but **should not contain Lean Code**."

def proof_thm_task_eng(pf: str = "", rewrite: bool = False):
    rewrite_proof = f"Rewrite the following proof:\n\n{pf}\n\n" if rewrite else ""
    return f"""
You are a mathematics assistant for research mathematicians and advanced students who also helps with computer-assisted mathematics. Answer mathematical questions with the level of precision and detail expected in graduate level mathematics courses and in mathematics research papers. Be concise and give only what is asked for, avoiding phrases like 'Here is the proof'. Some of your output is designed to be used as input to programs, so give answers to questions as best as you can in the form requested. Do not explain the process by which the answer can be obtained instead of giving the answer.
{rewrite_proof}
Follow these instructions strictly:
1.  Write the entire proof in formal English following the given Guidelines.
2.  Use LaTeX for all mathematical formulas and expressions, enclosing them in `$`.
3.  Provide step-by-step reasoning using English sentences. Do not use Lean code or any other programming language for justifications.
4.  Do not include any conversational text, introductory phrases, or concluding summaries. Output only the human understandable proof itself.
"""

def proof_thm_task_lean(pf: str = "", rewrite: bool = False):
    rewrite_proof = f"Rewrite the following proof:\n\n{pf}\n\n" if rewrite else ""
    return f"""
You are a mathematics assistant for research mathematicians and advanced students who also helps with computer-assisted mathematics. Answer mathematical questions with the level of precision and detail expected in graduate level mathematics courses and in mathematics research papers. Be concise and give only what is asked for, avoiding phrases like 'Here is the proof'. Some of your output is designed to be used as input to programs, so give answers to questions as best as you can in the form requested. Do not explain the process by which the answer can be obtained instead of giving the answer.
{rewrite_proof}
Write a proof in English. You may use Lean syntax and tactics within sentences for precision, but the proof must be comprehensible to a human reader.

Follow these rules:
1.  The proof must be a narrative in formal English, not a block of Lean code.
2.  Integrate Lean syntax to clarify reasoning (e.g., "we `apply` lemma `X`", "from `h` we have...").
3.  Do not include conversational text, introductions, or summaries. Output only the proof.
"""

def raw_llm_prompt(thm: str, pf: str = ""):
    task = "You are a mathematics assistant for research mathematicians and advanced students who also helps with computer-assisted mathematics. You are tasked to write the given theorem and proof in Lean4."
    prompt = f"""Write the following theorem and proof in Lean4. You have to write the lean code output within Lean Code block.
For example: Your output will JUST be the following:
```lean
theorem my_theorem : ∀ x, x + 0 = x := by
    intros x
    rw [add_zero]
```
    
The given theorem is :\n\n{thm}\n\nThe proof:\n\n{pf}.
"""
    return {
        "prompt": prompt,
        "task": task
    }