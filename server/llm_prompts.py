# File just contains the prompts used in the application.
from serv_utils import SCHEMA_JSON

ocr_rules = """
Follow the below rules while extracting text from the image:
1. Use `$` to enclose LaTeX formulas.
2. If equations are being referred with symbols or numbers, retain the symbols or numbers within the proof.
3. Do not use previously written fractions/expressions as references for upcoming steps for initial proof extraction. Interpret fractions/expressions at each step.
4. The generated proof will be used to CHECK the correctness of the original proof, so DO NOT make corrections, add unmentioned reasonings complete proofs, only clean up the language.
"""

def mathpaper_prompt(paper_text: str, pdf_input: bool = False):
    if pdf_input:
        non_pdf_suffix = ""
    else:
        non_pdf_suffix = f"\n\nThe paper content is:{paper_text}"
    return {
        "prompt": f"Write the attached mathematics paper as a structured JSON file in the given JSON schema format. Use LaTeX for formulas but otherwise use markdown.{non_pdf_suffix}.\n. The schema is: {str(SCHEMA_JSON)}.",
        "task": "You are an assistant that converts academic papers into structured JSON. Strictly follow the JSON schema."
    }

def thmpf_prompt(thm, pf):
    return f"The following is a custom JSON schema, which we call `PaperStructure.json`, for mathematical documents which structures theorem-proofs. Your task is to write the theorem and proof STRICTLY in the schema provided to you. Break down the proof as much as possible according to the schema.\n\nThe theorem and proof are as follows:\n\n## Theorem:\n {thm}\n\n## Proof:\n {pf}\n. The schema is: {str(SCHEMA_JSON)}."

soln_from_image_prompt = f"You are proficient in extracting Mathematical text from images. Your task is to rewrite the extracted text as a clean mathematical proof with full sentences, conjuctions etc. \n {ocr_rules}"