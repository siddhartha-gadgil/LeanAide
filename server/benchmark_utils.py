import json
import os
import time
import requests

from serv_utils import HOMEDIR
from llm_prompts import proof_guidelines_prompt, proof_thm_task_eng
from llm_response import model_response_gen, gen_thmpf_json
from api_server import HOST, PORT

BENCHMARK_PATH = os.path.join(HOMEDIR, "benchmark", "BenchMark_LeanAide.json")

def load_benchmark_dataset(file_path: str = BENCHMARK_PATH) -> dict:
    with open(file_path, 'r') as f:
        dataset = json.load(f)
    return dataset

def request_server_benchmark(request_payload: dict):
    response = requests.post(
            f"http://{HOST}:{PORT}", json=request_payload
    )
    if response.status_code == 200:
        response_data = response.json()
    else:
        response_data = {}
    return response_data

def result_time_capture(func, *args, **kwargs):
    """Helper function to time any function call and return result with time."""
    start_time = time.time()
    try:
        result = func(*args, **kwargs)
    except Exception as e:
        result = {}
        print(f"Error in function call: {e}")
    end_time = time.time()
    return result, end_time - start_time

def input_to_output(input_data: dict, llm_provider: str, model: str) -> dict:
    """
    Convert input theorem and proof to output Lean Code.
    """
    time_capture = {}
    theorem = input_data.get("theorem", "")
    proof = input_data.get("proof", "")
    if not theorem or not proof:
        return {"error": "Theorem or proof is missing in the input data."}
    
    ## Step 1: Request server for theorem details
    request_payload = {
        "tasks": ["translate_thm_detailed"],
        "text": theorem
    }
 
    thm_details, elapsed_time = result_time_capture(request_server_benchmark, request_payload)
    time_capture["thm_details"] = elapsed_time
 
    ## Step 2:  Rewrite the proof/generate if not provided
    prompt_guide_thm = proof_guidelines_prompt(thm = theorem, details= thm_details)
    rewrite_pf = True if proof else False
    prompt_proof_task = proof_thm_task_eng(pf=proof, rewrite =rewrite_pf)

    proof, elapsed_time = result_time_capture(
        model_response_gen,
        prompt=prompt_guide_thm,
        task=prompt_proof_task,
        provider=llm_provider,
        model=model
    )
    time_capture["genai_proof"] = elapsed_time

    ## Step 3: Get Structured JSON
    structured_proof, elapsed_time = result_time_capture(
        gen_thmpf_json,
        theorem=theorem,
        proof=proof,
        provider=llm_provider,
        model=model
    )
    time_capture["structured_json"] = elapsed_time

    assert type(structured_proof) is dict, "Structured proof should be a dictionary. Obtained type: {}".format(type(structured_proof))

    ## Step 4: Get Lean Code
    request_payload = {
        "tasks": ["lean_from_json_structured"],
        "json_structured": structured_proof
    }

    result, elapsed_time = result_time_capture(request_server_benchmark, request_payload)
    lean_code = result.get("lean_code", "")
    time_capture["lean_code"] = elapsed_time
     
    return {
        "theorem": theorem,
        "proof": proof,
        "lean_code": lean_code,
        "structured_proof": structured_proof,
        "time_capture": time_capture
    }

def benchmark_dataset_to_output(dataset: dict, llm_provider: str, model: str) -> list:
    """
    Convert a list of input data (theorems and proofs) to output Lean Code.
    """
    results = []
    for key, input_data in dataset.items():
        result = input_to_output(input_data=input_data, llm_provider=llm_provider, model=model)
        result["id"] = key  # Add the key as an identifier
        results.append(result)
    return results

if __name__ == "__main__":
    # Example usage
    dataset = load_benchmark_dataset()
    llm_provider = "openai"
    model = "gpt-4o"
    
    results = benchmark_dataset_to_output(dataset, llm_provider, model)
    
    # Save results to a file
    output_file = os.path.join(HOMEDIR, "benchmark", "output_results.json")
    with open(output_file, 'w') as f:
        json.dump(results, f, indent=4)
    
    print(f"Benchmark results saved to {output_file}")

