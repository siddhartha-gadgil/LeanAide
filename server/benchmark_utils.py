import json
import os
import time
from multiprocessing import Process, Queue
import requests

from logging_utils import load_env
load_env()  # Load environment variables if needed
from serv_utils import HOMEDIR
from llm_prompts import proof_guidelines_prompt, proof_thm_task_eng, raw_llm_prompt
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

def result_time_capture(func, *args, timeout: float = 300.0, **kwargs):
    """Helper function to time any function call and return result with time.
       If timeout is reached, returns None and logs the timeout.
       
    Args:
        func: Function to execute
        *args: Positional arguments for func
        timeout: Maximum seconds to wait (default: 300)
        **kwargs: Keyword arguments for func
        
    Returns:
        tuple: (result, elapsed_time) or (None, elapsed_time) if timeout/error
    """
    # Validate timeout
    if not isinstance(timeout, (int, float)):
        raise TypeError(f"timeout must be numeric, got {type(timeout)}")
    
    start_time = time.time()
    queue = Queue()
    p = Process(target=_worker, args=(func, args, kwargs, queue))
    p.start()
    
    try:
        # Wait with timeout
        p.join(timeout=timeout)
        
        if p.is_alive():
            p.terminate()
            p.join()
            raise TimeoutError(f"Function timed out after {timeout} seconds")
            
        # Get result from queue
        result, error = queue.get(timeout=1)  # Small timeout for queue safety
        if error:
            raise error
            
    except Exception as e:
        end_time = time.time()
        print(f"Error: {str(e)}")
        return None, end_time - start_time
        
    finally:
        # Ensure process is terminated
        if p.is_alive():
            p.terminate()
            p.join()
    
    end_time = time.time()
    return result, end_time - start_time

def _worker(func, args, kwargs, queue):
    """Worker function for Process"""
    try:
        result = func(*args, **kwargs)
        queue.put((result, None))
    except Exception as e:
        queue.put((None, e))

def leanaide_io(input_data: dict, llm_provider: str, model: str) -> dict:
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
        thm = theorem,
        pf=proof,
        provider=llm_provider,
        model=model
    ) # structured proof is a JSON string because of json.dumps
    time_capture["structured_json"] = elapsed_time

    ## Step 4: Get Lean Code
    request_payload = {
        "tasks": ["lean_from_json_structured"],
        "json_structured": json.loads(structured_proof)
    }

    result, elapsed_time = result_time_capture(request_server_benchmark, request_payload)
    if not result:
        result = {"lean_code": "sorry", "elapsed_time": elapsed_time}
    print("\n**RESULT**\n{}\n".format(result))
    lean_code = result.get("lean_code", "sorry")
    time_capture["lean_code"] = elapsed_time
     
    return {
        "theorem": theorem,
        # "proof": proof,
        "lean_code": lean_code,
        # "structured_proof": structured_proof,
        "time_taken": round(float(sum(time_capture.values())), 4),
    }

def benchmark_dataset_to_output(dataset: dict, llm_provider: str, model: str) -> list:
    """
    Convert a list of input data (theorems and proofs) to output Lean Code.
    """
    results = []
    for key, input_data in dataset.items():
        result = leanaide_io(input_data=input_data, llm_provider=llm_provider, model=model)
        result["id"] = key  # Add the key as an identifier
        results.append(result)
    return results

def llm_raw_io(input_data: dict, llm_provider: str, model: str) -> dict:
    """
    Convert input theorem and proof to raw LLM output.
    """
    theorem = input_data.get("theorem", "")
    proof = input_data.get("proof", "")
    if not theorem or not proof:
        return {"error": "Theorem or proof is missing in the input data."}
    
    try:
        # output, elapsed_time = result_time_capture(
        #     model_response_gen,
        #     prompt=raw_llm_prompt(thm=theorem, pf=proof)["prompt"],
        #     task=raw_llm_prompt(thm=theorem, pf=proof)["task"],
        #     provider=llm_provider,
        #     model=model
        # )
        output, elapsed_time = "```lean\n#eval 1+1\n```", 0.1  # Placeholder for actual LLM output
    except Exception as e:
        return {"error": f"Error in LLM response generation: {str(e)}"}
    
    lean_code = "sorry"
    if output:
        lean_code = output.strip("```lean\n").strip("```")
    else:
        lean_code += "\n -- No output generated by the LLM"
    
    return {
        "lean_code": lean_code,
        "time_taken": elapsed_time,
        "structured_proof": {}
    }

if __name__ == "__main__":
    # Example usage
    input_data = {
        "theorem": "The determinant of a 2x2 Identity Matrix is 1",
        "proof": "To prove that the determinant of a 2x2 identity matrix is 1, let's first define the 2 × 2 identity matrix:\n\nI_2 = [[1, 0], [0, 1]]\n\nThe determinant of a 2 × 2 matrix A = [[a, b], [c, d]] is given by the formula:\n\ndet(A) = ad - bc\n\nApplying this formula to the identity matrix I_2, we have:\n\ndet(I_2) = (1)(1) - (0)(0) = 1 - 0 = 1\n\nTherefore, the determinant of the 2 × 2 identity matrix is indeed 1."
    }
    result = leanaide_io(input_data, llm_provider="openai", model="gpt-4o")
    print("Result:", result)

    print("LEAN CODE:\n", result.get("lean_code", "No Lean code generated"))