import json
import os
import time
from multiprocessing import Process, Queue
import requests

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
    )
    time_capture["structured_json"] = elapsed_time

    structured_proof = json.loads(structured_proof)
    assert type(structured_proof) is dict, "Structured proof should be a dictionary. Obtained type: {}, str_proof obtained : {}".format(
        type(structured_proof), structured_proof  
    )

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
    dataset = load_benchmark_dataset()
    llm_provider = "openai"
    model = "gpt-4o"
    
    results = benchmark_dataset_to_output(dataset, llm_provider, model)
    
    # Save results to a file
    output_file = os.path.join(HOMEDIR, "benchmark", "output_results.json")
    with open(output_file, 'w') as f:
        json.dump(results, f, indent=4)
    
    print(f"Benchmark results saved to {output_file}")

