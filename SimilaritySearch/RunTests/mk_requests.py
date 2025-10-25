# Translates multiple theorems in a file and writes the responses in a lean file

import requests
import json
import time

url = "http://localhost:7654"

silly_inpath = "data/silly-prompts.txt"
false_inpath = "data/false-prompts.txt"
thm_inpath = "data/thm-prompts.txt"

silly_outpath = "SimilaritySearch/RunTests/TestResults/silly-2-bge.lean"
false_outpath = "SimilaritySearch/RunTests/TestResults/false-2-bge.lean"
thm_outpath = "SimilaritySearch/RunTests/TestResults/thm-2-bge.lean"

def mk_request(thm):
    # Set the payload for the request.
    payload = {
        "task": "translate_thm",
        "theorem_text": thm,
    }
    # Set the headers for the request.
    headers = {
        "Content-Type": "application/json"
    }
    # Make the request
    s = time.time()
    response = requests.post(url, headers=headers, data=json.dumps(payload))
    e = time.time()
    return response, (e-s)

def translate_and_print(thm):
    response, t = mk_request(thm)
    # Check response
    if response.ok:
        try:
            print(f"TEXT: {response.text}")
            resp = response.json()
            print(f"JSON: {resp}")
        except:
            print(f"ERROR! Response text: {response.text}")
    else:
        print(f"Request failed with status code {response.status_code}")
        print("Response text:", response.text)

def translate_and_write(n, thm, outfilepath):
    response, t = mk_request(thm)
    # Check response
    if response.ok:
        try:
            resp = response.json()
            thm_text = resp["theorem_text"]
            result = resp["result"]
            try: thm_code = resp["theorem_code"]
            except: 
                try: thm_code = resp["theorem"]
                except: thm_code = "None"
            with open(outfilepath, "a", encoding="utf-8") as file:
                file.write(f"--Result: {result}\n")
                file.write(f"--Time: {t:.2f} s\n")
                file.write(f"/--{thm_text}-/\n")
                file.write(f"theorem t{n} : {thm_code} :=\n")
                file.write("  by sorry\n\n")
        except:
            print(f"ERROR! Response text: {response.text}")
            print(f"Response: {response}")
    else:
        print(f"Request failed with status code {response.status_code}")
        print("Response text:", response.text)

def translate_multiple_and_write(infilepath, outfilepath):
    # Extract all the theorems in the file
    thms = []
    with open(infilepath, "r", encoding="utf-8") as file:
        for line in file:
            thms.append(line.strip())
    # Make translate request for each theorem
    n = 1
    l = len(thms)
    start = time.time()
    for thm in thms:
        translate_and_write(n, thm, outfilepath)
        print(f"{n}/{l} translated")
        n += 1
    end = time.time()
    print(f"Time to translate {l} statements: {end - start:.2f} s")
    print(f"Avg time per statement: {(end - start)/l:.2f} s")

if __name__ == "__main__":
    translate_multiple_and_write(false_inpath, false_outpath)
    # translate_and_print("There are infinite prime numbers.")