# Translates multiple theorems in a file and writes the responses in a lean file

import requests
import json
import time

url = "http://localhost:7654"

silly_inpath = "data/silly-prompts.txt"
false_inpath = "data/false-prompts.txt"
thm_inpath = "data/thm-prompts.txt"

silly_outpath = "SimilaritySearch/RunTests/TestResults/silly-prompts-768gemma.lean"
false_outpath = "SimilaritySearch/RunTests/TestResults/false-prompts-768gemma.lean"
thm_outpath = "SimilaritySearch/RunTests/TestResults/thm-prompts-768gemma.lean"

def translate(n, thm, outfilepath):
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
                file.write(f"--Time: {e - s:.2f} s\n")
                file.write(f"/--{thm_text}-/\n")
                file.write(f"theorem t{n} : {thm_code} :=\n")
                file.write("  by sorry\n\n")
        except:
            print(f"ERROR! Response text: {response.text}")
            print(f"Response: {response}")
    else:
        print(f"Request failed with status code {response.status_code}")
        print("Response text:", response.text)

def translate_multiple(infilepath, outfilepath):
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
        translate(n, thm, outfilepath)
        print(f"{n}/{l} translated")
        n += 1
    end = time.time()
    print(f"Time to translate {l} statements: {end - start:.2f} s")
    print(f"Avg time per statement: {(end - start)/l:.2f} s")


if __name__ == "__main__":
    # translate(1, "infinite primes", thm_outpath)
    translate_multiple(false_inpath, false_outpath)