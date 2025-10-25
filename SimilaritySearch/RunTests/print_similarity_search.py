# View the closest embeddings obtained from similarity search

import sys
import os
import json
import faiss
import numpy as np
from sentence_transformers import SentenceTransformer

# Config the file paths
DATA_FOLDER = "SimilaritySearch/Data"
INDEX_FOLDER = "SimilaritySearch/Indexes"

def MODEL_INDEXES_FOLDER(model_name):
    return f"{INDEX_FOLDER}/{model_name}"

def DESCFIELD_PATHS(descField):
    if descField == "docString":
        return f"{DATA_FOLDER}/mathlib4-prompts.jsonl"
    elif descField == "concise-description":
        return "resources/mathlib4-descs.jsonl"
    elif descField == "description":
        return "resources/mathlib4-descs.jsonl"
    else:
        raise Exception("Incorrect descField!")

def INDEX_PATHS(descField, model_name):
    if descField == "docString":
        return f"{MODEL_INDEXES_FOLDER(model_name)}/docString.index"
    elif descField == "concise-description":
        return f"{MODEL_INDEXES_FOLDER(model_name)}/concise-description.index"
    elif descField == "description":
        return f"{MODEL_INDEXES_FOLDER(model_name)}/description.index"
    else:
        raise Exception("Incorrect descField!")

FIELD_NAME = {
    "docString" : "doc",
    "concise-description" : "concise-description",
    "description" : "description"
}

DIM = 768 # If changed, add `truncate_dim = DIM` to all model.encode functions

def check_GPU():
  try:
      res = faiss.StandardGpuResources()
      index = faiss.GpuIndexFlatL2(res, 10)
      print("FAISS GPU index created!")
  except Exception as e:
      print(f"Failed to create FAISS GPU index: {e}")

# SECTION: SIMILARITY_SEARCH

def get_data(descField, idx):
    with open(DESCFIELD_PATHS(descField), "r", encoding="utf-8") as file:
        for line_num, line in enumerate(file):
            # index idx corresponds to line_num
            if line_num == idx:
                data = json.loads(line)
                return data
    return None

def modify_js(js, descField, distance):
    # Add distance field
    js["distance"] = float(distance)
    # Get FIELD_NAME[descField] value
    temp = js[FIELD_NAME[descField]]
    # Delete "docString" (in case of description and concise-description files) and FIELD_NAME[descField]
    if "docString" in js: del js["docString"]
    if FIELD_NAME[descField] in js: del js[FIELD_NAME[descField]]
    # Essentially, rename FIELD_NAME[descField] to "docString"
    js["docString"] = temp
    return js

def similarity_search(query, model, index, descField, num):
    # Encode the query theorem into a vector
    query_vector = model.encode([query], normalize_embeddings=True, convert_to_numpy=True)
    # Search the FAISS index
    distances, indices = index.search(query_vector, num)
    output = []
    for i, idx in enumerate(indices[0]):
        # Get the data on line (idx + 1)
        js = get_data(descField, idx)
        # Modify js
        js = modify_js(js, descField, distances[0][i])
        output.append(js)
    js_string = json.dumps(output)
    return js_string

def run_similarity_search(model, model_name, num, query = "mathematics", descField = "docString"):
    try: num = int(num)
    except: num = 10 # default value for num
    if descField not in ["docString", "concise-description", "description"]:
        descField = "docString" # default value for descField
    # Check if DESCFIELD_PATHS(descField) exists
    if not os.path.exists(DESCFIELD_PATHS(descField)):
        raise Exception(f"ERROR: docStrings NOT found at {DESCFIELD_PATHS(descField)}")
    # Read index (it should exist if the server was started, as create_indexes.py would be run)
    try: index = faiss.read_index(INDEX_PATHS(descField, model_name))
    except : raise Exception("Index not found! Please create the indexes (should be automatically created when the server starts).")
    # Run similarity search and print to standard output
    js_string = similarity_search(query, model, index, descField, num)
    print(js_string)

if __name__ == "__main__":
    MODEL_NAME = "BAAI/bge-base-en-v1.5"

    device = torch.device('cuda') if torch.cuda.is_available() else torch.device('cpu')
    print(f"Using device: {device}")
    print(f"Loading model {MODEL_NAME}...")
    MODEL = SentenceTransformer(MODEL_NAME, device=device, model_kwargs={"dtype": torch.bfloat16})
    print("Model loaded!")

    MODEL_NAME = MODEL_NAME.replace('/','-')

    # Enter your query here
    query = "There are infinite primes."
    descField = "docString"

    run_similarity_search(MODEL, MODEL_NAME, 10, query, descField)