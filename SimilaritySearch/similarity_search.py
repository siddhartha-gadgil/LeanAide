# Python code to run similarity search given query and numSim

import sys
import os
import requests
import json
import faiss
import numpy as np
from sentence_transformers import SentenceTransformer

# Config the file paths
DATA_FOLDER = "SimilaritySearch/Data"
INDEX_FOLDER = "SimilaritySearch/Indexes"

docString_url = "https://storage.googleapis.com/leanaide_data/mathlib4-prompts.jsonl"

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

# Adjust the batch size according to your memory
BATCH_SIZE = 4000

DIM = 768 # If changed, add `truncate_dim = DIM` to all model.encode functions

def check_GPU():
  try:
      res = faiss.StandardGpuResources()
      index = faiss.GpuIndexFlatL2(res, 10)
      print("FAISS GPU index created!")
  except Exception as e:
      print(f"Failed to create FAISS GPU index: {e}")

# SECTION: CREATE INDEXES

def check_paths(model_name):
    os.makedirs(DATA_FOLDER, exist_ok=True)
    os.makedirs(INDEX_FOLDER, exist_ok=True)
    os.makedirs(MODEL_INDEXES_FOLDER(model_name), exist_ok=True)

def download_file(url, filename):
    try:
        # Send a GET request to the URL.
        with requests.get(url, stream=True) as response:
            if response.status_code == 200:
                # Open the local file in binary write mode
                with open(filename, 'wb') as f:
                    for chunk in response.iter_content(chunk_size=8192):
                        f.write(chunk)
                print(f"File downloaded and saved at {filename}\n")
            else:
                # Print an error message if the download failed
                print(f"Error: Failed to download file. HTTP Status Code: {response.status_code}\n")

    except requests.exceptions.RequestException as e:
        print(f"An error occurred: {e}\n")
    except IOError as e:
        print(f"Error writing to file: {e}\n")

def check_data():
    if not os.path.exists(DESCFIELD_PATHS("docString")):
        print(f"Fetching docStrings from {docString_url}...")
        download_file(docString_url, DESCFIELD_PATHS("docString"))

def batch_generator(descField, batch_size):
    batch, ids = [], []
    with open(DESCFIELD_PATHS(descField), "r", encoding="utf-8") as file:
        for line_num, line in enumerate(file):
            data = json.loads(line)
            text = data[FIELD_NAME[descField]]
            batch.append(text)
            # The ids are the line numbers
            ids.append(np.int64(line_num))
            # Return a batch of batch_size with the ids
            if len(batch) == batch_size:
                yield (batch, np.array(ids))
                # Reset the batch and ids
                batch, ids = [], []
    # For the last remaining sentences that didn't form a complete batch 
    if batch: yield (batch, np.array(ids))

def create_index(descField, model, model_name):
    # Create an empty FAISS index with dimension DIM
    base_index = faiss.IndexFlatL2(DIM)
    # Make it an IDMap index
    index = faiss.IndexIDMap(base_index)
    # Get the batch generator
    data_batches = batch_generator(descField, BATCH_SIZE)
    # Loop over the batches and ids
    for batch, ids in data_batches:
        # Embed the batch
        embeddings = model.encode(batch, normalize_embeddings=True, show_progress_bar=True, convert_to_numpy=True)
        # Add it to the index
        index.add_with_ids(embeddings, ids)
        # Print progress
        print(f"- docstrings encoded: {ids[-1] + 1}")
    # Save the index to INDEX_PATHS(descField, model_name)
    faiss.write_index(index, INDEX_PATHS(descField, model_name))

def check_and_create_indexes(model, model_name):
    for descField in ["concise-description", "description", "docString"]:
        if not os.path.exists(INDEX_PATHS(descField, model_name)):
            print(f"Creating index for {descField} with {model_name}...")
            create_index(descField, model, model_name)
            print(f"Index created and saved at {INDEX_PATHS(descField, model_name)}\n")
        else:
            print(f"Found index for {descField} from {model_name}")
    print("\n")

def run_checks(model, model_name):
    check_paths(model_name)
    check_data()
    check_and_create_indexes(model, model_name)

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
    return js_string