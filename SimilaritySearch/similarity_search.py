# Python code to run similarity search given query and numSim

import sys
import os
import json
import faiss
import numpy as np
from sentence_transformers import SentenceTransformer

# Config the file paths
DESCFIELD_PATHS = {
    "docString" : "resources/mathlib4-prompts.jsonl",
    "concise-description" : "resources/mathlib4-descs.jsonl",
    "description" : "resources/mathlib4-descs.jsonl"
}
INDEX_PATHS = {
    "docString" : "SimilaritySearch/Indexes/docString_embeddinggemma-300m-768dim.index",
    "concise-description" : "SimilaritySearch/Indexes/concise-description_embeddinggemma-300m-768dim.index",
    "description" : "SimilaritySearch/Indexes/description_embeddinggemma-300m-768dim.index"
}
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

def batch_generator(descField, batch_size):
    batch, ids = [], []
    with open(DESCFIELD_PATHS[descField], "r", encoding="utf-8") as file:
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

def create_index(descField, model):
    # Create an empty FAISS index with dimension DIM
    base_index = faiss.IndexFlatL2(DIM)
    # Make it an IDMap index
    index = faiss.IndexIDMap(base_index)
    # Get the batch generator
    data_batches = batch_generator(descField, BATCH_SIZE)
    # Loop over the batches and ids
    for batch, ids in data_batches:
        # Embed the batch
        embeddings = model.encode(batch, show_progress_bar = True, convert_to_numpy = True)
        # Add it to the index
        index.add_with_ids(embeddings, ids)
        # Print progress
        print(f"- docstrings encoded: {ids[-1] + 1}")
    # Save the index to INDEX_PATHS[descField]
    faiss.write_index(index, INDEX_PATHS[descField])

def run_create_indexes(model):
    print("Checking indexes...")
    for descField in ["concise-description", "description", "docString"]:
        if not os.path.exists(INDEX_PATHS[descField]):
            print(f"Creating index for {descField}...")
            create_index(descField, model)
            print(f"Index created and saved at {INDEX_PATHS[descField]}")
        else:
            print(f"Found index for {descField}")

# SECTION: SIMILARITY_SEARCH

def get_data(descField, idx):
    with open(DESCFIELD_PATHS[descField], "r", encoding="utf-8") as file:
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
    query_vector = model.encode([query])
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

def run_similarity_search(model, num, query = "mathematics", descField = "docString"):
    try: num = int(num)
    except: num = 10 # default value for num
    if descField not in ["docString", "concise-description", "description"]:
        descField = "docString" # default value for descField
    # Check if DESCFIELD_PATHS[descField] exists
    if not os.path.exists(DESCFIELD_PATHS[descField]):
        raise Exception(f"ERROR: docStrings NOT found at {DESCFIELD_PATHS[descField]}")
    # Read index (it should exist if the server was started, as create_indexes.py would be run)
    try: index = faiss.read_index(INDEX_PATHS[descField])
    except : raise Exception("Index not found! Please create the indexes (should be automatically created when the server starts).")
    # Run similarity search and print to standard output
    js_string = similarity_search(query, model, index, descField, num)
    return js_string