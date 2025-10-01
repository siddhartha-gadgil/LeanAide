# Python code to run similarity search given query and numSim

import sys
import os
import json
import faiss
from sentence_transformers import SentenceTransformer

# Config the model and file paths
# MODEL = 'all-MiniLM-L6-v2' (moved over to server/api_server.py)
DESCFIELD_PATHS = {
    "docString" : "SimilaritySearch/docStrings/prompt_emb.json",
    "concise-description" : "SimilaritySearch/docStrings/concise_desc_emb.json",
    "description" : "SimilaritySearch/docStrings/desc_emb.json"
}
INDEX_PATHS = {
    "docString" : "SimilaritySearch/Indexes/docString_all-MiniLM-L6-v2.index",
    "concise-description" : "SimilaritySearch/Indexes/concise-description_all-MiniLM-L6-v2.index",
    "description" : "SimilaritySearch/Indexes/description_all-MiniLM-L6-v2.index"
}

def check_GPU():
  try:
      res = faiss.StandardGpuResources()
      index = faiss.GpuIndexFlatL2(res, 10)
      print("FAISS GPU index created successfully.")
  except Exception as e:
      print(f"Failed to create FAISS GPU index: {e}")

def load_data(file_path):
    with open(file_path, 'r', encoding='utf-8') as file:
        data = json.load(file)
    return data

# Creates new index
def create_index(index_path, data, model):
    # Extract the theorems out of full data
    theorems = [js["docString"] for js in data]  
    # Encode all theorems into vectors
    embeddings = model.encode(theorems)
    # Get the dimension of the embeddings
    d = embeddings.shape[1]
    # Build the FAISS index
    index = faiss.IndexFlatL2(d)
    # Add the theorem vectors to the index
    index.add(embeddings)
    # Save the index to INDEX_PATHS[descField]
    faiss.write_index(index, index_path)
    return index

def similarity_search(query, model, index, data, num):
    # Encode the query theorem into a vector
    query_vector = model.encode([query])
    # Search the FAISS index
    distances, indices = index.search(query_vector, num)
    output = []
    for i, idx in enumerate(indices[0]):
        js = data[idx]
        js["distance"] = float(distances[0][i])
        output.append(js)
    js_string = json.dumps(output)
    return js_string

def main(model, num, query = "mathematics", descField = "docString"):
    try: num = int(num)
    except: num = 10 # default value for num
    if descField not in ["docString", "concise-description", "description"]:
        descField = "docString" # default value for descField
    # Check if DESCFIELD_PATHS[descField] exists
    if not os.path.exists(DESCFIELD_PATHS[descField]):
        raise Exception(f"ERROR: docStrings NOT found at {DESCFIELD_PATHS[descField]}")
    # Get the full data from DESCFIELD_PATHS[descField]
    data = load_data(DESCFIELD_PATHS[descField])
    # Read index; create it if it doesn't exist
    if os.path.exists(INDEX_PATHS[descField]):
        index = faiss.read_index(INDEX_PATHS[descField])
    else:
        index = create_index(INDEX_PATHS[descField], data, model)
    # Run similarity search and print to standard output
    output = similarity_search(query, model, index, data, num)
    return output