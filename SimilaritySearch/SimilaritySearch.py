# Python code to run similarity search given query and numSim

import sys
import os
import json
import faiss
import torch
from sentence_transformers import SentenceTransformer

# Config the model and file paths
MODEL = 'all-MiniLM-L6-v2' 
DESCFIELD_PATHS = {
    "docString" : "TestEmbeddings/UnpickledFiles/prompt_emb.jsonl",
    "concise-description" : "TestEmbeddings/UnpickledFiles/concise_desc_emb.jsonl"
    "description" : "TestEmbeddings/UnpickledFiles/desc_emb.jsonl"
}
INDEX_PATHS = {
    "docString" : "TestEmbeddings/FAISSIndex/docString_all-MiniLM-L6-v2.index",
    "concise-description" : "TestEmbeddings/FAISSIndex/concise-description_all-MiniLM-L6-v2.index"
    "description" : "TestEmbeddings/FAISSIndex/description_all-MiniLM-L6-v2.index"
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
        data = [json.loads(line) for line in file]
    return data

def load_model():
    model = SentenceTransformer(MODEL, model_kwargs={"dtype": "float16"})
    return model

# Creates new index
def create_index(INDEX_PATHS[descField], data, model):
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
    faiss.write_index(index, INDEX_PATHS[descField])
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
    js_string = json.dumps(js)
    print(js_string)

def main(args):
    # Get the args
    try: query = args[0]
    except: query = "mathematics" #default value for query
    try: num = int(args[1])
    except: num = 10 # default value for num
    try: descField = args[2]
    except: descField = "docString" # default value for descField
    if descField not in ["docString", "concise-description", "description"] :
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
    # Load the model
    model = load_model()
    # Run similarity search and print to standard output
    similarity_search(query, model, index, data, num)

if __name__ == "__main__":
    main(sys.argv[1:])