# Python code to run similarity search given query and numSim

import sys
import os
import json
import faiss
import torch
from sentence_transformers import SentenceTransformer

# Config
MODEL = 'all-MiniLM-L6-v2' 
DATA_FILE = 'TestEmbeddings/UnpickledFiles/prompt_emb.jsonl'
INDEX_FILE = 'TestEmbeddings/FAISSIndex/theorems_all-MiniLM-L6-v2.index'

def check_GPU():
  try:
      res = faiss.StandardGpuResources()
      index = faiss.GpuIndexFlatL2(res, 10)
      print("FAISS GPU index created successfully.")
  except Exception as e:
      print(f"Failed to create FAISS GPU index: {e}")

def load_data(file_path):
    with open(file_path, 'r', encoding='utf-8') as file:
        # Try to rewrite this as single list comprehension
        data = [json.loads(line) for line in file]
    return data

# Creates new index
def create_index(index_file, data, model):
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
    # Save the index to index_file
    faiss.write_index(index, index_file)
    return index

def similarity_search(query, model, index, data, num):
    # Encode the query theorem into a vector
    query_vector = model.encode([query])
    # Search the FAISS index
    distances, indices = index.search(query_vector, num)
    output = []
    for i, idx in enumerate(indices[0]):
        js = data[idx]
        js["distance"] = distances[0][i]
        output.append(js)
    return output

def main(args):
    # Get the args
    query = args[0]
    try: num = int(args[1])
    except: num = 10 # default value for num
    # Check if DATA_FILE exists
    if not os.path.exists(DATA_FILE):
        raise Exception(f"ERROR: docStrings NOT found at {DATA_FILE}")
    # Get the full data from DATA_FILE
    data = load_data(DATA_FILE)
    print("Data loaded!")
    # Set device to "cuda" if available; "cpu" otherwise
    device = "cuda" if torch.cuda.is_available() else "cpu"
    model = SentenceTransformer(MODEL, device=device)
    # Read index; create it if it doesn't exist
    if os.path.exists(INDEX_FILE):
        index = faiss.read_index(INDEX_FILE)
        print("Index read!")
    else:
        index = create_index(INDEX_FILE, data, model)
        print("Index created!")
    # Run similarity search and print to standard output
    print("Running similarity search!")
    print(similarity_search(query, model, index, data, num))

if __name__ == "__main__":
    main(sys.argv[1:])