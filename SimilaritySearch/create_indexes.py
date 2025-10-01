import os
import json
import faiss

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

def load_data(file_path):
    with open(file_path, 'r', encoding='utf-8') as file:
        data = json.load(file)
    return data

def create_index(index_path, data, model):
    # Extract the theorems out of full data
    theorems = [js["docString"] for js in data]  
    # Encode all theorems into vectors
    embeddings = model.encode(theorems, show_progress_bar=True)
    # Get the dimension of the embeddings
    d = embeddings.shape[1]
    # Build the FAISS index
    index = faiss.IndexFlatL2(d)
    # Add the theorem vectors to the index
    index.add(embeddings)
    # Save the index to INDEX_PATHS[descField]
    faiss.write_index(index, index_path)

def main(model):
    for descField in ["docString", "concise-description", "description"]:
        if not os.path.exists(INDEX_PATHS[descField]):
            print(f"Creating index for {descField}...")
            data = load_data(DESCFIELD_PATHS[descField])
            create_index(INDEX_PATHS[descField], data, model)
            print(f"Index created and saved at {INDEX_PATHS[descField]}")
        else:
            print(f"Found index for {descField}")