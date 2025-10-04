import os
import json
import faiss
import numpy as np

DIM = 768
# Adjust the batch size according to your memory
BATCH_SIZE = 4000
DESCFIELD_PATHS = {
    "docString" : "resources/mathlib4-prompts_new.jsonl",
    "concise-description" : "resources/mathlib4-descs_new.jsonl",
    "description" : "resources/mathlib4-descs_new.jsonl"
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

def batch_generator(descField, batch_size):
    batch, ids = [], []
    with open(DESCFIELD_PATHS[descField], "r", encoding="utf-8") as file:
        for line_num, line in enumerate(file):
            data = json.loads(line)
            text = data[FIELD_NAME[descField]]
            batch.append(text)
            ids.append(np.int64(line_num))
            if len(batch) == batch_size:
                yield (batch, np.array(ids))
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

def main(model):
    for descField in ["concise-description", "description", "docString"]:
        if not os.path.exists(INDEX_PATHS[descField]):
            print(f"Creating index for {descField}...")
            create_index(descField, model)
            print(f"Index created and saved at {INDEX_PATHS[descField]}")
        else:
            print(f"Found index for {descField}")