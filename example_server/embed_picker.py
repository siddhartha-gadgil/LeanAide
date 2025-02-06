from sentence_transformers import SentenceTransformer
import os

model = os.environ.get("LEANAIDE_EXAMPLES_MODEL", 'all-MiniLM-L6-v2')

resources_dir = "resources"

# a few good models to choose from
models = {
    'all-MiniLM-L6-v2': SentenceTransformer('all-MiniLM-L6-v2'),
    'bge-m3': SentenceTransformer('BAAI/bge-m3'),
    'all-mpnet-base-v2': SentenceTransformer('all-mpnet-base-v2'),
}

import json
import numpy as np

from pathlib import Path

def sentences(filename):
    if filename.endswith('.jsonl'):
        file_path = Path.cwd().parent / resources_dir / filename
        with open(file_path, 'r', encoding='utf-8') as f:
            return [json.loads(line) for line in f if line.strip()]
    else:  # Assume standard JSON
        file_path = Path.cwd().parent / resources_dir / filename
        with open(file_path, 'r', encoding='utf-8') as f:
            return json.load(f)


def embeddings(filename, field, model):
    blob = sentences(filename)
    sents = [sent[field] for sent in blob]
    return models.get(model, SentenceTransformer(model)).encode(sents, normalize_embeddings=True)

def save_embeddings(filename, field, model):
    embs = embeddings(filename, field, model)
    # drop json extension
    if filename.endswith('.json'):
        filename = filename[:-5]
    if filename.endswith('.jsonl'):
        filename = filename[:-6]
    model = model.replace('/', '-')    
    np.save(filename + '-' + field + '-' + model + '.npy', embs)

def load_embeddings(filename, field, model):
    try:
        file_path = Path.cwd().parent / resources_dir / filename
        f = open(file_path, 'r')
        blob = f.read() 
        if filename.endswith('.jsonl'):
            data = [json.loads(line) for line in blob.split('\n') if line.strip()]
        else:
            data = json.loads(blob)
        f.close()
        if filename.endswith('.json'):
            short_filename = filename[:-5]
        if filename.endswith('.jsonl'):
            short_filename = filename[:-6]
        model = model.replace('/', '-')
        return np.load(short_filename + '-' + field + '-' + model + '.npy'), data
    except OSError:
        print ('Computing embeddings...')
        save_embeddings(filename, field, model)
        return load_embeddings(filename, field, model)

from numpy import dot
from numpy.linalg import norm

def closest_embeddings(sentence, model, embeddings, data, n):
    sentence_embedding = models.get(model, SentenceTransformer(model)).encode(sentence)
    distances = np.dot(embeddings, sentence_embedding)
    indices = np.argsort(distances)[-n:][::-1]
    return [data[i] for i in indices]

#print(embeddings('example.jsonl', 'description', model))