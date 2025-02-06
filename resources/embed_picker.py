from sentence_transformers import SentenceTransformer
model = 'all-MiniLM-L6-v2'

# a few good models to choose from
models = {
    'all-MiniLM-L6-v2': SentenceTransformer('all-MiniLM-L6-v2'),
    'bge-m3': SentenceTransformer('BAAI/bge-m3'),
    'all-mpnet-base-v2': SentenceTransformer('all-mpnet-base-v2'),
}

import json
import numpy as np


def sentences(filename):
    if filename.endswith('.jsonl'):
        with open(filename, 'r', encoding='utf-8') as f:
            return [json.loads(line) for line in f if line.strip()]
    else:  # Assume standard JSON
        with open(filename, 'r', encoding='utf-8') as f:
            return json.load(f)


def embeddings(filename, field, model):
    blob = sentences(filename)
    sents = [sent[field] for sent in blob]
    return models[model].encode(sents, normalize_embeddings=True)

def save_embeddings(filename, field, model):
    embs = embeddings(filename, field, model)
    # drop json extension
    filename = filename[:-5]
    np.save(filename + '-' + field + '-' + model + '.npy', embs)

def load_embeddings(filename, field, model):
    try:
        f = open(filename, 'r')
        blob = f.read() 
        data = json.loads(blob)
        f.close()
        filename = filename[:-5]
        return np.load(filename + '-' + field + '-' + model + '.npy'), data
    except OSError:
        print ('Computing embeddings...')
        save_embeddings(filename+'.json', field, model)
        return load_embeddings(filename+'.json', field, model)

from numpy import dot
from numpy.linalg import norm

def closest_embeddings(sentence, model, embeddings, data, n):
    sentence_embedding = models[model].encode(sentence)
    distances = np.dot(embeddings, sentence_embedding)
    indices = np.argsort(distances)[-n:][::-1]
    return [data[i] for i in indices]

#print(embeddings('example.jsonl', 'description', model))