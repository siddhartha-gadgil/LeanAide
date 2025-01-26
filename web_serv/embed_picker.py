from sentence_transformers import SentenceTransformer
model = SentenceTransformer('all-MiniLM-L6-v2')

models = {
    'all-MiniLM-L6-v2': SentenceTransformer('all-MiniLM-L6-v2'),
    'all-mpnet-base-v2': SentenceTransformer('all-mpnet-base-v2')
}

import json
import numpy as np
import torch

def sentences(filename):
    f = open(filename, 'r')
    blob = f.read()
    f.close()
    return json.loads(blob)

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
    distances = torch.tensor([dot(sentence_embedding, emb) for emb in embeddings])
    _, indices = torch.topk(distances, n)
    return [data[i] for i in indices]
