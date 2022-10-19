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

def embeddings(filename, field, model_name):
    blob = sentences(filename)
    sents = [sent[field] for sent in blob]
    return models[model_name].encode(sents)

def save_embeddings(filename, field, model_name):
    embs = embeddings(filename, field, model_name)
    # drop json extension
    filename = filename[:-5]
    np.save(filename + '-' + field + '-' + model_name + '.npy', embs)

def load_embeddings(filename, field, model_name):
    f = open(filename, 'r')
    blob = f.read() 
    data = json.loads(blob)
    f.close()
    filename = filename[:-5]
    return np.load(filename + '-' + field + '-' + model_name + '.npy'), data

from numpy import dot
from numpy.linalg import norm

def closest_embeddings(sentence, model_name, embeddings, data, n):
    sentence_embedding = models[model_name].encode(sentence)
    distances = torch.tensor([dot(sentence_embedding, emb)/(norm(sentence_embedding)*norm(emb)) for emb in embeddings])
    _, indices = torch.topk(distances, n)
    return [data[i] for i in indices]


