from sentence_transformers import SentenceTransformer
model = SentenceTransformer('all-MiniLM-L6-v2')

import json
import numpy as np
import torch

def sentences(filename):
    f = open(filename, 'r')
    blob = f.read()
    f.close()
    return json.loads(blob)

def embeddings(filename, field):
    blob = sentences(filename)
    sents = [sent[field] for sent in blob]
    return model.encode(sents)

def save_embeddings(filename, field):
    embs = embeddings(filename, field)
    # drop json extension
    filename = filename[:-5]
    np.save(filename + '.npy', embs)

def load_embeddings(filename):
    f = open(filename, 'r')
    blob = f.read() 
    data = json.loads(blob)
    f.close()
    filename = filename[:-5]
    return np.load(filename + '.npy'), data

from numpy import dot
from numpy.linalg import norm

def closest_embeddings(sentence, embeddings, data, n):
    sentence_embedding = model.encode(sentence)
    distances = torch.tensor([dot(sentence_embedding, emb)/(norm(sentence_embedding)*norm(emb)) for emb in embeddings])
    _, indices = torch.topk(distances, n)
    return [data[i] for i in indices]


