from sentence_transformers import SentenceTransformer
model = SentenceTransformer('all-MiniLM-L6-v2')

import json
import numpy as np
import torch

def sentences(filename, field):
    f = open(filename, 'r')
    blob = f.read()
    f.close()
    return json.loads(blob)

def embeddings(filename, field):
    sentences = sentences(filename, field)
    return model.encode(sentences)

def save_embeddings(filename, field):
    embeddings = embeddings(filename, field)
    # drop json extension
    filename = filename[:-5]
    np.save(filename + '.npy', embeddings)

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
    distances = np.array([dot(sentence, emb)/(norm(sentence)*norm(emb)) for emb in embeddings])
    _, indices = torch.topk(distances, n)
    return [data[i] for i in indices]


