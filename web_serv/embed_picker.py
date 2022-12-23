from sentence_transformers import SentenceTransformer
model = SentenceTransformer('all-MiniLM-L6-v2')

models = {
    'all-MiniLM-L6-v2': SentenceTransformer('all-MiniLM-L6-v2'),
    'all-mpnet-base-v2': SentenceTransformer('all-mpnet-base-v2')
}

import json
import numpy as np

def sentences(filename):
    f = open(filename, 'r')
    blob = f.read()
    f.close()
    return json.loads(blob)

def embeddings(filename, field, model_name):
    blob = sentences(filename)
    sents = [sent[field] for sent in blob]
    return models[model_name].encode(sents, normalize_embeddings=True)

def save_embeddings(filename, field, model_name):
    embs = embeddings(filename, field, model_name)
    # drop json extension
    filename = filename[:-5]
    np.save(filename + '-' + field + '-' + model_name + '.npy', embs)

def load_embeddings(filename, field, model_name):
    try:
        f = open(filename, 'r')
        blob = f.read() 
        data = json.loads(blob)
        f.close()
        filename = filename[:-5]
        return np.load(filename + '-' + field + '-' + model_name + '.npy'), data
    except OSError:
        print ('Computing embeddings...')
        save_embeddings(filename+'.json', field, model_name)
        return load_embeddings(filename+'.json', field, model_name)

def closest_embeddings(sentence, model_name, embeddings, data, n):
    sentence_embedding = models[model_name].encode(sentence)
    distances = np.dot(embeddings, sentence_embedding)
    indices = np.argsort(distances)[-n:]
    return [data[i] for i in indices]

def spread_similar_embeddings(sentence, model_name, embeddings, data, n_top, n_candidate):
    """
    An algorithm to find similar embeddings, but with a spread.

    The algorithm first finds the top `n_candidate`-many embeddings by similarity.
    A subset of size `n_top` is created from this set by greedily selecting elements that
    increase the sum of the pairwise distances of embeddings.
    """
    sentence_embedding = models[model_name].encode(sentence)
    distances = np.dot(embeddings, sentence_embedding)
    indices = list(np.argsort(distances)[-n_candidate:])
    print("Candidate keywords: ", [data[i] for i in indices])
    print("Candidate keyword scores: ", [distances[i] for i in indices])
    top_idx = indices.pop(-1)
    spread_indices = [top_idx] # the list of indices with a good pair-wise spread, initialised with the top scoring index
    v = embeddings[top_idx] # this vector stores the sum of all the entries in the `spread_idxs` list

    for _ in range(1, n_top):
        least_sim = np.argsort(np.dot(embeddings[indices], v))[0]
        idx = indices.pop(least_sim)
        spread_indices.append(idx)
        v = v + embeddings[idx]

    print("Selected keywords: ", [data[i] for i in spread_indices])
    print("Selected keyword scores: ", [distances[i] for i in spread_indices])
    
    return [data[i] for i in spread_indices]


# Testing
#model = "all-MiniLM-L6-v2"
#embs, kwds = load_embeddings("../data/wiktionary_mathematics_keywords.json", "keyword", model)
#n_top = 5
#n_candidate = 20
#statement = "If R is a left Noetherian ring, then the polynomial ring R[X] is also a left Noetherian ring."
#print(closest_embeddings(statement, model, embs, kwds, n_top))
#print(spread_similar_embeddings(statement, model, embs, kwds, n_top, n_candidate))
