#!/usr/bin/env python3

from web_serv.embed_picker import *
from sentence_transformers import SentenceTransformer
print ('Computing embeddings...')
save_embeddings('data/safe_prompts.json', 'doc_string', 'all-mpnet-base-v2')
save_embeddings('data/lean4-thms.json', 'core-prompt', 'all-MiniLM-L6-v2')

print ('Loading models...')
models = {
    'all-MiniLM-L6-v2': SentenceTransformer('all-MiniLM-L6-v2'),
    'all-mpnet-base-v2': SentenceTransformer('all-mpnet-base-v2')
}