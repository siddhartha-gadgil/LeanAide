#https://huggingface.co/course/chapter5/6?fw=tf
#https://huggingface.co/docs/datasets/loading

from sentence_transformers import SentenceTransformer, util
import torch
import json
import pickle
import time
#from torch.utils.data import Dataset
from datasets import Dataset
import os
import numpy as np


def convert_to_Dataset(embedding_path="/home/t-agrawala/Desktop/ATP-Project/SentenceSimilarityTask/embeddings_store/all-mpnet-base-v2.pkl"):
    full_dct = {}
    fIn = open(embedding_path,"rb")
    stored_data = pickle.load(fIn)
    corpus_path = stored_data["corpus_path"]
    sentences =  stored_data["sentences"]
    embeddings = stored_data["embeddings"].cpu().numpy()
    fread = open(corpus_path,"r",encoding="utf-8")
    prompt_corpus = json.load(fread)
    full_dct["info"] = prompt_corpus #6078 info
    full_dct["embeddings"] = embeddings #768 embedding size
    ret = Dataset.from_dict(full_dct)
    ret.add_faiss_index(column="embeddings")
    return ret



def faiss_sample(ret, #dataset object
                main_prompt,
                top_k=4,
                embedding_path = "/home/t-agrawala/Desktop/ATP-Project/SentenceSimilarityTask/embeddings_store/all-mpnet-base-v2.pkl", 
                model_name = 'sentence-transformers/all-mpnet-base-v2'):
    model = SentenceTransformer(model_name,device='cpu') #check with respect to Device #TODO
    query_embedding = model.encode(main_prompt)
    scores, samples = ret.get_nearest_examples("embeddings",query_embedding, k=top_k)
    return samples

class search_embedding_data(Dataset):
    def __init__(self,embedding_path):
        #embedding_path = embedding_store_path
        fIn = open(embedding_path,"rb")
        stored_data = pickle.load(fIn)
        self.corpus_path = stored_data["corpus_path"]
        self.sentences =  stored_data["sentences"]
        self.embeddings = stored_data["embeddings"].cpu().numpy()
        print(self.embeddings.shape)

    def __len__(self):
        return len(self.sentences)

    def __getitem__(self, idx):
        return {'sentence' : self.sentences[idx], 'embedding' : self.embeddings[idx]}  

# main_prompt = "For any propositions `P` and `A`, `P` follows from `A` under the assumption that `P` is true."
# samples = main_KNN_test(main_prompt)
# #samples = json.loads(samples)
# for s in samples["info"]:
#     print()
#     print(s["doc_string"])
# print("=====================================")
# print(samples["info"])