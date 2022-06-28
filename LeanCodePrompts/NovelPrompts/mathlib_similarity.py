#https://www.sbert.net/
# Some code is taken from `SentenceSimilarityTask/sentence_similarity.py`, since importing outside the folder is not possible in Python

from sentence_transformers import SentenceTransformer, util
import torch
import json

def sentence_tokenize_info(sentence,model):
        #print("Info for {}".format(sentence))
        #print("Print token ids..")
        inp_ids = model.tokenizer(sentence).input_ids
        #print(inp_ids,"\n")
        #print("Print the tokens mapped to the ids (to detect UNKOWN tokens)..")
        tokens = model.tokenizer.convert_ids_to_tokens(inp_ids)
        #print(tokens,"\n")

def calc_similarity(sentence_pair_list,model,check=False):
    """
    sentence_pair : list having pair of sentences to compute similarity
    model = language model being used to generate the embeddings
    check = bool flag to check the token-ids and mapped tokens
    """

    emb_1 = model.encode(sentence_pair_list[0],convert_to_tensor=True)
    emb_2 = model.encode(sentence_pair_list[1],convert_to_tensor=True)

    #compute cosine similarities of embeddings
    sim_score = (util.pytorch_cos_sim(emb_1, emb_2)).item()

    #check flag boolean to check the token-ids and mapped tokens
    if check:
        sentence_tokenize_info(sentence_pair_list[0], model)
        print("Size of embedding vector..")
        print(emb_1.shape[0],"\n")
        sentence_tokenize_info(sentence_pair_list[1], model)
        print("Size of embedding vector..")
        print(emb_2.shape[0],"\n")

    return sim_score

def mathlib_comparison(s : str) -> float:
    """
    This function is used to compare the similarity of the input sentence with the mathlib dataset.
    This is done by calculating the maximum similarity score between the input sentence and the mathlib dataset.
    """

    model_name = 'sentence-transformers/all-mpnet-base-v2' 
    model = SentenceTransformer(model_name)

    #Load the mathlib statements 
    with open('../../data/clean_prompt_statements.txt', 'r') as f:
        mathlib_statements = f.readlines()
   
    mathlib_statement_similarity_scores = map(lambda thm_st : calc_similarity([s, thm_st], model), mathlib_statements)
   
    return max(mathlib_statement_similarity_scores)

def is_novel (s : str) -> bool:
    """
    A string is considered "novel" (i.e., different from the mathlib dataset) if the similarity score is less than 0.7 (arbitrarily chosen for now).
    """
    return mathlib_comparison(s) < 0.7