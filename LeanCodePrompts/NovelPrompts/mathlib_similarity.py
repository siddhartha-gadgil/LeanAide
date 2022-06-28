#https://www.sbert.net/

import pwd
from sentence_transformers import SentenceTransformer, util
import torch
import json
import sys

sys.path.append(".")
sys.path.append("../../SentenceSimilarityTask")
from sentence_similarity import sentence_tokenize_info, calc_similarity

def is_novel_statement (s : str, threshold : float = 0.7) -> bool:
    """
    This function is used to compare the similarity of the input sentence with the mathlib dataset.
    A statement is considered "novel" if the similarity score with all the statements in the mathlib dataset is less than the threshold.
    """

    model_name = 'sentence-transformers/all-mpnet-base-v2' 
    model = SentenceTransformer(model_name)

    #Load the mathlib statements 
    with open('../../data/clean_prompt_statements.txt', 'r') as f:
        mathlib_statements = f.readlines()
   
    for thm_st in mathlib_statements:
        thm_st = thm_st.rstrip('\n')
        sim_score = calc_similarity([s, thm_st], model)
        if sim_score > threshold:
            return False

    return True