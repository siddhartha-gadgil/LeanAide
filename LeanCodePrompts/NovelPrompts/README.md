# Novel prompts for testing the model 

Several test prompts are required for assessing the autoformalisation capabilities of the language model. Good test prompts should ideally:
1. Be novel, i.e., not a part of the training data (which includes `mathlib`)
2. Be short, single-sentence docstrings 
3. Make use of only "standard" mathematical concepts, structures and terminology (such as groups, inequalities, graphs, real numbers, etc., and **not** surreal numbers, matroids, or affine connections that are a part of self-contained theories absent in `mathlib`)

# Structure of the folder

## `all_prompts.org`

This file will contain several prompts in plaintext format. 

## `all_clean_prompts.json`

This file will contain the same prompts in a more computer-readable format.

## `mathlib_similarity.py`

This file will contain code that compares the similarity of a given sentence with all the sentences in `data/clean_prompts.json` using the code in `SentenceSimilarityTask/sentence_similarity.py`, and judge whether the sentence is "novel" by checking whether the maximum similarity score is below a certain threshold.

## `novel_prompts.json`

This file will contain all the prompts judged to be "novel" by the above code. These prompts will constitute the final testing data for the model.

---