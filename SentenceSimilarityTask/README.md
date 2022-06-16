# Sentence Similarity

## Using pre-trained LMs
* install `sentence-transformers` : `pip install -U sentence-transformers`
* List of models available : [sentence-embedding-models](https://www.sbert.net/docs/pretrained_models.html#sentence-embedding-models/)
* Dealing with the Unkown tokens (TODO) :
    - Since these are trained on a different dataset, their vocab might not capture maths symbols
    - Example shown below \
    `Info for α : Type,      p : parser α    ⊢ p.bind parser.pure = p`\
    `Print token ids..` \
    `[101, 1155, 1024, 2828, 1010, 1052, 1024, 11968, 8043, 1155, 100, 1052, 1012, 14187, 11968, 8043, 1012, 5760, 1027, 1052, 102] ` \
    `Print the tokens mapped to the ids (to detect UNKOWN tokens)..` \
    `['[CLS]', 'α', ':', 'type', ',', 'p', ':', 'par', '##ser', 'α', '[UNK]', 'p', '.', 'bind', 'par', '##ser', '.', 'pure', '=', 'p', '[SEP]'] ` \


## Fine-tuning LMs for this task
* Use Siamese Networks

## Hand-crafted Heuristics
