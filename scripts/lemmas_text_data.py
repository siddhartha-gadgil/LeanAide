import json
import jsonlines
from transformers import AutoTokenizer


def preprocess_examples(example, tokenizer):
    # encode the code-docstring pairs
    statement = example['theorem']
    lemma = example['lemma']

    prompt = f'''State a Lemma (as a theorem in `Lean 4`) used in the proof of the following Lean 4 theorem: 
```lean
{statement}
```
'''
    chat = [{
        "role": "system",
        "content": "You are a Lean 4 coding assistant. When asked for code reply with ONLY the Lean 4 code."        
    },
    {
        "role": "user",
        "content": prompt
    },
    {
        "role": "assistant",
        "content": lemma
    }]
    text = tokenizer.apply_chat_template(chat, tokenize=False)

    # encode the summaries
    model_inputs = {"text" : text}

    return model_inputs

def preprocess_examples_query(example, tokenizer):
    # encode the code-docstring pairs
    statement = example['theorem']
    lemma = example['lemma']

    prompt = f'''State a Lemma (as a theorem in `Lean 4`) used in the proof of the following Lean 4 theorem: 
```lean
{statement}
```
'''
    chat = [{
        "role": "system",
        "content": "You are a Lean 4 coding assistant. When asked for code reply with ONLY the Lean 4 code."        
    },
    {
        "role": "user",
        "content": prompt
    },
    ]
    text = tokenizer.apply_chat_template(chat, tokenize=False)

    # encode the summaries
    model_inputs = {"text" : text}

    return model_inputs


def write_all(model_id = "morph-labs/morph-prover-v0-7b", set='train'):
    print('Writing ' + set)
    tokenizer = AutoTokenizer.from_pretrained(model_id)
    examples = []
    print('Reading ' + set)
    with jsonlines.open(f'rawdata/premises/doc_lemma_pairs/{set}.jsonl') as reader:
        for obj in reader:
            js = obj
            examples.append(preprocess_examples(js, tokenizer))
    with jsonlines.open('rawdata/premises/doc_lemma_pairs/' + model_id + f'/{set}.jsonl', 'w') as writer:
        writer.write_all(examples)

def write_all_queries(model_id = "morph-labs/morph-prover-v0-7b", set='train'):
    print('Writing ' + set)
    tokenizer = AutoTokenizer.from_pretrained(model_id)
    examples = []
    print('Reading ' + set)
    with jsonlines.open(f'rawdata/premises/doc_lemma_pairs/{set}.jsonl') as reader:
        for obj in reader:
            js = obj
            examples.append(preprocess_examples_query(js, tokenizer))
    with jsonlines.open('rawdata/premises/doc_lemma_pairs/' + model_id + f'/{set}-query.jsonl', 'w') as writer:
        writer.write_all(examples)

write_all(set='train')
write_all(set='test')
write_all(set='valid')

write_all_queries(set='test')
write_all_queries(set='valid')