import json
import jsonlines
from transformers import AutoTokenizer


def preprocess_examples(example, tokenizer):
    # encode the code-docstring pairs
    statement = example['statement']
    ids = example['identifiers']

    prompt = f'''List the premises (i.e., theorems) used in the proof of the following Lean 4 theorem: 
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
        "content": f"{ids}"
    }]
    text = tokenizer.apply_chat_template(chat, tokenize=False)

    # encode the summaries
    model_inputs = {"text" : text}

    return model_inputs

def write_all(model_id = "morph-labs/morph-prover-v0-7b", set='train'):
    print('Writing ' + set)
    tokenizer = AutoTokenizer.from_pretrained(model_id)
    examples = []
    print('Reading ' + set)
    with jsonlines.open(f'rawdata/premises/ident_strings/{set}.jsonl') as reader:
        for obj in reader:
            js = obj
            examples.append(preprocess_examples(js, tokenizer))
    with jsonlines.open('rawdata/premises/ident_strings/' + model_id + f'/{set}.jsonl', 'w') as writer:
        writer.write_all(examples)

write_all(set='test')
write_all(set='valid')