#!/usr/bin/env python
# coding: utf-8

# This is training of a model for generating lists of identifiers in a proof from the statement in Lean 4.

# This is adapted from a notebook for training a CodeT5 model on generating documentation for Ruby code.
import sys

size = sys.argv[1]
field = sys.argv[2]

prefixes = {
   'ids' : 'IDENTIFIERS',
   'lemma' : 'LEMMAS',
    'term' : 'TERMS'
}

prefix = prefixes[field] +  ' in Lean proof from Theorem: '

from transformers import RobertaTokenizer

tokenizer = RobertaTokenizer.from_pretrained(f"Salesforce/codet5-{size}")

max_input_length = 256
max_target_length = 256
batch_size = 8
if size == 'small':
    batch_size = 16

from transformers import T5ForConditionalGeneration 
model = T5ForConditionalGeneration.from_pretrained(f'Salesforce/codet5-{size}')
import torch
load_field = field
if len(sys.argv > 2):
    load_field = f'{sys.argv[2]}_field' # can be eg 'ids' or even a chain of fields like 'lemma_ids'

model.load_state_dict(torch.load(f"codet5_{load_field}_epoch_2.pt"))

device = torch.device("cuda") if torch.cuda.is_available() else torch.device("cpu")
model.to(device)
print ('Device: ')
print (device)

from tqdm.auto import tqdm

def generate_premises(prompt, prefix):
    input_ids = tokenizer(prefix + prompt, return_tensors='pt').to(device)
    gen_tokens = model.generate(
        input_ids,
        do_sample=True,
        temperature=0.8,
        num_return_sequences=5,
        max_length=256,
    )
    gen_text = tokenizer.decode(gen_tokens, skip_special_tokens=True)
    return gen_text

def evaluate():
    model.eval()
    import json
    import random
    with open(f'rawdata/test_ids.jsonl') as f:
        test_ids = [json.loads(line) for line in f if random.random() < 0.04]
    print ('Test set size:', len(test_ids))

    gen_progress_bar = tqdm(range(len(test_ids)))

    f= open(f"rawdata/test_{field}_generated.jsonl","w", encoding='utf-8')

    for d in test_ids:
        gens = generate_premises(d['theorem'], prefix)
        d[f'generated_{field}'] = gens
        gen_progress_bar.update(1)
        f.write(json.dumps(d, ensure_ascii=False) + '\n')

evaluate()