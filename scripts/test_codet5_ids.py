#!/usr/bin/env python
# coding: utf-8

# This is training of a model for generating lists of identifiers in a proof from the statement in Lean 4.

# This is adapted from a notebook for training a CodeT5 model on generating documentation for Ruby code.


from transformers import T5ForConditionalGeneration
import json
from transformers import RobertaTokenizer
import torch
from random import sample

tokenizer = RobertaTokenizer.from_pretrained("Salesforce/codet5p-220m")

prefix = "Lean proof-identifiers from Theorem: "
max_input_length = 256
max_target_length = 256


model = T5ForConditionalGeneration.from_pretrained("rawdata/idstrings_codet5p-220m/trained_model", device_map='auto')
# model = model.cuda()
# if torch.cuda.is_available() else torch.device("cpu")
device = torch.device("cuda")
# ## Inference
#
# Now that we've trained a model, let's test it on some examples from the test set.
model.eval()

# Empty the cache to free up GPU memory
torch.cuda.empty_cache()

def split_prediction(s):
    return json.loads(s)


class PredictionScores:
    def __init__(self, ids, prediction_strings):
        self.target_size = len(ids)
        prediction_lists = [split_prediction(p) for p in prediction_strings]
        predictions = set([p for l in prediction_lists for p in l])
        self.prediction_size = len(predictions)
        self.correct = [p for p in predictions if p in ids]
        self.missed = [p for p in ids if p not in predictions]
        self.coverage = len(self.correct) / len(ids) if len(ids) > 0 else 0
        self.efficiency = len(
            self.correct) / self.prediction_size if self.prediction_size > 0 else 0


with open('rawdata/premises/identifiers/test.jsonl') as f:
    test_ids = [json.loads(line) for line in f]

# test_ids = sample(test_ids, 1000) # for testing
print('Test set size:', len(test_ids))


def generate_ids(prompt, temperature=1.5, num_return_sequences=8, max_length=256):
    input_ids = tokenizer.encode(
        prefix + prompt, return_tensors='pt').to(device)
    gen_tokens = model.generate(
        input_ids,
        do_sample=True,
        temperature=temperature,
        num_return_sequences=num_return_sequences,
        max_length=max_length,
    )
    gen_text = tokenizer.batch_decode(gen_tokens, skip_special_tokens=True)
    return gen_text


coverage_list = []
efficiency_list = []
count = 0
covered = 0

with open('rawdata/premises/identifiers/codet5_test_data.jsonl', 'w', encoding='utf-8') as f:
    for d in test_ids:
        gens = generate_ids(d['theorem'])
        d['generated'] = gens
        scores = PredictionScores(d['identifiers'], gens)
        d['target_size'] = scores.target_size
        d['prediction_size'] = scores.prediction_size
        d['correct'] = scores.correct
        d['missed'] = scores.missed
        d['coverage'] = scores.coverage
        if scores.coverage == 1:
            covered += 1
        d['efficiency'] = scores.efficiency
        f.write(json.dumps(d, ensure_ascii=False) + '\n')
        coverage_list.append(scores.coverage)
        efficiency_list.append(scores.efficiency)
        count += 1
        if count % 100 == 0:
            print(count)
            print('average coverage:', sum(coverage_list) / len(coverage_list))
            print('average efficiency:', sum(
                efficiency_list) / len(efficiency_list))
            print('covered:', covered)
            print('fraction fully covered:', covered / count)
            print()
