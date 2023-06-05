#!/usr/bin/env python
# coding: utf-8

# This is training of a model for generating lists of identifiers in a proof from the statement in Lean 4.

# This is adapted from a notebook for training a CodeT5 model on generating documentation for Ruby code and further modified for the causal CodeGen model.


from datasets import load_dataset
import torch
from random import sample

dataset = load_dataset('json', data_dir='rawdata/premises/ident_strings', data_files="train.jsonl")
print(dataset)

# 
# Below, we define a `preprocess_examples` function, which we can apply on the entire dataset. 


from transformers import AutoModelForCausalLM, AutoTokenizer

checkpoint = "Salesforce/codegen-350M-multi"
tokenizer = AutoTokenizer.from_pretrained(checkpoint)

max_length = 512

def preprocess_examples(examples):
  # encode the code-docstring pairs
  
  inputs = ['theorem ' + eg['theorem'] + '\nIdentifiers: ' + eg['identifiers'] for eg in examples]
  model_inputs = tokenizer(inputs, max_length=max_length, padding="max_length", truncation=True)
  labels = model_inputs['input_ids']
  model_inputs["labels"] = labels
  return model_inputs


# Now that we have defined the function, let's call `.map()` on the HuggingFace Dataset object, which allows us to apply this function in batches (by default a batch size of 1,000 is used!) - hence super fast.



dataset = dataset.map(preprocess_examples, batched=True)

# Next, let's set the format to "torch" and create PyTorch dataloaders.
from torch.utils.data import DataLoader

dataset.set_format(type="torch", columns=['input_ids', 'attention_mask', 'labels'])
train_dataset = dataset['train']
# train_dataset = train_dataset.shuffle(seed=42).select(range(10000)) # for testing


model = AutoModelForCausalLM.from_pretrained(checkpoint)
model = model.cuda()
device = torch.device("cuda") 

from transformers import TrainingArguments, Trainer

training_args = TrainingArguments(output_dir="rawdata/idstrings_codegen_350")

trainer = Trainer(
    model=model,
    args=training_args,
    train_dataset=train_dataset,
)

trainer.train()

model.save_pretrained("rawdata/idstrings_codegen_350/trained_model")

train_dataloader = DataLoader(dataset['train'], shuffle=True, batch_size=8)


# ## Inference
# 
# Now that we've trained a model, let's test it on some examples from the test set.
model.eval()
import json

def split_prediction(s):
   return [x.strip() for x in s.split(';')]

class PredictionScores:
   def __init__(self, ids, prediction_strings):
      self.target_size = len(ids)
      prediction_lists = [split_prediction(p) for p in prediction_strings]
      predictions = set([p for l in prediction_lists for p in l])
      self.prediction_size = len(predictions)
      self.correct = [p for p in predictions if p in ids]
      self.missed = [p for p in ids if p not in predictions]
      self.coverage = len(self.correct) / len(ids) if len(ids) > 0 else 0
      self.efficiency = len(self.correct) / self.prediction_size if self.prediction_size > 0 else 0

with open('rawdata/premises/identifiers/test.jsonl') as f:
    test_ids = [json.loads(line) for line in f]

# test_ids = sample(test_ids, 1000) # for testing
print ('Test set size:', len(test_ids))

def generate_ids(prompt, temperature=1.5, num_return_sequences=8, max_length=256):
    input = "theorem " + prompt + '\nIdentifiers: '
    input_ids = tokenizer.encode(input, return_tensors='pt').to(device)
    completion_tokens = model.generate(
        input_ids,
        do_sample=True,
        temperature=temperature,
        num_return_sequences=num_return_sequences,
        max_length=max_length,
    )
    completion_text = tokenizer.batch_decode(completion_tokens, skip_special_tokens=True)
    gen_text = [t[len(input):] for t in completion_text]
    return gen_text

coverage_list=[]
efficiency_list=[]
count = 0
covered = 0

with open('rawdata/premises/identifiers/codegen_test_data.jsonl', 'w', encoding='utf-8') as f:
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
            print('average efficiency:', sum(efficiency_list) / len(efficiency_list))
            print('covered:', covered)
            print('fraction fully covered:', covered / count)
            print()



