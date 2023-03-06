#!/usr/bin/env python
# coding: utf-8


# This is training of a model for generating from a statement in Lean 4:
# * identifiers in the proof
# * lemmas in the proof, i.e., types of subterms which are proofs.
# * some subterms in the proof, prioritizing shorter ones.

# This is adapted from a notebook for training a CodeT5 model on generating documentation for Ruby code.


from datasets import load_dataset

dataset = load_dataset('json', data_dir='rawdata', data_files="train_ids.jsonl")
print(dataset)



# 
# 
# We need to turn the "theorem" input from above into `input_ids`, and similarly, we need to turn the "ids" output from above into `input_ids`, which will serve as the `labels` for the model.
# 
# In addition, as these models are trained on batches of examples rather than one example at a time, we'll need to pad/truncate both the inputs and labels, such that they are all of the same length. That's why we also will add an `attention_mask` input to the model, such that it knows not to take into account padding tokens when computing attention scores.
# 
# To summarize: 
# * input: theorem, which is turned into `input_ids` + `attention_mask`
# * output: ids, which are turned into `labels` (which are the `input_ids` of the docstrings).
# 
# Below, we define a `preprocess_examples` function, which we can apply on the entire dataset. 


from transformers import RobertaTokenizer

tokenizer = RobertaTokenizer.from_pretrained("Salesforce/codet5-base")

prefix_id = "Lean proof-identifiers from Theorem: "
prefix_lemma = "Lean proof-lemmas from Theorem: "
prefix_term = "Lean proof-subterms from Theorem: "

max_input_length = 256
max_target_length = 256

def preprocess_examples(examples, prefix, field):
  # encode the code-docstring pairs
  theorems = examples['theorem']
  ids = examples[field]
  
  inputs = [prefix + thm for thm in theorems]
  model_inputs = tokenizer(inputs, max_length=max_input_length, padding="max_length", truncation=True)

  # encode the summaries
  labels = tokenizer(ids, max_length=max_target_length, padding="max_length", truncation=True).input_ids

  # important: we need to replace the index of the padding tokens by -100
  # such that they are not taken into account by the CrossEntropyLoss
  labels_with_ignore_index = []
  for labels_example in labels:
    labels_example = [label if label != 0 else -100 for label in labels_example]
    labels_with_ignore_index.append(labels_example)
  
  model_inputs["labels"] = labels_with_ignore_index

  return model_inputs


# Now that we have defined the function, let's call `.map()` on the HuggingFace Dataset object, which allows us to apply this function in batches (by default a batch size of 1,000 is used!) - hence super fast.

def preprocess_examples_ids(examples):
    return preprocess_examples(examples, prefix_id, 'ids')

def preprocess_examples_lemmas(examples):
    return preprocess_examples(examples, prefix_lemma, 'lemmas')

def preprocess_examples_terms(examples):
    return preprocess_examples(examples, prefix_term, 'terms')


dataset_id = dataset.map(preprocess_examples_ids, batched=True)
dataset_lemma = dataset.map(preprocess_examples_lemmas, batched=True)
dataset_term = dataset.map(preprocess_examples_terms, batched=True)

# Next, let's set the format to "torch" and create PyTorch dataloaders.
from torch.utils.data import DataLoader

dataset_id.set_format(type="torch", columns=['input_ids', 'attention_mask', 'labels'])
dataset_lemma.set_format(type="torch", columns=['input_ids', 'attention_mask', 'labels'])
dataset_term.set_format(type="torch", columns=['input_ids', 'attention_mask', 'labels'])

train_dataloader_id = DataLoader(dataset_id['train'], shuffle=True, batch_size=8)
train_dataloader_lemma = DataLoader(dataset_lemma['train'], shuffle=True, batch_size=8)
train_dataloader_term = DataLoader(dataset_term['train'], shuffle=True, batch_size=8)

batch = next(iter(train_dataloader_id))
print(batch.keys())

batch = next(iter(train_dataloader_lemma))
print(batch.keys())

batch = next(iter(train_dataloader_term))
print(batch.keys())

# Let's verify an example, by decoding it back into text:
print ("Sample input:")
print (tokenizer.decode(batch['input_ids'][0]))

labels = batch['labels'][0]
print("Sample labels:")
print(tokenizer.decode([label for label in labels if label != -100]))

from transformers import T5ForConditionalGeneration 
model = T5ForConditionalGeneration.from_pretrained('Salesforce/codet5-base')
loss = model(input_ids=batch['input_ids'], attention_mask=batch['attention_mask'], labels=batch['labels']).loss
print("Loss:")
print (loss.item())


from torch.optim import AdamW
optimizer = AdamW(model.parameters(), lr=5e-5)
from transformers import get_scheduler
num_epochs = 3
num_training_steps = num_epochs * (len(train_dataloader_id) + len(train_dataloader_lemma) + len(train_dataloader_term))
lr_scheduler = get_scheduler(
    name="linear", optimizer=optimizer, num_warmup_steps=5000, num_training_steps=num_training_steps
)

import torch
device = torch.device("cuda") if torch.cuda.is_available() else torch.device("cpu")
model.to(device)
print ('Device: ')
print (device)


from tqdm.auto import tqdm

progress_bar = tqdm(range(num_training_steps))

model.train()
for epoch in range(num_epochs):
    for batch in train_dataloader_id:
        batch = {k: v.to(device) for k, v in batch.items()}
        outputs = model(**batch)
        loss = outputs.loss
        loss.backward()

        optimizer.step()
        lr_scheduler.step()
        optimizer.zero_grad()
        progress_bar.update(1)
    for batch in train_dataloader_lemma:
        batch = {k: v.to(device) for k, v in batch.items()}
        outputs = model(**batch)
        loss = outputs.loss
        loss.backward()
        optimizer.step()
        lr_scheduler.step()
        optimizer.zero_grad()
        progress_bar.update(1)
    for batch in train_dataloader_term:
        batch = {k: v.to(device) for k, v in batch.items()}
        outputs = model(**batch)
        loss = outputs.loss
        loss.backward()

        optimizer.step()
        lr_scheduler.step()
        optimizer.zero_grad()
        progress_bar.update(1)
    torch.save(model.state_dict(), f"codet5_ids_epoch_{epoch}.pt")

# ## Inference
# 
# Now that we've trained a model, let's test it on some examples from the test set.
model.eval()
import json
with open('rawdata/test_ids.jsonl') as f:
    test_ids = [json.loads(line) for line in f]
print ('Test set size:', len(test_ids))

gen_progress_bar = tqdm(range(len(test_ids)))

def generate_premises(prompt, prefix):
    input_ids = tokenizer.encode(prefix + prompt, return_tensors='pt').to(device)
    gen_tokens = model.generate(
        input_ids,
        do_sample=True,
        temperature=0.8,
        num_return_sequences=5,
        max_length=256,
    )
    gen_text = tokenizer.batch_decode(gen_tokens, skip_special_tokens=True)
    return gen_text

for d in test_ids:
    gens = generate_premises(d['theorem'], prefix_id)
    d['generated_ids'] = gens
    gens = generate_premises(d['theorem'], prefix_lemma)
    d['generated_lemmas'] = gens
    gens = generate_premises(d['theorem'], prefix_term)
    d['generated_terms'] = gens
    gen_progress_bar.update(1)

with open('rawdata/test_ids_generated.jsonl', 'w', encoding='utf-8') as f:
    for d in test_ids:
        f.write(json.dumps(d, ensure_ascii=False) + '\n')

# Some more training

progress_bar = tqdm(range(num_training_steps))

model.train()
for epoch in range(num_epochs, 2 * num_epochs):
    for batch in train_dataloader_id:
        batch = {k: v.to(device) for k, v in batch.items()}
        outputs = model(**batch)
        loss = outputs.loss
        loss.backward()

        optimizer.step()
        lr_scheduler.step()
        optimizer.zero_grad()
        progress_bar.update(1)
    for batch in train_dataloader_lemma:
        batch = {k: v.to(device) for k, v in batch.items()}
        outputs = model(**batch)
        loss = outputs.loss
        loss.backward()
        optimizer.step()
        lr_scheduler.step()
        optimizer.zero_grad()
        progress_bar.update(1)
    for batch in train_dataloader_term:
        batch = {k: v.to(device) for k, v in batch.items()}
        outputs = model(**batch)
        loss = outputs.loss
        loss.backward()

        optimizer.step()
        lr_scheduler.step()
        optimizer.zero_grad()
        progress_bar.update(1)
    torch.save(model.state_dict(), f"codet5_ids_epoch_{epoch}.pt")

# ## Inference
# 
# Now that we've trained a model, let's test it on some examples from the test set.
model.eval()
import json
with open('rawdata/test_ids.jsonl') as f:
    test_ids = [json.loads(line) for line in f]
print ('Test set size:', len(test_ids))

gen_progress_bar = tqdm(range(len(test_ids)))

def generate_premises(prompt, prefix):
    input_ids = tokenizer.encode(prefix + prompt, return_tensors='pt').to(device)
    gen_tokens = model.generate(
        input_ids,
        do_sample=True,
        temperature=0.8,
        num_return_sequences=5,
        max_length=256,
    )
    gen_text = tokenizer.batch_decode(gen_tokens, skip_special_tokens=True)
    return gen_text

for d in test_ids:
    gens = generate_premises(d['theorem'], prefix_id)
    d['generated_ids'] = gens
    gens = generate_premises(d['theorem'], prefix_lemma)
    d['generated_lemmas'] = gens
    gens = generate_premises(d['theorem'], prefix_term)
    d['generated_terms'] = gens
    gen_progress_bar.update(1)

with open('rawdata/test_ids_generated_round2.jsonl', 'w', encoding='utf-8') as f:
    for d in test_ids:
        f.write(json.dumps(d, ensure_ascii=False) + '\n')
