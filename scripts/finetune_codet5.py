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

from datasets import load_dataset

dataset = load_dataset('json', data_dir='rawdata', data_files="train_ids.jsonl")
print(dataset)

from transformers import RobertaTokenizer

tokenizer = RobertaTokenizer.from_pretrained(f"Salesforce/codet5-{size}")

max_input_length = 256
max_target_length = 256

def preprocess_examples(examples):
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
dataset = dataset.map(preprocess_examples, batched=True)

# Next, let's set the format to "torch" and create PyTorch dataloaders.
from torch.utils.data import DataLoader

batch_size = 8
if size == 'small':
    batch_size = 16

dataset.set_format(type="torch", columns=['input_ids', 'attention_mask', 'labels'])
train_dataloader = DataLoader(dataset['train'], shuffle=True, batch_size=batch_size)

batch = next(iter(train_dataloader))
print(batch.keys())


# Let's verify an example, by decoding it back into text:
print ("Sample input:")
print (tokenizer.decode(batch['input_ids'][0]))

labels = batch['labels'][0]
print("Sample labels:")
print(tokenizer.decode([label for label in labels if label != -100]))

from transformers import T5ForConditionalGeneration 
model = T5ForConditionalGeneration.from_pretrained(f'Salesforce/codet5-{size}')
import torch
save_field = field
if len(sys.argv > 2):
    load_field = sys.argv[2] # can be eg 'ids' or even a chain of fields like 'lemmas_ids'
    model.load_state_dict(torch.load(f"codet5_{load_field}_epoch_2.pt"))
    save_field = f"{load_field}_{field}"

loss = model(input_ids=batch['input_ids'], attention_mask=batch['attention_mask'], labels=batch['labels']).loss
print("Loss:")
print (loss.item())


from torch.optim import AdamW
optimizer = AdamW(model.parameters(), lr=5e-5)
from transformers import get_scheduler
num_epochs = 3
num_training_steps = num_epochs * len(train_dataloader)
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
    for batch in train_dataloader:
        batch = {k: v.to(device) for k, v in batch.items()}
        outputs = model(**batch)
        loss = outputs.loss
        loss.backward()

        optimizer.step()
        lr_scheduler.step()
        optimizer.zero_grad()
        progress_bar.update(1)
    file = f"codet5_{save_field}_epoch_{epoch}.pt"
    print (f"Saving model to {file}")
    torch.save(model.state_dict(), file)

