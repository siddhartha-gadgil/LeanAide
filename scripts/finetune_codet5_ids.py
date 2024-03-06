#!/usr/bin/env python
# coding: utf-8

# This is training of a model for generating lists of identifiers in a proof from the statement in Lean 4.

# This is adapted from a notebook for training a CodeT5 model on generating documentation for Ruby code.


import json
from transformers import TrainingArguments, Trainer
from torch.utils.data import DataLoader
from datasets import load_dataset
import torch
from random import sample

from transformers import T5ForConditionalGeneration, AutoTokenizer

checkpoint = "Salesforce/codet5p-220m"
device = "cuda" # for GPU usage or "cpu" for CPU usage

tokenizer = AutoTokenizer.from_pretrained(checkpoint)
model = T5ForConditionalGeneration.from_pretrained(checkpoint,
                                                   device_map='auto')



dataset = load_dataset(
    'json', data_dir='rawdata/premises/ident_strings', data_files="train.jsonl")
print(dataset)


#
#
# We need to turn the "statement" input from above into `input_ids`, and similarly, we need to turn the "identifiers" output from above into `input_ids`, which will serve as the `labels` for the model.
#
# In addition, as these models are trained on batches of examples rather than one example at a time, we'll need to pad/truncate both the inputs and labels, such that they are all of the same length. That's why we also will add an `attention_mask` input to the model, such that it knows not to take into account padding tokens when computing attention scores.
#
# To summarize:
# * input: statement, which is turned into `input_ids` + `attention_mask`
# * output: ids, which are turned into `labels` (which are the `input_ids` of the docstrings).
#
# Below, we define a `preprocess_examples` function, which we can apply on the entire dataset.


prefix = "Premises: "
max_input_length = 1024
max_target_length = 256


def preprocess_examples(examples):
    # encode the code-docstring pairs
    statements = examples['statement']
    ids = examples['identifiers']

    inputs = [prefix + thm for thm in statements]
    model_inputs = tokenizer(
        inputs, max_length=max_input_length, padding="max_length", truncation=True)

    # encode the summaries
    labels = tokenizer(ids, max_length=max_target_length,
                       padding="max_length", truncation=True).input_ids

    # important: we need to replace the index of the padding tokens by -100
    # such that they are not taken into account by the CrossEntropyLoss
    labels_with_ignore_index = []
    for labels_example in labels:
        labels_example = [label if label !=
                          0 else -100 for label in labels_example]
        labels_with_ignore_index.append(labels_example)

    model_inputs["labels"] = labels_with_ignore_index

    return model_inputs


# Now that we have defined the function, let's call `.map()` on the HuggingFace Dataset object, which allows us to apply this function in batches (by default a batch size of 1,000 is used!) - hence super fast.


dataset = dataset.map(preprocess_examples, batched=True)

# Next, let's set the format to "torch" and create PyTorch dataloaders.

dataset.set_format(type="torch", columns=[
                   'input_ids', 'attention_mask', 'labels'])
train_dataset = dataset['train']
# train_dataset = train_dataset.shuffle(seed=42).select(range(10000)) # for testing



training_args = TrainingArguments(
    output_dir="rawdata/idstrings_codet5p-220m",
    save_strategy="epoch",
    per_device_train_batch_size=4,)

trainer = Trainer(
    model=model,
    args=training_args,
    train_dataset=train_dataset,
)

trainer.train()

model.save_pretrained("rawdata/idstrings_codet5p-220m/trained_model")

train_dataloader = DataLoader(dataset['train'], shuffle=True, batch_size=8)


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
        gens = generate_ids(d['statement'])
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
