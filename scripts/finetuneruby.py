#!/usr/bin/env python
# coding: utf-8

# This is a slight modification of a notebook for training a CodeT5 model on generating documentation for Ruby code.

from datasets import load_dataset

dataset = load_dataset("code_x_glue_ct_code_to_text", "ruby")
print(dataset)

print("Example of the dataset:")
example = dataset['train'][0]

print("Code:", example["code"])
print("Docstring:", example["docstring"])


# The goal for the model is to generate a docstring based on the provided code. 
# 
# Let's now prepare the examples (i.e. code-docstring pairs) for the model. As you might know, Transformer models like BERT, BART, T5 etc. don't expect text as direct input, but rather integers which are called `input_ids` in HuggingFace Transformers. These represent tokens of a certain vocabulary. The model will learn rich contextual embedding vectors for each token, allowing it to get good results.
# 
# In other words, we need to turn the "Code" input from above into `input_ids`, and similarly, we need to turn the "Docstring" output from above into `input_ids`, which will serve as the `labels` for the model.
# 
# In addition, as these models are trained on batches of examples rather than one example at a time, we'll need to pad/truncate both the inputs and labels, such that they are all of the same length. That's why we also will add an `attention_mask` input to the model, such that it knows not to take into account padding tokens when computing attention scores.
# 
# To summarize: 
# * input: code, which is turned into `input_ids` + `attention_mask`
# * output: docstrings, which are turned into `labels` (which are the `input_ids` of the docstrings).
# 
# Below, we define a `preprocess_examples` function, which we can apply on the entire dataset. 



from transformers import RobertaTokenizer

tokenizer = RobertaTokenizer.from_pretrained("Salesforce/codet5-base")

prefix = "Summarize Ruby: "
max_input_length = 256
max_target_length = 128

def preprocess_examples(examples):
  # encode the code-docstring pairs
  codes = examples['code']
  docstrings = examples['docstring']
  
  inputs = [prefix + code for code in codes]
  model_inputs = tokenizer(inputs, max_length=max_input_length, padding="max_length", truncation=True)

  # encode the summaries
  labels = tokenizer(docstrings, max_length=max_target_length, padding="max_length", truncation=True).input_ids

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

print(dataset)
dataset.set_format(type="torch", columns=['input_ids', 'attention_mask', 'labels'])
train_dataset = dataset['train']
eval_dataset = dataset['test']

from transformers import T5ForConditionalGeneration 
model = T5ForConditionalGeneration.from_pretrained('Salesforce/codet5-base')
model = model.cuda()


import numpy as np
import evaluate

metric = evaluate.load("google_bleu")

def compute_metrics(eval_pred):
    logits, labels = eval_pred
    predictions = np.argmax(logits, axis=-1)
    return metric.compute(predictions=predictions, references=labels)

from transformers import TrainingArguments, Trainer

training_args = TrainingArguments(output_dir="test_trainer", evaluation_strategy="epoch")

trainer = Trainer(
    model=model,
    args=training_args,
    train_dataset=train_dataset,
    eval_dataset= eval_dataset,
    compute_metrics=compute_metrics,
)

trainer.train()
# ## Inference
# 
# Now that we've trained a model, let's test it on some examples from the test set.


from datasets import load_dataset

dataset = load_dataset("code_x_glue_ct_code_to_text", "ruby")
print(dataset['test'])


test_example = dataset['test'][2]
print("Code:", test_example['code'])


# We can load our trained model as follows:

# We can prepare the example using `RobertaTokenizer`, and generate using the `.generate()` method. Note that there are several ways of doing generation (greedy decoding/beam search/top k sampling/etc.), for that I refer to Patrick's blog post which you can find [here](https://huggingface.co/blog/how-to-generate). Here we will just use the default settings (i.e. greedy decoding).



# prepare for the model
input_ids = tokenizer(test_example['code'], return_tensors='pt').input_ids.to('cuda')
# generate
model.eval()
outputs = model.generate(input_ids)
print("Generated docstring:", tokenizer.decode(outputs[0], skip_special_tokens=True))

# Let's compare this to the ground-truth docstring:

print("Ground truth:", test_example['docstring'])

print("Multiple outputs:")

gen_tokens = model.generate(input_ids, do_sample=True,
        temperature=0.8,
        num_return_sequences=5)
gen_text = tokenizer.batch_decode(gen_tokens)
for text in gen_text:
    print(text)
