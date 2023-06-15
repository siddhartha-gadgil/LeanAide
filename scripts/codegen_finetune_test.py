import torch

from transformers import AutoModelForCausalLM, AutoTokenizer

checkpoint = "rawdata/idstrings_codegen_350/trained_model"
tokenizer = AutoTokenizer.from_pretrained("Salesforce/codegen-350M-mono")
tokenizer.add_special_tokens({'pad_token': '[PAD]'}) 

model = AutoModelForCausalLM.from_pretrained(checkpoint)
model = model.cuda()
device = torch.device("cuda") 


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
    input_ids = tokenizer(input, return_tensors='pt').input_ids.to(device)
    completion_tokens = model.generate(
        input_ids,
        do_sample=True,
        temperature=temperature,
        num_return_sequences=num_return_sequences,
        max_length=max_length,
        # pad_token_id=tokenizer.pad_token_id
    )
    completion_text = tokenizer.batch_decode(completion_tokens, skip_special_tokens=True)
    print (completion_text)
    gen_text = [t[len(input):] for t in completion_text]
    prompts = [t[:len(input)] for t in completion_text]
    return (gen_text, prompts)

coverage_list=[]
efficiency_list=[]
count = 0
covered = 0

with open('rawdata/premises/identifiers/codegen_test_data.jsonl', 'w', encoding='utf-8') as f:
    for d in test_ids:
        (gens, prompts) = generate_ids(d['theorem'])
        d['generated'] = gens
        # d['prompts'] = prompts
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



