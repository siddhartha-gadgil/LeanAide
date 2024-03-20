# Load model directly
from transformers import AutoTokenizer, AutoModelForCausalLM
import json
from random import sample
import sys

# model_id= "morph-labs/morph-prover-v0-7b"
model_id = sys.argv[1]
tokenizer = AutoTokenizer.from_pretrained(model_id)
model = AutoModelForCausalLM.from_pretrained(model_id, load_in_8bit=True)

device = 'cuda'
# model = model.to(device)

def preprocess_examples(example):
    # encode the code-docstring pairs
    statement = example['theorem']

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
    input_ids = tokenizer.apply_chat_template(chat, tokenize=True, return_tensors='pt')
    head = tokenizer.apply_chat_template(chat, tokenize=False, return_tensors='pt')
    return input_ids, head

with open('rawdata/premises/doc_lemma_pairs/test.jsonl') as f:
    test_ids = [json.loads(line) for line in f]

test_ids = sample(test_ids, 500) # for testing
print('Test set size:', len(test_ids))

def generate_ids(example, temperature=1.5, num_return_sequences=8, max_length=2048):
    input_ids, head = preprocess_examples(example)
    input_ids = input_ids.to(device)
    gen_tokens = model.generate(
        input_ids,
        do_sample=True,
        temperature=temperature,
        num_return_sequences=num_return_sequences,
        max_length=max_length,
    )
    gen_text = tokenizer.batch_decode(gen_tokens, skip_special_tokens=True)
    print(gen_text)
    gens = [gen[(len(head)-2):] for gen in gen_text]
    print(f"head: {head}")
    print("Lemmmas: ")
    for gen in gens:
        print (gen)
    return gens

count = 0
with open('results/morphprover_finetune_lemmas.jsonl', 'w', encoding='utf-8') as f:
    for d in test_ids:
        gens = generate_ids(d)
        d['generated'] = gens
        f.write(json.dumps(d, ensure_ascii=False) + '\n')
        count += 1
        print (f"count: {count}")
        # if count % 5 == 0:
        #     print(count)
        #     print('theorem:', d['theorem'])
        #     print('Lemmas:\n', json.dumps(gens, ensure_ascii=False, indent=2))
        #     print()
