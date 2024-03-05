import jsonlines

def filter_terms(set='train'):
    examples = []
    rejected = 0
    with jsonlines.open(f'rawdata/premises/term_pairs/{set}.jsonl') as reader:
        for obj in reader:
            term = obj['term']
            thm = obj['theorem']
            context = obj['term_context']
            if (term not in thm) and (term not in context):
                examples.append(obj)
            else:
                rejected += 1
    print(f'Rejected {rejected} examples')
    print(f'Kept {len(examples)} examples')  
    with jsonlines.open(f'rawdata/premises/term_pairs/{set}_filtered.jsonl', 'w') as writer:
        writer.write_all(examples)

filter_terms(set='train')
filter_terms(set='test')
filter_terms(set='valid')