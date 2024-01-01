import json
# import openai
from queries import math_terms, repeat_query
from time import sleep

inp = open("data/mathlib4-prompts.json", 'r', encoding='utf-8')
out = open("data/mathlib4-prompts-terms.json", 'w', encoding='utf-8')

def top_math_terms(statement):
    return math_terms(statement, 1)[0]

# read `inp` and extract json
js = json.load(inp)
count = 0
print(len(js))
# for each line, compute the terms
for l in js:
    terms = repeat_query(top_math_terms, l["docString"], [], 5, 1)
    l["terms"] = terms
    print(l["docString"])
    print(terms)
    count = count + 1
    print(count)

# write the embeddings to `out`
json.dump(js, out, indent=4, ensure_ascii=False)
# close `inp` and `out`
inp.close()
out.close()