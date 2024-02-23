import json
from queries import math_terms, repeat_query
import jsonlines

def top_math_terms(statement):
    return math_terms(statement, 1)[0]

js = []
with open("resources/mathlib4-prompts.json", 'r', encoding='utf-8') as inp:
    js = json.load(inp)

def add_terms(start, stop):
    count = 0
    with jsonlines.open('data/mathlib4-prompts-terms.jsonl', mode='a') as writer:
        for l in js[start:stop]:
            print(l["docString"])
            terms = repeat_query(top_math_terms, l["docString"], [], 5, 1)
            l["terms"] = terms
            writer.write(l)
            print(terms)
            count += 1
            print(count)

import sys

def main():
    add_terms(int(sys.argv[1]), int(sys.argv[2]))
    return 0

if __name__ == '__main__':
    sys.exit(main()) 