import json

wiktionary_keywords = open("../../data/wiktionary_mathematics_keywords.txt", "r").read()

mathlib_statements_keywords = json.load(open("../../LeanCodePrompts/KeywordSummary/mathlib_keyword_lookup.json", "r", encoding="utf-8"))

mathlib_keywords = mathlib_statements_keywords.keys()


valid_keywords = open("../../data/valid_keywords.txt", "w")
invalid_keywords = open("../../data/invalid_keywords.txt", "w")


for kw in mathlib_keywords:
    if '_'.join(kw.split(' ')) in wiktionary_keywords:
        valid_keywords.write(kw + '\n')
    else:
        invalid_keywords.write(kw + '\n')