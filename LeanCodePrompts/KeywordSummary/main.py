import sys
import os
import openai
import keyword_summary_prompts
import json

openai.api_key = os.getenv("OPENAI_API_KEY")

# Query OpenAI Codex
def codex_query(query_prompt:str):
    # Query OpenAI Codex
    return openai.Completion.create(
            model = "text-davinci-002",
            prompt = query_prompt,
            temperature = 1,
            n = 1,
            max_tokens = 150,
            echo = False,
            stop = "\n"
        )

input_prompt = '\n\n'.join(['Statement: ' + stmt + '\nKeywords: ' + ', '.join(kwds) for (stmt, kwds) in keyword_summary_prompts.prompts])

with open("keyword_summary_results.md", "w+") as out:
    out.write("# Keyword summary experiment")
    with open("docstrings.txt", "r") as f:
        docstrs = f.readlines()
        for i, docstr in enumerate(docstrs):
            out.write("\n\n\n## Prompt " + str(i) + '\n')
            prompt = input_prompt + '\n\nStatement: ' + docstr + 'Keywords: '
            print(docstr)
            out.write("\n### Statement" + '\n' + docstr + '\n')
            codex_outputs = codex_query(prompt)
            out.write("### Keywords" + '\n' + codex_outputs["choices"][0].text + '\n')            