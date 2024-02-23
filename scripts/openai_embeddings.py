import json
# import openai
from queries import azure_embed

inp = open("resources/mathlib4-prompts.json", 'r', encoding='utf-8')
out = open("rawdata/mathlib4-prompts-embeddings.json", 'w', encoding='utf-8')

# read `inp` and extract json
js = json.load(inp)
count = 0
print(len(js))
# for each line, compute the embeddings
for l in js:
    # response = openai.Embedding.create(
    # input=l["docString"],
    # model="text-embedding-ada-002"
    # )
    # embedding = response['data'][0]['embedding']
    embedding = azure_embed(l["docString"])
    l["embedding"] = embedding
    print(l["docString"])
    count = count + 1
    print(count)

# write the embeddings to `out`
json.dump(js, out, indent=4, ensure_ascii=False)
# close `inp` and `out`
inp.close()
out.close()