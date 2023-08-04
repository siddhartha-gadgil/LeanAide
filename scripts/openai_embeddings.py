import json
import openai

inp = open("data/mathlib4-thms.json", 'r', encoding='utf-8')
out = open("data/mathlib4-thms-embeddings.json", 'w', encoding='utf-8')

# read `inp` and extract json
js = json.load(inp)
count = 0
# for each line, compute the embeddings
for l in js:
    response = openai.Embedding.create(
    input=l["docString"],
    model="text-embedding-ada-002"
    )
    embedding = response['data'][0]['embedding']
    l["embedding"] = embedding
    print(l["docString"])
    count = count + 1
    print(count)

# write the embeddings to `out`
json.dump(js, out, indent=4, ensure_ascii=False)
# close `inp` and `out`
inp.close()
out.close()