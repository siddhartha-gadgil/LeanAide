import json
from openai import OpenAI


def ada_embeddings():
    client = OpenAI()

    with open("resources/mathlib4-prompts.json", 'r', encoding='utf-8') as inp, open("rawdata/mathlib4-prompts-embeddings.json", 'w', encoding='utf-8') as out:
        js = json.load(inp)
        count = 0
        print(len(js))

        # for each line, compute the embeddings
        for l in js:
            response = client.embeddings.create(
                input=l["docString"],
                model="text-embedding-ada-002",
            )
            embedding = response.data[0].embedding
            l["embedding"] = embedding
            print(l["docString"])
            count = count + 1
            print(f"Completed {count} out of {len(js)}")

        # write the embeddings to `out`
        json.dump(js, out, indent=4, ensure_ascii=False)


def small_embeddings_prompt():
    client = OpenAI()
    out_lines = []
    count = 0

    with open("resources/mathlib4-prompts.json", 'r', encoding='utf-8') as inp, open("rawdata/mathlib4-docStrings-small-embeddings.json", 'w', encoding='utf-8') as out:
        js = json.load(inp)
        for l in js:
            response = client.embeddings.create(
                input=l["docString"],
                model="text-embedding-3-small",
                # dimensions = 256
            )
            embedding = response.data[0].embedding
            l["embedding"] = embedding
            out_lines.append(l)
            count = count + 1
            print(l["docString"])
            print(f"Completed {count} out of {len(js)}")
        
        json.dump(out_lines, out, indent=4, ensure_ascii=False)


def small_embeddings_descs():
    client = OpenAI()
    out_lines = []
    count = 0

    with open("rawdata/mathlib4-descs-embeddings-small.json", 'w', encoding='utf-8') as out:
        with jsonlines.open("resources/mathlib4-descs.jsonl", 'r') as reader:
            for l in reader:
                for field in ["description", "concise-description"]:
                    if field in l and l[field]:
                        response = client.embeddings.create(
                            input=l[field],
                            model="text-embedding-3-small"
                        )
                        embedding = response.data[0].embedding
                        l[field + "-embedding"] = embedding
                        print("Field: ", field)
                        print(l[field])
                    else:
                        print(f"Field {field} not found")
                out_lines.append(l)
                count = count + 1
                print(f"Completed {count}")
            json.dump(out_lines, out, indent=4, ensure_ascii=False)
