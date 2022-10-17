import sys
sys.path.append("../SentenceSimilarityTask/")
import json
from flask import Flask,render_template
from flask import request
import pickle
from sentence_similarity import *
import copy
from embed_picker import *

app = Flask(__name__)

@app.route("/")
def index():
    #main_prompt = "For any propositions `P` and `A`, `P` follows from `A` under the assumption that `P` is true."
    main_prompt = request.args.get("main_prompt", "")
    k = request.args.get("k", "")
    if main_prompt:
        #return main_prompt
        lis = similar_from(main_prompt,int(k))
    else:
        lis = ""
    
    #print(lis)
    return (
        """<form action="" method="get">
                Natural Language Statement of the theorem: <input type="text" name="main_prompt">
                <br> 
                No. of prompts to retrieve (k): <input type="text" name="k">
                <br>
                <input type="submit" value="Search Relevant Prompts">
            </form>"""
        + "Input Dependent Prompts: "
        + "<br>"+ process(lis)
    )


@app.route('/similar_json', methods=['POST'])
def similar_from():
    data = str(request.data, 'utf-8')
    inp = data.split("top_K")
    main_prompt = inp[0]
    k = int(inp[1])
    print(main_prompt)

    #try:
    corpus_embeddings = None
    embedding_path = "../SentenceSimilarityTask/embeddings_store/all-mpnet-base-v2.pkl"
    with open(embedding_path, "rb") as fIn:
            stored_data = pickle.load(fIn)
            corpus_embeddings = stored_data['embeddings'] 

    lis = retrieve_similar_k_stats(main_prompt,
    corpus_path="../data/safe_prompts.json",
    top_k=k,
    model_name = 'sentence-transformers/all-mpnet-base-v2',
    use_precomputed_embeddings=True,
    corpus_embeddings=corpus_embeddings)

    output = [{"statement" : info["dct"]["statement"],"doc_string": info["dct"]["doc_string"], "theorem" : info["dct"]["theorem"], "args" : info["dct"]["args"], "name" : info["dct"]["name"], "type" : info["dct"]["type"]} for info in lis]
    jsBlob = str(json.dumps(output,ensure_ascii=False))
    print (jsBlob)
    return jsBlob

@app.route('/tactic_prompts', methods=['POST'])
def tactic_prompts():
    data = str(request.data, 'utf-8')
    js_query = json.loads(data)
    print(js_query)
    prompt_core = js_query["prompt_core"]
    n = js_query["n"]
    embs, data = load_embeddings('../data/mathlib-thms.json')
    choices = closest_embeddings(prompt_core, embs, data, n)
    return json.dumps(choices, ensure_ascii=False)

def process(lis):
    ans = ""
    for ind,ele in enumerate(lis):
        ans = ans + "#{}".format(ind+1)
        lis = process_output(ele)
        ans = ans + render_template('print_list.html',options = lis)
    return ans

def process_output(dct):
    return ["score: "+str(dct['score']), "doc_string: "+dct['dct']['doc_string'], "statement: "+dct['dct']['statement']]

@app.route('/process_json', methods=['POST'])
def process_similar_from():
    data = str(request.data, 'utf-8')
    inp = data.split("top_K")
    main_prompt = inp[0]
    k = int(inp[1])
    print(main_prompt)

    #try:
    corpus_embeddings = None
    embedding_path = "../SentenceSimilarityTask/embeddings_store/all-mpnet-base-v2.pkl"
    with open(embedding_path, "rb") as fIn:
            stored_data = pickle.load(fIn)
            corpus_embeddings = stored_data['embeddings'] 

    lis = retrieve_similar_k_stats(main_prompt,
    corpus_path="../data/clean_prompts.json",
    top_k=k,
    model_name = 'sentence-transformers/all-mpnet-base-v2',
    use_precomputed_embeddings=True,
    corpus_embeddings=corpus_embeddings)

    output = [{"statement" : info["dct"]["statement"],"doc_string": info["dct"]["doc_string"], "theorem" : info["dct"]["theorem"]} for info in lis]
    prompt = ""
    for line in output:
        prompt = prompt + "/--\n" + line["doc_string"] + "\n-/\n" + line["statement"] + " :=\n\n"
    prompt = prompt + "/--\n" + main_prompt + "\n-/\n"
    
    prompt = prompt + "theorem "
    print(prompt)
    return prompt

if __name__ == "__main__":
    app.run(host="127.0.0.1", port=5000, debug=True)
