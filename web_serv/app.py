import sys
sys.path.append("../OpenaiModelPrompting/")
import json
import NL_to_Lean_exp1.prompt_design
import codex_access_utils
from flask import Flask,render_template
from flask import request
import pickle
from sentence_similarity import *
import copy

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

# ...
@app.route('/post_json', methods=['POST'])
def process_json():
    main_prompt = str(request.data, 'utf-8')
    print
    print("\nNatural language for term/type/prop:") 
    print (main_prompt)
    #return main_prompt
    # data = request.json
    # main_prompt = data["prompt"]
    #k = data["k"]
    #lis = similar_from(main_prompt,k)
    corpus_embeddings = None
    embedding_path = "../SentenceSimilarityTask/embeddings_store/all-mpnet-base-v2.pkl"
    with open(embedding_path, "rb") as fIn:
            stored_data = pickle.load(fIn)
            corpus_embeddings = stored_data['embeddings'] 

    query = NL_to_Lean_exp1.prompt_design.retrieve_k_few_shot_prompts(main_prompt,
        corpus_path="../data/clean_prompts.json",
        top_k=4,
        model_name = 'sentence-transformers/all-mpnet-base-v2',
        use_precomputed_embeddings=True,
        use_theorem_name=False,
        corpus_embeddings=corpus_embeddings)
    print("\nQuery to Codex (with input-dependent prompts):")
    print (query[0])
    #return query
    query_parameters = {'model': 'code-davinci-002','temperature':0.0,'max_tokens':150,'stop': ':=','n':5}
    #return query_parameters
    query_parameters["prompt"] = query[0]
    ret = codex_access_utils.codex_run(query_parameters)
    output = json.loads(ret.stdout.decode("utf-8"))
    ans = copy.deepcopy(output["choices"])
    # for i,line in enumerate(ans):
    #     ans[i]["text"] = line["text"].replace("\'","\"")

    jsBlob = str(json.dumps(output["choices"],ensure_ascii=False))
    print
    print("\nOutput:")
    print (jsBlob)
    return jsBlob
    #return str(ans)
    #return json.loads(ret.stdout.decode("utf-8"))

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
    corpus_path="../data/clean_prompts.json",
    top_k=k,
    model_name = 'sentence-transformers/all-mpnet-base-v2',
    use_precomputed_embeddings=True,
    corpus_embeddings=corpus_embeddings)

    output = [{"statement" : info["dct"]["statement"],"doc_string": info["dct"]["doc_string"], "theorem" : info["dct"]["theorem"]} for info in lis]
    jsBlob = str(json.dumps(output,ensure_ascii=False))
    print (jsBlob)
    return jsBlob

def process(lis):
    ans = ""
    for ind,ele in enumerate(lis):
        ans = ans + "#{}".format(ind+1)
        lis = process_output(ele)
        ans = ans + render_template('print_list.html',options = lis)
    return ans

def process_output(dct):
    return ["score: "+str(dct['score']), "doc_string: "+dct['dct']['doc_string'], "statement: "+dct['dct']['statement']]



if __name__ == "__main__":
    app.run(host="127.0.0.1", port=5000, debug=True)
