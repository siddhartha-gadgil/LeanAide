import sys
sys.path.append("F:/ATP_WORK/ATP-Project/SentenceSimilarityTask/")
sys.path.append("F:/ATP_WORK/ATP-Project/OpenaiModelPrompting/NL_to_Lean_exp1/")
import json
import prompt_design
import codex_access_utils
from flask import Flask,render_template
from flask import request
import pickle
from sentence_similarity import *

app = Flask(__name__)

# class ItemTable(Table):
#     name = Col('score')
#     description = Col('dct')


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
    main_prompt = str(request.data)
    #return main_prompt
    # data = request.json
    # main_prompt = data["prompt"]
    #k = data["k"]
    #lis = similar_from(main_prompt,k)
    corpus_embeddings = None
    embedding_path = "F:/ATP_WORK/ATP-Project/SentenceSimilarityTask/embeddings_store/all-mpnet-base-v2.pkl"
    with open(embedding_path, "rb") as fIn:
            stored_data = pickle.load(fIn)
            corpus_embeddings = stored_data['embeddings'] 

    query = prompt_design.retrieve_k_few_shot_prompts(main_prompt,
        corpus_path="F:/ATP_WORK/ATP-Project/data/clean_prompts.json",
        top_k=4,
        model_name = 'sentence-transformers/all-mpnet-base-v2',
        use_precomputed_embeddings=True,
        use_theorem_name=False,
        corpus_embeddings=corpus_embeddings)
    
    #return query
    query_parameters = {'model': 'code-davinci-002','temperature':0.2,'max_tokens':150,'stop': ':=','n':3}
    #return query_parameters
    query_parameters["prompt"] = query[0]
    ret = codex_access_utils.codex_run(query_parameters)
    output = json.loads(ret.stdout.decode("utf-8"))
    return str(output["choices"])

    


    #return json.loads(ret.stdout.decode("utf-8"))

def process(lis):
    ans = ""
    for ind,ele in enumerate(lis):
        ans = ans + "#{}".format(ind+1)
        lis = process_output(ele)
        ans = ans + render_template('print_list.html',options = lis)
    return ans

def process_output(dct):
    return ["score: "+str(dct['score']), "doc_string: "+dct['dct']['doc_string'], "statement: "+dct['dct']['statement']]

def similar_from(main_prompt,k):

    try:
        corpus_embeddings = None
        embedding_path = "F:/ATP_WORK/ATP-Project/SentenceSimilarityTask/embeddings_store/all-mpnet-base-v2.pkl"
        with open(embedding_path, "rb") as fIn:
            stored_data = pickle.load(fIn)
            corpus_embeddings = stored_data['embeddings'] 

        lis = retrieve_similar_k_stats(main_prompt,
        corpus_path="F:/ATP_WORK/ATP-Project/data/clean_prompts.json",
        top_k=k,
        model_name = 'sentence-transformers/all-mpnet-base-v2',
        use_precomputed_embeddings=True,
        corpus_embeddings=corpus_embeddings)

        return lis
    except ValueError:
        return "Invalid Value"

if __name__ == "__main__":
    app.run(host="127.0.0.1", port=8080, debug=True)