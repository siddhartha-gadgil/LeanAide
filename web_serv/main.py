import sys
sys.path.append("F:/ATP_WORK/ATP-Project/SentenceSimilarityTask/")
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