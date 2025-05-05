import json
import socket
from flask import Flask,render_template
from flask import request
from embed_picker import *
from keyword_extractor import *


app = Flask(__name__)

@app.route("/")
def index():
   
    return (
        """<html><body>Hello World</body></html>"""
    )


@app.route('/nearest_prompts', methods=['POST'])
def tactic_prompts():
    data = str(request.data, 'utf-8')
    js_query = json.loads(data)
    print(js_query)
    field = js_query["field"]
    prompt_core = js_query[field]
    filename = js_query["filename"]
    model = js_query["model"]
    n = js_query["n"]
    embs, data = load_embeddings('../' + filename, field, model)
    choices = closest_embeddings(prompt_core, model, embs, data, n)
    log_json = {"query": js_query,  "choices": choices}
    log_string = json.dumps(log_json, ensure_ascii=False).replace('\n', '\\n')
    hostname = socket.gethostname()
    with open("logs-" + hostname + ".jsonl", "a") as myfile:
        myfile.write(log_string+'\n')
    return json.dumps(choices, ensure_ascii=False)

@app.route('/keywords', methods=['POST'])
def keywords():
    data = str(request.data, 'utf-8')
    # print(data)
    keywords_with_scores = extract_keywords(data)
    
    # for (kw, score) in keywords_with_scores:
    #     print(kw, score)
     
    return json.dumps(keywords_with_scores, ensure_ascii=False) 

if __name__ == "__main__":
    app.run(host="127.0.0.1", port=5000, debug=True)
