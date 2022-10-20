import json
from flask import Flask,render_template
from flask import request
from embed_picker import *

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
    model_name = js_query["model_name"]
    n = js_query["n"]
    embs, data = load_embeddings('../' + filename, field, model_name)
    choices = closest_embeddings(prompt_core, model_name, embs, data, n)
    return json.dumps(choices, ensure_ascii=False)


if __name__ == "__main__":
    app.run(host="127.0.0.1", port=5000, debug=True)
