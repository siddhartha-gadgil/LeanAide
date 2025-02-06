# Example server for LeanAide

If you wish to use embeddings different from the OpenAI embeddings, for example for a fully open-source solution, you can run an "examples server" and set the parameter `examples_url` to point to it. We provide a basic implementation of this in the `example_server` directory. To start this, run the following:

```bash
cd example_server
python3 prebuild_embeddings
flask run
```

The second command should be run only the first time you set up. Once you start the server, set `examples_url = "localhost:5000/find_nearest"` to use the embedding server.

By default, the embeddings use 'all-MiniLM-L6-v2'. To use a different model, set the environment variable "LEANAIDE_EXAMPLES_MODEL". Specifically, to use 'BAAI/bge-m3' you can set "LEANAIDE_EXAMPLES_MODEL=bge-m3'. However, for other models you should use their full name. You need to run `prebuild_embeddings` (once) after setting the environment variable to ensure the variable with the correct embedding is saved.

## Custom Server

The example server should be as follows:

* A server should be running with a port to which we can POST in Json.
* The post will have three (relevant) fields: 
  * **input**: The statement of a theorem or definition.
  * **prompt_type**: One of `docString`, `description` and `concise-description`. What field to match.
  *  **n**: The number of *nearest embeddings* to return.
* The response gives selected "nearest" examples based on *docString*s from `resources/mathlib4-prompts.jsonl` or *description*s and *concise-description*s from `resources/mathlib4-descs.jsonl`
* The response should be a Json array with the data from the resource files with one modification: the appropriate text should be returned as a field one of "docString", "doc" and "doc_string" (so for the nearest "description" add a "doc" field which is the description).

