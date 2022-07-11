#https://www.sbert.net/
#

from sentence_transformers import SentenceTransformer, util
import torch
import json
import pickle
import time
#from KNN_search import *

def sentence_tokenize_info(sentence,model):
        print("Info for {}".format(sentence))
        print("Print token ids..")
        inp_ids = model.tokenizer(sentence).input_ids
        print(inp_ids,"\n")
        print("Print the tokens mapped to the ids (to detect UNKOWN tokens)..")
        tokens = model.tokenizer.convert_ids_to_tokens(inp_ids)
        print(tokens,"\n")

def calc_similarity(sentence_pair_list,model,check=True):
    """
    sentence_pair : list having pair of sentences to compute similarity
    model = language model being used to generate the embeddings
    check = bool flag to check the token-ids and mapped tokens
    """

    emb_1 = model.encode(sentence_pair_list[0],convert_to_tensor=True)
    emb_2 = model.encode(sentence_pair_list[1],convert_to_tensor=True)

    #compute cosine similarities of embeddings
    sim_score = (util.pytorch_cos_sim(emb_1, emb_2)).item()

    #check flag boolean to check the token-ids and mapped tokens
    if check:
        sentence_tokenize_info(sentence_pair_list[0], model)
        print("Size of embedding vector..")
        print(emb_1.shape[0],"\n")
        sentence_tokenize_info(sentence_pair_list[1], model)
        print("Size of embedding vector..")
        print(emb_2.shape[0],"\n")

    return sim_score


def test_similarity():
    #Examples to check
    sentences = [
                    ["I'm happy", "I'm full of happiness"],
                    ["α : Type,	p : parser α	⊢ p.bind parser.pure = p", "I am happy"],
                    #["α : Type,	p : parser α    \u22A2 p.bind parser.pure = p", "I am happy"], #unknown for	'⊢' 
                    ["Multiplication of two with two is always four","two times two gives four"],
                    ["Multiplication of two with two is always four","2 times 2 gives 4"],
                    ["2 is a prime number","2 is divisible by every natural number other than 1 and 2"],
                    ["a ≤ b → a + c ≤ b + c","a ≤ b ∧ c > 0 → a*c ≤ b*c"]
                ]
    #Select Model
    #model_name = 'sentence-transformers/all-MiniLM-L6-v2'
    model_name = 'sentence-transformers/all-mpnet-base-v2' 
    model = SentenceTransformer(model_name)
    for i in range(len(sentences)):
        sim_score = calc_similarity(sentences[i], model)
        print("score: {}".format(sim_score))
        print("========================================")

def test_tokenize_info():
    model_name = 'sentence-transformers/all-mpnet-base-v2' 
    model = SentenceTransformer(model_name)
    fread = open("/home/t-agrawala/Desktop/ATP-Project/SentenceSimilarityTask/lean_notations.txt")
    ex_lis = fread.readlines()
    for ex in ex_lis:
        sentence_tokenize_info(ex, model)
        print("============================================")

def write_prompts_to_file():
    fread = open("/home/t-agrawala/Desktop/ATP-Project/data/prompts.json","r")
    lis = json.load(fread)
    fwrite = open("prompt_lists.txt","a+")
    for dct in lis:
        fwrite.write(dct['doc_string']+"\n")
    fwrite.close()
    fread.close()

def test_similarity_with_data():
    model_name = 'sentence-transformers/all-mpnet-base-v2'
    fread = open("/home/t-agrawala/Desktop/ATP-Project/SentenceSimilarityTask/prompt_lists.txt")
    prompt_corpus = fread.readlines()
    model = SentenceTransformer(model_name)
    corpus_embeddings = model.encode(prompt_corpus, convert_to_tensor=True)
    num_prompts_to_analyse = 20
    top_k = 10
    for prompt in prompt_corpus[:num_prompts_to_analyse]:
        query_embedding = model.encode(prompt, convert_to_tensor=True)
        cos_scores = util.cos_sim(query_embedding, corpus_embeddings)[0]
        top_results = torch.topk(cos_scores, k=top_k)

        print("\n\n======================\n\n")
        print("PROMPT:", prompt)
        print("\nTop {} most similar prompts from the entire corpus:".format(top_k))

        for score, idx in zip(top_results[0], top_results[1]):
            print(prompt_corpus[idx].rstrip("\n"), "(Score: {:.4f})".format(score))

    """
    # Alternatively, we can also use util.semantic_search to perform cosine similarty + topk
    hits = util.semantic_search(query_embedding, corpus_embeddings, top_k=5)
    hits = hits[0]      #Get the hits for the first query
    for hit in hits:
        print(corpus[hit['corpus_id']], "(Score: {:.4f})".format(hit['score']))
    """

def retrieve_similar_k_stats(main_prompt,
    corpus_path="/home/t-agrawala/Desktop/ATP-Project/data/clean_prompts.json",
    top_k=4,
    model_name = 'sentence-transformers/all-mpnet-base-v2',
    use_precomputed_embeddings=None,
    #embedding_store_path = "/home/t-agrawala/Desktop/ATP-Project/SentenceSimilarityTask/embeddings_store/"
    corpus_embeddings = None):

    fread = open(corpus_path,"r",encoding="utf-8")
    prompt_corpus = json.load(fread)
    model = SentenceTransformer(model_name,device='cpu')
    #corpus_embeddings = None
    #TODO optimization here, do one-time loading in the main method DONE for the sentence-similarity one
    # if use_precomputed_embeddings and embeddings is not None :
    #     embedding_path = embedding_store_path+model_name.split('/')[-1]+".pkl"
    #     with open(embedding_path, "rb") as fIn:
    #         stored_data = pickle.load(fIn)
    #         #stored_sentences = stored_data['sentences']
    #         corpus_embeddings = stored_data['embeddings']      
    if corpus_embeddings is None and use_precomputed_embeddings == False:
        prompts = [stats["doc_string"] for stats in prompt_corpus]
        corpus_embeddings = model.encode(prompts, convert_to_tensor=True)
    
    query_embedding = model.encode(main_prompt, convert_to_tensor=True)
    cos_scores = util.cos_sim(query_embedding.to('cpu'),corpus_embeddings.to('cpu'))[0]
    top_results = torch.topk(cos_scores.to('cpu'),k=top_k)
    top_results = top_results
    result_lis = []
    for score, idx in zip(top_results[0],top_results[1]):
        result = {}
        result['score'] = score.item()
        # print(prompts[idx])
        result['dct'] = prompt_corpus[idx]
        result_lis.append(result)

    return result_lis

def save_corpus_embeddings(corpus_path="/home/t-agrawala/Desktop/ATP-Project/data/clean_prompts.json",out_path = "/home/t-agrawala/Desktop/ATP-Project/SentenceSimilarityTask/embeddings_store/",model_name='sentence-transformers/all-mpnet-base-v2'):
    out_path = out_path + model_name.split('/')[-1]+".pkl"
    fread = open(corpus_path,"r",encoding="utf-8")
    prompt_corpus = json.load(fread) #Do we need to worry about the order?
    model = SentenceTransformer(model_name,device='cpu')
    prompts = [stats["doc_string"] for stats in prompt_corpus]
    corpus_embeddings = model.encode(prompts, convert_to_tensor=True)
    with open(out_path, "wb") as fOut:
        pickle.dump({'corpus_path':corpus_path,'sentences': prompts,'embeddings':corpus_embeddings}, fOut, protocol=pickle.HIGHEST_PROTOCOL)

#test_similarity_with_data()

save_corpus_embeddings(corpus_path="F:\ATP_WORK\ATP-Project\data\clean_prompts.json",out_path = "F:\\ATP_WORK\\ATP-Project\\SentenceSimilarityTask\\embeddings_store\\")

# main_prompt = "For any propositions `P` and `A`, `P` follows from `A` under the assumption that `P` is true."
# r1 = retrieve_similar_k_stats(main_prompt,use_precomputed_embeddings=True)
# for s in r1:
#     print(s['dct']["doc_string"])
# print("====================================")
# ret = convert_to_Dataset()
# samples = faiss_sample(ret, main_prompt)
# for s in samples['info']:
#     print(s["doc_string"])

# r2 = retrieve_similar_k_stats(main_prompt)
# print(r2)

#Compute embedding for both lists
#embedding_1= model.encode(sentences[0], convert_to_tensor=True)
#print(embedding_1.shape)
#output1 = model.tokenizer.encode(sentences[0])
#print(output1)
#TODO print(model.tokenize(sentences[0])) #strange output
#inp_ids = model.tokenizer(sentences[0]).input_ids
#print(inp_ids)
#print(model.tokenizer.convert_ids_to_tokens(inp_ids))
#print(model.tokens(sentences[0]))
#embedding_2 = model.encode(sentences[1], convert_to_tensor=True)
#print(embedding_2.shape)
#print(embedding_1)
#print(embedding_2)
#print(util.pytorch_cos_sim(embedding_1, embedding_2))
#test_similarity()