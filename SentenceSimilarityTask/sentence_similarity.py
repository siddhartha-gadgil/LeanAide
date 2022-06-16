#https://www.sbert.net/
#

from sentence_transformers import SentenceTransformer, util

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
        print("Info for {}".format(sentence_pair_list[0]))
        print("Print token ids..")
        inp_ids0 = model.tokenizer(sentence_pair_list[0]).input_ids
        print(inp_ids0,"\n")
        print("Print the tokens mapped to the ids (to detect UNKOWN tokens)..")
        tokens0 = model.tokenizer.convert_ids_to_tokens(inp_ids0)
        print(tokens0,"\n")
        print("Size of embedding vector..")
        print(emb_1.shape[0],"\n")

        print("Info for {}".format(sentence_pair_list[1]))
        print("Print token ids..")
        inp_ids1 = model.tokenizer(sentence_pair_list[1]).input_ids
        print(inp_ids1,"\n")
        print("Print the tokens mapped to the ids (to detect UNKOWN tokens)..")
        tokens1 = model.tokenizer.convert_ids_to_tokens(inp_ids1)
        print(tokens1,"\n")
        print("Size of embedding vector..")
        print(emb_2.shape[0],"\n")

    return sim_score


def main():
    #Examples to check
    sentences = [
                    ["I'm happy", "I'm full of happiness"],
                    #["α : Type,	p : parser α	⊢ p.bind parser.pure = p", "I am happy"],
                    ["α : Type,	p : parser α    \u22A2 p.bind parser.pure = p", "I am happy"], #unknown for	'⊢' 
                    ["Multiplication of two with two is always four","two times two gives four"],
                    ["Multiplication of two with two is always four","2 times 2 gives 4"],
                    ["2 is a prime number","2 is divisible by every natural number other than 1 and 2"]
                ]
    #Select Model
    model_name = 'sentence-transformers/all-MiniLM-L6-v2' 
    model = SentenceTransformer(model_name)
    for i in range(len(sentences)):
        sim_score = calc_similarity(sentences[i], model)
        print("score: {}".format(sim_score))
        print("========================================")

main()


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
