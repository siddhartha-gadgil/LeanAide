import subprocess  
import sys  
import ast
import json  
import argparse
sys.path.append("/home/ayushagrawal/FSTAR/AI4F-star")
from openai_query import chat
import os

fixed_prompts = 

def run_cmd_elaborate(jsonl_file,data_type):
    try:  
        elaborated = subprocess.check_output(["lake","exe","bulkelab","--query_data",jsonl_file,data_type,"-d","0"], stderr=subprocess.STDOUT, universal_newlines=True)  
    except subprocess.CalledProcessError as e:  
        elaborated = e.output  
    with open(jsonl_file.replace(".jsonl",".txt"),"w") as f:
        f.write(elaborated)
  
def run_cmd_prompts(nl_stmt,num):  
    try:  
        prompts = subprocess.check_output(["lake","exe","nearest_embeddings_full",nl_stmt,str(num)], stderr=subprocess.STDOUT, universal_newlines=True)  
    except subprocess.CalledProcessError as e:  
        prompts = e.output  
    print("done",nl_stmt)
    return prompts  

def prompt_create(nl_stmt,prompts):
    #print(prompts)
    prompts = json.loads(prompts)
    prompt = ""
    for entry in prompts:
        cur_prompt = f"""/-- {entry["docString"].strip()} -/
theorem {entry["theorem"].strip()} :=

"""
        prompt = prompt + cur_prompt
    add_nl_stmt = f"""/-- {nl_stmt.strip()} -/
theorem"""
    prompt = prompt + add_nl_stmt
    return prompt

def run_model(model,temperature,max_tokens,stop,num_gen,load_path):
    # parser = argparse.ArgumentParser()
    # parser.add_argument("--model","-m",type=str,required=True,help="path to model")
    # parser.add_argument("--temperature","-t",type=float,default=0.8,help="temperature")
    # parser.add_argument("--max_tokens","-max_t",type=int,default=500,help="max_tokens")
    # parser.add_argument("--stop","-stop",type=str,default=":=",help="stop token")
    # parser.add_argument("--load_path","-l",type=str,required=True,help="path to load json file")
    # parser.add_argument("--save_path","-s",type=str,required=True,help="path to save directory")
    # parser.add_argument("--num","-n",type=int,required=True,help="number of outputs to generate")
    # parser.add_argument("--data_type","-d",type=str,required=True,help="data type")
    # args = parser.parse_args()
    stmt_json = json.load(open(load_path,"r"))
    res = []
    for i,entry in enumerate(stmt_json):
        stmt = entry["stmt"]
        prompt = prompt_create(stmt,entry["prompts"])
        entry["prompt_cons"] = prompt
        messages = [{"role" : "system", "content" : "You are a coding assistant who translates from natural language to Lean Theorem Prover code following examples. Follow EXACTLY the examples given"},{"role" : "user", "content" : prompt}]
        entry["choices"] = chat(model,messages,temperature,num_gen,max_tokens,stop)
        res.append(entry)
        print("done",i)
    with open(load_path.replace(".json","_results.json"),"w") as f:
        json.dump(res,f,indent=2,ensure_ascii=False)

def save_prompts_jsons(load_path,save_path,num_prompts,prompt_type):
    # parser = argparse.ArgumentParser()
    # parser.add_argument("--load_path","-l",type=str,required=True,help="path to log directory")
    # parser.add_argument("--save_path","-s",type=str,required=True,help="path to save directory")
    # parser.add_argument("--num","-n",type=int,required=True,help="number of prompts to generate")
    # args = parser.parse_args()
    stmts = open(load_path,"r").readlines()
    res = []
    for stmt in stmts:
        stmt = stmt.strip()
        if stmt == "":
            continue
        
        prompts =  run_cmd_prompts(stmt,num_prompts)
        res.append({"stmt":stmt,"prompts":prompts})
    os.makedirs(os.path.dirname(save_path), exist_ok=True)
    with open(save_path,"w") as f:
        json.dump(res,f,indent=2)

def json_to_jsonl(load_path):
    #parser = argparse.ArgumentParser()
    #parser.add_argument("--load_path","-l",type=str,required=True,help="path to json file")
    # Load the JSON data as a list of dictionaries
    #args = parser.parse_args()
    with open(load_path, 'r') as f:
        data = json.load(f)

    # Dump each dictionary to a file with a newline character
    with open(load_path.replace("json","jsonl"), 'w') as f:
        for item in data:
            json.dump({"docString" : item["stmt"], "choices" : item["choices"]}, f, ensure_ascii=False)
            f.write('\n')


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--load_path","-l",type=str,required=True,help="path to log directory")
    parser.add_argument("--save_path","-s",type=str,required=True,help="path to save directory")
    parser.add_argument("--num_prompts","-np",type=int,required=True,help="number of prompts to generate")
    parser.add_argument("--model","-m",type=str,required=True,help="path to model")
    parser.add_argument("--temperature","-t",type=float,default=0.8,help="temperature")
    parser.add_argument("--max_tokens","-max_t",type=int,default=500,help="max_tokens")
    parser.add_argument("--stop","-stop",type=str,default=":=",help="stop token")
    parser.add_argument("--num_gen","-ng",type=int,required=True,help="number of outputs to generate")
    parser.add_argument("--data_type","-d",type=str,required=True,help="data type")
    parser.add_argument("--prompt_type","-pt",type=str,required=True,help="prompt type")
    
    args = parser.parse_args()
    save_prompts_jsons(args.load_path,args.save_path,args.num_prompts)
    # #model,temperature,max_tokens,stop,prompt,num_gen,load_path
    run_model(args.model,args.temperature,args.max_tokens,args.stop,args.num_gen,args.save_path)
    json_to_jsonl(args.save_path.replace(".json","_results.json"))
    #run_cmd_elaborate(args.save_path.replace(".json","_results.jsonl"),args.data_type)
    

if __name__ == "__main__": 
    #save_prompts_jsons() 
    #run_model()
    #json_to_jsonl()
    main()
