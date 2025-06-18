import base64
import json
import os

import pymupdf
import streamlit as st
from dotenv import load_dotenv
from openai import OpenAI

from llm_prompts import thmpf_prompt, soln_from_image_prompt, mathpaper_prompt
from serv_utils import SCHEMA_JSON, HOMEDIR

load_dotenv(os.path.join(HOMEDIR, ".env"))

provider_info = {
    "OpenAI": {
        "name": "OpenAI",
        "default_model": "o4-mini",
        "api_key": os.getenv("OPENAI_API_KEY", "Key Not Found"),
    },
    "Gemini": {
        "name": "Gemini",
        "default_model": "gemini-1.5-pro",
        "api_key": os.getenv("GEMINI_API_KEY", "Key Not Found"),
    },
    "OpenRouter": {
        "name": "OpenRouter",
        "default_model": "gpt-4o",
        "api_key": os.getenv("OPENROUTER_API_KEY", "Key Not Found"),
    },
    "DeepInfra": {
        "name": "DeepInfra",
        "default_model": "deepseek-ai/DeepSeek-R1-0528",
        "api_key": os.getenv("DEEPINFRA_API_KEY", "Key Not Found"),
    }
}

# Extract API keys for backwards compatibility
OPENAI_API_KEY = provider_info["OpenAI"]["api_key"]
GEMINI_API_KEY = provider_info["Gemini"]["api_key"]
OPENROUTER_API_KEY = provider_info["OpenRouter"]["api_key"]
DEEPINFRA_API_KEY = provider_info["DeepInfra"]["api_key"]

openai_client = OpenAI(api_key=OPENAI_API_KEY)
gemini_client = OpenAI(api_key=GEMINI_API_KEY, base_url="https://generativelanguage.googleapis.com/v1beta/openai/")
openrouter_client = OpenAI(api_key=OPENROUTER_API_KEY, base_url="https://openrouter.ai/api/v1")
deepinfra_client = OpenAI(api_key=DEEPINFRA_API_KEY, base_url="https://api.deepinfra.com/v1/openai")

def match_provider_client(provider: str = "openai"):
    provider = provider.lower()
    if provider == "openai":
        return openai_client
    elif provider == "gemini":
        return gemini_client
    elif provider == "openrouter":
        return openrouter_client
    elif provider == "deepinfra":
        return deepinfra_client
    else:
        return openai_client  # Default to OpenAI if provider is not recognized


## Get model list supported by API KEY
def get_supported_models(provider):
    """
    Get the list of models supported by the OpenAI API key.
    """
    client = match_provider_client(provider)
    try:
        models = client.models.list()
        return [model.id for model in models.data]
    except Exception as e:
        st.error(f"Error fetching models: {e}")
        return []

def get_pdf_id(pdf_path: str, provider: str = "openai"):
    client = match_provider_client(provider)
    file = client.files.create(
        file=open(pdf_path, "rb"),
        purpose="user_data"
    )
    return file

## Images
def encode_image(image_path):
  with open(image_path, "rb") as image_file:
    return base64.b64encode(image_file.read()).decode('utf-8')

def image_solution(image_path: str, provider = "openai", model: str = "gpt-4o"):
    image_encoded = encode_image(image_path) 
    prompt = "Extract text using LaTeX from the given mathematics as images. DO NOT include any other text in the response. Do not write extra proofs or explanations."

    client = match_provider_client(provider)
    response = client.chat.completions.create(
        model=model,
        messages=[
            {
                "role": "user",
                "content": [
                    {
                        "type": "text",
                        "text": prompt,
                    },
                    {
                        "type": "image_url",
                        "image_url": {
                            "url":  f"data:image/jpeg;base64,{image_encoded}"
                        },
                    },
                ],
            }
        ],
        temperature=0.0,
    )

    response_txt = response.choices[0].message.content
    if response_txt is None or response_txt == "":
        return "No response from model while extracting text from image"
    if response_txt:
        response_txt = response_txt.strip("```latex").strip("```")
    return response_txt

def solution_from_images(image_paths, provider = "openai", model: str = "gpt-4o"):
    combined_text = ""
    for image_path in image_paths:
        response = image_solution(image_path)
        combined_text += str(response)

    return str(model_response_gen(soln_from_image_prompt(combined_text), provider=provider, model=model))

## PDF
def extract_text_from_pdf(path: str) -> str:
    """Extract text from a PDF file."""
    with pymupdf.open(path) as doc:  # open document
        text = chr(12).join([page.get_text() for page in doc])
    return text

def model_response_gen(prompt:str, task:str = "", provider = "openai", model:str ="gpt-4o", json_output: bool = False, json_schema = SCHEMA_JSON, pdf_val = None, paper_input: bool = False):
    """
    GPT response generator function.
    Args:
        prompt (str): The prompt to send to the GPT model.
        task (str): Optional system message to set the context for the model.
        json_output (bool): Whether to format the response as JSON, else text.
        json_schema (dict): The JSON schema to use for the response format.
        model (str): The model to use for generating the response.
        provider (str): The provider to use for the model (e.g., "openai", "gemini", "openrouter", "deepinfra").
        pdf_val (str or OpenAI File object): The PDF content or OpenAI File object to be used in the prompt.
        paper_input (bool): Whether the input is a paper (True) or non-paper (False). If True, pdf_val is expected to be an OpenAI File object.
    """
    messages = []
    if task != "":
        messages.append({
            "role": "system",
            "content": task
        })
    messages.append({
        "role": "user",
        "content": prompt,
    })
    
    ## Case 1. In case of non paper, the pdf/non-pdf content is passed in prompt.
    ## Case 2. In case of paper, the non pdf content is passed in prompt.
    ## Case 3. In case of paper, the pdf_val is the OpenAI File object.
    if type(pdf_val) is not type("") and not paper_input:
        pass # Case 1
    elif type(pdf_val)!= type("") and paper_input: # Case 3
        # pdf_text is not string but OpenAi File object
        pdf_id = pdf_val.id
        messages.append({
            "role": "user",
            "content": {
                "type": "file",
                "file": {
                    "file_id": pdf_id,  
                }
            }
        }) 

    client = match_provider_client(provider)
    if json_output:
        response = client.chat.completions.create(
                model=model,
                messages=messages,
                response_format= {"type": "json_object"}
                # This wont work for complex schema
                # response_format={
                #     "type": "json_schema",
                #     "json_schema": {
                #         "name": "LeanAide_PaperStructure",
                #         "schema": json_schema,
                #         "strict": True
                #     }
                # }
        ) 
        
    else:
        response = client.chat.completions.create(
            model=model,
            messages=messages,
        )
    if response is None:
        return "No response from model."

    return response.choices[0].message.content

    
def gen_thmpf_json(thm: str, pf: str, provider = "openai", model: str = "gpt-4o"):
    response = model_response_gen(
        thmpf_prompt(thm, pf),
        json_output = True, 
        provider = provider,
        model = model
    )
    # response = json.dumps({"x": 1, "y": 2}, indent = 2)  # Placeholder for actual response generation FOR DEBUGGING
    if "no response" in response.lower():
        return {"response" : "No response from model while generating structured proof"}
    response_cleaned = response.strip("```json").strip("```")

    output = json.dumps(json.loads(response_cleaned), indent=2)
    return output

def gen_paper_json(paper_text, pdf_input:bool = False, provider = "openai", model: str = "gpt-4o"):
    # st.toast(f"Paper text: {paper_text}, PDF input: {pdf_input}")
    response = model_response_gen(
        prompt = mathpaper_prompt(paper_text, pdf_input)["prompt"],
        task = mathpaper_prompt(paper_text, pdf_input)["task"],
        json_output=True,
        provider=provider,
        model=model,
        paper_input=True,
        pdf_val=paper_text, # the File Object goes from here in case of paper
    )
    # response = json.dumps({"x": 1, "y": 2}, indent = 2)  # Placeholder for actual response generation FOR DEBUGGING

    if "no response" in response.lower():
        return {"response" : "No response from model while generating structured proof"}
    response_cleaned = response.strip("```json").strip("```")
    
    return json.dumps(json.loads(response_cleaned), indent=2)

if __name__ == "__main__":
    model = "gpt-4o"
    thm= "The sum of the interior angles of any triangle is 180 degrees."
    pf ="Consider a triangle with vertices $A$, $B$, and $C$. Draw a line parallel to side $BC$ through vertex $A$. By the alternate interior angle theorem, the angles at $B$ and $C$ of the triangle are equal to the corresponding alternate angles formed by the parallel line and the transversal lines $AB$ and $AC$. Since the angles on a straight line sum to $180^\\circ$, the sum of the interior angles of the triangle, $\\angle A + \\angle B + \\angle C$, is $180^\\circ$."
    print(gen_thmpf_json(thm, pf, model=model))
