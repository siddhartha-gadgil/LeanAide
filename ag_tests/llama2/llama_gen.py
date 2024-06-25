from openai import OpenAI
def llama(problem:str):
    # Create an OpenAI client with your deepinfra token and endpoint
    openai = OpenAI(
        api_key="<deep_infra_api_key>",
        base_url="https://api.deepinfra.com/v1/openai",
    )

    chat_completion = openai.chat.completions.create(
        model="meta-llama/Meta-Llama-3-70B-Instruct", ## MODEL NAME
        messages=[
            {"role": "user", "content": problem},
        ],
    )

    return chat_completion.choices[0].message.content

