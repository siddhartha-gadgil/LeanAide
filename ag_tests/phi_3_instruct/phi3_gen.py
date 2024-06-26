from openai import OpenAI
def phigen(problem:str):
    # Create an OpenAI client with your deepinfra token and endpoint
    openai = OpenAI(
        api_key="<API-KEY>",
        base_url="https://api.deepinfra.com/v1/openai",
    )

    chat_completion = openai.chat.completions.create(
        model="microsoft/Phi-3-medium-4k-instruct", ## MODEL NAME
        messages=[
            {"role": "user", "content": problem},
        ],
    )

    return chat_completion.choices[0].message.content

