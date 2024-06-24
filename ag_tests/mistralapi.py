from mistralai.client import MistralClient
from mistralai.models.chat_completion import ChatMessage
def mistral_api_out(problem:str):
    api_key = "<API_KEY_MISTRALAI>"
    model = "mistral-large-latest"

    client = MistralClient(api_key=api_key)

    messages = [
        ChatMessage(role="user", content=problem)
    ]

    chat_response = client.chat(
        model=model,
        response_format={"type": "json_object"},
        messages=messages,
    )

    response = chat_response.choices[0].message.content
    return response