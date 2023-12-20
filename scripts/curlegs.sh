#!bin/bash

curl $AZURE_OPENAI_ENDPOINT/openai/deployments/leanaide-gpt4/chat/completions?api-version=2023-05-15   -H "Content-Type: application/json"   -H "api-key: $AZURE_OPENAI_KEY"   -d '{"messages":[{"role": "system", "content": "You are a helpful assistant."},{"role": "user", "content": "Does Azure OpenAI support customer managed keys?"},{"role": "assistant", "content": "Yes, customer managed keys are supported by Azure OpenAI."},{"role": "user", "content": "Do other Azure AI services support this too?"}]}'

curl $AZURE_OPENAI_ENDPOINT/openai/deployments/leanaide-embed/embeddings?api-version=2023-05-15   -H "Content-Type: application/json"   -H "api-key: $AZURE_OPENAI_KEY"   -d '{"input": "The food was delicious and the waiter..."}'

curl http://localhost:8000/v1/chat/completions     -H "Content-Type: application/json"     -d '{
        "model": "morph-labs/morph-prover-v0-7b",
        "messages": [
           {"role": "system", "content": "You are a helpful assistant. Give very detailed answers"},  {"role": "user", "content": "Who won the world series in 2020?"}
        ]
    }'


python3 -m vllm.entrypoints.openai.api_server --model morph-labs/morph-prover-v0-7b

curl https://api.openai.com/v1/chat/completions   -H "Content-Type: application/json"   -H "Authorization: Bearer $OPENAI_API_KEY"   -d '{
    "model": "gpt-4-1106-preview",
    "messages": [
      {
        "role": "system",
        "content": "You are a poetic assistant, skilled in explaining complex programming concepts with creative flair."
      },
      {
        "role": "user",
        "content": "Compose a poem that explains the concept of recursion in programming."
      }
    ]
  }'
