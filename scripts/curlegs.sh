#!bin/bash

curl $AZURE_OPENAI_ENDPOINT/openai/deployments/leanaide-gpt4/chat/completions?api-version=2023-05-15   -H "Content-Type: application/json"   -H "api-key: $AZURE_OPENAI_KEY"   -d '{"messages":[{"role": "system", "content": "You are a helpful assistant."},{"role": "user", "content": "Does Azure OpenAI support customer managed keys?"},{"role": "assistant", "content": "Yes, customer managed keys are supported by Azure OpenAI."},{"role": "user", "content": "Do other Azure AI services support this too?"}]}'

curl $AZURE_OPENAI_ENDPOINT/openai/deployments/leanaide-embed/embeddings?api-version=2023-05-15   -H "Content-Type: application/json"   -H "api-key: $AZURE_OPENAI_KEY"   -d '{"input": "The food was delicious and the waiter..."}'