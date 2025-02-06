from embed_picker import save_embeddings, model

print('Computing embeddings...')
save_embeddings('mathlib4-descs.jsonl', 'concise-description', model)
save_embeddings('mathlib4-descs.jsonl', 'description', model)
save_embeddings('mathlib4-prompts.json', 'docString', model)

print('Embeddings computed and saved.')