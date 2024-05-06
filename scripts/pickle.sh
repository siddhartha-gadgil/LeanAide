lake exe pickle_embeddings
lake exe pickle_embeddings mathlib4-descs-embeddings.json description "description-embedding"
lake exe pickle_embeddings mathlib4-descs-embeddings.json concise-description "concise-description-embedding"
rsycnc -vz .lake/build/lib/mathlib4-*.olean  math.iisc.ac.in:~/public_html/data/
