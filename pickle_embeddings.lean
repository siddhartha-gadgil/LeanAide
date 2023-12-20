import LeanCodePrompts.Embeddings
import Std.Util.Pickle

def main : IO Unit := do
  let embArrDocs ← readEmbeddingsDocsArray
  pickle ".lake/build/lib/mathlib4-doc-thms-embeddings.olean" embArrDocs
  let embArrFullDocs ← readEmbeddingsFullDocsArray
  pickle ".lake/build/lib/mathlib4-prompts-embeddings.olean" embArrFullDocs
