import LeanCodePrompts.Embeddings
import Mathlib.Util.Pickle

def main : IO Unit := do
  let embArrDocs ← readEmbeddingsDocsArray
  pickle "build/lib/mathlib4-doc-thms-embeddings.olean" embArrDocs
  let embArrFullDocs ← readEmbeddingsFullDocsArray
  pickle "build/lib/mathlib4-prompts-embeddings.olean" embArrFullDocs