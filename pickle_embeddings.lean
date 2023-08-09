import LeanCodePrompts.Embeddings
import Mathlib.Util.Pickle

def main : IO Unit := do
  let embArr ← readEmbeddingsArray
  pickle "rawdata/mathlib4-thms-embeddings.olean" embArr
  let embArrFull ← readEmbeddingsFullArray
  pickle "rawdata/mathlib4-doc-thms-embeddings.olean" embArrFull