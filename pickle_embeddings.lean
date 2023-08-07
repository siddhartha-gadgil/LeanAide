import LeanCodePrompts.Embeddings
import Mathlib.Util.Pickle

def main : IO Unit := do
  let embArr ← readEmbeddingsArray
  pickle "rawdata/mathlib4-thms-embeddings.olean" embArr