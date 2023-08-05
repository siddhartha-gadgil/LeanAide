import LeanCodePrompts.Embeddings
import Mathlib.Util.Pickle

def main : IO Unit := do
  let embMap ← readEmbeddingsArray
  pickle "rawdata/mathlib4-thms-embeddings.json.olean" embMap