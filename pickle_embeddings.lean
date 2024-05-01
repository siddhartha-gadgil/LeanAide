import LeanCodePrompts.Embeddings
import Std.Util.Pickle

def main : IO Unit := do
  let blob ←
    IO.FS.readFile <|
      System.mkFilePath ["rawdata", "mathlib4-prompts-embeddings.json"]
  let embArrFullDocs ← readEmbeddingsFullDocsArray blob "docString"
  pickle (← picklePath "docString") embArrFullDocs
