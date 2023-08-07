import LeanCodePrompts.Embeddings
import LeanAide.Aides
import Lean.Data.Json
open Lean

unsafe def main (args: List String) : IO Unit := do
  let doc := args.head!
  -- IO.println doc
  let embs ← nearestDocsToDoc doc 3
  -- IO.println "complete"
  IO.println <| Lean.Json.arr <| embs.toArray.map Json.str
