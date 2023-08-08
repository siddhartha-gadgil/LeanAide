import LeanCodePrompts.Embeddings
import LeanAide.Aides
import Lean.Data.Json
open Lean

unsafe def show_nearest (stdin stdout : IO.FS.Stream) : IO Unit := do
  let doc ← stdin.getLine
  let embs ← nearestDocsToDoc doc 10
  let out := Lean.Json.arr <| embs.toArray.map Json.str
  stdout.putStrLn out.compress
  show_nearest stdin stdout

unsafe def main (_: List String) : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  show_nearest stdin stdout
