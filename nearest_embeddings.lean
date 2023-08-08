import LeanCodePrompts.Embeddings
import LeanAide.Aides
import Lean.Data.Json
import Mathlib.Util.Pickle
open Lean

unsafe def show_nearest (stdin stdout : IO.FS.Stream)(data: Array (String × FloatArray)) : IO Unit := do
  let doc ← stdin.getLine
  let embs ← nearestDocsToDoc data doc 10
  let out := Lean.Json.arr <| embs.toArray.map Json.str
  stdout.putStrLn out.compress
  show_nearest stdin stdout data

unsafe def main (_: List String) : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  withUnpickle  "rawdata/mathlib4-thms-embeddings.olean" <| fun (data : Array <| String ×  FloatArray) => show_nearest stdin stdout data
