import LeanCodePrompts.Embeddings
import LeanAide.Aides
import Lean.Data.Json
import Mathlib.Util.Pickle
open Lean

unsafe def show_nearest (stdin stdout : IO.FS.Stream)(data: Array (String × FloatArray)) : IO Unit := do
  let inp ← stdin.getLine
  let (doc, num, halt) := 
    match Json.parse inp with
    | Except.error _ => (inp, 10)
    | Except.ok j => 
      (j.getObjValAs? String "docString" |>.toOption.orElse 
        (fun _ => j.getObjValAs? String "doc_string" |>.toOption) 
        |>.getD inp, 
      j.getObjValAs? Nat "n" |>.toOption.getD 10,
      j.getObjValAs? Bool "halt" |>.toOption.getD false)
  let embs ← nearestDocsToDoc data doc num
  let out := Lean.Json.arr <| embs.toArray.map Json.str
  stdout.putStrLn out.compress
  unless halt do 
    show_nearest stdin stdout data
  return ()

unsafe def main (_: List String) : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let picklePath : System.FilePath := "rawdata/mathlib4-thms-embeddings.olean"
  unless ← picklePath.pathExists do
    IO.println "Fetching embeddings ..."
    let out ← IO.Process.run {
      cmd := "curl",
      args := #["--output", "rawdata/mathlib4-thms-embeddings.olean", "-s",  "https://math.iisc.ac.in/~gadgil/data/mathlib4-thms-embeddings.olean"]
    }
    IO.println out
  withUnpickle  picklePath <| fun (data : Array <| String ×  FloatArray) => show_nearest stdin stdout data
