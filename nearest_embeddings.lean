import LeanCodePrompts.Embeddings
import LeanAide.Aides
import Lean.Data.Json
import Mathlib.Util.Pickle
open Lean

unsafe def show_nearest (stdin stdout : IO.FS.Stream)(data: Array ((String × String) × FloatArray)) : IO Unit := do
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
  let embs ← nearestDocsToDocFull data doc num
  let out := 
    Lean.Json.arr <| 
      embs.toArray.map fun (doc, thm) =>
        Json.mkObj <| [
          ("docString", Json.str doc),
          ("theorem", Json.str thm)
        ] 
  stdout.putStrLn out.compress
  stdout.flush
  unless halt do 
    show_nearest stdin stdout data
  return ()

unsafe def main (args: List String) : IO Unit := do
  let picklePath : System.FilePath := "rawdata/mathlib4-doc-thms-embeddings.olean"
  unless ← picklePath.pathExists do
    IO.println "Fetching embeddings ..."
    let out ← IO.Process.run {
      cmd := "curl",
      args := #["--output", "rawdata/mathlib4-doc-thms-embeddings.olean", "-s",  "https://math.iisc.ac.in/~gadgil/data/mathlib4-doc-thms-embeddings.olean"]
    }
    IO.println out
  withUnpickle  picklePath <| 
    fun (data : Array <| (String × String) ×  FloatArray) => do
      let doc? := args[0]?
      match doc? with
      | some doc => 
        let num := (args[1]?.bind fun s => s.toNat?).getD 10
        let embs ← nearestDocsToDocFull data doc num
        IO.println <| 
          Lean.Json.arr <| 
            embs.toArray.map fun (doc, thm) =>
              Json.mkObj <| [
                ("docString", Json.str doc),
                ("theorem", Json.str thm)
              ] 
      | none =>
        let stdin ← IO.getStdin
        let stdout ← IO.getStdout
        show_nearest stdin stdout data
