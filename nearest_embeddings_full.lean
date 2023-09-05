import LeanCodePrompts.NearestEmbeddings
import LeanAide.Aides
import Lean.Data.Json
import Std.Util.Pickle
open Lean

unsafe def show_nearest_full (stdin stdout : IO.FS.Stream)
  (data: Array ((String × String × Bool) × FloatArray))
  (logHandle: IO.FS.Handle) : IO Unit := do
  let inp ← stdin.getLine
  logHandle.putStrLn s!"finding parameter {← IO.monoMsNow}"
  let (doc, num, penalty, halt) := 
    match Json.parse inp with
    | Except.error _ => (inp, 10, 2.0, false)
    | Except.ok j => 
      (j.getObjValAs? String "docString" |>.toOption.orElse 
        (fun _ => j.getObjValAs? String "doc_string" |>.toOption) 
        |>.getD inp, 
      j.getObjValAs? Nat "n" |>.toOption.getD 10,
      j.getObjValAs? Float "penalty" |>.toOption.getD 2.0,
      j.getObjValAs? Bool "halt" |>.toOption.getD false)
  logHandle.putStrLn s!"finding nearest {← IO.monoMsNow}"
  let embs ← nearestDocsToDocFull data doc num (penalty := penalty)
  logHandle.putStrLn s!"found nearest {← IO.monoMsNow}"
  logHandle.flush
  let out := 
    Lean.Json.arr <| 
      embs.toArray.map fun (doc, thm, isProp) =>
        Json.mkObj <| [
          ("docString", Json.str doc),
          ("theorem", Json.str thm),
          ("isProp", Json.bool isProp)
        ] 
  stdout.putStrLn out.compress
  stdout.flush
  unless halt do 
    show_nearest_full stdin stdout data logHandle
  return ()

unsafe def main (args: List String) : IO Unit := do
  let logPath : System.FilePath := 
    "build/lib/mathlib4-prompts-embeddings.log"
  let logHandle ← IO.FS.Handle.mk logPath IO.FS.Mode.append
  logHandle.putStrLn s!"starting process {← IO.monoMsNow}"
  logHandle.flush
  let picklePath : System.FilePath := "build/lib/mathlib4-prompts-embeddings.olean"
  unless ← picklePath.pathExists do
    IO.eprintln "Fetching embeddings ..."
    let out ← IO.Process.run {
      cmd := "curl",
      args := #["--output", picklePath.toString, "-s",  "https://math.iisc.ac.in/~gadgil/data/mathlib4-prompts-embeddings.olean"]
    }
    IO.eprintln out
  logHandle.putStrLn s!"found/downloaded pickle {← IO.monoMsNow}"
  withUnpickle  picklePath <| 
    fun (data : Array <| (String × String × Bool) ×  FloatArray) => do
      let doc? := args[0]?
      match doc? with
      | some doc => 
        let num := (args[1]?.bind fun s => s.toNat?).getD 10
        logHandle.putStrLn s!"finding nearest {← IO.monoMsNow}"
        let embs ← nearestDocsToDocFull data doc num (penalty := 2.0)
        logHandle.putStrLn s!"found nearest {← IO.monoMsNow}"
        IO.println <| 
          Lean.Json.arr <| 
            embs.toArray.map fun (doc, thm, isProp) =>
              Json.mkObj <| [
                ("docString", Json.str doc),
                ("theorem", Json.str thm),
                ("isProp", Json.bool isProp)
              ] 
      | none =>
        let stdin ← IO.getStdin
        let stdout ← IO.getStdout
        show_nearest_full stdin stdout data logHandle
