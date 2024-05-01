import LeanCodePrompts.NearestEmbeddings
import LeanCodePrompts.EpsilonClusters
import Cache.IO
import LeanAide.Aides
import Lean.Data.Json
import Std.Util.Pickle
open Lean Cache.IO

unsafe def show_nearest_full (stdin stdout : IO.FS.Stream)
  (data: Array ((String × String × Bool × String) × FloatArray)): IO Unit := do
  let inp ← stdin.getLine
  logTimed "finding parameter"
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
  logTimed s!"finding nearest to `{doc}`"
  let embs ← nearestDocsToDocFull data doc num (penalty := penalty)
  logTimed "found nearest"
  let out :=
    Lean.Json.arr <|
      embs.toArray.map fun (doc, thm, isProp, name, d) =>
        Json.mkObj <| [
          ("docString", Json.str doc),
          ("theorem", Json.str thm),
          ("isProp", Json.bool isProp),
          ("name", Json.str name),
          ("distance", toJson d)
        ]
  stdout.putStrLn out.compress
  stdout.flush
  unless halt do
    show_nearest_full stdin stdout data
  return ()

unsafe def main (args: List String) : IO Unit := do
  logTimed "starting nearest embedding process"
  let picklePath ← picklePath "docString"
  let picklePresent ←
    if ← picklePath.pathExists then
    try
      withUnpickle  picklePath <|
        fun (_ : Array <| (String × String × Bool × String) ×  FloatArray) => do
        pure true
    catch _ => pure false
     else pure false
  unless picklePresent do
    IO.eprintln "Fetching embeddings ..."
    let out ← runCurl #["--output", picklePath.toString, "-s",  "https://math.iisc.ac.in/~gadgil/data/{picklePath.fileName.get!}"]

    IO.eprintln "Fetched embeddings"
    IO.eprintln out
  logTimed "found/downloaded pickle"
  withUnpickle  picklePath <|
    fun (data : Array <| (String × String × Bool × String) ×  FloatArray) => do
      let doc? := args[0]?
      match doc? with
      | some doc =>
        let num := (args[1]?.bind fun s => s.toNat?).getD 10
        logTimed s!"finding nearest to `{doc}`"
        let start ← IO.monoMsNow
        let embs ← nearestDocsToDocFull data doc num (penalty := 2.0)
        IO.println <|
          Lean.Json.arr <|
            embs.toArray.map fun (doc, thm, isProp, name, d) =>
              Json.mkObj <| [
                ("docString", Json.str doc),
                ("theorem", Json.str thm),
                ("isProp", Json.bool isProp),
                ("name", Json.str name),
                ("distance", toJson d)
              ]
        let finish ← IO.monoMsNow
        logTimed "found nearest"
        IO.eprintln s!"Time taken: {finish - start} ms"
        -- IO.eprintln "Clustering with epsilon 0.5"
        -- let clusters ← epsilonClusters 0.4 (fun (_, a) (_, b) =>
        --   distL2Sq a b.data) data
        -- IO.eprintln s!"Found {clusters.size} clusters"
        -- IO.eprintln s!"Sizes: {clusters.map (·.elements.size)}"
      | none =>
        let stdin ← IO.getStdin
        let stdout ← IO.getStdout
        show_nearest_full stdin stdout data

#check FloatArray
