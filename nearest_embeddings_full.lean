import LeanCodePrompts.NearestEmbeddings
import LeanCodePrompts.EpsilonClusters
import Cache.IO
import LeanAide.Aides
import Lean.Data.Json
import Batteries.Util.Pickle
open Lean Cache.IO

unsafe def show_nearest_full (stdin stdout : IO.FS.Stream)
  (docStringData: Array ((String × String × Bool × String) × FloatArray))
  (descData: Array ((String × String × Bool × String) × FloatArray))
  (concDescData: Array ((String × String × Bool × String) × FloatArray)): IO Unit := do
  let inp ← stdin.getLine
  logTimed "finding parameter"
  let (descField, doc, num, penalty, halt) :=
    match Json.parse inp with
    | Except.error _ => ("docString", inp, 10, 2.0, false)
    | Except.ok j =>
      (j.getObjValAs? String "descField" |>.toOption.getD "docString",
        j.getObjValAs? String "docString" |>.toOption.orElse
        (fun _ => j.getObjValAs? String "doc_string" |>.toOption)
        |>.getD inp,
      j.getObjValAs? Nat "n" |>.toOption.getD 10,
      j.getObjValAs? Float "penalty" |>.toOption.getD 2.0,
      j.getObjValAs? Bool "halt" |>.toOption.getD false)
  logTimed s!"finding nearest to `{doc}`"
  let data := match descField with
    | "docString" => docStringData
    | "description" => descData
    | "concise-description" => concDescData
    | _ => docStringData
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
    show_nearest_full stdin stdout docStringData descData concDescData
  return ()

unsafe def checkAndFetch (descField: String) : IO Unit := do
  let picklePath ← picklePath descField
  let picklePresent ←
    if ← picklePath.pathExists then
    try
      withUnpickle  picklePath <|
        fun (_ : EmbedData) => do
        pure true
    catch _ => pure false
     else pure false
  unless picklePresent do
    IO.eprintln "Fetching embeddings ..."
    let out ← runCurl #["--output", picklePath.toString, "-k", "-s",  "https://math.iisc.ac.in/~gadgil/data/{picklePath.fileName.get!}"]
    IO.eprintln "Fetched embeddings"
    IO.eprintln out

unsafe def main (args: List String) : IO Unit := do
  for descField in ["docString", "description", "concise-description"] do
    checkAndFetch descField
  match args.get? 0 with
  | some doc =>
  logTimed "starting nearest embedding process"
  let descField := args.getD 1 "docString"
  let picklePath ← picklePath descField
  withUnpickle  picklePath <|
    fun (data : EmbedData) => do
        IO.eprintln s!"Searching among {data.size} embeddings"
        let num := (args[1]?.bind fun s => s.toNat?).getD 10
        logTimed s!"finding nearest to `{doc}`"
        let start ← IO.monoMsNow
        let embs ← nearestDocsToDocFull data doc num (penalty := 2.0)
        IO.println <|
            embs.toArray.map fun (doc, thm, isProp, name, d) =>
              Json.mkObj <| [
                (descField, Json.str doc),
                ("theorem", Json.str thm),
                ("isProp", Json.bool isProp),
                ("name", Json.str name),
                ("distance", toJson d)
              ]
        let finish ← IO.monoMsNow
        logTimed "found nearest"
        IO.eprintln s!"Time taken: {finish - start} ms"
  | none =>
    logTimed "No arguments provided, starting interactive mode"
    withUnpickle (← picklePath "docString") <|fun
    (docStringData : EmbedData) =>
    do
    withUnpickle (← picklePath "description") <|fun
    (descData : EmbedData) =>
    do
    withUnpickle (← picklePath "concise-description") <|fun
    (concDescData : EmbedData) =>

    do
        IO.eprintln "Enter the document string to find the nearest embeddings"
        let stdin ← IO.getStdin
        let stdout ← IO.getStdout
        show_nearest_full stdin stdout docStringData descData concDescData
