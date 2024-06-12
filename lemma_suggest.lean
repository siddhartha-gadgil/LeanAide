import LeanCodePrompts.NearestEmbeddings
import LeanAide.Descriptions
import Cache.IO
import LeanAide.Aides
import Lean.Data.Json
import Std.Util.Pickle
open Lean Cache.IO LeanAide.Meta

unsafe def checkAndFetch (descField: String) : IO Unit := do
  let picklePath ← picklePath descField
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

unsafe def main  : IO Unit := do
  searchPathRef.set compile_time_search_path%
  let env ←
    importModules #[{module := `Mathlib},
    {module:= `LeanAide.TheoremElab},
    {module:= `LeanCodePrompts.Translate}] {}
  let source ← IO.FS.readFile ("rawdata" / "premises" / "ident_pairs" / "more-frequencies.json")
  let jsSource ←  match Json.parse source with
    | Except.error _ => IO.throwServerError "failed to parse"
    | Except.ok j => pure j
  let jsArray ←  match jsSource.getArr? with
    | Except.ok a => pure a
    | _ => IO.throwServerError "expected array"
  let jsArray := jsArray.filter fun js =>
    (js.getObjValAs? Nat "frequency" |>.toOption) = some 2
  IO.println s!"{jsArray.size} theorems with frequency 2\n"
  let names := jsArray.filterMap fun js =>
    js.getObjValAs? String "name" |>.toOption
  IO.println s!"{names.size} names\n"
  for descField in ["docString", "description", "concise-description"] do
    checkAndFetch descField
  let descField := "description"
  let num := 10
  let picklePath ← picklePath descField
  let penalty := 2.0
  let cacheMap ← getCachedDescriptionsMap
  IO.println s!"{cacheMap.size} descriptions in cache\n"
  withUnpickle  picklePath <|
    fun (data : Array <| (String × String × Bool × String) ×  FloatArray) => do
    let mut count := 0
    for name in names[:3] do
    IO.println s!"{count} {name}"
    let core := getDescriptionCachedCore name cacheMap
    let io? ←
      core.run' {fileName := "", fileMap := {source:= "", positions := #[]}, maxHeartbeats := 0, maxRecDepth := 1000000} {env := env} |>.runToIO'
    match io? with
    | none =>
      IO.println "failed to obtain description"
    | some json =>
      IO.println json.pretty
    count := count + 1
    -- let embs ← nearestDocsToDocFull data doc num (penalty := penalty)
    -- logTimed "found nearest"
    -- let out :=
    --   Lean.Json.arr <|
    --     embs.toArray.map fun (doc, thm, isProp, name, d) =>
    --       Json.mkObj <| [
    --         ("docString", Json.str doc),
    --         ("theorem", Json.str thm),
    --         ("isProp", Json.bool isProp),
    --         ("name", Json.str name),
    --         ("distance", toJson d)
    --       ]
    -- IO.print out.compress
