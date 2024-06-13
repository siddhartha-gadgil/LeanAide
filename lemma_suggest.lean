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
  let outFile : System.FilePath := "rawdata" / "premises" / "ident_pairs" / "lemmas.json"
  let preNames ←
    match ← outFile.pathExists with
    | true =>
      let outLines ← IO.FS.lines outFile
      outLines.filterMapM fun line =>
      match Json.parse line with
      | Except.error _ => pure none
      | Except.ok j => pure <| j.getObjValAs? String "name" |>.toOption
    | false => pure #[]
  let errFile : System.FilePath := "rawdata" / "premises" / "ident_pairs" / "lemma-errors.txt"
  let errLines ←
    if ← errFile.pathExists then
      IO.FS.lines errFile
    else
      pure #[]
  let preNames := preNames ++ errLines
  let errH ← IO.FS.Handle.mk errFile IO.FS.Mode.append
  IO.eprintln s!"{preNames.size} names already done\n"
  let h ← IO.FS.Handle.mk outFile IO.FS.Mode.append
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
  let names := names.filter fun name => !preNames.contains name
  IO.println s!"{names.size} names remaining\n"
  for descField in ["docString", "description", "concise-description"] do
    checkAndFetch descField
  let descField := "description"
  let num := 10
  let picklePath ← picklePath descField
  let penalty := 2.0
  withUnpickle  picklePath <|
    fun (data : Array <| (String × String × Bool × String) ×  FloatArray) => do
    let mut count := 0
    count := count + 1
    let mut cacheMap ← getCachedDescriptionsMap
    for name in names[:3] do
      IO.println s!"{count} {name}"
      IO.println s!"{cacheMap.size} descriptions in cache\n"
      let core := getDescriptionCachedCore name cacheMap
      let io? ←
        core.run' {fileName := "", fileMap := {source:= "", positions := #[]}, maxHeartbeats := 0, maxRecDepth := 1000000} {env := env} |>.runToIO'
      match io? with
      | none =>
        IO.println "failed to obtain description"
        errH.putStrLn name
      | some json =>
        IO.println json.pretty
        cacheMap := cacheMap.insert name json
        let doc? := json.getObjValAs? String descField
        match doc? with
        | Except.error _ =>
          IO.println "failed to obtain description"
          errH.putStrLn name
        | Except.ok  doc =>
          let embs ← nearestDocsToDocFull data doc num (penalty := penalty)
          let lemmaPairs := embs.map fun (doc, _, _, name, _) =>
            (name.toName, doc)
          let core := lemmaChatQueryCore? name.toName doc 12 lemmaPairs
          let io? ←
            core.run' {fileName := "", fileMap := {source:= "", positions := #[]}, maxHeartbeats := 0, maxRecDepth := 1000000} {env := env} |>.runToIO'
          match io? with
          | none =>
            IO.println "failed to obtain chat"
            errH.putStrLn name
          | some (arr, thm, lemmas) =>
            IO.println s!"Obtained lemmas for {name}"
            for s in arr do
              IO.println s
            let js := Json.mkObj [("name", name), ("theorem", thm), ("suggested-lemmas", toJson arr), ("lemmas", toJson lemmas)]
            h.putStrLn js.compress
            IO.sleep 10000
