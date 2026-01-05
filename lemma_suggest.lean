import LeanCodePrompts.NearestEmbeddings
import LeanAide.Descriptions
import LeanAide.Aides
import Lean.Data.Json
import Batteries.Util.Pickle
open Lean LeanAide.Meta LeanAide Translator

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
    logToStdErr `leanaide.translate.info "Fetching embeddings ..."
    let out ← IO.Process.output {cmd:= "curl", args := #["--output", picklePath.toString,   "https://storage.googleapis.com/leanaide_data/{picklePath.fileName.get!}"]}
    logToStdErr `leanaide.translate.info "Fetched embeddings"
    logToStdErr `leanaide.translate.info out.stdout

unsafe def main  : IO Unit := do
  searchPathRef.set compile_time_search_path%
  let env ←
    importModules (loadExts := true) #[{module := `Mathlib},
    {module:= `LeanAide.TheoremElab},
    {module:= `LeanCodePrompts.Translate}] {}
  let source ← IO.FS.readFile ("rawdata" / "premises" / "ident_pairs" / "more-frequencies.json")
  let outDir : System.FilePath := "rawdata" / "premises" / "lemma_predictions"
  if !(← outDir.pathExists) then
    IO.FS.createDirAll outDir
  let outFile : System.FilePath := outDir / "lemmas.jsonl"
  let preNames ←
    match ← outFile.pathExists with
    | true =>
      let outLines ← IO.FS.lines outFile
      outLines.filterMapM fun line =>
      match Json.parse line with
      | Except.error _ => pure none
      | Except.ok j => pure <| j.getObjValAs? String "name" |>.toOption
    | false => pure #[]
  let errFile : System.FilePath := outDir / "lemma-errors.txt"
  let errLines ←
    if ← errFile.pathExists then
      IO.FS.lines errFile
    else
      pure #[]
  let preNames := preNames ++ errLines
  let errH ← IO.FS.Handle.mk errFile IO.FS.Mode.append
  logToStdErr `leanaide.translate.info s!"{preNames.size} names already done\n"
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
  let num := 20
  let picklePath ← picklePath descField
  let penalty := 2.0
  withUnpickle  picklePath <|
    fun (data : EmbedData) => do
    let mut count := 0
    let mut cacheMap ← getCachedDescriptionsMap
    for name in names do
      IO.println s!"{count} {name}"
      count := count + 1
      IO.println s!"{cacheMap.size} descriptions in cache\n"
      let core := getDescriptionCachedCore name  (cacheMap := cacheMap) {}
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
            IO.println s!"Obtained lemmas for {name}: {arr.size} lemmas"
            for s in arr do
              IO.println s
            let js := Json.mkObj [("name", name), ("theorem", thm), ("suggested-lemmas", toJson arr), ("lemmas", toJson lemmas)]
            h.putStrLn js.compress
            IO.sleep 20000
