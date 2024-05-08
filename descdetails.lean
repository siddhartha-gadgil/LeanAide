import Lean.Meta
import LeanAide.Config
import LeanAide.Descriptions
open Lean LeanAide.Meta

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000
set_option compiler.extract_closed false

def coreContext : Core.Context := {fileName := "", fileMap := {source:= "", positions := #[]}, maxHeartbeats := 100000000000, maxRecDepth := 1000000
    }

def main : IO Unit := do
  initSearchPath (← Lean.findSysroot) initFiles
  let env ←
    importModules #[
    {module := `Mathlib},
    {module := `LeanAide.ConstDeps}] {}
  let dataPath : System.FilePath := ("rawdata"/ "premises" / "ident_pairs"/"descs.jsonl")
  let jsData ←
      IO.FS.lines dataPath
  let dataPathDocs : System.FilePath := ("rawdata"/ "premises" / "ident_pairs"/"descs_docs.jsonl")
  let jsDataDocs ←
      IO.FS.lines dataPathDocs
  let data :=
    (jsData ++ jsDataDocs).filterMap (fun js => Json.parse js |>.toOption)
  let outPath := System.mkFilePath ["resources", "mathlib4-descs.jsonl"]
  IO.FS.writeFile outPath ""
  let h ← IO.FS.Handle.mk outPath IO.FS.Mode.append
  let mut count := 0
  for js in data do
    let name? := js.getObjValAs? String "name" |>.toOption
    let desc? := js.getObjValAs? String "description" |>.toOption
    let concise? :=
      js.getObjValAs? String "concise-description" |>.toOption
    match name?, desc?, concise? with
    | some name, some desc, some concise =>
      let name := name.toName
      let core := DefnTypes.thmFromNameCore? name
      let dfn? ← core.run' coreContext {env := env} |>.runToIO'
      match dfn? with
      | some dfn =>
        let desc := desc
        let concise := concise
        let js := Json.mkObj [("name", Json.str name.toString), ("description", Json.str desc), ("concise-description", Json.str concise)]
        let js' := toJson dfn
        h.putStrLn (js.mergeObj js' |>.compress)
        h.flush
      | _ =>
        IO.println s!"{name} not found"
        pure ()
    | _, _, _ =>
      -- IO.println s!"{js.compress} not found"
      pure ()
    count := count + 1
    if count % 100 == 0 then
      IO.println s!"{count} done"
