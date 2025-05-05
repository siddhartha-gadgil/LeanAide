import Lean.Meta
-- import LeanCodePrompts
import LeanAide.Config
import LeanAide.Descriptions
open Lean LeanAide.Meta LeanAide

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000
set_option compiler.extract_closed false

def coreContext : Core.Context := {fileName := "", fileMap := {source:= "", positions := #[]}, maxHeartbeats := 100000000000, maxRecDepth := 1000000
    }

def main : IO Unit := do
  let names ← IO.FS.lines ((← resourcesDir) / "doconly_names.txt")
  let names := names.map (fun s => s.trim)
  initSearchPath (← Lean.findSysroot) initFiles
  let env ←
    importModules #[
    {module := `Mathlib},
    {module := `DataGenAide.ConstDeps}] {}
  let outpath : System.FilePath := ("rawdata"/ "premises" / "ident_pairs"/"descriptions_docs.jsonl")
  let preread ← if ← outpath.pathExists then
      IO.FS.lines outpath
    else
      IO.println "No output file found"
      pure #[]
  let prenames := preread.filterMap (fun js =>
      match Json.parse js with
      | Except.error _ => none
      | Except.ok js =>
        js.getObjValAs? String "name"  |>.toOption)
  IO.println s!"Read {prenames.size} names from output file"
  IO.println s!"Got names; size {names.size}"
  let names := names.filter (fun name => !prenames.contains name)
  IO.println s!"Filtered names; size {names.size}"
  let handle ←
    IO.FS.Handle.mk outpath IO.FS.Mode.append
  let mut count := 1
  for name in names do
    IO.println s!"Processing {count} of {names.size}"
    let js := Json.mkObj [("name", Json.str name)]
    let translator : Translator := {}
    let core := translator.addDescriptionCore js
    let (js, check) ← core.run' coreContext {env := env} |>.runToIO'
    handle.putStrLn js.compress
    handle.flush
    if check then
      IO.println s!"Added {js.compress}"
      IO.sleep 10000
    else
      IO.println s!"Skipped {js.compress}"
    count := count + 1
