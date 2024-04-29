import Lean.Meta
import LeanAide.Config
import LeanAide.Descriptions
open Lean LeanAide.Meta

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000
set_option compiler.extract_closed false

def coreContext : Core.Context := {fileName := "", fileMap := ⟨"", #[], #[]⟩, maxHeartbeats := 100000000000, maxRecDepth := 1000000
    }

def ul (name: Name)(js: Json) : Option String :=
  let desc? := js.getObjValAs? String "description"
  let statement? := js.getObjValAs? String "statement"
  match desc?, statement? with
  | Except.ok desc, Except.ok statement => some s!"<li><ul>\n<li><strong>Name:</strong> {name}</li>\n<li>{statement}</li>\n<li>{desc}</li>\n</ul></li>"
  | _, _ => none

def main : IO Unit := do
  initSearchPath (← Lean.findSysroot) initFiles
  let env ←
    importModules #[
    {module := `Mathlib},
    {module := `LeanAide.ConstDeps}] {}
  let dataPath : System.FilePath := ("rawdata"/ "premises" / "ident_pairs"/"descriptions.jsonl")
  let jsData ←
      IO.FS.lines dataPath
  let data :=  jsData.filterMap (fun js => Json.parse js |>.toOption)
  let dataMapArr := data.filterMap (fun js =>
    match js.getObjValAs? String "name" with
    | Except.error _ => none
    | Except.ok name => some (name, js))
  let dataMap : HashMap Name Json := HashMap.ofList dataMapArr.toList
  let core := modulePairs
  let mp ← core.run' coreContext {env := env} |>.runToIO'
  IO.println s!"{mp.size} module pairs"
  IO.println s!"{dataMap.size} descriptions"
  for i in [0:10] do
    let (module, consts) := mp.get! i
    IO.println s!"Module: {module}"
    for n in consts do
      match dataMap.find? n with
      | some js =>
        match ul n js with
        | some ul => IO.println ul
        | none =>
          -- IO.println s!"skipped (no description): {n}"
          pure ()
      | none =>
          -- IO.println s!"skipped (no data): {n}"
          pure ()
    IO.println "-----------------"
