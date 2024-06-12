import Lean.Meta
-- import LeanCodePrompts
import LeanAide.Config
import LeanAide.Descriptions
open Lean LeanAide.Meta

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000
set_option compiler.extract_closed false

def coreContext : Core.Context := {fileName := "", fileMap := {source:= "", positions := #[]}, maxHeartbeats := 100000000000, maxRecDepth := 1000000
    }

def main : IO Unit := do
  let sourceJson ←
    IO.FS.readFile
    ("rawdata"/ "premises" / "ident_pairs"/"frequencies.json")
  let input? := Json.parse sourceJson
  initSearchPath (← Lean.findSysroot) initFiles
  let env ←
    importModules #[
    {module := `Mathlib},
    {module := `LeanAide.ConstDeps}] {}
  let outpath : System.FilePath := ("rawdata"/ "premises" / "ident_pairs"/"descriptions.jsonl")
  let preread ← if ← outpath.pathExists then
      IO.FS.lines outpath
    else
      IO.println "No output file found"
      pure #[]
  let prenames := preread.filterMap (fun js =>
      match Json.parse js with
      | Except.error _ => none
      | Except.ok js =>
        js.getObjVal? "name"  |>.toOption)
  IO.println s!"Read {prenames.size} names from output file"
  match input? with
  | Except.error _ => IO.println "Failed to parse JSON"
  | Except.ok json =>
    IO.println "Parsed JSON"
    match json.getArr? with
    | Except.error _ => IO.println "Failed to parse JSON"
    | Except.ok jsarr => do
        IO.println s!"Parsed JSON array; size {jsarr.size}"
        -- let jsarr := jsarr.filter (fun js =>
        --   match js.getObjVal? "name" with
        --   | Except.error _ => false
        --   | Except.ok name => !prenames.contains name)
        IO.println s!"Filtered JSON array; size {jsarr.size}"
        let mut count := 1
        let mut rewrites := 0
        for js in jsarr do
          -- IO.println s!"Processing {count} of {jsarr.size}"
          let name? := js.getObjValAs? String "name"
          match name? with
          | Except.error _ =>
              IO.println s!"Failed to parse JSON"
          | Except.ok name => do
            let core := needsIndCore name.toName
            let names? ← core.run' coreContext {env := env} |>.runToIO'
            match names? with
            | none => pure ()
            | some names => do
              IO.println s!"Need to rewrite for {name}; uses {names}"
              rewrites := rewrites + 1
              IO.println s!"rewrites: {rewrites} out of {count}"
            if count % 1000 == 0 then
              IO.println s!"{count} out of {jsarr.size} processed"
            count := count + 1
