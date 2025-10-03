import Lean.Meta
-- import LeanCodePrompts
import LeanAide.Config
import DataGenAide.ConstDeps
import DataGenAide.CheckDescs
open Lean LeanAide Meta

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000
set_option compiler.extract_closed false

def coreContext : Core.Context := {fileName := "", fileMap := {source:= "", positions := #[]}, maxHeartbeats := 100000000000, maxRecDepth := 1000000
    }

unsafe def main : IO Unit := do
  initSearchPath (← Lean.findSysroot)
  enableInitializersExecution
  let env ←
    importModules (loadExts := true) #[
    {module := `Mathlib},
    {module := `DataGenAide.ConstDeps}] {}
  let lines ← IO.FS.lines ((← resourcesDir) / "mathlib4-descs.jsonl")
  let jsLines := lines.filterMap fun line =>
    (Json.parse line).toOption
  IO.eprintln s!"Read {jsLines.size} lines (after filtering) from {(lines.size)}"
  let h ← IO.FS.Handle.mk ((← resourcesDir) / "mathlib4-descs.jsonl") IO.FS.Mode.write
  let mut count := 0
  for js in jsLines do
    count := count + 1
    if count % 1000 == 0 then IO.eprintln s!"Processing {count} lines"
    let .ok name := js.getObjValAs? Name "name" | throw <| IO.userError s!"Failed to parse JSON: {js}"
    let core := updateDescCore? js
    let js? ← core.run' coreContext {env := env} |>.runToIO'
    match js? with
    | none =>
      -- IO.eprintln s!"No update for {name}"
      continue
    | some js =>
      -- IO.eprintln s!"Updated {name}"
      h.putStrLn js.compress
