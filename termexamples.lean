import Lean.Meta
-- import LeanCodePrompts
import LeanAide.Config
import LeanAide.ConstDeps
import LeanAide.PremiseData
open Lean LeanAide.Meta

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000
set_option compiler.extract_closed false

def coreContext : Core.Context := {fileName := "", fileMap := ⟨"", #[], #[]⟩, maxHeartbeats := 100000000000, maxRecDepth := 1000000
    }

def main : IO Unit := do
  initSearchPath (← Lean.findSysroot) initFiles
  let env ←
    importModules #[
    {module := `Mathlib},
    {module := `LeanAide.ConstDeps}] {}
  IO.eprintln "Seeking term kind examples..."
  let core := termKindExamplesCore
  let l ← core.run' coreContext {env := env} |>.runToIO'
  let js := toJson l
  let path := System.mkFilePath ["data", "term-kinds.json"]
  IO.FS.writeFile path <| js.pretty
  let jsl := jsonLines l.toArray
  let path := System.mkFilePath ["data", "term-kinds.jsonl"]
  IO.FS.writeFile path <| jsl
