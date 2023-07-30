import Lean.Meta
-- import LeanCodePrompts
import LeanAide.Config
import LeanAide.ConstDeps
open Lean LeanAide.Meta

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000
set_option compiler.extract_closed false

def coreContext : Core.Context := {fileName := "", fileMap := ⟨"", #[], #[]⟩, maxHeartbeats := 100000000000, maxRecDepth := 1000000
    }

def main : IO Unit := do
  initSearchPath (← Lean.findSysroot) initFiles
  let env ← 
    importModules [
    {module := `Mathlib},
    {module := `LeanAide.ConstDeps}] {}
  let core := writeDocsCore
  core.run' coreContext {env := env} |>.runToIO'
