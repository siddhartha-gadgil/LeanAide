import Lean.Meta
-- import LeanCodePrompts
import LeanAide.Config
import DataGenAide.ConstDeps
open Lean LeanAide.Meta

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
  let core := writeDocsCore
  let js ← core.run' coreContext {env := env} |>.runToIO'
  logToStdErr `leanaide.translate.info "Writing to resources/mathlib4-prompts.json and resources/mathlib4-prompts.jsonl"
  -- IO.FS.writeFile ((← resourcesDir) / "mathlib4-prompts.json") js.pretty
  let h ← IO.FS.Handle.mk ((← resourcesDir) / "mathlib4-prompts.jsonl") IO.FS.Mode.write
  let .ok lines := js.getArr? | throw <| IO.userError "Expected array"
  let mut count := 0
  for line in lines do
    count := count + 1
    if count % 1000 == 0 then logToStdErr `leanaide.translate.info s!"Wrote {count} lines"
    h.putStrLn line.compress
