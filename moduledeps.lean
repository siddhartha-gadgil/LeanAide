import LeanAide.ImportList
import Lean.Meta
import LeanAide.Config
open Lean Meta

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000
set_option compiler.extract_closed false


def main (args: List String) : IO Unit := do
  initSearchPath (← Lean.findSysroot)
  let nameStr := args.head!
  let name : Name := nameStr.toName
  let env ←
    importModules (loadExts := true) #[
    {module:= `LeanAide.ImportList},
    {module:= name}] {}
  let core : CoreM Nat :=
     writeImport nameStr
  let io? :=
    core.run' {fileName := "", fileMap := {source:= "", positions := #[]}, maxHeartbeats := 100000000000, maxRecDepth := 1000000, openDecls := [Lean.OpenDecl.simple `LeanAide.Meta []]
    }
    {env := env}
  match ← io?.toIO' with
  | Except.ok cursor =>
    IO.println s!"Success: got {cursor} names"
  | Except.error e =>
    do
          IO.println "Ran with error"
          let msg ← e.toMessageData.toString
          IO.throwServerError msg
  return ()
