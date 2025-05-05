import Lean.Meta
-- import LeanCodePrompts
import LeanAide.Config
import DataGenAide.ConstDeps
open Lean LeanAide.Meta

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000
set_option compiler.extract_closed false

def main : IO Unit := do
  initSearchPath (← Lean.findSysroot) initFiles
  let env ←
    importModules #[
    {module := `Mathlib},
    {module := `DataGenAide.ConstDeps}] {}
  let core := constantNamesCore
  let io? :=
    core.run' {fileName := "", fileMap := {source:= "", positions := #[]}, maxHeartbeats := 100000000000, maxRecDepth := 1000000} {env := env}
    match ← io?.toIO' with
    | Except.ok res =>
      IO.println s!"obtained constants: {res.size}"
      let file := System.mkFilePath ["extra_resources/binport_names.txt"]
      IO.FS.writeFile file <|
        res.foldl (fun acc x => acc ++ s!"{x}\n") ""
    | Except.error e =>
      IO.println "error"
      let m := e.toMessageData
      IO.println <| ← m.toString
