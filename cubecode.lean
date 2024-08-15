import Lean.Meta
import LeanCodePrompts
import LeanCodePrompts.Examples.Structured
import LeanAide.Config
import Cli
open Lean Cli

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000
set_option compiler.extract_closed false

def main : IO Unit := do
  initSearchPath (← Lean.findSysroot) initFiles
  let env ←
    importModules #[{module := `Mathlib},
    {module:= `LeanAide.TheoremElab},
    {module:= `LeanCodePrompts.Translate},
    {module := `Mathlib}] {}
  let core : CoreM <| Option String := cubeCodeCore
  let io? :=
    core.run' {fileName := "", fileMap := {source:= "", positions := #[]}, maxHeartbeats := 100000000000, maxRecDepth := 1000000}
    {env := env}
  match ← io?.toIO' with
  | Except.ok code? =>
    IO.println "Success in running"
    match code? with
    | some code =>
      IO.println "Code generated"
      IO.println code
      let outFile := "CodeGen/cubes.lean"
      IO.FS.writeFile outFile code
    | none =>
      IO.println "No code generated"
  | Except.error e =>
    do
          IO.println "Ran with error"
          let msg ← e.toMessageData.toString
          IO.println msg
