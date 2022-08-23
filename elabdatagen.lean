import Lean.Meta
import LeanCodePrompts
import LeanCodePrompts.Translate
open Lean

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000
set_option compiler.extract_closed false


def main (args: List String) : IO Unit := do
  initSearchPath (← Lean.findSysroot) ["build/lib", "lean_packages/mathlib/build/lib/", "lean_packages/lean3port/build/lib/", "lean_packages/mathlib3port/build/lib/"]
  let env ← 
    importModules [{module := `Mathlib},
    {module := `LeanCodePrompts.Basic},
    {module:= `LeanCodePrompts.CheckParse},
    {module:= `LeanCodePrompts.ParseJson},
    {module:= `LeanCodePrompts.Translate},
    {module := `Mathbin.All}] {}
  let file := System.mkFilePath ["data/parsed_thms.txt"]
  let thms ←  IO.FS.lines file
  for thm in thms do
    -- IO.println s!"processing: {thm}"
    let core := hasElabCore thm
    let io? := 
      core.run' {fileName := "", fileMap := ⟨"", #[], #[]⟩, maxHeartbeats := 100000, maxRecDepth := 1000000} 
      {env := env}
    -- IO.println "creating task"
    let ioTask? ←  io?.asTask
    -- IO.println "task made"
    match ioTask?.get with
    | Except.ok res =>
      if res then 
        IO.println thm
      else
        IO.eprintln thm
    | Except.error e =>
      do
            let msg ← e.toMessageData.toString
            IO.eprintln msg
  return ()
