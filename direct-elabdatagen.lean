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
  let mut count := 0
  let mut elaborated := 0
  let thm := ": ∀ {p : ℕ}, Nat.Prime p → p = 2 ∨ p % 2 = 1"
  let core := elabThmTransCore thm 
  let io? := 
    core.run' {fileName := "", fileMap := ⟨"", #[], #[]⟩, maxHeartbeats := 10000000, maxRecDepth := 1000} 
    {env := env}
  match ← io?.toIO' with
  | Except.ok res =>
    IO.println res
  | Except.error e =>
    do
          let msg ← e.toMessageData.toString
          IO.eprintln msg

  -- for thm in thms do
  --   -- IO.println s!"processing: {thm}"
  --   let core := hasElabCore thm (some 50)
  --   let io? := 
  --     core.run' {fileName := "", fileMap := ⟨"", #[], #[]⟩, maxHeartbeats := 1000000, maxRecDepth := 1000} 
  --     {env := env}
  --   -- IO.println "creating task"
  --   let ioTask? ←  io?.asTask
  --   count := count + 1
  --   -- IO.println "task made"
  --   IO.eprintln count
  --   IO.eprintln elaborated
  --   match ioTask?.get with
  --   | Except.ok res =>
  --     if res then 
  --       elaborated := elaborated + 1
  --       IO.println thm
  --     else
  --       IO.eprintln thm
  --   | Except.error e =>
  --     do
  --           let msg ← e.toMessageData.toString
  --           IO.eprintln msg
  return ()
