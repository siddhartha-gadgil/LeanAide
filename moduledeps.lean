import LeanCodePrompts.ImportList
import Lean.Meta
open Lean Meta 

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000
set_option compiler.extract_closed false


def main (args: List String) : IO Unit := do
  initSearchPath (← Lean.findSysroot) (["build/lib", "lake-packages/mathlib/build/lib/",  "lake-packages/std/build/lib/", "lake-packages/Qq/build/lib/", "lake-packages/aesop/build/lib/" ])
  let nameStr := args.head!
  let name : Name := nameStr.toName 
  let env ← 
    importModules [
    {module:= `LeanCodePrompts.ImportList},
    {module:= name}] {}
  let core : CoreM Nat :=  
     writeImport nameStr
  let io? := 
    core.run' {fileName := "", fileMap := ⟨"", #[], #[]⟩, maxHeartbeats := 100000000000, maxRecDepth := 1000000, openDecls := [Lean.OpenDecl.simple `LeanAide.Meta []]
    } 
    {env := env}
  match ← io?.toIO' with
  | Except.ok cursor =>
    IO.println s!"Success: got {cursor} names"
  | Except.error e =>
    do
          IO.println "Ran with error"
          let msg ← e.toMessageData.toString
          IO.println msg

  return ()
