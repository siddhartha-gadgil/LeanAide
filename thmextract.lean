import Lean.Meta
import LeanCodePrompts
import LeanCodePrompts.FirstTacticData
open Lean

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000
set_option compiler.extract_closed false

def main (args: List String) : IO Unit := do
  initSearchPath (← Lean.findSysroot) ["build/lib", "lake-packages/mathlib/build/lib/",  "lake-packages/std/build/lib/", "lake-packages/Qq/build/lib/", "lake-packages/aesop/build/lib/", "lake-packages/proofwidgets/build/lib" ]
  let env ← 
    importModules [
    {module := `LeanCodePrompts.Basic},
    {module:= `LeanCodePrompts.CheckParse},
    {module:= `LeanCodePrompts.FirstTacticData},
    {module := `Mathlib}] {}
  let core := 
    readAndSaveTheoremTacticsCore args.tail! 
  let io? := 
    core.run' {fileName := "", fileMap := ⟨"", #[], #[]⟩, maxHeartbeats := 10000000, maxRecDepth := 1000} 
    {env := env}
  match ← io?.toIO' with
  | Except.ok js =>
    IO.println "Success"
    IO.FS.writeFile args.head! js
  | Except.error e =>
    do
          IO.println "Ran with error"
          let msg ← e.toMessageData.toString
          IO.println msg
  return ()
