import LeanCodePrompts.Premises
import Lean.Meta
open Lean Meta LeanAide.Meta

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000
set_option compiler.extract_closed false


def main (args: List String) : IO Unit := do
  initSearchPath (← Lean.findSysroot) (["build/lib", "lake-packages/mathlib/build/lib/",  "lake-packages/std/build/lib/", "lake-packages/Qq/build/lib/", "lake-packages/aesop/build/lib/" ])
  let start := 
    (args.get? 0 >>= fun s => s.toNat?).getD 0 
  let stop := 
    (args.get? 1 >>= fun s => s.toNat?).getD 1
  let env ← 
    importModules [{module := `Mathlib},
    {module:= `LeanCodePrompts.CheckParse},
    {module:= `LeanCodePrompts.ParseJson},
    {module:= `LeanCodePrompts.Premises},
    {module := `Mathlib}] {}
  let core : CoreM Nat :=  
     writeBatchPremisesCore start stop
  let io? := 
    core.run' {fileName := "", fileMap := ⟨"", #[], #[]⟩, maxHeartbeats := 100000000000, maxRecDepth := 1000000} 
    {env := env}
  match ← io?.toIO' with
  | Except.ok cursor =>
    IO.println s!"Success: ran to {cursor}"
  | Except.error e =>
    do
          IO.println "Ran with error"
          let msg ← e.toMessageData.toString
          IO.println msg

  return ()
