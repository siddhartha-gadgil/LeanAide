import LeanCodePrompts.Premises
import Lean.Meta
open Lean Meta LeanAide.Meta

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000
set_option compiler.extract_closed false

def init : IO Unit := do
  initSearchPath (← Lean.findSysroot) (["build/lib", "lake-packages/mathlib/build/lib/",  "lake-packages/std/build/lib/", "lake-packages/Qq/build/lib/", "lake-packages/aesop/build/lib/" ])

def environment : IO Environment := do
  importModules [{module := `Mathlib},
    {module:= `LeanCodePrompts.CheckParse},
    {module:= `LeanCodePrompts.ParseJson},
    {module:= `LeanCodePrompts.VerboseDelabs},
    {module:= `LeanCodePrompts.Premises},
    {module := `Mathlib}] {}

def coreContext : Core.Context := {fileName := "", fileMap := ⟨"", #[], #[]⟩, maxHeartbeats := 100000000000, maxRecDepth := 1000000, openDecls := [Lean.OpenDecl.simple `LeanAide.Meta []]
    }   

def main (args: List String) : IO Unit := do
  init
  let env ← environment
  let propMap ←  
    propMapCore.run' coreContext {env := env} |>.runToIO'
  IO.println s!"Success: ran to {propMap.size}"
  let names := args.map String.toName
  let handles ← fileHandles
  IO.println "Writing batch"
  let testCore := 
    PremiseData.writeBatchCore (names) "extra" handles propMap true
  discard <| testCore.run' coreContext {env := env} |>.runToIO'  
  IO.println "Done"
  return ()
