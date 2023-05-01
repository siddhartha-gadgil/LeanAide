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

def main (_: List String) : IO Unit := do
  init
  let env ← environment
  let propMap ←  
    propMapCore.run' coreContext {env := env} |>.runToIO'
  IO.println s!"Obtained prop-map: {propMap.size} entries"
  let propNames := propMap.toArray.map (·.1)
  let groupedNames ←  splitData propNames 
  let handles ← fileHandles
  let concurrency := (← threadNum) * 3 / 4
  IO.println s!"Using {concurrency} threads"
  for group in groups do
    IO.println s!"Finding premises for group {group}"
    let allNames := groupedNames[group].get!
    IO.println s!"Definitions in group {group}: {allNames.size}"
    let batches := allNames.batches' concurrency
    let batches := batches.map (fun batch => batch.map (·.toName) |>.toList) 
    IO.println s!"Made {batches.size} batches"
    let tasks ←  batches.mapM fun names => do
        let writeCore := PremiseData.writeBatchCore names group handles propMap
        writeCore.run' coreContext {env := env} |>.spawnToIO
    IO.println "Spawned tasks"
    let unifyTasks ← BaseIO.mapTasks pure tasks.toList
    let getTasks := unifyTasks.get
    discard <| getTasks.mapM id 
    IO.println s!"Done {group}"
  IO.println s!"Done: all tasks completed"
  return ()
