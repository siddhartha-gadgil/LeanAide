import LeanAide.IdentData
import LeanAide.ConstDeps
import Lean.Meta
import LeanAide.Config
open Lean Meta LeanAide.Meta

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000
set_option compiler.extract_closed false
set_option pp.fullNames false

def init : IO Unit := do
  initSearchPath (← Lean.findSysroot) initFiles

def environment : IO Environment := do
  importModules #[{module := `Mathlib},
    {module:= `LeanAide.ConstDeps},
    {module:= `LeanAide.IdentData},
    {module:= `LeanAide.Aides},
    {module := `Mathlib}] {}

def environment' : IO Environment := do
  importModules #[{module := `Mathlib},
    {module:= `LeanAide.TheoremElab},
    {module:= `LeanAide.ConstDeps},
    {module := `Mathlib}] {}


def coreContext : Core.Context := {fileName := "", fileMap := {source:= "", positions := #[]}, maxHeartbeats := 100000000000, maxRecDepth := 1000000, openDecls := [Lean.OpenDecl.simple `LeanAide.Meta []]
    }

unsafe def main (_: List String) : IO Unit := do
  enableInitializersExecution
  init
  let env ← environment
  let names ←
    constantNamesCore.run' coreContext {env := env} |>.runToIO'
  let groupedNames ←  splitData names
  let handles ← PropIdentData.handles
  let concurrency := (← threadNum) * 3 / 4
  IO.println s!"Using {concurrency} threads"
  for group in groups do
    IO.println s!"Finding premises for group {group}"
    let allNames := groupedNames[group]? |>.getD (Array.empty)
    IO.println s!"Definitions in group {group}: {allNames.size}"
    let batches := allNames.batches' concurrency
    let batches := batches.map (fun batch => batch.toList)
    IO.println s!"Made {batches.size} batches"
    let batches' := batches.zip (Array.range batches.size)
    let tasks ←  batches'.mapM fun (names, k) => do
        let writeCore :=
          PropIdentData.writeBatchCore names group handles
            s!"batch: {k} of group {group}"
        let t ← writeCore.run' coreContext {env := env} |>.spawnToIO
        pure (t, k)
    IO.println "Spawned tasks"
    let mut count := 0
    for (task, k) in tasks.reverse do
      count := count + 1
      IO.println s!"Waiting for task {k}: {count} of {tasks.size}"
      IO.println s!"Task {k} finished with premises: {← task.get}"
    -- let unifyTasks ← BaseIO.mapTasks pure tasks.toList
    -- let getTasks := unifyTasks.get
    -- discard <| getTasks.mapM id
    IO.println s!"Done {group}"
  IO.println s!"Done: all tasks completed"
  return ()
