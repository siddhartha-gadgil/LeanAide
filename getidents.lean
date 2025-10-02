import LeanAide.IdentData
import DataGenAide.ConstDeps
import Lean.Meta
import LeanAide.Config
open Lean Meta LeanAide.Meta

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000
set_option compiler.extract_closed false
set_option pp.fullNames false

def init : IO Unit := do
  initSearchPath (← Lean.findSysroot)

def environment : IO Environment := do
  importModules (loadExts := true) #[{module := `Mathlib},
    {module:= `DataGenAide.ConstDeps},
    {module:= `LeanAide.IdentData},
    {module:= `LeanAide.Aides},
    {module := `Mathlib}] {}

def environment' : IO Environment := do
  importModules (loadExts := true) #[{module := `Mathlib},
    {module:= `LeanAide.TheoremElab},
    {module:= `DataGenAide.ConstDeps},
    {module := `Mathlib}] {}


def coreContext : Core.Context := {fileName := "", fileMap := {source:= "", positions := #[]}, maxHeartbeats := 100000000000, maxRecDepth := 1000000, openDecls := [Lean.OpenDecl.simple `LeanAide.Meta []]
    }

unsafe def main (_: List String) : IO Unit := do
  enableInitializersExecution
  init
  let env ← environment
  IO.eprintln "Obtaining names"
  let groupedNameFiles (group: String) : System.FilePath :=
    "rawdata" / "premises" / "identifiers" / "grouped_names" / s!"{group}.txt"
  let preGroups : Bool ← groups.allM fun group => do
    let groupedNameFile := groupedNameFiles group
    pure (← groupedNameFile.pathExists)
  let doneNamesFile : System.FilePath :=
    "rawdata" / "premises" / "identifiers" / "done_names.json"
  let groupedNames ← if preGroups
    then
      let mut m : Std.HashMap String (Array Name) := Std.HashMap.empty
      for group in groups do
        let mut names : Array Name := Array.empty
        let lines ← IO.FS.lines (groupedNameFiles group)
        for line in lines do
          let name := line.toName
          names := names.push name
        m := m.insert group names
      pure m
    else do
      let names ←
        propNamesCore.run' coreContext {env := env} |>.runToIO'
      IO.eprintln s!"Obtained names: {names.size} entries"
      let m ← splitData names
      for group in groups do
        let names := m[group]!
        IO.FS.writeFile (groupedNameFiles group) ""
        let h ← IO.FS.Handle.mk (groupedNameFiles group) IO.FS.Mode.write
        for name in names do
          h.putStrLn <| name.toString
      IO.FS.writeFile doneNamesFile ""
      pure m
  let doneNames ← IO.FS.lines doneNamesFile
  IO.eprintln s!"Obtained grouped names: {groupedNames.size} entries"
  let handles ← PropIdentData.handles !preGroups
  let concurrency := (← threadNum) * 3 / 4
  IO.println s!"Using {concurrency} threads"
  for group in groups do
    IO.println s!"Finding premises for group {group}"
    let allNames := groupedNames[group]? |>.getD (Array.empty)
    IO.println s!"Definitions in group {group}: {allNames.size}"
    let allNames := allNames.filter (fun name => !doneNames.contains name.toString)
    IO.println s!"Definitions in group {group} not done: {allNames.size}"
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
