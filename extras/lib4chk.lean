import Lean.Meta
import LeanCodePrompts
import LeanAide.TheoremElab
import LeanCodePrompts.Makecaps
import LeanAide.Config
open Lean

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000
set_option compiler.extract_closed false

def promptsIO : IO (Array String) := do
  let file := System.mkFilePath ["data/all_outputs.txt"]
  let lines ← IO.FS.lines file
  let cls := lines.map mkCap
  return cls

def main : IO Unit := do
  IO.println "starting"
  let initTime ← IO.monoMsNow
  let file := System.mkFilePath ["data/lib4_outputs.txt"]
  let lines ← IO.FS.lines file
  IO.println "loaded file"
  searchPathRef.set compile_time_search_path%
  let env ←
    importModules #[{module := `Mathlib},
    {module := `LeanCodePrompts.Basic},
    {module:= `LeanAide.TheoremElab},
    {module := `Mathlib}] {}
  IO.println s!"enviroment loaded: {(← IO.monoMsNow) - initTime}ms"
  let mut count := 0
  let mut failures := 0
  let mut elabs : Array String := Array.empty
  IO.println s!"total size: {lines.size}"
  for s in lines do
    -- IO.println s!"parsing: {s}"
    let core := elabThmCore s
    let io? :=
    core.run' {fileName := "", fileMap := {source:= "", positions := #[]}, maxHeartbeats := 100000000000, maxRecDepth := 1000000} {env := env}
    match ← io?.toIO' with
    | Except.ok res =>
      match res with
      | Except.ok _ =>
        IO.println "success"
        elabs:= elabs.push s
        IO.println s!"successes: {elabs.size}"
        IO.println s!"failures: {failures}"
        IO.println s!"total: {count} out of {lines.size}"
      | Except.error err =>
        IO.println "failure"
        failures := failures + 1
        IO.println s!"failures: {failures}"
        IO.println s!"successes: {elabs.size}"
        IO.eprintln s
        IO.eprintln err
        IO.eprintln "-----------------------------------------"
        pure ()
    | Except.error e =>
      IO.println "error"
      let m := e.toMessageData
      IO.println <| ← m.toString
    count := count + 1
  IO.println s!"parsed: {count}"
  IO.println s!"success: {elabs.size}"
  IO.println s!"failures: {failures}"
  IO.println s!"elapsed: {(← IO.monoMsNow) - initTime}ms"
