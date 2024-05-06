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
  initSearchPath (← Lean.findSysroot) initFiles
  let env ←
    importModules #[{module := `Mathlib},
    {module := `LeanCodePrompts.Basic},
    {module:= `LeanAide.TheoremElab},
    {module := `Mathlib}] {}
  IO.println s!"enviroment loaded: {(← IO.monoMsNow) - initTime}ms"
  let mut count := 0
  let mut elabs : Array String := Array.empty
  let prompts ← promptsIO
  IO.println s!"total size: {prompts.size}"
  for s in prompts do
    -- IO.println s!"parsing: {s}"
    let core := elabThmCore s
    let io? :=
    core.run' {fileName := "", fileMap := {source := "", positions := #[]}, maxHeartbeats := 100000000000, maxRecDepth := 1000000} {env := env}
    match ← io?.toIO' with
    | Except.ok res =>
      match res with
      | Except.ok expr =>
        -- IO.println "success"
        -- IO.println expr
        elabs:= elabs.push s
      | Except.error err =>
        -- IO.println "failure"
        -- IO.println err
        pure ()
    | Except.error e =>
      IO.println "error"
      let m := e.toMessageData
      IO.println <| ← m.toString
    count := count + 1
  IO.println s!"parsed: {count}"
  IO.println s!"success: {elabs.size}"
  IO.println s!"elapsed: {(← IO.monoMsNow) - initTime}ms"
  count := 0
  let mut ids := 0
  let mut eqs := 0
  for i in [0:elabs.size - 1] do
    for j' in [0: elabs.size/20] do
      let j := j' * 20
      let s₁ := elabs[i]!
      let s₂ := elabs[j]!
      if s₁ = s₂ then ids := ids + 1
      let core := compareThmsCore s₁ s₂
      let io? :=
      core.run' {fileName := "", fileMap := {source := "", positions := #[]}, maxHeartbeats := 100000000000, maxRecDepth := 1000000} {env := env}
      match ← io?.toIO' with
      | Except.ok res =>
        match res with
        | Except.ok expr =>
          -- IO.println "success"
          -- IO.println expr
          if expr then eqs := eqs + 1
        | Except.error err =>
          IO.println "failure"
          IO.println err
      | Except.error e =>
        IO.println "error"
        let m := e.toMessageData
        IO.println <| ← m.toString
      count := count + 1
  IO.println s!"compared: {count}"
  IO.println s!"equal: {eqs}"
  IO.println s!"identical: {ids}"
  IO.println s!"elapsed: {(← IO.monoMsNow) - initTime}ms"
