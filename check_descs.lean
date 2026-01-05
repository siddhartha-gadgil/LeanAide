import Lean.Meta
import LeanCodePrompts
import LeanAide.TheoremElab
import LeanAide.TheoremElabCheck
import LeanCodePrompts.Makecaps
import LeanAide.Config
open Lean LeanAide

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000
set_option compiler.extract_closed false


def main : IO Unit := do
  initSearchPath (← Lean.findSysroot)
  let env ←
    importModules (loadExts := true) #[{module := `Mathlib},
    {module:= `LeanAide.TheoremElab}, {module:= `LeanAide.TheoremElabCheck},
    {module := `Mathlib}] {}
  let jsLines ← IO.FS.lines ((← resourcesDir) / "mathlib4-descs.jsonl")
  let mut count := 0
  let mut errorCount := 0
  for line in jsLines do
    count := count + 1
    if count % 100 == 0 then
      logToStdErr `leanaide.translate.info s!"{count}, errors : {errorCount}"
    let .ok js := Json.parse line | throw <| IO.userError s!"Failed to parse JSON line: {line}"
    let .ok name := js.getObjValAs? String "name" | throw <| IO.userError s!"Failed to parse JSON line: {line}"
    let .ok s := js.getObjValAs? String "type" | throw <| IO.userError s!"Failed to parse JSON line: {line}"
    let core := elabThm4 s |>.runToCore
    let io? :=
    core.run' {fileName := "", fileMap := {source:= "", positions := #[]}, maxHeartbeats := 100000000000, maxRecDepth := 1000000} {env := env}
    match ← io?.toIO' with
    | Except.ok res =>
      match res with
      | Except.ok _ =>
        IO.println s!"Succeeded for {name} : {s}"
      | Except.error err =>
        logToStdErr `leanaide.translate.info "failure"
        IO.println s!"Failed for {name} : {s}"
        IO.println err.error
        errorCount := errorCount + 1
        IO.println "----"
    | Except.error e =>
      logToStdErr `leanaide.translate.info "error"
      let m := e.toMessageData
      logToStdErr `leanaide.translate.info <| ← m.toString
      logToStdErr `leanaide.translate.info s!"Failed for {name} : {s}"
      logToStdErr `leanaide.translate.info "----"
