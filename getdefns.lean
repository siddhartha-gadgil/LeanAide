import LeanAide.Premises
import Lean.Meta
import LeanAide.Config
open Lean Meta LeanAide.Meta

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000
set_option compiler.extract_closed false


def main (args: List String) : IO Unit := do
  searchPathRef.set compile_time_search_path%
  let start :=
    (args.get? 0 >>= fun s => s.toNat?).getD 0
  let stop :=
    (args.get? 1 >>= fun s => s.toNat?).getD 1
  let env ←
    importModules #[{module := `Mathlib},
    {module:= `LeanAide.TheoremElab},

    {module:= `LeanAide.VerboseDelabs},
    {module:= `LeanAide.Premises},
    {module := `Mathlib}] {}
  let core : CoreM Nat :=
     writeBatchDefnsCore start stop
  let io? :=
    core.run' {fileName := "", fileMap := {source:= "", positions := #[]}, maxHeartbeats := 100000000000, maxRecDepth := 1000000, openDecls := [Lean.OpenDecl.simple `LeanAide.Meta []]
    }
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
