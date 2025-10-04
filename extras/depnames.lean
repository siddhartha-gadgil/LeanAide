import Lean.Meta
import LeanCodePrompts
import DataGenAide.ConstDeps
import LeanAide.Config
open Lean LeanAide.Meta

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000
set_option compiler.extract_closed false

def main : IO Unit := do
  initSearchPath (← Lean.findSysroot)
  let env ←
    importModules (loadExts := true) #[
    {module := `Mathlib}] {}
  let core := offSpringShallowTripleCore
  let io? :=
    core.run' {fileName := "", fileMap := {source:= "", positions := #[]}, maxHeartbeats := 100000000000, maxRecDepth := 1000000, options := ⟨[(`synthInstance.maxHeartbeats, (DataValue.ofNat 100000))]⟩} {env := env}
  match ← io?.toIO' with
    | Except.ok _ =>
      IO.println s!"obtained triples"
      -- let file := System.mkFilePath ["extra_resources/dep_names.txt"]
      -- IO.FS.writeFile file <|
      --   res.foldl (fun acc x => acc ++ s!"{x}\n") ""
    | Except.error e =>
      IO.println "error"
      let m := e.toMessageData
      IO.println <| ← m.toString
