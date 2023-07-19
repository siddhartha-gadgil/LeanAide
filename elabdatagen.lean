import Lean.Meta
import LeanCodePrompts
import LeanCodePrompts.BatchTranslate
open Lean

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000
set_option compiler.extract_closed false


def main (args: List String) : IO Unit := do
  let start? := (args.get? 0).bind (fun x => x.toNat?)
  let size? := (args.get? 1).bind (fun x => x.toNat?)
  initSearchPath (← Lean.findSysroot) ["build/lib", "lake-packages/mathlib/build/lib/",  "lake-packages/std/build/lib/", "lake-packages/Qq/build/lib/", "lake-packages/aesop/build/lib/", "lake-packages/proofwidgets/build/lib" ]
  let env ← 
    importModules [{module := `Mathlib},
    {module := `LeanCodePrompts.Basic},
    {module:= `LeanCodePrompts.CheckParse},
    {module:= `LeanCodePrompts.ParseJson},
    {module:= `LeanCodePrompts.Translate},
    {module := `Mathlib}] {}
  let core := elabThmSplitCore start? size?
  let io? := 
    core.run' {fileName := "", fileMap := ⟨"", #[], #[]⟩, maxHeartbeats := 100000000000, maxRecDepth := 1000000} 
    {env := env}
  match ← io?.toIO' with
  | Except.ok (succ, fail) =>
    IO.println "Success"
    IO.println s!"parsed : {succ.size}"
    IO.println s!"failed to parse: {fail.size}"
    -- let succFile := System.mkFilePath ["data/elab_thms.txt"]
    -- let h ← IO.FS.Handle.mk succFile IO.FS.Mode.append Bool.false
    -- h.putStr <| 
    --   succ.foldl (fun acc x => acc ++ s!"{x}\n") ""
  | Except.error e =>
    do
          let msg ← e.toMessageData.toString
          IO.println msg
