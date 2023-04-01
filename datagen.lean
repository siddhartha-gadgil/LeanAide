import Lean.Meta
import LeanCodePrompts
import LeanCodePrompts.CheckParse
open Lean

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000
set_option compiler.extract_closed false


def main (args: List String) : IO Unit := do
  initSearchPath (← Lean.findSysroot) ["build/lib", "lake-packages/mathlib/build/lib/",  "lake-packages/std/build/lib/", "lake-packages/Qq/build/lib/", "lake-packages/aesop/build/lib/" ]
  let env ← 
    importModules [{module := `Mathlib},
    {module:= `LeanCodePrompts.CheckParse},
    {module := `Mathlib}] {}
  let core := promptsThmSplitCore
  let io? := 
    core.run' {fileName := "", fileMap := ⟨"", #[], #[]⟩, maxHeartbeats := 100000000000, maxRecDepth := 1000000} 
    {env := env}
  match ← io?.toIO' with
  | Except.ok (succ, fail) =>
    IO.println "Success"
    IO.println s!"parsed : {succ.size}"
    IO.println s!"failed to parse: {fail.size}"
    let succFile := System.mkFilePath ["data/parsed_thms.txt"]
    IO.FS.writeFile succFile <| 
      succ.foldl (fun acc x => acc ++ s!"{x}\n") ""
    let failFile := System.mkFilePath ["data/unparsed_thms.txt"]
    IO.FS.writeFile failFile <| 
      fail.foldl (fun acc x => acc ++ s!"{x}\n") ""
  | Except.error e =>
    do
          let msg ← e.toMessageData.toString
          IO.println msg
