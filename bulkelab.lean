import Lean.Meta
import LeanCodePrompts
import LeanCodePrompts.BatchTranslate
open Lean

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000
set_option compiler.extract_closed false

def main (args: List String) : IO Unit := do
  initSearchPath (← Lean.findSysroot) ["build/lib", "lake-packages/mathlib/build/lib/",  "lake-packages/std/build/lib/", "lake-packages/Qq/build/lib/", "lake-packages/aesop/build/lib/" ]
  let type := (args.getD 0 "thm")
  let numSim := 
    (args.get? 1 >>= fun s => s.toNat?).getD 10 
  let numKW := 
    (args.get? 2 >>= fun s => s.toNat?).getD 1
  let includeFixed := 
    (args.get? 3 >>= fun s => s.toLower.startsWith "t").getD Bool.false
  let queryNum := 
    (args.get? 4 >>= fun s => s.toNat?).getD 5
  let temp10 :=
    (args.get? 5 >>= fun s => s.toNat?).getD 2
  let temp : JsonNumber := ⟨temp10, 1⟩
  let outFile := System.mkFilePath 
      ["results", 
      s!"{type}-elab-{numSim}-{numKW}-{includeFixed}-{queryNum}-{temp10}.json"]
  let env ← 
    importModules [{module := `Mathlib},
    {module := `LeanCodePrompts.Basic},
    {module:= `LeanCodePrompts.CheckParse},
    {module:= `LeanCodePrompts.ParseJson},
    {module:= `LeanCodePrompts.Translate},
    {module := `Mathlib}] {}
  let core := 
    checkTranslatedThmsCore type
      numSim numKW includeFixed queryNum temp
  let io? := 
    core.run' {fileName := "", fileMap := ⟨"", #[], #[]⟩, maxHeartbeats := 100000000000, maxRecDepth := 1000000} 
    {env := env}
  match ← io?.toIO' with
  | Except.ok js =>
    IO.println "Success"
    IO.FS.writeFile outFile js.pretty
  | Except.error e =>
    do
          IO.println "Ran with error"
          let msg ← e.toMessageData.toString
          IO.println msg

  return ()
