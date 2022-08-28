import Lean.Meta
import LeanCodePrompts
import LeanCodePrompts.Translate
open Lean

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000
set_option compiler.extract_closed false

def main (args: List String) : IO Unit := do
  initSearchPath (← Lean.findSysroot) ["build/lib", "lean_packages/mathlib/build/lib/", "lean_packages/lean3port/build/lib/", "lean_packages/mathlib3port/build/lib/"]
  let numSim := 
    (args.get? 0 >>= fun s => s.toNat?).getD 10 
  let numKW := 
    (args.get? 0 >>= fun s => s.toNat?).getD 4
  let includeFixed := 
    (args.get? 0 >>= fun s => s.toLower.startsWith "t").getD Bool.false
  let queryNum := 
    (args.get? 0 >>= fun s => s.toNat?).getD 5
  let temp10 :=
    (args.get? 0 >>= fun s => s.toNat?).getD 4
  let temp : JsonNumber := ⟨temp10, 1⟩
  let env ← 
    importModules [{module := `Mathlib},
    {module := `LeanCodePrompts.Basic},
    {module:= `LeanCodePrompts.CheckParse},
    {module:= `LeanCodePrompts.ParseJson},
    {module:= `LeanCodePrompts.Translate},
    {module := `Mathbin.All}] {}
  let core := 
    checkTranslatedThmsCore
      numSim numKW includeFixed queryNum temp
  let io? := 
    core.run' {fileName := "", fileMap := ⟨"", #[], #[]⟩, maxHeartbeats := 100000000000, maxRecDepth := 1000000} 
    {env := env}
  match ← io?.toIO' with
  | Except.ok _ =>
    IO.println "Success"
    -- let succFile := System.mkFilePath ["data/elab_thms.txt"]
    -- let h ← IO.FS.Handle.mk succFile IO.FS.Mode.append Bool.false
    -- h.putStr <| 
    --   succ.foldl (fun acc x => acc ++ s!"{x}\n") ""
  | Except.error e =>
    do
          let msg ← e.toMessageData.toString
          IO.println msg

  return ()
