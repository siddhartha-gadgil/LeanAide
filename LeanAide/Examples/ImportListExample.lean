import Lean
import Mathlib.Data.Nat.Prime
open Lean

def imps : CoreM <| Array Name := do
  return (← getEnv).allImportedModuleNames

#eval imps

def writeImport : CoreM Nat := do
  let namesFile := System.mkFilePath ["data/prime_deps.txt"] 
  let names ← imps
  IO.FS.writeFile namesFile <| 
        names.map toString |>.foldl (fun a b ↦ a  ++ b ++ "\n") ""
  return names.size

#eval writeImport