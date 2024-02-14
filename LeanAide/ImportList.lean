import Lean
open Lean

def imps : CoreM <| Array Name := do
  return (← getEnv).allImportedModuleNames


def writeImport (name: String) : CoreM Nat := do
  let namesFile := System.mkFilePath [s!"data/moduledeps.{name.toLower}.txt"]
  let names ← imps
  IO.FS.writeFile namesFile <|
        names.map toString |>.foldl (fun a b ↦ a  ++ b ++ "\n") ""
  return names.size
