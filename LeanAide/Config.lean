import Lean
import LeanAideCore.Config
open Lean Meta

def initFiles : List System.FilePath := [".lake/build/lib", ".lake/packages/mathlib/.lake/build/lib",  ".lake/packages/Qq/.lake/build/lib", ".lake/packages/aesop/.lake/build/lib", ".lake/packages/proofwidgets/.lake/build/lib", ".lake/packages/importGraph/.lake/build/lib", ".lake/packages/batteries/.lake/build/lib", ".lake/packages/plausible/.lake/build/lib", ".lake/packages/batteries/.lake/CLi/lib", ".lake/packages/LeanSearchClient/.lake/build/lib" ]

def baseDirImpl : IO System.FilePath := do
  let pathLeanAidePackages := System.mkFilePath [".lake","packages","leanaide"]
  let leanAide := System.mkFilePath ["LeanAide"]
  let resources := System.mkFilePath ["resources"]
  if (← (((← IO.currentDir).join leanAide).pathExists)) &&
  (← (((← IO.currentDir).join resources).pathExists)) then
    return (← IO.currentDir)
  else if (← ((pathLeanAidePackages.join leanAide).pathExists)) && (← ((pathLeanAidePackages.join resources).pathExists)) then
    return pathLeanAidePackages
  else
    throw (IO.userError "LeanAide not found.")

instance : LeanAideBaseDir where
  baseDir := baseDirImpl


-- #eval resourcesDir
