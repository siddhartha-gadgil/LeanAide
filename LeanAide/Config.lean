import Lean
import LeanAideCore.Config
import LeanAideCore.Aides.Logging
import LeanSearchClient
open Lean Meta

namespace LeanAide

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

open LeanSearchClient LibrarySuggestions  in
def stateSearchSuggestions  (leanVersion := "v4.22.0") : Selector := fun goal config =>
   do
  try
    let fmt ← ppGoal goal
    let res ← queryStateSearch fmt.pretty config.maxSuggestions leanVersion
    return (res.map fun r => {name := r.name.toName, score := 0.8})
  catch e =>
    traceAide `leanaide.interpreter.info s!"Error querying StateSearch for goal {← PrettyPrinter.ppExpr <| ← goal.getType}: {← e.toMessageData.toString}"
    return #[]

set_library_suggestions stateSearchSuggestions
-- #eval resourcesDir
