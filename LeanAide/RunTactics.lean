import Lean
import LeanAideCore.Aides
import LeanAideCore.SimpleFrontend
import LeanAideCore.RunTactics
-- import LeanSearchClient
import Hammer

open Lean Meta Elab Term PrettyPrinter Nat Tactic

namespace LeanAide


-- open LibrarySuggestions in
-- def suggestionsForGoal' (goal: MVarId) (maxSuggestions: Nat := 30) : MetaM (Array Name) := do
--   try
--     let selector ← getSelector
--     let defaultSelector := Cloud.premiseSelector <|> mepoSelector (useRarity := true) (p := 0.6) (c := 0.9)
--     let selector := selector.getD defaultSelector
--     let suggestions ← selector goal {maxSuggestions := maxSuggestions}
--     return (suggestions.map fun s => s.name)
--   catch e =>
--     traceAide `leanaide.interpreter.info s!"Error querying StateSearch for goal {← PrettyPrinter.ppExpr <| ← goal.getType}: {← e.toMessageData.toString}"
--     return #[]


-- def suggestionsForGrind' (goal: MVarId) (maxSuggestions: Nat := 15)  : MetaM (Array Name) := do
--   let all ← suggestionsForGoal' goal maxSuggestions
--   all.filterM fun name => checkGrind name

open Parser.Tactic
-- def grindWithSuggestions' (goal: MVarId) (localNames : Array Name) (maxSuggestions: Nat := 15)  : MetaM (TSyntax ``tacticSeq) := do
--   let names ← suggestionsForGrind' goal maxSuggestions
--   let names := names ++ localNames
--   let params : Array (TSyntax ``grindParam) ← names.mapM fun
--     name => do
--       let id := mkIdent name
--       `(grindParam| $id:ident)
--   `(tacticSeq| grind? [$params,*])

-- def simpWithSuggestions' (goal: MVarId) (localNames : Array Name) (maxSuggestions: Nat := 15) : MetaM (TSyntax ``tacticSeq) := do
--   let names ← suggestionsForGoal' goal maxSuggestions
--   let names := names ++ localNames
--   let params : Array (TSyntax ``simpLemma) ← names.mapM fun
--     name => do
--       let id := mkIdent name
--       `(simpLemma| $id:ident)
--   `(tacticSeq| simp? [$params,*])

def getHammerTactics? (goal: MVarId) : TermElabM <| Option (TSyntax ``tacticSeq) := do
  let tactics? ← runTacticsAndGetTryThis? goal #[(← `(tactic| hammer {aesopPremises := 5, autoPremises := 0}))]
  match tactics? with
  | none => return none
  | some tacs =>
    if tacs.isEmpty then
      return none
    else
      let tacticCode ←  `(tacticSeq| $tacs*)
      return some tacticCode


end LeanAide
