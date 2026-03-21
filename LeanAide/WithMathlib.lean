import Mathlib
import Lean
import LeanAideCore.RunTactics

open Lean Meta

namespace LeanAide

def minFac4M : CoreM Nat :=
  return Nat.minFac 4

def egSuggestions : MetaM (Array Name) := do
  let goalExpr ← mkFreshExprMVar (← mkAppM ``Nat.Prime #[mkConst ``Nat.zero])
  let suggs ← suggestionsForGoal goalExpr.mvarId!
  return suggs

def egSuggestionsCore : CoreM (Array Name) := do
  egSuggestions |>.run' {}

end LeanAide
