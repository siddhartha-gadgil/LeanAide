import LeanAide.SimpleFrontend
import LeanAideCore.Aides
import Mathlib

open LeanAide Lean Meta Elab

open scoped Nat

universe u v w u_1 u_2 u_3 u₁ u₂ u₃

namespace LeanAideTest

/-- info: #[`x] -/
#guard_msgs in
#eval newDeclarations "def x : Nat := 0"

elab "#new_defs" s:str : command => Command.liftTermElabM do
  let s := s.getString
  let (nameDefs, msgs) ← elabFrontDefsNewExprM s
  for (n, v) in nameDefs do
    logInfo s!"New definition: {n} with value {← ppExpr v}"
  for msg in msgs.toList do
    logInfo msg.data

/-- info: New definition: y with value 1 -/
#guard_msgs in
#new_defs "def y : Nat := 1"

/-- info: ok: ∀ {G : Type u} [inst : Group G] (a : G) (n : ℕ), a ^ n = 1 → ∃ m, n = m * orderOf a -/
#guard_msgs in
#eval ppExprM? <| elabFrontTheoremExprM "∀ {G : Type u} [inst : Group G] (a : G) (n : ℕ), a ^ n = 1 → ∃ m : ℕ, n = m * orderOf a"


end LeanAideTest
