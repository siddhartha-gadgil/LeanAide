import Lean
import Mathlib
open Lean Meta Elab Term Tactic
open Mathlib.Prelude.Rename

def usingM (type: Expr) : TacticM Unit := 
  withMainContext do
  let goal ← getMainGoal 
  let target ←  mkArrow type (← getMainTarget)
  let goal1 ← mkFreshExprMVar type
  let goal2 ← mkFreshExprMVar target 
  goal.assign (mkApp goal2 goal1)
  replaceMainGoal [goal1.mvarId!, goal2.mvarId!]

elab "using" l:term : tactic =>
  withMainContext do
    let type ← elabType l
    usingM type

example : 1 ≤ 3 := by
  using 1 ≤ 2
  · apply Nat.le_succ
  · intro h
    apply Nat.le_step
    assumption  

#check getLocalDeclFromUserName