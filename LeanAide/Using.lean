import Lean
import Mathlib
open Lean Meta Elab Term Tactic
open Mathlib.Prelude.Rename

elab "using" l:term : tactic =>
  withMainContext do
    let goal ← getMainGoal 
    let target1 ← elabType l
    let target2 ←  mkArrow target1 (← getMainTarget)
    let goal1 ← mkFreshExprMVar target1
    let goal2 ← mkFreshExprMVar target2 
    goal.assign (mkApp goal2 goal1)
    replaceMainGoal [goal1.mvarId!, goal2.mvarId!]

example : 1 ≤ 3 := by
  using 1 ≤ 2
  · apply Nat.le_succ
  · intro h
    apply Nat.le_step
    assumption  

#check getLocalDeclFromUserName