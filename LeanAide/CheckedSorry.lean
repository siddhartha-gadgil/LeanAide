import Lean
import Mathlib.Tactic.SlimCheck
/-!
# Checked sorry

This file defines tactics that falls back to sorry if the target passes a check given by `slim_check` and possibly other checks.
-/
open Lean Meta Elab Tactic

def checkedSorry (allowType: Bool := false) : TacticM Unit := do
  let s ← Tactic.saveState
  unless allowType || (← isProp (← getMainTarget)) do
    throwError "checkedSorry failed: not a proposition"
  try
    evalTactic (← `(tactic|slim_check))
    s.restore
    evalTactic (← `(tactic|sorry))
  catch e =>
    let msgs := e.toMessageData
    let msgs ← msgs.toString
    if (msgs.splitOn "Found problems!").length > 1 then
      throwError "checkedSorry failed with {e.toMessageData}"
    else
      s.restore
      evalTactic (← `(tactic|sorry))


elab "checked_sorry" : tactic => checkedSorry

elab "checked_sorry'" : tactic => checkedSorry true


example : 1 + 1 = 2 := by checked_sorry
example : Nat := by
  checked_sorry'
-- example : 2 + 1 = 4 := by checked_sorry
-- example : Nat := by checked_sorry
