import Lean
import Mathlib.Tactic.SlimCheck
/-!
# Checked sorry

This file defines tactics that falls back to sorry if the target passes a check given by `slim_check` and possibly other checks.
-/
open Lean Meta Elab Tactic

def checkedSorry (checkType: Expr → MetaM Bool) : TacticM Unit := do
  let s ← Tactic.saveState
  let check ← checkType (← getMainTarget)
  unless check do
    throwError "checkedSorry failed: not a proposition or other requirement"
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


elab "checked_sorry" : tactic => checkedSorry (isProp)

elab "checked_sorry'" : tactic => checkedSorry (fun _ => pure true)


example : 1 + 1 = 2 := by checked_sorry
example : Nat := by
  checked_sorry'
-- example : 2 + 1 = 4 := by checked_sorry
-- example : Nat := by checked_sorry
theorem myTheorem (n: Nat): 1 + 1 = 2 := by checked_sorry

#print myTheorem

open Lean Meta Elab Term

def findSorry? (n: Name) : MetaM (Option Expr) := do
  let env ← getEnv
  let decl := env.find? n
  let e? := decl.bind (fun d => d.value?)
  return e?.bind (fun e =>
    e.find? fun expr => expr.isSorry)

#eval findSorry? `myTheorem

def replaceSorryWithMVarM? (e: Expr) : MetaM (Option (Expr × Expr × Expr)) := do
  let sorryPos? := e.find? fun expr => expr.isSorry
  sorryPos?.mapM fun sorryPos => do
    let type ← inferType sorryPos
    let mvar ← mkFreshExprMVar type
    return (e.replace (fun exp => if exp == sorryPos then some mvar else none), type, mvar)

partial def replaceAllSorriesWithMVarsM : Expr → MetaM Expr :=
  fun e => do
    let e? ← replaceSorryWithMVarM? e
    match e? with
    | some (e, _) => replaceAllSorriesWithMVarsM e
    | none => return e

partial def replaceAllSorriesWithMVarsM' (e: Expr): MetaM (Expr × List Expr × List Expr) :=
  do
    let e? ← replaceSorryWithMVarM? e
    match e? with
    | some (e, h, h') => do
      let (e', t, t') ← replaceAllSorriesWithMVarsM' e
      return (e', h::t, h'::t')
    | none => return (e, [], [])


elab "#sorry_free" n:ident : term => do
  let info ← getConstInfo n.getId
  let e := info.value!
  let (e', goals, mvars) ← replaceAllSorriesWithMVarsM' e
  logInfo m!"{e} -> {e'}"
  logInfo m!"goals: {goals}"
  logInfo m!"mvars: {mvars}"
  return e

set_option pp.mvars.withType true
#check #sorry_free myTheorem

theorem multigoal : 1 + 1 = 2 ∧ 2 + 2 = 4 ∧ 1 + 1 = 2 := by
  apply And.intro
  checked_sorry
  apply And.intro
  checked_sorry
  checked_sorry

#check #sorry_free multigoal
#check Expr.hasSorry
