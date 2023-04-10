import Lean
import LeanCodePrompts.TacticExtractionOutputCache
import Mathlib.Tactic.Simps.Basic
import Mathlib.Tactic.PermuteGoals
import Mathlib.Tactic.Classical

open Lean Elab Parser Term Meta Tactic

section Misc

  section Utils
  
  def evalTacticM (stx : TacticM <| TSyntax `tactic) : TacticM Unit :=
    stx >>= evalTactic ∘ TSyntax.raw

  def Lean.TSyntax.succ : TSyntax `num → TSyntax `num :=
    fun nm ↦ Syntax.mkNumLit <| toString nm.getNat.succ

  end Utils

  section Logging

  def logTacticSnapshot (depth : ℕ) (tac : TSyntax `tactic) (ref : Option Syntax := some tac) : TacticM Unit := do
    let goalsBefore ← getUnsolvedGoals
    evalTacticM <| pure tac
    let goalsAfter ← getUnsolvedGoals
    let snap : TacticSnapshot := ⟨depth, goalsBefore, tac, goalsAfter, ref⟩
    tacticSnapRef.push snap

  end Logging

end Misc

syntax (name := snap) "snap" num tactic : tactic
syntax (name := seq) "seq" num tacticSeq : tactic

macro_rules
  | `(tactic| seq $n $[$tacs]*) => do
    let tacs' ← tacs.mapM <|
      fun tac ↦ `(tactic| snap $n.succ $tac)
    `(tactic| {$[$tacs']*})

@[tactic seq] def traceSeq : Tactic
  | `(tacticSeq| seq $n $[$tacs]*) => do
    -- withoutModifyingState <| logTacticSnapshot n.getNat <| ← `(tactic| {$[$tacs]*} )
    dbg_trace n
    for tac in tacs do
      evalTacticM `(tactic| snap $n.succ $tac)
  | _ => panic! "Invalid `seq` format."

@[tactic snap] partial def traceTacticSnap : Tactic
  | `(tactic| snap $n $t:tactic) => do
    withRef t <| logInfo n
    logTacticSnapshot n.getNat t
  | _ => panic! "Invalid `snap` format."

section ByTactic

-- a clone of the `by` tactic
syntax (name := byTactic') "by' " tacticSeq : term

@[term_elab byTactic'] def elabByTactic' : TermElab := fun stx expectedType? => do
  match expectedType? with
  | some expectedType =>
    let mvar ← mkFreshExprMVar expectedType MetavarKind.syntheticOpaque
    let mvarId := mvar.mvarId!
    let ref ← getRef
    registerSyntheticMVar ref mvarId <| SyntheticMVarKind.tactic stx (← saveContext)
    return mvar
  | none =>
    tryPostpone
    throwError ("invalid 'by\'' tactic, expected type has not been provided")

-- intercepting the `by` tactic to output intermediate trace data
-- the `by'` clone is needed here to avoid infinite recursion
macro_rules
  | `(by $t) => `(by' seq 0 $t) 

end ByTactic

#eval do
  let tacs ← (tacticSnapRef.get : IO _)
  return tacs.size

example : ∀ n : Nat, n = n := by
  intro n
  rfl

#eval do
  let tacs ← (tacticSnapRef.get : IO _)
  return tacs.size