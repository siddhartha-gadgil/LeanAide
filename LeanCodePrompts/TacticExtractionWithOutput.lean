import Lean
import LeanCodePrompts.TacticExtractionOutputCache
import Mathlib.Tactic.Simps.Basic
import Mathlib.Tactic.PermuteGoals
import Mathlib.Tactic.Classical

open Lean Elab Parser Term Meta Tactic

syntax (name := seq) "seq" num tacticSeq : tactic

section Misc

  section Utils
  
  def evalTacticM (stx : TacticM <| TSyntax ``tacticSeq) : TacticM Unit :=
    stx >>= evalTactic ∘ TSyntax.raw 

  def Lean.TSyntax.succ : TSyntax `num → TSyntax `num :=
    fun nm ↦ Syntax.mkNumLit <| toString nm.getNat.succ
  
  instance : Coe (TSyntax `tactic) (TSyntax ``tacticSeq) where
    coe 
      | `(tactic| $tac) => ⟨tac⟩

  end Utils

  section Logging

  def logTacticSnapshot (depth : ℕ) (tac : TSyntax ``tacticSeq) (ref : Syntax := tac) : TacticM Unit := do
    let goalsBefore ← getUnsolvedGoals
    evalTacticM <| pure tac
    let goalsAfter ← getUnsolvedGoals
    let snap : TacticSnapshot := ⟨depth, goalsBefore, tac, goalsAfter, ref⟩
    tacticSnapRef.push snap

  end Logging

end Misc

@[tactic seq]
partial def traceTactic : Tactic
  | `(tactic| seq $n $[$tacs]*) => do
    withoutModifyingState <| logTacticSnapshot n.getNat <| ← `(tacticSeq| $[$tacs]*)
    let tacs' ← tacs.mapM <|
      fun | `(tactic| $tac) => `(tactic| seq $n.succ {$tac})
    evalTacticM `(tacticSeq| $[$tacs']*) 
  | `(tactic| seq $n { $[$tacs]* }) => do
    withoutModifyingState <| logTacticSnapshot n.getNat <| ← `(tacticSeq| { $[$tacs]* })
    evalTacticM `(tactic| { seq $n.succ $[$tacs]* })
  | `(tactic| seq $n · $[$tacs]*) => do
    withoutModifyingState <| logTacticSnapshot n.getNat <| ← `(tacticSeq| · $[$tacs]*)
    evalTacticM `(tactic| · seq $n.succ $[$tacs]*)
  | `(tactic| seq $n focus $[$tacs]*) => do
    withoutModifyingState <| logTacticSnapshot n.getNat <| ← `(tacticSeq| focus $[$tacs]*)
    evalTacticM `(tactic| focus seq $n.succ $[$tacs]*)
  | `(tactic| seq $n $t:tactic) => do
    logTacticSnapshot n.getNat t
  | _ => panic! "Invalid `seq` format."


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