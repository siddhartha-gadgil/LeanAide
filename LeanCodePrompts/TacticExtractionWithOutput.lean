import Lean
import Mathlib.Tactic.Simps.Basic
import Mathlib.Tactic.PermuteGoals
import Mathlib.Tactic.Classical

open Lean Elab Parser Term Meta Tactic

structure TacticSnapshot where
  depth : Nat
  goalsBefore : List MVarId
  tactic : TSyntax ``tacticSeq
  goalsAfter : List MVarId
  ref : Syntax

initialize tacticSnapRef : IO.Ref (Array TacticSnapshot) ← IO.mkRef #[] 

def tacticSnapRef.push (snap : TacticSnapshot) : IO Unit := do
  let snaps ← tacticSnapRef.get
  tacticSnapRef.set <| snaps.push snap


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