import Lean
import Mathlib.Tactic.Simps.Basic
import Mathlib.Tactic.PermuteGoals
import Mathlib.Tactic.Classical

open Lean Elab Parser Term Meta Tactic

structure TacticSnapshot where
  depth : Nat
  goalsBefore : List MVarId
  tactic : TSyntax `tactic
  goalsAfter : List MVarId
  ref : Syntax

initialize tacticSeqRef : IO.Ref (Array TacticSnapshot) ← IO.mkRef #[] 

syntax (name := seq) "seq" num tacticSeq : tactic

section Misc

  section Utils
  
  def evalTacticM (stx : TacticM Syntax) : TacticM Unit :=
    stx >>= evalTactic 

  def Lean.TSyntax.succ : TSyntax `num → TSyntax `num :=
    fun nm ↦ Syntax.mkNumLit <| toString nm.getNat.succ
  
  end Utils

end Misc

@[tactic seq]
partial def traceTactic : Tactic
  | `(tactic| seq $n $[$tacs]*) => do
    let tacs' ← tacs.mapM <|
      fun | `(tactic| $tac) => `(tactic| seq $n.succ {$tac})
    evalTacticM `(tacticSeq| $[$tacs']*) 
  | `(tactic| seq $n { $[$tacs]* }) =>
    evalTacticM `(tactic| { seq $n.succ $[$tacs]* })
  | `(tactic| seq $n · $[$tacs]*) =>
    evalTacticM `(tactic| · seq $n.succ $[$tacs]*)
  | `(tactic| seq $n focus $[$tacs]*) =>
    evalTacticM `(tactic| focus seq $n.succ $[$tacs]*)
  | `(tactic| seq $n $t:tactic) => do
    let goalsBefore ← getUnsolvedGoals
    evalTacticM `(tactic| $t)
    let goalsAfter ← getUnsolvedGoals
    let snap : TacticSnapshot := ⟨n.getNat, goalsBefore, t, goalsAfter, t⟩
    let snaps ← tacticSeqRef.get
    tacticSeqRef.set <| snaps.push snap
  | _ => panic! "Invalid `seq` format."