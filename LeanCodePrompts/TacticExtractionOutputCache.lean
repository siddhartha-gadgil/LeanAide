import Lean

open Lean Elab Parser Term Meta Tactic

structure TacticSnapshot where
  depth : Nat
  goalsBefore : List MVarId
  tactic : TSyntax `tactic
  goalsAfter : List MVarId
  ref : Option Syntax

initialize tacticSnapRef : IO.Ref (Array TacticSnapshot) ← IO.mkRef #[] 

def tacticSnapRef.push (snap : TacticSnapshot) : IO Unit := do
  let snaps ← tacticSnapRef.get
  tacticSnapRef.set <| snaps.push snap