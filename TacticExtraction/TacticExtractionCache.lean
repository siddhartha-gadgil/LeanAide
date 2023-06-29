import Lean

open Lean Elab Parser Term Meta Tactic

structure TacticSnapshot where
  depth : Nat
  goalsBefore : String
  tactic : TSyntax `tactic
  goalsAfter : String
  ref : Option Syntax
deriving Inhabited


initialize counter : IO.Ref Nat ← IO.mkRef .zero

initialize tacticSnapRef : IO.Ref <|HashMap Nat (Array TacticSnapshot)
  ← IO.mkRef .empty


def counter.getIdx : IO Nat := do
  let i ← counter.get
  counter.set i.succ
  let snapsMap ← tacticSnapRef.get
  tacticSnapRef.set <| snapsMap.insert i #[]
  return i

def tacticSnapRef.getIdx (idx : Nat) : IO <| Array TacticSnapshot := do
  let snapsMap ← tacticSnapRef.get
  return snapsMap.find! idx

def tacticSnapRef.setIdx (idx : Nat) (snaps : Array TacticSnapshot) : IO Unit := do
  let snapsMap ← tacticSnapRef.get
  tacticSnapRef.set <| snapsMap.insert idx snaps

def tacticSnapRef.insert (idx : Nat) (snap : TacticSnapshot) : IO Unit := do
  let snapsMap ← tacticSnapRef.get
  let snaps ← getIdx idx
  tacticSnapRef.set <| snapsMap.insert idx (snaps.push snap)
