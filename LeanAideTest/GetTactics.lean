import Lean
import LeanAideCore.SimpleFrontend
import LeanAide.Config
import Mathlib
import LeanAide.RunTactics
open LeanAide Lean Meta Elab Parser
set_option linter.unreachableTactic false

def runFrontendForMessagesM (input: String) : MetaM (List String) := do
  let msgs ← runFrontEndForMessages input
  msgs.toList.mapM (·.toString)

def runFrontendForTactics (input: String) : MetaM (List (Array Syntax.Tactic)) := do
  let msgs ← runFrontEndForMessages input
  let mut res := []
  for msg in msgs.toList do
    match ← getTacticsFromMessageData? (← msg.data.toString) with
    | some tacs =>
      logInfo s!"Tactics: {← tacs.mapM fun tac => PrettyPrinter.ppTactic tac}"
      res := res ++ [tacs]
    | none =>
      logInfo s!"No tactics found, in:{← msg.data.toString}"
      continue
  return res

example (x : Nat) : 0 < match x with
  | 0   => 1
  | n+1 => x + n := by
  grind?


#eval runFrontendForMessagesM "example (n : Nat) : n ≤ n + 1 := by grind? "


#eval runFrontendForMessagesM "example (n : Nat) : n ≤ n + 1 := by exact? "

#eval runFrontendForMessagesM "example (n : Nat) : n ≤ n + n := by grind? "


#eval runFrontendForMessagesM "example (x : Nat) : 0 < match x with
  | 0   => 1
  | n+1 => x + n := by
  grind? "


example (x : Nat) : 0 < match x with
  | 0   => 1
  | n+1 => x + n := by
  grind?

#eval runFrontendForTactics "example (n : Nat) : n ≤ n + 1 := by grind? "


#eval runFrontendForTactics "example (n : Nat) : n ≤ n + 1 := by exact? "

#eval runFrontendForTactics "example (n : Nat) : n ≤ n + n := by grind? "


#eval runFrontendForTactics "example (x : Nat) : 0 < match x with
  | 0   => 1
  | n+1 => x + n := by
  grind? "
