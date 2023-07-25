import Lean
import Std.Tactic.TryThis

open Lean Elab Tactic Parser Tactic Term
open Lsp Server RequestM
open Std Tactic

def Lean.Elab.GoalsAtResult.display (goalsAt : Lean.Elab.GoalsAtResult) : IO (Format × Format) := do
  let goalsBefore ← goalsAt.ctxInfo.ppGoals goalsAt.tacticInfo.goalsBefore
  let goalsAfter ← goalsAt.ctxInfo.ppGoals goalsAt.tacticInfo.goalsAfter
  return (goalsBefore, goalsAfter)

syntax (name := finishTac) "finish_with" tacticSeqBracketed tacticSeq : tactic

@[tactic finishTac]
def finishTacElab : Tactic
  | stx@`(tactic| finish_with $cmd $[$tacs]*) => do
    for tac in tacs do
      try
        evalTactic cmd
        unless (← getGoals).isEmpty do
          throwError m!"Unfinished goals."
        logInfoAt tac m!"Goals closed with {cmd}."
      catch e => continue
      evalTactic tac
  |  _ => throwUnsupportedSyntax

-- A dummy version of `by#` to test `Try this ...` replacement
syntax (name := bySharpTac) "by#" tacticSeq : term

@[term_elab bySharpTac] def bySharpElab : TermElab
  | stx@`(term| by# $tacs), type? => do
    let by_block ← `(term| by $tacs)
    TryThis.addSuggestion stx by_block
    elabTerm by_block type?
  | _, _ => throwUnsupportedSyntax

example : ∀ n : ℕ, n = n := by#
  intro n
  rfl