import Lean

open Lean Elab Tactic Parser Tactic
open Lsp Server RequestM

@[code_action_provider]
def dummyCodeAction : CodeActionProvider := fun params _ ↦ do
  let ca : CodeAction := 
    {
      title := "Dummy code action", 
      kind? := "quickfix"
      disabled? := some ⟨"Inactive"⟩ -- TODO: Make a function of `params`
    }
  return #[{eager := ca, lazy? := some <| pure <| {ca with disabled? := none}}]

syntax (name := finishTac) "finish_with" tacticSeqIndentGt tacticSeq : tactic

@[tactic finishTac]
def finishTacElab : Tactic
  | `(tactic| finish_with $cmd $[$tacs]*) => do
    for tac in tacs do
      evalTactic tac
      try
        evalTactic cmd
        unless (← getGoals).isEmpty do
          throwError m!"Unfinished goals."
        logInfoAt tac m!"Goals closed with {cmd}."
      catch e => continue
  |  _ => throwUnsupportedSyntax

example : ∀ n : ℕ, n = n := by
  finish_with rfl
  intro n