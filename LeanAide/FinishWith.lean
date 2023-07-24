import Lean
import Std

open Lean Elab Tactic Parser Tactic
open Lsp Server RequestM

def Lean.Elab.GoalsAtResult.display (goalsAt : Lean.Elab.GoalsAtResult) : IO (Format × Format) := do
  let goalsBefore ← goalsAt.ctxInfo.ppGoals goalsAt.tacticInfo.goalsBefore
  let goalsAfter ← goalsAt.ctxInfo.ppGoals goalsAt.tacticInfo.goalsAfter
  return (goalsBefore, goalsAfter)

@[code_action_provider]
def dummyCodeAction : CodeActionProvider := fun params snap ↦ do
  let doc ← readDoc
  let text := doc.meta.text
  -- the current position in the text document
  let pos : String.Pos := text.lspPosToUtf8Pos params.range.end
  let allGoals ← snap.infoTree.goalsAt? text pos |>.mapM (GoalsAtResult.display ·)
  let data := Format.pretty <| Format.join <|
    allGoals.foldl (fun l (goalsBefore, goalsAfter) ↦ goalsBefore :: goalsAfter :: l) []

  let ca : CodeAction := 
    {
      title := "Show tactic state here", 
      kind? := "quickfix"
    }
  return #[{
    eager := ca, 
    lazy? := some do
      dbg_trace data
      return ca
  }]

syntax (name := finishTac) "finish_with" tacticSeqIndentGt tacticSeq : tactic

#check addMessageContext

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

#check Snapshot
#check Std.Tactic.TryThis.addSuggestion
#check InfoTree.hoverableInfoAt?
#check InfoTree.goalsAt?
#check GoalsAtResult
#check ContextInfo
#check ContextInfo.ppGoals
#check TacticInfo
#check ElabInfo
#check LocalContext
#check TacticInfo.format
#check MetavarContext
#check Format
#check FileWorker.EditableDocument

example : ∀ n : ℕ, ∀ m : ℕ, n = n := by
  intros
  sorry
