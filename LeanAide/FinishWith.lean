import Lean
import Std

open Lean Elab Tactic Parser Tactic Term
open Lsp Server RequestM
open Std Tactic CodeAction

def Lean.Elab.GoalsAtResult.display (goalsAt : Lean.Elab.GoalsAtResult) : IO (Format × Format) := do
  let goalsBefore ← goalsAt.ctxInfo.ppGoals goalsAt.tacticInfo.goalsBefore
  let goalsAfter ← goalsAt.ctxInfo.ppGoals goalsAt.tacticInfo.goalsAfter
  return (goalsBefore, goalsAfter)

syntax (name := bySharpTac) "by#" tacticSeq : term

@[term_elab bySharpTac] def bySharpElab : TermElab
  | stx@`(term| by# $tacs), type? => do
    let by_block ← `(term| by $tacs)
    -- TryThis.addSuggestion stx by_block
    elabTerm by_block type?
  | _, _ => throwUnsupportedSyntax

@[tactic_code_action*]
def testTacticCodeAction : TacticCodeAction := fun params snap ci stk node ↦ do
  let .node (.ofTacticInfo info) _ := node | return #[]
  let .some (tacs, _) := stk[stk.length - 4]? | return #[]
  -- ensures that the tactic is within an `async` block
  unless (Syntax.getKind <$> tacs.getHead?) = some `«by#» do
    return #[]
  
  let some start := tacs.getPos? | return #[]
  let some stop := tacs.getTailPos? | return #[]

  let doc ← readDoc
  let eager := {
    title := "Clear tactic block."
    kind? := "quickfix"
    isPreferred? := true
    edit? := some <|.ofTextEdit params.textDocument.uri {
      range := doc.meta.text.utf8RangeToLspRange ⟨start, stop⟩
      newText := "sorry"
    }
  }
  pure #[{ eager }]

  


theorem xyz : ∀ n : ℕ, n = n := by#
  skip
  simp

example : 1 = 1 ↔ 2 = 2 := by#
  constructor
  · intro
    rfl
  · intro
    rfl  

-- The code action does not appear in ordinary `by` blocks, by design
example : 1 = 1 := by
  rfl