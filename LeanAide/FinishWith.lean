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

deriving instance Hashable for Substring
deriving instance Hashable for SourceInfo
deriving instance Hashable for Syntax.Preresolved
deriving instance Hashable for Syntax

structure GoalsInfo where
  goalsBefore : List MVarId
  goalsAfter : List MVarId
deriving BEq, Hashable, Repr

def Lean.Elab.TacticInfo.toGoalsInfo : TacticInfo → GoalsInfo
  | ⟨_, _, goalsBefore, _, goalsAfter⟩ => ⟨goalsBefore, goalsAfter⟩

#check TacticInfo.format
#check MetavarContext
#check Syntax.Stack

def Lean.Syntax.Stack.findSmallest? (stack : Syntax.Stack) (p : Syntax → Bool) : Option Syntax :=
  stack |>.map Prod.fst |>.filter p |>.head?

def Lean.Syntax.getHeadKind? (stx : Syntax) :=
  Syntax.getKind <$> stx.getHead?

def padWithIndent (s : String) (indent : Nat) : String :=
  s |>.splitOn (sep := "\n") 
    |>.map ("\n".pushn ' ' indent ++ ·)
    |> String.join

#check String.join
#check ContextInfo.ppGoals
#check Format.pretty
#check OptionT.run
#check TacticInfo
#check findIndentAndIsStart
#check Syntax.getArgs

def dummyStx : Syntax :=
  .node .none ``tacticTrivial #[.atom .none "trivial"]

@[tactic_code_action*]
def testTacticCodeAction : TacticCodeAction := fun params snap ci stk node ↦ do
  let .some block := stk.findSmallest? (·.getHeadKind? = some `«by#») | return #[]
  let .some (current, i) := stk[0]? | return #[]
  let .some (next, _) := stk[1]? | return #[]

  let .node (.ofTacticInfo info) _ := node | return #[]
  
  let goalsKey ← Format.pretty <$> ci.ppGoals info.goalsAfter

  let some start := next.getPos? | return #[]
  let some stop := next.getTailPos? | return #[]
  
  let stx := next.setArgs (next.getArgs ++ dummyStx.getArgs)

  let doc ← readDoc
  -- let res ← snap.runTermElabM doc.meta (_ : MetaM Unit)
  -- let indent := (findIndentAndIsStart doc.meta.text.source start).fst


  let eager := {
    title := "Clear tactic block."
    kind? := "quickfix"
    isPreferred? := true
    edit? := some <|.ofTextEdit params.textDocument.uri {
      range := doc.meta.text.utf8RangeToLspRange ⟨start, stop⟩
      newText := stx.reprint.get! }
    }
  return #[{ eager, lazy? := some <| do
    return eager }]

  


theorem xyz : ∀ n : ℕ, n = n := by# sorry

#check Syntax

example : 1 = 1 ↔ 2 = 2 ∧ True := by#
  constructor
  · intro
    constructor
    · skip
      sorry
    · sorry  
  · simp

-- The code action does not appear in ordinary `by` blocks, by design
example : 1 = 1 := by
  rfl