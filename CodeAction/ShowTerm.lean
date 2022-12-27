import CodeAction.Interface

open Lean Meta Elab Parser Tactic

def tacticSeq.showTerm (tacSeq : TSyntax ``tacticSeq) : TacticM Unit := do
  let mvar ← getMainGoal
  evalTacticSeq tacSeq
  let some term ← getExprMVarAssignment? mvar | failure
  let term ← instantiateMVars term
  addTrace `test m!"{← PrettyPrinter.ppExpr term}"

elab "showTerm " t:tacticSeq : tactic =>
  tacticSeq.showTerm t

section Test

example : True := by
  showTerm
    trivial

example : true := by
  showTerm
    rfl

example : ∀ n : Nat, n + .zero = .zero + n := by
  intro n
  showTerm
    rw [Nat.add_zero]
  showTerm
    rw [Nat.zero_add]

example : P → Q → P ∧ Q := by
  showTerm
    intros
    apply And.intro <;>
    assumption

example : P → Q → P ∧ Q := by
  intros p q
  showTerm 
    -- TODO debug the diplayed names issue
    apply And.intro <;>
    assumption

end Test