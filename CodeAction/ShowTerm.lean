import CodeAction.Interface

open Lean Meta Elab Parser Tactic Term

def tacticSeq.showTerm (tacSeq : TSyntax ``tacticSeq) : TacticM Unit := do
  let mvar ← getMainGoal
  evalTacticSeq tacSeq
  let some term ← getExprMVarAssignment? mvar | failure
  let term ← instantiateMVars term
  addTrace `test m!"exact {← PrettyPrinter.ppExpr term}"

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
  showTerm
    intro n
    rw [Nat.add_zero]
    rw [Nat.zero_add]

example : P → Q → P ∧ Q := by
  showTerm
    intros p q
    apply And.intro <;>
    assumption

example : P → Q → P ∧ Q := by
  showTerm
    intros p q
    apply And.intro <;>
    assumption

end Test

open Server Lsp RequestM

@[codeActionProvider]
def showTermCodeAction : CodeActionProvider := fun params _snap => do
  let doc ← readDoc
  let text := doc.meta.text

  let edit : IO TextEdit := do
    -- the current position in the text document
    let pos : String.Pos := text.lspPosToUtf8Pos params.range.end

    -- the portion of the document to be processed
    let input? : Option (Syntax × String.Range) := do 
      /- Parse the `Syntax` using the `InfoTree` -/
      -- the smallest node of the `InfoTree` containing the current position
      let info ← _snap.infoTree.findInfo? (·.stx.getKind = ``byTactic)
      pure (info.stx, ← info.range?)
    match input? with
      | some (stx, ⟨start, stop⟩) => return {
          range :=
            ⟨text.leanPosToLspPos <| text.toPosition start, 
            text.leanPosToLspPos <| text.toPosition stop⟩
          newText := ← do
            let term := elabByTactic stx none -- TODO change `none` to the theorem type
            let output ← EIO.toIO (fun _ => IO.userError "Action failed.") <|
                _snap.runTermElabM doc.meta term
            -- TODO find a better workaround for this
            -- toString <$> Lean.ppExpr {env := ← mkEmptyEnvironment} output 
            return "sorry" }
      | none => throw <| IO.userError "Parsing input failed." 

  let ca : CodeAction := { title := "Testing", kind? := "quickfix" }
  return #[{ 
    eager := ca, 
    lazy? := some $ return { ca with 
      edit? := WorkspaceEdit.ofTextEdit params.textDocument.uri $ ← edit} 
    }]

section Test

theorem xyz : 1 = 1 := sorry

theorem abc : 2 = 2 := by exact Eq.refl 2

end Test