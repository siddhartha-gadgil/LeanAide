import Lean
import Mathlib.Tactic.Basic
import Aesop

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
    -- the node of the infotree containing the current position
    let some info := _snap.infoTree.findInfo? (·.contains pos) | IO.throwServerError "Infotree not found"
    match info.stx with
    -- TODO allow docstrings
    | `(theorem $nm:ident $args* : $typ:term := by $tacs:tacticSeq) =>
      let pptrm : TermElabM Syntax := do
        let typ ← instantiateMVars <| ← elabType typ
        synthesizeSyntheticMVarsNoPostponing
        let trm ← instantiateMVars <| ← elabByTactic tacs typ
        synthesizeSyntheticMVarsNoPostponing
        let trm ← reduce trm
        synthesizeSyntheticMVarsNoPostponing
        PrettyPrinter.delab trm
      let some ⟨start, stop⟩ := tacs.raw.getRange? | IO.throwServerError "Failed to obtain range"
      let output : TSyntax `term := ⟨← EIO.toIO (fun _ => IO.userError "Code action failed") <|
          _snap.runTermElabM doc.meta pptrm⟩
      return {
        range := 
            ⟨text.leanPosToLspPos <| text.toPosition start, 
            text.leanPosToLspPos <| text.toPosition stop⟩,
        newText := ← do
          return output.raw.reprint.get!
      }
    | _ => IO.throwServerError "Parsing input failed. Input must be a `theorem` or `def` with a tactic proof."

  let ca : CodeAction := { title := "Show the term corresponding to the tactic proof.", kind? := "quickfix" }
  return #[{ 
    eager := ca, 
    lazy? := some $ return { ca with 
      edit? := WorkspaceEdit.ofTextEdit params.textDocument.uri $ ← edit} 
    }]

section Test

theorem xyz : 1 = 1 := by exact Eq.refl 1

theorem abc (n : Nat) (m : Nat) : n ≥ 0 ↔ m ≥ 0 := by
  showTerm
  refine' ⟨fun _ => _, fun _ => _⟩ <;>
  apply Nat.zero_le

end Test

#check Snapshots.Snapshot.env
#check synthesizeSyntheticMVarsNoPostponing
#check evalTacticSeq
#print Tactic
#check Tactic.run
#check Snapshots.Snapshot.tacticCache
#check Tactic.Cache
#check InfoTree.goalsAt?
#check ContextInfo

set_option tactic.simp.trace true
-- set_option trace.Elab.definition.structural true
-- set_option pp.analyze true

-- macro "simp" args:Std.Tactic.simpTraceArgsRest : tactic => `(tactic| simp? $args) 
macro "aesop" args:Aesop.tactic_clause* : tactic => `(tactic| aesop? $args:Aesop.tactic_clause*)

declare_aesop_rule_sets [test]

example : a + 0 = a := by dsimp