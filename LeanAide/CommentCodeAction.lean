import Std.CodeAction.Misc

open Lean Std Parser CodeAction Elab Command Server Lsp RequestM Snapshots

syntax (name := translationComment) "//-" commentBody : command

@[command_elab translationComment]
def translationCommentElab : CommandElab := fun _ ↦ pure ()

def extractTranslationCommentBody : TSyntax ``translationComment → String
  | ⟨.node _ _ #[_, .atom _ doc]⟩ => doc.dropRight 2
  | stx => panic! s!"Ill-formed translation comment syntax: {stx}."

def dummyTranslateStatement (_stmt : String) : TermElabM String := 
  pure "\ntheorem fermat_last : ∀ x y z n : Nat, n > 2 → x^n + y^n = z^n → x * y * z = 0 := by \n  sorry"

@[command_code_action translationComment]
def translationCommentCodeAction : CommandCodeAction := fun _params _snap _ctx _info ↦ do
  let .node (.ofCommandInfo cmdInfo) _ := _info | return #[]
  let doc ← readDoc
  
  let eager := {
    title := "Auto-formalise to Lean."
    kind? := "quickfix",
    isPreferred? := true }
  return #[{
    eager
    lazy? := some do
      let stx := cmdInfo.stx
      let .some pos := stx.getTailPos? | return eager
      let res ← EIO.toIO (fun _ ↦ .userError "Translation failed.") <| _snap.runTermElabM doc.meta <|
          dummyTranslateStatement (extractTranslationCommentBody ⟨stx⟩)
      return { eager with
        edit? := some <| .ofTextEdit doc.meta.uri {
          range := doc.meta.text.utf8RangeToLspRange ⟨pos, pos⟩,
          newText := res }}
    }]