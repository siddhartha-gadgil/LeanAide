import Lean
import LeanCodePrompts.Translate

open Lean Server Lsp RequestM

def test : CoreM String := pure "\nexample : 1 = 1 := rfl"

/-- A code action for translating doc-strings to Lean code using OpenAI Codex -/
@[codeActionProvider] def formaliseDocStr : CodeActionProvider := fun params snap => do
  let doc ← readDoc
  let text := doc.meta.text

  let edit : IO TextEdit := return {
    range :=
      -- the end of the current snapshot
      let endPos := text.leanPosToLspPos $  text.toPosition snap.endPos
      -- the trivial range starting and ending at the last position in the current snapshot
      ⟨endPos, endPos⟩
    newText := ← do
      -- the smallest node of the `InfoTree` containing the end of the current snapshot
      let info? := snap.infoTree.findInfo? (·.tailPos?.any (· ≥ snap.endPos))
      -- the `Syntax` corresponding to the `Info` node
      let stx? := (·.stx) <$> info?
      -- the printed form of the `Syntax`
      let stmt? := stx? >>= Syntax.reprint

      if let some stmt := stmt? then
        -- assuming the input is of the form `/--s-/`
        let s := stmt.drop 3 |>.dropRight 2
        dbg_trace s
        let translation' := snap.runCoreM doc.meta $ test -- translateViewCore s
        EIO.toIO (λ _ => IO.userError "Translation failed.") translation'
      else throw $ IO.userError "Failed to extract snapshot." 
  }

  let ca : CodeAction := { title := "Translate theorem docstring to Lean code", kind? := "quickfix" }
  return #[{ eager := ca, lazy? := some $ return {ca with edit? := WorkspaceEdit.ofTextEdit params.textDocument.uri $ ← edit} }]

/-- Every prime number is either two or odd. -/
example : 1 = 1 := rfl