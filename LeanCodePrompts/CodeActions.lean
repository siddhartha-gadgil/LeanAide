import Lean
import LeanCodePrompts.Translate

open Lean Server Lsp RequestM

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

      if let some stx := stx? then
        -- let s := stx[0]![0]![1]! |>.getAtomVal.dropRight 2
        let s := "There are infinitely many odd numbers"
        let translation' := 
          snap.runTermElabM doc.meta <| translateViewM s
        EIO.toIO (λ _ => IO.userError "Translation failed.") translation'
      else throw $ IO.userError "Failed to extract snapshot." 
  }

  let ca : CodeAction := { title := "Translate theorem docstring to Lean code", kind? := "quickfix" }
  return #[{ eager := ca, lazy? := some $ return {ca with edit? := WorkspaceEdit.ofTextEdit params.textDocument.uri $ ← edit} }]

def egTrans:= translateViewM "There are infinitely many odd numbers"

#eval egTrans

#check Snapshots.Snapshot.runTermElabM
