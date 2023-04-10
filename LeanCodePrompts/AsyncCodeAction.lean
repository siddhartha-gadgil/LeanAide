import LeanCodePrompts.Async

open Lean Meta Elab Term Tactic Core
open Lsp Server RequestM

def textEdits (text: FileMap) : IO <| Array TextEdit := do
  let mut edits : Array TextEdit := #[]
  let m ← tacticPosCache.get
  for (k, s) in m.toArray do
    match s.tailPos? with
    | none => pure ()
    | some tailPos => 
      let edit : TextEdit := {
        range := ⟨text.leanPosToLspPos <| text.toPosition k.pos, text.leanPosToLspPos <| text.toPosition tailPos⟩
        newText := s.script.reprint.get!
      }
      edits := edits.push edit
  pure edits


@[codeActionProvider] def fillInProofs : CodeActionProvider := fun params _ => do
  let doc ← readDoc
  let text := doc.meta.text
  let edits ← textEdits text
  let mut ws : WorkspaceEdit := ∅
  for edit in edits do
    ws := ws ++ (WorkspaceEdit.ofTextEdit params.textDocument.uri edit)
  let ca : CodeAction := { 
    title := "Fill in Async Proofs", 
    kind? := "quickfix", 
    edit? := some ws,
  }
  
  return #[ca]
