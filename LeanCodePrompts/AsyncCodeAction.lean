import LeanCodePrompts.Async

open Lean Meta Elab Term Tactic Core
open Lsp Server RequestM

def textEdits (text: FileMap) : IO <| Array TextEdit := do
  let mut edits : Array TextEdit := #[]
  let m ← tacticPosCache.get
  let source := text.source
  for (k, s) in m.toArray do
    match s.tailPos? with
    | none => pure ()
    | some tailPos => 
      let current := source.extract k.pos tailPos
      let edit : TextEdit := {
        range := ⟨text.leanPosToLspPos <| text.toPosition k.pos, text.leanPosToLspPos <| text.toPosition tailPos⟩
        newText := 
          if (current.trim = s.preScript.trim) 
            then s.script.reprint.get!.trimRight
          else current ++ s!"/-change detected: {s.preScript} to {current}-/"
      }
      edits := edits.push edit
  -- tacticPosCache.set ∅
  pure edits


@[codeActionProvider] def fillInProofs : CodeActionProvider := fun params _ => do
  let doc ← readDoc
  let text := doc.meta.text
  let edits ← textEdits text
  let ws : IO WorkspaceEdit := do
    let mut ws : WorkspaceEdit := ∅
    for edit in edits do
      ws := ws ++ (WorkspaceEdit.ofTextEdit params.textDocument.uri edit)
    return ws
  let ca : CodeAction := { 
    title := "Fill in Async Proofs", 
    kind? := "quickfix", 
  }
  
  return #[{ eager := ca, lazy? := some $ return {ca with 
  edit? := some <| ← ws}}]
