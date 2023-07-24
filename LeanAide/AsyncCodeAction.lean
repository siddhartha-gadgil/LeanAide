import LeanAide.Async

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
      let checkStart : Bool := 
        match s.preScript with
          | none => false
          | some pre => pre.trim == current.trim
      let edit : TextEdit := {
        range := ⟨text.leanPosToLspPos <| text.toPosition k.pos, text.leanPosToLspPos <| text.toPosition tailPos⟩
        newText := 
          if checkStart 
            then
              let stx := s.script
              let stx' := stx.raw.copyHeadTailInfoFrom .missing 
              stx'.reprint.get!.trimRight
          else current  -- ++ s!"/-change detected: {s.preScript.get!} to {current}-/"
      }
      edits := edits.push edit
  -- tacticPosCache.set ∅
  pure edits


@[code_action_provider] def fillInProofs : CodeActionProvider := fun params _ => do
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
