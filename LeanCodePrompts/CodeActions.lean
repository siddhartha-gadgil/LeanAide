import Lean
import LeanCodePrompts.Translate

open Lean Server Lsp RequestM

/-- Finds the comment or doc-string in the source nearest to the given position. -/
def nearestComment (source : Substring) (pos : String.Pos) : 
  Option String.Range := sorry

/-- Extracts the text contained in a comment. -/
def extractCommentText (comment : String) : Option String :=
  /- TODO: Check whether the string is a comment before trimming, 
    and extend to work for docstrings and other variants of the comment syntax. -/
  return comment.drop 2 |>.dropRight 2

/-
open Parser.Command in
def Syntax.extractComment : Syntax → Option String
  | `($doc:docComment ) => getDocStringText doc
  | _ => none

#check getDocStringText
-/

#check String.anyAux
#check String.nextUntil

/-- A code action for translating doc-strings to Lean code using OpenAI Codex -/
@[codeActionProvider] def formaliseDocStr : CodeActionProvider := fun params snap => do
  let doc ← readDoc
  let text := doc.meta.text
  let source := text.source

  let edit : IO TextEdit := return {
    range :=
      -- the end of the current snapshot
      let endPos := text.leanPosToLspPos <| text.toPosition snap.endPos
      -- the trivial range starting and ending at the last position in the current snapshot
      ⟨endPos, endPos⟩
    newText := ← do
      -- the current position in the text document
      let currentPos : String.Pos := text.lspPosToUtf8Pos params.range.end
      -- the smallest node of the `InfoTree` containing the current position
      let info? := snap.infoTree.findInfo? (·.contains currentPos)
      -- the `Syntax` corresponding to the `Info` node
      let stx? := (·.stx) <$> info?

      -- the statement to be translated to Lean code
      let stmt? : Option String := 
        (none /- TODO: First attempt to parse using `Syntax` -/)  <|>
        (do
          let snapWindow := Substring.mk source snap.beginPos snap.endPos
          let ⟨start, «end»⟩ ← nearestComment snapWindow currentPos
          let comment := source.extract start «end»
          extractCommentText comment
        ) <|> 
        (some "Every prime number is odd.")

      match stmt? with
        | some stmt => 
          let translation := snap.runTermElabM doc.meta <| translateViewM stmt
          EIO.toIO (λ _ => IO.userError "Translation failed.") translation
        | none => throw $ IO.userError "No input found."
  }

  let ca : CodeAction := { title := "Translate theorem docstring to Lean code", kind? := "quickfix" }
  return #[{ eager := ca, lazy? := some $ return {ca with edit? := WorkspaceEdit.ofTextEdit params.textDocument.uri $ ← edit} }]