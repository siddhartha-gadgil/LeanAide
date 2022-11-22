import Lean
import LeanCodePrompts.Translate

open Lean Server Lsp RequestM

partial def String.Iterator.findFirst? : String.Iterator → String → Option String.Pos
  | i, pre => if i.hasNext then
    if i.remainingToString.startsWith pre then 
      some i.pos 
    else 
      i.next.findFirst? pre
  else none

def String.Range.expand : String.Range → Nat → String.Range
  | ⟨start, stop⟩, i => ⟨start - ⟨i⟩, stop + ⟨i⟩⟩

/-- Finds the comment or doc-string in the source nearest to the given position. -/
partial def nearestComment (source : String) 
  (pos : String.Pos) (start : String.Pos := ⟨0⟩) : Option String.Range := do
    guard $ start ≤ pos
    let firstCommentRange ← findFirstComment? source start
    if (firstCommentRange.expand 2).contains pos then
      some firstCommentRange
    else
      nearestComment source pos (source.next firstCommentRange.stop)
  where findFirstComment? (source : String) (init : String.Pos) : Option String.Range := do
    let start ← (String.Iterator.mk source init).findFirst? "/-"
    let stop ← (String.Iterator.mk source start).findFirst? "-/"
    return ⟨start, stop + ⟨2⟩⟩

/-- Extracts the text contained in a comment. -/
def extractCommentText (comment : String) : Option String := do
  guard $ comment.startsWith "/-"
  guard $ comment.endsWith "-/"
  let text := comment |>.drop 2 |>.dropRight 2
  let c := text.front
  if c.isAlphanum || c.isWhitespace then
    return text
  else
    return text.drop 1

/-
open Parser.Command in
def Syntax.extractComment : Syntax → Option String
  | `($doc:docComment ) => getDocStringText doc
  | _ => none

#check getDocStringText
-/

/-- A code action for translating doc-strings to Lean code using OpenAI Codex -/
@[codeActionProvider] def formaliseDocStr : CodeActionProvider := fun params snap => do
  let doc ← readDoc
  let text := doc.meta.text
  let source := text.source

  let edit : IO TextEdit := do
    -- the current position in the text document
    let pos : String.Pos := text.lspPosToUtf8Pos params.range.end
    let some ⟨start, stop⟩ := nearestComment source pos | throw $ IO.userError "No input found."
    return {
    range := ⟨text.leanPosToLspPos <| text.toPosition start, text.leanPosToLspPos <| text.toPosition stop⟩
    newText := ← do
      -- the smallest node of the `InfoTree` containing the current position
      let info? := snap.infoTree.findInfo? (·.contains pos)
      -- the `Syntax` corresponding to the `Info` node
      let stx? := (·.stx) <$> info?

      -- the statement to be translated to Lean code
      let stmt? : Option String := 
        (none /- TODO: First attempt to parse using `Syntax` -/)  <|>
        ( /- Parse as a string -/
          let comment := source.extract start stop
          extractCommentText comment
        )

      let translation' := snap.runTermElabM doc.meta <| translateViewM stmt?.get!
      let translation ← EIO.toIO (λ _ => IO.userError "Translation failed.") translation'
      return formatAsTheorem stmt? translation
  }

  let ca : CodeAction := { title := "Translate theorem docstring to Lean code", kind? := "quickfix" }
  return #[{ eager := ca, lazy? := some $ return {ca with edit? := WorkspaceEdit.ofTextEdit params.textDocument.uri $ ← edit} }]
where
  formatAsTheorem : Option String → String → String
    | some comment, type => s!"/--{comment}-/\nexample : {type.trim} := sorry"
    |     none    , type => s!"\nexample : {type.trim} := sorry"


open RequestM in
@[codeActionProvider]
def readFile : CodeActionProvider := fun params _snap => do
  let doc ← readDoc
  let text := doc.meta.text
  let source := text.source
  let pos := text.lspPosToUtf8Pos params.range.end
  let edit : TextEdit := {
    range := params.range
    newText :=
      let tail := Substring.mk source pos source.endPos
      let tail := tail.toString.splitOn "/-" |>.head!
      "/- " ++ tail ++ "-/"
  }
  let ca : CodeAction := {title := "tail of source", kind? := "quickfix"}
  return #[{eager := ca, lazy? := some $ return { ca with edit? := WorkspaceEdit.ofTextEdit params.textDocument.uri edit}}]
  
/- 

example : 1 = 1 := by
  simp
-/


/-- There are infinitely many odd numbers -/
example : ∀ (n : ℕ), ∃ m, m > n ∧ m % 2 = 1 := sorry
