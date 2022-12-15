import StatementAutoformalisation.Translate

/-- A generic interface for code actions that scan the file for certain occurrences,
 process them and replace them with the output. -/
structure Interface.Params (α : Type _) where
  /-- The title of the code action. -/
  title : String
  /-- The occurrence of the desired pattern that is closest to the given position. -/
  nearestOccurrence? : (source : String) → (pos : String.Pos) → Option String.Range := fun _ _ => none
  /-- Process the selected portion of the file to extract the main text of interest. -/
  extractText? : String → Option String
  /-- The transformation to perform to the input text (for example, translation). -/
  action : String → Lean.Elab.TermElabM α
  /-- Format and render the final output. -/
  postProcess : (input : String) → (output : α) → String

open Lean Server Lsp RequestM in
/-- An abstraction for performing edits through code actions. -/
def performCodeAction {T : Type _} (iparams : Interface.Params T) : CodeActionProvider := fun params _snap => do
  let doc ← readDoc
  let text := doc.meta.text
  let source := text.source

  let edit : IO TextEdit := do
    -- the current position in the text document
    let pos : String.Pos := text.lspPosToUtf8Pos params.range.end

    -- the portion of the document to be processed
    let input? : Option (String × String.Range) :=
        ( do /- Parse the `Syntax` using the `InfoTree` -/
          -- the smallest node of the `InfoTree` containing the current position
          let info ← _snap.infoTree.findInfo? (·.contains pos)
          -- the `Syntax` corresponding to the `Info` node
          let stx := info.stx
          let rawText ← stx.reprint
          pure (← iparams.extractText? rawText, ← info.range?) )
           <|> /- alternatively -/
        ( do /- Parse the document as a string -/
          let range ← iparams.nearestOccurrence? source pos
          let rawText := source.extract range.start range.stop
          pure (← iparams.extractText? rawText, range) )

    match input? with
      | some (txt, ⟨start, stop⟩) => return {
          range :=
            ⟨text.leanPosToLspPos <| text.toPosition start, 
            text.leanPosToLspPos <| text.toPosition stop⟩
          newText := ← do
            let output ← EIO.toIO (fun _ => IO.userError "Action failed.") <|
                _snap.runTermElabM doc.meta <| iparams.action txt
            return iparams.postProcess txt output }
      | none => throw <| IO.userError "Parsing input failed."

  let ca : CodeAction := { title := iparams.title, kind? := "quickfix" }
  return #[{ 
    eager := ca, 
    lazy? := some $ return { ca with 
      edit? := WorkspaceEdit.ofTextEdit params.textDocument.uri $ ← edit} 
    }]

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
def extractCommentText? (comment : String) : Option String := do
  guard $ comment.startsWith "/-"
  guard $ comment.endsWith "-/"
  let text := comment |>.drop 2 |>.dropRight 2
  let c := text.front
  if c.isAlphanum || c.isWhitespace then
    return text
  else
    return text.drop 1