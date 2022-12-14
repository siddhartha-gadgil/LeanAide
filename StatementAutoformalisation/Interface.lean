import StatementAutoformalisation.Translate

/-- A generic interface for code actions that scan the file for certain occurrences,
 process them and replace them with the output. -/
structure Interface.Params (α : Type _) where
  /-- The title of the code action. -/
  title : String
  /-- The occurrence of the desired pattern that is closest to the given position. -/
  nearestOccurrence? : (source : String) → (pos : String.Pos) → Option String.Range
  /-- Process the selected portion of the file to extract the main text of interest. -/
  extractText? : String → Option String
  /-- The transformation to perform to the input text (for example, translation). -/
  action : String → Lean.Elab.TermElabM α
  /-- Format and render the final output. -/
  postProcess : (input : Option String) → (output : α) → String

open Lean Server Lsp RequestM in
/-- An abstraction for performing edits through code actions. -/
def performCodeAction {T : Type _} (iparams : Interface.Params T) : CodeActionProvider := fun params _snap => do
  let doc ← readDoc
  let text := doc.meta.text
  let source := text.source

  let edit : IO TextEdit := do
    -- the current position in the text document
    let pos : String.Pos := text.lspPosToUtf8Pos params.range.end
    let some ⟨start, stop⟩ := iparams.nearestOccurrence? source pos | throw $ IO.userError "No input found."
    return {
    range := ⟨text.leanPosToLspPos <| text.toPosition start, text.leanPosToLspPos <| text.toPosition stop⟩
    newText := ← do
      -- the smallest node of the `InfoTree` containing the current position
      let info? := _snap.infoTree.findInfo? (·.contains pos)
      -- the `Syntax` corresponding to the `Info` node
      let stx? := (·.stx) <$> info?

      -- the portion of the document to be processed
      let rawText? : Option String :=
        -- this is safe because the `range` is available
        (none /- TODO: First attempt to parse using `Syntax` -/)  <|>
        ( /- Parse as a string -/
          some <| source.extract start stop)
      let input? := rawText? >>= iparams.extractText?

      let output := _snap.runTermElabM doc.meta <| do
        let some input := input? | failure
        iparams.action input
      let output ← EIO.toIO (fun _ => IO.userError "Action failed.") output
      return iparams.postProcess input? output
    }

  let ca : CodeAction := { title := iparams.title, kind? := "quickfix" }
  return #[{ eager := ca, lazy? := some $ return {ca with edit? := WorkspaceEdit.ofTextEdit params.textDocument.uri $ ← edit} }]


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
