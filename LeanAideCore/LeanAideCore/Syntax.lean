import Lake.Toml.ParserUtil
import Lean

open Lean Meta Elab Term PrettyPrinter Tactic Command Parser

namespace LeanAide.Meta

syntax (name := thmCommand) "#theorem" (ident)? (":")? str : command
syntax (name := defCommand) "#def"  str : command
open Lake.Toml
def proofFn : ParserFn := takeWhile1Fn fun c => c != '∎'

def proofBodyInit : Parser :=
  { fn := rawFn proofFn}

def proofBody : Parser := andthen proofBodyInit "∎"

@[combinator_parenthesizer proofBodyInit] def proofBodyInit.parenthesizer := PrettyPrinter.Parenthesizer.visitToken
@[combinator_formatter proofBodyInit] def proofBodyInit.formatter := PrettyPrinter.Formatter.visitAtom Name.anonymous

/-!
# Proof Syntax
-/
syntax (name := proofCmd) withPosition("#proof" ppLine (colGt (str <|> proofBody) )) : command

def mkProofStx (s: String) : Syntax :=
  mkNode ``proofCmd #[mkAtom "#proof", mkAtom s, mkAtom "∎"]

@[command_elab proofCmd] def elabProofCmd : CommandElab :=
  fun stx => Command.liftTermElabM do
  match stx with
  | `(command| #proof $t:proofBodyInit ∎) =>
    let s := stx.getArgs[1]!.reprint.get!.trim
    logInfo m!"Syntax: {stx}"
    let stx' := mkProofStx "Some proof."
    logInfo m!"Extract: {s}"
    logInfo m!"Details: {repr stx}"
    logInfo m!"{stx'}"
  | _ => throwUnsupportedSyntax


syntax (name := textCmd) withPosition("#text" ppLine (colGt (str <|> proofBody) )) : command

syntax (name:= whyTac) "why" : tactic

syntax (name:= textProof) withPosition("#proof" ppLine (str <|> proofBody)) : tactic


syntax (name:= addDocs) "#doc" command : command

syntax (name := askCommand) "#ask" (num)? str : command





def mkTextStx (s: String) : Syntax :=
  mkNode ``textCmd #[mkAtom "#text", mkAtom s, mkAtom "∎"]

@[command_elab textCmd] def elabTextCmd : CommandElab :=
  fun stx => Command.liftTermElabM do
  match stx with
  | `(command| #text $t:proofBodyInit ∎) =>
    -- let s := stx.getArgs[1]!.reprint.get!.trim
    return
  | _ => throwUnsupportedSyntax

/-!
# From Descriptions
-/


open Tactic
@[tactic textProof] def textProofImpl : Tactic :=
  fun _ => withMainContext do
  evalTactic (← `(tactic|sorry))

-- example : True := by
--   #proof "trivial"

open Lean.Parser.Command

@[command_parser]
def proofComment := leading_parser
  ppDedent <| "/proof" >> ppSpace >> commentBody >> ppLine

def getProofStringText [Monad m] [MonadError m] (stx : TSyntax ``proofComment) : m String :=
  match stx.raw[1] with
  | Lean.Syntax.atom _ val => return val.extract 0 (val.endPos - ⟨2⟩)
  | _                 => throwErrorAt stx "unexpected doc string{indentD stx.raw[1]}"

@[command_elab proofComment] def elabProofComment : CommandElab :=
  fun stx => Command.liftTermElabM do
  match stx with
  | `(command|$doc:proofComment) =>
    let view ← getProofStringText doc
    logInfo m!"Proof comment: {view}"
  | _ => throwUnsupportedSyntax

-- /proof Hello there -/

end LeanAide.Meta

namespace LeanAide

declare_syntax_cat theorem_head
syntax "theorem" : theorem_head
syntax "def" : theorem_head
syntax "lemma" : theorem_head
syntax "instance" : theorem_head
syntax "example" : theorem_head

declare_syntax_cat theorem_statement
syntax bracketedBinder* docComment (theorem_head)?  bracketedBinder*  ":" term : theorem_statement
syntax (theorem_head)? (ident)? bracketedBinder*  ":" term : theorem_statement
syntax (theorem_head)? (ident)? bracketedBinder*  ":" term  ":=" term: theorem_statement
syntax term : theorem_statement


syntax (name := codegenCmd) "#codegen" ppSpace term : command


macro "#codegen" source:json : command =>
  `(command| #codegen json% $source)

macro doc:docComment "#text" ppSpace n:ident : command =>
  let text := doc.raw.reprint.get!
  let text := text.drop 4 |>.dropRight 4
  let textStx := Syntax.mkStrLit text
  `(command| def $n := $textStx)

def mkTextCmd (doc: String) (name: Name) : CoreM <| Syntax.Command := do
  let docs := mkNode ``Lean.Parser.Command.docComment #[mkAtom "/--", mkAtom (doc ++ " -/")]
  let ident := mkIdent name
  `(command| $docs:docComment #text $ident)

declare_syntax_cat filepath
syntax str : filepath
syntax filepath ppSpace "/" ppSpace str : filepath

partial def filePath : TSyntax `filepath → System.FilePath
  | `(filepath| $s:str) => s.getString
  | `(filepath| $fs:filepath / $s) => (filePath fs / s.getString)
  | _ => System.FilePath.mk ""


syntax (name:= loadFile) "#load_file" (ppSpace ident)? (ppSpace filepath)? : command
@[command_elab loadFile] def loadFileImpl : CommandElab := fun stx  =>
 Command.liftTermElabM  do
  match stx with
  | `(command| #load_file $id:ident $file) =>
    let filePath : System.FilePath := filePath file
    let content ← try
        IO.FS.readFile filePath
      catch _ =>
        if ← filePath.isDir then
          let files ← filePath.readDir
          let files := files.map (·.fileName)
          for f in files do
            let name := Syntax.mkStrLit f
            let newPath ← `(filepath| $file / $name)
            let newCommand ← `(command| #load_file $id $newPath)
            TryThis.addSuggestion stx newCommand
        else
          logWarning s!"Failed to read file: {filePath}"
        return
    let content := "\n" ++ content.trim ++ "\n"
    let name := id.getId
    let textCmd ← mkTextCmd content name
    TryThis.addSuggestion (header := "Load source:\n") stx textCmd
  | `(command| #load_file $file:filepath) =>
    let filePath : System.FilePath := filePath file
    let content ← try
        IO.FS.readFile filePath

      catch _ =>
        if ← filePath.isDir then
          let files ← filePath.readDir
          let files := files.map (·.fileName)
          for f in files do
            let name := Syntax.mkStrLit f
            let newPath ← `(filepath| $file / $name)
            let newCommand ← `(command| #load_file $newPath:filepath)
            TryThis.addSuggestion stx newCommand
        else
          logWarning s!"Failed to read file: {filePath}"
        return
    let content := "\n" ++ content.trim ++ "\n"
    let name := filePath.fileName.getD "source"
    let textCmd ← mkTextCmd content name.toName
    TryThis.addSuggestion (header := "Load source:\n") stx textCmd
  | `(command| #load_file $id:ident) =>
    let filePath : System.FilePath := "."
    let files ← filePath.readDir
    let files := files.map (·.fileName)
    for f in files do
      let name := Syntax.mkStrLit f
      let newPath ← `(filepath| $name:str)
      let newCommand ← `(command| #load_file $id $newPath:filepath)
      TryThis.addSuggestion stx newCommand
  | `(command| #load_file) =>
    let filePath : System.FilePath := "."
    let files ← filePath.readDir
    let files := files.map (·.fileName)
    for f in files do
      let name := Syntax.mkStrLit f
      let newPath ← `(filepath| $name:str)
      let newCommand ← `(command| #load_file $newPath:filepath)
      TryThis.addSuggestion stx newCommand
  | _ => throwUnsupportedSyntax

end LeanAide
