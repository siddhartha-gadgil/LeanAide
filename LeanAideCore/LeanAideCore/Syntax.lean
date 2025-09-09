import Lake.Toml.ParserUtil
import Lean
import LeanAideCore.Kernel

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
@[command_elab thmCommand] def thmCommandImpl : CommandElab :=
  fun stx => Command.liftTermElabM do
  match stx with
  | `(command| #theorem $s:str) =>
    let s := s.getString
    go s stx none
  | `(command| #theorem $name:ident $s:str) =>
    let s := s.getString
    let name := name.getId
    go s stx (some name)
  | `(command| #theorem : $s:str) =>
    let s := s.getString
    go s stx none
  | `(command| #theorem $name:ident : $s:str) =>
    let s := s.getString
    let name := name.getId
    go s stx (some name)
  | _ => throwUnsupportedSyntax
  where go (s: String) (stx: Syntax) (name? : Option Name) : TermElabM Unit := do
    if s.endsWith "." then
      -- let translator : Translator ← Translator.defaultDefM
      -- let (js, _) ←
      --   translator.getLeanCodeJson  s |>.run' {}
      let e? ← KernelM.translateThmFallback s
      -- let e? ←
      --   jsonToExprFallback js (← greedy) !(← chatParams).stopColEq |>.run' {}
      let name ← match name? with
      | some name => pure name
      | none =>
          KernelM.theoremName s
      let name := mkIdent name
      match e? with
      | .ok e =>
        -- logTimed "obtained expression"
        let stx' ← delab e
        -- logTimed "obtained syntax"
        let cmd ← `(command| theorem $name : $stx' := by sorry)
        TryThis.addSuggestion stx cmd
        -- logTimed "added suggestion"
        let docs := mkNode ``Lean.Parser.Command.docComment #[mkAtom "/--", mkAtom (s ++ " -/")]
        let cmd ←
          `(command| $docs:docComment theorem $name:ident : $stx' := by sorry)
        TryThis.addSuggestion stx cmd (header := "Try This (with docstring): ")
        return
      | .error e =>
        logWarning "No valid lean code found, suggesting best option"
        let cmd := s!"theorem {name} : {e} := by sorry"
        TryThis.addSuggestion stx cmd
        let cmd := s!"/-- {s} -/\ntheorem {name} : {e} := by sorry"
        TryThis.addSuggestion stx cmd (header := "Try This (with docstring): ")

    else
      logWarning "To translate a theorem, end the string with a `.`."

@[command_elab defCommand] def defCommandImpl : CommandElab :=
  fun stx => Command.liftTermElabM do
  match stx with
  | `(command| #def $s:str) =>
    let s := s.getString
    go s stx
  | _ => throwUnsupportedSyntax
  where go (s: String) (stx: Syntax) : TermElabM Unit := do
    if s.endsWith "." then
      -- let translator : Translator ← Translator.defaultDefM
      let cmd? ←
        KernelM.translateDefFallback  s |>.run' {}
      match cmd? with
      | .ok cmd =>
        TryThis.addSuggestion stx cmd
        -- logTimed "added suggestion"
        let docs := mkNode ``Lean.Parser.Command.docComment #[mkAtom "/--", mkAtom (s ++ " -/")]
        match cmd with
        | `(command| def $name $args* : $stx' := $val) =>
          let cmd ←
            `(command| $docs:docComment def $name $args* : $stx' := $val)
          TryThis.addSuggestion stx cmd (header := "Try This (with docstring): ")
        | `(command| noncomputable def $name:ident $args* : $stx' := $val) =>
          let cmd ←
            `(command| $docs:docComment noncomputable def $name:ident $args* : $stx' := $val)
          TryThis.addSuggestion stx cmd (header := "Try This (with docstring): ")
        | _ => pure ()
        return
      | .error e =>
        -- let e ← CmdElabError.fallback es
        logWarning "No valid lean code found, suggesting best option"
        TryThis.addSuggestion stx e
        let cmd := s!"/-- {s} -/\n{e}"
        TryThis.addSuggestion stx cmd (header := "Try This (with docstring): ")
    else
      logWarning "To translate a definition, end the string with a `.`."


@[command_elab askCommand] def askCommandImpl : CommandElab :=
  fun stx => Command.liftTermElabM do
  match stx with
  | `(command| #ask $s:str) =>
    let s := s.getString
    go s none stx
  | `(command| #ask $n:num $s:str) =>
    let s := s.getString
    let n := n.getNat
    go s n stx
  | _ => throwUnsupportedSyntax
  where go (s: String) (n?: Option Nat)(stx: Syntax) : TermElabM Unit := do
    if s.endsWith "." || s.endsWith "?" then
      -- let server ← chatServer
      let n := n?.getD 3
      let responses ← KernelM.mathQuery s n
      for r in responses do
        logInfo r
      let stxs ← responses.mapM fun res =>
        let qr := s!"**Query**: {s}\n\n **Response:** {res}"
        let stx := mkNode ``textCmd #[mkAtom "#text", mkAtom qr, mkAtom "∎"]
        ppCategory ``textCmd stx
      let stxs : List TryThis.Suggestion :=
        stxs.map fun stx => stx.pretty
      TryThis.addSuggestions stx <| stxs.toArray
    else
      logWarning "To make a query, end the string with a `.` or `?`."

open Command in
@[command_elab addDocs] def elabAddDocsImpl : CommandElab := fun stx =>
  match stx with
  | `(#doc theorem $id:ident $ty:declSig $val:declVal) =>
    Command.liftTermElabM do
    let name := id.getId
    let stx' ← `(command| theorem $id:ident $ty $val)
    -- let fmt ← PrettyPrinter.ppCommand stx'
    -- let type : Expr ← elabFrontThmExprM fmt.pretty name true
    -- let some (desc, _) ←
    --   Translator.getTypeDescriptionM type {} | throwError "No description found for type {type}"
    let desc ← KernelM.theoremDoc name stx'
    let docs := mkNode ``Lean.Parser.Command.docComment #[mkAtom "/--", mkAtom (desc ++ " -/")]
    let stx' ← `(command| $docs:docComment theorem $id:ident $ty $val)
    TryThis.addSuggestion stx stx'
  | `(#doc def $id:ident $args* : $ty:term := $val:term) =>
    Command.liftTermElabM do
    let name := id.getId
    let stx' ← `(command| def $id:ident $args* : $ty:term := $val:term)
    -- let fmt ← PrettyPrinter.ppCommand stx'
    -- let (type, value) ← elabFrontDefTypeValExprM fmt.pretty name true
    -- let some (desc, _) ←
    --   Translator.getDefDescriptionM type value name {} | throwError "No description found for type {type}"
    let desc ← KernelM.defDoc name stx'
    let docs := mkNode ``Lean.Parser.Command.docComment #[mkAtom "/--", mkAtom (desc ++ " -/")]
    let stx' ← `(command| $docs:docComment def $id:ident $args* : $ty:term := $val:term)
    TryThis.addSuggestion stx stx'
  | `(#doc noncomputable def $id:ident $args* : $ty:term := $val:term) =>
    Command.liftTermElabM do
    let name := id.getId
    let stx' ← `(command| noncomputable def $id:ident $args* : $ty:term := $val:term)
    -- let fmt ← PrettyPrinter.ppCommand stx'
    -- let (type, value) ← elabFrontDefTypeValExprM fmt.pretty name true
    -- let some (desc, _) ←
    --   Translator.getDefDescriptionM type value name {} | throwError "No description found for type {type}"
    let desc ← KernelM.defDoc name stx'
    let docs := mkNode ``Lean.Parser.Command.docComment #[mkAtom "/--", mkAtom (desc ++ " -/")]
    let stx' ← `(command| $docs:docComment noncomputable def $id:ident $args* : $ty:term := $val:term)
    TryThis.addSuggestion stx stx'
  | _ => throwError "unexpected syntax"



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
