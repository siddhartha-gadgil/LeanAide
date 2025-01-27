import LeanCodePrompts.Translate
import Lake.Toml.ParserUtil

open Lean Meta Elab Term PrettyPrinter Tactic Command Parser

namespace LeanAide.Meta

syntax (name := thmCommand) "#theorem" (ident)? (":")? str : command
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
      let translator : Translator := {server := ← chatServer, pb := PromptExampleBuilder.embedBuilder (← promptSize) (← conciseDescSize) (← descSize), params := ← chatParams}
      let (js, _) ←
        translator.getLeanCodeJson  s |>.run' {}
      let name ← match name? with
      | some name => pure name
      | none =>
          translator.server.theoremName s
      let name := mkIdent name
      let e? ←
        jsonToExprFallback js (← greedy) !(← chatParams).stopColEq |>.run' {}
      match e? with
      | .ok e =>
        logTimed "obtained expression"
        let stx' ← delab e
        logTimed "obtained syntax"
        let cmd ← `(command| theorem $name : $stx' := by sorry)
        TryThis.addSuggestion stx cmd
        logTimed "added suggestion"
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

syntax (name := defCommand) "#def"  str : command
@[command_elab defCommand] def defCommandImpl : CommandElab :=
  fun stx => Command.liftTermElabM do
  match stx with
  | `(command| #def $s:str) =>
    let s := s.getString
    go s stx
  | _ => throwUnsupportedSyntax
  where go (s: String) (stx: Syntax) : TermElabM Unit := do
    if s.endsWith "." then
      let translator : Translator := {server := ← chatServer, pb := PromptExampleBuilder.embedBuilder (← promptSize) (← conciseDescSize) 0, params := ← chatParams, toChat := .doc}
      let cmd? ←
        translator.translateDefCmdM?  s |>.run' {}
      match cmd? with
      | .ok cmd =>
        TryThis.addSuggestion stx cmd
        logTimed "added suggestion"
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
      | .error es =>
        let e ← CmdElabError.fallback es
        logWarning "No valid lean code found, suggesting best option"
        TryThis.addSuggestion stx e
        let cmd := s!"/-- {s} -/\n{e}"
        TryThis.addSuggestion stx cmd (header := "Try This (with docstring): ")
    else
      logWarning "To translate a definition, end the string with a `.`."


/-!
# Proof Syntax
-/
open Lake.Toml
def proofFn : ParserFn := takeWhile1Fn fun c => c != '∎'

def proofBodyInit : Parser :=
  { fn := rawFn proofFn}

def proofBody : Parser := andthen proofBodyInit "∎"

@[combinator_parenthesizer proofBodyInit] def proofBodyInit.parenthesizer := PrettyPrinter.Parenthesizer.visitToken
@[combinator_formatter proofBodyInit] def proofBodyInit.formatter := PrettyPrinter.Formatter.visitAtom Name.anonymous

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
syntax (name:= textProof) withPosition("#proof" ppLine (str <|> proofBody)) : tactic

open Tactic
@[tactic textProof] def textProofImpl : Tactic :=
  fun _ => withMainContext do
  evalTactic (← `(tactic|sorry))

-- example : True := by
--   #proof "trivial"

open Tactic Translator
elab "what" : tactic => withMainContext do
  let goal ← getMainGoal
  let type ← relLCtx goal
  logInfo m!"goal : {type}"
  -- let defs ← defsInExpr type
  -- logInfo m!"defs : {defs}"
  let some (transl, _, _) ← getTypeDescriptionM type {} | throwError "No description from LLM"
  logInfo transl

syntax (name:= whyTac) "why" : tactic
@[tactic whyTac] def whyTacImpl : Tactic := fun stx => withMainContext do
  let goal ← getMainGoal
  let type ← relLCtx goal
  logInfo m!"goal : {type}"
  let some (transl, _, _) ← getTypeProofM type {} |
            throwError "No description from LLM"
  logInfo m!"Theorem and proof: {transl}"
  -- let pfStx := Syntax.mkStrLit proof[0]!
  -- let proofTac ← `(tactic| #proof $pfStx)
  let proofTac : Syntax.Tactic := ⟨mkProofStx transl⟩
  TryThis.addSuggestion stx proofTac

syntax (name:= addDocs) "#doc" command : command

open Command in
@[command_elab addDocs] def elabAddDocsImpl : CommandElab := fun stx =>
  match stx with
  | `(#doc theorem $id:ident $ty:declSig $val:declVal) =>
    Command.liftTermElabM do
    let name := id.getId
    let stx' ← `(command| theorem $id:ident $ty $val)
    let fmt ← PrettyPrinter.ppCommand stx'
    let type : Expr ← elabFrontThmExprM fmt.pretty name true
    let some (desc, _) ←
      Translator.getTypeDescriptionM type {} | throwError "No description found for type {type}"
    let docs := mkNode ``Lean.Parser.Command.docComment #[mkAtom "/--", mkAtom (desc ++ " -/")]
    let stx' ← `(command| $docs:docComment theorem $id:ident $ty $val)
    TryThis.addSuggestion stx stx'
  | `(#doc def $id:ident $args* : $ty:term := $val:term) =>
    Command.liftTermElabM do
    let name := id.getId
    let stx' ← `(command| def $id:ident $args* : $ty:term := $val:term)
    let fmt ← PrettyPrinter.ppCommand stx'
    let (type, value) ← elabFrontDefTypeValExprM fmt.pretty name true
    let some (desc, _) ←
      Translator.getDefDescriptionM type value name {} | throwError "No description found for type {type}"
    let docs := mkNode ``Lean.Parser.Command.docComment #[mkAtom "/--", mkAtom (desc ++ " -/")]
    let stx' ← `(command| $docs:docComment def $id:ident $args* : $ty:term := $val:term)
    TryThis.addSuggestion stx stx'
  | `(#doc noncomputable def $id:ident $args* : $ty:term := $val:term) =>
    Command.liftTermElabM do
    let name := id.getId
    let stx' ← `(command| noncomputable def $id:ident $args* : $ty:term := $val:term)
    let fmt ← PrettyPrinter.ppCommand stx'
    let (type, value) ← elabFrontDefTypeValExprM fmt.pretty name true
    let some (desc, _) ←
      Translator.getDefDescriptionM type value name {} | throwError "No description found for type {type}"
    let docs := mkNode ``Lean.Parser.Command.docComment #[mkAtom "/--", mkAtom (desc ++ " -/")]
    let stx' ← `(command| $docs:docComment noncomputable def $id:ident $args* : $ty:term := $val:term)
    TryThis.addSuggestion stx stx'
  | _ => throwError "unexpected syntax"


syntax (name := askCommand) "#ask" (num)? str : command
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
      let server ← chatServer
      let n := n?.getD 3
      let responses ← server.mathCompletions s (n := n)
      for r in responses do
        logInfo r
      let stxs ← responses.mapM fun res =>
        let qr := s!"**Query**: {s}\n\n **Response:** {res}"
        let stx := mkNode ``textCmd #[mkAtom "#text", mkAtom qr, mkAtom "∎"]
        ppCategory ``textCmd stx
      let stxs : Array TryThis.Suggestion :=
        stxs.map fun stx => stx.pretty
      TryThis.addSuggestions stx <| stxs
    else
      logWarning "To make a query, end the string with a `.` or `?`."

#check TryThis.Suggestion
