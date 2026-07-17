import Lean
import LeanAideCore.Kernel
import LeanAideCore.Syntax.Basic

open Lean Meta Elab Term PrettyPrinter Tactic Command Parser

namespace LeanAide

declare_syntax_cat discussion
syntax "following" term : discussion
syntax "initiate" : discussion

syntax (name := llmQueryCommand) "#llm_query" (ppSpace num)? ppSpace str (ppSpace discussion)? : command

end LeanAide

namespace LeanAide.Meta


declare_syntax_cat thmAction
syntax "translate_theorem" : thmAction

syntax (name := thmCommand) "#theorem" (ppSpace ident)? (ppSpace ":")? ppSpace str (ppSpace ">>" ppSpace thmAction)?: command

syntax (name := defCommand) "#def" ppSpace str (ppSpace ">>" ppSpace "translate_definition")? : command

syntax (name:= addDocs) "#doc" command : command




open Lean.Parser.Command

-- @[command_parser]
-- def proofComment := leading_parser
--   ppDedent <| "/proof" >> ppSpace >> commentBody >> ppLine

-- def getProofStringText [Monad m] [MonadError m] (stx : TSyntax ``proofComment) : m String :=
--   match stx.raw[1] with
--   | Lean.Syntax.atom _ val => return val.raw.pos.extract 0 (val.endPos - ⟨2⟩)
--   | _                 => throwErrorAt stx "unexpected doc string{indentD stx.raw[1]}"

-- @[command_elab proofComment] def elabProofComment : CommandElab :=
--   fun stx => Command.liftTermElabM do
--   match stx with
--   | `(command|$doc:proofComment) =>
--     let view ← getProofStringText doc
--     logInfo m!"Proof comment: {view}"
--   | _ => throwUnsupportedSyntax

-- /proof Hello there -/
@[command_elab thmCommand] def thmCommandImpl : CommandElab :=
  fun stx => Command.liftTermElabM do
  match stx with
  | `(command| #theorem $s:str) =>
    let stx' ← `(command| #theorem : $s:str >> translate_theorem)
    TryThis.addSuggestion stx stx' (header :="Choose action on theorem text:\n")
  | `(command| #theorem $name:ident $s:str) =>
    let stx' ← `(command| #theorem $name:ident : $s:str >> translate_theorem)
    TryThis.addSuggestion stx stx' (header :="Choose action on theorem text:\n")
  | `(command| #theorem : $s:str) =>
    let stx' ← `(command| #theorem : $s:str >> translate_theorem)
    TryThis.addSuggestion stx stx' (header :="Choose action on theorem text:\n")
  | `(command| #theorem $name:ident : $s:str) =>
    let stx' ← `(command| #theorem $name:ident : $s:str >> translate_theorem)
    TryThis.addSuggestion stx stx' (header :="Choose action on theorem text:\n")
  -- Now handle the actual translation
  | `(command| #theorem $s:str >> translate_theorem) =>
    let s := s.getString
    go s stx none
  | `(command| #theorem $name:ident $s:str >> translate_theorem) =>
    let s := s.getString
    let name := name.getId
    go s stx (some name)
  | `(command| #theorem : $s:str >> translate_theorem) =>
    let s := s.getString
    go s stx none
  | `(command| #theorem $name:ident : $s:str >> translate_theorem) =>
    let s := s.getString
    let name := name.getId
    go s stx (some name)
  | _ => throwUnsupportedSyntax
  where go (s: String) (stx: Syntax) (name? : Option Name) : TermElabM Unit := do
    -- if s.endsWith "." then
      let e? ← KernelM.translateThmFallback s |>.run' {}
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
        -- TryThis.addSuggestion stx cmd
        -- logTimed "added suggestion"
        let docs := mkNode ``Lean.Parser.Command.docComment #[mkAtom "/--", mkAtom (s ++ " -/")]
        let cmd ←
          `(command| $docs:docComment theorem $name:ident : $stx' := by sorry)
        TryThis.addSuggestion stx cmd
        return
      | .error e =>
        logWarning "No valid lean code found, suggesting best option"
        let cmd := s!"theorem {name} : {e} := by sorry"
        -- TryThis.addSuggestion stx cmd
        let cmd := s!"/-- {s} -/\ntheorem {name} : {e} := by sorry"
        TryThis.addSuggestion stx cmd

    -- else
    --   logWarning "To translate a theorem, end the string with a `.`."

@[command_elab defCommand] def defCommandImpl : CommandElab :=
  fun stx => Command.liftTermElabM do
  match stx with
  | `(command| #def $s:str >> translate_definition) =>
    let s := s.getString
    go s stx
  | `(command| #def $s:str) =>
    let stx' ← `(command| #def $s:str >> translate_definition)
    TryThis.addSuggestion stx stx' (header :="Choose action on definition text:\n")
  | _ => throwUnsupportedSyntax
  where go (s: String) (stx: Syntax) : TermElabM Unit := do
    if s.endsWith "." then
      -- let translator : Translator ← Translator.defaultDefM
      let cmd? ←
        KernelM.translateDefFallback  s |>.run' {}
      match cmd? with
      | .ok cmd =>
        -- TryThis.addSuggestion stx cmd
        -- logTimed "added suggestion"
        let docs := mkNode ``Lean.Parser.Command.docComment #[mkAtom "/--", mkAtom (s ++ " -/")]
        match cmd with
        | `(command| def $name $args* : $stx' := $val) =>
          let cmd ←
            `(command| $docs:docComment def $name $args* : $stx' := $val)
          TryThis.addSuggestion stx cmd
        | `(command| noncomputable def $name:ident $args* : $stx' := $val) =>
          let cmd ←
            `(command| $docs:docComment noncomputable def $name:ident $args* : $stx' := $val)
          TryThis.addSuggestion stx cmd
        | _ => TryThis.addSuggestion stx cmd
        return
      | .error e =>
        -- let e ← CmdElabError.fallback es
        logWarning "No valid lean code found, suggesting best option"
        TryThis.addSuggestion stx e
        let cmd := s!"/-- {s} -/\n{e}"
        TryThis.addSuggestion stx cmd (header := "Try This (with docstring): ")
    else
      logWarning "To translate a definition, end the string with a `.`."

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
    let desc ← KernelM.theoremDoc name stx' |>.run' {}
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
    let desc ← KernelM.defDoc name stx' |>.run' {}
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
    let desc ← KernelM.defDoc name stx' |>.run' {}
    let docs := mkNode ``Lean.Parser.Command.docComment #[mkAtom "/--", mkAtom (desc ++ " -/")]
    let stx' ← `(command| $docs:docComment noncomputable def $id:ident $args* : $ty:term := $val:term)
    TryThis.addSuggestion stx stx'
  | _ => throwError "unexpected syntax"



end LeanAide.Meta

namespace LeanAide

open Meta

declare_syntax_cat theorem_head
syntax "theorem" : theorem_head
syntax "def" : theorem_head
syntax "lemma" : theorem_head
syntax "instance" : theorem_head
syntax "example" : theorem_head
syntax "noncomputable" "def": theorem_head

declare_syntax_cat theorem_statement
--syntax bracketedBinder* docComment (theorem_head)?  bracketedBinder*  ":" term : theorem_statement
syntax (theorem_head)? (ident)? bracketedBinder*  ":" term : theorem_statement
syntax (docComment) (theorem_head)? (ident)? bracketedBinder*  ":" term : theorem_statement
syntax (theorem_head)? (ident)? bracketedBinder*  ":" term  ":=" term: theorem_statement
syntax (docComment) (theorem_head)? (ident)? bracketedBinder*  ":" term  ":=" term: theorem_statement
syntax term : theorem_statement
syntax (docComment) term : theorem_statement

syntax (name := codegenCmd) "#codegen" ppSpace term : command

macro "#codegen" source:json : command =>
  `(command| #codegen json% $source)

open Command Elab Term Meta in
@[command_elab codegenCmd] def elabCodegenCmdImpl : CommandElab
| stx@`(command| #codegen $s:term) =>
  Command.liftTermElabM do
  withoutModifyingEnv do
    let sourceTerm ←  Term.elabTerm s (mkConst ``Json)
    let sourceJson ←  unsafe evalExpr Json (mkConst ``Json) sourceTerm
    let code ←
      KernelM.codeFromJson sourceJson |>.run' {}
    TryThis.addSuggestion stx code
| _ => throwUnsupportedSyntax

syntax (name := codegenToken) "codegen%" ppSpace term : term

macro "codegen%" source:json : term =>
  `(codegen% json% $source)

open Command Elab Term Meta in
@[term_elab codegenToken] def elabCodegenTokenImpl : TermElab
| stx@`(codegen% $s:term), _ =>
  withoutModifyingEnv do
    let sourceTerm ←  Term.elabTerm s (mkConst ``Json)
    let sourceJson ←  unsafe evalExpr Json (mkConst ``Json) sourceTerm
    let token ← getCodeJsonTokenM sourceJson
    let token := token.toNat
    let stx' := Syntax.mkNatLit token
    TryThis.addSuggestion stx stx'
    return toExpr token
| _, _ => throwUnsupportedSyntax


syntax (name := codegenAsyncCmd) "#codegen_async" ppSpace term : command

open Command Elab Term Meta in
@[command_elab codegenAsyncCmd] def elabCodegenAsyncCmdImpl : CommandElab
| stx@`(command| #codegen_async $s:term) =>
  Command.liftTermElabM do
  withoutModifyingEnv do
    let tokenTerm ←  Term.elabTerm s (mkConst ``Json)
    let token ←
      unsafe evalExpr Nat (mkConst ``Nat) tokenTerm
    match ← updateCodeByToken token.toUInt64 |>.run' {} with
    | .some code =>
      TryThis.addSuggestion stx code
    | none =>
      logInfo s!"No code found for token {token}, process still running at {← timestamp}"
| _ => throwUnsupportedSyntax

syntax (name := considerCmd) "#consider"  ppSpace term : command
@[command_elab considerCmd] def elabConsiderCmdImpl : CommandElab
| stx@`(command| #consider $s:term) =>
  Command.liftTermElabM do
  let x ← Term.elabTerm s none
  let e ← mkAppM ``definitionCommand #[x]
  let type ← mkAppM ``TermElabM #[mkConst ``Syntax.Command]
  Term.synthesizeSyntheticMVarsNoPostponing
  let cmdM ← unsafe evalExpr (TermElabM Syntax.Command) type e
  let cmd ← cmdM
  TryThis.addSuggestion stx cmd
| _ => throwUnsupportedSyntax

-- #consider "Hello there."



end LeanAide
