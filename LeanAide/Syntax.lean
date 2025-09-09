import LeanCodePrompts.Translate
import Lake.Toml.ParserUtil
import Lean
import LeanAideCore.Syntax
import LeanAideCore.Kernel
import LeanAide.Responses

open Lean Meta Elab Term PrettyPrinter Tactic Command Parser

namespace LeanAide.Meta



open Tactic Translator
elab "what" : tactic => withMainContext do
  let goal ← getMainGoal
  let type ← relLCtx goal
  logInfo m!"goal : {type}"
  -- let defs ← defsInExpr type
  -- logInfo m!"defs : {defs}"
  let some (transl, _, _) ← getTypeDescriptionM type {} | throwError "No description from LLM"
  logInfo transl


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



-- #check TryThis.Suggestion

open Lean.Parser.Command


end LeanAide.Meta
