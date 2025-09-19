import Lean
import LeanAideCore.Kernel
import LeanAideCore.Discussion
import LeanAideCore.KernelGenerators
import LeanAideCore.Syntax.Basic

open Lean Meta Elab Term PrettyPrinter Tactic Command Parser

namespace LeanAide
open Meta

def pruneName (n : Name) : Name :=
  let cs := n.componentsRev
  let cs := cs.tail.reverse
  cs.foldl (fun acc c => if c == Name.anonymous then acc else acc.append c) Name.anonymous

macro doc:docComment "#proof_document" ppSpace n:ident : command =>
  let text := doc.raw.reprint.get!
  let text := text.drop 4 |>.dropRight 4
  let textStx := Syntax.mkStrLit text
  let name := n.getId
  let nameStx := mkIdent name
  let docName := pruneName name
  `(command| def $nameStx : ProofDocument := { name := $(quote docName), content := $(textStx) } )

instance documentCommand : DefinitionCommand ProofDocument where
  cmd d  := do
    let name := d.name ++ ".proof_doc".toName
    let nameStx := Lean.mkIdent (d.name ++ "proof_doc".toName)
    let docs := mkNode ``Lean.Parser.Command.docComment #[mkAtom "/--", mkAtom ( d.content ++ " -/")]

    return (← `(command| $docs:docComment #proof_document $nameStx), name)


instance structuredDocumentCommand : DefinitionCommand StructuredProof where
  cmd s := do
    let name := s.name ++ ".struct_proof".toName
    let nameStx := Lean.mkIdent name
    let jsStx ← getJsonSyntax s.json
    let typeId := Lean.mkIdent ``StructuredProof
    return (← `(command| def $nameStx : $typeId := ⟨ $(quote s.name),  json% $jsStx ⟩), name)

-- #consider ({name := `hello, json := json% {a : {b : 1}} }: StructuredProof)

macro doc:docComment "#conjecture" ppSpace n:ident ppSpace ":" ppSpace t:term : command => do
  let name := n.getId
  let nameStx := mkIdent name
  `(command| $doc:docComment def $nameStx : Prop := $t )

/--
Just a test
-/
#conjecture easy : 2 + 2 = 4

#check easy

instance : DefinitionCommand TheoremCode where
  cmd c := do
    let name := c.name ++ ".conj".toName
    let nameStx := Lean.mkIdent name
    let docs := mkNode ``Lean.Parser.Command.docComment #[mkAtom "/--", mkAtom ( c.text ++ " -/")]
    let typeStx ← delab c.type
    return (← `(command| $docs:docComment #conjecture $nameStx : $typeStx), name)

instance : DefinitionCommand DefinitionCode where
  cmd d := return (d.statement, d.name)

instance : DefinitionCommand TheoremText where
  cmd t := do
    let name := t.name? |>.getD ("theorem_" ++ toString (hash t.text)).toName
    return (← mkQuoteCmd t.text name, name)

instance : ReplaceCommand ProofCode where
  replace stx dc := do
    let codeText ← printCommands dc.code
    let text := s!"section {dc.name}\n\n{codeText}\n\nend {dc.name}"
    TryThis.addSuggestion stx text

instance : ReplaceCommand (Discussion ProofCode) where
  replace stx dc := do
    let dc := dc.last
    let codeText ← printCommands dc.code
    let text := s!"section {dc.name}\n\n{codeText}\n\nend {dc.name}"
    TryThis.addSuggestion stx text


syntax (name:= proofGenCmd) "#prove" ppSpace term (">>" ppSpace term)? : command

@[command_elab proofGenCmd] def elabProofGenCmd : CommandElab
  | stx@`(command| #prove $t:term >> $out:term) =>
    Command.liftTermElabM do
    let type ← elabType out
    let init ← Term.elabTerm t none
    let result ← mkAppM ``generateM #[type, init]
    let SideEffect' ← mkAppM ``TermElabM #[mkConst ``Unit]
    let SideEffect ← mkArrow (mkConst ``Syntax) SideEffect'
    let resultEffectExpr ← mkAppM ``replaceCommandM #[result]
    let resultEffect ← unsafe evalExpr (Syntax → (TermElabM Unit)) SideEffect resultEffectExpr
    resultEffect stx
  | stx@`(command| #prove $t:term ) => Command.liftTermElabM do
    let tc := mkIdent ``TheoremCode
    let pd := mkIdent ``ProofDocument
    let sp := mkIdent ``StructuredProof
    let pc := mkIdent ``ProofCode
    TryThis.addSuggestions stx #[(← `(command| #prove $t:term >> $tc)), (← `(command| #prove $t:term >> $pd)), (← `(command| #prove $t:term >> $sp)), (← `(command| #prove $t:term >> $pc))] (header := "Specify output type with >>")
  | _ => throwUnsupportedSyntax

@[command_elab askCommand] def askCommandImpl : CommandElab :=
  fun stx => Command.liftTermElabM do
  match stx with
  | `(command| #ask  $_:str) =>
    logWarning "Follow ask command with 'following <term>' or 'initiate' to continue/start a discussion."
  | `(command| #ask $_:num $_:str) =>
    logWarning "Follow ask command with 'following <term>' or 'initiate' to continue/start a discussion."
  | `(command| #ask $s:str following $p:term) =>
    let s := s.getString
    let _p ← Term.elabTerm p none
    go s none stx
  | `(command| #ask $n:num $s:str following $p:term) =>
    let s := s.getString
    let _p ← Term.elabTerm p none
    let n := n.getNat
    go s (some n) stx
  | `(command| #ask $s:str initiate) =>
    let s := s.getString
    go s none stx
  | `(command| #ask $n:num $s:str initiate) =>
    let s := s.getString
    let n := n.getNat
    go s (some n) stx
  | _ => throwUnsupportedSyntax
  where go (s: String) (n?: Option Nat)(stx: Syntax) : TermElabM Unit := do
      -- let server ← chatServer
      let n := n?.getD 3
      let responses ← KernelM.mathQuery s [] n
      for r in responses do
        logInfo r
      let stxs : List TryThis.Suggestion ← responses.mapM fun res => do
        -- let qr := s!"**Query**: {s}\n\n **Response:** {res}"
        let queryName := s!"query_{hash s}" |>.toName
        let resName := s!"response_{hash s}" |>.toName
        let stxQ ← mkQuoteCmd s queryName
        let stxR ←  mkQuoteCmd res resName
        printCommands <| ←  toCommandSeq #[stxQ, stxR]
      TryThis.addSuggestions stx <| stxs.toArray


end LeanAide
