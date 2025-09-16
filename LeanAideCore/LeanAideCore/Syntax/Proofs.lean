import Lean
import LeanAideCore.Kernel
import LeanAideCore.Discussion
import LeanAideCore.KernelGenerators
import LeanAideCore.Syntax.Basic

open Lean Meta Elab Term PrettyPrinter Tactic Command Parser

namespace LeanAide

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
    let nameStx := Lean.mkIdent <| d.name ++ "proof_doc".toName
    let docs := mkNode ``Lean.Parser.Command.docComment #[mkAtom "/--", mkAtom ( d.content ++ " -/")]

    `(command| $docs:docComment #proof_document $nameStx)

/-- world -/
#proof_document hello.doc

#eval hello.doc

instance structuredDocumentCommand : DefinitionCommand StructuredProof where
  cmd s := do
    let nameStx := Lean.mkIdent (s.name  ++ "struct_proof".toName)
    let jsStx ← getJsonSyntax s.json
    let typeId := Lean.mkIdent ``StructuredProof
    `(command| def $nameStx : $typeId := ⟨ $(quote s.name),  json% $jsStx ⟩  )

#consider ({name := `hello, json := json% {a : {b : 1}} }: StructuredProof)

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
    let nameStx := Lean.mkIdent (c.name ++ "conj".toName)
    let docs := mkNode ``Lean.Parser.Command.docComment #[mkAtom "/--", mkAtom ( c.text ++ " -/")]
    let typeStx ← delab c.type
    `(command| $docs:docComment #conjecture $nameStx : $typeStx)

instance : DefinitionCommand DefinitionCode where
  cmd d := return d.statement

instance : DefinitionCommand TheoremText where
  cmd t := do
    mkQuoteCmd t.text t.name?

instance : ReplaceCommand ProofCode where
  replace stx dc := do
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

end LeanAide
