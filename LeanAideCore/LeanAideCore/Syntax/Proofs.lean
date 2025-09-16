import Lean
import LeanAideCore.Kernel
import LeanAideCore.Discussion
import LeanAideCore.KernelGenerators
import LeanAideCore.Syntax.Basic

open Lean Meta Elab Term PrettyPrinter Tactic Command Parser

namespace LeanAide

macro doc:docComment "#document" ppSpace n:ident : command =>
  let text := doc.raw.reprint.get!
  let text := text.drop 4 |>.dropRight 4
  let textStx := Syntax.mkStrLit text
  let name := n.getId ++ "doc".toName
  let nameStx := mkIdent name
  `(command| def $nameStx : Document := { name := $(quote n.getId), content := $(textStx) } )

instance documentCommand : DefinitionCommand Document where
  cmd d  := do
    let nameStx := Lean.mkIdent d.name
    let docs := mkNode ``Lean.Parser.Command.docComment #[mkAtom "/--", mkAtom ( d.content ++ " -/")]

    `(command| $docs:docComment #document $nameStx)

#consider ({name := `hello, content := "world" }: Document)

#check Name.components

instance structuredDocumentCommand : DefinitionCommand StructuredDocument where
  cmd s := do
    let nameStx := Lean.mkIdent s.name
    let jsStx ← getJsonSyntax s.json
    let typeId := Lean.mkIdent ``StructuredDocument
    `(command| def $nameStx : $typeId := ⟨ $(quote s.name),  json% $jsStx ⟩  )

#consider ({name := `hello, json := json% {a : {b : 1}} }: StructuredDocument)

macro doc:docComment "#conjecture" ppSpace n:ident ppSpace ":" ppSpace t:term : command => do
  let name := n.getId ++ "conj".toName
  let propId ← `(Prop)
  let nameStx := mkIdent name
  `(command| $doc:docComment def $nameStx : $propId := $t )

/--
Just a test
-/
#conjecture easy : 2 + 2 = 4

#check easy.conj

#check Syntax.Level

#check mkSort

elab "#propview" : command =>
  Command.liftTermElabM do
  let t ← Term.elabTerm (← `(Prop)) none
  let s := mkSort Level.zero
  let ss ← delab s
  let pp ← PrettyPrinter.ppExpr t
  logInfo m!"{pp}, {t}"
  let pp ← PrettyPrinter.ppExpr s
  logInfo m!"Sort: {pp}, {repr ss}"

#propview

end LeanAide
