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
  cmd d name? := do
    let name := match name? with
      | some n => n
      | none => d.name
    let nameStx := Lean.mkIdent name
    let docs := mkNode ``Lean.Parser.Command.docComment #[mkAtom "/--", mkAtom ( d.content ++ " -/")]

    `(command| $docs:docComment #document $nameStx)

#consider ({name := `hello, content := "world" }: Document)

#check Name.components

instance structuredDocumentCommand : DefinitionCommand StructuredDocument where
  cmd s name? := do
    let name := match name? with
      | some n => n
      | none => s.name
    let nameStx := Lean.mkIdent name
    let jsStx ← getJsonSyntax s.json
    let typeId := Lean.mkIdent ``StructuredDocument
    `(command| def $nameStx : $typeId := ⟨ $(quote s.name),  json% $jsStx ⟩  )

#consider ({name := `hello, json := json% {a : {b : 1}} }: StructuredDocument)

end LeanAide
