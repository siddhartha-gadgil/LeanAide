import LeanCodePrompts.Translate

open Lean Meta Elab Term Tactic  Parser Command

namespace LeanAide

def addDocLint : Linter where
  run stx :=
    Command.liftTermElabM do
      match stx with
      | `(command| theorem $id:ident $ty:declSig $val:declVal) =>

        let name := id.getId
        let info ← getConstInfo name
        let type := info.type
        logInfo m!"Type : {type}"
        let some (desc, _) ← Translator.getTypeDescriptionM type {} | throwError "No description found for type {type}"
        logInfo m!"{desc}"
        -- let docs := mkNode ``Lean.Parser.Command.docComment #[mkAtom "/--", mkAtom (desc ++ " -/")]
        -- let stx' ← `(command| $docs:docComment theorem $id:ident $ty $val)
        -- TryThis.addSuggestion stx stx'
      | _ =>
        -- logInfo m!"Not a theorem : {stx}"
        return

initialize addLinter addDocLint


end LeanAide
