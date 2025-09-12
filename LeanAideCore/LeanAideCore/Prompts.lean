import LeanAideCore.StatementSyntax
import LeanAideCore.Template
open Lean Meta

namespace LeanAide

namespace Prompts

def proveForFormalization (theorem_text: String) (theorem_type : Expr) : MetaM String := do
  let defs? ← defsBlob? theorem_type
  let defs := defs?.getD ""
  let theorem_type_str ← PrettyPrinter.ppExpr theorem_type
  fromTemplate "prove_theorem_for_formalization" [("theorem", theorem_text),  ("statement", theorem_type_str.pretty), ("definitions", defs), ("proof_guidelines", Resources.proofGuidelines)]

def jsonStructured (document: String) : MetaM String := do
  fromTemplate "json_structured" [("document", document), ("schema", Resources.paperStructure.pretty)]

end Prompts

end LeanAide
