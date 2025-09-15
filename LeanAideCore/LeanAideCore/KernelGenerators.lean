import LeanAideCore.Discussion
import LeanAideCore.Kernel

namespace LeanAide

open Discussion KernelM Lean

variable [kernel : Kernel]

instance : Continuation Query Response where
  continueM d := do
    let (history, _) ←  d.historyM
    let res ← mathQuery d.last.message history 1
    return d.append {message := res.head!}

instance : GenerateM TheoremText TheoremCode where
  generateM t := do
    let (name, expr, cmd) ←
      translateThmDetailed t.text t.name?
    return { text:= t.text, name := name, type := expr,  statement := cmd }

instance : GenerateM DefinitionText DefinitionCode where
  generateM d := do
    let .ok (cmd : Syntax.Command) ← KernelM.translateDef d.text | throwError "Translation failed"
     return { text := d.text, statement := cmd }

instance : GenerateM TheoremCode Document where
  generateM t := do
    let doc ← proveForFormalization t.text t.type t.statement
    return { name := t.name, content := doc }

instance : GenerateM Document StructuredDocument where
  generateM d := do
    let sdoc ← jsonStructured d.content
    return { name := d.name, json := sdoc }

instance : GenerateM StructuredDocument DocumentCode where
  generateM s := do
    let cmd ← codeFromJson s.json
    return { name := s.name, code := cmd }

end LeanAide
