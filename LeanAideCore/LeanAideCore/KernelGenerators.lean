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

instance : GenerateM TheoremText TheoremCodeM where
  generateM t := do
    let (name, expr, cmd) ←
      translateThmDetailed t.text t.name?
    return { text:= t.text, name := name, type := expr,  statement := cmd }

instance : GenerateM String TheoremCodeM where
  generateM s := do
    let (name, expr, cmd) ←
      translateThmDetailed s none
    return { text:= s, name := name, type := expr,  statement := cmd }

instance : GenerateM DefinitionText DefinitionCodeM where
  generateM d := do
    let .ok (cmd : Syntax.Command) ← KernelM.translateDef d.text | throwError "Translation failed"
    let .some name := getCommandName cmd | throwError "Cannot extract name from definition"
    return { text := d.text, statement := cmd, name := name }

instance : GenerateM TheoremCodeM ProofDocument where
  generateM t := do
    let doc ← proveForFormalization t.text t.type t.statement
    return { name := t.name, content := doc }

instance : GenerateM ProofDocument StructuredProof where
  generateM d := do
    let sdoc ← jsonStructured d.content
    return { name := d.name, json := sdoc }

instance : GenerateM StructuredProof ProofCode where
  generateM s := do
    let cmd ← codeFromJson s.json
    return { name := s.name, code := cmd }

#synth GenerateM String ProofCode


end LeanAide
