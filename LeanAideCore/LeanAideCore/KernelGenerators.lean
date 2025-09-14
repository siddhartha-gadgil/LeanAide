import LeanAideCore.Discussion
import LeanAideCore.Kernel

namespace LeanAide

open Discussion KernelM

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
