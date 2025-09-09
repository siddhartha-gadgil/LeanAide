import LeanAideCore.Kernel
import LeanAide.Responses

namespace LeanAide

#synth Kernel

#eval KernelM.translateThm "There are infinitely many odd numbers."

def dfEg := KernelM.translateDef "A group is said to be sane if every proper normal subgroup is cyclic"

open Lean Meta Elab Term

def showDfEg : TermElabM Unit := do
  let df ← dfEg
  match df with
  | .ok decl => logInfo (← PrettyPrinter.ppCommand decl)
  | .error err => logError m!"Error: {repr err}"

#eval showDfEg


end LeanAide
