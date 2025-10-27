import LeanAideCore
import Mathlib

open LeanAide
universe u v w u_1 u_2 u_3 u₁ u₂ u₃
@[default_instance]
instance : Add ℤ := inferInstance
@[default_instance]
instance : Semiring ℤ := inferInstance

#leanaide_connect

#eval LeanAidePipe.response <| json% {"task": "echo"}

#eval KernelM.translateThm "There are infinitely many odd numbers."

def dfEg := KernelM.translateDef "A group is said to be sane if every proper normal subgroup is cyclic"

open Lean Meta Elab Term

def showDfEg : TermElabM Unit := do
  let df ← dfEg
  match df with
  | .ok decl => logInfo (← PrettyPrinter.ppCommand decl)
  | .error err => logError m!"Error: {repr err}"

#eval showDfEg



#theorem silly : "If a vector space has dimension `2`, then it is finite dimensional." >>
  translate_theorem

#theorem : "There are infinitely many odd numbers." >> translate_theorem

#llm_query "Prove that there are infinitely many even numbers."

#def "A group is said to be sane if every proper normal subgroup is cyclic."
