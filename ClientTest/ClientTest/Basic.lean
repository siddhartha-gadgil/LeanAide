import LeanAideCore
import Mathlib

open LeanAide

@[default_instance]
instance : Add ℤ := inferInstance
@[default_instance]
instance : Semiring ℤ := inferInstance

#leanaide_connect

#eval LeanAidePipe.response <| json% {"task": "echo"}

#eval KernelM.translateThm "There are infinitely many odd numbers."
