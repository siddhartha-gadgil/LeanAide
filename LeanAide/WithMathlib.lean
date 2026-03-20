import Mathlib
import Lean

open Lean

namespace LeanAide

def minFac4M : CoreM Nat :=
  return Nat.minFac 4

end LeanAide
