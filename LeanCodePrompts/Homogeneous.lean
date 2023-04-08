import Lean
import Mathlib
/-!
An attempt to give priority to homogeneous operations in the elaborator and make some other changes that allow expressions without too many type annotations.

* 
-/

open Lean Meta Elab Term

attribute [-instance] Nat.instDivNat
-- example (n : ℕ) : ℚ := (4 *(n*(n-1)/2)^3-(n*(n-1)/2)^2)/3
example (n : ℕ) : ℚ := ((4 *((n*(n-1)/2 : ℚ)^3 : ℚ) - (((n*(n-1)/2 : ℚ)^2) : ℚ)) : ℚ)/3
