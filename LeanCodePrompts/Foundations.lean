import Mathlib.Init.Data.Nat.Basic
import Mathlib.Init.Logic

/-
Basic examples of Lean's dependent type theory, including
- Functions (`λ` notation, `fun` notation, `def` notation, etc)
- Sum and product types (and their `Prop` versions)
- Dependent sum and product types (and their `Prop` versions)
- `Unit` and `Empty` types (and their `Prop` versions, including a few examples of negation)
- Some basic proofs in the style of the introductory chapters of TPiL

The aim is to introduce most of the basic constructions in Lean along with their notational nuances.
-/

/-
Text: `m` is a natural number.
-/
def m : Nat := 1

/-
Text: `n` is a natural number equal to `0`.
-/

def n := (0 : ℕ)
