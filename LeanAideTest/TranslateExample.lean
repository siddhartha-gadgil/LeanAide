import Mathlib
import LeanAideCore.Translate

open LeanAide Translate Translator
/-!
# Translation demo

-/

set_option lean_aide.translate.model "gpt-5.4" -- remove to use "gpt-3.5-turbo"
-- set_option trace.Translate.info true

-- Testing local server at the given url
-- #eval translateViewM "Every prime number is either `2` or odd" (url? := some "http://10.134.13.103:8000") (model := "morph-labs/morph-prover-v0-7b")

#eval translateViewM "There are infinitely many odd numbers"

#eval translateViewM "If a vector space has dimension `2` then it is finite dimensional."

#eval translateDefViewM? (translator := {params := {n := 20}})  "A complex square matrix A is said to be diagonalizable if there exists an invertible matrix P such that P^(-1)AP is a diagonal matrix."

#eval translateDefViewM? (translator := {params := {n := 20}})  "A natural number is said to be square-free if it is not divisible by the square of a prime number."

#eval translateDefViewM? (translator := {params := {n := 20}})  "A natural number is said to be cube-free if it is not divisible by the cube of a prime number."

#eval translateDefViewM? (translator := {params := {n := 20}})  "A group is said to be crazy if every normal subgroup is cyclic."

#eval translateDefViewM? (translator := {params := {n := 20}})  "A group is said to be sane if every proper normal subgroup is cyclic."


/--
info: Matrix.IsDiag.{u_1, u_4} {α : Type u_1} {n : Type u_4} [Zero α] (A : Matrix n n α) : Prop
-/
#guard_msgs in
#check Matrix.IsDiag

def Matrix.isDiagonalizable {n : Type u} {α : Type v} [Fintype n] [DecidableEq n] [CommRing α] [StarRing α]
    (A : Matrix n n α) : Prop :=
      ∃ (P : Matrix n n α), P.det ≠ 0 ∧ ∃ (D : Matrix n n α), D.IsDiag ∧ P⁻¹ * A * P = D

-- #eval LeanAide.Meta.getDescription ``Matrix.IsDiag

example : ∃ x y : Nat, x = y := by
  apply Exists.intro 0
  apply Exists.intro 0
  rfl

def Matrix.IsDiagonalizable {n : Type u} [Fintype n] {𝕜 : Type v} [Field 𝕜] [DecidableEq n] (A : Matrix n n 𝕜) :=
  ∃ (P : Matrix n n 𝕜) (_ : Invertible P), IsDiag (P⁻¹ * A * P)
