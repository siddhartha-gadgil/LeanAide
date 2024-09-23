import Mathlib
import LeanCodePrompts.Translate

/-!
# Translation demo

-/

set_option lean_aide.translate.model "gpt-4o" -- remove to use "gpt-3.5-turbo"
set_option trace.Translate.info true

-- Testing local server at the given url
-- #eval translateViewM "Every prime number is either `2` or odd" (url? := some "http://10.134.13.103:8000") (model := "morph-labs/morph-prover-v0-7b")

#eval translateViewM "There are infinitely many odd numbers"

#eval translateViewM "If a vector space has dimension `2` then it is finite dimensional."

#eval translateDefViewM? (params := {n := 8}) (numConcise := 8) "A complex square matrix A is said to be diagonalizable if there exists an invertible matrix P such that P^(-1)AP is a diagonal matrix."

-- def Matrix.isDiagonalizable {n : Type u} {α : Type v} [Fintype n] [DecidableEq n] [CommRing α] [StarRing α]
--     (A : Matrix n n α) : Prop :=
--       ∃ (P : Matrix n n α), P.det ≠ 0 ∧ ∃ (D : Matrix n n α), D.diagonal ∧ P⁻¹ * A * P = D
#check Matrix.IsDiag

def Matrix.isDiagonalizable {n : Type u} {α : Type v} [Fintype n] [DecidableEq n] [CommRing α] [StarRing α]
    (A : Matrix n n α) : Prop :=
      ∃ (P : Matrix n n α), P.det ≠ 0 ∧ ∃ (D : Matrix n n α), D.IsDiag ∧ P⁻¹ * A * P = D

#eval LeanAide.Meta.getDescription ``Matrix.IsDiag
