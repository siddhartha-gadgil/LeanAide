import Mathlib.Data.Nat.Basic

/-
A collection of mathematics contest problems along with their formalised statements.
The `binport` files can be used for using concepts that have been formalised in `mathlib`.
-/

section MiklosSchweitzerProblems

-- 2020 Miklós Schweitzer Memorial Competition in Mathematics, Question 1

/-
We say that two sequences x, y : ℕ → ℕ are completely different if x(n) ≠ y(n) holds for all
n ∈ ℕ. Let F be a function assigning a natural number to every sequence of natural numbers such
that F (x) ≠ F (y) for any pair of completely different sequences x, y, and for constant sequences we
have F ((k, k, . . .)) = k. Prove that there exists n ∈ ℕ such that F (x) = x(n) for all sequences x.
-/

section Q1

abbrev Sequence := ℕ → ℕ

def completelyDifferent (x y : Sequence) := ∀ n : ℕ, x n ≠ y n

def constantSeq (k : ℕ) : Sequence := λ _ => k

variable (F : Sequence → ℕ)
variable (completelyDifferentDistinguish : ∀ x y : Sequence, completelyDifferent x y → F x ≠ F y)
variable (constantMatch : ∀ k : ℕ, F (constantSeq k) = k)

theorem sequence_val_by_eval : ∃ n : ℕ, ∀ x : Sequence, F x = x n := sorry

end Q1

end MiklosSchweitzerProblems
