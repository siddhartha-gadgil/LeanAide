import Aesop
import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.Group.Basic

/-!
# `Aesop` demo

This file demonstrates some of the out-of-the-box
capabilities of the `Aesop` automation tool for `Lean4`.

The focus is on theorems that `Aesop` can directly prove
without any additional configuration.
-/

section PropositionalLogic

/-!
## Propositional logic using `Aesop`

`Aesop` can prove routine theorems in
propositional logic automatically.
-/

variable (P Q R : Prop)


example : P → P := by aesop

example : P → (Q → P) := by aesop

example : P ∧ Q → P ∨ Q := by aesop

example : P ∨ P ↔ P ∧ P := by aesop

example : (P → Q) → (¬Q → ¬P) := by aesop

example : (P ∨ Q)  ↔  (Q ∨ P) := by aesop

example : (P ∧ Q) → R  ↔  P → (Q → R) := by aesop

example : (P → (Q → R)) → ((P → R) → (P → R)) := by aesop

end PropositionalLogic


section TrivialLemmas

/-!

## Proving trivial lemmas with `Aesop`

`Aesop` uses Lean's simplifier internally, which
allows it to prove trivial lemmas by simplification.

-/

example {a b : ℕ} (h₁ : a = 5) (h₂ : b = 2 + 3) : a = b :=
  by aesop

example {a : ℕ} : a + 0 = 0 → a = 0 + 0 := by aesop

example {G : Type} [Group G] {g : G} : 1⁻¹ * 1 = g * 1 * g⁻¹ :=
  by aesop

example : [1, 2, 3] ≠ [] := by aesop

example {l : List α} {a : α} : a ∈ l → l ≠ [] := by aesop

end TrivialLemmas


/-
section TermConstruction

/-!
## Constructing terms of types

Just as `Aesop` can produce proofs of some propositions,
it can construct terms of some types.
-/

variable (A B C : Type _)

-- the identity function
example : A → A := by aesop

-- projection onto the first coordinate
example : A → B → A := by aesop

-- formally similar to the adjoint of a linear transformation
example : (A → B) → ((B → C) → (A → C)) := by aesop

-- formally similar to the differential map between tangent spaces of manifolds
example (f : A → B) : ((A → C) → C) → ((B → C) → C) := by aesop 

end TermConstruction
-/