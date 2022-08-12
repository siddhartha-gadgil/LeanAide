/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.Algebra.Algebra.Basic
import Mathbin.Algebra.Order.Smul

/-!
# Ordered algebras

An ordered algebra is an ordered semiring, which is an algebra over an ordered commutative semiring,
for which scalar multiplication is "compatible" with the two orders.

The prototypical example is 2x2 matrices over the reals or complexes (or indeed any C^* algebra)
where the ordering the one determined by the positive cone of positive operators,
i.e. `A ≤ B` iff `B - A = star R * R` for some `R`.
(We don't yet have this example in mathlib.)

## Implementation

Because the axioms for an ordered algebra are exactly the same as those for the underlying
module being ordered, we don't actually introduce a new class, but just use the `ordered_smul`
mixin.

## Tags

ordered algebra
-/


section OrderedAlgebra

variable {R A : Type _} {a b : A} {r : R}

variable [OrderedCommRing R] [OrderedRing A] [Algebra R A] [OrderedSmul R A]

theorem algebra_map_monotone : Monotone (algebraMap R A) := fun a b h => by
  rw [Algebra.algebra_map_eq_smul_one, Algebra.algebra_map_eq_smul_one, ← sub_nonneg, ← sub_smul]
  trans (b - a) • (0 : A)
  · simp
    
  · exact smul_le_smul_of_nonneg zero_le_one (sub_nonneg.mpr h)
    

end OrderedAlgebra

section Instances

variable {R : Type _} [LinearOrderedCommRing R]

instance LinearOrderedCommRing.to_ordered_smul : OrderedSmul R R where
  smul_lt_smul_of_pos := OrderedSemiring.mul_lt_mul_of_pos_left
  lt_of_smul_lt_smul_of_pos := fun a b c w₁ w₂ => (mul_lt_mul_left w₂).mp w₁

end Instances

