/-
Copyright (c) 2021 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import Mathbin.Algebra.Order.Ring
import Mathbin.Algebra.Invertible

/-!
# Lemmas about `inv_of` in ordered (semi)rings.
-/


variable {α : Type _} [LinearOrderedSemiring α] {a : α}

@[simp]
theorem inv_of_pos [Invertible a] : 0 < ⅟ a ↔ 0 < a := by
  have : 0 < a * ⅟ a := by
    simp only [← mul_inv_of_self, ← zero_lt_one]
  exact ⟨fun h => pos_of_mul_pos_left this h.le, fun h => pos_of_mul_pos_right this h.le⟩

@[simp]
theorem inv_of_nonpos [Invertible a] : ⅟ a ≤ 0 ↔ a ≤ 0 := by
  simp only [not_ltₓ, ← inv_of_pos]

@[simp]
theorem inv_of_nonneg [Invertible a] : 0 ≤ ⅟ a ↔ 0 ≤ a := by
  have : 0 < a * ⅟ a := by
    simp only [← mul_inv_of_self, ← zero_lt_one]
  exact ⟨fun h => (pos_of_mul_pos_left this h).le, fun h => (pos_of_mul_pos_right this h).le⟩

@[simp]
theorem inv_of_lt_zero [Invertible a] : ⅟ a < 0 ↔ a < 0 := by
  simp only [not_leₓ, ← inv_of_nonneg]

@[simp]
theorem inv_of_le_one [Invertible a] (h : 1 ≤ a) : ⅟ a ≤ 1 :=
  have := @LinearOrderₓ.decidableLe α _
  mul_inv_of_self a ▸ Decidable.le_mul_of_one_le_left (inv_of_nonneg.2 <| zero_le_one.trans h) h

