/-
Copyright (c) 2014 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Yaël Dillies, Patrick Stevens
-/
import Mathbin.Algebra.Order.Field
import Mathbin.Data.Nat.Cast

/-!
# Cast of naturals into fields

This file concerns the canonical homomorphism `ℕ → F`, where `F` is a field.

## Main results

 * `nat.cast_div`: if `n` divides `m`, then `↑(m / n) = ↑m / ↑n`
 * `nat.cast_div_le`: in all cases, `↑(m / n) ≤ ↑m / ↑ n`
-/


namespace Nat

variable {α : Type _}

@[simp]
theorem cast_div [Field α] {m n : ℕ} (n_dvd : n ∣ m) (n_nonzero : (n : α) ≠ 0) : ((m / n : ℕ) : α) = m / n := by
  rcases n_dvd with ⟨k, rfl⟩
  have : n ≠ 0 := by
    rintro rfl
    simpa using n_nonzero
  rw [Nat.mul_div_cancel_leftₓ _ this.bot_lt, cast_mul, mul_div_cancel_left _ n_nonzero]

section LinearOrderedSemifield

variable [LinearOrderedSemifield α]

/-- Natural division is always less than division in the field. -/
theorem cast_div_le {m n : ℕ} : ((m / n : ℕ) : α) ≤ m / n := by
  cases n
  · rw [cast_zero, div_zero, Nat.div_zeroₓ, cast_zero]
    
  rwa [le_div_iff, ← Nat.cast_mulₓ]
  exact Nat.cast_le.2 (Nat.div_mul_le_selfₓ m n.succ)
  · exact Nat.cast_pos.2 n.succ_pos
    

theorem inv_pos_of_nat {n : ℕ} : 0 < ((n : α) + 1)⁻¹ :=
  inv_pos.2 <| add_pos_of_nonneg_of_pos n.cast_nonneg zero_lt_one

theorem one_div_pos_of_nat {n : ℕ} : 0 < 1 / ((n : α) + 1) := by
  rw [one_div]
  exact inv_pos_of_nat

theorem one_div_le_one_div {n m : ℕ} (h : n ≤ m) : 1 / ((m : α) + 1) ≤ 1 / ((n : α) + 1) := by
  refine' one_div_le_one_div_of_le _ _
  exact Nat.cast_add_one_pos _
  simpa

theorem one_div_lt_one_div {n m : ℕ} (h : n < m) : 1 / ((m : α) + 1) < 1 / ((n : α) + 1) := by
  refine' one_div_lt_one_div_of_lt _ _
  exact Nat.cast_add_one_pos _
  simpa

end LinearOrderedSemifield

end Nat

