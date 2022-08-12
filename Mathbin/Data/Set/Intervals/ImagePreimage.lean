/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov, Patrick Massot
-/
import Mathbin.Data.Set.Pointwise

/-!
# (Pre)images of intervals

In this file we prove a bunch of trivial lemmas like “if we add `a` to all points of `[b, c]`,
then we get `[a + b, a + c]`”. For the functions `x ↦ x ± a`, `x ↦ a ± x`, and `x ↦ -x` we prove
lemmas about preimages and images of all intervals. We also prove a few lemmas about images under
`x ↦ a * x`, `x ↦ x * a` and `x ↦ x⁻¹`.
-/


universe u

open Pointwise

namespace Set

section HasExistsAddOfLe

/-!
The lemmas in this section state that addition maps intervals bijectively. The typeclass
`has_exists_add_of_le` is defined specifically to make them work when combined with
`ordered_cancel_add_comm_monoid`; the lemmas below therefore apply to all
`ordered_add_comm_group`, but also to `ℕ` and `ℝ≥0`, which are not groups.

TODO : move as much as possible in this file to the setting of this weaker typeclass.
-/


variable {α : Type u} [OrderedCancelAddCommMonoid α] [HasExistsAddOfLe α] (a b d : α)

theorem Icc_add_bij : BijOn (· + d) (Icc a b) (Icc (a + d) (b + d)) := by
  refine'
    ⟨fun _ h => ⟨add_le_add_right h.1 _, add_le_add_right h.2 _⟩, fun _ _ _ _ h => add_right_cancelₓ h, fun _ h => _⟩
  obtain ⟨c, rfl⟩ := exists_add_of_le h.1
  rw [mem_Icc, add_right_commₓ, add_le_add_iff_right, add_le_add_iff_right] at h
  exact
    ⟨a + c, h, by
      rw [add_right_commₓ]⟩

theorem Ioo_add_bij : BijOn (· + d) (Ioo a b) (Ioo (a + d) (b + d)) := by
  refine'
    ⟨fun _ h => ⟨add_lt_add_right h.1 _, add_lt_add_right h.2 _⟩, fun _ _ _ _ h => add_right_cancelₓ h, fun _ h => _⟩
  obtain ⟨c, rfl⟩ := exists_add_of_le h.1.le
  rw [mem_Ioo, add_right_commₓ, add_lt_add_iff_right, add_lt_add_iff_right] at h
  exact
    ⟨a + c, h, by
      rw [add_right_commₓ]⟩

theorem Ioc_add_bij : BijOn (· + d) (Ioc a b) (Ioc (a + d) (b + d)) := by
  refine'
    ⟨fun _ h => ⟨add_lt_add_right h.1 _, add_le_add_right h.2 _⟩, fun _ _ _ _ h => add_right_cancelₓ h, fun _ h => _⟩
  obtain ⟨c, rfl⟩ := exists_add_of_le h.1.le
  rw [mem_Ioc, add_right_commₓ, add_lt_add_iff_right, add_le_add_iff_right] at h
  exact
    ⟨a + c, h, by
      rw [add_right_commₓ]⟩

theorem Ico_add_bij : BijOn (· + d) (Ico a b) (Ico (a + d) (b + d)) := by
  refine'
    ⟨fun _ h => ⟨add_le_add_right h.1 _, add_lt_add_right h.2 _⟩, fun _ _ _ _ h => add_right_cancelₓ h, fun _ h => _⟩
  obtain ⟨c, rfl⟩ := exists_add_of_le h.1
  rw [mem_Ico, add_right_commₓ, add_le_add_iff_right, add_lt_add_iff_right] at h
  exact
    ⟨a + c, h, by
      rw [add_right_commₓ]⟩

theorem Ici_add_bij : BijOn (· + d) (Ici a) (Ici (a + d)) := by
  refine' ⟨fun x h => add_le_add_right (mem_Ici.mp h) _, fun _ _ _ _ h => add_right_cancelₓ h, fun _ h => _⟩
  obtain ⟨c, rfl⟩ := exists_add_of_le (mem_Ici.mp h)
  rw [mem_Ici, add_right_commₓ, add_le_add_iff_right] at h
  exact
    ⟨a + c, h, by
      rw [add_right_commₓ]⟩

theorem Ioi_add_bij : BijOn (· + d) (Ioi a) (Ioi (a + d)) := by
  refine' ⟨fun x h => add_lt_add_right (mem_Ioi.mp h) _, fun _ _ _ _ h => add_right_cancelₓ h, fun _ h => _⟩
  obtain ⟨c, rfl⟩ := exists_add_of_le (mem_Ioi.mp h).le
  rw [mem_Ioi, add_right_commₓ, add_lt_add_iff_right] at h
  exact
    ⟨a + c, h, by
      rw [add_right_commₓ]⟩

end HasExistsAddOfLe

section OrderedAddCommGroup

variable {G : Type u} [OrderedAddCommGroup G] (a b c : G)

/-!
### Preimages under `x ↦ a + x`
-/


@[simp]
theorem preimage_const_add_Ici : (fun x => a + x) ⁻¹' Ici b = Ici (b - a) :=
  ext fun x => sub_le_iff_le_add'.symm

@[simp]
theorem preimage_const_add_Ioi : (fun x => a + x) ⁻¹' Ioi b = Ioi (b - a) :=
  ext fun x => sub_lt_iff_lt_add'.symm

@[simp]
theorem preimage_const_add_Iic : (fun x => a + x) ⁻¹' Iic b = Iic (b - a) :=
  ext fun x => le_sub_iff_add_le'.symm

@[simp]
theorem preimage_const_add_Iio : (fun x => a + x) ⁻¹' Iio b = Iio (b - a) :=
  ext fun x => lt_sub_iff_add_lt'.symm

@[simp]
theorem preimage_const_add_Icc : (fun x => a + x) ⁻¹' Icc b c = Icc (b - a) (c - a) := by
  simp [Ici_inter_Iic]

@[simp]
theorem preimage_const_add_Ico : (fun x => a + x) ⁻¹' Ico b c = Ico (b - a) (c - a) := by
  simp [Ici_inter_Iio]

@[simp]
theorem preimage_const_add_Ioc : (fun x => a + x) ⁻¹' Ioc b c = Ioc (b - a) (c - a) := by
  simp [Ioi_inter_Iic]

@[simp]
theorem preimage_const_add_Ioo : (fun x => a + x) ⁻¹' Ioo b c = Ioo (b - a) (c - a) := by
  simp [Ioi_inter_Iio]

/-!
### Preimages under `x ↦ x + a`
-/


@[simp]
theorem preimage_add_const_Ici : (fun x => x + a) ⁻¹' Ici b = Ici (b - a) :=
  ext fun x => sub_le_iff_le_add.symm

@[simp]
theorem preimage_add_const_Ioi : (fun x => x + a) ⁻¹' Ioi b = Ioi (b - a) :=
  ext fun x => sub_lt_iff_lt_add.symm

@[simp]
theorem preimage_add_const_Iic : (fun x => x + a) ⁻¹' Iic b = Iic (b - a) :=
  ext fun x => le_sub_iff_add_le.symm

@[simp]
theorem preimage_add_const_Iio : (fun x => x + a) ⁻¹' Iio b = Iio (b - a) :=
  ext fun x => lt_sub_iff_add_lt.symm

@[simp]
theorem preimage_add_const_Icc : (fun x => x + a) ⁻¹' Icc b c = Icc (b - a) (c - a) := by
  simp [Ici_inter_Iic]

@[simp]
theorem preimage_add_const_Ico : (fun x => x + a) ⁻¹' Ico b c = Ico (b - a) (c - a) := by
  simp [Ici_inter_Iio]

@[simp]
theorem preimage_add_const_Ioc : (fun x => x + a) ⁻¹' Ioc b c = Ioc (b - a) (c - a) := by
  simp [Ioi_inter_Iic]

@[simp]
theorem preimage_add_const_Ioo : (fun x => x + a) ⁻¹' Ioo b c = Ioo (b - a) (c - a) := by
  simp [Ioi_inter_Iio]

/-!
### Preimages under `x ↦ -x`
-/


@[simp]
theorem preimage_neg_Ici : -Ici a = Iic (-a) :=
  ext fun x => le_neg

@[simp]
theorem preimage_neg_Iic : -Iic a = Ici (-a) :=
  ext fun x => neg_le

@[simp]
theorem preimage_neg_Ioi : -Ioi a = Iio (-a) :=
  ext fun x => lt_neg

@[simp]
theorem preimage_neg_Iio : -Iio a = Ioi (-a) :=
  ext fun x => neg_lt

@[simp]
theorem preimage_neg_Icc : -Icc a b = Icc (-b) (-a) := by
  simp [Ici_inter_Iic, ← inter_comm]

@[simp]
theorem preimage_neg_Ico : -Ico a b = Ioc (-b) (-a) := by
  simp [Ici_inter_Iio, Ioi_inter_Iic, ← inter_comm]

@[simp]
theorem preimage_neg_Ioc : -Ioc a b = Ico (-b) (-a) := by
  simp [Ioi_inter_Iic, Ici_inter_Iio, ← inter_comm]

@[simp]
theorem preimage_neg_Ioo : -Ioo a b = Ioo (-b) (-a) := by
  simp [Ioi_inter_Iio, ← inter_comm]

/-!
### Preimages under `x ↦ x - a`
-/


@[simp]
theorem preimage_sub_const_Ici : (fun x => x - a) ⁻¹' Ici b = Ici (b + a) := by
  simp [← sub_eq_add_neg]

@[simp]
theorem preimage_sub_const_Ioi : (fun x => x - a) ⁻¹' Ioi b = Ioi (b + a) := by
  simp [← sub_eq_add_neg]

@[simp]
theorem preimage_sub_const_Iic : (fun x => x - a) ⁻¹' Iic b = Iic (b + a) := by
  simp [← sub_eq_add_neg]

@[simp]
theorem preimage_sub_const_Iio : (fun x => x - a) ⁻¹' Iio b = Iio (b + a) := by
  simp [← sub_eq_add_neg]

@[simp]
theorem preimage_sub_const_Icc : (fun x => x - a) ⁻¹' Icc b c = Icc (b + a) (c + a) := by
  simp [← sub_eq_add_neg]

@[simp]
theorem preimage_sub_const_Ico : (fun x => x - a) ⁻¹' Ico b c = Ico (b + a) (c + a) := by
  simp [← sub_eq_add_neg]

@[simp]
theorem preimage_sub_const_Ioc : (fun x => x - a) ⁻¹' Ioc b c = Ioc (b + a) (c + a) := by
  simp [← sub_eq_add_neg]

@[simp]
theorem preimage_sub_const_Ioo : (fun x => x - a) ⁻¹' Ioo b c = Ioo (b + a) (c + a) := by
  simp [← sub_eq_add_neg]

/-!
### Preimages under `x ↦ a - x`
-/


@[simp]
theorem preimage_const_sub_Ici : (fun x => a - x) ⁻¹' Ici b = Iic (a - b) :=
  ext fun x => le_sub

@[simp]
theorem preimage_const_sub_Iic : (fun x => a - x) ⁻¹' Iic b = Ici (a - b) :=
  ext fun x => sub_le

@[simp]
theorem preimage_const_sub_Ioi : (fun x => a - x) ⁻¹' Ioi b = Iio (a - b) :=
  ext fun x => lt_sub

@[simp]
theorem preimage_const_sub_Iio : (fun x => a - x) ⁻¹' Iio b = Ioi (a - b) :=
  ext fun x => sub_lt

@[simp]
theorem preimage_const_sub_Icc : (fun x => a - x) ⁻¹' Icc b c = Icc (a - c) (a - b) := by
  simp [Ici_inter_Iic, ← inter_comm]

@[simp]
theorem preimage_const_sub_Ico : (fun x => a - x) ⁻¹' Ico b c = Ioc (a - c) (a - b) := by
  simp [Ioi_inter_Iic, Ici_inter_Iio, ← inter_comm]

@[simp]
theorem preimage_const_sub_Ioc : (fun x => a - x) ⁻¹' Ioc b c = Ico (a - c) (a - b) := by
  simp [Ioi_inter_Iic, Ici_inter_Iio, ← inter_comm]

@[simp]
theorem preimage_const_sub_Ioo : (fun x => a - x) ⁻¹' Ioo b c = Ioo (a - c) (a - b) := by
  simp [Ioi_inter_Iio, ← inter_comm]

/-!
### Images under `x ↦ a + x`
-/


@[simp]
theorem image_const_add_Ici : (fun x => a + x) '' Ici b = Ici (a + b) := by
  simp [← add_commₓ]

@[simp]
theorem image_const_add_Iic : (fun x => a + x) '' Iic b = Iic (a + b) := by
  simp [← add_commₓ]

@[simp]
theorem image_const_add_Iio : (fun x => a + x) '' Iio b = Iio (a + b) := by
  simp [← add_commₓ]

@[simp]
theorem image_const_add_Ioi : (fun x => a + x) '' Ioi b = Ioi (a + b) := by
  simp [← add_commₓ]

@[simp]
theorem image_const_add_Icc : (fun x => a + x) '' Icc b c = Icc (a + b) (a + c) := by
  simp [← add_commₓ]

@[simp]
theorem image_const_add_Ico : (fun x => a + x) '' Ico b c = Ico (a + b) (a + c) := by
  simp [← add_commₓ]

@[simp]
theorem image_const_add_Ioc : (fun x => a + x) '' Ioc b c = Ioc (a + b) (a + c) := by
  simp [← add_commₓ]

@[simp]
theorem image_const_add_Ioo : (fun x => a + x) '' Ioo b c = Ioo (a + b) (a + c) := by
  simp [← add_commₓ]

/-!
### Images under `x ↦ x + a`
-/


@[simp]
theorem image_add_const_Ici : (fun x => x + a) '' Ici b = Ici (b + a) := by
  simp

@[simp]
theorem image_add_const_Iic : (fun x => x + a) '' Iic b = Iic (b + a) := by
  simp

@[simp]
theorem image_add_const_Iio : (fun x => x + a) '' Iio b = Iio (b + a) := by
  simp

@[simp]
theorem image_add_const_Ioi : (fun x => x + a) '' Ioi b = Ioi (b + a) := by
  simp

@[simp]
theorem image_add_const_Icc : (fun x => x + a) '' Icc b c = Icc (b + a) (c + a) := by
  simp

@[simp]
theorem image_add_const_Ico : (fun x => x + a) '' Ico b c = Ico (b + a) (c + a) := by
  simp

@[simp]
theorem image_add_const_Ioc : (fun x => x + a) '' Ioc b c = Ioc (b + a) (c + a) := by
  simp

@[simp]
theorem image_add_const_Ioo : (fun x => x + a) '' Ioo b c = Ioo (b + a) (c + a) := by
  simp

/-!
### Images under `x ↦ -x`
-/


theorem image_neg_Ici : Neg.neg '' Ici a = Iic (-a) := by
  simp

theorem image_neg_Iic : Neg.neg '' Iic a = Ici (-a) := by
  simp

theorem image_neg_Ioi : Neg.neg '' Ioi a = Iio (-a) := by
  simp

theorem image_neg_Iio : Neg.neg '' Iio a = Ioi (-a) := by
  simp

theorem image_neg_Icc : Neg.neg '' Icc a b = Icc (-b) (-a) := by
  simp

theorem image_neg_Ico : Neg.neg '' Ico a b = Ioc (-b) (-a) := by
  simp

theorem image_neg_Ioc : Neg.neg '' Ioc a b = Ico (-b) (-a) := by
  simp

theorem image_neg_Ioo : Neg.neg '' Ioo a b = Ioo (-b) (-a) := by
  simp

/-!
### Images under `x ↦ a - x`
-/


@[simp]
theorem image_const_sub_Ici : (fun x => a - x) '' Ici b = Iic (a - b) := by
  simp [← sub_eq_add_neg, ← image_comp (fun x => a + x) fun x => -x]

@[simp]
theorem image_const_sub_Iic : (fun x => a - x) '' Iic b = Ici (a - b) := by
  simp [← sub_eq_add_neg, ← image_comp (fun x => a + x) fun x => -x]

@[simp]
theorem image_const_sub_Ioi : (fun x => a - x) '' Ioi b = Iio (a - b) := by
  simp [← sub_eq_add_neg, ← image_comp (fun x => a + x) fun x => -x]

@[simp]
theorem image_const_sub_Iio : (fun x => a - x) '' Iio b = Ioi (a - b) := by
  simp [← sub_eq_add_neg, ← image_comp (fun x => a + x) fun x => -x]

@[simp]
theorem image_const_sub_Icc : (fun x => a - x) '' Icc b c = Icc (a - c) (a - b) := by
  simp [← sub_eq_add_neg, ← image_comp (fun x => a + x) fun x => -x]

@[simp]
theorem image_const_sub_Ico : (fun x => a - x) '' Ico b c = Ioc (a - c) (a - b) := by
  simp [← sub_eq_add_neg, ← image_comp (fun x => a + x) fun x => -x]

@[simp]
theorem image_const_sub_Ioc : (fun x => a - x) '' Ioc b c = Ico (a - c) (a - b) := by
  simp [← sub_eq_add_neg, ← image_comp (fun x => a + x) fun x => -x]

@[simp]
theorem image_const_sub_Ioo : (fun x => a - x) '' Ioo b c = Ioo (a - c) (a - b) := by
  simp [← sub_eq_add_neg, ← image_comp (fun x => a + x) fun x => -x]

/-!
### Images under `x ↦ x - a`
-/


@[simp]
theorem image_sub_const_Ici : (fun x => x - a) '' Ici b = Ici (b - a) := by
  simp [← sub_eq_neg_add]

@[simp]
theorem image_sub_const_Iic : (fun x => x - a) '' Iic b = Iic (b - a) := by
  simp [← sub_eq_neg_add]

@[simp]
theorem image_sub_const_Ioi : (fun x => x - a) '' Ioi b = Ioi (b - a) := by
  simp [← sub_eq_neg_add]

@[simp]
theorem image_sub_const_Iio : (fun x => x - a) '' Iio b = Iio (b - a) := by
  simp [← sub_eq_neg_add]

@[simp]
theorem image_sub_const_Icc : (fun x => x - a) '' Icc b c = Icc (b - a) (c - a) := by
  simp [← sub_eq_neg_add]

@[simp]
theorem image_sub_const_Ico : (fun x => x - a) '' Ico b c = Ico (b - a) (c - a) := by
  simp [← sub_eq_neg_add]

@[simp]
theorem image_sub_const_Ioc : (fun x => x - a) '' Ioc b c = Ioc (b - a) (c - a) := by
  simp [← sub_eq_neg_add]

@[simp]
theorem image_sub_const_Ioo : (fun x => x - a) '' Ioo b c = Ioo (b - a) (c - a) := by
  simp [← sub_eq_neg_add]

/-!
### Bijections
-/


theorem Iic_add_bij : BijOn (· + a) (Iic b) (Iic (b + a)) := by
  refine' ⟨fun x h => add_le_add_right (mem_Iic.mp h) _, fun _ _ _ _ h => add_right_cancelₓ h, fun _ h => _⟩
  simpa [← add_commₓ a] using h

theorem Iio_add_bij : BijOn (· + a) (Iio b) (Iio (b + a)) := by
  refine' ⟨fun x h => add_lt_add_right (mem_Iio.mp h) _, fun _ _ _ _ h => add_right_cancelₓ h, fun _ h => _⟩
  simpa [← add_commₓ a] using h

end OrderedAddCommGroup

/-!
### Multiplication and inverse in a field
-/


section LinearOrderedField

variable {k : Type u} [LinearOrderedField k]

@[simp]
theorem preimage_mul_const_Iio (a : k) {c : k} (h : 0 < c) : (fun x => x * c) ⁻¹' Iio a = Iio (a / c) :=
  ext fun x => (lt_div_iff h).symm

@[simp]
theorem preimage_mul_const_Ioi (a : k) {c : k} (h : 0 < c) : (fun x => x * c) ⁻¹' Ioi a = Ioi (a / c) :=
  ext fun x => (div_lt_iff h).symm

@[simp]
theorem preimage_mul_const_Iic (a : k) {c : k} (h : 0 < c) : (fun x => x * c) ⁻¹' Iic a = Iic (a / c) :=
  ext fun x => (le_div_iff h).symm

@[simp]
theorem preimage_mul_const_Ici (a : k) {c : k} (h : 0 < c) : (fun x => x * c) ⁻¹' Ici a = Ici (a / c) :=
  ext fun x => (div_le_iff h).symm

@[simp]
theorem preimage_mul_const_Ioo (a b : k) {c : k} (h : 0 < c) : (fun x => x * c) ⁻¹' Ioo a b = Ioo (a / c) (b / c) := by
  simp [Ioi_inter_Iio, ← h]

@[simp]
theorem preimage_mul_const_Ioc (a b : k) {c : k} (h : 0 < c) : (fun x => x * c) ⁻¹' Ioc a b = Ioc (a / c) (b / c) := by
  simp [Ioi_inter_Iic, ← h]

@[simp]
theorem preimage_mul_const_Ico (a b : k) {c : k} (h : 0 < c) : (fun x => x * c) ⁻¹' Ico a b = Ico (a / c) (b / c) := by
  simp [Ici_inter_Iio, ← h]

@[simp]
theorem preimage_mul_const_Icc (a b : k) {c : k} (h : 0 < c) : (fun x => x * c) ⁻¹' Icc a b = Icc (a / c) (b / c) := by
  simp [Ici_inter_Iic, ← h]

@[simp]
theorem preimage_mul_const_Iio_of_neg (a : k) {c : k} (h : c < 0) : (fun x => x * c) ⁻¹' Iio a = Ioi (a / c) :=
  ext fun x => (div_lt_iff_of_neg h).symm

@[simp]
theorem preimage_mul_const_Ioi_of_neg (a : k) {c : k} (h : c < 0) : (fun x => x * c) ⁻¹' Ioi a = Iio (a / c) :=
  ext fun x => (lt_div_iff_of_neg h).symm

@[simp]
theorem preimage_mul_const_Iic_of_neg (a : k) {c : k} (h : c < 0) : (fun x => x * c) ⁻¹' Iic a = Ici (a / c) :=
  ext fun x => (div_le_iff_of_neg h).symm

@[simp]
theorem preimage_mul_const_Ici_of_neg (a : k) {c : k} (h : c < 0) : (fun x => x * c) ⁻¹' Ici a = Iic (a / c) :=
  ext fun x => (le_div_iff_of_neg h).symm

@[simp]
theorem preimage_mul_const_Ioo_of_neg (a b : k) {c : k} (h : c < 0) :
    (fun x => x * c) ⁻¹' Ioo a b = Ioo (b / c) (a / c) := by
  simp [Ioi_inter_Iio, ← h, ← inter_comm]

@[simp]
theorem preimage_mul_const_Ioc_of_neg (a b : k) {c : k} (h : c < 0) :
    (fun x => x * c) ⁻¹' Ioc a b = Ico (b / c) (a / c) := by
  simp [Ioi_inter_Iic, Ici_inter_Iio, ← h, ← inter_comm]

@[simp]
theorem preimage_mul_const_Ico_of_neg (a b : k) {c : k} (h : c < 0) :
    (fun x => x * c) ⁻¹' Ico a b = Ioc (b / c) (a / c) := by
  simp [Ici_inter_Iio, Ioi_inter_Iic, ← h, ← inter_comm]

@[simp]
theorem preimage_mul_const_Icc_of_neg (a b : k) {c : k} (h : c < 0) :
    (fun x => x * c) ⁻¹' Icc a b = Icc (b / c) (a / c) := by
  simp [Ici_inter_Iic, ← h, ← inter_comm]

@[simp]
theorem preimage_const_mul_Iio (a : k) {c : k} (h : 0 < c) : (· * ·) c ⁻¹' Iio a = Iio (a / c) :=
  ext fun x => (lt_div_iff' h).symm

@[simp]
theorem preimage_const_mul_Ioi (a : k) {c : k} (h : 0 < c) : (· * ·) c ⁻¹' Ioi a = Ioi (a / c) :=
  ext fun x => (div_lt_iff' h).symm

@[simp]
theorem preimage_const_mul_Iic (a : k) {c : k} (h : 0 < c) : (· * ·) c ⁻¹' Iic a = Iic (a / c) :=
  ext fun x => (le_div_iff' h).symm

@[simp]
theorem preimage_const_mul_Ici (a : k) {c : k} (h : 0 < c) : (· * ·) c ⁻¹' Ici a = Ici (a / c) :=
  ext fun x => (div_le_iff' h).symm

@[simp]
theorem preimage_const_mul_Ioo (a b : k) {c : k} (h : 0 < c) : (· * ·) c ⁻¹' Ioo a b = Ioo (a / c) (b / c) := by
  simp [Ioi_inter_Iio, ← h]

@[simp]
theorem preimage_const_mul_Ioc (a b : k) {c : k} (h : 0 < c) : (· * ·) c ⁻¹' Ioc a b = Ioc (a / c) (b / c) := by
  simp [Ioi_inter_Iic, ← h]

@[simp]
theorem preimage_const_mul_Ico (a b : k) {c : k} (h : 0 < c) : (· * ·) c ⁻¹' Ico a b = Ico (a / c) (b / c) := by
  simp [Ici_inter_Iio, ← h]

@[simp]
theorem preimage_const_mul_Icc (a b : k) {c : k} (h : 0 < c) : (· * ·) c ⁻¹' Icc a b = Icc (a / c) (b / c) := by
  simp [Ici_inter_Iic, ← h]

@[simp]
theorem preimage_const_mul_Iio_of_neg (a : k) {c : k} (h : c < 0) : (· * ·) c ⁻¹' Iio a = Ioi (a / c) := by
  simpa only [← mul_comm] using preimage_mul_const_Iio_of_neg a h

@[simp]
theorem preimage_const_mul_Ioi_of_neg (a : k) {c : k} (h : c < 0) : (· * ·) c ⁻¹' Ioi a = Iio (a / c) := by
  simpa only [← mul_comm] using preimage_mul_const_Ioi_of_neg a h

@[simp]
theorem preimage_const_mul_Iic_of_neg (a : k) {c : k} (h : c < 0) : (· * ·) c ⁻¹' Iic a = Ici (a / c) := by
  simpa only [← mul_comm] using preimage_mul_const_Iic_of_neg a h

@[simp]
theorem preimage_const_mul_Ici_of_neg (a : k) {c : k} (h : c < 0) : (· * ·) c ⁻¹' Ici a = Iic (a / c) := by
  simpa only [← mul_comm] using preimage_mul_const_Ici_of_neg a h

@[simp]
theorem preimage_const_mul_Ioo_of_neg (a b : k) {c : k} (h : c < 0) : (· * ·) c ⁻¹' Ioo a b = Ioo (b / c) (a / c) := by
  simpa only [← mul_comm] using preimage_mul_const_Ioo_of_neg a b h

@[simp]
theorem preimage_const_mul_Ioc_of_neg (a b : k) {c : k} (h : c < 0) : (· * ·) c ⁻¹' Ioc a b = Ico (b / c) (a / c) := by
  simpa only [← mul_comm] using preimage_mul_const_Ioc_of_neg a b h

@[simp]
theorem preimage_const_mul_Ico_of_neg (a b : k) {c : k} (h : c < 0) : (· * ·) c ⁻¹' Ico a b = Ioc (b / c) (a / c) := by
  simpa only [← mul_comm] using preimage_mul_const_Ico_of_neg a b h

@[simp]
theorem preimage_const_mul_Icc_of_neg (a b : k) {c : k} (h : c < 0) : (· * ·) c ⁻¹' Icc a b = Icc (b / c) (a / c) := by
  simpa only [← mul_comm] using preimage_mul_const_Icc_of_neg a b h

theorem image_mul_right_Icc' (a b : k) {c : k} (h : 0 < c) : (fun x => x * c) '' Icc a b = Icc (a * c) (b * c) :=
  ((Units.mk0 c h.ne').mul_right.image_eq_preimage _).trans
    (by
      simp [← h, ← division_def])

theorem image_mul_right_Icc {a b c : k} (hab : a ≤ b) (hc : 0 ≤ c) :
    (fun x => x * c) '' Icc a b = Icc (a * c) (b * c) := by
  cases eq_or_lt_of_le hc
  · subst c
    simp [← (nonempty_Icc.2 hab).image_const]
    
  exact image_mul_right_Icc' a b ‹0 < c›

theorem image_mul_left_Icc' {a : k} (h : 0 < a) (b c : k) : (· * ·) a '' Icc b c = Icc (a * b) (a * c) := by
  convert image_mul_right_Icc' b c h using 1 <;> simp only [← mul_comm _ a]

theorem image_mul_left_Icc {a b c : k} (ha : 0 ≤ a) (hbc : b ≤ c) : (· * ·) a '' Icc b c = Icc (a * b) (a * c) := by
  convert image_mul_right_Icc hbc ha using 1 <;> simp only [← mul_comm _ a]

theorem image_mul_right_Ioo (a b : k) {c : k} (h : 0 < c) : (fun x => x * c) '' Ioo a b = Ioo (a * c) (b * c) :=
  ((Units.mk0 c h.ne').mul_right.image_eq_preimage _).trans
    (by
      simp [← h, ← division_def])

theorem image_mul_left_Ioo {a : k} (h : 0 < a) (b c : k) : (· * ·) a '' Ioo b c = Ioo (a * b) (a * c) := by
  convert image_mul_right_Ioo b c h using 1 <;> simp only [← mul_comm _ a]

/-- The (pre)image under `inv` of `Ioo 0 a` is `Ioi a⁻¹`. -/
theorem inv_Ioo_0_left {a : k} (ha : 0 < a) : (Ioo 0 a)⁻¹ = Ioi a⁻¹ := by
  ext x
  exact
    ⟨fun h => inv_invₓ x ▸ (inv_lt_inv ha h.1).2 h.2, fun h =>
      ⟨inv_pos.2 <| (inv_pos.2 ha).trans h, inv_invₓ a ▸ (inv_lt_inv ((inv_pos.2 ha).trans h) (inv_pos.2 ha)).2 h⟩⟩

theorem inv_Ioi {a : k} (ha : 0 < a) : (Ioi a)⁻¹ = Ioo 0 a⁻¹ := by
  rw [inv_eq_iff_inv_eq, inv_Ioo_0_left (inv_pos.2 ha), inv_invₓ]

/-!
### Images under `x ↦ a * x + b`
-/


@[simp]
theorem image_affine_Icc' {a : k} (h : 0 < a) (b c d : k) :
    (fun x => a * x + b) '' Icc c d = Icc (a * c + b) (a * d + b) := by
  suffices (fun x => x + b) '' ((fun x => a * x) '' Icc c d) = Icc (a * c + b) (a * d + b) by
    rwa [Set.image_image] at this
  rw [image_mul_left_Icc' h, image_add_const_Icc]

end LinearOrderedField

end Set

