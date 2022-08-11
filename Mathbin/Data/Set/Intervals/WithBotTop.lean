/-
Copyright (c) 2022 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import Mathbin.Data.Set.Intervals.Basic

/-!
# Intervals in `with_top α` and `with_bot α`

In this file we prove various lemmas about `set.image`s and `set.preimage`s of intervals under
`coe : α → with_top α` and `coe : α → with_bot α`.
-/


open Set

variable {α : Type _}

/-! ### `with_top` -/


namespace WithTop

@[simp]
theorem preimage_coe_top : (coe : α → WithTop α) ⁻¹' {⊤} = (∅ : Set α) :=
  eq_empty_of_subset_empty fun a => coe_ne_top

variable [PartialOrderₓ α] {a b : α}

theorem range_coe : Range (coe : α → WithTop α) = Iio ⊤ := by
  ext x
  rw [mem_Iio, lt_top_iff_ne_top, mem_range, ← none_eq_top, Option.ne_none_iff_exists]
  rfl

@[simp]
theorem preimage_coe_Ioi : (coe : α → WithTop α) ⁻¹' Ioi a = Ioi a :=
  ext fun x => coe_lt_coe

@[simp]
theorem preimage_coe_Ici : (coe : α → WithTop α) ⁻¹' Ici a = Ici a :=
  ext fun x => coe_le_coe

@[simp]
theorem preimage_coe_Iio : (coe : α → WithTop α) ⁻¹' Iio a = Iio a :=
  ext fun x => coe_lt_coe

@[simp]
theorem preimage_coe_Iic : (coe : α → WithTop α) ⁻¹' Iic a = Iic a :=
  ext fun x => coe_le_coe

@[simp]
theorem preimage_coe_Icc : (coe : α → WithTop α) ⁻¹' Icc a b = Icc a b := by
  simp [Ici_inter_Iic]

@[simp]
theorem preimage_coe_Ico : (coe : α → WithTop α) ⁻¹' Ico a b = Ico a b := by
  simp [Ici_inter_Iio]

@[simp]
theorem preimage_coe_Ioc : (coe : α → WithTop α) ⁻¹' Ioc a b = Ioc a b := by
  simp [Ioi_inter_Iic]

@[simp]
theorem preimage_coe_Ioo : (coe : α → WithTop α) ⁻¹' Ioo a b = Ioo a b := by
  simp [Ioi_inter_Iio]

@[simp]
theorem preimage_coe_Iio_top : (coe : α → WithTop α) ⁻¹' Iio ⊤ = univ := by
  rw [← range_coe, preimage_range]

@[simp]
theorem preimage_coe_Ico_top : (coe : α → WithTop α) ⁻¹' Ico a ⊤ = Ici a := by
  simp [Ici_inter_Iio]

@[simp]
theorem preimage_coe_Ioo_top : (coe : α → WithTop α) ⁻¹' Ioo a ⊤ = Ioi a := by
  simp [Ioi_inter_Iio]

theorem image_coe_Ioi : (coe : α → WithTop α) '' Ioi a = Ioo a ⊤ := by
  rw [← preimage_coe_Ioi, image_preimage_eq_inter_range, range_coe, Ioi_inter_Iio]

theorem image_coe_Ici : (coe : α → WithTop α) '' Ici a = Ico a ⊤ := by
  rw [← preimage_coe_Ici, image_preimage_eq_inter_range, range_coe, Ici_inter_Iio]

theorem image_coe_Iio : (coe : α → WithTop α) '' Iio a = Iio a := by
  rw [← preimage_coe_Iio, image_preimage_eq_inter_range, range_coe,
    inter_eq_self_of_subset_left (Iio_subset_Iio le_top)]

theorem image_coe_Iic : (coe : α → WithTop α) '' Iic a = Iic a := by
  rw [← preimage_coe_Iic, image_preimage_eq_inter_range, range_coe,
    inter_eq_self_of_subset_left (Iic_subset_Iio.2 <| coe_lt_top a)]

theorem image_coe_Icc : (coe : α → WithTop α) '' Icc a b = Icc a b := by
  rw [← preimage_coe_Icc, image_preimage_eq_inter_range, range_coe,
    inter_eq_self_of_subset_left (subset.trans Icc_subset_Iic_self <| Iic_subset_Iio.2 <| coe_lt_top b)]

theorem image_coe_Ico : (coe : α → WithTop α) '' Ico a b = Ico a b := by
  rw [← preimage_coe_Ico, image_preimage_eq_inter_range, range_coe,
    inter_eq_self_of_subset_left (subset.trans Ico_subset_Iio_self <| Iio_subset_Iio le_top)]

theorem image_coe_Ioc : (coe : α → WithTop α) '' Ioc a b = Ioc a b := by
  rw [← preimage_coe_Ioc, image_preimage_eq_inter_range, range_coe,
    inter_eq_self_of_subset_left (subset.trans Ioc_subset_Iic_self <| Iic_subset_Iio.2 <| coe_lt_top b)]

theorem image_coe_Ioo : (coe : α → WithTop α) '' Ioo a b = Ioo a b := by
  rw [← preimage_coe_Ioo, image_preimage_eq_inter_range, range_coe,
    inter_eq_self_of_subset_left (subset.trans Ioo_subset_Iio_self <| Iio_subset_Iio le_top)]

end WithTop

/-! ### `with_bot` -/


namespace WithBot

@[simp]
theorem preimage_coe_bot : (coe : α → WithBot α) ⁻¹' {⊥} = (∅ : Set α) :=
  @WithTop.preimage_coe_top αᵒᵈ

variable [PartialOrderₓ α] {a b : α}

theorem range_coe : Range (coe : α → WithBot α) = Ioi ⊥ :=
  @WithTop.range_coe αᵒᵈ _

@[simp]
theorem preimage_coe_Ioi : (coe : α → WithBot α) ⁻¹' Ioi a = Ioi a :=
  ext fun x => coe_lt_coe

@[simp]
theorem preimage_coe_Ici : (coe : α → WithBot α) ⁻¹' Ici a = Ici a :=
  ext fun x => coe_le_coe

@[simp]
theorem preimage_coe_Iio : (coe : α → WithBot α) ⁻¹' Iio a = Iio a :=
  ext fun x => coe_lt_coe

@[simp]
theorem preimage_coe_Iic : (coe : α → WithBot α) ⁻¹' Iic a = Iic a :=
  ext fun x => coe_le_coe

@[simp]
theorem preimage_coe_Icc : (coe : α → WithBot α) ⁻¹' Icc a b = Icc a b := by
  simp [Ici_inter_Iic]

@[simp]
theorem preimage_coe_Ico : (coe : α → WithBot α) ⁻¹' Ico a b = Ico a b := by
  simp [Ici_inter_Iio]

@[simp]
theorem preimage_coe_Ioc : (coe : α → WithBot α) ⁻¹' Ioc a b = Ioc a b := by
  simp [Ioi_inter_Iic]

@[simp]
theorem preimage_coe_Ioo : (coe : α → WithBot α) ⁻¹' Ioo a b = Ioo a b := by
  simp [Ioi_inter_Iio]

@[simp]
theorem preimage_coe_Ioi_bot : (coe : α → WithBot α) ⁻¹' Ioi ⊥ = univ := by
  rw [← range_coe, preimage_range]

@[simp]
theorem preimage_coe_Ioc_bot : (coe : α → WithBot α) ⁻¹' Ioc ⊥ a = Iic a := by
  simp [Ioi_inter_Iic]

@[simp]
theorem preimage_coe_Ioo_bot : (coe : α → WithBot α) ⁻¹' Ioo ⊥ a = Iio a := by
  simp [Ioi_inter_Iio]

theorem image_coe_Iio : (coe : α → WithBot α) '' Iio a = Ioo ⊥ a := by
  rw [← preimage_coe_Iio, image_preimage_eq_inter_range, range_coe, inter_comm, Ioi_inter_Iio]

theorem image_coe_Iic : (coe : α → WithBot α) '' Iic a = Ioc ⊥ a := by
  rw [← preimage_coe_Iic, image_preimage_eq_inter_range, range_coe, inter_comm, Ioi_inter_Iic]

theorem image_coe_Ioi : (coe : α → WithBot α) '' Ioi a = Ioi a := by
  rw [← preimage_coe_Ioi, image_preimage_eq_inter_range, range_coe,
    inter_eq_self_of_subset_left (Ioi_subset_Ioi bot_le)]

theorem image_coe_Ici : (coe : α → WithBot α) '' Ici a = Ici a := by
  rw [← preimage_coe_Ici, image_preimage_eq_inter_range, range_coe,
    inter_eq_self_of_subset_left (Ici_subset_Ioi.2 <| bot_lt_coe a)]

theorem image_coe_Icc : (coe : α → WithBot α) '' Icc a b = Icc a b := by
  rw [← preimage_coe_Icc, image_preimage_eq_inter_range, range_coe,
    inter_eq_self_of_subset_left (subset.trans Icc_subset_Ici_self <| Ici_subset_Ioi.2 <| bot_lt_coe a)]

theorem image_coe_Ioc : (coe : α → WithBot α) '' Ioc a b = Ioc a b := by
  rw [← preimage_coe_Ioc, image_preimage_eq_inter_range, range_coe,
    inter_eq_self_of_subset_left (subset.trans Ioc_subset_Ioi_self <| Ioi_subset_Ioi bot_le)]

theorem image_coe_Ico : (coe : α → WithBot α) '' Ico a b = Ico a b := by
  rw [← preimage_coe_Ico, image_preimage_eq_inter_range, range_coe,
    inter_eq_self_of_subset_left (subset.trans Ico_subset_Ici_self <| Ici_subset_Ioi.2 <| bot_lt_coe a)]

theorem image_coe_Ioo : (coe : α → WithBot α) '' Ioo a b = Ioo a b := by
  rw [← preimage_coe_Ioo, image_preimage_eq_inter_range, range_coe,
    inter_eq_self_of_subset_left (subset.trans Ioo_subset_Ioi_self <| Ioi_subset_Ioi bot_le)]

end WithBot

