/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Benjamin Davidson
-/
import Mathbin.Analysis.SpecialFunctions.Trigonometric.Complex

/-!
# The `arctan` function.

Inequalities, derivatives,
and `real.tan` as a `local_homeomorph` between `(-(π / 2), π / 2)` and the whole line.
-/


noncomputable section

namespace Real

open Set Filter

open TopologicalSpace Real

theorem tan_add {x y : ℝ}
    (h :
      ((∀ k : ℤ, x ≠ (2 * k + 1) * π / 2) ∧ ∀ l : ℤ, y ≠ (2 * l + 1) * π / 2) ∨
        (∃ k : ℤ, x = (2 * k + 1) * π / 2) ∧ ∃ l : ℤ, y = (2 * l + 1) * π / 2) :
    tan (x + y) = (tan x + tan y) / (1 - tan x * tan y) := by
  simpa only [Complex.of_real_inj, ← Complex.of_real_sub, ← Complex.of_real_add, ← Complex.of_real_div, ←
    Complex.of_real_mul, ← Complex.of_real_tan] using
    @Complex.tan_add (x : ℂ) (y : ℂ)
      (by
        convert h <;> norm_cast)

theorem tan_add' {x y : ℝ} (h : (∀ k : ℤ, x ≠ (2 * k + 1) * π / 2) ∧ ∀ l : ℤ, y ≠ (2 * l + 1) * π / 2) :
    tan (x + y) = (tan x + tan y) / (1 - tan x * tan y) :=
  tan_add (Or.inl h)

theorem tan_two_mul {x : ℝ} : tan (2 * x) = 2 * tan x / (1 - tan x ^ 2) := by
  simpa only [Complex.of_real_inj, ← Complex.of_real_sub, ← Complex.of_real_div, ← Complex.of_real_pow, ←
    Complex.of_real_mul, ← Complex.of_real_tan, ← Complex.of_real_bit0, ← Complex.of_real_one] using Complex.tan_two_mul

theorem tan_ne_zero_iff {θ : ℝ} : tan θ ≠ 0 ↔ ∀ k : ℤ, θ ≠ k * π / 2 := by
  rw [← Complex.of_real_ne_zero, Complex.of_real_tan, Complex.tan_ne_zero_iff] <;> norm_cast

theorem tan_eq_zero_iff {θ : ℝ} : tan θ = 0 ↔ ∃ k : ℤ, θ = k * π / 2 := by
  rw [← not_iff_not, not_exists, ← Ne, tan_ne_zero_iff]

theorem tan_int_mul_pi_div_two (n : ℤ) : tan (n * π / 2) = 0 :=
  tan_eq_zero_iff.mpr
    (by
      use n)

theorem continuous_on_tan : ContinuousOn tan { x | cos x ≠ 0 } := by
  suffices ContinuousOn (fun x => sin x / cos x) { x | cos x ≠ 0 } by
    have h_eq : (fun x => sin x / cos x) = tan := by
      ext1 x
      rw [tan_eq_sin_div_cos]
    rwa [h_eq] at this
  exact continuous_on_sin.div continuous_on_cos fun x => id

@[continuity]
theorem continuous_tan : Continuous fun x : { x | cos x ≠ 0 } => tan x :=
  continuous_on_iff_continuous_restrict.1 continuous_on_tan

theorem continuous_on_tan_Ioo : ContinuousOn tan (Ioo (-(π / 2)) (π / 2)) := by
  refine' ContinuousOn.mono continuous_on_tan fun x => _
  simp only [← and_imp, ← mem_Ioo, ← mem_set_of_eq, ← Ne.def]
  rw [cos_eq_zero_iff]
  rintro hx_gt hx_lt ⟨r, hxr_eq⟩
  cases le_or_ltₓ 0 r
  · rw [lt_iff_not_geₓ] at hx_lt
    refine' hx_lt _
    rw [hxr_eq, ← one_mulₓ (π / 2), mul_div_assoc, ge_iff_le, mul_le_mul_right (half_pos pi_pos)]
    simp [← h]
    
  · rw [lt_iff_not_geₓ] at hx_gt
    refine' hx_gt _
    rw [hxr_eq, ← one_mulₓ (π / 2), mul_div_assoc, ge_iff_le, neg_mul_eq_neg_mulₓ, mul_le_mul_right (half_pos pi_pos)]
    have hr_le : r ≤ -1 := by
      rwa [Int.lt_iff_add_one_leₓ, ← le_neg_iff_add_nonpos_right] at h
    rw [← le_sub_iff_add_le, mul_comm, ← le_div_iff]
    · norm_num
      rw [← Int.cast_oneₓ, ← Int.cast_neg]
      norm_cast
      exact hr_le
      
    · exact zero_lt_two
      
    

theorem surj_on_tan : SurjOn tan (Ioo (-(π / 2)) (π / 2)) Univ :=
  have := neg_lt_self pi_div_two_pos
  continuous_on_tan_Ioo.surj_on_of_tendsto (nonempty_Ioo.2 this)
    (by
      simp [← tendsto_tan_neg_pi_div_two, ← this])
    (by
      simp [← tendsto_tan_pi_div_two, ← this])

theorem tan_surjective : Function.Surjective tan := fun x => surj_on_tan.subset_range trivialₓ

theorem image_tan_Ioo : tan '' Ioo (-(π / 2)) (π / 2) = univ :=
  univ_subset_iff.1 surj_on_tan

/-- `real.tan` as an `order_iso` between `(-(π / 2), π / 2)` and `ℝ`. -/
def tanOrderIso : Ioo (-(π / 2)) (π / 2) ≃o ℝ :=
  (strict_mono_on_tan.OrderIso _ _).trans <| (OrderIso.setCongr _ _ image_tan_Ioo).trans OrderIso.Set.univ

/-- Inverse of the `tan` function, returns values in the range `-π / 2 < arctan x` and
`arctan x < π / 2` -/
@[pp_nodot]
noncomputable def arctan (x : ℝ) : ℝ :=
  tanOrderIso.symm x

@[simp]
theorem tan_arctan (x : ℝ) : tan (arctan x) = x :=
  tanOrderIso.apply_symm_apply x

theorem arctan_mem_Ioo (x : ℝ) : arctan x ∈ Ioo (-(π / 2)) (π / 2) :=
  Subtype.coe_prop _

@[simp]
theorem range_arctan : Range arctan = Ioo (-(π / 2)) (π / 2) :=
  ((EquivLike.surjective _).range_comp _).trans Subtype.range_coe

theorem arctan_tan {x : ℝ} (hx₁ : -(π / 2) < x) (hx₂ : x < π / 2) : arctan (tan x) = x :=
  Subtype.ext_iff.1 <| tanOrderIso.symm_apply_apply ⟨x, hx₁, hx₂⟩

theorem cos_arctan_pos (x : ℝ) : 0 < cos (arctan x) :=
  cos_pos_of_mem_Ioo <| arctan_mem_Ioo x

theorem cos_sq_arctan (x : ℝ) : cos (arctan x) ^ 2 = 1 / (1 + x ^ 2) := by
  rw [one_div, ← inv_one_add_tan_sq (cos_arctan_pos x).ne', tan_arctan]

theorem sin_arctan (x : ℝ) : sin (arctan x) = x / sqrt (1 + x ^ 2) := by
  rw [← tan_div_sqrt_one_add_tan_sq (cos_arctan_pos x), tan_arctan]

theorem cos_arctan (x : ℝ) : cos (arctan x) = 1 / sqrt (1 + x ^ 2) := by
  rw [one_div, ← inv_sqrt_one_add_tan_sq (cos_arctan_pos x), tan_arctan]

theorem arctan_lt_pi_div_two (x : ℝ) : arctan x < π / 2 :=
  (arctan_mem_Ioo x).2

theorem neg_pi_div_two_lt_arctan (x : ℝ) : -(π / 2) < arctan x :=
  (arctan_mem_Ioo x).1

theorem arctan_eq_arcsin (x : ℝ) : arctan x = arcsin (x / sqrt (1 + x ^ 2)) :=
  Eq.symm <| arcsin_eq_of_sin_eq (sin_arctan x) (mem_Icc_of_Ioo <| arctan_mem_Ioo x)

theorem arcsin_eq_arctan {x : ℝ} (h : x ∈ Ioo (-(1 : ℝ)) 1) : arcsin x = arctan (x / sqrt (1 - x ^ 2)) := by
  rw [arctan_eq_arcsin, div_pow, sq_sqrt, one_add_div, div_div, ← sqrt_mul, mul_div_cancel', sub_add_cancel, sqrt_one,
      div_one] <;>
    nlinarith [h.1, h.2]

@[simp]
theorem arctan_zero : arctan 0 = 0 := by
  simp [← arctan_eq_arcsin]

theorem arctan_eq_of_tan_eq {x y : ℝ} (h : tan x = y) (hx : x ∈ Ioo (-(π / 2)) (π / 2)) : arctan y = x :=
  inj_on_tan (arctan_mem_Ioo _) hx
    (by
      rw [tan_arctan, h])

@[simp]
theorem arctan_one : arctan 1 = π / 4 :=
  arctan_eq_of_tan_eq tan_pi_div_four <| by
    constructor <;> linarith [pi_pos]

@[simp]
theorem arctan_neg (x : ℝ) : arctan (-x) = -arctan x := by
  simp [← arctan_eq_arcsin, ← neg_div]

@[continuity]
theorem continuous_arctan : Continuous arctan :=
  continuous_subtype_coe.comp tanOrderIso.toHomeomorph.continuous_inv_fun

theorem continuous_at_arctan {x : ℝ} : ContinuousAt arctan x :=
  continuous_arctan.ContinuousAt

/-- `real.tan` as a `local_homeomorph` between `(-(π / 2), π / 2)` and the whole line. -/
def tanLocalHomeomorph : LocalHomeomorph ℝ ℝ where
  toFun := tan
  invFun := arctan
  Source := Ioo (-(π / 2)) (π / 2)
  Target := Univ
  map_source' := maps_to_univ _ _
  map_target' := fun y hy => arctan_mem_Ioo y
  left_inv' := fun x hx => arctan_tan hx.1 hx.2
  right_inv' := fun y hy => tan_arctan y
  open_source := is_open_Ioo
  open_target := is_open_univ
  continuous_to_fun := continuous_on_tan_Ioo
  continuous_inv_fun := continuous_arctan.ContinuousOn

@[simp]
theorem coe_tan_local_homeomorph : ⇑tan_local_homeomorph = tan :=
  rfl

@[simp]
theorem coe_tan_local_homeomorph_symm : ⇑tanLocalHomeomorph.symm = arctan :=
  rfl

end Real

