/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Benjamin Davidson
-/
import Mathbin.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathbin.Topology.Algebra.Order.ProjIcc

/-!
# Inverse trigonometric functions.

See also `analysis.special_functions.trigonometric.arctan` for the inverse tan function.
(This is delayed as it is easier to set up after developing complex trigonometric functions.)

Basic inequalities on trigonometric functions.
-/


noncomputable section

open Classical TopologicalSpace Filter

open Set Filter

open Real

namespace Real

/-- Inverse of the `sin` function, returns values in the range `-π / 2 ≤ arcsin x ≤ π / 2`.
It defaults to `-π / 2` on `(-∞, -1)` and to `π / 2` to `(1, ∞)`. -/
@[pp_nodot]
noncomputable def arcsin : ℝ → ℝ :=
  coe ∘ iccExtend (neg_le_self zero_le_one) sinOrderIso.symm

theorem arcsin_mem_Icc (x : ℝ) : arcsin x ∈ Icc (-(π / 2)) (π / 2) :=
  Subtype.coe_prop _

@[simp]
theorem range_arcsin : Range arcsin = Icc (-(π / 2)) (π / 2) := by
  rw [arcsin, range_comp coe]
  simp [← Icc]

theorem arcsin_le_pi_div_two (x : ℝ) : arcsin x ≤ π / 2 :=
  (arcsin_mem_Icc x).2

theorem neg_pi_div_two_le_arcsin (x : ℝ) : -(π / 2) ≤ arcsin x :=
  (arcsin_mem_Icc x).1

theorem arcsin_proj_Icc (x : ℝ) : arcsin (projIcc (-1) 1 (neg_le_self zero_le_one) x) = arcsin x := by
  rw [arcsin, Function.comp_app, Icc_extend_coe, Function.comp_app, Icc_extend]

theorem sin_arcsin' {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) : sin (arcsin x) = x := by
  simpa [← arcsin, ← Icc_extend_of_mem _ _ hx, -OrderIso.apply_symm_apply] using
    Subtype.ext_iff.1 (sin_order_iso.apply_symm_apply ⟨x, hx⟩)

theorem sin_arcsin {x : ℝ} (hx₁ : -1 ≤ x) (hx₂ : x ≤ 1) : sin (arcsin x) = x :=
  sin_arcsin' ⟨hx₁, hx₂⟩

theorem arcsin_sin' {x : ℝ} (hx : x ∈ Icc (-(π / 2)) (π / 2)) : arcsin (sin x) = x :=
  inj_on_sin (arcsin_mem_Icc _) hx <| by
    rw [sin_arcsin (neg_one_le_sin _) (sin_le_one _)]

theorem arcsin_sin {x : ℝ} (hx₁ : -(π / 2) ≤ x) (hx₂ : x ≤ π / 2) : arcsin (sin x) = x :=
  arcsin_sin' ⟨hx₁, hx₂⟩

theorem strict_mono_on_arcsin : StrictMonoOn arcsin (Icc (-1) 1) :=
  (Subtype.strict_mono_coe _).comp_strict_mono_on <| sinOrderIso.symm.StrictMono.strict_mono_on_Icc_extend _

theorem monotone_arcsin : Monotone arcsin :=
  (Subtype.mono_coe _).comp <| sinOrderIso.symm.Monotone.iccExtend _

theorem inj_on_arcsin : InjOn arcsin (Icc (-1) 1) :=
  strict_mono_on_arcsin.InjOn

theorem arcsin_inj {x y : ℝ} (hx₁ : -1 ≤ x) (hx₂ : x ≤ 1) (hy₁ : -1 ≤ y) (hy₂ : y ≤ 1) : arcsin x = arcsin y ↔ x = y :=
  inj_on_arcsin.eq_iff ⟨hx₁, hx₂⟩ ⟨hy₁, hy₂⟩

@[continuity]
theorem continuous_arcsin : Continuous arcsin :=
  continuous_subtype_coe.comp sinOrderIso.symm.Continuous.Icc_extend'

theorem continuous_at_arcsin {x : ℝ} : ContinuousAt arcsin x :=
  continuous_arcsin.ContinuousAt

theorem arcsin_eq_of_sin_eq {x y : ℝ} (h₁ : sin x = y) (h₂ : x ∈ Icc (-(π / 2)) (π / 2)) : arcsin y = x := by
  subst y
  exact inj_on_sin (arcsin_mem_Icc _) h₂ (sin_arcsin' (sin_mem_Icc x))

@[simp]
theorem arcsin_zero : arcsin 0 = 0 :=
  arcsin_eq_of_sin_eq sin_zero ⟨neg_nonpos.2 pi_div_two_pos.le, pi_div_two_pos.le⟩

@[simp]
theorem arcsin_one : arcsin 1 = π / 2 :=
  arcsin_eq_of_sin_eq sin_pi_div_two <| right_mem_Icc.2 (neg_le_self pi_div_two_pos.le)

theorem arcsin_of_one_le {x : ℝ} (hx : 1 ≤ x) : arcsin x = π / 2 := by
  rw [← arcsin_proj_Icc, proj_Icc_of_right_le _ hx, Subtype.coe_mk, arcsin_one]

theorem arcsin_neg_one : arcsin (-1) = -(π / 2) :=
  arcsin_eq_of_sin_eq
      (by
        rw [sin_neg, sin_pi_div_two]) <|
    left_mem_Icc.2 (neg_le_self pi_div_two_pos.le)

theorem arcsin_of_le_neg_one {x : ℝ} (hx : x ≤ -1) : arcsin x = -(π / 2) := by
  rw [← arcsin_proj_Icc, proj_Icc_of_le_left _ hx, Subtype.coe_mk, arcsin_neg_one]

@[simp]
theorem arcsin_neg (x : ℝ) : arcsin (-x) = -arcsin x := by
  cases' le_totalₓ x (-1) with hx₁ hx₁
  · rw [arcsin_of_le_neg_one hx₁, neg_negₓ, arcsin_of_one_le (le_neg.2 hx₁)]
    
  cases' le_totalₓ 1 x with hx₂ hx₂
  · rw [arcsin_of_one_le hx₂, arcsin_of_le_neg_one (neg_le_neg hx₂)]
    
  refine' arcsin_eq_of_sin_eq _ _
  · rw [sin_neg, sin_arcsin hx₁ hx₂]
    
  · exact ⟨neg_le_neg (arcsin_le_pi_div_two _), neg_le.2 (neg_pi_div_two_le_arcsin _)⟩
    

theorem arcsin_le_iff_le_sin {x y : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) (hy : y ∈ Icc (-(π / 2)) (π / 2)) :
    arcsin x ≤ y ↔ x ≤ sin y := by
  rw [← arcsin_sin' hy, strict_mono_on_arcsin.le_iff_le hx (sin_mem_Icc _), arcsin_sin' hy]

theorem arcsin_le_iff_le_sin' {x y : ℝ} (hy : y ∈ Ico (-(π / 2)) (π / 2)) : arcsin x ≤ y ↔ x ≤ sin y := by
  cases' le_totalₓ x (-1) with hx₁ hx₁
  · simp [← arcsin_of_le_neg_one hx₁, ← hy.1, ← hx₁.trans (neg_one_le_sin _)]
    
  cases' lt_or_leₓ 1 x with hx₂ hx₂
  · simp [← arcsin_of_one_le hx₂.le, ← hy.2.not_le, ← (sin_le_one y).trans_lt hx₂]
    
  exact arcsin_le_iff_le_sin ⟨hx₁, hx₂⟩ (mem_Icc_of_Ico hy)

theorem le_arcsin_iff_sin_le {x y : ℝ} (hx : x ∈ Icc (-(π / 2)) (π / 2)) (hy : y ∈ Icc (-1 : ℝ) 1) :
    x ≤ arcsin y ↔ sin x ≤ y := by
  rw [← neg_le_neg_iff, ← arcsin_neg,
    arcsin_le_iff_le_sin ⟨neg_le_neg hy.2, neg_le.2 hy.1⟩ ⟨neg_le_neg hx.2, neg_le.2 hx.1⟩, sin_neg, neg_le_neg_iff]

theorem le_arcsin_iff_sin_le' {x y : ℝ} (hx : x ∈ Ioc (-(π / 2)) (π / 2)) : x ≤ arcsin y ↔ sin x ≤ y := by
  rw [← neg_le_neg_iff, ← arcsin_neg, arcsin_le_iff_le_sin' ⟨neg_le_neg hx.2, neg_lt.2 hx.1⟩, sin_neg, neg_le_neg_iff]

theorem arcsin_lt_iff_lt_sin {x y : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) (hy : y ∈ Icc (-(π / 2)) (π / 2)) :
    arcsin x < y ↔ x < sin y :=
  not_leₓ.symm.trans <| (not_congr <| le_arcsin_iff_sin_le hy hx).trans not_leₓ

theorem arcsin_lt_iff_lt_sin' {x y : ℝ} (hy : y ∈ Ioc (-(π / 2)) (π / 2)) : arcsin x < y ↔ x < sin y :=
  not_leₓ.symm.trans <| (not_congr <| le_arcsin_iff_sin_le' hy).trans not_leₓ

theorem lt_arcsin_iff_sin_lt {x y : ℝ} (hx : x ∈ Icc (-(π / 2)) (π / 2)) (hy : y ∈ Icc (-1 : ℝ) 1) :
    x < arcsin y ↔ sin x < y :=
  not_leₓ.symm.trans <| (not_congr <| arcsin_le_iff_le_sin hy hx).trans not_leₓ

theorem lt_arcsin_iff_sin_lt' {x y : ℝ} (hx : x ∈ Ico (-(π / 2)) (π / 2)) : x < arcsin y ↔ sin x < y :=
  not_leₓ.symm.trans <| (not_congr <| arcsin_le_iff_le_sin' hx).trans not_leₓ

theorem arcsin_eq_iff_eq_sin {x y : ℝ} (hy : y ∈ Ioo (-(π / 2)) (π / 2)) : arcsin x = y ↔ x = sin y := by
  simp only [← le_antisymm_iffₓ, ← arcsin_le_iff_le_sin' (mem_Ico_of_Ioo hy), ←
    le_arcsin_iff_sin_le' (mem_Ioc_of_Ioo hy)]

@[simp]
theorem arcsin_nonneg {x : ℝ} : 0 ≤ arcsin x ↔ 0 ≤ x :=
  (le_arcsin_iff_sin_le' ⟨neg_lt_zero.2 pi_div_two_pos, pi_div_two_pos.le⟩).trans <| by
    rw [sin_zero]

@[simp]
theorem arcsin_nonpos {x : ℝ} : arcsin x ≤ 0 ↔ x ≤ 0 :=
  neg_nonneg.symm.trans <| arcsin_neg x ▸ arcsin_nonneg.trans neg_nonneg

@[simp]
theorem arcsin_eq_zero_iff {x : ℝ} : arcsin x = 0 ↔ x = 0 := by
  simp [← le_antisymm_iffₓ]

@[simp]
theorem zero_eq_arcsin_iff {x} : 0 = arcsin x ↔ x = 0 :=
  eq_comm.trans arcsin_eq_zero_iff

@[simp]
theorem arcsin_pos {x : ℝ} : 0 < arcsin x ↔ 0 < x :=
  lt_iff_lt_of_le_iff_le arcsin_nonpos

@[simp]
theorem arcsin_lt_zero {x : ℝ} : arcsin x < 0 ↔ x < 0 :=
  lt_iff_lt_of_le_iff_le arcsin_nonneg

@[simp]
theorem arcsin_lt_pi_div_two {x : ℝ} : arcsin x < π / 2 ↔ x < 1 :=
  (arcsin_lt_iff_lt_sin' (right_mem_Ioc.2 <| neg_lt_self pi_div_two_pos)).trans <| by
    rw [sin_pi_div_two]

@[simp]
theorem neg_pi_div_two_lt_arcsin {x : ℝ} : -(π / 2) < arcsin x ↔ -1 < x :=
  (lt_arcsin_iff_sin_lt' <| left_mem_Ico.2 <| neg_lt_self pi_div_two_pos).trans <| by
    rw [sin_neg, sin_pi_div_two]

@[simp]
theorem arcsin_eq_pi_div_two {x : ℝ} : arcsin x = π / 2 ↔ 1 ≤ x :=
  ⟨fun h => not_ltₓ.1 fun h' => (arcsin_lt_pi_div_two.2 h').Ne h, arcsin_of_one_le⟩

@[simp]
theorem pi_div_two_eq_arcsin {x} : π / 2 = arcsin x ↔ 1 ≤ x :=
  eq_comm.trans arcsin_eq_pi_div_two

@[simp]
theorem pi_div_two_le_arcsin {x} : π / 2 ≤ arcsin x ↔ 1 ≤ x :=
  (arcsin_le_pi_div_two x).le_iff_eq.trans pi_div_two_eq_arcsin

@[simp]
theorem arcsin_eq_neg_pi_div_two {x : ℝ} : arcsin x = -(π / 2) ↔ x ≤ -1 :=
  ⟨fun h => not_ltₓ.1 fun h' => (neg_pi_div_two_lt_arcsin.2 h').ne' h, arcsin_of_le_neg_one⟩

@[simp]
theorem neg_pi_div_two_eq_arcsin {x} : -(π / 2) = arcsin x ↔ x ≤ -1 :=
  eq_comm.trans arcsin_eq_neg_pi_div_two

@[simp]
theorem arcsin_le_neg_pi_div_two {x} : arcsin x ≤ -(π / 2) ↔ x ≤ -1 :=
  (neg_pi_div_two_le_arcsin x).le_iff_eq.trans arcsin_eq_neg_pi_div_two

@[simp]
theorem pi_div_four_le_arcsin {x} : π / 4 ≤ arcsin x ↔ sqrt 2 / 2 ≤ x := by
  rw [← sin_pi_div_four, le_arcsin_iff_sin_le']
  have := pi_pos
  constructor <;> linarith

theorem maps_to_sin_Ioo : MapsTo sin (Ioo (-(π / 2)) (π / 2)) (Ioo (-1) 1) := fun x h => by
  rwa [mem_Ioo, ← arcsin_lt_pi_div_two, ← neg_pi_div_two_lt_arcsin, arcsin_sin h.1.le h.2.le]

/-- `real.sin` as a `local_homeomorph` between `(-π / 2, π / 2)` and `(-1, 1)`. -/
@[simp]
def sinLocalHomeomorph : LocalHomeomorph ℝ ℝ where
  toFun := sin
  invFun := arcsin
  Source := Ioo (-(π / 2)) (π / 2)
  Target := Ioo (-1) 1
  map_source' := maps_to_sin_Ioo
  map_target' := fun y hy => ⟨neg_pi_div_two_lt_arcsin.2 hy.1, arcsin_lt_pi_div_two.2 hy.2⟩
  left_inv' := fun x hx => arcsin_sin hx.1.le hx.2.le
  right_inv' := fun y hy => sin_arcsin hy.1.le hy.2.le
  open_source := is_open_Ioo
  open_target := is_open_Ioo
  continuous_to_fun := continuous_sin.ContinuousOn
  continuous_inv_fun := continuous_arcsin.ContinuousOn

theorem cos_arcsin_nonneg (x : ℝ) : 0 ≤ cos (arcsin x) :=
  cos_nonneg_of_mem_Icc ⟨neg_pi_div_two_le_arcsin _, arcsin_le_pi_div_two _⟩

theorem cos_arcsin {x : ℝ} (hx₁ : -1 ≤ x) (hx₂ : x ≤ 1) : cos (arcsin x) = sqrt (1 - x ^ 2) := by
  have : sin (arcsin x) ^ 2 + cos (arcsin x) ^ 2 = 1 := sin_sq_add_cos_sq (arcsin x)
  rw [← eq_sub_iff_add_eq', ← sqrt_inj (sq_nonneg _) (sub_nonneg.2 (sin_sq_le_one (arcsin x))), sq,
    sqrt_mul_self (cos_arcsin_nonneg _)] at this
  rw [this, sin_arcsin hx₁ hx₂]

/-- Inverse of the `cos` function, returns values in the range `0 ≤ arccos x` and `arccos x ≤ π`.
  If the argument is not between `-1` and `1` it defaults to `π / 2` -/
@[pp_nodot]
noncomputable def arccos (x : ℝ) : ℝ :=
  π / 2 - arcsin x

theorem arccos_eq_pi_div_two_sub_arcsin (x : ℝ) : arccos x = π / 2 - arcsin x :=
  rfl

theorem arcsin_eq_pi_div_two_sub_arccos (x : ℝ) : arcsin x = π / 2 - arccos x := by
  simp [← arccos]

theorem arccos_le_pi (x : ℝ) : arccos x ≤ π := by
  unfold arccos <;> linarith [neg_pi_div_two_le_arcsin x]

theorem arccos_nonneg (x : ℝ) : 0 ≤ arccos x := by
  unfold arccos <;> linarith [arcsin_le_pi_div_two x]

theorem cos_arccos {x : ℝ} (hx₁ : -1 ≤ x) (hx₂ : x ≤ 1) : cos (arccos x) = x := by
  rw [arccos, cos_pi_div_two_sub, sin_arcsin hx₁ hx₂]

theorem arccos_cos {x : ℝ} (hx₁ : 0 ≤ x) (hx₂ : x ≤ π) : arccos (cos x) = x := by
  rw [arccos, ← sin_pi_div_two_sub, arcsin_sin] <;> simp [← sub_eq_add_neg] <;> linarith

theorem strict_anti_on_arccos : StrictAntiOn arccos (Icc (-1) 1) := fun x hx y hy h =>
  sub_lt_sub_left (strict_mono_on_arcsin hx hy h) _

theorem arccos_inj_on : InjOn arccos (Icc (-1) 1) :=
  strict_anti_on_arccos.InjOn

theorem arccos_inj {x y : ℝ} (hx₁ : -1 ≤ x) (hx₂ : x ≤ 1) (hy₁ : -1 ≤ y) (hy₂ : y ≤ 1) : arccos x = arccos y ↔ x = y :=
  arccos_inj_on.eq_iff ⟨hx₁, hx₂⟩ ⟨hy₁, hy₂⟩

@[simp]
theorem arccos_zero : arccos 0 = π / 2 := by
  simp [← arccos]

@[simp]
theorem arccos_one : arccos 1 = 0 := by
  simp [← arccos]

@[simp]
theorem arccos_neg_one : arccos (-1) = π := by
  simp [← arccos, ← add_halves]

@[simp]
theorem arccos_eq_zero {x} : arccos x = 0 ↔ 1 ≤ x := by
  simp [← arccos, ← sub_eq_zero]

@[simp]
theorem arccos_eq_pi_div_two {x} : arccos x = π / 2 ↔ x = 0 := by
  simp [← arccos]

@[simp]
theorem arccos_eq_pi {x} : arccos x = π ↔ x ≤ -1 := by
  rw [arccos, sub_eq_iff_eq_add, ← sub_eq_iff_eq_add', div_two_sub_self, neg_pi_div_two_eq_arcsin]

theorem arccos_neg (x : ℝ) : arccos (-x) = π - arccos x := by
  rw [← add_halves π, arccos, arcsin_neg, arccos, add_sub_assoc, sub_sub_self, sub_neg_eq_add]

theorem sin_arccos {x : ℝ} (hx₁ : -1 ≤ x) (hx₂ : x ≤ 1) : sin (arccos x) = sqrt (1 - x ^ 2) := by
  rw [arccos_eq_pi_div_two_sub_arcsin, sin_pi_div_two_sub, cos_arcsin hx₁ hx₂]

@[simp]
theorem arccos_le_pi_div_two {x} : arccos x ≤ π / 2 ↔ 0 ≤ x := by
  simp [← arccos]

@[simp]
theorem arccos_le_pi_div_four {x} : arccos x ≤ π / 4 ↔ sqrt 2 / 2 ≤ x := by
  rw [arccos, ← pi_div_four_le_arcsin]
  constructor <;>
    · intro
      linarith
      

@[continuity]
theorem continuous_arccos : Continuous arccos :=
  continuous_const.sub continuous_arcsin

end Real

