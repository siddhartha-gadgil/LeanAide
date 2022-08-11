/-
Copyright (c) 2020 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Scott Morrison
-/
import Mathbin.Topology.Instances.Real
import Mathbin.Topology.Algebra.Field
import Mathbin.Data.Set.Intervals.ProjIcc

/-!
# The unit interval, as a topological space

Use `open_locale unit_interval` to turn on the notation `I := set.Icc (0 : ℝ) (1 : ℝ)`.

We provide basic instances, as well as a custom tactic for discharging
`0 ≤ ↑x`, `0 ≤ 1 - ↑x`, `↑x ≤ 1`, and `1 - ↑x ≤ 1` when `x : I`.

-/


noncomputable section

open Classical TopologicalSpace Filter

open Set Int

/-! ### The unit interval -/


/-- The unit interval `[0,1]` in ℝ. -/
abbrev UnitInterval : Set ℝ :=
  Set.Icc 0 1

-- mathport name: «exprI»
localized [UnitInterval] notation "I" => UnitInterval

namespace UnitInterval

theorem zero_mem : (0 : ℝ) ∈ I :=
  ⟨le_rfl, zero_le_one⟩

theorem one_mem : (1 : ℝ) ∈ I :=
  ⟨zero_le_one, le_rfl⟩

theorem mul_mem {x y : ℝ} (hx : x ∈ I) (hy : y ∈ I) : x * y ∈ I :=
  ⟨mul_nonneg hx.1 hy.1, (mul_le_mul hx.2 hy.2 hy.1 zero_le_one).trans_eq <| one_mulₓ 1⟩

theorem div_mem {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : x ≤ y) : x / y ∈ I :=
  ⟨div_nonneg hx hy, div_le_one_of_le hxy hy⟩

theorem fract_mem (x : ℝ) : fract x ∈ I :=
  ⟨fract_nonneg _, (fract_lt_one _).le⟩

theorem mem_iff_one_sub_mem {t : ℝ} : t ∈ I ↔ 1 - t ∈ I := by
  rw [mem_Icc, mem_Icc]
  constructor <;> intro <;> constructor <;> linarith

instance hasZero : Zero I :=
  ⟨⟨0, zero_mem⟩⟩

@[simp, norm_cast]
theorem coe_zero : ((0 : I) : ℝ) = 0 :=
  rfl

@[simp]
theorem mk_zero (h : (0 : ℝ) ∈ Icc (0 : ℝ) 1) : (⟨0, h⟩ : I) = 0 :=
  rfl

@[simp, norm_cast]
theorem coe_eq_zero {x : I} : (x : ℝ) = 0 ↔ x = 0 := by
  symm
  exact Subtype.ext_iff

instance hasOne : One I :=
  ⟨⟨1, by
      constructor <;> norm_num⟩⟩

@[simp, norm_cast]
theorem coe_one : ((1 : I) : ℝ) = 1 :=
  rfl

theorem coe_ne_zero {x : I} : (x : ℝ) ≠ 0 ↔ x ≠ 0 :=
  not_iff_not.mpr coe_eq_zero

@[simp]
theorem mk_one (h : (1 : ℝ) ∈ Icc (0 : ℝ) 1) : (⟨1, h⟩ : I) = 1 :=
  rfl

@[simp, norm_cast]
theorem coe_eq_one {x : I} : (x : ℝ) = 1 ↔ x = 1 := by
  symm
  exact Subtype.ext_iff

theorem coe_ne_one {x : I} : (x : ℝ) ≠ 1 ↔ x ≠ 1 :=
  not_iff_not.mpr coe_eq_one

instance : Nonempty I :=
  ⟨0⟩

instance : Mul I :=
  ⟨fun x y => ⟨x * y, mul_mem x.2 y.2⟩⟩

@[simp, norm_cast]
theorem coe_mul {x y : I} : ((x * y : I) : ℝ) = x * y :=
  rfl

-- todo: we could set up a `linear_ordered_comm_monoid_with_zero I` instance
theorem mul_le_left {x y : I} : x * y ≤ x :=
  Subtype.coe_le_coe.mp <| (mul_le_mul_of_nonneg_left y.2.2 x.2.1).trans_eq <| mul_oneₓ x

theorem mul_le_right {x y : I} : x * y ≤ y :=
  Subtype.coe_le_coe.mp <| (mul_le_mul_of_nonneg_right x.2.2 y.2.1).trans_eq <| one_mulₓ y

/-- Unit interval central symmetry. -/
def symm : I → I := fun t => ⟨1 - t, mem_iff_one_sub_mem.mp t.Prop⟩

-- mathport name: «exprσ»
localized [UnitInterval] notation "σ" => UnitInterval.symm

@[simp]
theorem symm_zero : σ 0 = 1 :=
  Subtype.ext <| by
    simp [← symm]

@[simp]
theorem symm_one : σ 1 = 0 :=
  Subtype.ext <| by
    simp [← symm]

@[simp]
theorem symm_symm (x : I) : σ (σ x) = x :=
  Subtype.ext <| by
    simp [← symm]

@[simp]
theorem coe_symm_eq (x : I) : (σ x : ℝ) = 1 - x :=
  rfl

@[continuity]
theorem continuous_symm : Continuous σ := by
  continuity!

instance : ConnectedSpace I :=
  Subtype.connected_space ⟨nonempty_Icc.mpr zero_le_one, is_preconnected_Icc⟩

/-- Verify there is an instance for `compact_space I`. -/
example : CompactSpace I := by
  infer_instance

theorem nonneg (x : I) : 0 ≤ (x : ℝ) :=
  x.2.1

theorem one_minus_nonneg (x : I) : 0 ≤ 1 - (x : ℝ) := by
  simpa using x.2.2

theorem le_one (x : I) : (x : ℝ) ≤ 1 :=
  x.2.2

theorem one_minus_le_one (x : I) : 1 - (x : ℝ) ≤ 1 := by
  simpa using x.2.1

/-- like `unit_interval.nonneg`, but with the inequality in `I`. -/
theorem nonneg' {t : I} : 0 ≤ t :=
  t.2.1

/-- like `unit_interval.le_one`, but with the inequality in `I`. -/
theorem le_one' {t : I} : t ≤ 1 :=
  t.2.2

theorem mul_pos_mem_iff {a t : ℝ} (ha : 0 < a) : a * t ∈ I ↔ t ∈ Set.Icc (0 : ℝ) (1 / a) := by
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor
  · exact nonneg_of_mul_nonneg_right h₁ ha
    
  · rwa [le_div_iff ha, mul_comm]
    
  · exact mul_nonneg ha.le h₁
    
  · rwa [le_div_iff ha, mul_comm] at h₂
    

theorem two_mul_sub_one_mem_iff {t : ℝ} : 2 * t - 1 ∈ I ↔ t ∈ Set.Icc (1 / 2 : ℝ) 1 := by
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

end UnitInterval

@[simp]
theorem proj_Icc_eq_zero {x : ℝ} : projIcc (0 : ℝ) 1 zero_le_one x = 0 ↔ x ≤ 0 :=
  proj_Icc_eq_left zero_lt_one

@[simp]
theorem proj_Icc_eq_one {x : ℝ} : projIcc (0 : ℝ) 1 zero_le_one x = 1 ↔ 1 ≤ x :=
  proj_Icc_eq_right zero_lt_one

namespace Tactic.Interactive

-- ./././Mathport/Syntax/Translate/Basic.lean:1087:4: warning: unsupported (TODO): `[tacs]
-- ./././Mathport/Syntax/Translate/Basic.lean:1087:4: warning: unsupported (TODO): `[tacs]
-- ./././Mathport/Syntax/Translate/Basic.lean:1087:4: warning: unsupported (TODO): `[tacs]
-- ./././Mathport/Syntax/Translate/Basic.lean:1087:4: warning: unsupported (TODO): `[tacs]
/-- A tactic that solves `0 ≤ ↑x`, `0 ≤ 1 - ↑x`, `↑x ≤ 1`, and `1 - ↑x ≤ 1` for `x : I`. -/
unsafe def unit_interval : tactic Unit :=
  sorry <|> sorry <|> sorry <|> sorry

end Tactic.Interactive

section

variable {𝕜 : Type _} [LinearOrderedField 𝕜] [TopologicalSpace 𝕜] [TopologicalRing 𝕜]

/-- The image of `[0,1]` under the homeomorphism `λ x, a * x + b` is `[b, a+b]`.
-/
-- We only need the ordering on `𝕜` here to avoid talking about flipping the interval over.
-- At the end of the day I only care about `ℝ`, so I'm hesitant to put work into generalizing.
theorem affine_homeomorph_image_I (a b : 𝕜) (h : 0 < a) :
    affineHomeomorph a b h.Ne.symm '' Set.Icc 0 1 = Set.Icc b (a + b) := by
  simp [← h]

/-- The affine homeomorphism from a nontrivial interval `[a,b]` to `[0,1]`.
-/
def iccHomeoI (a b : 𝕜) (h : a < b) : Set.Icc a b ≃ₜ Set.Icc (0 : 𝕜) (1 : 𝕜) := by
  let e := Homeomorph.image (affineHomeomorph (b - a) a (sub_pos.mpr h).Ne.symm) (Set.Icc 0 1)
  refine' (e.trans _).symm
  apply Homeomorph.setCongr
  simp [← sub_pos.mpr h]

@[simp]
theorem Icc_homeo_I_apply_coe (a b : 𝕜) (h : a < b) (x : Set.Icc a b) : ((iccHomeoI a b h) x : 𝕜) = (x - a) / (b - a) :=
  rfl

@[simp]
theorem Icc_homeo_I_symm_apply_coe (a b : 𝕜) (h : a < b) (x : Set.Icc (0 : 𝕜) (1 : 𝕜)) :
    ((iccHomeoI a b h).symm x : 𝕜) = (b - a) * x + a :=
  rfl

end

