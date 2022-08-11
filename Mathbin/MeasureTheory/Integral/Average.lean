/-
Copyright (c) 2022 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import Mathbin.MeasureTheory.Integral.SetIntegral

/-!
# Integral average of a function

In this file we define `measure_theory.average μ f` (notation: `⨍ x, f x ∂μ`) to be the average
value of `f` with respect to measure `μ`. It is defined as `∫ x, f x ∂((μ univ)⁻¹ • μ)`, so it
is equal to zero if `f` is not integrable or if `μ` is an infinite measure. If `μ` is a probability
measure, then the average of any function is equal to its integral.

For the average on a set, we use `⨍ x in s, f x ∂μ` (notation for `⨍ x, f x ∂(μ.restrict s)`). For
average w.r.t. the volume, one can omit `∂volume`.

## Implementation notes

The average is defined as an integral over `(μ univ)⁻¹ • μ` so that all theorems about Bochner
integrals work for the average without modifications. For theorems that require integrability of a
function, we provide a convenience lemma `measure_theory.integrable.to_average`.

## Tags

integral, center mass, average value
-/


open MeasureTheory MeasureTheory.Measure Metric Set Filter TopologicalSpace Function

open TopologicalSpace BigOperators Ennreal Convex

variable {α E F : Type _} {m0 : MeasurableSpace α} [NormedGroup E] [NormedSpace ℝ E] [CompleteSpace E] [NormedGroup F]
  [NormedSpace ℝ F] [CompleteSpace F] {μ : Measureₓ α} {s : Set E}

/-!
### Average value of a function w.r.t. a measure

The average value of a function `f` w.r.t. a measure `μ` (notation: `⨍ x, f x ∂μ`) is defined as
`(μ univ).to_real⁻¹ • ∫ x, f x ∂μ`, so it is equal to zero if `f` is not integrable or if `μ` is an
infinite measure. If `μ` is a probability measure, then the average of any function is equal to its
integral.

-/


namespace MeasureTheory

variable (μ)

include m0

/-- Average value of a function `f` w.r.t. a measure `μ`, notation: `⨍ x, f x ∂μ`. It is defined as
`(μ univ).to_real⁻¹ • ∫ x, f x ∂μ`, so it is equal to zero if `f` is not integrable or if `μ` is an
infinite measure. If `μ` is a probability measure, then the average of any function is equal to its
integral.

For the average on a set, use `⨍ x in s, f x ∂μ` (defined as `⨍ x, f x ∂(μ.restrict s)`). For
average w.r.t. the volume, one can omit `∂volume`. -/
noncomputable def average (f : α → E) :=
  ∫ x, f x ∂(μ Univ)⁻¹ • μ

-- mathport name: «expr⨍ , ∂ »
notation3"⨍ "(...)", "r:(scoped f => f)" ∂"μ => average μ r

-- mathport name: «expr⨍ , »
notation3"⨍ "(...)", "r:(scoped f => average volume f) => r

-- mathport name: «expr⨍ in , ∂ »
notation3"⨍ "(...)" in "s", "r:(scoped f => f)" ∂"μ => average (Measure.restrict μ s) r

-- mathport name: «expr⨍ in , »
notation3"⨍ "(...)" in "s", "r:(scoped f => average Measure.restrict volume s f) => r

@[simp]
theorem average_zero : (⨍ x, (0 : E) ∂μ) = 0 := by
  rw [average, integral_zero]

@[simp]
theorem average_zero_measure (f : α → E) : (⨍ x, f x ∂(0 : Measure α)) = 0 := by
  rw [average, smul_zero, integral_zero_measure]

@[simp]
theorem average_neg (f : α → E) : (⨍ x, -f x ∂μ) = -⨍ x, f x ∂μ :=
  integral_neg f

theorem average_def (f : α → E) : (⨍ x, f x ∂μ) = ∫ x, f x ∂(μ Univ)⁻¹ • μ :=
  rfl

theorem average_def' (f : α → E) : (⨍ x, f x ∂μ) = (μ Univ).toReal⁻¹ • ∫ x, f x ∂μ := by
  rw [average_def, integral_smul_measure, Ennreal.to_real_inv]

theorem average_eq_integral [IsProbabilityMeasure μ] (f : α → E) : (⨍ x, f x ∂μ) = ∫ x, f x ∂μ := by
  rw [average, measure_univ, Ennreal.inv_one, one_smul]

@[simp]
theorem measure_smul_average [IsFiniteMeasure μ] (f : α → E) : ((μ Univ).toReal • ⨍ x, f x ∂μ) = ∫ x, f x ∂μ := by
  cases' eq_or_ne μ 0 with hμ hμ
  · rw [hμ, integral_zero_measure, average_zero_measure, smul_zero]
    
  · rw [average_def', smul_inv_smul₀]
    refine' (Ennreal.to_real_pos _ <| measure_ne_top _ _).ne'
    rwa [Ne.def, measure_univ_eq_zero]
    

theorem set_average_eq (f : α → E) (s : Set α) : (⨍ x in s, f x ∂μ) = (μ s).toReal⁻¹ • ∫ x in s, f x ∂μ := by
  rw [average_def', restrict_apply_univ]

variable {μ}

theorem average_congr {f g : α → E} (h : f =ᵐ[μ] g) : (⨍ x, f x ∂μ) = ⨍ x, g x ∂μ := by
  simp only [← average_def', ← integral_congr_ae h]

theorem average_add_measure [IsFiniteMeasure μ] {ν : Measure α} [IsFiniteMeasure ν] {f : α → E} (hμ : Integrable f μ)
    (hν : Integrable f ν) :
    (⨍ x, f x ∂μ + ν) =
      (((μ Univ).toReal / ((μ Univ).toReal + (ν Univ).toReal)) • ⨍ x, f x ∂μ) +
        ((ν Univ).toReal / ((μ Univ).toReal + (ν Univ).toReal)) • ⨍ x, f x ∂ν :=
  by
  simp only [← div_eq_inv_mul, ← mul_smul, ← measure_smul_average, smul_add, integral_add_measure hμ hν,
    Ennreal.to_real_add (measure_ne_top μ _) (measure_ne_top ν _)]
  rw [average_def', measure.add_apply]

theorem average_pair {f : α → E} {g : α → F} (hfi : Integrable f μ) (hgi : Integrable g μ) :
    (⨍ x, (f x, g x) ∂μ) = (⨍ x, f x ∂μ, ⨍ x, g x ∂μ) :=
  integral_pair hfi.to_average hgi.to_average

theorem measure_smul_set_average (f : α → E) {s : Set α} (h : μ s ≠ ∞) :
    ((μ s).toReal • ⨍ x in s, f x ∂μ) = ∫ x in s, f x ∂μ := by
  have := Fact.mk h.lt_top
  rw [← measure_smul_average, restrict_apply_univ]

theorem average_union {f : α → E} {s t : Set α} (hd : AeDisjoint μ s t) (ht : NullMeasurableSet t μ) (hsμ : μ s ≠ ∞)
    (htμ : μ t ≠ ∞) (hfs : IntegrableOn f s μ) (hft : IntegrableOn f t μ) :
    (⨍ x in s ∪ t, f x ∂μ) =
      (((μ s).toReal / ((μ s).toReal + (μ t).toReal)) • ⨍ x in s, f x ∂μ) +
        ((μ t).toReal / ((μ s).toReal + (μ t).toReal)) • ⨍ x in t, f x ∂μ :=
  by
  have := Fact.mk hsμ.lt_top
  have := Fact.mk htμ.lt_top
  rw [restrict_union₀ hd ht, average_add_measure hfs hft, restrict_apply_univ, restrict_apply_univ]

theorem average_union_mem_open_segment {f : α → E} {s t : Set α} (hd : AeDisjoint μ s t) (ht : NullMeasurableSet t μ)
    (hs₀ : μ s ≠ 0) (ht₀ : μ t ≠ 0) (hsμ : μ s ≠ ∞) (htμ : μ t ≠ ∞) (hfs : IntegrableOn f s μ)
    (hft : IntegrableOn f t μ) : (⨍ x in s ∪ t, f x ∂μ) ∈ OpenSegment ℝ (⨍ x in s, f x ∂μ) (⨍ x in t, f x ∂μ) := by
  replace hs₀ : 0 < (μ s).toReal
  exact Ennreal.to_real_pos hs₀ hsμ
  replace ht₀ : 0 < (μ t).toReal
  exact Ennreal.to_real_pos ht₀ htμ
  refine'
    mem_open_segment_iff_div.mpr ⟨(μ s).toReal, (μ t).toReal, hs₀, ht₀, (average_union hd ht hsμ htμ hfs hft).symm⟩

theorem average_union_mem_segment {f : α → E} {s t : Set α} (hd : AeDisjoint μ s t) (ht : NullMeasurableSet t μ)
    (hsμ : μ s ≠ ∞) (htμ : μ t ≠ ∞) (hfs : IntegrableOn f s μ) (hft : IntegrableOn f t μ) :
    (⨍ x in s ∪ t, f x ∂μ) ∈ [⨍ x in s, f x ∂μ -[ℝ] ⨍ x in t, f x ∂μ] := by
  by_cases' hse : μ s = 0
  · rw [← ae_eq_empty] at hse
    rw [restrict_congr_set (hse.union eventually_eq.rfl), empty_union]
    exact right_mem_segment _ _ _
    
  · refine'
      mem_segment_iff_div.mpr
        ⟨(μ s).toReal, (μ t).toReal, Ennreal.to_real_nonneg, Ennreal.to_real_nonneg, _,
          (average_union hd ht hsμ htμ hfs hft).symm⟩
    calc 0 < (μ s).toReal := Ennreal.to_real_pos hse hsμ _ ≤ _ := le_add_of_nonneg_right Ennreal.to_real_nonneg
    

theorem average_mem_open_segment_compl_self [IsFiniteMeasure μ] {f : α → E} {s : Set α} (hs : NullMeasurableSet s μ)
    (hs₀ : μ s ≠ 0) (hsc₀ : μ (sᶜ) ≠ 0) (hfi : Integrable f μ) :
    (⨍ x, f x ∂μ) ∈ OpenSegment ℝ (⨍ x in s, f x ∂μ) (⨍ x in sᶜ, f x ∂μ) := by
  simpa only [← union_compl_self, ← restrict_univ] using
    average_union_mem_open_segment ae_disjoint_compl_right hs.compl hs₀ hsc₀ (measure_ne_top _ _) (measure_ne_top _ _)
      hfi.integrable_on hfi.integrable_on

end MeasureTheory

