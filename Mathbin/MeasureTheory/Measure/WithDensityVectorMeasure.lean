/-
Copyright (c) 2021 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
import Mathbin.MeasureTheory.Measure.VectorMeasure
import Mathbin.MeasureTheory.Function.AeEqOfIntegral

/-!

# Vector measure defined by an integral

Given a measure `μ` and an integrable function `f : α → E`, we can define a vector measure `v` such
that for all measurable set `s`, `v i = ∫ x in s, f x ∂μ`. This definition is useful for
the Radon-Nikodym theorem for signed measures.

## Main definitions

* `measure_theory.measure.with_densityᵥ`: the vector measure formed by integrating a function `f`
  with respect to a measure `μ` on some set if `f` is integrable, and `0` otherwise.

-/


noncomputable section

open Classical MeasureTheory Nnreal Ennreal

variable {α β : Type _} {m : MeasurableSpace α}

namespace MeasureTheory

open TopologicalSpace

variable {μ ν : Measure α}

variable {E : Type _} [NormedGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Given a measure `μ` and an integrable function `f`, `μ.with_densityᵥ f` is
the vector measure which maps the set `s` to `∫ₛ f ∂μ`. -/
def Measure.withDensityᵥ {m : MeasurableSpace α} (μ : Measure α) (f : α → E) : VectorMeasure α E :=
  if hf : Integrable f μ then
    { measureOf' := fun s => if MeasurableSet s then ∫ x in s, f x ∂μ else 0,
      empty' := by
        simp ,
      not_measurable' := fun s hs => if_neg hs,
      m_Union' := fun s hs₁ hs₂ => by
        convert has_sum_integral_Union hs₁ hs₂ hf.integrable_on
        · ext n
          rw [if_pos (hs₁ n)]
          
        · rw [if_pos (MeasurableSet.Union hs₁)]
           }
  else 0

open Measureₓ

include m

variable {f g : α → E}

theorem with_densityᵥ_apply (hf : Integrable f μ) {s : Set α} (hs : MeasurableSet s) :
    μ.withDensityᵥ f s = ∫ x in s, f x ∂μ := by
  rw [with_densityᵥ, dif_pos hf]
  exact dif_pos hs

@[simp]
theorem with_densityᵥ_zero : μ.withDensityᵥ (0 : α → E) = 0 := by
  ext1 s hs
  erw [with_densityᵥ_apply (integrable_zero α E μ) hs]
  simp

@[simp]
theorem with_densityᵥ_neg : μ.withDensityᵥ (-f) = -μ.withDensityᵥ f := by
  by_cases' hf : integrable f μ
  · ext1 i hi
    rw [vector_measure.neg_apply, with_densityᵥ_apply hf hi, ← integral_neg, with_densityᵥ_apply hf.neg hi]
    rfl
    
  · rw [with_densityᵥ, with_densityᵥ, dif_neg hf, dif_neg, neg_zero]
    rwa [integrable_neg_iff]
    

theorem with_densityᵥ_neg' : (μ.withDensityᵥ fun x => -f x) = -μ.withDensityᵥ f :=
  with_densityᵥ_neg

@[simp]
theorem with_densityᵥ_add (hf : Integrable f μ) (hg : Integrable g μ) :
    μ.withDensityᵥ (f + g) = μ.withDensityᵥ f + μ.withDensityᵥ g := by
  ext1 i hi
  rw [with_densityᵥ_apply (hf.add hg) hi, vector_measure.add_apply, with_densityᵥ_apply hf hi,
    with_densityᵥ_apply hg hi]
  simp_rw [Pi.add_apply]
  rw [integral_add] <;> rw [← integrable_on_univ]
  · exact hf.integrable_on.restrict MeasurableSet.univ
    
  · exact hg.integrable_on.restrict MeasurableSet.univ
    

theorem with_densityᵥ_add' (hf : Integrable f μ) (hg : Integrable g μ) :
    (μ.withDensityᵥ fun x => f x + g x) = μ.withDensityᵥ f + μ.withDensityᵥ g :=
  with_densityᵥ_add hf hg

@[simp]
theorem with_densityᵥ_sub (hf : Integrable f μ) (hg : Integrable g μ) :
    μ.withDensityᵥ (f - g) = μ.withDensityᵥ f - μ.withDensityᵥ g := by
  rw [sub_eq_add_neg, sub_eq_add_neg, with_densityᵥ_add hf hg.neg, with_densityᵥ_neg]

theorem with_densityᵥ_sub' (hf : Integrable f μ) (hg : Integrable g μ) :
    (μ.withDensityᵥ fun x => f x - g x) = μ.withDensityᵥ f - μ.withDensityᵥ g :=
  with_densityᵥ_sub hf hg

@[simp]
theorem with_densityᵥ_smul {𝕜 : Type _} [NondiscreteNormedField 𝕜] [NormedSpace 𝕜 E] [SmulCommClass ℝ 𝕜 E] (f : α → E)
    (r : 𝕜) : μ.withDensityᵥ (r • f) = r • μ.withDensityᵥ f := by
  by_cases' hf : integrable f μ
  · ext1 i hi
    rw [with_densityᵥ_apply (hf.smul r) hi, vector_measure.smul_apply, with_densityᵥ_apply hf hi, ← integral_smul r f]
    rfl
    
  · by_cases' hr : r = 0
    · rw [hr, zero_smul, zero_smul, with_densityᵥ_zero]
      
    · rw [with_densityᵥ, with_densityᵥ, dif_neg hf, dif_neg, smul_zero]
      rwa [integrable_smul_iff hr f]
      
    

theorem with_densityᵥ_smul' {𝕜 : Type _} [NondiscreteNormedField 𝕜] [NormedSpace 𝕜 E] [SmulCommClass ℝ 𝕜 E] (f : α → E)
    (r : 𝕜) : (μ.withDensityᵥ fun x => r • f x) = r • μ.withDensityᵥ f :=
  with_densityᵥ_smul f r

theorem Measure.with_densityᵥ_absolutely_continuous (μ : Measure α) (f : α → ℝ) :
    μ.withDensityᵥ f ≪ᵥ μ.toEnnrealVectorMeasure := by
  by_cases' hf : integrable f μ
  · refine' vector_measure.absolutely_continuous.mk fun i hi₁ hi₂ => _
    rw [to_ennreal_vector_measure_apply_measurable hi₁] at hi₂
    rw [with_densityᵥ_apply hf hi₁, measure.restrict_zero_set hi₂, integral_zero_measure]
    
  · rw [with_densityᵥ, dif_neg hf]
    exact vector_measure.absolutely_continuous.zero _
    

/-- Having the same density implies the underlying functions are equal almost everywhere. -/
theorem Integrable.ae_eq_of_with_densityᵥ_eq {f g : α → E} (hf : Integrable f μ) (hg : Integrable g μ)
    (hfg : μ.withDensityᵥ f = μ.withDensityᵥ g) : f =ᵐ[μ] g := by
  refine' hf.ae_eq_of_forall_set_integral_eq f g hg fun i hi _ => _
  rw [← with_densityᵥ_apply hf hi, hfg, with_densityᵥ_apply hg hi]

theorem WithDensityᵥEq.congr_ae {f g : α → E} (h : f =ᵐ[μ] g) : μ.withDensityᵥ f = μ.withDensityᵥ g := by
  by_cases' hf : integrable f μ
  · ext i hi
    rw [with_densityᵥ_apply hf hi, with_densityᵥ_apply (hf.congr h) hi]
    exact integral_congr_ae (ae_restrict_of_ae h)
    
  · have hg : ¬integrable g μ := by
      intro hg
      exact hf (hg.congr h.symm)
    rw [with_densityᵥ, with_densityᵥ, dif_neg hf, dif_neg hg]
    

theorem Integrable.with_densityᵥ_eq_iff {f g : α → E} (hf : Integrable f μ) (hg : Integrable g μ) :
    μ.withDensityᵥ f = μ.withDensityᵥ g ↔ f =ᵐ[μ] g :=
  ⟨fun hfg => hf.ae_eq_of_with_densityᵥ_eq hg hfg, fun h => WithDensityᵥEq.congr_ae h⟩

section SignedMeasure

theorem with_densityᵥ_to_real {f : α → ℝ≥0∞} (hfm : AeMeasurable f μ) (hf : (∫⁻ x, f x ∂μ) ≠ ∞) :
    (μ.withDensityᵥ fun x => (f x).toReal) =
      @toSignedMeasure α _ (μ.withDensity f) (is_finite_measure_with_density hf) :=
  by
  have hfi := integrable_to_real_of_lintegral_ne_top hfm hf
  ext i hi
  rw [with_densityᵥ_apply hfi hi, to_signed_measure_apply_measurable hi, with_density_apply _ hi,
    integral_to_real hfm.restrict]
  refine' ae_lt_top' hfm.restrict (ne_top_of_le_ne_top hf _)
  conv_rhs => rw [← set_lintegral_univ]
  exact lintegral_mono_set (Set.subset_univ _)

theorem with_densityᵥ_eq_with_density_pos_part_sub_with_density_neg_part {f : α → ℝ} (hfi : Integrable f μ) :
    μ.withDensityᵥ f =
      @toSignedMeasure α _ (μ.withDensity fun x => Ennreal.ofReal <| f x)
          (is_finite_measure_with_density_of_real hfi.2) -
        @toSignedMeasure α _ (μ.withDensity fun x => Ennreal.ofReal <| -f x)
          (is_finite_measure_with_density_of_real hfi.neg.2) :=
  by
  ext i hi
  rw [with_densityᵥ_apply hfi hi, integral_eq_lintegral_pos_part_sub_lintegral_neg_part hfi.integrable_on,
    vector_measure.sub_apply, to_signed_measure_apply_measurable hi, to_signed_measure_apply_measurable hi,
    with_density_apply _ hi, with_density_apply _ hi]

theorem Integrable.with_densityᵥ_trim_eq_integral {m m0 : MeasurableSpace α} {μ : Measure α} (hm : m ≤ m0) {f : α → ℝ}
    (hf : Integrable f μ) {i : Set α} (hi : measurable_set[m] i) : (μ.withDensityᵥ f).trim hm i = ∫ x in i, f x ∂μ := by
  rw [vector_measure.trim_measurable_set_eq hm hi, with_densityᵥ_apply hf (hm _ hi)]

theorem Integrable.with_densityᵥ_trim_absolutely_continuous {m m0 : MeasurableSpace α} {μ : Measure α} (hm : m ≤ m0)
    (hfi : Integrable f μ) : (μ.withDensityᵥ f).trim hm ≪ᵥ (μ.trim hm).toEnnrealVectorMeasure := by
  refine' vector_measure.absolutely_continuous.mk fun j hj₁ hj₂ => _
  rw [measure.to_ennreal_vector_measure_apply_measurable hj₁, trim_measurable_set_eq hm hj₁] at hj₂
  rw [vector_measure.trim_measurable_set_eq hm hj₁, with_densityᵥ_apply hfi (hm _ hj₁)]
  simp only [← measure.restrict_eq_zero.mpr hj₂, ← integral_zero_measure]

end SignedMeasure

end MeasureTheory

