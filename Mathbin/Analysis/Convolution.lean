/-
Copyright (c) 2022 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import Mathbin.MeasureTheory.Group.Integration
import Mathbin.MeasureTheory.Group.Prod
import Mathbin.MeasureTheory.Function.LocallyIntegrable
import Mathbin.Analysis.Calculus.SpecificFunctions
import Mathbin.Analysis.Calculus.ParametricIntegral

/-!
# Convolution of functions

This file defines the convolution on two functions, i.e. `x ↦ ∫ f(t)g(x - t) ∂t`.
In the general case, these functions can be vector-valued, and have an arbitrary (additive)
group as domain. We use a continuous bilinear operation `L` on these function values as
"multiplication". The domain must be equipped with a Haar measure `μ`
(though many individual results have weaker conditions on `μ`).

For many applications we can take `L = lsmul ℝ ℝ` or `L = lmul ℝ ℝ`.

We also define `convolution_exists` and `convolution_exists_at` to state that the convolution is
well-defined (everywhere or at a single point). These conditions are needed for pointwise
computations (e.g. `convolution_exists_at.distrib_add`), but are generally not stong enough for any
local (or global) properties of the convolution. For this we need stronger assumptions on `f`
and/or `g`, and generally if we impose stronger conditions on one of the functions, we can impose
weaker conditions on the other.
We have proven many of the properties of the convolution assuming one of these functions
has compact support (in which case the other function only needs to be locally integrable).
We still need to prove the properties for other pairs of conditions (e.g. both functions are
rapidly decreasing)

# Design Decisions

We use a bilinear map `L` to "multiply" the two functions in the integrand.
This generality has several advantages

* This allows us to compute the total derivative of the convolution, in case the functions are
  multivariate. The total derivative is again a convolution, but where the codomains of the
  functions can be higher-dimensional. See `has_compact_support.has_fderiv_at_convolution_right`.
* This allows us to use `@[to_additive]` everywhere (which would not be possible if we would use
  `mul`/`smul` in the integral, since `@[to_additive]` will incorrectly also try to additivize
  those definitions).
* We need to support the case where at least one of the functions is vector-valued, but if we use
  `smul` to multiply the functions, that would be an asymmetric definition.

# Main Definitions
* `convolution f g L μ x = (f ⋆[L, μ] g) x = ∫ t, L (f t) (g (x - t)) ∂μ` is the convolution of
  `f` and `g` w.r.t. the continuous bilinear map `L` and measure `μ`.
* `convolution_exists_at f g x L μ` states that the convolution `(f ⋆[L, μ] g) x` is well-defined
  (i.e. the integral exists).
* `convolution_exists f g L μ` states that the convolution `f ⋆[L, μ] g` is well-defined at each
  point.

# Main Results
* `has_compact_support.has_fderiv_at_convolution_right` and
  `has_compact_support.has_fderiv_at_convolution_left`: we can compute the total derivative
  of the convolution as a convolution with the total derivative of the right (left) function.
* `has_compact_support.cont_diff_convolution_right` and
  `has_compact_support.cont_diff_convolution_left`: the convolution is `𝒞ⁿ` if one of the functions
  is `𝒞ⁿ` with compact support and the other function in locally integrable.
* `convolution_tendsto_right`: Given a sequence of nonnegative normalized functions whose support
  tends to a small neighborhood around `0`, the convolution tends to the right argument.
  This is specialized to bump functions in `cont_diff_bump_of_inner.convolution_tendsto_right`.

# Notation
The following notations are localized in the locale `convolution`:
* `f ⋆[L, μ] g` for the convolution. Note: you have to use parentheses to apply the convolution
  to an argument: `(f ⋆[L, μ] g) x`.
* `f ⋆[L] g := f ⋆[L, volume] g`
* `f ⋆ g := f ⋆[lsmul ℝ ℝ] g`

# To do
* Prove properties about the convolution if both functions are rapidly decreasing.
* Use `@[to_additive]` everywhere
-/


open Set Function Filter MeasureTheory MeasureTheory.Measure TopologicalSpace

open ContinuousLinearMap Metric

open Pointwise TopologicalSpace Nnreal

variable {𝕜 G E E' E'' F F' F'' : Type _}

variable [NormedGroup E] [NormedGroup E'] [NormedGroup E''] [NormedGroup F]

variable {f f' : G → E} {g g' : G → E'} {x x' : G} {y y' : E}

section NondiscreteNormedField

variable [NondiscreteNormedField 𝕜]

variable [NormedSpace 𝕜 E] [NormedSpace 𝕜 E'] [NormedSpace 𝕜 E''] [NormedSpace 𝕜 F]

variable (L : E →L[𝕜] E' →L[𝕜] F)

section NoMeasurability

variable [AddGroupₓ G] [TopologicalSpace G]

theorem HasCompactSupport.convolution_integrand_bound_right (hcg : HasCompactSupport g) (hg : Continuous g) {x t : G}
    {s : Set G} (hx : x ∈ s) :
    ∥L (f t) (g (x - t))∥ ≤ (-Tsupport g + s).indicator (fun t => ∥L∥ * ∥f t∥ * ⨆ i, ∥g i∥) t := by
  refine' le_indicator (fun t ht => _) (fun t ht => _) t
  · refine' (L.le_op_norm₂ _ _).trans _
    exact
      mul_le_mul_of_nonneg_left (le_csupr (hg.norm.bdd_above_range_of_has_compact_support hcg.norm) <| x - t)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    
  · have : x - t ∉ support g := by
      refine' mt (fun hxt => _) ht
      refine' ⟨_, _, set.neg_mem_neg.mpr (subset_closure hxt), hx, _⟩
      rw [neg_sub, sub_add_cancel]
    rw [nmem_support.mp this, (L _).map_zero, norm_zero]
    

theorem Continuous.convolution_integrand_fst [HasContinuousSub G] (hg : Continuous g) (t : G) :
    Continuous fun x => L (f t) (g (x - t)) :=
  L.continuous₂.comp₂ continuous_const <| hg.comp <| continuous_id.sub continuous_const

theorem HasCompactSupport.convolution_integrand_bound_left (hcf : HasCompactSupport f) (hf : Continuous f) {x t : G}
    {s : Set G} (hx : x ∈ s) :
    ∥L (f (x - t)) (g t)∥ ≤ (-Tsupport f + s).indicator (fun t => (∥L∥ * ⨆ i, ∥f i∥) * ∥g t∥) t := by
  convert hcf.convolution_integrand_bound_right L.flip hf hx
  simp_rw [L.op_norm_flip, mul_right_commₓ]

end NoMeasurability

section Measurability

variable [MeasurableSpace G] {μ : Measureₓ G}

/-- The convolution of `f` and `g` exists at `x` when the function `t ↦ L (f t) (g (x - t))` is
integrable. There are various conditions on `f` and `g` to prove this. -/
def ConvolutionExistsAt [Sub G] (f : G → E) (g : G → E') (x : G) (L : E →L[𝕜] E' →L[𝕜] F)
    (μ : Measureₓ G := by
      run_tac
        volume_tac) :
    Prop :=
  Integrable (fun t => L (f t) (g (x - t))) μ

/-- The convolution of `f` and `g` exists when the function `t ↦ L (f t) (g (x - t))` is integrable
for all `x : G`. There are various conditions on `f` and `g` to prove this. -/
def ConvolutionExists [Sub G] (f : G → E) (g : G → E') (L : E →L[𝕜] E' →L[𝕜] F)
    (μ : Measureₓ G := by
      run_tac
        volume_tac) :
    Prop :=
  ∀ x : G, ConvolutionExistsAt f g x L μ

section ConvolutionExists

variable {L}

theorem ConvolutionExistsAt.integrable [Sub G] {x : G} (h : ConvolutionExistsAt f g x L μ) :
    Integrable (fun t => L (f t) (g (x - t))) μ :=
  h

variable (L)

section Groupₓ

variable [AddGroupₓ G]

variable [HasMeasurableAdd₂ G] [HasMeasurableNeg G]

theorem MeasureTheory.AeStronglyMeasurable.convolution_integrand' [SigmaFinite μ] (hf : AeStronglyMeasurable f μ)
    (hg : AeStronglyMeasurable g <| map (fun p : G × G => p.1 - p.2) (μ.Prod μ)) :
    AeStronglyMeasurable (fun p : G × G => L (f p.2) (g (p.1 - p.2))) (μ.Prod μ) :=
  L.ae_strongly_measurable_comp₂ hf.snd <| hg.comp_measurable <| measurable_fst.sub measurable_snd

theorem MeasureTheory.AeStronglyMeasurable.convolution_integrand_snd' (hf : AeStronglyMeasurable f μ) {x : G}
    (hg : AeStronglyMeasurable g <| map (fun t => x - t) μ) : AeStronglyMeasurable (fun t => L (f t) (g (x - t))) μ :=
  L.ae_strongly_measurable_comp₂ hf <| hg.comp_measurable <| measurable_id.const_sub x

theorem MeasureTheory.AeStronglyMeasurable.convolution_integrand_swap_snd' {x : G}
    (hf : AeStronglyMeasurable f <| map (fun t => x - t) μ) (hg : AeStronglyMeasurable g μ) :
    AeStronglyMeasurable (fun t => L (f (x - t)) (g t)) μ :=
  L.ae_strongly_measurable_comp₂ (hf.comp_measurable <| measurable_id.const_sub x) hg

/-- A sufficient condition to prove that `f ⋆[L, μ] g` exists.
We assume that the integrand has compact support and `g` is bounded on this support (note that
both properties hold if `g` is continuous with compact support). We also require that `f` is
integrable on the support of the integrand, and that both functions are strongly measurable.

Note: we could weaken the measurability condition to hold only for `μ.restrict s`. -/
theorem BddAbove.convolution_exists_at' {x₀ : G} {s : Set G}
    (hbg : BddAbove ((fun i => ∥g i∥) '' ((fun t => -t + x₀) ⁻¹' s))) (hs : MeasurableSet s)
    (h2s : (Support fun t => L (f t) (g (x₀ - t))) ⊆ s) (hf : IntegrableOn f s μ) (hmf : AeStronglyMeasurable f μ)
    (hmg : AeStronglyMeasurable g <| map (fun t => x₀ - t) μ) : ConvolutionExistsAt f g x₀ L μ := by
  set s' := (fun t => -t + x₀) ⁻¹' s
  have : ∀ᵐ t : G ∂μ, ∥L (f t) (g (x₀ - t))∥ ≤ s.indicator (fun t => ∥L∥ * ∥f t∥ * ⨆ i : s', ∥g i∥) t := by
    refine' eventually_of_forall _
    refine' le_indicator (fun t ht => _) fun t ht => _
    · refine' (L.le_op_norm₂ _ _).trans _
      refine'
        mul_le_mul_of_nonneg_left (le_csupr_set hbg <| mem_preimage.mpr _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      rwa [neg_sub, sub_add_cancel]
      
    · have : t ∉ support fun t => L (f t) (g (x₀ - t)) := mt (fun h => h2s h) ht
      rw [nmem_support.mp this, norm_zero]
      
  refine' integrable.mono' _ _ this
  · rw [integrable_indicator_iff hs]
    exact (hf.norm.const_mul _).mul_const _
    
  · exact hmf.convolution_integrand_snd' L hmg
    

section Left

variable [SigmaFinite μ] [IsAddLeftInvariant μ]

theorem MeasureTheory.AeStronglyMeasurable.convolution_integrand_snd (hf : AeStronglyMeasurable f μ)
    (hg : AeStronglyMeasurable g μ) (x : G) : AeStronglyMeasurable (fun t => L (f t) (g (x - t))) μ :=
  hf.convolution_integrand_snd' L <| hg.mono' <| map_sub_left_absolutely_continuous μ x

theorem MeasureTheory.AeStronglyMeasurable.convolution_integrand_swap_snd (hf : AeStronglyMeasurable f μ)
    (hg : AeStronglyMeasurable g μ) (x : G) : AeStronglyMeasurable (fun t => L (f (x - t)) (g t)) μ :=
  (hf.mono' (map_sub_left_absolutely_continuous μ x)).convolution_integrand_swap_snd' L hg

end Left

section Right

variable [SigmaFinite μ] [IsAddRightInvariant μ]

theorem MeasureTheory.AeStronglyMeasurable.convolution_integrand (hf : AeStronglyMeasurable f μ)
    (hg : AeStronglyMeasurable g μ) : AeStronglyMeasurable (fun p : G × G => L (f p.2) (g (p.1 - p.2))) (μ.Prod μ) :=
  hf.convolution_integrand' L <| hg.mono' (quasi_measure_preserving_sub μ).AbsolutelyContinuous

theorem MeasureTheory.Integrable.convolution_integrand (hf : Integrable f μ) (hg : Integrable g μ) :
    Integrable (fun p : G × G => L (f p.2) (g (p.1 - p.2))) (μ.Prod μ) := by
  have h_meas : ae_strongly_measurable (fun p : G × G => L (f p.2) (g (p.1 - p.2))) (μ.prod μ) :=
    hf.ae_strongly_measurable.convolution_integrand L hg.ae_strongly_measurable
  have h2_meas : ae_strongly_measurable (fun y : G => ∫ x : G, ∥L (f y) (g (x - y))∥ ∂μ) μ :=
    h_meas.prod_swap.norm.integral_prod_right'
  simp_rw [integrable_prod_iff' h_meas]
  refine' ⟨eventually_of_forall fun t => (L (f t)).integrable_comp (hg.comp_sub_right t), _⟩
  refine' integrable.mono' _ h2_meas (eventually_of_forall fun t => (_ : _ ≤ ∥L∥ * ∥f t∥ * ∫ x, ∥g (x - t)∥ ∂μ))
  · simp_rw [integral_sub_right_eq_self fun t => ∥g t∥]
    exact (hf.norm.const_mul _).mul_const _
    
  · simp_rw [← integral_mul_left]
    rw [Real.norm_of_nonneg]
    · exact
        integral_mono_of_nonneg (eventually_of_forall fun t => norm_nonneg _) ((hg.comp_sub_right t).norm.const_mul _)
          (eventually_of_forall fun t => L.le_op_norm₂ _ _)
      
    exact integral_nonneg fun x => norm_nonneg _
    

theorem MeasureTheory.Integrable.ae_convolution_exists (hf : Integrable f μ) (hg : Integrable g μ) :
    ∀ᵐ x ∂μ, ConvolutionExistsAt f g x L μ :=
  ((integrable_prod_iff <| hf.AeStronglyMeasurable.convolution_integrand L hg.AeStronglyMeasurable).mp <|
      hf.convolution_integrand L hg).1

end Right

variable [TopologicalSpace G] [TopologicalAddGroup G] [BorelSpace G] [SecondCountableTopology G] [SigmaCompactSpace G]

theorem HasCompactSupport.convolution_exists_at {x₀ : G} (h : HasCompactSupport fun t => L (f t) (g (x₀ - t)))
    (hf : LocallyIntegrable f μ) (hg : Continuous g) : ConvolutionExistsAt f g x₀ L μ :=
  ((((Homeomorph.neg G).trans <| Homeomorph.addRight x₀).compact_preimage.mpr h).bdd_above_image
        hg.norm.ContinuousOn).convolution_exists_at'
    L is_closed_closure.MeasurableSet subset_closure (hf h) hf.AeStronglyMeasurable hg.AeStronglyMeasurable

theorem HasCompactSupport.convolution_exists_right (hcg : HasCompactSupport g) (hf : LocallyIntegrable f μ)
    (hg : Continuous g) : ConvolutionExists f g L μ := by
  intro x₀
  refine' HasCompactSupport.convolution_exists_at L _ hf hg
  refine' (hcg.comp_homeomorph (Homeomorph.subLeft x₀)).mono _
  refine' fun t => mt fun ht : g (x₀ - t) = 0 => _
  simp_rw [ht, (L _).map_zero]

theorem HasCompactSupport.convolution_exists_left_of_continuous_right (hcf : HasCompactSupport f)
    (hf : LocallyIntegrable f μ) (hg : Continuous g) : ConvolutionExists f g L μ := by
  intro x₀
  refine' HasCompactSupport.convolution_exists_at L _ hf hg
  refine' hcf.mono _
  refine' fun t => mt fun ht : f t = 0 => _
  simp_rw [ht, L.map_zero₂]

end Groupₓ

section CommGroupₓ

variable [AddCommGroupₓ G]

section MeasurableGroup

variable [HasMeasurableAdd₂ G] [HasMeasurableNeg G] [IsAddLeftInvariant μ]

/-- A sufficient condition to prove that `f ⋆[L, μ] g` exists.
We assume that the integrand has compact support and `g` is bounded on this support (note that
both properties hold if `g` is continuous with compact support). We also require that `f` is
integrable on the support of the integrand, and that both functions are strongly measurable.

This is a variant of `bdd_above.convolution_exists_at'` in an abelian group with a left-invariant
measure. This allows us to state the boundedness and measurability of `g` in a more natural way. -/
theorem BddAbove.convolution_exists_at [SigmaFinite μ] {x₀ : G} {s : Set G}
    (hbg : BddAbove ((fun i => ∥g i∥) '' ((fun t => x₀ - t) ⁻¹' s))) (hs : MeasurableSet s)
    (h2s : (Support fun t => L (f t) (g (x₀ - t))) ⊆ s) (hf : IntegrableOn f s μ) (hmf : AeStronglyMeasurable f μ)
    (hmg : AeStronglyMeasurable g μ) : ConvolutionExistsAt f g x₀ L μ := by
  refine' BddAbove.convolution_exists_at' L _ hs h2s hf hmf _
  · simp_rw [← sub_eq_neg_add, hbg]
    
  · exact hmg.mono' (map_sub_left_absolutely_continuous μ x₀)
    

variable {L} [IsNegInvariant μ]

theorem convolution_exists_at_flip : ConvolutionExistsAt g f x L.flip μ ↔ ConvolutionExistsAt f g x L μ := by
  simp_rw [ConvolutionExistsAt, ← integrable_comp_sub_left (fun t => L (f t) (g (x - t))) x, sub_sub_cancel, flip_apply]

theorem ConvolutionExistsAt.integrable_swap (h : ConvolutionExistsAt f g x L μ) :
    Integrable (fun t => L (f (x - t)) (g t)) μ := by
  convert h.comp_sub_left x
  simp_rw [sub_sub_self]

theorem convolution_exists_at_iff_integrable_swap :
    ConvolutionExistsAt f g x L μ ↔ Integrable (fun t => L (f (x - t)) (g t)) μ :=
  convolution_exists_at_flip.symm

end MeasurableGroup

variable [TopologicalSpace G] [TopologicalAddGroup G] [BorelSpace G] [SecondCountableTopology G] [IsAddLeftInvariant μ]
  [IsNegInvariant μ] [SigmaCompactSpace G]

theorem HasCompactSupport.convolution_exists_left (hcf : HasCompactSupport f) (hf : Continuous f)
    (hg : LocallyIntegrable g μ) : ConvolutionExists f g L μ := fun x₀ =>
  convolution_exists_at_flip.mp <| hcf.convolution_exists_right L.flip hg hf x₀

theorem HasCompactSupport.convolution_exists_right_of_continuous_left (hcg : HasCompactSupport g) (hf : Continuous f)
    (hg : LocallyIntegrable g μ) : ConvolutionExists f g L μ := fun x₀ =>
  convolution_exists_at_flip.mp <| hcg.convolution_exists_left_of_continuous_right L.flip hg hf x₀

end CommGroupₓ

end ConvolutionExists

variable [NormedSpace ℝ F] [CompleteSpace F]

/-- The convolution of two functions `f` and `g` with respect to a continuous bilinear map `L` and
measure `μ`. It is defined to be `(f ⋆[L, μ] g) x = ∫ t, L (f t) (g (x - t)) ∂μ`. -/
noncomputable def convolution [Sub G] (f : G → E) (g : G → E') (L : E →L[𝕜] E' →L[𝕜] F)
    (μ : Measureₓ G := by
      run_tac
        volume_tac) :
    G → F := fun x => ∫ t, L (f t) (g (x - t)) ∂μ

-- mathport name: «expr ⋆[ , ] »
localized [convolution] notation:67 f " ⋆[" L:67 ", " μ:67 "] " g:66 => convolution f g L μ

-- mathport name: «expr ⋆[ ] »
localized [convolution] notation:67 f " ⋆[" L:67 "]" g:66 => convolution f g L MeasureTheory.MeasureSpace.volume

-- mathport name: «expr ⋆ »
localized [convolution]
  notation:67 f " ⋆ " g:66 => convolution f g (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.MeasureSpace.volume

theorem convolution_def [Sub G] : (f ⋆[L, μ] g) x = ∫ t, L (f t) (g (x - t)) ∂μ :=
  rfl

/-- The definition of convolution where the bilinear operator is scalar multiplication.
Note: it often helps the elaborator to give the type of the convolution explicitly. -/
theorem convolution_lsmul [Sub G] {f : G → 𝕜} {g : G → F} : (f ⋆[lsmul 𝕜 𝕜, μ] g : G → F) x = ∫ t, f t • g (x - t) ∂μ :=
  rfl

/-- The definition of convolution where the bilinear operator is multiplication. -/
theorem convolution_lmul [Sub G] [NormedSpace ℝ 𝕜] [CompleteSpace 𝕜] {f : G → 𝕜} {g : G → 𝕜} :
    (f ⋆[lmul 𝕜 𝕜, μ] g) x = ∫ t, f t * g (x - t) ∂μ :=
  rfl

section Groupₓ

variable {L} [AddGroupₓ G]

theorem smul_convolution [SmulCommClass ℝ 𝕜 F] {y : 𝕜} : y • f ⋆[L, μ] g = y • (f ⋆[L, μ] g) := by
  ext
  simp only [← Pi.smul_apply, ← convolution_def, integral_smul, ← L.map_smul₂]

theorem convolution_smul [SmulCommClass ℝ 𝕜 F] {y : 𝕜} : f ⋆[L, μ] y • g = y • (f ⋆[L, μ] g) := by
  ext
  simp only [← Pi.smul_apply, ← convolution_def, integral_smul, ← (L _).map_smul]

theorem zero_convolution : 0 ⋆[L, μ] g = 0 := by
  ext
  simp_rw [convolution_def, Pi.zero_apply, L.map_zero₂, integral_zero]

theorem convolution_zero : f ⋆[L, μ] 0 = 0 := by
  ext
  simp_rw [convolution_def, Pi.zero_apply, (L _).map_zero, integral_zero]

theorem ConvolutionExistsAt.distrib_add {x : G} (hfg : ConvolutionExistsAt f g x L μ)
    (hfg' : ConvolutionExistsAt f g' x L μ) : (f ⋆[L, μ] (g + g')) x = (f ⋆[L, μ] g) x + (f ⋆[L, μ] g') x := by
  simp only [← convolution_def, ← (L _).map_add, ← Pi.add_apply, ← integral_add hfg hfg']

theorem ConvolutionExists.distrib_add (hfg : ConvolutionExists f g L μ) (hfg' : ConvolutionExists f g' L μ) :
    f ⋆[L, μ] (g + g') = f ⋆[L, μ] g + f ⋆[L, μ] g' := by
  ext
  exact (hfg x).distrib_add (hfg' x)

theorem ConvolutionExistsAt.add_distrib {x : G} (hfg : ConvolutionExistsAt f g x L μ)
    (hfg' : ConvolutionExistsAt f' g x L μ) : ((f + f') ⋆[L, μ] g) x = (f ⋆[L, μ] g) x + (f' ⋆[L, μ] g) x := by
  simp only [← convolution_def, ← L.map_add₂, ← Pi.add_apply, ← integral_add hfg hfg']

theorem ConvolutionExists.add_distrib (hfg : ConvolutionExists f g L μ) (hfg' : ConvolutionExists f' g L μ) :
    (f + f') ⋆[L, μ] g = f ⋆[L, μ] g + f' ⋆[L, μ] g := by
  ext
  exact (hfg x).add_distrib (hfg' x)

variable (L)

theorem convolution_congr [HasMeasurableAdd G] [HasMeasurableNeg G] [IsAddLeftInvariant μ] [IsNegInvariant μ]
    (h1 : f =ᵐ[μ] f') (h2 : g =ᵐ[μ] g') : f ⋆[L, μ] g = f' ⋆[L, μ] g' := by
  ext x
  apply integral_congr_ae
  exact (h1.prod_mk <| h2.comp_tendsto (map_sub_left_ae μ x).le).fun_comp ↿fun x y => L x y

theorem support_convolution_subset_swap : Support (f ⋆[L, μ] g) ⊆ Support g + Support f := by
  intro x h2x
  by_contra hx
  apply h2x
  simp_rw [Set.mem_add, not_exists, not_and_distrib, nmem_support] at hx
  rw [convolution_def]
  convert integral_zero G F
  ext t
  rcases hx (x - t) t with (h | h | h)
  · rw [h, (L _).map_zero]
    
  · rw [h, L.map_zero₂]
    
  · exact (h <| sub_add_cancel x t).elim
    

variable [TopologicalSpace G]

variable [TopologicalAddGroup G]

theorem HasCompactSupport.convolution [T2Space G] (hcf : HasCompactSupport f) (hcg : HasCompactSupport g) :
    HasCompactSupport (f ⋆[L, μ] g) :=
  compact_of_is_closed_subset (hcg.IsCompact.add hcf) is_closed_closure <|
    closure_minimal ((support_convolution_subset_swap L).trans <| add_subset_add subset_closure subset_closure)
      (hcg.IsCompact.add hcf).IsClosed

variable [BorelSpace G] [SecondCountableTopology G]

/-- The convolution is continuous if one function is locally integrable and the other has compact
support and is continuous. -/
theorem HasCompactSupport.continuous_convolution_right [LocallyCompactSpace G] [T2Space G] (hcg : HasCompactSupport g)
    (hf : LocallyIntegrable f μ) (hg : Continuous g) : Continuous (f ⋆[L, μ] g) := by
  refine' continuous_iff_continuous_at.mpr fun x₀ => _
  obtain ⟨K, hK, h2K⟩ := exists_compact_mem_nhds x₀
  let K' := -Tsupport g + K
  have hK' : IsCompact K' := hcg.neg.add hK
  have : ∀ᶠ x in 𝓝 x₀, ∀ᵐ t : G ∂μ, ∥L (f t) (g (x - t))∥ ≤ K'.indicator (fun t => ∥L∥ * ∥f t∥ * ⨆ i, ∥g i∥) t :=
    eventually_of_mem h2K fun x hx => eventually_of_forall fun t => hcg.convolution_integrand_bound_right L hg hx
  refine' continuous_at_of_dominated _ this _ _
  · exact eventually_of_forall fun x => hf.ae_strongly_measurable.convolution_integrand_snd' L hg.ae_strongly_measurable
    
  · rw [integrable_indicator_iff hK'.measurable_set]
    exact ((hf hK').norm.const_mul _).mul_const _
    
  · exact
      eventually_of_forall fun t =>
        (L.continuous₂.comp₂ continuous_const <|
            hg.comp <|
              continuous_id.sub <| by
                apply continuous_const).ContinuousAt
    

/-- The convolution is continuous if one function is integrable and the other is bounded and
continuous. -/
theorem BddAbove.continuous_convolution_right_of_integrable (hbg : BddAbove (range fun x => ∥g x∥))
    (hf : Integrable f μ) (hg : Continuous g) : Continuous (f ⋆[L, μ] g) := by
  refine' continuous_iff_continuous_at.mpr fun x₀ => _
  have : ∀ᶠ x in 𝓝 x₀, ∀ᵐ t : G ∂μ, ∥L (f t) (g (x - t))∥ ≤ ∥L∥ * ∥f t∥ * ⨆ i, ∥g i∥ := by
    refine' eventually_of_forall fun x => eventually_of_forall fun t => _
    refine' (L.le_op_norm₂ _ _).trans _
    exact mul_le_mul_of_nonneg_left (le_csupr hbg <| x - t) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  refine' continuous_at_of_dominated _ this _ _
  · exact eventually_of_forall fun x => hf.ae_strongly_measurable.convolution_integrand_snd' L hg.ae_strongly_measurable
    
  · exact (hf.norm.const_mul _).mul_const _
    
  · exact
      eventually_of_forall fun t =>
        (L.continuous₂.comp₂ continuous_const <|
            hg.comp <|
              continuous_id.sub <| by
                apply continuous_const).ContinuousAt
    

/-- A version of `has_compact_support.continuous_convolution_right` that works if `G` is
not locally compact but requires that `g` is integrable. -/
theorem HasCompactSupport.continuous_convolution_right_of_integrable (hcg : HasCompactSupport g) (hf : Integrable f μ)
    (hg : Continuous g) : Continuous (f ⋆[L, μ] g) :=
  (hg.norm.bdd_above_range_of_has_compact_support hcg.norm).continuous_convolution_right_of_integrable L hf hg

variable [SigmaFinite μ] [IsAddRightInvariant μ]

theorem MeasureTheory.Integrable.integrable_convolution (hf : Integrable f μ) (hg : Integrable g μ) :
    Integrable (f ⋆[L, μ] g) μ :=
  (hf.convolution_integrand L hg).integral_prod_left

end Groupₓ

section CommGroupₓ

variable [AddCommGroupₓ G]

theorem support_convolution_subset : Support (f ⋆[L, μ] g) ⊆ Support f + Support g :=
  (support_convolution_subset_swap L).trans (add_commₓ _ _).Subset

variable [TopologicalSpace G]

variable [TopologicalAddGroup G]

variable [BorelSpace G]

variable [IsAddLeftInvariant μ] [IsNegInvariant μ]

variable (L)

/-- Commutativity of convolution -/
theorem convolution_flip : g ⋆[L.flip, μ] f = f ⋆[L, μ] g := by
  ext1 x
  simp_rw [convolution_def]
  rw [← integral_sub_left_eq_self _ μ x]
  simp_rw [sub_sub_self, flip_apply]

/-- The symmetric definition of convolution. -/
theorem convolution_eq_swap : (f ⋆[L, μ] g) x = ∫ t, L (f (x - t)) (g t) ∂μ := by
  rw [← convolution_flip]
  rfl

/-- The symmetric definition of convolution where the bilinear operator is scalar multiplication. -/
theorem convolution_lsmul_swap {f : G → 𝕜} {g : G → F} : (f ⋆[lsmul 𝕜 𝕜, μ] g : G → F) x = ∫ t, f (x - t) • g t ∂μ :=
  convolution_eq_swap _

/-- The symmetric definition of convolution where the bilinear operator is multiplication. -/
theorem convolution_lmul_swap [NormedSpace ℝ 𝕜] [CompleteSpace 𝕜] {f : G → 𝕜} {g : G → 𝕜} :
    (f ⋆[lmul 𝕜 𝕜, μ] g) x = ∫ t, f (x - t) * g t ∂μ :=
  convolution_eq_swap _

variable [SecondCountableTopology G]

theorem HasCompactSupport.continuous_convolution_left [LocallyCompactSpace G] [T2Space G] (hcf : HasCompactSupport f)
    (hf : Continuous f) (hg : LocallyIntegrable g μ) : Continuous (f ⋆[L, μ] g) := by
  rw [← convolution_flip]
  exact hcf.continuous_convolution_right L.flip hg hf

theorem BddAbove.continuous_convolution_left_of_integrable (hbf : BddAbove (range fun x => ∥f x∥)) (hf : Continuous f)
    (hg : Integrable g μ) : Continuous (f ⋆[L, μ] g) := by
  rw [← convolution_flip]
  exact hbf.continuous_convolution_right_of_integrable L.flip hg hf

/-- A version of `has_compact_support.continuous_convolution_left` that works if `G` is
not locally compact but requires that `g` is integrable. -/
theorem HasCompactSupport.continuous_convolution_left_of_integrable (hcf : HasCompactSupport f) (hf : Continuous f)
    (hg : Integrable g μ) : Continuous (f ⋆[L, μ] g) := by
  rw [← convolution_flip]
  exact hcf.continuous_convolution_right_of_integrable L.flip hg hf

end CommGroupₓ

section NormedGroup

variable [SemiNormedGroup G]

/-- Compute `(f ⋆ g) x₀` if the support of the `f` is within `metric.ball 0 R`, and `g` is constant
on `metric.ball x₀ R`.

We can simplify the RHS further if we assume `f` is integrable, but also if `L = (•)` or more
generally if `L` has a `antilipschitz_with`-condition. -/
theorem convolution_eq_right' {x₀ : G} {R : ℝ} (hf : Support f ⊆ Ball (0 : G) R)
    (hg : ∀, ∀ x ∈ Ball x₀ R, ∀, g x = g x₀) : (f ⋆[L, μ] g) x₀ = ∫ t, L (f t) (g x₀) ∂μ := by
  have h2 : ∀ t, L (f t) (g (x₀ - t)) = L (f t) (g x₀) := by
    intro t
    by_cases' ht : t ∈ support f
    · have h2t := hf ht
      rw [mem_ball_zero_iff] at h2t
      specialize hg (x₀ - t)
      rw [sub_eq_add_neg, add_mem_ball_iff_norm, norm_neg, ← sub_eq_add_neg] at hg
      rw [hg h2t]
      
    · rw [nmem_support] at ht
      simp_rw [ht, L.map_zero₂]
      
  simp_rw [convolution_def, h2]

variable [BorelSpace G] [SecondCountableTopology G]

variable [IsAddLeftInvariant μ] [SigmaFinite μ]

/-- Approximate `(f ⋆ g) x₀` if the support of the `f` is bounded within a ball, and `g` is near
`g x₀` on a ball with the same radius around `x₀`. See `dist_convolution_le` for a special case.

We can simplify the second argument of `dist` further if we assume `f` is integrable, but also if
`L = (•)` or more generally if `L` has a `antilipschitz_with`-condition. -/
theorem dist_convolution_le' {x₀ : G} {R ε : ℝ} (hε : 0 ≤ ε) (hif : Integrable f μ) (hf : Support f ⊆ Ball (0 : G) R)
    (hmg : AeStronglyMeasurable g μ) (hg : ∀, ∀ x ∈ Ball x₀ R, ∀, dist (g x) (g x₀) ≤ ε) :
    dist ((f ⋆[L, μ] g : G → F) x₀) (∫ t, L (f t) (g x₀) ∂μ) ≤ (∥L∥ * ∫ x, ∥f x∥ ∂μ) * ε := by
  have hfg : ConvolutionExistsAt f g x₀ L μ := by
    refine'
      BddAbove.convolution_exists_at L _ metric.is_open_ball.measurable_set (subset_trans _ hf) hif.integrable_on
        hif.ae_strongly_measurable hmg
    swap
    · refine' fun t => mt fun ht : f t = 0 => _
      simp_rw [ht, L.map_zero₂]
      
    rw [bdd_above_def]
    refine' ⟨∥g x₀∥ + ε, _⟩
    rintro _ ⟨x, hx, rfl⟩
    refine' norm_le_norm_add_const_of_dist_le (hg x _)
    rwa [mem_ball_iff_norm, norm_sub_rev, ← mem_ball_zero_iff]
  have h2 : ∀ t, dist (L (f t) (g (x₀ - t))) (L (f t) (g x₀)) ≤ ∥L (f t)∥ * ε := by
    intro t
    by_cases' ht : t ∈ support f
    · have h2t := hf ht
      rw [mem_ball_zero_iff] at h2t
      specialize hg (x₀ - t)
      rw [sub_eq_add_neg, add_mem_ball_iff_norm, norm_neg, ← sub_eq_add_neg] at hg
      refine' ((L (f t)).dist_le_op_norm _ _).trans _
      exact mul_le_mul_of_nonneg_left (hg h2t) (norm_nonneg _)
      
    · rw [nmem_support] at ht
      simp_rw [ht, L.map_zero₂, L.map_zero, norm_zero, zero_mul, dist_self]
      
  simp_rw [convolution_def]
  simp_rw [dist_eq_norm] at h2⊢
  rw [← integral_sub hfg.integrable]
  swap
  · exact (L.flip (g x₀)).integrable_comp hif
    
  refine' (norm_integral_le_of_norm_le ((L.integrable_comp hif).norm.mul_const ε) (eventually_of_forall h2)).trans _
  rw [integral_mul_right]
  refine' mul_le_mul_of_nonneg_right _ hε
  have h3 : ∀ t, ∥L (f t)∥ ≤ ∥L∥ * ∥f t∥ := fun t => L.le_op_norm (f t)
  refine' (integral_mono (L.integrable_comp hif).norm (hif.norm.const_mul _) h3).trans_eq _
  rw [integral_mul_left]

variable [NormedSpace ℝ E] [NormedSpace ℝ E'] [CompleteSpace E']

/-- Approximate `f ⋆ g` if the support of the `f` is bounded within a ball, and `g` is near `g x₀`
on a ball with the same radius around `x₀`.

This is a special case of `dist_convolution_le'` where `L` is `(•)`, `f` has integral 1 and `f` is
nonnegative. -/
theorem dist_convolution_le {f : G → ℝ} {x₀ : G} {R ε : ℝ} (hε : 0 ≤ ε) (hf : Support f ⊆ Ball (0 : G) R)
    (hnf : ∀ x, 0 ≤ f x) (hintf : (∫ x, f x ∂μ) = 1) (hmg : AeStronglyMeasurable g μ)
    (hg : ∀, ∀ x ∈ Ball x₀ R, ∀, dist (g x) (g x₀) ≤ ε) : dist ((f ⋆[lsmul ℝ ℝ, μ] g : G → E') x₀) (g x₀) ≤ ε := by
  have hif : integrable f μ := by
    by_contra hif
    exact zero_ne_one ((integral_undef hif).symm.trans hintf)
  convert (dist_convolution_le' _ hε hif hf hmg hg).trans _
  · simp_rw [lsmul_apply, integral_smul_const, hintf, one_smul]
    
  · simp_rw [Real.norm_of_nonneg (hnf _), hintf, mul_oneₓ]
    exact (mul_le_mul_of_nonneg_right op_norm_lsmul_le hε).trans_eq (one_mulₓ ε)
    

/-- `(φ i ⋆ g) x₀` tends to `g x₀` if `φ` is a sequence of nonnegative functions with integral 1
whose support tends to small neighborhoods around `(0 : G)` and `g` is continuous at `x₀`.

See also `cont_diff_bump_of_inner.convolution_tendsto_right'`. -/
theorem convolution_tendsto_right {ι} {l : Filter ι} {φ : ι → G → ℝ} (hnφ : ∀ i x, 0 ≤ φ i x)
    (hiφ : ∀ i, (∫ s, φ i s ∂μ) = 1) (hφ : Tendsto (fun n => Support (φ n)) l (𝓝 0).smallSets)
    (hmg : AeStronglyMeasurable g μ) {x₀ : G} (hcg : ContinuousAt g x₀) :
    Tendsto (fun i => (φ i ⋆[lsmul ℝ ℝ, μ] g : G → E') x₀) l (𝓝 (g x₀)) := by
  simp_rw [tendsto_small_sets_iff] at hφ
  rw [Metric.continuous_at_iff] at hcg
  rw [Metric.tendsto_nhds]
  intro ε hε
  rcases hcg (ε / 2) (half_pos hε) with ⟨δ, hδ, hgδ⟩
  refine' (hφ (ball (0 : G) δ) <| ball_mem_nhds _ hδ).mono fun i hi => _
  exact
    (dist_convolution_le (half_pos hε).le hi (hnφ i) (hiφ i) hmg fun x hx => (hgδ hx.out).le).trans_lt (half_lt_self hε)

end NormedGroup

namespace ContDiffBumpOfInner

variable {n : WithTop ℕ}

variable [NormedSpace ℝ E']

variable [InnerProductSpace ℝ G]

variable [CompleteSpace E']

variable {a : G} {φ : ContDiffBumpOfInner (0 : G)}

/-- If `φ` is a bump function, compute `(φ ⋆ g) x₀` if `g` is constant on `metric.ball x₀ φ.R`. -/
theorem convolution_eq_right {x₀ : G} (hg : ∀, ∀ x ∈ Ball x₀ φ.r, ∀, g x = g x₀) :
    (φ ⋆[lsmul ℝ ℝ, μ] g : G → E') x₀ = integral μ φ • g x₀ := by
  simp_rw [convolution_eq_right' _ φ.support_eq.subset hg, lsmul_apply, integral_smul_const]

variable [BorelSpace G]

variable [IsLocallyFiniteMeasure μ] [IsOpenPosMeasure μ]

variable [FiniteDimensional ℝ G]

/-- If `φ` is a normed bump function, compute `φ ⋆ g` if `g` is constant on `metric.ball x₀ φ.R`. -/
theorem normed_convolution_eq_right {x₀ : G} (hg : ∀, ∀ x ∈ Ball x₀ φ.r, ∀, g x = g x₀) :
    (φ.normed μ ⋆[lsmul ℝ ℝ, μ] g : G → E') x₀ = g x₀ := by
  simp_rw [convolution_eq_right' _ φ.support_normed_eq.subset hg, lsmul_apply]
  exact integral_normed_smul φ μ (g x₀)

variable [IsAddLeftInvariant μ]

/-- If `φ` is a normed bump function, approximate `(φ ⋆ g) x₀` if `g` is near `g x₀` on a ball with
radius `φ.R` around `x₀`. -/
theorem dist_normed_convolution_le {x₀ : G} {ε : ℝ} (hmg : AeStronglyMeasurable g μ)
    (hg : ∀, ∀ x ∈ Ball x₀ φ.r, ∀, dist (g x) (g x₀) ≤ ε) :
    dist ((φ.normed μ ⋆[lsmul ℝ ℝ, μ] g : G → E') x₀) (g x₀) ≤ ε :=
  dist_convolution_le
    (by
      simp_rw [← dist_self (g x₀), hg x₀ (mem_ball_self φ.R_pos)])
    φ.support_normed_eq.Subset φ.nonneg_normed φ.integral_normed hmg hg

/-- If `φ i` is a sequence of normed bump function, `(φ i ⋆ g) x₀` tends to `g x₀` if `(φ i).R`
tends to `0` and `g` is continuous at `x₀`. -/
theorem convolution_tendsto_right' {ι} {φ : ι → ContDiffBumpOfInner (0 : G)} {l : Filter ι}
    (hφ : Tendsto (fun i => (φ i).r) l (𝓝 0)) (hmg : AeStronglyMeasurable g μ) {x₀ : G} (hcg : ContinuousAt g x₀) :
    Tendsto (fun i => ((fun x => (φ i).normed μ x) ⋆[lsmul ℝ ℝ, μ] g : G → E') x₀) l (𝓝 (g x₀)) := by
  refine' convolution_tendsto_right (fun i => (φ i).nonneg_normed) (fun i => (φ i).integral_normed) _ hmg hcg
  rw [NormedGroup.tendsto_nhds_zero] at hφ
  rw [tendsto_small_sets_iff]
  intro t ht
  rcases metric.mem_nhds_iff.mp ht with ⟨ε, hε, ht⟩
  refine' (hφ ε hε).mono fun i hi => subset_trans _ ht
  simp_rw [(φ i).support_normed_eq]
  rw [Real.norm_eq_abs, abs_eq_self.mpr (φ i).R_pos.le] at hi
  exact ball_subset_ball hi.le

/-- Special case of `cont_diff_bump_of_inner.convolution_tendsto_right'` where `g` is continuous. -/
theorem convolution_tendsto_right {ι} {φ : ι → ContDiffBumpOfInner (0 : G)} {l : Filter ι}
    (hφ : Tendsto (fun i => (φ i).r) l (𝓝 0)) (hg : Continuous g) (x₀ : G) :
    Tendsto (fun i => ((fun x => (φ i).normed μ x) ⋆[lsmul ℝ ℝ, μ] g : G → E') x₀) l (𝓝 (g x₀)) :=
  convolution_tendsto_right' hφ hg.AeStronglyMeasurable hg.ContinuousAt

end ContDiffBumpOfInner

end Measurability

end NondiscreteNormedField

open convolution

section IsROrC

variable [IsROrC 𝕜]

variable [NormedSpace 𝕜 E]

variable [NormedSpace 𝕜 E']

variable [NormedSpace 𝕜 E'']

variable [NormedSpace ℝ F] [NormedSpace 𝕜 F]

variable {n : WithTop ℕ}

variable [CompleteSpace F]

variable [MeasurableSpace G] {μ : Measureₓ G}

variable (L : E →L[𝕜] E' →L[𝕜] F)

section Assoc

variable [NormedGroup F'] [NormedSpace ℝ F'] [NormedSpace 𝕜 F'] [CompleteSpace F']

variable [NormedGroup F''] [NormedSpace ℝ F''] [NormedSpace 𝕜 F''] [CompleteSpace F'']

variable {k : G → E''}

variable (L₂ : F →L[𝕜] E'' →L[𝕜] F')

variable (L₃ : E →L[𝕜] F'' →L[𝕜] F')

variable (L₄ : E' →L[𝕜] E'' →L[𝕜] F'')

variable [AddGroupₓ G] [HasMeasurableAdd G]

variable [SigmaFinite μ]

variable {ν : Measureₓ G} [SigmaFinite ν] [IsAddRightInvariant ν]

/-- Convolution is associative.
To do: prove that `hi` follows from simpler conditions. -/
theorem convolution_assoc (hL : ∀ (x : E) (y : E') (z : E''), L₂ (L x y) z = L₃ x (L₄ y z)) {x₀ : G}
    (h₄ : ConvolutionExists g k L₄ ν) (h₁ : ConvolutionExists f g L μ)
    (hi : Integrable (uncurry fun x y => (L₃ (f y)) ((L₄ (g (x - y))) (k (x₀ - x)))) (ν.Prod μ)) :
    ((f ⋆[L, μ] g) ⋆[L₂, ν] k) x₀ = (f ⋆[L₃, μ] g ⋆[L₄, ν] k) x₀ := by
  have h1 := fun t => (L₂.flip (k (x₀ - t))).integral_comp_comm (h₁ t)
  dsimp' only [← flip_apply]  at h1
  simp_rw [convolution_def, ← (L₃ (f _)).integral_comp_comm (h₄ (x₀ - _)), ← h1, hL]
  rw [integral_integral_swap hi]
  congr
  ext t
  rw [eq_comm, ← integral_sub_right_eq_self _ t]
  · simp_rw [sub_sub_sub_cancel_right]
    
  · infer_instance
    

end Assoc

variable [NormedGroup G] [BorelSpace G]

variable [SecondCountableTopology G] [SigmaCompactSpace G]

theorem convolution_precompR_apply {g : G → E'' →L[𝕜] E'} (hf : LocallyIntegrable f μ) (hcg : HasCompactSupport g)
    (hg : Continuous g) (x₀ : G) (x : E'') : (f ⋆[L.precompR E'', μ] g) x₀ x = (f ⋆[L, μ] fun a => g a x) x₀ := by
  have := hcg.convolution_exists_right (L.precompR E'') hf hg x₀
  simp_rw [convolution_def, ContinuousLinearMap.integral_apply this]
  rfl

variable [SigmaFinite μ] [IsAddLeftInvariant μ]

variable [NormedSpace 𝕜 G] [ProperSpace G]

/-- Compute the total derivative of `f ⋆ g` if `g` is `C^1` with compact support and `f` is locally
integrable. To write down the total derivative as a convolution, we use
`continuous_linear_map.precompR`. -/
theorem HasCompactSupport.has_fderiv_at_convolution_right (hcg : HasCompactSupport g) (hf : LocallyIntegrable f μ)
    (hg : ContDiff 𝕜 1 g) (x₀ : G) : HasFderivAt (f ⋆[L, μ] g) ((f ⋆[L.precompR G, μ] fderiv 𝕜 g) x₀) x₀ := by
  set L' := L.precompR G
  have h1 : ∀ᶠ x in 𝓝 x₀, ae_strongly_measurable (fun t => L (f t) (g (x - t))) μ :=
    eventually_of_forall (hf.ae_strongly_measurable.convolution_integrand_snd L hg.continuous.ae_strongly_measurable)
  have h2 : ∀ x, ae_strongly_measurable (fun t => L' (f t) (fderiv 𝕜 g (x - t))) μ :=
    hf.ae_strongly_measurable.convolution_integrand_snd L' (hg.continuous_fderiv le_rfl).AeStronglyMeasurable
  have h3 : ∀ x t, HasFderivAt (fun x => g (x - t)) (fderiv 𝕜 g (x - t)) x := by
    intro x t
    simpa using
      (hg.differentiable le_rfl).DifferentiableAt.HasFderivAt.comp x
        ((has_fderiv_at_id x).sub (has_fderiv_at_const t x))
  let K' := -Tsupport (fderiv 𝕜 g) + closed_ball x₀ 1
  have hK' : IsCompact K' := (hcg.fderiv 𝕜).neg.add (is_compact_closed_ball x₀ 1)
  refine' has_fderiv_at_integral_of_dominated_of_fderiv_le zero_lt_one h1 _ (h2 x₀) _ _ _
  · exact K'.indicator fun t => ∥L'∥ * ∥f t∥ * ⨆ x, ∥fderiv 𝕜 g x∥
    
  · exact hcg.convolution_exists_right L hf hg.continuous x₀
    
  · refine' eventually_of_forall fun t x hx => _
    exact (hcg.fderiv 𝕜).convolution_integrand_bound_right L' (hg.continuous_fderiv le_rfl) (ball_subset_closed_ball hx)
    
  · rw [integrable_indicator_iff hK'.measurable_set]
    exact ((hf hK').norm.const_mul _).mul_const _
    
  · exact eventually_of_forall fun t x hx => (L _).HasFderivAt.comp x (h3 x t)
    

theorem HasCompactSupport.has_fderiv_at_convolution_left [IsNegInvariant μ] (hcf : HasCompactSupport f)
    (hf : ContDiff 𝕜 1 f) (hg : LocallyIntegrable g μ) (x₀ : G) :
    HasFderivAt (f ⋆[L, μ] g) ((fderiv 𝕜 f ⋆[L.precompL G, μ] g) x₀) x₀ := by
  simp (config := { singlePass := true })only [convolution_flip]
  exact hcf.has_fderiv_at_convolution_right L.flip hg hf x₀

theorem HasCompactSupport.cont_diff_convolution_right [FiniteDimensional 𝕜 G] (hcg : HasCompactSupport g)
    (hf : LocallyIntegrable f μ) (hg : ContDiff 𝕜 n g) : ContDiff 𝕜 n (f ⋆[L, μ] g) := by
  induction' n using WithTop.nat_induction with n ih ih generalizing g
  · rw [cont_diff_zero] at hg⊢
    exact hcg.continuous_convolution_right L hf hg
    
  · have h : ∀ x, HasFderivAt (f ⋆[L, μ] g) ((f ⋆[L.precompR G, μ] fderiv 𝕜 g) x) x :=
      hcg.has_fderiv_at_convolution_right L hf hg.one_of_succ
    rw [cont_diff_succ_iff_fderiv_apply]
    constructor
    · exact fun x₀ => ⟨_, h x₀⟩
      
    · simp_rw [fderiv_eq h, convolution_precompR_apply L hf (hcg.fderiv 𝕜) (hg.one_of_succ.continuous_fderiv le_rfl)]
      intro x
      refine' ih _ _
      · refine'
          @HasCompactSupport.comp_left _ _ _ _ _ _ (fun G : _ →L[𝕜] _ => G x) _ (hcg.fderiv 𝕜)
            (ContinuousLinearMap.zero_apply x)
        
      · revert x
        rw [← cont_diff_clm_apply]
        exact (cont_diff_succ_iff_fderiv.mp hg).2
        
      
    
  · rw [cont_diff_top] at hg⊢
    exact fun n => ih n hcg (hg n)
    

theorem HasCompactSupport.cont_diff_convolution_left [FiniteDimensional 𝕜 G] [IsNegInvariant μ]
    (hcf : HasCompactSupport f) (hf : ContDiff 𝕜 n f) (hg : LocallyIntegrable g μ) : ContDiff 𝕜 n (f ⋆[L, μ] g) := by
  rw [← convolution_flip]
  exact hcf.cont_diff_convolution_right L.flip hg hf

end IsROrC

section Real

/-! The one-variable case -/


variable [IsROrC 𝕜]

variable [NormedSpace 𝕜 E]

variable [NormedSpace 𝕜 E']

variable [NormedSpace ℝ F] [NormedSpace 𝕜 F]

variable {f₀ : 𝕜 → E} {g₀ : 𝕜 → E'}

variable {n : WithTop ℕ}

variable (L : E →L[𝕜] E' →L[𝕜] F)

variable [CompleteSpace F]

variable {μ : Measureₓ 𝕜}

variable [IsAddLeftInvariant μ] [SigmaFinite μ]

theorem HasCompactSupport.has_deriv_at_convolution_right (hf : LocallyIntegrable f₀ μ) (hcg : HasCompactSupport g₀)
    (hg : ContDiff 𝕜 1 g₀) (x₀ : 𝕜) : HasDerivAt (f₀ ⋆[L, μ] g₀) ((f₀ ⋆[L, μ] deriv g₀) x₀) x₀ := by
  convert (hcg.has_fderiv_at_convolution_right L hf hg x₀).HasDerivAt
  rw [convolution_precompR_apply L hf (hcg.fderiv 𝕜) (hg.continuous_fderiv le_rfl)]
  rfl

theorem HasCompactSupport.has_deriv_at_convolution_left [IsNegInvariant μ] (hcf : HasCompactSupport f₀)
    (hf : ContDiff 𝕜 1 f₀) (hg : LocallyIntegrable g₀ μ) (x₀ : 𝕜) :
    HasDerivAt (f₀ ⋆[L, μ] g₀) ((deriv f₀ ⋆[L, μ] g₀) x₀) x₀ := by
  simp (config := { singlePass := true })only [convolution_flip]
  exact hcf.has_deriv_at_convolution_right L.flip hg hf x₀

end Real

