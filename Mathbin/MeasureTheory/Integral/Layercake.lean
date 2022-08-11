/-
Copyright (c) 2022 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
import Mathbin.MeasureTheory.Integral.IntervalIntegral
import Mathbin.Analysis.SpecialFunctions.Integrals

/-!
# The layer cake formula / Cavalieri's principle / tail probability formula

In this file we prove the following layer cake formula.

Consider a non-negative measurable function `f` on a sigma-finite measure space. Apply pointwise
to it an increasing absolutely continuous function `G : ℝ≥0 → ℝ≥0` vanishing at the origin, with
derivative `G' = g` on the positive real line (in other words, `G` a primitive of a non-negative
locally integrable function `g` on the positive real line). Then the integral of the result,
`∫ G ∘ f`, can be written as the integral over the positive real line of the "tail measures" of `f`
(i.e., a function giving the measures of the sets on which `f` exceeds different positive real
values) weighted by `g`. In probability theory contexts, the "tail measures" could be referred to
as "tail probabilities" of the random variable `f`, or as values of the "complementary cumulative
distribution function" of the random variable `f`. The terminology "tail probability formula" is
therefore occasionally used for the layer cake formula (or a standard application of it).

The essence of the (mathematical) proof is Fubini's theorem.

We also give the two most common applications of the layer cake formula
 * a representation of the integral of a nonnegative function f:
   ∫ f(ω) ∂μ(ω) = ∫ μ {ω | f(ω) ≥ t} dt
 * a representation of the integral of the p:th power of a nonnegative function f:
   ∫ f(ω)^p ∂μ(ω) = p * ∫ t^(p-1) * μ {ω | f(ω) ≥ t} dt .

## Main results

 * `lintegral_comp_eq_lintegral_meas_le_mul`: The general layer cake formula with Lebesgue
   integrals.
 * `lintegral_eq_lintegral_meas_le`: The most common special case of the layer cake formula, which
   states that for a nonnegative function f we have ∫ f(ω) ∂μ(ω) = ∫ μ {ω | f(ω) ≥ t} dt .

## Tags

layer cake representation, Cavalieri's principle, tail probability formula
-/


noncomputable section

open Ennreal MeasureTheory

open Set MeasureTheory Filter

/-! ### Layercake theorem -/


section Layercake

namespace MeasureTheory

variable {α : Type _} [MeasurableSpace α] {f : α → ℝ} {g : ℝ → ℝ} {s : Set α}

/-- An auxiliary version of the layer cake theorem (Cavalieri's principle, tail probability
formula), with a measurability assumption that would also essentially follow from the
integrability assumptions.

See `measure_theory.layercake` for the main formulation of the layer cake theorem. -/
theorem lintegral_comp_eq_lintegral_meas_le_mul_of_measurable (μ : Measure α) [SigmaFinite μ] (f_nn : 0 ≤ f)
    (f_mble : Measurable f) (g_intble : ∀, ∀ t > 0, ∀, IntervalIntegrable g volume 0 t) (g_mble : Measurable g)
    (g_nn : ∀, ∀ t > 0, ∀, 0 ≤ g t) :
    (∫⁻ ω, Ennreal.ofReal (∫ t in 0 ..f ω, g t) ∂μ) = ∫⁻ t in Ioi 0, μ { a : α | t ≤ f a } * Ennreal.ofReal (g t) := by
  have g_intble' : ∀ t : ℝ, 0 ≤ t → IntervalIntegrable g volume 0 t := by
    intro t ht
    cases eq_or_lt_of_le ht
    · simp [h]
      
    · exact g_intble t h
      
  have integrand_eq : ∀ ω, Ennreal.ofReal (∫ t in 0 ..f ω, g t) = ∫⁻ t in Ioc 0 (f ω), Ennreal.ofReal (g t) := by
    intro ω
    have g_ae_nn : 0 ≤ᵐ[volume.restrict (Ioc 0 (f ω))] g := by
      filter_upwards [self_mem_ae_restrict
          (measurable_set_Ioc : MeasurableSet (Ioc 0 (f ω)))] with x hx using g_nn x hx.1
    rw [← of_real_integral_eq_lintegral_of_real (g_intble' (f ω) (f_nn ω)).1 g_ae_nn]
    congr
    exact intervalIntegral.integral_of_le (f_nn ω)
  simp_rw [integrand_eq, ← lintegral_indicator (fun t => Ennreal.ofReal (g t)) measurable_set_Ioc, ←
    lintegral_indicator _ measurable_set_Ioi]
  rw [lintegral_lintegral_swap]
  · apply congr_arg
    funext s
    have aux₁ :
      (fun x => (Ioc 0 (f x)).indicator (fun t : ℝ => Ennreal.ofReal (g t)) s) = fun x =>
        Ennreal.ofReal (g s) * (Ioi (0 : ℝ)).indicator (fun _ => 1) s *
          (Ici s).indicator (fun t : ℝ => (1 : ℝ≥0∞)) (f x) :=
      by
      funext a
      by_cases' s ∈ Ioc (0 : ℝ) (f a)
      · simp only [← h, ← show s ∈ Ioi (0 : ℝ) from h.1, ← show f a ∈ Ici s from h.2, ← indicator_of_mem, ← mul_oneₓ]
        
      · have h_copy := h
        simp only [← mem_Ioc, ← not_and, ← not_leₓ] at h
        by_cases' h' : 0 < s
        · simp only [← h_copy, ← h h', ← indicator_of_not_mem, ← not_false_iff, ← mem_Ici, ← not_leₓ, ← mul_zero]
          
        · have : s ∉ Ioi (0 : ℝ) := h'
          simp only [← this, ← h', ← indicator_of_not_mem, ← not_false_iff, ← mul_zero, ← zero_mul, ← mem_Ioc, ←
            false_andₓ]
          
        
    simp_rw [aux₁]
    rw [lintegral_const_mul']
    swap
    · apply Ennreal.mul_ne_top Ennreal.of_real_ne_top
      by_cases' s ∈ Ioi (0 : ℝ) <;>
        · simp [← h]
          
      
    simp_rw
      [show
        (fun a => (Ici s).indicator (fun t : ℝ => (1 : ℝ≥0∞)) (f a)) = fun a =>
          { a : α | s ≤ f a }.indicator (fun _ => 1) a
        by
        funext a
        by_cases' s ≤ f a <;> simp [← h]]
    rw [lintegral_indicator]
    swap
    · exact f_mble measurable_set_Ici
      
    rw [lintegral_one, measure.restrict_apply MeasurableSet.univ, univ_inter, indicator_mul_left, mul_assoc,
      show
        (Ioi 0).indicator (fun _x : ℝ => (1 : ℝ≥0∞)) s * μ { a : α | s ≤ f a } =
          (Ioi 0).indicator (fun _x : ℝ => 1 * μ { a : α | s ≤ f a }) s
        by
        by_cases' 0 < s <;> simp [← h]]
    simp_rw [mul_comm _ (Ennreal.ofReal _), one_mulₓ]
    rfl
    
  have aux₂ :
    (Function.uncurry fun (x : α) (y : ℝ) => (Ioc 0 (f x)).indicator (fun t : ℝ => Ennreal.ofReal (g t)) y) =
      { p : α × ℝ | p.2 ∈ Ioc 0 (f p.1) }.indicator fun p => Ennreal.ofReal (g p.2) :=
    by
    funext p
    cases p
    rw [Function.uncurry_apply_pair]
    by_cases' p_snd ∈ Ioc 0 (f p_fst)
    · have h' : (p_fst, p_snd) ∈ { p : α × ℝ | p.snd ∈ Ioc 0 (f p.fst) } := h
      rw [Set.indicator_of_mem h', Set.indicator_of_mem h]
      
    · have h' : (p_fst, p_snd) ∉ { p : α × ℝ | p.snd ∈ Ioc 0 (f p.fst) } := h
      rw [Set.indicator_of_not_mem h', Set.indicator_of_not_mem h]
      
  rw [aux₂]
  have mble := measurable_set_region_between_oc measurable_zero f_mble MeasurableSet.univ
  simp_rw [mem_univ, Pi.zero_apply, true_andₓ] at mble
  exact (ennreal.measurable_of_real.comp (g_mble.comp measurable_snd)).AeMeasurable.indicator mble

/-- The layer cake theorem / Cavalieri's principle / tail probability formula:

Let `f` be a non-negative measurable function on a sigma-finite measure space. Let `G` be an
increasing absolutely continuous function on the positive real line, vanishing at the origin,
with derivative `G' = g`. Then the integral of the composition `G ∘ f` can be written as
the integral over the positive real line of the "tail measures" `μ {ω | f(ω) ≥ t}` of `f`
weighted by `g`.

Roughly speaking, the statement is: `∫⁻ (G ∘ f) ∂μ = ∫⁻ t in 0 .. ∞, g(t) * μ {ω | f(ω) ≥ t}`. -/
theorem lintegral_comp_eq_lintegral_meas_le_mul (μ : Measure α) [SigmaFinite μ] (f_nn : 0 ≤ f) (f_mble : Measurable f)
    (g_intble : ∀, ∀ t > 0, ∀, IntervalIntegrable g volume 0 t) (g_nn : ∀ᵐ t ∂volume.restrict (Ioi 0), 0 ≤ g t) :
    (∫⁻ ω, Ennreal.ofReal (∫ t in 0 ..f ω, g t) ∂μ) = ∫⁻ t in Ioi 0, μ { a : α | t ≤ f a } * Ennreal.ofReal (g t) := by
  have ex_G : ∃ G : ℝ → ℝ, Measurable G ∧ 0 ≤ G ∧ g =ᵐ[volume.restrict (Ioi 0)] G := by
    refine' AeMeasurable.exists_measurable_nonneg _ g_nn
    exact ae_measurable_Ioi_of_forall_Ioc fun t ht => (g_intble t ht).1.1.AeMeasurable
  rcases ex_G with ⟨G, G_mble, G_nn, g_eq_G⟩
  have g_eq_G_on : ∀ t, g =ᵐ[volume.restrict (Ioc 0 t)] G := fun t =>
    ae_mono (measure.restrict_mono Ioc_subset_Ioi_self le_rfl) g_eq_G
  have G_intble : ∀, ∀ t > 0, ∀, IntervalIntegrable G volume 0 t := by
    refine' fun t t_pos => ⟨integrable_on.congr_fun' (g_intble t t_pos).1 (g_eq_G_on t), _⟩
    rw [Ioc_eq_empty_of_le t_pos.lt.le]
    exact integrable_on_empty
  have eq₁ :
    (∫⁻ t in Ioi 0, μ { a : α | t ≤ f a } * Ennreal.ofReal (g t)) =
      ∫⁻ t in Ioi 0, μ { a : α | t ≤ f a } * Ennreal.ofReal (G t) :=
    by
    apply lintegral_congr_ae
    filter_upwards [g_eq_G] with a ha
    rw [ha]
  have eq₂ : ∀ ω, (∫ t in 0 ..f ω, g t) = ∫ t in 0 ..f ω, G t := by
    refine' fun ω => intervalIntegral.integral_congr_ae _
    have fω_nn : 0 ≤ f ω := f_nn ω
    rw [interval_oc_of_le fω_nn, ← ae_restrict_iff' (measurable_set_Ioc : MeasurableSet (Ioc (0 : ℝ) (f ω)))]
    exact g_eq_G_on (f ω)
  simp_rw [eq₁, eq₂]
  exact lintegral_comp_eq_lintegral_meas_le_mul_of_measurable μ f_nn f_mble G_intble G_mble fun t t_pos => G_nn t

/-- The standard case of the layer cake formula / Cavalieri's principle / tail probability formula:

For a nonnegative function `f` on a sigma-finite measure space, the Lebesgue integral of `f` can
be written (roughly speaking) as: `∫⁻ f ∂μ = ∫⁻ t in 0 .. ∞, μ {ω | f(ω) ≥ t}`. -/
theorem lintegral_eq_lintegral_meas_le (μ : Measure α) [SigmaFinite μ] (f_nn : 0 ≤ f) (f_mble : Measurable f) :
    (∫⁻ ω, Ennreal.ofReal (f ω) ∂μ) = ∫⁻ t in Ioi 0, μ { a : α | t ≤ f a } := by
  set cst := fun t : ℝ => (1 : ℝ) with def_cst
  have cst_intble : ∀, ∀ t > 0, ∀, IntervalIntegrable cst volume 0 t := fun _ _ => interval_integrable_const
  have key :=
    lintegral_comp_eq_lintegral_meas_le_mul μ f_nn f_mble cst_intble (eventually_of_forall fun t => zero_le_one)
  simp_rw [def_cst, Ennreal.of_real_one, mul_oneₓ] at key
  rw [← key]
  congr with ω
  simp only [← intervalIntegral.integral_const, ← sub_zero, ← Algebra.id.smul_eq_mul, ← mul_oneₓ]

/-- An application of the layer cake formula / Cavalieri's principle / tail probability formula:

For a nonnegative function `f` on a sigma-finite measure space, the Lebesgue integral of `f` can
be written (roughly speaking) as: `∫⁻ f^p ∂μ = p * ∫⁻ t in 0 .. ∞, t^(p-1) * μ {ω | f(ω) ≥ t}`. -/
theorem lintegral_rpow_eq_lintegral_meas_le_mul (μ : Measure α) [SigmaFinite μ] (f_nn : 0 ≤ f) (f_mble : Measurable f)
    {p : ℝ} (p_pos : 0 < p) :
    (∫⁻ ω, Ennreal.ofReal (f ω ^ p) ∂μ) =
      Ennreal.ofReal p * ∫⁻ t in Ioi 0, μ { a : α | t ≤ f a } * Ennreal.ofReal (t ^ (p - 1)) :=
  by
  have one_lt_p : -1 < p - 1 := by
    linarith
  have obs : ∀ x : ℝ, (∫ t : ℝ in 0 ..x, t ^ (p - 1)) = x ^ p / p := by
    intro x
    rw [integral_rpow (Or.inl one_lt_p)]
    simp [← Real.zero_rpow p_pos.ne.symm]
  set g := fun t : ℝ => t ^ (p - 1) with g_def
  have g_nn : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)), 0 ≤ g t := by
    filter_upwards [self_mem_ae_restrict (measurable_set_Ioi : MeasurableSet (Ioi (0 : ℝ)))]
    intro t t_pos
    rw [g_def]
    exact Real.rpow_nonneg_of_nonneg (mem_Ioi.mp t_pos).le (p - 1)
  have g_intble : ∀, ∀ t > 0, ∀, IntervalIntegrable g volume 0 t := fun _ _ =>
    intervalIntegral.interval_integrable_rpow' one_lt_p
  have key := lintegral_comp_eq_lintegral_meas_le_mul μ f_nn f_mble g_intble g_nn
  simp_rw [g_def] at key
  rw [← key, ← lintegral_const_mul (Ennreal.ofReal p)] <;> simp_rw [obs]
  · congr with ω
    rw [← Ennreal.of_real_mul p_pos.le, mul_div_cancel' (f ω ^ p) p_pos.ne.symm]
    
  · exact ((f_mble.pow measurable_const).div_const p).ennreal_of_real
    

end MeasureTheory

end Layercake

