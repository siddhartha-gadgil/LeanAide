/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import Mathbin.MeasureTheory.Measure.Regular
import Mathbin.MeasureTheory.Function.SimpleFuncDenseLp
import Mathbin.Topology.UrysohnsLemma
import Mathbin.MeasureTheory.Function.L1Space

/-!
# Approximation in Lᵖ by continuous functions

This file proves that bounded continuous functions are dense in `Lp E p μ`, for `1 ≤ p < ∞`, if the
domain `α` of the functions is a normal topological space and the measure `μ` is weakly regular.

The result is presented in several versions:
* `measure_theory.Lp.bounded_continuous_function_dense`: The subgroup
  `measure_theory.Lp.bounded_continuous_function` of `Lp E p μ`, the additive subgroup of
  `Lp E p μ` consisting of equivalence classes containing a continuous representative, is dense in
  `Lp E p μ`.
* `bounded_continuous_function.to_Lp_dense_range`: For finite-measure `μ`, the continuous linear
  map `bounded_continuous_function.to_Lp p μ 𝕜` from `α →ᵇ E` to `Lp E p μ` has dense range.
* `continuous_map.to_Lp_dense_range`: For compact `α` and finite-measure `μ`, the continuous linear
  map `continuous_map.to_Lp p μ 𝕜` from `C(α, E)` to `Lp E p μ` has dense range.

Note that for `p = ∞` this result is not true:  the characteristic function of the set `[0, ∞)` in
`ℝ` cannot be continuously approximated in `L∞`.

The proof is in three steps.  First, since simple functions are dense in `Lp`, it suffices to prove
the result for a scalar multiple of a characteristic function of a measurable set `s`. Secondly,
since the measure `μ` is weakly regular, the set `s` can be approximated above by an open set and
below by a closed set.  Finally, since the domain `α` is normal, we use Urysohn's lemma to find a
continuous function interpolating between these two sets.

## Related results

Are you looking for a result on "directional" approximation (above or below with respect to an
order) of functions whose codomain is `ℝ≥0∞` or `ℝ`, by semicontinuous functions?  See the
Vitali-Carathéodory theorem, in the file `measure_theory.vitali_caratheodory`.

-/


open Ennreal Nnreal TopologicalSpace BoundedContinuousFunction

open MeasureTheory TopologicalSpace ContinuousMap

variable {α : Type _} [MeasurableSpace α] [TopologicalSpace α] [NormalSpace α] [BorelSpace α]

variable (E : Type _) [NormedGroup E] [SecondCountableTopologyEither α E]

variable {p : ℝ≥0∞} [_i : Fact (1 ≤ p)] (hp : p ≠ ∞) (μ : Measureₓ α)

include _i hp

namespace MeasureTheory.lp

variable [NormedSpace ℝ E]

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (u «expr ⊇ » s)
-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (F «expr ⊆ » s)
/-- A function in `Lp` can be approximated in `Lp` by continuous functions. -/
theorem bounded_continuous_function_dense [μ.WeaklyRegular] :
    (boundedContinuousFunction E p μ).topologicalClosure = ⊤ := by
  have hp₀ : 0 < p := lt_of_lt_of_leₓ Ennreal.zero_lt_one _i.elim
  have hp₀' : 0 ≤ 1 / p.to_real := div_nonneg zero_le_one Ennreal.to_real_nonneg
  have hp₀'' : 0 < p.to_real := by
    simpa [Ennreal.to_real_lt_to_real Ennreal.zero_ne_top hp] using hp₀
  -- It suffices to prove that scalar multiples of the indicator function of a finite-measure
  -- measurable set can be approximated by continuous functions
  suffices
    ∀ (c : E) {s : Set α} (hs : MeasurableSet s) (hμs : μ s < ⊤),
      (Lp.simple_func.indicator_const p hs hμs.Ne c : Lp E p μ) ∈ (BoundedContinuousFunction E p μ).topologicalClosure
    by
    rw [AddSubgroup.eq_top_iff']
    refine' Lp.induction hp _ _ _ _
    · exact this
      
    · exact fun f g hf hg hfg' => AddSubgroup.add_mem _
      
    · exact AddSubgroup.is_closed_topological_closure _
      
  -- Let `s` be a finite-measure measurable set, let's approximate `c` times its indicator function
  intro c s hs hsμ
  refine' mem_closure_iff_frequently.mpr _
  rw [metric.nhds_basis_closed_ball.frequently_iff]
  intro ε hε
  -- A little bit of pre-emptive work, to find `η : ℝ≥0` which will be a margin small enough for
  -- our purposes
  obtain ⟨η, hη_pos, hη_le⟩ : ∃ η, 0 < η ∧ (↑(∥bit0 ∥c∥∥₊ * (2 * η) ^ (1 / p.to_real)) : ℝ) ≤ ε := by
    have : Filter.Tendsto (fun x : ℝ≥0 => ∥bit0 ∥c∥∥₊ * (2 * x) ^ (1 / p.to_real)) (𝓝 0) (𝓝 0) := by
      have : Filter.Tendsto (fun x : ℝ≥0 => 2 * x) (𝓝 0) (𝓝 (2 * 0)) := filter.tendsto_id.const_mul 2
      convert ((Nnreal.continuous_at_rpow_const (Or.inr hp₀')).Tendsto.comp this).const_mul _
      simp [← hp₀''.ne']
    let ε' : ℝ≥0 := ⟨ε, hε.le⟩
    have hε' : 0 < ε' := by
      exact_mod_cast hε
    obtain ⟨δ, hδ, hδε'⟩ := nnreal.nhds_zero_basis.eventually_iff.mp (eventually_le_of_tendsto_lt hε' this)
    obtain ⟨η, hη, hηδ⟩ := exists_between hδ
    refine' ⟨η, hη, _⟩
    exact_mod_cast hδε' hηδ
  have hη_pos' : (0 : ℝ≥0∞) < η := Ennreal.coe_pos.2 hη_pos
  -- Use the regularity of the measure to `η`-approximate `s` by an open superset and a closed
  -- subset
  obtain ⟨u, su, u_open, μu⟩ : ∃ (u : _)(_ : u ⊇ s), IsOpen u ∧ μ u < μ s + ↑η := by
    refine' s.exists_is_open_lt_of_lt _ _
    simpa using Ennreal.add_lt_add_left hsμ.ne hη_pos'
  obtain ⟨F, Fs, F_closed, μF⟩ : ∃ (F : _)(_ : F ⊆ s), IsClosed F ∧ μ s < μ F + ↑η :=
    hs.exists_is_closed_lt_add hsμ.ne hη_pos'.ne'
  have : Disjoint (uᶜ) F := (Fs.trans su).disjoint_compl_left
  have h_μ_sdiff : μ (u \ F) ≤ 2 * η := by
    have hFμ : μ F < ⊤ := (measure_mono Fs).trans_lt hsμ
    refine' Ennreal.le_of_add_le_add_left hFμ.ne _
    have : μ u < μ F + ↑η + ↑η := μu.trans (Ennreal.add_lt_add_right Ennreal.coe_ne_top μF)
    convert this.le using 1
    · rw [add_commₓ, ← measure_union, Set.diff_union_of_subset (Fs.trans su)]
      exacts[disjoint_sdiff_self_left, F_closed.measurable_set]
      
    have : (2 : ℝ≥0∞) * η = η + η := by
      simpa using add_mulₓ (1 : ℝ≥0∞) 1 η
    rw [this]
    abel
  -- Apply Urysohn's lemma to get a continuous approximation to the characteristic function of
  -- the set `s`
  obtain ⟨g, hgu, hgF, hg_range⟩ := exists_continuous_zero_one_of_closed u_open.is_closed_compl F_closed this
  -- Multiply this by `c` to get a continuous approximation to the function `f`; the key point is
  -- that this is pointwise bounded by the indicator of the set `u \ F`
  have g_norm : ∀ x, ∥g x∥ = g x := fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hg_range x).1]
  have gc_bd : ∀ x, ∥g x • c - s.indicator (fun x => c) x∥ ≤ ∥(u \ F).indicator (fun x => bit0 ∥c∥) x∥ := by
    intro x
    by_cases' hu : x ∈ u
    · rw [← Set.diff_union_of_subset (Fs.trans su)] at hu
      cases' hu with hFu hF
      · refine' (norm_sub_le _ _).trans _
        refine' (add_le_add_left (norm_indicator_le_norm_self (fun x => c) x) _).trans _
        have h₀ : g x * ∥c∥ + ∥c∥ ≤ 2 * ∥c∥ := by
          nlinarith [(hg_range x).1, (hg_range x).2, norm_nonneg c]
        have h₁ : (2 : ℝ) * ∥c∥ = bit0 ∥c∥ := by
          simpa using add_mulₓ (1 : ℝ) 1 ∥c∥
        simp [← hFu, ← norm_smul, ← h₀, h₁, ← g_norm x]
        
      · simp [← hgF hF, ← Fs hF]
        
      
    · have : x ∉ s := fun h => hu (su h)
      simp [← hgu hu, ← this]
      
  -- The rest is basically just `ennreal`-arithmetic
  have gc_snorm :
    snorm ((fun x => g x • c) - s.indicator fun x => c) p μ ≤ (↑(∥bit0 ∥c∥∥₊ * (2 * η) ^ (1 / p.to_real)) : ℝ≥0∞) := by
    refine' (snorm_mono_ae (Filter.eventually_of_forall gc_bd)).trans _
    rw [snorm_indicator_const (u_open.sdiff F_closed).MeasurableSet hp₀.ne' hp]
    push_cast [Ennreal.coe_rpow_of_nonneg _ hp₀']
    exact Ennreal.mul_left_mono (Ennreal.monotone_rpow_of_nonneg hp₀' h_μ_sdiff)
  have gc_cont : Continuous fun x => g x • c := g.continuous.smul continuous_const
  have gc_mem_ℒp : mem_ℒp (fun x => g x • c) p μ := by
    have : mem_ℒp ((fun x => g x • c) - s.indicator fun x => c) p μ :=
      ⟨gc_cont.ae_strongly_measurable.sub (strongly_measurable_const.indicator hs).AeStronglyMeasurable,
        gc_snorm.trans_lt Ennreal.coe_lt_top⟩
    simpa using this.add (mem_ℒp_indicator_const p hs c (Or.inr hsμ.ne))
  refine' ⟨gc_mem_ℒp.to_Lp _, _, _⟩
  · rw [mem_closed_ball_iff_norm]
    refine' le_transₓ _ hη_le
    rw [simple_func.coe_indicator_const, indicator_const_Lp, ← mem_ℒp.to_Lp_sub, Lp.norm_to_Lp]
    exact Ennreal.to_real_le_coe_of_le_coe gc_snorm
    
  · rw [SetLike.mem_coe, mem_bounded_continuous_function_iff]
    refine' ⟨BoundedContinuousFunction.ofNormedGroup _ gc_cont ∥c∥ _, rfl⟩
    intro x
    have h₀ : g x * ∥c∥ ≤ ∥c∥ := by
      nlinarith [(hg_range x).1, (hg_range x).2, norm_nonneg c]
    simp [← norm_smul, ← g_norm x, ← h₀]
    

end MeasureTheory.lp

variable (𝕜 : Type _) [NormedField 𝕜] [NormedAlgebra ℝ 𝕜] [NormedSpace 𝕜 E]

namespace BoundedContinuousFunction

theorem to_Lp_dense_range [μ.WeaklyRegular] [IsFiniteMeasure μ] : DenseRange ⇑(toLp p μ 𝕜 : (α →ᵇ E) →L[𝕜] lp E p μ) :=
  by
  have : NormedSpace ℝ E := RestrictScalars.normedSpace ℝ 𝕜 E
  rw [dense_range_iff_closure_range]
  suffices (to_Lp p μ 𝕜 : _ →L[𝕜] Lp E p μ).range.toAddSubgroup.topologicalClosure = ⊤ by
    exact congr_arg coe this
  simp [← range_to_Lp p μ, ← MeasureTheory.lp.bounded_continuous_function_dense E hp]

end BoundedContinuousFunction

namespace ContinuousMap

theorem to_Lp_dense_range [CompactSpace α] [μ.WeaklyRegular] [IsFiniteMeasure μ] :
    DenseRange ⇑(toLp p μ 𝕜 : C(α, E) →L[𝕜] lp E p μ) := by
  have : NormedSpace ℝ E := RestrictScalars.normedSpace ℝ 𝕜 E
  rw [dense_range_iff_closure_range]
  suffices (to_Lp p μ 𝕜 : _ →L[𝕜] Lp E p μ).range.toAddSubgroup.topologicalClosure = ⊤ by
    exact congr_arg coe this
  simp [← range_to_Lp p μ, ← MeasureTheory.lp.bounded_continuous_function_dense E hp]

end ContinuousMap

