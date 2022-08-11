/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathbin.Analysis.BoxIntegral.Basic
import Mathbin.MeasureTheory.Measure.Regular

/-!
# McShane integrability vs Bochner integrability

In this file we prove that any Bochner integrable function is McShane integrable (hence, it is
Henstock and `⊥` integrable) with the same integral. The proof is based on
[Russel A. Gordon, *The integrals of Lebesgue, Denjoy, Perron, and Henstock*][Gordon55].

## Tags

integral, McShane integral, Bochner integral
-/


open Classical Nnreal Ennreal TopologicalSpace BigOperators

universe u v

variable {ι : Type u} {E : Type v} [Fintype ι] [NormedGroup E] [NormedSpace ℝ E]

open MeasureTheory Metric Set Finset Filter BoxIntegral

namespace BoxIntegral

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (F «expr ⊆ » «expr ∩ »(s, I.Icc))
-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (U «expr ⊇ » «expr ∩ »(s, I.Icc))
/-- The indicator function of a measurable set is McShane integrable with respect to any
locally-finite measure. -/
theorem has_integral_indicator_const (l : IntegrationParams) (hl : l.bRiemann = ff) {s : Set (ι → ℝ)}
    (hs : MeasurableSet s) (I : Box ι) (y : E) (μ : Measureₓ (ι → ℝ)) [IsLocallyFiniteMeasure μ] :
    HasIntegral.{u, v, v} I l (s.indicator fun _ => y) μ.toBoxAdditive.toSmul ((μ (s ∩ I)).toReal • y) := by
  refine' has_integral_of_mul ∥y∥ fun ε ε0 => _
  lift ε to ℝ≥0 using ε0.le
  rw [Nnreal.coe_pos] at ε0
  /- First we choose a closed set `F ⊆ s ∩ I.Icc` and an open set `U ⊇ s` such that
    both `(s ∩ I.Icc) \ F` and `U \ s` have measuer less than `ε`. -/
  have A : μ (s ∩ I.Icc) ≠ ∞ := ((measure_mono <| Set.inter_subset_right _ _).trans_lt (I.measure_Icc_lt_top μ)).Ne
  have B : μ (s ∩ I) ≠ ∞ := ((measure_mono <| Set.inter_subset_right _ _).trans_lt (I.measure_coe_lt_top μ)).Ne
  obtain ⟨F, hFs, hFc, hμF⟩ : ∃ (F : _)(_ : F ⊆ s ∩ I.Icc), IsClosed F ∧ μ ((s ∩ I.Icc) \ F) < ε
  exact (hs.inter I.measurable_set_Icc).exists_is_closed_diff_lt A (Ennreal.coe_pos.2 ε0).ne'
  obtain ⟨U, hsU, hUo, hUt, hμU⟩ : ∃ (U : _)(_ : U ⊇ s ∩ I.Icc), IsOpen U ∧ μ U < ∞ ∧ μ (U \ (s ∩ I.Icc)) < ε
  exact (hs.inter I.measurable_set_Icc).exists_is_open_diff_lt A (Ennreal.coe_pos.2 ε0).ne'
  /- Then we choose `r` so that `closed_ball x (r x) ⊆ U` whenever `x ∈ s ∩ I.Icc` and
    `closed_ball x (r x)` is disjoint with `F` otherwise. -/
  have : ∀, ∀ x ∈ s ∩ I.Icc, ∀, ∃ r : Ioi (0 : ℝ), closed_ball x r ⊆ U := fun x hx =>
    Subtype.exists'.1 (nhds_basis_closed_ball.mem_iff.1 (hUo.mem_nhds <| hsU hx))
  choose! rs hrsU
  have : ∀, ∀ x ∈ I.Icc \ s, ∀, ∃ r : Ioi (0 : ℝ), closed_ball x r ⊆ Fᶜ := fun x hx =>
    Subtype.exists'.1 (nhds_basis_closed_ball.mem_iff.1 (hFc.is_open_compl.mem_nhds fun hx' => hx.2 (hFs hx').1))
  choose! rs' hrs'F
  set r : (ι → ℝ) → Ioi (0 : ℝ) := s.piecewise rs rs'
  refine' ⟨fun c => r, fun c => l.r_cond_of_bRiemann_eq_ff hl, fun c π hπ hπp => _⟩
  rw [mul_comm]
  /- Then the union of boxes `J ∈ π` such that `π.tag ∈ s` includes `F` and is included by `U`,
    hence its measure is `ε`-close to the measure of `s`. -/
  dsimp' [← integral_sum]
  simp only [← mem_closed_ball, ← dist_eq_norm, indicator_const_smul_apply, ← sum_indicator_eq_sum_filter, sum_smul,
    sub_smul, ← norm_smul, ← Real.norm_eq_abs, prepartition.filter_boxes, prepartition.measure_Union_to_real]
  refine' mul_le_mul_of_nonneg_right _ (norm_nonneg y)
  set t := (π.to_prepartition.filter fun J => π.tag J ∈ s).Union
  change abs ((μ t).toReal - (μ (s ∩ I)).toReal) ≤ ε
  have htU : t ⊆ U ∩ I := by
    simp only [← t, ← prepartition.Union_def, ← Union_subset_iff, ← prepartition.mem_filter, ← and_imp]
    refine' fun J hJ hJs x hx => ⟨hrsU _ ⟨hJs, π.tag_mem_Icc J⟩ _, π.le_of_mem' J hJ hx⟩
    simpa only [← r, ← s.piecewise_eq_of_mem _ _ hJs] using hπ.1 J hJ (box.coe_subset_Icc hx)
  refine' abs_sub_le_iff.2 ⟨_, _⟩
  · refine' (Ennreal.le_to_real_sub B).trans (Ennreal.to_real_le_coe_of_le_coe _)
    refine' (tsub_le_tsub (measure_mono htU) le_rfl).trans (le_measure_diff.trans _)
    refine' (measure_mono fun x hx => _).trans hμU.le
    exact ⟨hx.1.1, fun hx' => hx.2 ⟨hx'.1, hx.1.2⟩⟩
    
  · have hμt : μ t ≠ ∞ := ((measure_mono (htU.trans (inter_subset_left _ _))).trans_lt hUt).Ne
    refine' (Ennreal.le_to_real_sub hμt).trans (Ennreal.to_real_le_coe_of_le_coe _)
    refine' le_measure_diff.trans ((measure_mono _).trans hμF.le)
    rintro x ⟨⟨hxs, hxI⟩, hxt⟩
    refine' ⟨⟨hxs, box.coe_subset_Icc hxI⟩, fun hxF => hxt _⟩
    simp only [← t, ← prepartition.Union_def, ← prepartition.mem_filter, ← Set.mem_Union, ← exists_prop]
    rcases hπp x hxI with ⟨J, hJπ, hxJ⟩
    refine' ⟨J, ⟨hJπ, _⟩, hxJ⟩
    contrapose hxF
    refine' hrs'F _ ⟨π.tag_mem_Icc J, hxF⟩ _
    simpa only [← r, ← s.piecewise_eq_of_not_mem _ _ hxF] using hπ.1 J hJπ (box.coe_subset_Icc hxJ)
    

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (U «expr ⊇ » «expr ⁻¹' »(N, {n}))
/-- If `f` is a.e. equal to zero on a rectangular box, then it has McShane integral zero on this
box. -/
theorem has_integral_zero_of_ae_eq_zero {l : IntegrationParams} {I : Box ι} {f : (ι → ℝ) → E} {μ : Measureₓ (ι → ℝ)}
    [IsLocallyFiniteMeasure μ] (hf : f =ᵐ[μ.restrict I] 0) (hl : l.bRiemann = ff) :
    HasIntegral.{u, v, v} I l f μ.toBoxAdditive.toSmul 0 := by
  /- Each set `{x | n < ∥f x∥ ≤ n + 1}`, `n : ℕ`, has measure zero. We cover it by an open set of
    measure less than `ε / 2 ^ n / (n + 1)`. Then the norm of the integral sum is less than `ε`. -/
  refine' has_integral_iff.2 fun ε ε0 => _
  lift ε to ℝ≥0 using ε0.lt.le
  rw [gt_iff_lt, Nnreal.coe_pos] at ε0
  rcases Nnreal.exists_pos_sum_of_encodable ε0.ne' ℕ with ⟨δ, δ0, c, hδc, hcε⟩
  have := Fact.mk (I.measure_coe_lt_top μ)
  change μ.restrict I { x | f x ≠ 0 } = 0 at hf
  set N : (ι → ℝ) → ℕ := fun x => ⌈∥f x∥⌉₊
  have N0 : ∀ {x}, N x = 0 ↔ f x = 0 := by
    intro x
    simp [← N]
  have : ∀ n, ∃ (U : _)(_ : U ⊇ N ⁻¹' {n}), IsOpen U ∧ μ.restrict I U < δ n / n := by
    refine' fun n => (N ⁻¹' {n}).exists_is_open_lt_of_lt _ _
    cases n
    · simpa [← Ennreal.div_zero (Ennreal.coe_pos.2 (δ0 _)).ne'] using measure_lt_top (μ.restrict I) _
      
    · refine' (measure_mono_null _ hf).le.trans_lt _
      · exact fun x hxN hxf => n.succ_ne_zero ((Eq.symm hxN).trans <| N0.2 hxf)
        
      · simp [← (δ0 _).ne']
        
      
  choose U hNU hUo hμU
  have : ∀ x, ∃ r : Ioi (0 : ℝ), closed_ball x r ⊆ U (N x) := fun x =>
    Subtype.exists'.1 (nhds_basis_closed_ball.mem_iff.1 ((hUo _).mem_nhds (hNU _ rfl)))
  choose r hrU
  refine' ⟨fun _ => r, fun c => l.r_cond_of_bRiemann_eq_ff hl, fun c π hπ hπp => _⟩
  rw [dist_eq_norm, sub_zero, ← integral_sum_fiberwise fun J => N (π.tag J)]
  refine' le_transₓ _ (Nnreal.coe_lt_coe.2 hcε).le
  refine' (norm_sum_le_of_le _ _).trans (sum_le_has_sum _ (fun n _ => (δ n).2) (Nnreal.has_sum_coe.2 hδc))
  rintro n -
  dsimp' [← integral_sum]
  have : ∀, ∀ J ∈ π.filter fun J => N (π.tag J) = n, ∀, ∥(μ ↑J).toReal • f (π.tag J)∥ ≤ (μ J).toReal * n := by
    intro J hJ
    rw [tagged_prepartition.mem_filter] at hJ
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg Ennreal.to_real_nonneg]
    exact mul_le_mul_of_nonneg_left (hJ.2 ▸ Nat.le_ceil _) Ennreal.to_real_nonneg
  refine' (norm_sum_le_of_le _ this).trans _
  clear this
  rw [← sum_mul, ← prepartition.measure_Union_to_real]
  generalize hm : μ (π.filter fun J => N (π.tag J) = n).Union = m
  have : m < δ n / n := by
    simp only [← measure.restrict_apply (hUo _).MeasurableSet] at hμU
    refine' hm ▸ (measure_mono _).trans_lt (hμU _)
    simp only [← Set.subset_def, ← tagged_prepartition.mem_Union, ← exists_prop, ← tagged_prepartition.mem_filter]
    rintro x ⟨J, ⟨hJ, rfl⟩, hx⟩
    exact ⟨hrU _ (hπ.1 _ hJ (box.coe_subset_Icc hx)), π.le_of_mem' J hJ hx⟩
  lift m to ℝ≥0 using ne_top_of_lt this
  rw [Ennreal.coe_to_real, ← Nnreal.coe_nat_cast, ← Nnreal.coe_mul, Nnreal.coe_le_coe, ← Ennreal.coe_le_coe,
    Ennreal.coe_mul, Ennreal.coe_nat, mul_comm]
  exact (mul_le_mul_left' this.le _).trans Ennreal.mul_div_le

/-- If `f` has integral `y` on a box `I` with respect to a locally finite measure `μ` and `g` is
a.e. equal to `f` on `I`, then `g` has the same integral on `I`.  -/
theorem HasIntegral.congr_ae {l : IntegrationParams} {I : Box ι} {y : E} {f g : (ι → ℝ) → E} {μ : Measureₓ (ι → ℝ)}
    [IsLocallyFiniteMeasure μ] (hf : HasIntegral.{u, v, v} I l f μ.toBoxAdditive.toSmul y) (hfg : f =ᵐ[μ.restrict I] g)
    (hl : l.bRiemann = ff) : HasIntegral.{u, v, v} I l g μ.toBoxAdditive.toSmul y := by
  have : g - f =ᵐ[μ.restrict I] 0 := hfg.mono fun x hx => sub_eq_zero.2 hx.symm
  simpa using hf.add (has_integral_zero_of_ae_eq_zero this hl)

end BoxIntegral

namespace MeasureTheory

namespace SimpleFunc

-- ./././Mathport/Syntax/Translate/Basic.lean:647:16: unsupported tactic `borelize #[[expr E]]
/-- A simple function is McShane integrable w.r.t. any locally finite measure. -/
theorem has_box_integral (f : SimpleFunc (ι → ℝ) E) (μ : Measure (ι → ℝ)) [IsLocallyFiniteMeasure μ] (I : Box ι)
    (l : IntegrationParams) (hl : l.bRiemann = ff) :
    HasIntegral.{u, v, v} I l f μ.toBoxAdditive.toSmul (f.integral (μ.restrict I)) := by
  induction' f using MeasureTheory.SimpleFunc.induction with y s hs f g hd hfi hgi
  · simpa [← Function.const, ← measure.restrict_apply hs] using BoxIntegral.has_integral_indicator_const l hl hs I y μ
    
  · trace "./././Mathport/Syntax/Translate/Basic.lean:647:16: unsupported tactic `borelize #[[expr E]]"
    have := Fact.mk (I.measure_coe_lt_top μ)
    rw [integral_add]
    exacts[hfi.add hgi, integrable_iff.2 fun _ _ => measure_lt_top _ _, integrable_iff.2 fun _ _ => measure_lt_top _ _]
    

/-- For a simple function, its McShane (or Henstock, or `⊥`) box integral is equal to its
integral in the sense of `measure_theory.simple_func.integral`. -/
theorem box_integral_eq_integral (f : SimpleFunc (ι → ℝ) E) (μ : Measure (ι → ℝ)) [IsLocallyFiniteMeasure μ] (I : Box ι)
    (l : IntegrationParams) (hl : l.bRiemann = ff) :
    BoxIntegral.integral.{u, v, v} I l f μ.toBoxAdditive.toSmul = f.integral (μ.restrict I) :=
  (f.has_box_integral μ I l hl).integral_eq

end SimpleFunc

open TopologicalSpace

-- ./././Mathport/Syntax/Translate/Basic.lean:647:16: unsupported tactic `borelize #[[expr E]]
/-- If `f : ℝⁿ → E` is Bochner integrable w.r.t. a locally finite measure `μ` on a rectangular box
`I`, then it is McShane integrable on `I` with the same integral.  -/
theorem IntegrableOn.has_box_integral [CompleteSpace E] {f : (ι → ℝ) → E} {μ : Measure (ι → ℝ)}
    [IsLocallyFiniteMeasure μ] {I : Box ι} (hf : IntegrableOn f I μ) (l : IntegrationParams) (hl : l.bRiemann = ff) :
    HasIntegral.{u, v, v} I l f μ.toBoxAdditive.toSmul (∫ x in I, f x ∂μ) := by
  trace "./././Mathport/Syntax/Translate/Basic.lean:647:16: unsupported tactic `borelize #[[expr E]]"
  -- First we replace an `ae_strongly_measurable` function by a measurable one.
  rcases hf.ae_strongly_measurable with ⟨g, hg, hfg⟩
  have : separable_space (range g ∪ {0} : Set E) := hg.separable_space_range_union_singleton
  rw [integral_congr_ae hfg]
  have hgi : integrable_on g I μ := (integrable_congr hfg).1 hf
  refine' BoxIntegral.HasIntegral.congr_ae _ hfg.symm hl
  clear! f
  /- Now consider the sequence of simple functions
    `simple_func.approx_on g hg.measurable (range g ∪ {0}) 0 (by simp)`
    approximating `g`. Recall some properties of this sequence. -/
  set f : ℕ → simple_func (ι → ℝ) E :=
    simple_func.approx_on g hg.measurable (range g ∪ {0}) 0
      (by
        simp )
  have hfi : ∀ n, integrable_on (f n) I μ := simple_func.integrable_approx_on_range hg.measurable hgi
  have hfi' := fun n => ((f n).has_box_integral μ I l hl).Integrable
  have hfgi : tendsto (fun n => (f n).integral (μ.restrict I)) at_top (𝓝 <| ∫ x in I, g x ∂μ) :=
    tendsto_integral_approx_on_of_measurable_of_range_subset hg.measurable hgi _ subset.rfl
  have hfg_mono : ∀ (x) {m n}, m ≤ n → ∥f n x - g x∥ ≤ ∥f m x - g x∥ := by
    intro x m n hmn
    rw [← dist_eq_norm, ← dist_eq_norm, dist_nndist, dist_nndist, Nnreal.coe_le_coe, ← Ennreal.coe_le_coe, ←
      edist_nndist, ← edist_nndist]
    exact simple_func.edist_approx_on_mono hg.measurable _ x hmn
  /- Now consider `ε > 0`. We need to find `r` such that for any tagged partition subordinate
    to `r`, the integral sum is `(μ I + 1 + 1) * ε`-close to the Bochner integral. -/
  refine' has_integral_of_mul ((μ I).toReal + 1 + 1) fun ε ε0 => _
  lift ε to ℝ≥0 using ε0.le
  rw [Nnreal.coe_pos] at ε0
  have ε0' := Ennreal.coe_pos.2 ε0
  -- Choose `N` such that the integral of `∥f N x - g x∥` is less than or equal to `ε`.
  obtain ⟨N₀, hN₀⟩ : ∃ N : ℕ, (∫ x in I, ∥f N x - g x∥ ∂μ) ≤ ε := by
    have : tendsto (fun n => ∫⁻ x in I, ∥f n x - g x∥₊ ∂μ) at_top (𝓝 0) :=
      simple_func.tendsto_approx_on_range_L1_nnnorm hg.measurable hgi
    refine' (this.eventually (ge_mem_nhds ε0')).exists.imp fun N hN => _
    exact integral_coe_le_of_lintegral_coe_le hN
  -- For each `x`, we choose `Nx x ≥ N₀` such that `dist (f Nx x) (g x) ≤ ε`.
  have : ∀ x, ∃ N₁, N₀ ≤ N₁ ∧ dist (f N₁ x) (g x) ≤ ε := by
    intro x
    have : tendsto (fun n => f n x) at_top (𝓝 <| g x) :=
      simple_func.tendsto_approx_on hg.measurable _
        (subset_closure
          (by
            simp ))
    exact ((eventually_ge_at_top N₀).And <| this <| closed_ball_mem_nhds _ ε0).exists
  choose Nx hNx hNxε
  -- We also choose a convergent series with `∑' i : ℕ, δ i < ε`.
  rcases Nnreal.exists_pos_sum_of_encodable ε0.ne' ℕ with ⟨δ, δ0, c, hδc, hcε⟩
  /- Since each simple function `fᵢ` is integrable, there exists `rᵢ : ℝⁿ → (0, ∞)` such that
    the integral sum of `f` over any tagged prepartition is `δᵢ`-close to the sum of integrals
    of `fᵢ` over the boxes of this prepartition. For each `x`, we choose `r (Nx x)` as the radius
    at `x`. -/
  set r : ℝ≥0 → (ι → ℝ) → Ioi (0 : ℝ) := fun c x => (hfi' <| Nx x).convergenceR (δ <| Nx x) c x
  refine' ⟨r, fun c => l.r_cond_of_bRiemann_eq_ff hl, fun c π hπ hπp => _⟩
  /- Now we prove the estimate in 3 "jumps": first we replace `g x` in the formula for the
    integral sum by `f (Nx x)`; then we replace each `μ J • f (Nx (π.tag J)) (π.tag J)`
    by the Bochner integral of `f (Nx (π.tag J)) x` over `J`, then we jump to the Bochner
    integral of `g`. -/
  refine'
    (dist_triangle4 _ (∑ J in π.boxes, (μ J).toReal • f (Nx <| π.tag J) (π.tag J))
          (∑ J in π.boxes, ∫ x in J, f (Nx <| π.tag J) x ∂μ) _).trans
      _
  rw [add_mulₓ, add_mulₓ, one_mulₓ]
  refine' add_le_add_three _ _ _
  · /- Since each `f (Nx $ π.tag J)` is `ε`-close to `g (π.tag J)`, replacing the latter with
        the former in the formula for the integral sum changes the sum at most by `μ I * ε`. -/
    rw [← hπp.Union_eq, π.to_prepartition.measure_Union_to_real, sum_mul, integral_sum]
    refine' dist_sum_sum_le_of_le _ fun J hJ => _
    dsimp'
    rw [dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg Ennreal.to_real_nonneg]
    refine' mul_le_mul_of_nonneg_left _ Ennreal.to_real_nonneg
    rw [← dist_eq_norm']
    exact hNxε _
    
  · /- We group the terms of both sums by the values of `Nx (π.tag J)`.
        For each `N`, the sum of Bochner integrals over the boxes is equal
        to the sum of box integrals, and the sum of box integrals is `δᵢ`-close
        to the corresponding integral sum due to the Henstock-Sacks inequality. -/
    rw [← π.to_prepartition.sum_fiberwise fun J => Nx (π.tag J), ←
      π.to_prepartition.sum_fiberwise fun J => Nx (π.tag J)]
    refine' le_transₓ _ (Nnreal.coe_lt_coe.2 hcε).le
    refine'
      (dist_sum_sum_le_of_le _ fun n hn => _).trans (sum_le_has_sum _ (fun n _ => (δ n).2) (Nnreal.has_sum_coe.2 hδc))
    have hNxn : ∀, ∀ J ∈ π.filter fun J => Nx (π.tag J) = n, ∀, Nx (π.tag J) = n := fun J hJ => (π.mem_filter.1 hJ).2
    have hrn :
      ∀, ∀ J ∈ π.filter fun J => Nx (π.tag J) = n, ∀, r c (π.tag J) = (hfi' n).convergenceR (δ n) c (π.tag J) := by
      intro J hJ
      obtain rfl := hNxn J hJ
      rfl
    have : l.mem_base_set I c ((hfi' n).convergenceR (δ n) c) (π.filter fun J => Nx (π.tag J) = n) :=
      (hπ.filter _).mono' _ le_rfl le_rfl fun J hJ => (hrn J hJ).le
    convert (hfi' n).dist_integral_sum_sum_integral_le_of_mem_base_set (δ0 _) this using 2
    · refine' sum_congr rfl fun J hJ => _
      simp [← hNxn J hJ]
      
    · refine' sum_congr rfl fun J hJ => _
      rw [← simple_func.integral_eq_integral, simple_func.box_integral_eq_integral _ _ _ _ hl, hNxn J hJ]
      exact (hfi _).mono_set (prepartition.le_of_mem _ hJ)
      
    
  · /-  For the last jump, we use the fact that the distance between `f (Nx x) x` and `g x` is less
        than or equal to the distance between `f N₀ x` and `g x` and the integral of `∥f N₀ x - g x∥`
        is less than or equal to `ε`. -/
    refine' le_transₓ _ hN₀
    have hfi : ∀ (n), ∀ J ∈ π, ∀, integrable_on (f n) (↑J) μ := fun n J hJ => (hfi n).mono_set (π.le_of_mem' J hJ)
    have hgi : ∀, ∀ J ∈ π, ∀, integrable_on g (↑J) μ := fun J hJ => hgi.mono_set (π.le_of_mem' J hJ)
    have hfgi : ∀ (n), ∀ J ∈ π, ∀, integrable_on (fun x => ∥f n x - g x∥) J μ := fun n J hJ =>
      ((hfi n J hJ).sub (hgi J hJ)).norm
    rw [← hπp.Union_eq, prepartition.Union_def',
      integral_finset_bUnion π.boxes (fun J hJ => J.measurable_set_coe) π.pairwise_disjoint hgi,
      integral_finset_bUnion π.boxes (fun J hJ => J.measurable_set_coe) π.pairwise_disjoint (hfgi _)]
    refine' dist_sum_sum_le_of_le _ fun J hJ => _
    rw [dist_eq_norm, ← integral_sub (hfi _ J hJ) (hgi J hJ)]
    refine' norm_integral_le_of_norm_le (hfgi _ J hJ) (eventually_of_forall fun x => _)
    exact hfg_mono x (hNx (π.tag J))
    

end MeasureTheory

