/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathbin.Topology.MetricSpace.Baire
import Mathbin.Analysis.NormedSpace.OperatorNorm
import Mathbin.Analysis.NormedSpace.AffineIsometry

/-!
# Banach open mapping theorem

This file contains the Banach open mapping theorem, i.e., the fact that a bijective
bounded linear map between Banach spaces has a bounded inverse.
-/


open Function Metric Set Filter Finset

open Classical TopologicalSpace BigOperators Nnreal

variable {𝕜 : Type _} [NondiscreteNormedField 𝕜] {E : Type _} [NormedGroup E] [NormedSpace 𝕜 E] {F : Type _}
  [NormedGroup F] [NormedSpace 𝕜 F] (f : E →L[𝕜] F)

include 𝕜

namespace ContinuousLinearMap

/-- A (possibly nonlinear) right inverse to a continuous linear map, which doesn't have to be
linear itself but which satisfies a bound `∥inverse x∥ ≤ C * ∥x∥`. A surjective continuous linear
map doesn't always have a continuous linear right inverse, but it always has a nonlinear inverse
in this sense, by Banach's open mapping theorem. -/
structure NonlinearRightInverse where
  toFun : F → E
  nnnorm : ℝ≥0
  bound' : ∀ y, ∥to_fun y∥ ≤ nnnorm * ∥y∥
  right_inv' : ∀ y, f (to_fun y) = y

instance : CoeFun (NonlinearRightInverse f) fun _ => F → E :=
  ⟨fun fsymm => fsymm.toFun⟩

@[simp]
theorem NonlinearRightInverse.right_inv {f : E →L[𝕜] F} (fsymm : NonlinearRightInverse f) (y : F) : f (fsymm y) = y :=
  fsymm.right_inv' y

theorem NonlinearRightInverse.bound {f : E →L[𝕜] F} (fsymm : NonlinearRightInverse f) (y : F) :
    ∥fsymm y∥ ≤ fsymm.nnnorm * ∥y∥ :=
  fsymm.bound' y

end ContinuousLinearMap

/-- Given a continuous linear equivalence, the inverse is in particular an instance of
`nonlinear_right_inverse` (which turns out to be linear). -/
noncomputable def ContinuousLinearEquiv.toNonlinearRightInverse (f : E ≃L[𝕜] F) :
    ContinuousLinearMap.NonlinearRightInverse (f : E →L[𝕜] F) where
  toFun := f.invFun
  nnnorm := ∥(f.symm : F →L[𝕜] E)∥₊
  bound' := fun y => ContinuousLinearMap.le_op_norm (f.symm : F →L[𝕜] E) _
  right_inv' := f.apply_symm_apply

noncomputable instance (f : E ≃L[𝕜] F) : Inhabited (ContinuousLinearMap.NonlinearRightInverse (f : E →L[𝕜] F)) :=
  ⟨f.toNonlinearRightInverse⟩

/-! ### Proof of the Banach open mapping theorem -/


variable [CompleteSpace F]

namespace ContinuousLinearMap

/-- First step of the proof of the Banach open mapping theorem (using completeness of `F`):
by Baire's theorem, there exists a ball in `E` whose image closure has nonempty interior.
Rescaling everything, it follows that any `y ∈ F` is arbitrarily well approached by
images of elements of norm at most `C * ∥y∥`.
For further use, we will only need such an element whose image
is within distance `∥y∥/2` of `y`, to apply an iterative process. -/
theorem exists_approx_preimage_norm_le (surj : Surjective f) :
    ∃ C ≥ 0, ∀ y, ∃ x, dist (f x) y ≤ 1 / 2 * ∥y∥ ∧ ∥x∥ ≤ C * ∥y∥ := by
  have A : (⋃ n : ℕ, Closure (f '' ball 0 n)) = univ := by
    refine' subset.antisymm (subset_univ _) fun y hy => _
    rcases surj y with ⟨x, hx⟩
    rcases exists_nat_gt ∥x∥ with ⟨n, hn⟩
    refine' mem_Union.2 ⟨n, subset_closure _⟩
    refine' (mem_image _ _ _).2 ⟨x, ⟨_, hx⟩⟩
    rwa [mem_ball, dist_eq_norm, sub_zero]
  have : ∃ (n : ℕ)(x : _), x ∈ Interior (Closure (f '' ball 0 n)) :=
    nonempty_interior_of_Union_of_closed (fun n => is_closed_closure) A
  simp only [← mem_interior_iff_mem_nhds, ← Metric.mem_nhds_iff] at this
  rcases this with ⟨n, a, ε, ⟨εpos, H⟩⟩
  rcases NormedField.exists_one_lt_norm 𝕜 with ⟨c, hc⟩
  refine' ⟨(ε / 2)⁻¹ * ∥c∥ * 2 * n, _, fun y => _⟩
  · refine'
      mul_nonneg
        (mul_nonneg (mul_nonneg _ (norm_nonneg _))
          (by
            norm_num))
        _
    exacts[inv_nonneg.2
        (div_nonneg (le_of_ltₓ εpos)
          (by
            norm_num)),
      n.cast_nonneg]
    
  · by_cases' hy : y = 0
    · use 0
      simp [← hy]
      
    · rcases rescale_to_shell hc (half_pos εpos) hy with ⟨d, hd, ydlt, leyd, dinv⟩
      let δ := ∥d∥ * ∥y∥ / 4
      have δpos : 0 < δ :=
        div_pos (mul_pos (norm_pos_iff.2 hd) (norm_pos_iff.2 hy))
          (by
            norm_num)
      have : a + d • y ∈ ball a ε := by
        simp [← dist_eq_norm, ← lt_of_le_of_ltₓ ydlt.le (half_lt_self εpos)]
      rcases Metric.mem_closure_iff.1 (H this) _ δpos with ⟨z₁, z₁im, h₁⟩
      rcases(mem_image _ _ _).1 z₁im with ⟨x₁, hx₁, xz₁⟩
      rw [← xz₁] at h₁
      rw [mem_ball, dist_eq_norm, sub_zero] at hx₁
      have : a ∈ ball a ε := by
        simp
        exact εpos
      rcases Metric.mem_closure_iff.1 (H this) _ δpos with ⟨z₂, z₂im, h₂⟩
      rcases(mem_image _ _ _).1 z₂im with ⟨x₂, hx₂, xz₂⟩
      rw [← xz₂] at h₂
      rw [mem_ball, dist_eq_norm, sub_zero] at hx₂
      let x := x₁ - x₂
      have I : ∥f x - d • y∥ ≤ 2 * δ :=
        calc
          ∥f x - d • y∥ = ∥f x₁ - (a + d • y) - (f x₂ - a)∥ := by
            congr 1
            simp only [← x, ← f.map_sub]
            abel
          _ ≤ ∥f x₁ - (a + d • y)∥ + ∥f x₂ - a∥ := norm_sub_le _ _
          _ ≤ δ + δ := by
            apply add_le_add
            · rw [← dist_eq_norm, dist_comm]
              exact le_of_ltₓ h₁
              
            · rw [← dist_eq_norm, dist_comm]
              exact le_of_ltₓ h₂
              
          _ = 2 * δ := (two_mul _).symm
          
      have J : ∥f (d⁻¹ • x) - y∥ ≤ 1 / 2 * ∥y∥ :=
        calc
          ∥f (d⁻¹ • x) - y∥ = ∥d⁻¹ • f x - (d⁻¹ * d) • y∥ := by
            rwa [f.map_smul _, inv_mul_cancel, one_smul]
          _ = ∥d⁻¹ • (f x - d • y)∥ := by
            rw [mul_smul, smul_sub]
          _ = ∥d∥⁻¹ * ∥f x - d • y∥ := by
            rw [norm_smul, norm_inv]
          _ ≤ ∥d∥⁻¹ * (2 * δ) := by
            apply mul_le_mul_of_nonneg_left I
            rw [inv_nonneg]
            exact norm_nonneg _
          _ = ∥d∥⁻¹ * ∥d∥ * ∥y∥ / 2 := by
            simp only [← δ]
            ring
          _ = ∥y∥ / 2 := by
            rw [inv_mul_cancel, one_mulₓ]
            simp [← norm_eq_zero, ← hd]
          _ = 1 / 2 * ∥y∥ := by
            ring
          
      rw [← dist_eq_norm] at J
      have K : ∥d⁻¹ • x∥ ≤ (ε / 2)⁻¹ * ∥c∥ * 2 * ↑n * ∥y∥ :=
        calc
          ∥d⁻¹ • x∥ = ∥d∥⁻¹ * ∥x₁ - x₂∥ := by
            rw [norm_smul, norm_inv]
          _ ≤ (ε / 2)⁻¹ * ∥c∥ * ∥y∥ * (n + n) := by
            refine' mul_le_mul dinv _ (norm_nonneg _) _
            · exact le_transₓ (norm_sub_le _ _) (add_le_add (le_of_ltₓ hx₁) (le_of_ltₓ hx₂))
              
            · apply mul_nonneg (mul_nonneg _ (norm_nonneg _)) (norm_nonneg _)
              exact inv_nonneg.2 (le_of_ltₓ (half_pos εpos))
              
          _ = (ε / 2)⁻¹ * ∥c∥ * 2 * ↑n * ∥y∥ := by
            ring
          
      exact ⟨d⁻¹ • x, J, K⟩
      
    

variable [CompleteSpace E]

/-- The Banach open mapping theorem: if a bounded linear map between Banach spaces is onto, then
any point has a preimage with controlled norm. -/
theorem exists_preimage_norm_le (surj : Surjective f) : ∃ C > 0, ∀ y, ∃ x, f x = y ∧ ∥x∥ ≤ C * ∥y∥ := by
  obtain ⟨C, C0, hC⟩ := exists_approx_preimage_norm_le f surj
  /- Second step of the proof: starting from `y`, we want an exact preimage of `y`. Let `g y` be
    the approximate preimage of `y` given by the first step, and `h y = y - f(g y)` the part that
    has no preimage yet. We will iterate this process, taking the approximate preimage of `h y`,
    leaving only `h^2 y` without preimage yet, and so on. Let `u n` be the approximate preimage
    of `h^n y`. Then `u` is a converging series, and by design the sum of the series is a
    preimage of `y`. This uses completeness of `E`. -/
  choose g hg using hC
  let h := fun y => y - f (g y)
  have hle : ∀ y, ∥h y∥ ≤ 1 / 2 * ∥y∥ := by
    intro y
    rw [← dist_eq_norm, dist_comm]
    exact (hg y).1
  refine'
    ⟨2 * C + 1, by
      linarith, fun y => _⟩
  have hnle : ∀ n : ℕ, ∥(h^[n]) y∥ ≤ (1 / 2) ^ n * ∥y∥ := by
    intro n
    induction' n with n IH
    · simp only [← one_div, ← Nat.nat_zero_eq_zero, ← one_mulₓ, ← iterate_zero_apply, ← pow_zeroₓ]
      
    · rw [iterate_succ']
      apply le_transₓ (hle _) _
      rw [pow_succₓ, mul_assoc]
      apply mul_le_mul_of_nonneg_left IH
      norm_num
      
  let u := fun n => g ((h^[n]) y)
  have ule : ∀ n, ∥u n∥ ≤ (1 / 2) ^ n * (C * ∥y∥) := by
    intro n
    apply le_transₓ (hg _).2 _
    calc C * ∥(h^[n]) y∥ ≤ C * ((1 / 2) ^ n * ∥y∥) :=
        mul_le_mul_of_nonneg_left (hnle n) C0 _ = (1 / 2) ^ n * (C * ∥y∥) := by
        ring
  have sNu : Summable fun n => ∥u n∥ := by
    refine' summable_of_nonneg_of_le (fun n => norm_nonneg _) ule _
    exact
      Summable.mul_right _
        (summable_geometric_of_lt_1
          (by
            norm_num)
          (by
            norm_num))
  have su : Summable u := summable_of_summable_norm sNu
  let x := tsum u
  have x_ineq : ∥x∥ ≤ (2 * C + 1) * ∥y∥ :=
    calc
      ∥x∥ ≤ ∑' n, ∥u n∥ := norm_tsum_le_tsum_norm sNu
      _ ≤ ∑' n, (1 / 2) ^ n * (C * ∥y∥) := tsum_le_tsum ule sNu (Summable.mul_right _ summable_geometric_two)
      _ = (∑' n, (1 / 2) ^ n) * (C * ∥y∥) := tsum_mul_right
      _ = 2 * C * ∥y∥ := by
        rw [tsum_geometric_two, mul_assoc]
      _ ≤ 2 * C * ∥y∥ + ∥y∥ := le_add_of_nonneg_right (norm_nonneg y)
      _ = (2 * C + 1) * ∥y∥ := by
        ring
      
  have fsumeq : ∀ n : ℕ, f (∑ i in Finset.range n, u i) = y - (h^[n]) y := by
    intro n
    induction' n with n IH
    · simp [← f.map_zero]
      
    · rw [sum_range_succ, f.map_add, IH, iterate_succ', sub_add]
      
  have : tendsto (fun n => ∑ i in Finset.range n, u i) at_top (𝓝 x) := su.has_sum.tendsto_sum_nat
  have L₁ : tendsto (fun n => f (∑ i in Finset.range n, u i)) at_top (𝓝 (f x)) := (f.continuous.tendsto _).comp this
  simp only [← fsumeq] at L₁
  have L₂ : tendsto (fun n => y - (h^[n]) y) at_top (𝓝 (y - 0)) := by
    refine' tendsto_const_nhds.sub _
    rw [tendsto_iff_norm_tendsto_zero]
    simp only [← sub_zero]
    refine' squeeze_zero (fun _ => norm_nonneg _) hnle _
    rw [← zero_mul ∥y∥]
    refine' (tendsto_pow_at_top_nhds_0_of_lt_1 _ _).mul tendsto_const_nhds <;> norm_num
  have feq : f x = y - 0 := tendsto_nhds_unique L₁ L₂
  rw [sub_zero] at feq
  exact ⟨x, feq, x_ineq⟩

/-- The Banach open mapping theorem: a surjective bounded linear map between Banach spaces is
open. -/
protected theorem is_open_map (surj : Surjective f) : IsOpenMap f := by
  intro s hs
  rcases exists_preimage_norm_le f surj with ⟨C, Cpos, hC⟩
  refine' is_open_iff.2 fun y yfs => _
  rcases mem_image_iff_bex.1 yfs with ⟨x, xs, fxy⟩
  rcases is_open_iff.1 hs x xs with ⟨ε, εpos, hε⟩
  refine' ⟨ε / C, div_pos εpos Cpos, fun z hz => _⟩
  rcases hC (z - y) with ⟨w, wim, wnorm⟩
  have : f (x + w) = z := by
    rw [f.map_add, wim, fxy, add_sub_cancel'_right]
  rw [← this]
  have : x + w ∈ ball x ε :=
    calc
      dist (x + w) x = ∥w∥ := by
        rw [dist_eq_norm]
        simp
      _ ≤ C * ∥z - y∥ := wnorm
      _ < C * (ε / C) := by
        apply mul_lt_mul_of_pos_left _ Cpos
        rwa [mem_ball, dist_eq_norm] at hz
      _ = ε := mul_div_cancel' _ (ne_of_gtₓ Cpos)
      
  exact Set.mem_image_of_mem _ (hε this)

protected theorem quotient_map (surj : Surjective f) : QuotientMap f :=
  (f.IsOpenMap surj).to_quotient_map f.Continuous surj

theorem _root_.affine_map.is_open_map {P Q : Type _} [MetricSpace P] [NormedAddTorsor E P] [MetricSpace Q]
    [NormedAddTorsor F Q] (f : P →ᵃ[𝕜] Q) (hf : Continuous f) (surj : Surjective f) : IsOpenMap f :=
  AffineMap.is_open_map_linear_iff.mp <|
    ContinuousLinearMap.is_open_map { f.linear with cont := AffineMap.continuous_linear_iff.mpr hf }
      (f.surjective_iff_linear_surjective.mpr surj)

/-! ### Applications of the Banach open mapping theorem -/


theorem interior_preimage (hsurj : Surjective f) (s : Set F) : Interior (f ⁻¹' s) = f ⁻¹' Interior s :=
  ((f.IsOpenMap hsurj).preimage_interior_eq_interior_preimage f.Continuous s).symm

theorem closure_preimage (hsurj : Surjective f) (s : Set F) : Closure (f ⁻¹' s) = f ⁻¹' Closure s :=
  ((f.IsOpenMap hsurj).preimage_closure_eq_closure_preimage f.Continuous s).symm

theorem frontier_preimage (hsurj : Surjective f) (s : Set F) : Frontier (f ⁻¹' s) = f ⁻¹' Frontier s :=
  ((f.IsOpenMap hsurj).preimage_frontier_eq_frontier_preimage f.Continuous s).symm

theorem exists_nonlinear_right_inverse_of_surjective (f : E →L[𝕜] F) (hsurj : f.range = ⊤) :
    ∃ fsymm : NonlinearRightInverse f, 0 < fsymm.nnnorm := by
  choose C hC fsymm h using exists_preimage_norm_le _ (linear_map.range_eq_top.mp hsurj)
  use { toFun := fsymm, nnnorm := ⟨C, hC.lt.le⟩, bound' := fun y => (h y).2, right_inv' := fun y => (h y).1 }
  exact hC

/-- A surjective continuous linear map between Banach spaces admits a (possibly nonlinear)
controlled right inverse. In general, it is not possible to ensure that such a right inverse
is linear (take for instance the map from `E` to `E/F` where `F` is a closed subspace of `E`
without a closed complement. Then it doesn't have a continuous linear right inverse.) -/
noncomputable irreducible_def nonlinearRightInverseOfSurjective (f : E →L[𝕜] F) (hsurj : f.range = ⊤) :
  NonlinearRightInverse f :=
  Classical.some (exists_nonlinear_right_inverse_of_surjective f hsurj)

theorem nonlinear_right_inverse_of_surjective_nnnorm_pos (f : E →L[𝕜] F) (hsurj : f.range = ⊤) :
    0 < (nonlinearRightInverseOfSurjective f hsurj).nnnorm := by
  rw [nonlinear_right_inverse_of_surjective]
  exact Classical.some_spec (exists_nonlinear_right_inverse_of_surjective f hsurj)

end ContinuousLinearMap

namespace LinearEquiv

variable [CompleteSpace E]

/-- If a bounded linear map is a bijection, then its inverse is also a bounded linear map. -/
@[continuity]
theorem continuous_symm (e : E ≃ₗ[𝕜] F) (h : Continuous e) : Continuous e.symm := by
  rw [continuous_def]
  intro s hs
  rw [← e.image_eq_preimage]
  rw [← e.coe_coe] at h⊢
  exact ContinuousLinearMap.is_open_map ⟨↑e, h⟩ e.surjective s hs

/-- Associating to a linear equivalence between Banach spaces a continuous linear equivalence when
the direct map is continuous, thanks to the Banach open mapping theorem that ensures that the
inverse map is also continuous. -/
def toContinuousLinearEquivOfContinuous (e : E ≃ₗ[𝕜] F) (h : Continuous e) : E ≃L[𝕜] F :=
  { e with continuous_to_fun := h, continuous_inv_fun := e.continuous_symm h }

@[simp]
theorem coe_fn_to_continuous_linear_equiv_of_continuous (e : E ≃ₗ[𝕜] F) (h : Continuous e) :
    ⇑(e.toContinuousLinearEquivOfContinuous h) = e :=
  rfl

@[simp]
theorem coe_fn_to_continuous_linear_equiv_of_continuous_symm (e : E ≃ₗ[𝕜] F) (h : Continuous e) :
    ⇑(e.toContinuousLinearEquivOfContinuous h).symm = e.symm :=
  rfl

end LinearEquiv

namespace ContinuousLinearEquiv

variable [CompleteSpace E]

/-- Convert a bijective continuous linear map `f : E →L[𝕜] F` from a Banach space to a normed space
to a continuous linear equivalence. -/
noncomputable def ofBijective (f : E →L[𝕜] F) (hinj : f.ker = ⊥) (hsurj : f.range = ⊤) : E ≃L[𝕜] F :=
  (LinearEquiv.ofBijective (↑f) (LinearMap.ker_eq_bot.mp hinj)
        (LinearMap.range_eq_top.mp hsurj)).toContinuousLinearEquivOfContinuous
    f.Continuous

@[simp]
theorem coe_fn_of_bijective (f : E →L[𝕜] F) (hinj : f.ker = ⊥) (hsurj : f.range = ⊤) :
    ⇑(ofBijective f hinj hsurj) = f :=
  rfl

theorem coe_of_bijective (f : E →L[𝕜] F) (hinj : f.ker = ⊥) (hsurj : f.range = ⊤) : ↑(ofBijective f hinj hsurj) = f :=
  by
  ext
  rfl

@[simp]
theorem of_bijective_symm_apply_apply (f : E →L[𝕜] F) (hinj : f.ker = ⊥) (hsurj : f.range = ⊤) (x : E) :
    (ofBijective f hinj hsurj).symm (f x) = x :=
  (ofBijective f hinj hsurj).symm_apply_apply x

@[simp]
theorem of_bijective_apply_symm_apply (f : E →L[𝕜] F) (hinj : f.ker = ⊥) (hsurj : f.range = ⊤) (y : F) :
    f ((ofBijective f hinj hsurj).symm y) = y :=
  (ofBijective f hinj hsurj).apply_symm_apply y

end ContinuousLinearEquiv

namespace ContinuousLinearMap

variable [CompleteSpace E]

/-- Intermediate definition used to show
`continuous_linear_map.closed_complemented_range_of_is_compl_of_ker_eq_bot`.

This is `f.coprod G.subtypeL` as an `continuous_linear_equiv`. -/
noncomputable def coprodSubtypeLEquivOfIsCompl (f : E →L[𝕜] F) {G : Submodule 𝕜 F} (h : IsCompl f.range G)
    [CompleteSpace G] (hker : f.ker = ⊥) : (E × G) ≃L[𝕜] F :=
  ContinuousLinearEquiv.ofBijective (f.coprod G.subtypeL)
    (by
      rw [ker_coprod_of_disjoint_range]
      · rw [hker, Submodule.ker_subtypeL, Submodule.prod_bot]
        
      · rw [Submodule.range_subtypeL]
        exact h.disjoint
        )
    (by
      simp only [← range_coprod, ← h.sup_eq_top, ← Submodule.range_subtypeL])

theorem range_eq_map_coprod_subtypeL_equiv_of_is_compl (f : E →L[𝕜] F) {G : Submodule 𝕜 F} (h : IsCompl f.range G)
    [CompleteSpace G] (hker : f.ker = ⊥) :
    f.range =
      ((⊤ : Submodule 𝕜 E).Prod (⊥ : Submodule 𝕜 G)).map (f.coprodSubtypeLEquivOfIsCompl h hker : E × G →ₗ[𝕜] F) :=
  by
  rw [coprod_subtypeL_equiv_of_is_compl, _root_.coe_coe, ContinuousLinearEquiv.coe_of_bijective, coe_coprod,
    LinearMap.coprod_map_prod, Submodule.map_bot, sup_bot_eq, Submodule.map_top, range]

/- TODO: remove the assumption `f.ker = ⊥` in the next lemma, by using the map induced by `f` on
`E / f.ker`, once we have quotient normed spaces. -/
theorem closed_complemented_range_of_is_compl_of_ker_eq_bot (f : E →L[𝕜] F) (G : Submodule 𝕜 F) (h : IsCompl f.range G)
    (hG : IsClosed (G : Set F)) (hker : f.ker = ⊥) : IsClosed (f.range : Set F) := by
  have : CompleteSpace G := hG.complete_space_coe
  let g := coprod_subtypeL_equiv_of_is_compl f h hker
  rw [congr_arg coe (range_eq_map_coprod_subtypeL_equiv_of_is_compl f h hker)]
  apply g.to_homeomorph.is_closed_image.2
  exact is_closed_univ.prod is_closed_singleton

end ContinuousLinearMap

section ClosedGraphThm

variable [CompleteSpace E] (g : E →ₗ[𝕜] F)

/-- The **closed graph theorem** : a linear map between two Banach spaces whose graph is closed
is continuous. -/
theorem LinearMap.continuous_of_is_closed_graph (hg : IsClosed (g.graph : Set <| E × F)) : Continuous g := by
  let this : CompleteSpace g.graph := complete_space_coe_iff_is_complete.mpr hg.is_complete
  let φ₀ : E →ₗ[𝕜] E × F := linear_map.id.prod g
  have : Function.LeftInverse Prod.fst φ₀ := fun x => rfl
  let φ : E ≃ₗ[𝕜] g.graph := (LinearEquiv.ofLeftInverse this).trans (LinearEquiv.ofEq _ _ g.graph_eq_range_prod.symm)
  let ψ : g.graph ≃L[𝕜] E := φ.symm.to_continuous_linear_equiv_of_continuous continuous_subtype_coe.fst
  exact (continuous_subtype_coe.comp ψ.symm.continuous).snd

/-- A useful form of the **closed graph theorem** : let `f` be a linear map between two Banach
spaces. To show that `f` is continuous, it suffices to show that for any convergent sequence
`uₙ ⟶ x`, if `f(uₙ) ⟶ y` then `y = f(x)`. -/
theorem LinearMap.continuous_of_seq_closed_graph
    (hg : ∀ (u : ℕ → E) (x y), Tendsto u atTop (𝓝 x) → Tendsto (g ∘ u) atTop (𝓝 y) → y = g x) : Continuous g := by
  refine' g.continuous_of_is_closed_graph (is_seq_closed_iff_is_closed.mp <| is_seq_closed_of_def _)
  rintro φ ⟨x, y⟩ hφg hφ
  refine' hg (Prod.fst ∘ φ) x y ((continuous_fst.tendsto _).comp hφ) _
  have : g ∘ Prod.fst ∘ φ = Prod.snd ∘ φ := by
    ext n
    exact (hφg n).symm
  rw [this]
  exact (continuous_snd.tendsto _).comp hφ

variable {g}

namespace ContinuousLinearMap

/-- Upgrade a `linear_map` to a `continuous_linear_map` using the **closed graph theorem**. -/
def ofIsClosedGraph (hg : IsClosed (g.graph : Set <| E × F)) : E →L[𝕜] F where
  toLinearMap := g
  cont := g.continuous_of_is_closed_graph hg

@[simp]
theorem coe_fn_of_is_closed_graph (hg : IsClosed (g.graph : Set <| E × F)) :
    ⇑(ContinuousLinearMap.ofIsClosedGraph hg) = g :=
  rfl

theorem coe_of_is_closed_graph (hg : IsClosed (g.graph : Set <| E × F)) :
    ↑(ContinuousLinearMap.ofIsClosedGraph hg) = g := by
  ext
  rfl

/-- Upgrade a `linear_map` to a `continuous_linear_map` using a variation on the
**closed graph theorem**. -/
def ofSeqClosedGraph (hg : ∀ (u : ℕ → E) (x y), Tendsto u atTop (𝓝 x) → Tendsto (g ∘ u) atTop (𝓝 y) → y = g x) :
    E →L[𝕜] F where
  toLinearMap := g
  cont := g.continuous_of_seq_closed_graph hg

@[simp]
theorem coe_fn_of_seq_closed_graph
    (hg : ∀ (u : ℕ → E) (x y), Tendsto u atTop (𝓝 x) → Tendsto (g ∘ u) atTop (𝓝 y) → y = g x) :
    ⇑(ContinuousLinearMap.ofSeqClosedGraph hg) = g :=
  rfl

theorem coe_of_seq_closed_graph
    (hg : ∀ (u : ℕ → E) (x y), Tendsto u atTop (𝓝 x) → Tendsto (g ∘ u) atTop (𝓝 y) → y = g x) :
    ↑(ContinuousLinearMap.ofSeqClosedGraph hg) = g := by
  ext
  rfl

end ContinuousLinearMap

end ClosedGraphThm

