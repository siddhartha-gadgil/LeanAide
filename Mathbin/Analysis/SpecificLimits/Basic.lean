/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Johannes Hölzl, Yury G. Kudryashov, Patrick Massot
-/
import Mathbin.Algebra.GeomSum
import Mathbin.Order.Filter.Archimedean
import Mathbin.Order.Iterate
import Mathbin.Topology.Instances.Ennreal

/-!
# A collection of specific limit computations

This file, by design, is independent of `normed_space` in the import hierarchy.  It contains
important specific limit computations in metric spaces, in ordered rings/fields, and in specific
instances of these such as `ℝ`, `ℝ≥0` and `ℝ≥0∞`.
-/


noncomputable section

open Classical Set Function Filter Finset Metric

open Classical TopologicalSpace Nat BigOperators uniformity Nnreal Ennreal

variable {α : Type _} {β : Type _} {ι : Type _}

theorem tendsto_inverse_at_top_nhds_0_nat : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
  tendsto_inv_at_top_zero.comp tendsto_coe_nat_at_top_at_top

theorem tendsto_const_div_at_top_nhds_0_nat (C : ℝ) : Tendsto (fun n : ℕ => C / n) atTop (𝓝 0) := by
  simpa only [← mul_zero] using tendsto_const_nhds.mul tendsto_inverse_at_top_nhds_0_nat

theorem Nnreal.tendsto_inverse_at_top_nhds_0_nat : Tendsto (fun n : ℕ => (n : ℝ≥0 )⁻¹) atTop (𝓝 0) := by
  rw [← Nnreal.tendsto_coe]
  exact tendsto_inverse_at_top_nhds_0_nat

theorem Nnreal.tendsto_const_div_at_top_nhds_0_nat (C : ℝ≥0 ) : Tendsto (fun n : ℕ => C / n) atTop (𝓝 0) := by
  simpa using tendsto_const_nhds.mul Nnreal.tendsto_inverse_at_top_nhds_0_nat

theorem tendsto_one_div_add_at_top_nhds_0_nat : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
  suffices Tendsto (fun n : ℕ => 1 / (↑(n + 1) : ℝ)) atTop (𝓝 0) by
    simpa
  (tendsto_add_at_top_iff_nat 1).2 (tendsto_const_div_at_top_nhds_0_nat 1)

/-! ### Powers -/


theorem tendsto_add_one_pow_at_top_at_top_of_pos [LinearOrderedSemiring α] [Archimedean α] {r : α} (h : 0 < r) :
    Tendsto (fun n : ℕ => (r + 1) ^ n) atTop atTop :=
  (tendsto_at_top_at_top_of_monotone' fun n m => pow_le_pow (le_add_of_nonneg_left (le_of_ltₓ h))) <|
    not_bdd_above_iff.2 fun x => Set.exists_range_iff.2 <| add_one_pow_unbounded_of_pos _ h

theorem tendsto_pow_at_top_at_top_of_one_lt [LinearOrderedRing α] [Archimedean α] {r : α} (h : 1 < r) :
    Tendsto (fun n : ℕ => r ^ n) atTop atTop :=
  sub_add_cancel r 1 ▸ tendsto_add_one_pow_at_top_at_top_of_pos (sub_pos.2 h)

theorem Nat.tendsto_pow_at_top_at_top_of_one_lt {m : ℕ} (h : 1 < m) : Tendsto (fun n : ℕ => m ^ n) atTop atTop :=
  tsub_add_cancel_of_le (le_of_ltₓ h) ▸ tendsto_add_one_pow_at_top_at_top_of_pos (tsub_pos_of_lt h)

theorem tendsto_pow_at_top_nhds_0_of_lt_1 {𝕜 : Type _} [LinearOrderedField 𝕜] [Archimedean 𝕜] [TopologicalSpace 𝕜]
    [OrderTopology 𝕜] {r : 𝕜} (h₁ : 0 ≤ r) (h₂ : r < 1) : Tendsto (fun n : ℕ => r ^ n) atTop (𝓝 0) :=
  h₁.eq_or_lt.elim
    (fun this : 0 = r =>
      (tendsto_add_at_top_iff_nat 1).mp <| by
        simp [← pow_succₓ, this, ← tendsto_const_nhds])
    fun this : 0 < r =>
    have : Tendsto (fun n => (r⁻¹ ^ n)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_at_top_zero.comp (tendsto_pow_at_top_at_top_of_one_lt <| one_lt_inv this h₂)
    this.congr fun n => by
      simp

theorem tendsto_pow_at_top_nhds_within_0_of_lt_1 {𝕜 : Type _} [LinearOrderedField 𝕜] [Archimedean 𝕜]
    [TopologicalSpace 𝕜] [OrderTopology 𝕜] {r : 𝕜} (h₁ : 0 < r) (h₂ : r < 1) :
    Tendsto (fun n : ℕ => r ^ n) atTop (𝓝[>] 0) :=
  tendsto_inf.2
    ⟨tendsto_pow_at_top_nhds_0_of_lt_1 h₁.le h₂, tendsto_principal.2 <| eventually_of_forall fun n => pow_pos h₁ _⟩

theorem uniformity_basis_dist_pow_of_lt_1 {α : Type _} [PseudoMetricSpace α] {r : ℝ} (h₀ : 0 < r) (h₁ : r < 1) :
    (𝓤 α).HasBasis (fun k : ℕ => True) fun k => { p : α × α | dist p.1 p.2 < r ^ k } :=
  (Metric.mk_uniformity_basis fun i _ => pow_pos h₀ _) fun ε ε0 =>
    (exists_pow_lt_of_lt_one ε0 h₁).imp fun k hk => ⟨trivialₓ, hk.le⟩

theorem geom_lt {u : ℕ → ℝ} {c : ℝ} (hc : 0 ≤ c) {n : ℕ} (hn : 0 < n) (h : ∀, ∀ k < n, ∀, c * u k < u (k + 1)) :
    c ^ n * u 0 < u n := by
  refine' (monotone_mul_left_of_nonneg hc).seq_pos_lt_seq_of_le_of_lt hn _ _ h
  · simp
    
  · simp [← pow_succₓ, ← mul_assoc, ← le_reflₓ]
    

theorem geom_le {u : ℕ → ℝ} {c : ℝ} (hc : 0 ≤ c) (n : ℕ) (h : ∀, ∀ k < n, ∀, c * u k ≤ u (k + 1)) : c ^ n * u 0 ≤ u n :=
  by
  refine' (monotone_mul_left_of_nonneg hc).seq_le_seq n _ _ h <;> simp [← pow_succₓ, ← mul_assoc, ← le_reflₓ]

theorem lt_geom {u : ℕ → ℝ} {c : ℝ} (hc : 0 ≤ c) {n : ℕ} (hn : 0 < n) (h : ∀, ∀ k < n, ∀, u (k + 1) < c * u k) :
    u n < c ^ n * u 0 := by
  refine' (monotone_mul_left_of_nonneg hc).seq_pos_lt_seq_of_lt_of_le hn _ h _
  · simp
    
  · simp [← pow_succₓ, ← mul_assoc, ← le_reflₓ]
    

theorem le_geom {u : ℕ → ℝ} {c : ℝ} (hc : 0 ≤ c) (n : ℕ) (h : ∀, ∀ k < n, ∀, u (k + 1) ≤ c * u k) : u n ≤ c ^ n * u 0 :=
  by
  refine' (monotone_mul_left_of_nonneg hc).seq_le_seq n _ h _ <;> simp [← pow_succₓ, ← mul_assoc, ← le_reflₓ]

/-- If a sequence `v` of real numbers satisfies `k * v n ≤ v (n+1)` with `1 < k`,
then it goes to +∞. -/
theorem tendsto_at_top_of_geom_le {v : ℕ → ℝ} {c : ℝ} (h₀ : 0 < v 0) (hc : 1 < c) (hu : ∀ n, c * v n ≤ v (n + 1)) :
    Tendsto v atTop atTop :=
  (tendsto_at_top_mono fun n => geom_le (zero_le_one.trans hc.le) n fun k hk => hu k) <|
    (tendsto_pow_at_top_at_top_of_one_lt hc).at_top_mul_const h₀

theorem Nnreal.tendsto_pow_at_top_nhds_0_of_lt_1 {r : ℝ≥0 } (hr : r < 1) : Tendsto (fun n : ℕ => r ^ n) atTop (𝓝 0) :=
  Nnreal.tendsto_coe.1 <| by
    simp only [← Nnreal.coe_pow, ← Nnreal.coe_zero, ← tendsto_pow_at_top_nhds_0_of_lt_1 r.coe_nonneg hr]

theorem Ennreal.tendsto_pow_at_top_nhds_0_of_lt_1 {r : ℝ≥0∞} (hr : r < 1) : Tendsto (fun n : ℕ => r ^ n) atTop (𝓝 0) :=
  by
  rcases Ennreal.lt_iff_exists_coe.1 hr with ⟨r, rfl, hr'⟩
  rw [← Ennreal.coe_zero]
  norm_cast  at *
  apply Nnreal.tendsto_pow_at_top_nhds_0_of_lt_1 hr

/-! ### Geometric series-/


section Geometric

theorem has_sum_geometric_of_lt_1 {r : ℝ} (h₁ : 0 ≤ r) (h₂ : r < 1) : HasSum (fun n : ℕ => r ^ n) (1 - r)⁻¹ :=
  have : r ≠ 1 := ne_of_ltₓ h₂
  have : Tendsto (fun n => (r ^ n - 1) * (r - 1)⁻¹) atTop (𝓝 ((0 - 1) * (r - 1)⁻¹)) :=
    ((tendsto_pow_at_top_nhds_0_of_lt_1 h₁ h₂).sub tendsto_const_nhds).mul tendsto_const_nhds
  (has_sum_iff_tendsto_nat_of_nonneg (pow_nonneg h₁) _).mpr <| by
    simp_all [← neg_inv, ← geom_sum_eq, ← div_eq_mul_inv]

theorem summable_geometric_of_lt_1 {r : ℝ} (h₁ : 0 ≤ r) (h₂ : r < 1) : Summable fun n : ℕ => r ^ n :=
  ⟨_, has_sum_geometric_of_lt_1 h₁ h₂⟩

theorem tsum_geometric_of_lt_1 {r : ℝ} (h₁ : 0 ≤ r) (h₂ : r < 1) : (∑' n : ℕ, r ^ n) = (1 - r)⁻¹ :=
  (has_sum_geometric_of_lt_1 h₁ h₂).tsum_eq

theorem has_sum_geometric_two : HasSum (fun n : ℕ => ((1 : ℝ) / 2) ^ n) 2 := by
  convert has_sum_geometric_of_lt_1 _ _ <;> norm_num

theorem summable_geometric_two : Summable fun n : ℕ => ((1 : ℝ) / 2) ^ n :=
  ⟨_, has_sum_geometric_two⟩

theorem summable_geometric_two_encode {ι : Type _} [Encodable ι] :
    Summable fun i : ι => (1 / 2 : ℝ) ^ Encodable.encode i :=
  summable_geometric_two.comp_injective Encodable.encode_injective

theorem tsum_geometric_two : (∑' n : ℕ, ((1 : ℝ) / 2) ^ n) = 2 :=
  has_sum_geometric_two.tsum_eq

theorem sum_geometric_two_le (n : ℕ) : (∑ i : ℕ in range n, (1 / (2 : ℝ)) ^ i) ≤ 2 := by
  have : ∀ i, 0 ≤ (1 / (2 : ℝ)) ^ i := by
    intro i
    apply pow_nonneg
    norm_num
  convert sum_le_tsum (range n) (fun i _ => this i) summable_geometric_two
  exact tsum_geometric_two.symm

theorem tsum_geometric_inv_two : (∑' n : ℕ, (2 : ℝ)⁻¹ ^ n) = 2 :=
  (inv_eq_one_div (2 : ℝ)).symm ▸ tsum_geometric_two

/-- The sum of `2⁻¹ ^ i` for `n ≤ i` equals `2 * 2⁻¹ ^ n`. -/
theorem tsum_geometric_inv_two_ge (n : ℕ) : (∑' i, ite (n ≤ i) ((2 : ℝ)⁻¹ ^ i) 0) = 2 * 2⁻¹ ^ n := by
  have A : Summable fun i : ℕ => ite (n ≤ i) ((2⁻¹ : ℝ) ^ i) 0 := by
    apply summable_of_nonneg_of_le _ _ summable_geometric_two <;>
      · intro i
        by_cases' hi : n ≤ i <;> simp [← hi]
        
  have B : ((Finset.range n).Sum fun i : ℕ => ite (n ≤ i) ((2⁻¹ : ℝ) ^ i) 0) = 0 :=
    Finset.sum_eq_zero fun i hi => ite_eq_right_iff.2 fun h => (lt_irreflₓ _ ((Finset.mem_range.1 hi).trans_le h)).elim
  simp only [sum_add_tsum_nat_add n A, ← B, ← if_true, ← zero_addₓ, ← zero_le', ← le_add_iff_nonneg_left, ← pow_addₓ, ←
    tsum_mul_right, ← tsum_geometric_inv_two]

theorem has_sum_geometric_two' (a : ℝ) : HasSum (fun n : ℕ => a / 2 / 2 ^ n) a := by
  convert HasSum.mul_left (a / 2) (has_sum_geometric_of_lt_1 (le_of_ltₓ one_half_pos) one_half_lt_one)
  · funext n
    simp
    rfl
    
  · norm_num
    

theorem summable_geometric_two' (a : ℝ) : Summable fun n : ℕ => a / 2 / 2 ^ n :=
  ⟨a, has_sum_geometric_two' a⟩

theorem tsum_geometric_two' (a : ℝ) : (∑' n : ℕ, a / 2 / 2 ^ n) = a :=
  (has_sum_geometric_two' a).tsum_eq

/-- **Sum of a Geometric Series** -/
theorem Nnreal.has_sum_geometric {r : ℝ≥0 } (hr : r < 1) : HasSum (fun n : ℕ => r ^ n) (1 - r)⁻¹ := by
  apply Nnreal.has_sum_coe.1
  push_cast
  rw [Nnreal.coe_sub (le_of_ltₓ hr)]
  exact has_sum_geometric_of_lt_1 r.coe_nonneg hr

theorem Nnreal.summable_geometric {r : ℝ≥0 } (hr : r < 1) : Summable fun n : ℕ => r ^ n :=
  ⟨_, Nnreal.has_sum_geometric hr⟩

theorem tsum_geometric_nnreal {r : ℝ≥0 } (hr : r < 1) : (∑' n : ℕ, r ^ n) = (1 - r)⁻¹ :=
  (Nnreal.has_sum_geometric hr).tsum_eq

/-- The series `pow r` converges to `(1-r)⁻¹`. For `r < 1` the RHS is a finite number,
and for `1 ≤ r` the RHS equals `∞`. -/
@[simp]
theorem Ennreal.tsum_geometric (r : ℝ≥0∞) : (∑' n : ℕ, r ^ n) = (1 - r)⁻¹ := by
  cases' lt_or_leₓ r 1 with hr hr
  · rcases Ennreal.lt_iff_exists_coe.1 hr with ⟨r, rfl, hr'⟩
    norm_cast  at *
    convert Ennreal.tsum_coe_eq (Nnreal.has_sum_geometric hr)
    rw [Ennreal.coe_inv <| ne_of_gtₓ <| tsub_pos_iff_lt.2 hr]
    
  · rw [tsub_eq_zero_iff_le.mpr hr, Ennreal.inv_zero, Ennreal.tsum_eq_supr_nat, supr_eq_top]
    refine' fun a ha => (Ennreal.exists_nat_gt (lt_top_iff_ne_top.1 ha)).imp fun n hn => lt_of_lt_of_leₓ hn _
    calc (n : ℝ≥0∞) = ∑ i in range n, 1 := by
        rw [sum_const, nsmul_one, card_range]_ ≤ ∑ i in range n, r ^ i :=
        sum_le_sum fun k _ => one_le_pow_of_one_le' hr k
    

end Geometric

/-!
### Sequences with geometrically decaying distance in metric spaces

In this paragraph, we discuss sequences in metric spaces or emetric spaces for which the distance
between two consecutive terms decays geometrically. We show that such sequences are Cauchy
sequences, and bound their distances to the limit. We also discuss series with geometrically
decaying terms.
-/


section EdistLeGeometric

variable [PseudoEmetricSpace α] (r C : ℝ≥0∞) (hr : r < 1) (hC : C ≠ ⊤) {f : ℕ → α}
  (hu : ∀ n, edist (f n) (f (n + 1)) ≤ C * r ^ n)

include hr hC hu

/-- If `edist (f n) (f (n+1))` is bounded by `C * r^n`, `C ≠ ∞`, `r < 1`,
then `f` is a Cauchy sequence.-/
theorem cauchy_seq_of_edist_le_geometric : CauchySeq f := by
  refine' cauchy_seq_of_edist_le_of_tsum_ne_top _ hu _
  rw [Ennreal.tsum_mul_left, Ennreal.tsum_geometric]
  refine' Ennreal.mul_ne_top hC (Ennreal.inv_ne_top.2 _)
  exact (tsub_pos_iff_lt.2 hr).ne'

omit hr hC

/-- If `edist (f n) (f (n+1))` is bounded by `C * r^n`, then the distance from
`f n` to the limit of `f` is bounded above by `C * r^n / (1 - r)`. -/
theorem edist_le_of_edist_le_geometric_of_tendsto {a : α} (ha : Tendsto f atTop (𝓝 a)) (n : ℕ) :
    edist (f n) a ≤ C * r ^ n / (1 - r) := by
  convert edist_le_tsum_of_edist_le_of_tendsto _ hu ha _
  simp only [← pow_addₓ, ← Ennreal.tsum_mul_left, ← Ennreal.tsum_geometric, ← div_eq_mul_inv, ← mul_assoc]

/-- If `edist (f n) (f (n+1))` is bounded by `C * r^n`, then the distance from
`f 0` to the limit of `f` is bounded above by `C / (1 - r)`. -/
theorem edist_le_of_edist_le_geometric_of_tendsto₀ {a : α} (ha : Tendsto f atTop (𝓝 a)) : edist (f 0) a ≤ C / (1 - r) :=
  by
  simpa only [← pow_zeroₓ, ← mul_oneₓ] using edist_le_of_edist_le_geometric_of_tendsto r C hu ha 0

end EdistLeGeometric

section EdistLeGeometricTwo

variable [PseudoEmetricSpace α] (C : ℝ≥0∞) (hC : C ≠ ⊤) {f : ℕ → α} (hu : ∀ n, edist (f n) (f (n + 1)) ≤ C / 2 ^ n)
  {a : α} (ha : Tendsto f atTop (𝓝 a))

include hC hu

/-- If `edist (f n) (f (n+1))` is bounded by `C * 2^-n`, then `f` is a Cauchy sequence.-/
theorem cauchy_seq_of_edist_le_geometric_two : CauchySeq f := by
  simp only [← div_eq_mul_inv, ← Ennreal.inv_pow] at hu
  refine' cauchy_seq_of_edist_le_geometric 2⁻¹ C _ hC hu
  simp [← Ennreal.one_lt_two]

omit hC

include ha

/-- If `edist (f n) (f (n+1))` is bounded by `C * 2^-n`, then the distance from
`f n` to the limit of `f` is bounded above by `2 * C * 2^-n`. -/
theorem edist_le_of_edist_le_geometric_two_of_tendsto (n : ℕ) : edist (f n) a ≤ 2 * C / 2 ^ n := by
  simp only [← div_eq_mul_inv, ← Ennreal.inv_pow] at *
  rw [mul_assoc, mul_comm]
  convert edist_le_of_edist_le_geometric_of_tendsto 2⁻¹ C hu ha n
  rw [Ennreal.one_sub_inv_two, inv_invₓ]

/-- If `edist (f n) (f (n+1))` is bounded by `C * 2^-n`, then the distance from
`f 0` to the limit of `f` is bounded above by `2 * C`. -/
theorem edist_le_of_edist_le_geometric_two_of_tendsto₀ : edist (f 0) a ≤ 2 * C := by
  simpa only [← pow_zeroₓ, ← div_eq_mul_inv, ← Ennreal.inv_one, ← mul_oneₓ] using
    edist_le_of_edist_le_geometric_two_of_tendsto C hu ha 0

end EdistLeGeometricTwo

section LeGeometric

variable [PseudoMetricSpace α] {r C : ℝ} (hr : r < 1) {f : ℕ → α} (hu : ∀ n, dist (f n) (f (n + 1)) ≤ C * r ^ n)

include hr hu

theorem aux_has_sum_of_le_geometric : HasSum (fun n : ℕ => C * r ^ n) (C / (1 - r)) := by
  rcases sign_cases_of_C_mul_pow_nonneg fun n => dist_nonneg.trans (hu n) with (rfl | ⟨C₀, r₀⟩)
  · simp [← has_sum_zero]
    
  · refine' HasSum.mul_left C _
    simpa using has_sum_geometric_of_lt_1 r₀ hr
    

variable (r C)

/-- If `dist (f n) (f (n+1))` is bounded by `C * r^n`, `r < 1`, then `f` is a Cauchy sequence.
Note that this lemma does not assume `0 ≤ C` or `0 ≤ r`. -/
theorem cauchy_seq_of_le_geometric : CauchySeq f :=
  cauchy_seq_of_dist_le_of_summable _ hu ⟨_, aux_has_sum_of_le_geometric hr hu⟩

/-- If `dist (f n) (f (n+1))` is bounded by `C * r^n`, `r < 1`, then the distance from
`f n` to the limit of `f` is bounded above by `C * r^n / (1 - r)`. -/
theorem dist_le_of_le_geometric_of_tendsto₀ {a : α} (ha : Tendsto f atTop (𝓝 a)) : dist (f 0) a ≤ C / (1 - r) :=
  (aux_has_sum_of_le_geometric hr hu).tsum_eq ▸
    dist_le_tsum_of_dist_le_of_tendsto₀ _ hu ⟨_, aux_has_sum_of_le_geometric hr hu⟩ ha

/-- If `dist (f n) (f (n+1))` is bounded by `C * r^n`, `r < 1`, then the distance from
`f 0` to the limit of `f` is bounded above by `C / (1 - r)`. -/
theorem dist_le_of_le_geometric_of_tendsto {a : α} (ha : Tendsto f atTop (𝓝 a)) (n : ℕ) :
    dist (f n) a ≤ C * r ^ n / (1 - r) := by
  have := aux_has_sum_of_le_geometric hr hu
  convert dist_le_tsum_of_dist_le_of_tendsto _ hu ⟨_, this⟩ ha n
  simp only [← pow_addₓ, ← mul_left_commₓ C, ← mul_div_right_comm]
  rw [mul_comm]
  exact (this.mul_left _).tsum_eq.symm

omit hr hu

variable (hu₂ : ∀ n, dist (f n) (f (n + 1)) ≤ C / 2 / 2 ^ n)

/-- If `dist (f n) (f (n+1))` is bounded by `(C / 2) / 2^n`, then `f` is a Cauchy sequence. -/
theorem cauchy_seq_of_le_geometric_two : CauchySeq f :=
  cauchy_seq_of_dist_le_of_summable _ hu₂ <| ⟨_, has_sum_geometric_two' C⟩

/-- If `dist (f n) (f (n+1))` is bounded by `(C / 2) / 2^n`, then the distance from
`f 0` to the limit of `f` is bounded above by `C`. -/
theorem dist_le_of_le_geometric_two_of_tendsto₀ {a : α} (ha : Tendsto f atTop (𝓝 a)) : dist (f 0) a ≤ C :=
  tsum_geometric_two' C ▸ dist_le_tsum_of_dist_le_of_tendsto₀ _ hu₂ (summable_geometric_two' C) ha

include hu₂

/-- If `dist (f n) (f (n+1))` is bounded by `(C / 2) / 2^n`, then the distance from
`f n` to the limit of `f` is bounded above by `C / 2^n`. -/
theorem dist_le_of_le_geometric_two_of_tendsto {a : α} (ha : Tendsto f atTop (𝓝 a)) (n : ℕ) :
    dist (f n) a ≤ C / 2 ^ n := by
  convert dist_le_tsum_of_dist_le_of_tendsto _ hu₂ (summable_geometric_two' C) ha n
  simp only [← add_commₓ n, ← pow_addₓ, div_div]
  symm
  exact ((has_sum_geometric_two' C).div_const _).tsum_eq

end LeGeometric

/-! ### Summability tests based on comparison with geometric series -/


/-- A series whose terms are bounded by the terms of a converging geometric series converges. -/
theorem summable_one_div_pow_of_le {m : ℝ} {f : ℕ → ℕ} (hm : 1 < m) (fi : ∀ i, i ≤ f i) :
    Summable fun i => 1 / m ^ f i := by
  refine'
    summable_of_nonneg_of_le (fun a => one_div_nonneg.mpr (pow_nonneg (zero_le_one.trans hm.le) _)) (fun a => _)
      (summable_geometric_of_lt_1 (one_div_nonneg.mpr (zero_le_one.trans hm.le))
        ((one_div_lt (zero_lt_one.trans hm) zero_lt_one).mpr (one_div_one.le.trans_lt hm)))
  rw [div_pow, one_pow]
  refine' (one_div_le_one_div _ _).mpr (pow_le_pow hm.le (fi a)) <;> exact pow_pos (zero_lt_one.trans hm) _

/-! ### Positive sequences with small sums on encodable types -/


/-- For any positive `ε`, define on an encodable type a positive sequence with sum less than `ε` -/
def posSumOfEncodable {ε : ℝ} (hε : 0 < ε) (ι) [Encodable ι] :
    { ε' : ι → ℝ // (∀ i, 0 < ε' i) ∧ ∃ c, HasSum ε' c ∧ c ≤ ε } := by
  let f := fun n => ε / 2 / 2 ^ n
  have hf : HasSum f ε := has_sum_geometric_two' _
  have f0 : ∀ n, 0 < f n := fun n => div_pos (half_pos hε) (pow_pos zero_lt_two _)
  refine' ⟨f ∘ Encodable.encode, fun i => f0 _, _⟩
  rcases hf.summable.comp_injective (@Encodable.encode_injective ι _) with ⟨c, hg⟩
  refine' ⟨c, hg, has_sum_le_inj _ (@Encodable.encode_injective ι _) _ _ hg hf⟩
  · intro i _
    exact le_of_ltₓ (f0 _)
    
  · intro n
    exact le_rfl
    

theorem Set.Countable.exists_pos_has_sum_le {ι : Type _} {s : Set ι} (hs : s.Countable) {ε : ℝ} (hε : 0 < ε) :
    ∃ ε' : ι → ℝ, (∀ i, 0 < ε' i) ∧ ∃ c, HasSum (fun i : s => ε' i) c ∧ c ≤ ε := by
  have := hs.to_encodable
  rcases posSumOfEncodable hε s with ⟨f, hf0, ⟨c, hfc, hcε⟩⟩
  refine' ⟨fun i => if h : i ∈ s then f ⟨i, h⟩ else 1, fun i => _, ⟨c, _, hcε⟩⟩
  · split_ifs
    exacts[hf0 _, zero_lt_one]
    
  · simpa only [← Subtype.coe_prop, ← dif_pos, ← Subtype.coe_eta]
    

theorem Set.Countable.exists_pos_forall_sum_le {ι : Type _} {s : Set ι} (hs : s.Countable) {ε : ℝ} (hε : 0 < ε) :
    ∃ ε' : ι → ℝ, (∀ i, 0 < ε' i) ∧ ∀ t : Finset ι, ↑t ⊆ s → (∑ i in t, ε' i) ≤ ε := by
  rcases hs.exists_pos_has_sum_le hε with ⟨ε', hpos, c, hε'c, hcε⟩
  refine' ⟨ε', hpos, fun t ht => _⟩
  rw [← sum_subtype_of_mem _ ht]
  refine' (sum_le_has_sum _ _ hε'c).trans hcε
  exact fun _ _ => (hpos _).le

namespace Nnreal

theorem exists_pos_sum_of_encodable {ε : ℝ≥0 } (hε : ε ≠ 0) (ι) [Encodable ι] :
    ∃ ε' : ι → ℝ≥0 , (∀ i, 0 < ε' i) ∧ ∃ c, HasSum ε' c ∧ c < ε :=
  let ⟨a, a0, aε⟩ := exists_between (pos_iff_ne_zero.2 hε)
  let ⟨ε', hε', c, hc, hcε⟩ := posSumOfEncodable a0 ι
  ⟨fun i => ⟨ε' i, le_of_ltₓ <| hε' i⟩, fun i => Nnreal.coe_lt_coe.1 <| hε' i,
    ⟨c, has_sum_le (fun i => le_of_ltₓ <| hε' i) has_sum_zero hc⟩, Nnreal.has_sum_coe.1 hc,
    lt_of_le_of_ltₓ (Nnreal.coe_le_coe.1 hcε) aε⟩

end Nnreal

namespace Ennreal

theorem exists_pos_sum_of_encodable {ε : ℝ≥0∞} (hε : ε ≠ 0) (ι) [Encodable ι] :
    ∃ ε' : ι → ℝ≥0 , (∀ i, 0 < ε' i) ∧ (∑' i, (ε' i : ℝ≥0∞)) < ε := by
  rcases exists_between (pos_iff_ne_zero.2 hε) with ⟨r, h0r, hrε⟩
  rcases lt_iff_exists_coe.1 hrε with ⟨x, rfl, hx⟩
  rcases Nnreal.exists_pos_sum_of_encodable (coe_pos.1 h0r).ne' ι with ⟨ε', hp, c, hc, hcr⟩
  exact ⟨ε', hp, (Ennreal.tsum_coe_eq hc).symm ▸ lt_transₓ (coe_lt_coe.2 hcr) hrε⟩

theorem exists_pos_sum_of_encodable' {ε : ℝ≥0∞} (hε : ε ≠ 0) (ι) [Encodable ι] :
    ∃ ε' : ι → ℝ≥0∞, (∀ i, 0 < ε' i) ∧ (∑' i, ε' i) < ε :=
  let ⟨δ, δpos, hδ⟩ := exists_pos_sum_of_encodable hε ι
  ⟨fun i => δ i, fun i => Ennreal.coe_pos.2 (δpos i), hδ⟩

theorem exists_pos_tsum_mul_lt_of_encodable {ε : ℝ≥0∞} (hε : ε ≠ 0) {ι} [Encodable ι] (w : ι → ℝ≥0∞)
    (hw : ∀ i, w i ≠ ∞) : ∃ δ : ι → ℝ≥0 , (∀ i, 0 < δ i) ∧ (∑' i, (w i * δ i : ℝ≥0∞)) < ε := by
  lift w to ι → ℝ≥0 using hw
  rcases exists_pos_sum_of_encodable hε ι with ⟨δ', Hpos, Hsum⟩
  have : ∀ i, 0 < max 1 (w i) := fun i => zero_lt_one.trans_le (le_max_leftₓ _ _)
  refine' ⟨fun i => δ' i / max 1 (w i), fun i => Nnreal.div_pos (Hpos _) (this i), _⟩
  refine' lt_of_le_of_ltₓ (Ennreal.tsum_le_tsum fun i => _) Hsum
  rw [coe_div (this i).ne']
  refine' mul_le_of_le_div' (Ennreal.mul_le_mul le_rfl <| Ennreal.inv_le_inv.2 _)
  exact coe_le_coe.2 (le_max_rightₓ _ _)

end Ennreal

/-!
### Factorial
-/


theorem factorial_tendsto_at_top : Tendsto Nat.factorial atTop atTop :=
  tendsto_at_top_at_top_of_monotone Nat.monotone_factorial fun n => ⟨n, n.self_le_factorial⟩

theorem tendsto_factorial_div_pow_self_at_top : Tendsto (fun n => n ! / n ^ n : ℕ → ℝ) atTop (𝓝 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (tendsto_const_div_at_top_nhds_0_nat 1)
    (eventually_of_forall fun n =>
      div_nonneg
        (by
          exact_mod_cast n.factorial_pos.le)
        (pow_nonneg
          (by
            exact_mod_cast n.zero_le)
          _))
    (by
      refine' (eventually_gt_at_top 0).mono fun n hn => _
      rcases Nat.exists_eq_succ_of_ne_zero hn.ne.symm with ⟨k, rfl⟩
      rw [← prod_range_add_one_eq_factorial, pow_eq_prod_const, div_eq_mul_inv, ← inv_eq_one_div, prod_nat_cast,
        Nat.cast_succₓ, ← prod_inv_distrib, ← prod_mul_distrib, Finset.prod_range_succ']
      simp only [← prod_range_succ', ← one_mulₓ, ← Nat.cast_addₓ, ← zero_addₓ, ← Nat.cast_oneₓ]
      refine'
          mul_le_of_le_one_left
            (inv_nonneg.mpr <| by
              exact_mod_cast hn.le)
            (prod_le_one _ _) <;>
        intro x hx <;> rw [Finset.mem_range] at hx
      · refine' mul_nonneg _ (inv_nonneg.mpr _) <;> norm_cast <;> linarith
        
      · refine'
          (div_le_one <| by
                exact_mod_cast hn).mpr
            _
        norm_cast
        linarith
        )

/-!
### Ceil and floor
-/


section

theorem tendsto_nat_floor_at_top {α : Type _} [LinearOrderedSemiring α] [FloorSemiring α] :
    Tendsto (fun x : α => ⌊x⌋₊) atTop atTop :=
  Nat.floor_mono.tendsto_at_top_at_top fun x =>
    ⟨max 0 (x + 1), by
      simp [← Nat.le_floor_iff]⟩

variable {R : Type _} [TopologicalSpace R] [LinearOrderedField R] [OrderTopology R] [FloorRing R]

theorem tendsto_nat_floor_mul_div_at_top {a : R} (ha : 0 ≤ a) : Tendsto (fun x => (⌊a * x⌋₊ : R) / x) atTop (𝓝 a) := by
  have A : tendsto (fun x : R => a - x⁻¹) at_top (𝓝 (a - 0)) := tendsto_const_nhds.sub tendsto_inv_at_top_zero
  rw [sub_zero] at A
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' A tendsto_const_nhds
  · refine' eventually_at_top.2 ⟨1, fun x hx => _⟩
    simp only [← le_div_iff (zero_lt_one.trans_le hx), ← sub_mul, ← inv_mul_cancel (zero_lt_one.trans_le hx).ne']
    have := Nat.lt_floor_add_one (a * x)
    linarith
    
  · refine' eventually_at_top.2 ⟨1, fun x hx => _⟩
    rw [div_le_iff (zero_lt_one.trans_le hx)]
    simp [← Nat.floor_le (mul_nonneg ha (zero_le_one.trans hx))]
    

theorem tendsto_nat_floor_div_at_top : Tendsto (fun x => (⌊x⌋₊ : R) / x) atTop (𝓝 1) := by
  simpa using tendsto_nat_floor_mul_div_at_top (zero_le_one' R)

theorem tendsto_nat_ceil_mul_div_at_top {a : R} (ha : 0 ≤ a) : Tendsto (fun x => (⌈a * x⌉₊ : R) / x) atTop (𝓝 a) := by
  have A : tendsto (fun x : R => a + x⁻¹) at_top (𝓝 (a + 0)) := tendsto_const_nhds.add tendsto_inv_at_top_zero
  rw [add_zeroₓ] at A
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds A
  · refine' eventually_at_top.2 ⟨1, fun x hx => _⟩
    rw [le_div_iff (zero_lt_one.trans_le hx)]
    exact Nat.le_ceil _
    
  · refine' eventually_at_top.2 ⟨1, fun x hx => _⟩
    simp [← div_le_iff (zero_lt_one.trans_le hx), ← inv_mul_cancel (zero_lt_one.trans_le hx).ne', ←
      (Nat.ceil_lt_add_one (mul_nonneg ha (zero_le_one.trans hx))).le, ← add_mulₓ]
    

theorem tendsto_nat_ceil_div_at_top : Tendsto (fun x => (⌈x⌉₊ : R) / x) atTop (𝓝 1) := by
  simpa using tendsto_nat_ceil_mul_div_at_top (zero_le_one' R)

end

