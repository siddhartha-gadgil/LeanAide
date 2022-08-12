/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker, Sébastien Gouëzel, Yury G. Kudryashov, Dylan MacKenzie, Patrick Massot
-/
import Mathbin.Algebra.Order.Field
import Mathbin.Analysis.Asymptotics.Asymptotics
import Mathbin.Analysis.SpecificLimits.Basic

/-!
# A collection of specific limit computations

This file contains important specific limit computations in (semi-)normed groups/rings/spaces, as
as well as such computations in `ℝ` when the natural proof passes through a fact about normed
spaces.

-/


noncomputable section

open Classical Set Function Filter Finset Metric Asymptotics

open Classical TopologicalSpace Nat BigOperators uniformity Nnreal Ennreal

variable {α : Type _} {β : Type _} {ι : Type _}

theorem tendsto_norm_at_top_at_top : Tendsto (norm : ℝ → ℝ) atTop atTop :=
  tendsto_abs_at_top_at_top

theorem summable_of_absolute_convergence_real {f : ℕ → ℝ} :
    (∃ r, Tendsto (fun n => ∑ i in range n, abs (f i)) atTop (𝓝 r)) → Summable f
  | ⟨r, hr⟩ => by
    refine' summable_of_summable_norm ⟨r, (has_sum_iff_tendsto_nat_of_nonneg _ _).2 _⟩
    exact fun i => norm_nonneg _
    simpa only using hr

/-! ### Powers -/


theorem tendsto_norm_zero' {𝕜 : Type _} [NormedGroup 𝕜] : Tendsto (norm : 𝕜 → ℝ) (𝓝[≠] 0) (𝓝[>] 0) :=
  tendsto_norm_zero.inf <| tendsto_principal_principal.2 fun x hx => norm_pos_iff.2 hx

namespace NormedField

theorem tendsto_norm_inverse_nhds_within_0_at_top {𝕜 : Type _} [NormedField 𝕜] :
    Tendsto (fun x : 𝕜 => ∥x⁻¹∥) (𝓝[≠] 0) atTop :=
  (tendsto_inv_zero_at_top.comp tendsto_norm_zero').congr fun x => (norm_inv x).symm

theorem tendsto_norm_zpow_nhds_within_0_at_top {𝕜 : Type _} [NormedField 𝕜] {m : ℤ} (hm : m < 0) :
    Tendsto (fun x : 𝕜 => ∥x ^ m∥) (𝓝[≠] 0) atTop := by
  rcases neg_surjective m with ⟨m, rfl⟩
  rw [neg_lt_zero] at hm
  lift m to ℕ using hm.le
  rw [Int.coe_nat_pos] at hm
  simp only [← norm_pow, ← zpow_neg, ← zpow_coe_nat, inv_pow]
  exact (tendsto_pow_at_top hm.ne').comp NormedField.tendsto_norm_inverse_nhds_within_0_at_top

/-- The (scalar) product of a sequence that tends to zero with a bounded one also tends to zero. -/
theorem tendsto_zero_smul_of_tendsto_zero_of_bounded {ι 𝕜 𝔸 : Type _} [NormedField 𝕜] [NormedGroup 𝔸] [NormedSpace 𝕜 𝔸]
    {l : Filter ι} {ε : ι → 𝕜} {f : ι → 𝔸} (hε : Tendsto ε l (𝓝 0)) (hf : Filter.IsBoundedUnder (· ≤ ·) l (norm ∘ f)) :
    Tendsto (ε • f) l (𝓝 0) := by
  rw [← is_o_one_iff 𝕜] at hε⊢
  simpa using is_o.smul_is_O hε (hf.is_O_const (one_ne_zero : (1 : 𝕜) ≠ 0))

@[simp]
theorem continuous_at_zpow {𝕜 : Type _} [NondiscreteNormedField 𝕜] {m : ℤ} {x : 𝕜} :
    ContinuousAt (fun x => x ^ m) x ↔ x ≠ 0 ∨ 0 ≤ m := by
  refine' ⟨_, continuous_at_zpow₀ _ _⟩
  contrapose!
  rintro ⟨rfl, hm⟩ hc
  exact
    not_tendsto_at_top_of_tendsto_nhds (hc.tendsto.mono_left nhds_within_le_nhds).norm
      (tendsto_norm_zpow_nhds_within_0_at_top hm)

@[simp]
theorem continuous_at_inv {𝕜 : Type _} [NondiscreteNormedField 𝕜] {x : 𝕜} : ContinuousAt Inv.inv x ↔ x ≠ 0 := by
  simpa [← (@zero_lt_one ℤ _ _).not_le] using @continuous_at_zpow _ _ (-1) x

end NormedField

theorem is_o_pow_pow_of_lt_left {r₁ r₂ : ℝ} (h₁ : 0 ≤ r₁) (h₂ : r₁ < r₂) :
    (fun n : ℕ => r₁ ^ n) =o[at_top] fun n => r₂ ^ n :=
  have H : 0 < r₂ := h₁.trans_lt h₂
  (is_o_of_tendsto fun n hn => False.elim <| H.ne' <| pow_eq_zero hn) <|
    (tendsto_pow_at_top_nhds_0_of_lt_1 (div_nonneg h₁ (h₁.trans h₂.le)) ((div_lt_one H).2 h₂)).congr fun n =>
      div_pow _ _ _

theorem is_O_pow_pow_of_le_left {r₁ r₂ : ℝ} (h₁ : 0 ≤ r₁) (h₂ : r₁ ≤ r₂) :
    (fun n : ℕ => r₁ ^ n) =O[at_top] fun n => r₂ ^ n :=
  h₂.eq_or_lt.elim (fun h => h ▸ is_O_refl _ _) fun h => (is_o_pow_pow_of_lt_left h₁ h).IsO

theorem is_o_pow_pow_of_abs_lt_left {r₁ r₂ : ℝ} (h : abs r₁ < abs r₂) :
    (fun n : ℕ => r₁ ^ n) =o[at_top] fun n => r₂ ^ n := by
  refine' (is_o.of_norm_left _).of_norm_right
  exact (is_o_pow_pow_of_lt_left (abs_nonneg r₁) h).congr (pow_abs r₁) (pow_abs r₂)

/-- Various statements equivalent to the fact that `f n` grows exponentially slower than `R ^ n`.

* 0: $f n = o(a ^ n)$ for some $-R < a < R$;
* 1: $f n = o(a ^ n)$ for some $0 < a < R$;
* 2: $f n = O(a ^ n)$ for some $-R < a < R$;
* 3: $f n = O(a ^ n)$ for some $0 < a < R$;
* 4: there exist `a < R` and `C` such that one of `C` and `R` is positive and $|f n| ≤ Ca^n$
     for all `n`;
* 5: there exists `0 < a < R` and a positive `C` such that $|f n| ≤ Ca^n$ for all `n`;
* 6: there exists `a < R` such that $|f n| ≤ a ^ n$ for sufficiently large `n`;
* 7: there exists `0 < a < R` such that $|f n| ≤ a ^ n$ for sufficiently large `n`.

NB: For backwards compatibility, if you add more items to the list, please append them at the end of
the list. -/
theorem tfae_exists_lt_is_o_pow (f : ℕ → ℝ) (R : ℝ) :
    Tfae
      [∃ a ∈ ioo (-R) R, f =o[at_top] pow a, ∃ a ∈ ioo 0 R, f =o[at_top] pow a, ∃ a ∈ ioo (-R) R, f =O[at_top] pow a,
        ∃ a ∈ ioo 0 R, f =O[at_top] pow a, ∃ a < R, ∃ (C : _)(h₀ : 0 < C ∨ 0 < R), ∀ n, abs (f n) ≤ C * a ^ n,
        ∃ a ∈ ioo 0 R, ∃ C > 0, ∀ n, abs (f n) ≤ C * a ^ n, ∃ a < R, ∀ᶠ n in at_top, abs (f n) ≤ a ^ n,
        ∃ a ∈ ioo 0 R, ∀ᶠ n in at_top, abs (f n) ≤ a ^ n] :=
  by
  have A : Ico 0 R ⊆ Ioo (-R) R := fun x hx => ⟨(neg_lt_zero.2 (hx.1.trans_lt hx.2)).trans_le hx.1, hx.2⟩
  have B : Ioo 0 R ⊆ Ioo (-R) R := subset.trans Ioo_subset_Ico_self A
  -- First we prove that 1-4 are equivalent using 2 → 3 → 4, 1 → 3, and 2 → 1
  tfae_have 1 → 3
  exact fun ⟨a, ha, H⟩ => ⟨a, ha, H.IsO⟩
  tfae_have 2 → 1
  exact fun ⟨a, ha, H⟩ => ⟨a, B ha, H⟩
  tfae_have 3 → 2
  · rintro ⟨a, ha, H⟩
    rcases exists_between (abs_lt.2 ha) with ⟨b, hab, hbR⟩
    exact
      ⟨b, ⟨(abs_nonneg a).trans_lt hab, hbR⟩, H.trans_is_o (is_o_pow_pow_of_abs_lt_left (hab.trans_le (le_abs_self b)))⟩
    
  tfae_have 2 → 4
  exact fun ⟨a, ha, H⟩ => ⟨a, ha, H.IsO⟩
  tfae_have 4 → 3
  exact fun ⟨a, ha, H⟩ => ⟨a, B ha, H⟩
  -- Add 5 and 6 using 4 → 6 → 5 → 3
  tfae_have 4 → 6
  · rintro ⟨a, ha, H⟩
    rcases bound_of_is_O_nat_at_top H with ⟨C, hC₀, hC⟩
    refine' ⟨a, ha, C, hC₀, fun n => _⟩
    simpa only [← Real.norm_eq_abs, ← abs_pow, ← abs_of_nonneg ha.1.le] using hC (pow_ne_zero n ha.1.ne')
    
  tfae_have 6 → 5
  exact fun ⟨a, ha, C, H₀, H⟩ => ⟨a, ha.2, C, Or.inl H₀, H⟩
  tfae_have 5 → 3
  · rintro ⟨a, ha, C, h₀, H⟩
    rcases sign_cases_of_C_mul_pow_nonneg fun n => (abs_nonneg _).trans (H n) with (rfl | ⟨hC₀, ha₀⟩)
    · obtain rfl : f = 0 := by
        ext n
        simpa using H n
      simp only [← lt_irreflₓ, ← false_orₓ] at h₀
      exact ⟨0, ⟨neg_lt_zero.2 h₀, h₀⟩, is_O_zero _ _⟩
      
    exact ⟨a, A ⟨ha₀, ha⟩, is_O_of_le' _ fun n => (H n).trans <| mul_le_mul_of_nonneg_left (le_abs_self _) hC₀.le⟩
    
  -- Add 7 and 8 using 2 → 8 → 7 → 3
  tfae_have 2 → 8
  · rintro ⟨a, ha, H⟩
    refine' ⟨a, ha, (H.def zero_lt_one).mono fun n hn => _⟩
    rwa [Real.norm_eq_abs, Real.norm_eq_abs, one_mulₓ, abs_pow, abs_of_pos ha.1] at hn
    
  tfae_have 8 → 7
  exact fun ⟨a, ha, H⟩ => ⟨a, ha.2, H⟩
  tfae_have 7 → 3
  · rintro ⟨a, ha, H⟩
    have : 0 ≤ a := nonneg_of_eventually_pow_nonneg (H.mono fun n => (abs_nonneg _).trans)
    refine' ⟨a, A ⟨this, ha⟩, is_O.of_bound 1 _⟩
    simpa only [← Real.norm_eq_abs, ← one_mulₓ, ← abs_pow, ← abs_of_nonneg this]
    
  tfae_finish

/-- For any natural `k` and a real `r > 1` we have `n ^ k = o(r ^ n)` as `n → ∞`. -/
theorem is_o_pow_const_const_pow_of_one_lt {R : Type _} [NormedRing R] (k : ℕ) {r : ℝ} (hr : 1 < r) :
    (fun n => n ^ k : ℕ → R) =o[at_top] fun n => r ^ n := by
  have : tendsto (fun x : ℝ => x ^ k) (𝓝[>] 1) (𝓝 1) :=
    ((continuous_id.pow k).tendsto' (1 : ℝ) 1 (one_pow _)).mono_left inf_le_left
  obtain ⟨r' : ℝ, hr' : r' ^ k < r, h1 : 1 < r'⟩ := ((this.eventually (gt_mem_nhds hr)).And self_mem_nhds_within).exists
  have h0 : 0 ≤ r' := zero_le_one.trans h1.le
  suffices : (fun n => n ^ k : ℕ → R) =O[at_top] fun n : ℕ => (r' ^ k) ^ n
  exact this.trans_is_o (is_o_pow_pow_of_lt_left (pow_nonneg h0 _) hr')
  conv in (r' ^ _) ^ _ => rw [← pow_mulₓ, mul_comm, pow_mulₓ]
  suffices : ∀ n : ℕ, ∥(n : R)∥ ≤ (r' - 1)⁻¹ * ∥(1 : R)∥ * ∥r' ^ n∥
  exact (is_O_of_le' _ this).pow _
  intro n
  rw [mul_right_commₓ]
  refine' n.norm_cast_le.trans (mul_le_mul_of_nonneg_right _ (norm_nonneg _))
  simpa [← div_eq_inv_mul, ← Real.norm_eq_abs, ← abs_of_nonneg h0] using n.cast_le_pow_div_sub h1

/-- For a real `r > 1` we have `n = o(r ^ n)` as `n → ∞`. -/
theorem is_o_coe_const_pow_of_one_lt {R : Type _} [NormedRing R] {r : ℝ} (hr : 1 < r) :
    (coe : ℕ → R) =o[at_top] fun n => r ^ n := by
  simpa only [← pow_oneₓ] using @is_o_pow_const_const_pow_of_one_lt R _ 1 _ hr

/-- If `∥r₁∥ < r₂`, then for any naturak `k` we have `n ^ k r₁ ^ n = o (r₂ ^ n)` as `n → ∞`. -/
theorem is_o_pow_const_mul_const_pow_const_pow_of_norm_lt {R : Type _} [NormedRing R] (k : ℕ) {r₁ : R} {r₂ : ℝ}
    (h : ∥r₁∥ < r₂) : (fun n => n ^ k * r₁ ^ n : ℕ → R) =o[at_top] fun n => r₂ ^ n := by
  by_cases' h0 : r₁ = 0
  · refine' (is_o_zero _ _).congr' (mem_at_top_sets.2 <| ⟨1, fun n hn => _⟩) eventually_eq.rfl
    simp [← zero_pow (zero_lt_one.trans_le hn), ← h0]
    
  rw [← Ne.def, ← norm_pos_iff] at h0
  have A : (fun n => n ^ k : ℕ → R) =o[at_top] fun n => (r₂ / ∥r₁∥) ^ n :=
    is_o_pow_const_const_pow_of_one_lt k ((one_lt_div h0).2 h)
  suffices (fun n => r₁ ^ n) =O[at_top] fun n => ∥r₁∥ ^ n by
    simpa [← div_mul_cancel _ (pow_pos h0 _).ne'] using A.mul_is_O this
  exact
    is_O.of_bound 1
      (by
        simpa using eventually_norm_pow_le r₁)

theorem tendsto_pow_const_div_const_pow_of_one_lt (k : ℕ) {r : ℝ} (hr : 1 < r) :
    Tendsto (fun n => n ^ k / r ^ n : ℕ → ℝ) atTop (𝓝 0) :=
  (is_o_pow_const_const_pow_of_one_lt k hr).tendsto_div_nhds_zero

/-- If `|r| < 1`, then `n ^ k r ^ n` tends to zero for any natural `k`. -/
theorem tendsto_pow_const_mul_const_pow_of_abs_lt_one (k : ℕ) {r : ℝ} (hr : abs r < 1) :
    Tendsto (fun n => n ^ k * r ^ n : ℕ → ℝ) atTop (𝓝 0) := by
  by_cases' h0 : r = 0
  · exact
      tendsto_const_nhds.congr'
        (mem_at_top_sets.2
          ⟨1, fun n hn => by
            simp [← zero_lt_one.trans_le hn, ← h0]⟩)
    
  have hr' : 1 < (abs r)⁻¹ := one_lt_inv (abs_pos.2 h0) hr
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simpa [← div_eq_mul_inv] using tendsto_pow_const_div_const_pow_of_one_lt k hr'

/-- If `0 ≤ r < 1`, then `n ^ k r ^ n` tends to zero for any natural `k`.
This is a specialized version of `tendsto_pow_const_mul_const_pow_of_abs_lt_one`, singled out
for ease of application. -/
theorem tendsto_pow_const_mul_const_pow_of_lt_one (k : ℕ) {r : ℝ} (hr : 0 ≤ r) (h'r : r < 1) :
    Tendsto (fun n => n ^ k * r ^ n : ℕ → ℝ) atTop (𝓝 0) :=
  tendsto_pow_const_mul_const_pow_of_abs_lt_one k (abs_lt.2 ⟨neg_one_lt_zero.trans_le hr, h'r⟩)

/-- If `|r| < 1`, then `n * r ^ n` tends to zero. -/
theorem tendsto_self_mul_const_pow_of_abs_lt_one {r : ℝ} (hr : abs r < 1) :
    Tendsto (fun n => n * r ^ n : ℕ → ℝ) atTop (𝓝 0) := by
  simpa only [← pow_oneₓ] using tendsto_pow_const_mul_const_pow_of_abs_lt_one 1 hr

/-- If `0 ≤ r < 1`, then `n * r ^ n` tends to zero. This is a specialized version of
`tendsto_self_mul_const_pow_of_abs_lt_one`, singled out for ease of application. -/
theorem tendsto_self_mul_const_pow_of_lt_one {r : ℝ} (hr : 0 ≤ r) (h'r : r < 1) :
    Tendsto (fun n => n * r ^ n : ℕ → ℝ) atTop (𝓝 0) := by
  simpa only [← pow_oneₓ] using tendsto_pow_const_mul_const_pow_of_lt_one 1 hr h'r

/-- In a normed ring, the powers of an element x with `∥x∥ < 1` tend to zero. -/
theorem tendsto_pow_at_top_nhds_0_of_norm_lt_1 {R : Type _} [NormedRing R] {x : R} (h : ∥x∥ < 1) :
    Tendsto (fun n : ℕ => x ^ n) atTop (𝓝 0) := by
  apply squeeze_zero_norm' (eventually_norm_pow_le x)
  exact tendsto_pow_at_top_nhds_0_of_lt_1 (norm_nonneg _) h

theorem tendsto_pow_at_top_nhds_0_of_abs_lt_1 {r : ℝ} (h : abs r < 1) : Tendsto (fun n : ℕ => r ^ n) atTop (𝓝 0) :=
  tendsto_pow_at_top_nhds_0_of_norm_lt_1 h

/-! ### Geometric series-/


section Geometric

variable {K : Type _} [NormedField K] {ξ : K}

theorem has_sum_geometric_of_norm_lt_1 (h : ∥ξ∥ < 1) : HasSum (fun n : ℕ => ξ ^ n) (1 - ξ)⁻¹ := by
  have xi_ne_one : ξ ≠ 1 := by
    contrapose! h
    simp [← h]
  have A : tendsto (fun n => (ξ ^ n - 1) * (ξ - 1)⁻¹) at_top (𝓝 ((0 - 1) * (ξ - 1)⁻¹)) :=
    ((tendsto_pow_at_top_nhds_0_of_norm_lt_1 h).sub tendsto_const_nhds).mul tendsto_const_nhds
  rw [has_sum_iff_tendsto_nat_of_summable_norm]
  · simpa [← geom_sum_eq, ← xi_ne_one, ← neg_inv, ← div_eq_mul_inv] using A
    
  · simp [← norm_pow, ← summable_geometric_of_lt_1 (norm_nonneg _) h]
    

theorem summable_geometric_of_norm_lt_1 (h : ∥ξ∥ < 1) : Summable fun n : ℕ => ξ ^ n :=
  ⟨_, has_sum_geometric_of_norm_lt_1 h⟩

theorem tsum_geometric_of_norm_lt_1 (h : ∥ξ∥ < 1) : (∑' n : ℕ, ξ ^ n) = (1 - ξ)⁻¹ :=
  (has_sum_geometric_of_norm_lt_1 h).tsum_eq

theorem has_sum_geometric_of_abs_lt_1 {r : ℝ} (h : abs r < 1) : HasSum (fun n : ℕ => r ^ n) (1 - r)⁻¹ :=
  has_sum_geometric_of_norm_lt_1 h

theorem summable_geometric_of_abs_lt_1 {r : ℝ} (h : abs r < 1) : Summable fun n : ℕ => r ^ n :=
  summable_geometric_of_norm_lt_1 h

theorem tsum_geometric_of_abs_lt_1 {r : ℝ} (h : abs r < 1) : (∑' n : ℕ, r ^ n) = (1 - r)⁻¹ :=
  tsum_geometric_of_norm_lt_1 h

/-- A geometric series in a normed field is summable iff the norm of the common ratio is less than
one. -/
@[simp]
theorem summable_geometric_iff_norm_lt_1 : (Summable fun n : ℕ => ξ ^ n) ↔ ∥ξ∥ < 1 := by
  refine' ⟨fun h => _, summable_geometric_of_norm_lt_1⟩
  obtain ⟨k : ℕ, hk : dist (ξ ^ k) 0 < 1⟩ := (h.tendsto_cofinite_zero.eventually (ball_mem_nhds _ zero_lt_one)).exists
  simp only [← norm_pow, ← dist_zero_right] at hk
  rw [← one_pow k] at hk
  exact lt_of_pow_lt_pow _ zero_le_one hk

end Geometric

section MulGeometric

theorem summable_norm_pow_mul_geometric_of_norm_lt_1 {R : Type _} [NormedRing R] (k : ℕ) {r : R} (hr : ∥r∥ < 1) :
    Summable fun n : ℕ => ∥(n ^ k * r ^ n : R)∥ := by
  rcases exists_between hr with ⟨r', hrr', h⟩
  exact
    summable_of_is_O_nat (summable_geometric_of_lt_1 ((norm_nonneg _).trans hrr'.le) h)
      (is_o_pow_const_mul_const_pow_const_pow_of_norm_lt _ hrr').IsO.norm_left

theorem summable_pow_mul_geometric_of_norm_lt_1 {R : Type _} [NormedRing R] [CompleteSpace R] (k : ℕ) {r : R}
    (hr : ∥r∥ < 1) : Summable (fun n => n ^ k * r ^ n : ℕ → R) :=
  summable_of_summable_norm <| summable_norm_pow_mul_geometric_of_norm_lt_1 _ hr

/-- If `∥r∥ < 1`, then `∑' n : ℕ, n * r ^ n = r / (1 - r) ^ 2`, `has_sum` version. -/
theorem has_sum_coe_mul_geometric_of_norm_lt_1 {𝕜 : Type _} [NormedField 𝕜] [CompleteSpace 𝕜] {r : 𝕜} (hr : ∥r∥ < 1) :
    HasSum (fun n => n * r ^ n : ℕ → 𝕜) (r / (1 - r) ^ 2) := by
  have A : Summable (fun n => n * r ^ n : ℕ → 𝕜) := by
    simpa using summable_pow_mul_geometric_of_norm_lt_1 1 hr
  have B : HasSum (pow r : ℕ → 𝕜) (1 - r)⁻¹ := has_sum_geometric_of_norm_lt_1 hr
  refine' A.has_sum_iff.2 _
  have hr' : r ≠ 1 := by
    rintro rfl
    simpa [← lt_irreflₓ] using hr
  set s : 𝕜 := ∑' n : ℕ, n * r ^ n
  calc s = (1 - r) * s / (1 - r) := (mul_div_cancel_left _ (sub_ne_zero.2 hr'.symm)).symm _ = (s - r * s) / (1 - r) :=
      by
      rw [sub_mul, one_mulₓ]_ = (((0 : ℕ) * r ^ 0 + ∑' n : ℕ, (n + 1 : ℕ) * r ^ (n + 1)) - r * s) / (1 - r) := by
      rw [← tsum_eq_zero_add A]_ = ((r * ∑' n : ℕ, (n + 1) * r ^ n) - r * s) / (1 - r) := by
      simp [← pow_succₓ, ← mul_left_commₓ _ r, ← tsum_mul_left]_ = r / (1 - r) ^ 2 := by
      simp [← add_mulₓ, ← tsum_add A B.summable, ← mul_addₓ, ← B.tsum_eq, div_eq_mul_inv, ← sq, ← div_div]

/-- If `∥r∥ < 1`, then `∑' n : ℕ, n * r ^ n = r / (1 - r) ^ 2`. -/
theorem tsum_coe_mul_geometric_of_norm_lt_1 {𝕜 : Type _} [NormedField 𝕜] [CompleteSpace 𝕜] {r : 𝕜} (hr : ∥r∥ < 1) :
    (∑' n : ℕ, n * r ^ n : 𝕜) = r / (1 - r) ^ 2 :=
  (has_sum_coe_mul_geometric_of_norm_lt_1 hr).tsum_eq

end MulGeometric

section SummableLeGeometric

variable [SemiNormedGroup α] {r C : ℝ} {f : ℕ → α}

theorem SemiNormedGroup.cauchy_seq_of_le_geometric {C : ℝ} {r : ℝ} (hr : r < 1) {u : ℕ → α}
    (h : ∀ n, ∥u n - u (n + 1)∥ ≤ C * r ^ n) : CauchySeq u :=
  cauchy_seq_of_le_geometric r C hr
    (by
      simpa [← dist_eq_norm] using h)

theorem dist_partial_sum_le_of_le_geometric (hf : ∀ n, ∥f n∥ ≤ C * r ^ n) (n : ℕ) :
    dist (∑ i in range n, f i) (∑ i in range (n + 1), f i) ≤ C * r ^ n := by
  rw [sum_range_succ, dist_eq_norm, ← norm_neg, neg_sub, add_sub_cancel']
  exact hf n

/-- If `∥f n∥ ≤ C * r ^ n` for all `n : ℕ` and some `r < 1`, then the partial sums of `f` form a
Cauchy sequence. This lemma does not assume `0 ≤ r` or `0 ≤ C`. -/
theorem cauchy_seq_finset_of_geometric_bound (hr : r < 1) (hf : ∀ n, ∥f n∥ ≤ C * r ^ n) :
    CauchySeq fun s : Finset ℕ => ∑ x in s, f x :=
  cauchy_seq_finset_of_norm_bounded _ (aux_has_sum_of_le_geometric hr (dist_partial_sum_le_of_le_geometric hf)).Summable
    hf

/-- If `∥f n∥ ≤ C * r ^ n` for all `n : ℕ` and some `r < 1`, then the partial sums of `f` are within
distance `C * r ^ n / (1 - r)` of the sum of the series. This lemma does not assume `0 ≤ r` or
`0 ≤ C`. -/
theorem norm_sub_le_of_geometric_bound_of_has_sum (hr : r < 1) (hf : ∀ n, ∥f n∥ ≤ C * r ^ n) {a : α} (ha : HasSum f a)
    (n : ℕ) : ∥(∑ x in Finset.range n, f x) - a∥ ≤ C * r ^ n / (1 - r) := by
  rw [← dist_eq_norm]
  apply dist_le_of_le_geometric_of_tendsto r C hr (dist_partial_sum_le_of_le_geometric hf)
  exact ha.tendsto_sum_nat

@[simp]
theorem dist_partial_sum (u : ℕ → α) (n : ℕ) : dist (∑ k in range (n + 1), u k) (∑ k in range n, u k) = ∥u n∥ := by
  simp [← dist_eq_norm, ← sum_range_succ]

@[simp]
theorem dist_partial_sum' (u : ℕ → α) (n : ℕ) : dist (∑ k in range n, u k) (∑ k in range (n + 1), u k) = ∥u n∥ := by
  simp [← dist_eq_norm', ← sum_range_succ]

theorem cauchy_series_of_le_geometric {C : ℝ} {u : ℕ → α} {r : ℝ} (hr : r < 1) (h : ∀ n, ∥u n∥ ≤ C * r ^ n) :
    CauchySeq fun n => ∑ k in range n, u k :=
  cauchy_seq_of_le_geometric r C hr
    (by
      simp [← h])

theorem NormedGroup.cauchy_series_of_le_geometric' {C : ℝ} {u : ℕ → α} {r : ℝ} (hr : r < 1)
    (h : ∀ n, ∥u n∥ ≤ C * r ^ n) : CauchySeq fun n => ∑ k in range (n + 1), u k :=
  (cauchy_series_of_le_geometric hr h).comp_tendsto <| tendsto_add_at_top_nat 1

theorem NormedGroup.cauchy_series_of_le_geometric'' {C : ℝ} {u : ℕ → α} {N : ℕ} {r : ℝ} (hr₀ : 0 < r) (hr₁ : r < 1)
    (h : ∀, ∀ n ≥ N, ∀, ∥u n∥ ≤ C * r ^ n) : CauchySeq fun n => ∑ k in range (n + 1), u k := by
  set v : ℕ → α := fun n => if n < N then 0 else u n
  have hC : 0 ≤ C := (zero_le_mul_right <| pow_pos hr₀ N).mp ((norm_nonneg _).trans <| h N <| le_reflₓ N)
  have : ∀, ∀ n ≥ N, ∀, u n = v n := by
    intro n hn
    simp [← v, ← hn, ← if_neg (not_lt.mpr hn)]
  refine' cauchy_seq_sum_of_eventually_eq this (NormedGroup.cauchy_series_of_le_geometric' hr₁ _)
  · exact C
    
  intro n
  dsimp' [← v]
  split_ifs with H H
  · rw [norm_zero]
    exact mul_nonneg hC (pow_nonneg hr₀.le _)
    
  · push_neg  at H
    exact h _ H
    

end SummableLeGeometric

section NormedRingGeometric

variable {R : Type _} [NormedRing R] [CompleteSpace R]

open NormedSpace

/-- A geometric series in a complete normed ring is summable.
Proved above (same name, different namespace) for not-necessarily-complete normed fields. -/
theorem NormedRing.summable_geometric_of_norm_lt_1 (x : R) (h : ∥x∥ < 1) : Summable fun n : ℕ => x ^ n := by
  have h1 : Summable fun n : ℕ => ∥x∥ ^ n := summable_geometric_of_lt_1 (norm_nonneg _) h
  refine' summable_of_norm_bounded_eventually _ h1 _
  rw [Nat.cofinite_eq_at_top]
  exact eventually_norm_pow_le x

/-- Bound for the sum of a geometric series in a normed ring.  This formula does not assume that the
normed ring satisfies the axiom `∥1∥ = 1`. -/
theorem NormedRing.tsum_geometric_of_norm_lt_1 (x : R) (h : ∥x∥ < 1) :
    ∥∑' n : ℕ, x ^ n∥ ≤ ∥(1 : R)∥ - 1 + (1 - ∥x∥)⁻¹ := by
  rw [tsum_eq_zero_add (NormedRing.summable_geometric_of_norm_lt_1 x h)]
  simp only [← pow_zeroₓ]
  refine' le_transₓ (norm_add_le _ _) _
  have : ∥∑' b : ℕ, (fun n => x ^ (n + 1)) b∥ ≤ (1 - ∥x∥)⁻¹ - 1 := by
    refine' tsum_of_norm_bounded _ fun b => norm_pow_le' _ (Nat.succ_posₓ b)
    convert (has_sum_nat_add_iff' 1).mpr (has_sum_geometric_of_lt_1 (norm_nonneg x) h)
    simp
  linarith

theorem geom_series_mul_neg (x : R) (h : ∥x∥ < 1) : (∑' i : ℕ, x ^ i) * (1 - x) = 1 := by
  have := (NormedRing.summable_geometric_of_norm_lt_1 x h).HasSum.mul_right (1 - x)
  refine' tendsto_nhds_unique this.tendsto_sum_nat _
  have : tendsto (fun n : ℕ => 1 - x ^ n) at_top (𝓝 1) := by
    simpa using tendsto_const_nhds.sub (tendsto_pow_at_top_nhds_0_of_norm_lt_1 h)
  convert ← this
  ext n
  rw [← geom_sum_mul_neg, Finset.sum_mul]

theorem mul_neg_geom_series (x : R) (h : ∥x∥ < 1) : ((1 - x) * ∑' i : ℕ, x ^ i) = 1 := by
  have := (NormedRing.summable_geometric_of_norm_lt_1 x h).HasSum.mul_left (1 - x)
  refine' tendsto_nhds_unique this.tendsto_sum_nat _
  have : tendsto (fun n : ℕ => 1 - x ^ n) at_top (nhds 1) := by
    simpa using tendsto_const_nhds.sub (tendsto_pow_at_top_nhds_0_of_norm_lt_1 h)
  convert ← this
  ext n
  rw [← mul_neg_geom_sum, Finset.mul_sum]

end NormedRingGeometric

/-! ### Summability tests based on comparison with geometric series -/


theorem summable_of_ratio_norm_eventually_le {α : Type _} [SemiNormedGroup α] [CompleteSpace α] {f : ℕ → α} {r : ℝ}
    (hr₁ : r < 1) (h : ∀ᶠ n in at_top, ∥f (n + 1)∥ ≤ r * ∥f n∥) : Summable f := by
  by_cases' hr₀ : 0 ≤ r
  · rw [eventually_at_top] at h
    rcases h with ⟨N, hN⟩
    rw [← @summable_nat_add_iff α _ _ _ _ N]
    refine'
      summable_of_norm_bounded (fun n => ∥f N∥ * r ^ n) (Summable.mul_left _ <| summable_geometric_of_lt_1 hr₀ hr₁)
        fun n => _
    conv_rhs => rw [mul_comm, ← zero_addₓ N]
    refine' le_geom hr₀ n fun i _ => _
    convert hN (i + N) (N.le_add_left i) using 3
    ac_rfl
    
  · push_neg  at hr₀
    refine' summable_of_norm_bounded_eventually 0 summable_zero _
    rw [Nat.cofinite_eq_at_top]
    filter_upwards [h] with _ hn
    by_contra' h
    exact not_lt.mpr (norm_nonneg _) (lt_of_le_of_ltₓ hn <| mul_neg_of_neg_of_pos hr₀ h)
    

theorem summable_of_ratio_test_tendsto_lt_one {α : Type _} [NormedGroup α] [CompleteSpace α] {f : ℕ → α} {l : ℝ}
    (hl₁ : l < 1) (hf : ∀ᶠ n in at_top, f n ≠ 0) (h : Tendsto (fun n => ∥f (n + 1)∥ / ∥f n∥) atTop (𝓝 l)) :
    Summable f := by
  rcases exists_between hl₁ with ⟨r, hr₀, hr₁⟩
  refine' summable_of_ratio_norm_eventually_le hr₁ _
  filter_upwards [eventually_le_of_tendsto_lt hr₀ h, hf] with _ _ h₁
  rwa [← div_le_iff (norm_pos_iff.mpr h₁)]

theorem not_summable_of_ratio_norm_eventually_ge {α : Type _} [SemiNormedGroup α] {f : ℕ → α} {r : ℝ} (hr : 1 < r)
    (hf : ∃ᶠ n in at_top, ∥f n∥ ≠ 0) (h : ∀ᶠ n in at_top, r * ∥f n∥ ≤ ∥f (n + 1)∥) : ¬Summable f := by
  rw [eventually_at_top] at h
  rcases h with ⟨N₀, hN₀⟩
  rw [frequently_at_top] at hf
  rcases hf N₀ with ⟨N, hNN₀ : N₀ ≤ N, hN⟩
  rw [← @summable_nat_add_iff α _ _ _ _ N]
  refine' mt Summable.tendsto_at_top_zero fun h' => not_tendsto_at_top_of_tendsto_nhds (tendsto_norm_zero.comp h') _
  convert tendsto_at_top_of_geom_le _ hr _
  · refine' lt_of_le_of_neₓ (norm_nonneg _) _
    intro h''
    specialize hN₀ N hNN₀
    simp only [← comp_app, ← zero_addₓ] at h''
    exact hN h''.symm
    
  · intro i
    dsimp' only [← comp_app]
    convert hN₀ (i + N) (hNN₀.trans (N.le_add_left i)) using 3
    ac_rfl
    

theorem not_summable_of_ratio_test_tendsto_gt_one {α : Type _} [SemiNormedGroup α] {f : ℕ → α} {l : ℝ} (hl : 1 < l)
    (h : Tendsto (fun n => ∥f (n + 1)∥ / ∥f n∥) atTop (𝓝 l)) : ¬Summable f := by
  have key : ∀ᶠ n in at_top, ∥f n∥ ≠ 0 := by
    filter_upwards [eventually_ge_of_tendsto_gt hl h] with _ hn hc
    rw [hc, div_zero] at hn
    linarith
  rcases exists_between hl with ⟨r, hr₀, hr₁⟩
  refine' not_summable_of_ratio_norm_eventually_ge hr₀ key.frequently _
  filter_upwards [eventually_ge_of_tendsto_gt hr₁ h, key] with _ _ h₁
  rwa [← le_div_iff (lt_of_le_of_neₓ (norm_nonneg _) h₁.symm)]

section

/-! ### Dirichlet and alternating series tests -/


variable {E : Type _} [NormedGroup E] [NormedSpace ℝ E]

variable {b : ℝ} {f : ℕ → ℝ} {z : ℕ → E}

/-- **Dirichlet's Test** for monotone sequences. -/
theorem Monotone.cauchy_seq_series_mul_of_tendsto_zero_of_bounded (hfa : Monotone f) (hf0 : Tendsto f atTop (𝓝 0))
    (hgb : ∀ n, ∥∑ i in range n, z i∥ ≤ b) : CauchySeq fun n => ∑ i in range (n + 1), f i • z i := by
  simp_rw [Finset.sum_range_by_parts _ _ (Nat.succ _), sub_eq_add_neg, Nat.succ_sub_succ_eq_sub, tsub_zero]
  apply
    (NormedField.tendsto_zero_smul_of_tendsto_zero_of_bounded hf0
          ⟨b, eventually_map.mpr <| eventually_of_forall fun n => hgb <| n + 1⟩).CauchySeq.add
  apply (cauchy_seq_range_of_norm_bounded _ _ (_ : ∀ n, _ ≤ b * abs (f (n + 1) - f n))).neg
  · exact normed_uniform_group
    
  · simp_rw [abs_of_nonneg (sub_nonneg_of_le (hfa (Nat.le_succₓ _))), ← mul_sum]
    apply real.uniform_continuous_mul_const.comp_cauchy_seq
    simp_rw [sum_range_sub, sub_eq_add_neg]
    exact (tendsto.cauchy_seq hf0).AddConst
    
  · intro n
    rw [norm_smul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hgb _) (abs_nonneg _)
    

/-- **Dirichlet's test** for antitone sequences. -/
theorem Antitone.cauchy_seq_series_mul_of_tendsto_zero_of_bounded (hfa : Antitone f) (hf0 : Tendsto f atTop (𝓝 0))
    (hzb : ∀ n, ∥∑ i in range n, z i∥ ≤ b) : CauchySeq fun n => ∑ i in range (n + 1), f i • z i := by
  have hfa' : Monotone fun n => -f n := fun _ _ hab => neg_le_neg <| hfa hab
  have hf0' : tendsto (fun n => -f n) at_top (𝓝 0) := by
    convert hf0.neg
    norm_num
  convert (hfa'.cauchy_seq_series_mul_of_tendsto_zero_of_bounded hf0' hzb).neg
  funext
  simp

theorem norm_sum_neg_one_pow_le (n : ℕ) : ∥∑ i in range n, (-1 : ℝ) ^ i∥ ≤ 1 := by
  rw [neg_one_geom_sum]
  split_ifs <;> norm_num

/-- The **alternating series test** for monotone sequences.
See also `tendsto_alternating_series_of_monotone_tendsto_zero`. -/
theorem Monotone.cauchy_seq_alternating_series_of_tendsto_zero (hfa : Monotone f) (hf0 : Tendsto f atTop (𝓝 0)) :
    CauchySeq fun n => ∑ i in range (n + 1), -1 ^ i * f i := by
  simp_rw [mul_comm]
  exact hfa.cauchy_seq_series_mul_of_tendsto_zero_of_bounded hf0 norm_sum_neg_one_pow_le

/-- The **alternating series test** for monotone sequences. -/
theorem Monotone.tendsto_alternating_series_of_tendsto_zero (hfa : Monotone f) (hf0 : Tendsto f atTop (𝓝 0)) :
    ∃ l, Tendsto (fun n => ∑ i in range (n + 1), -1 ^ i * f i) atTop (𝓝 l) :=
  cauchy_seq_tendsto_of_complete <| hfa.cauchy_seq_alternating_series_of_tendsto_zero hf0

/-- The **alternating series test** for antitone sequences.
See also `tendsto_alternating_series_of_antitone_tendsto_zero`. -/
theorem Antitone.cauchy_seq_alternating_series_of_tendsto_zero (hfa : Antitone f) (hf0 : Tendsto f atTop (𝓝 0)) :
    CauchySeq fun n => ∑ i in range (n + 1), -1 ^ i * f i := by
  simp_rw [mul_comm]
  exact hfa.cauchy_seq_series_mul_of_tendsto_zero_of_bounded hf0 norm_sum_neg_one_pow_le

/-- The **alternating series test** for antitone sequences. -/
theorem Antitone.tendsto_alternating_series_of_tendsto_zero (hfa : Antitone f) (hf0 : Tendsto f atTop (𝓝 0)) :
    ∃ l, Tendsto (fun n => ∑ i in range (n + 1), -1 ^ i * f i) atTop (𝓝 l) :=
  cauchy_seq_tendsto_of_complete <| hfa.cauchy_seq_alternating_series_of_tendsto_zero hf0

end

/-!
### Factorial
-/


/-- The series `∑' n, x ^ n / n!` is summable of any `x : ℝ`. See also `exp_series_div_summable`
for a version that also works in `ℂ`, and `exp_series_summable'` for a version that works in
any normed algebra over `ℝ` or `ℂ`. -/
theorem Real.summable_pow_div_factorial (x : ℝ) : Summable (fun n => x ^ n / n ! : ℕ → ℝ) := by
  -- We start with trivial extimates
  have A : (0 : ℝ) < ⌊∥x∥⌋₊ + 1 :=
    zero_lt_one.trans_le
      (by
        simp )
  have B : ∥x∥ / (⌊∥x∥⌋₊ + 1) < 1 := (div_lt_one A).2 (Nat.lt_floor_add_one _)
  -- Then we apply the ratio test. The estimate works for `n ≥ ⌊∥x∥⌋₊`.
  suffices : ∀, ∀ n ≥ ⌊∥x∥⌋₊, ∀, ∥x ^ (n + 1) / (n + 1)!∥ ≤ ∥x∥ / (⌊∥x∥⌋₊ + 1) * ∥x ^ n / ↑n !∥
  exact summable_of_ratio_norm_eventually_le B (eventually_at_top.2 ⟨⌊∥x∥⌋₊, this⟩)
  -- Finally, we prove the upper estimate
  intro n hn
  calc ∥x ^ (n + 1) / (n + 1)!∥ = ∥x∥ / (n + 1) * ∥x ^ n / n !∥ := by
      rw [pow_succₓ, Nat.factorial_succ, Nat.cast_mulₓ, ← div_mul_div_comm, norm_mul, norm_div, Real.norm_coe_nat,
        Nat.cast_succₓ]_ ≤ ∥x∥ / (⌊∥x∥⌋₊ + 1) * ∥x ^ n / n !∥ :=
      by
      mono* with 0 ≤ ∥x ^ n / n !∥, 0 ≤ ∥x∥ <;> apply norm_nonneg

theorem Real.tendsto_pow_div_factorial_at_top (x : ℝ) : Tendsto (fun n => x ^ n / n ! : ℕ → ℝ) atTop (𝓝 0) :=
  (Real.summable_pow_div_factorial x).tendsto_at_top_zero

