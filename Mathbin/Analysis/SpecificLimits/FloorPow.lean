/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathbin.Analysis.SpecificLimits.Basic
import Mathbin.Analysis.SpecialFunctions.Pow

/-!
# Results on discretized exponentials

We state several auxiliary results pertaining to sequences of the form `⌊c^n⌋₊`.

* `tendsto_div_of_monotone_of_tendsto_div_floor_pow`: If a monotone sequence `u` is such that
  `u ⌊c^n⌋₊ / ⌊c^n⌋₊` converges to a limit `l` for all `c > 1`, then `u n / n` tends to `l`.
* `sum_div_nat_floor_pow_sq_le_div_sq`: The sum of `1/⌊c^i⌋₊^2` above a threshold `j` is comparable
  to `1/j^2`, up to a multiplicative constant.
-/


open Filter Finset

open TopologicalSpace BigOperators

/-- If a monotone sequence `u` is such that `u n / n` tends to a limit `l` along subsequences with
exponential growth rate arbitrarily close to `1`, then `u n / n` tends to `l`. -/
theorem tendsto_div_of_monotone_of_exists_subseq_tendsto_div (u : ℕ → ℝ) (l : ℝ) (hmono : Monotone u)
    (hlim :
      ∀ a : ℝ,
        1 < a →
          ∃ c : ℕ → ℕ,
            (∀ᶠ n in at_top, (c (n + 1) : ℝ) ≤ a * c n) ∧
              Tendsto c atTop atTop ∧ Tendsto (fun n => u (c n) / c n) atTop (𝓝 l)) :
    Tendsto (fun n => u n / n) atTop (𝓝 l) := by
  /- To check the result up to some `ε > 0`, we use a sequence `c` for which the ratio
    `c (N+1) / c N` is bounded by `1 + ε`. Sandwiching a given `n` between two consecutive values of
    `c`, say `c N` and `c (N+1)`, one can then bound `u n / n` from above by `u (c N) / c (N - 1)`
    and from below by `u (c (N - 1)) / c N` (using that `u` is monotone), which are both comparable
    to the limit `l` up to `1 + ε`.
    We give a version of this proof by clearing out denominators first, to avoid discussing the sign
    of different quantities. -/
  have lnonneg : 0 ≤ l := by
    rcases hlim 2 one_lt_two with ⟨c, cgrowth, ctop, clim⟩
    have : tendsto (fun n => u 0 / c n) at_top (𝓝 0) :=
      tendsto_const_nhds.div_at_top (tendsto_coe_nat_at_top_iff.2 ctop)
    apply le_of_tendsto_of_tendsto' this clim fun n => _
    simp_rw [div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left (hmono (zero_le _)) (inv_nonneg.2 (Nat.cast_nonneg _))
  have A : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in at_top, u n - n * l ≤ ε * (1 + ε + l) * n := by
    intro ε εpos
    rcases hlim (1 + ε) ((lt_add_iff_pos_right _).2 εpos) with ⟨c, cgrowth, ctop, clim⟩
    have L : ∀ᶠ n in at_top, u (c n) - c n * l ≤ ε * c n := by
      rw [← tendsto_sub_nhds_zero_iff, ← Asymptotics.is_o_one_iff ℝ, Asymptotics.is_o_iff] at clim
      filter_upwards [clim εpos, ctop (Ioi_mem_at_top 0)] with n hn cnpos'
      have cnpos : 0 < c n := cnpos'
      calc u (c n) - c n * l = (u (c n) / c n - l) * c n := by
          simp' only [← cnpos.ne', ← Ne.def, ← Nat.cast_eq_zero, ← not_false_iff] with field_simps _ ≤ ε * c n := by
          apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
          simp only [← mul_oneₓ, ← Real.norm_eq_abs, ← abs_one] at hn
          exact le_transₓ (le_abs_self _) hn
    obtain ⟨a, ha⟩ : ∃ a : ℕ, ∀ b : ℕ, a ≤ b → (c (b + 1) : ℝ) ≤ (1 + ε) * c b ∧ u (c b) - c b * l ≤ ε * c b :=
      eventually_at_top.1 (cgrowth.and L)
    let M :=
      ((Finset.range (a + 1)).Image fun i => c i).max'
        (by
          simp )
    filter_upwards [Ici_mem_at_top M] with n hn
    have exN : ∃ N, n < c N := by
      rcases(tendsto_at_top.1 ctop (n + 1)).exists with ⟨N, hN⟩
      exact
        ⟨N, by
          linarith only [hN]⟩
    let N := Nat.findₓ exN
    have ncN : n < c N := Nat.find_specₓ exN
    have aN : a + 1 ≤ N := by
      by_contra' h
      have cNM : c N ≤ M := by
        apply le_max'
        apply mem_image_of_mem
        exact mem_range.2 h
      exact lt_irreflₓ _ ((cNM.trans hn).trans_lt ncN)
    have Npos : 0 < N := lt_of_lt_of_leₓ Nat.succ_pos' aN
    have cNn : c (N - 1) ≤ n := by
      have : N - 1 < N := Nat.pred_ltₓ Npos.ne'
      simpa only [← not_ltₓ] using Nat.find_minₓ exN this
    have IcN : (c N : ℝ) ≤ (1 + ε) * c (N - 1) := by
      have A : a ≤ N - 1 := by
        linarith only [aN, Npos]
      have B : N - 1 + 1 = N := Nat.succ_pred_eq_of_posₓ Npos
      have := (ha _ A).1
      rwa [B] at this
    calc u n - n * l ≤ u (c N) - c (N - 1) * l := by
        apply sub_le_sub (hmono ncN.le)
        apply mul_le_mul_of_nonneg_right (Nat.cast_le.2 cNn) lnonneg _ = u (c N) - c N * l + (c N - c (N - 1)) * l := by
        ring _ ≤ ε * c N + ε * c (N - 1) * l := by
        apply add_le_add
        · apply (ha _ _).2
          exact
            le_transₓ
              (by
                simp only [← le_add_iff_nonneg_right, ← zero_le'])
              aN
          
        · apply mul_le_mul_of_nonneg_right _ lnonneg
          linarith only [IcN]
          _ ≤ ε * ((1 + ε) * c (N - 1)) + ε * c (N - 1) * l :=
        add_le_add (mul_le_mul_of_nonneg_left IcN εpos.le) le_rfl _ = ε * (1 + ε + l) * c (N - 1) := by
        ring _ ≤ ε * (1 + ε + l) * n := by
        refine' mul_le_mul_of_nonneg_left (Nat.cast_le.2 cNn) _
        apply mul_nonneg εpos.le
        linarith only [εpos, lnonneg]
  have B : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in at_top, (n : ℝ) * l - u n ≤ ε * (1 + l) * n := by
    intro ε εpos
    rcases hlim (1 + ε) ((lt_add_iff_pos_right _).2 εpos) with ⟨c, cgrowth, ctop, clim⟩
    have L : ∀ᶠ n : ℕ in at_top, (c n : ℝ) * l - u (c n) ≤ ε * c n := by
      rw [← tendsto_sub_nhds_zero_iff, ← Asymptotics.is_o_one_iff ℝ, Asymptotics.is_o_iff] at clim
      filter_upwards [clim εpos, ctop (Ioi_mem_at_top 0)] with n hn cnpos'
      have cnpos : 0 < c n := cnpos'
      calc (c n : ℝ) * l - u (c n) = -(u (c n) / c n - l) * c n := by
          simp' only [← cnpos.ne', ← Ne.def, ← Nat.cast_eq_zero, ← not_false_iff, ← neg_sub] with
            field_simps _ ≤ ε * c n :=
          by
          apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
          simp only [← mul_oneₓ, ← Real.norm_eq_abs, ← abs_one] at hn
          exact le_transₓ (neg_le_abs_self _) hn
    obtain ⟨a, ha⟩ : ∃ a : ℕ, ∀ b : ℕ, a ≤ b → (c (b + 1) : ℝ) ≤ (1 + ε) * c b ∧ (c b : ℝ) * l - u (c b) ≤ ε * c b :=
      eventually_at_top.1 (cgrowth.and L)
    let M :=
      ((Finset.range (a + 1)).Image fun i => c i).max'
        (by
          simp )
    filter_upwards [Ici_mem_at_top M] with n hn
    have exN : ∃ N, n < c N := by
      rcases(tendsto_at_top.1 ctop (n + 1)).exists with ⟨N, hN⟩
      exact
        ⟨N, by
          linarith only [hN]⟩
    let N := Nat.findₓ exN
    have ncN : n < c N := Nat.find_specₓ exN
    have aN : a + 1 ≤ N := by
      by_contra' h
      have cNM : c N ≤ M := by
        apply le_max'
        apply mem_image_of_mem
        exact mem_range.2 h
      exact lt_irreflₓ _ ((cNM.trans hn).trans_lt ncN)
    have Npos : 0 < N := lt_of_lt_of_leₓ Nat.succ_pos' aN
    have aN' : a ≤ N - 1 := by
      linarith only [aN, Npos]
    have cNn : c (N - 1) ≤ n := by
      have : N - 1 < N := Nat.pred_ltₓ Npos.ne'
      simpa only [← not_ltₓ] using Nat.find_minₓ exN this
    calc (n : ℝ) * l - u n ≤ c N * l - u (c (N - 1)) := by
        refine' add_le_add (mul_le_mul_of_nonneg_right (Nat.cast_le.2 ncN.le) lnonneg) _
        exact neg_le_neg (hmono cNn)_ ≤ (1 + ε) * c (N - 1) * l - u (c (N - 1)) := by
        refine' add_le_add (mul_le_mul_of_nonneg_right _ lnonneg) le_rfl
        have B : N - 1 + 1 = N := Nat.succ_pred_eq_of_posₓ Npos
        have := (ha _ aN').1
        rwa [B] at this _ = c (N - 1) * l - u (c (N - 1)) + ε * c (N - 1) * l := by
        ring _ ≤ ε * c (N - 1) + ε * c (N - 1) * l := add_le_add (ha _ aN').2 le_rfl _ = ε * (1 + l) * c (N - 1) := by
        ring _ ≤ ε * (1 + l) * n := by
        refine' mul_le_mul_of_nonneg_left (Nat.cast_le.2 cNn) _
        exact mul_nonneg εpos.le (add_nonneg zero_le_one lnonneg)
  refine' tendsto_order.2 ⟨fun d hd => _, fun d hd => _⟩
  · obtain ⟨ε, hε, εpos⟩ : ∃ ε : ℝ, d + ε * (1 + l) < l ∧ 0 < ε := by
      have L : tendsto (fun ε => d + ε * (1 + l)) (𝓝[>] 0) (𝓝 (d + 0 * (1 + l))) := by
        apply tendsto.mono_left _ nhds_within_le_nhds
        exact tendsto_const_nhds.add (tendsto_id.mul tendsto_const_nhds)
      simp only [← zero_mul, ← add_zeroₓ] at L
      exact (((tendsto_order.1 L).2 l hd).And self_mem_nhds_within).exists
    filter_upwards [B ε εpos, Ioi_mem_at_top 0] with n hn npos
    simp_rw [div_eq_inv_mul]
    calc d < n⁻¹ * n * (l - ε * (1 + l)) := by
        rw [inv_mul_cancel, one_mulₓ]
        · linarith only [hε]
          
        · exact Nat.cast_ne_zero.2 (ne_of_gtₓ npos)
          _ = n⁻¹ * (n * l - ε * (1 + l) * n) :=
        by
        ring _ ≤ n⁻¹ * u n := by
        refine' mul_le_mul_of_nonneg_left _ (inv_nonneg.2 (Nat.cast_nonneg _))
        linarith only [hn]
    
  · obtain ⟨ε, hε, εpos⟩ : ∃ ε : ℝ, l + ε * (1 + ε + l) < d ∧ 0 < ε := by
      have L : tendsto (fun ε => l + ε * (1 + ε + l)) (𝓝[>] 0) (𝓝 (l + 0 * (1 + 0 + l))) := by
        apply tendsto.mono_left _ nhds_within_le_nhds
        exact tendsto_const_nhds.add (tendsto_id.mul ((tendsto_const_nhds.add tendsto_id).add tendsto_const_nhds))
      simp only [← zero_mul, ← add_zeroₓ] at L
      exact (((tendsto_order.1 L).2 d hd).And self_mem_nhds_within).exists
    filter_upwards [A ε εpos, Ioi_mem_at_top 0] with n hn npos
    simp_rw [div_eq_inv_mul]
    calc (n : ℝ)⁻¹ * u n ≤ (n : ℝ)⁻¹ * (n * l + ε * (1 + ε + l) * n) := by
        refine' mul_le_mul_of_nonneg_left _ (inv_nonneg.2 (Nat.cast_nonneg _))
        linarith only [hn]_ = (n : ℝ)⁻¹ * n * (l + ε * (1 + ε + l)) := by
        ring _ < d := by
        rwa [inv_mul_cancel, one_mulₓ]
        exact Nat.cast_ne_zero.2 (ne_of_gtₓ npos)
    

/-- If a monotone sequence `u` is such that `u ⌊c^n⌋₊ / ⌊c^n⌋₊` converges to a limit `l` for all
`c > 1`, then `u n / n` tends to `l`. It is even enough to have the assumption for a sequence of
`c`s converging to `1`. -/
theorem tendsto_div_of_monotone_of_tendsto_div_floor_pow (u : ℕ → ℝ) (l : ℝ) (hmono : Monotone u) (c : ℕ → ℝ)
    (cone : ∀ k, 1 < c k) (clim : Tendsto c atTop (𝓝 1))
    (hc : ∀ k, Tendsto (fun n : ℕ => u ⌊c k ^ n⌋₊ / ⌊c k ^ n⌋₊) atTop (𝓝 l)) : Tendsto (fun n => u n / n) atTop (𝓝 l) :=
  by
  apply tendsto_div_of_monotone_of_exists_subseq_tendsto_div u l hmono
  intro a ha
  obtain ⟨k, hk⟩ : ∃ k, c k < a := ((tendsto_order.1 clim).2 a ha).exists
  refine' ⟨fun n => ⌊c k ^ n⌋₊, _, tendsto_nat_floor_at_top.comp (tendsto_pow_at_top_at_top_of_one_lt (cone k)), hc k⟩
  have H : ∀ n : ℕ, (0 : ℝ) < ⌊c k ^ n⌋₊ := by
    intro n
    refine' zero_lt_one.trans_le _
    simp only [← Nat.one_le_cast, ← Nat.one_le_floor_iff, ← one_le_pow_of_one_le (cone k).le n]
  have A :
    tendsto (fun n : ℕ => (⌊c k ^ (n + 1)⌋₊ : ℝ) / c k ^ (n + 1) * c k / (⌊c k ^ n⌋₊ / c k ^ n)) at_top
      (𝓝 (1 * c k / 1)) :=
    by
    refine' tendsto.div (tendsto.mul _ tendsto_const_nhds) _ one_ne_zero
    · refine' tendsto_nat_floor_div_at_top.comp _
      exact (tendsto_pow_at_top_at_top_of_one_lt (cone k)).comp (tendsto_add_at_top_nat 1)
      
    · refine' tendsto_nat_floor_div_at_top.comp _
      exact tendsto_pow_at_top_at_top_of_one_lt (cone k)
      
  have B : tendsto (fun n : ℕ => (⌊c k ^ (n + 1)⌋₊ : ℝ) / ⌊c k ^ n⌋₊) at_top (𝓝 (c k)) := by
    simp only [← one_mulₓ, ← div_one] at A
    convert A
    ext1 n
    simp'(disch :=
      run_tac
        tactic.field_simp.ne_zero) only [←
      (zero_lt_one.trans (cone k)).ne', ← Ne.def, ← not_false_iff, ← (H n).ne'] with field_simps
    ring_exp
  filter_upwards [(tendsto_order.1 B).2 a hk] with n hn
  exact (div_le_iff (H n)).1 hn.le

/-- The sum of `1/(c^i)^2` above a threshold `j` is comparable to `1/j^2`, up to a multiplicative
constant. -/
theorem sum_div_pow_sq_le_div_sq (N : ℕ) {j : ℝ} (hj : 0 < j) {c : ℝ} (hc : 1 < c) :
    (∑ i in (range N).filter fun i => j < c ^ i, 1 / (c ^ i) ^ 2) ≤ c ^ 3 * (c - 1)⁻¹ / j ^ 2 := by
  have cpos : 0 < c := zero_lt_one.trans hc
  have A : 0 < c⁻¹ ^ 2 := sq_pos_of_pos (inv_pos.2 cpos)
  have B : c ^ 2 * (1 - c⁻¹ ^ 2)⁻¹ ≤ c ^ 3 * (c - 1)⁻¹ := by
    rw [← div_eq_mul_inv, ← div_eq_mul_inv, div_le_div_iff _ (sub_pos.2 hc)]
    swap
    · exact sub_pos.2 (pow_lt_one (inv_nonneg.2 cpos.le) (inv_lt_one hc) two_ne_zero)
      
    have : c ^ 3 = c ^ 2 * c := by
      ring_exp
    simp only [← mul_sub, ← this, ← mul_oneₓ, ← inv_pow, ← sub_le_sub_iff_left]
    rw [mul_assoc, mul_comm c, ← mul_assoc, mul_inv_cancel (sq_pos_of_pos cpos).ne', one_mulₓ]
    simpa using pow_le_pow hc.le one_le_two
  calc
    (∑ i in (range N).filter fun i => j < c ^ i, 1 / (c ^ i) ^ 2) ≤
        ∑ i in Ico ⌊Real.log j / Real.log c⌋₊ N, 1 / (c ^ i) ^ 2 :=
      by
      refine' sum_le_sum_of_subset_of_nonneg _ fun i hi hident => div_nonneg zero_le_one (sq_nonneg _)
      intro i hi
      simp only [← mem_filter, ← mem_range] at hi
      simp only [← hi.1, ← mem_Ico, ← and_trueₓ]
      apply Nat.floor_le_of_le
      apply le_of_ltₓ
      rw [div_lt_iff (Real.log_pos hc), ← Real.log_pow]
      exact Real.log_lt_log hj hi.2_ = ∑ i in Ico ⌊Real.log j / Real.log c⌋₊ N, (c⁻¹ ^ 2) ^ i := by
      congr 1 with i
      simp [pow_mulₓ, ← mul_comm]_ ≤ (c⁻¹ ^ 2) ^ ⌊Real.log j / Real.log c⌋₊ / (1 - c⁻¹ ^ 2) := by
      apply geom_sum_Ico_le_of_lt_one (sq_nonneg _)
      rw [sq_lt_one_iff (inv_nonneg.2 (zero_le_one.trans hc.le))]
      exact inv_lt_one hc _ ≤ (c⁻¹ ^ 2) ^ (Real.log j / Real.log c - 1) / (1 - c⁻¹ ^ 2) := by
      apply div_le_div _ _ _ le_rfl
      · apply Real.rpow_nonneg_of_nonneg (sq_nonneg _)
        
      · rw [← Real.rpow_nat_cast]
        apply Real.rpow_le_rpow_of_exponent_ge A
        · exact pow_le_one _ (inv_nonneg.2 (zero_le_one.trans hc.le)) (inv_le_one hc.le)
          
        · exact (Nat.sub_one_lt_floor _).le
          
        
      · simpa only [← inv_pow, ← sub_pos] using inv_lt_one (one_lt_pow hc two_ne_zero)
        _ = c ^ 2 * (1 - c⁻¹ ^ 2)⁻¹ / j ^ 2 :=
      by
      have I : (c⁻¹ ^ 2) ^ (Real.log j / Real.log c) = 1 / j ^ 2 := by
        apply Real.log_inj_on_pos (Real.rpow_pos_of_pos A _)
        · rw [one_div]
          exact inv_pos.2 (sq_pos_of_pos hj)
          
        rw [Real.log_rpow A]
        simp only [← one_div, ← Real.log_inv, ← Real.log_pow, ← Nat.cast_bit0, ← Nat.cast_oneₓ, ← mul_neg, ← neg_inj]
        field_simp [← (Real.log_pos hc).ne']
        ring
      rw [Real.rpow_sub A, I]
      have : c ^ 2 - 1 ≠ 0 := (sub_pos.2 (one_lt_pow hc two_ne_zero)).ne'
      field_simp [← hj.ne', ← (zero_lt_one.trans hc).ne']
      ring _ ≤ c ^ 3 * (c - 1)⁻¹ / j ^ 2 := by
      apply div_le_div _ B (sq_pos_of_pos hj) le_rfl
      exact mul_nonneg (pow_nonneg cpos.le _) (inv_nonneg.2 (sub_pos.2 hc).le)

theorem mul_pow_le_nat_floor_pow {c : ℝ} (hc : 1 < c) (i : ℕ) : (1 - c⁻¹) * c ^ i ≤ ⌊c ^ i⌋₊ := by
  have cpos : 0 < c := zero_lt_one.trans hc
  rcases Nat.eq_zero_or_posₓ i with (rfl | hi)
  · simp only [← pow_zeroₓ, ← Nat.floor_one, ← Nat.cast_oneₓ, ← mul_oneₓ, ← sub_le_self_iff, ← inv_nonneg, ← cpos.le]
    
  have hident : 1 ≤ i := hi
  calc (1 - c⁻¹) * c ^ i = c ^ i - c ^ i * c⁻¹ := by
      ring _ ≤ c ^ i - 1 := by
      simpa only [div_eq_mul_inv, ← sub_le_sub_iff_left, ← one_le_div cpos, ← pow_oneₓ] using
        pow_le_pow hc.le hident _ ≤ ⌊c ^ i⌋₊ :=
      (Nat.sub_one_lt_floor _).le

/-- The sum of `1/⌊c^i⌋₊^2` above a threshold `j` is comparable to `1/j^2`, up to a multiplicative
constant. -/
theorem sum_div_nat_floor_pow_sq_le_div_sq (N : ℕ) {j : ℝ} (hj : 0 < j) {c : ℝ} (hc : 1 < c) :
    (∑ i in (range N).filter fun i => j < ⌊c ^ i⌋₊, (1 : ℝ) / ⌊c ^ i⌋₊ ^ 2) ≤ c ^ 5 * (c - 1)⁻¹ ^ 3 / j ^ 2 := by
  have cpos : 0 < c := zero_lt_one.trans hc
  have A : 0 < 1 - c⁻¹ := sub_pos.2 (inv_lt_one hc)
  calc
    (∑ i in (range N).filter fun i => j < ⌊c ^ i⌋₊, (1 : ℝ) / ⌊c ^ i⌋₊ ^ 2) ≤
        ∑ i in (range N).filter fun i => j < c ^ i, (1 : ℝ) / ⌊c ^ i⌋₊ ^ 2 :=
      by
      apply sum_le_sum_of_subset_of_nonneg
      · intro i hi
        simp only [← mem_filter, ← mem_range] at hi
        simpa only [← hi.1, ← mem_filter, ← mem_range, ← true_andₓ] using
          hi.2.trans_le (Nat.floor_le (pow_nonneg cpos.le _))
        
      · intro i hi hident
        exact div_nonneg zero_le_one (sq_nonneg _)
        _ ≤ ∑ i in (range N).filter fun i => j < c ^ i, (1 - c⁻¹)⁻¹ ^ 2 * (1 / (c ^ i) ^ 2) :=
      by
      apply sum_le_sum fun i hi => _
      rw [mul_div_assoc', mul_oneₓ, div_le_div_iff]
      rotate_left
      · apply sq_pos_of_pos
        refine' zero_lt_one.trans_le _
        simp only [← Nat.le_floor, ← one_le_pow_of_one_le, ← hc.le, ← Nat.one_le_cast, ← Nat.cast_oneₓ]
        
      · exact sq_pos_of_pos (pow_pos cpos _)
        
      rw [one_mulₓ, ← mul_powₓ]
      apply pow_le_pow_of_le_left (pow_nonneg cpos.le _)
      rw [← div_eq_inv_mul, le_div_iff A, mul_comm]
      exact mul_pow_le_nat_floor_pow hc i _ ≤ (1 - c⁻¹)⁻¹ ^ 2 * (c ^ 3 * (c - 1)⁻¹) / j ^ 2 := by
      rw [← mul_sum, ← mul_div_assoc']
      refine' mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      exact sum_div_pow_sq_le_div_sq N hj hc _ = c ^ 5 * (c - 1)⁻¹ ^ 3 / j ^ 2 := by
      congr 1
      field_simp [← cpos.ne', ← (sub_pos.2 hc).ne']
      ring

