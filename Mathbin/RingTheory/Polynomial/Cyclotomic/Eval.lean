/-
Copyright (c) 2021 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez
-/
import Mathbin.RingTheory.Polynomial.Cyclotomic.Basic
import Mathbin.Tactic.ByContra
import Mathbin.Topology.Algebra.Polynomial
import Mathbin.NumberTheory.Padics.PadicVal
import Mathbin.Analysis.Complex.Arg

/-!
# Evaluating cyclotomic polynomials
This file states some results about evaluating cyclotomic polynomials in various different ways.
## Main definitions
* `polynomial.eval(₂)_one_cyclotomic_prime(_pow)`: `eval 1 (cyclotomic p^k R) = p`.
* `polynomial.eval_one_cyclotomic_not_prime_pow`: Otherwise, `eval 1 (cyclotomic n R) = 1`.
* `polynomial.cyclotomic_pos` : `∀ x, 0 < eval x (cyclotomic n R)` if `2 < n`.
-/


namespace Polynomial

open Finset Nat

open BigOperators

@[simp]
theorem eval_one_cyclotomic_prime {R : Type _} [CommRingₓ R] {p : ℕ} [hn : Fact p.Prime] :
    eval 1 (cyclotomic p R) = p := by
  simp only [← cyclotomic_eq_geom_sum hn.out, ← eval_X, ← one_pow, ← sum_const, ← eval_pow, ← eval_finset_sum, ←
    card_range, ← smul_one_eq_coe]

@[simp]
theorem eval₂_one_cyclotomic_prime {R S : Type _} [CommRingₓ R] [Semiringₓ S] (f : R →+* S) {p : ℕ} [Fact p.Prime] :
    eval₂ f 1 (cyclotomic p R) = p := by
  simp

@[simp]
theorem eval_one_cyclotomic_prime_pow {R : Type _} [CommRingₓ R] {p : ℕ} (k : ℕ) [hn : Fact p.Prime] :
    eval 1 (cyclotomic (p ^ (k + 1)) R) = p := by
  simp only [← cyclotomic_prime_pow_eq_geom_sum hn.out, ← eval_X, ← one_pow, ← sum_const, ← eval_pow, ← eval_finset_sum,
    ← card_range, ← smul_one_eq_coe]

@[simp]
theorem eval₂_one_cyclotomic_prime_pow {R S : Type _} [CommRingₓ R] [Semiringₓ S] (f : R →+* S) {p : ℕ} (k : ℕ)
    [Fact p.Prime] : eval₂ f 1 (cyclotomic (p ^ (k + 1)) R) = p := by
  simp

private theorem cyclotomic_neg_one_pos {n : ℕ} (hn : 2 < n) {R} [LinearOrderedCommRing R] :
    0 < eval (-1 : R) (cyclotomic n R) := by
  have := NeZero.of_gt hn
  rw [← map_cyclotomic_int, ← Int.cast_oneₓ, ← Int.cast_neg, eval_int_cast_map, Int.coe_cast_ring_hom, Int.cast_pos]
  suffices 0 < eval (↑(-1 : ℤ)) (cyclotomic n ℝ) by
    rw [← map_cyclotomic_int n ℝ, eval_int_cast_map, Int.coe_cast_ring_hom] at this
    exact_mod_cast this
  simp only [← Int.cast_oneₓ, ← Int.cast_neg]
  have h0 := cyclotomic_coeff_zero ℝ hn.le
  rw [coeff_zero_eq_eval_zero] at h0
  by_contra' hx
  have := intermediate_value_univ (-1) 0 (cyclotomic n ℝ).Continuous
  obtain ⟨y, hy : is_root _ y⟩ :=
    this
      (show (0 : ℝ) ∈ Set.Icc _ _ by
        simpa [← h0] using hx)
  rw [is_root_cyclotomic_iff] at hy
  rw [hy.eq_order_of] at hn
  exact hn.not_le LinearOrderedRing.order_of_le_two

theorem cyclotomic_pos {n : ℕ} (hn : 2 < n) {R} [LinearOrderedCommRing R] (x : R) : 0 < eval x (cyclotomic n R) := by
  induction' n using Nat.strong_induction_onₓ with n ih
  have hn' : 0 < n := pos_of_gt hn
  have hn'' : 1 < n := one_lt_two.trans hn
  dsimp'  at ih
  have := prod_cyclotomic_eq_geom_sum hn' R
  apply_fun eval x  at this
  rw [divisors_eq_proper_divisors_insert_self_of_pos hn', insert_sdiff_of_not_mem, prod_insert, eval_mul,
    eval_geom_sum] at this
  rotate_left
  · simp only [← lt_self_iff_false, ← mem_sdiff, ← not_false_iff, ← mem_proper_divisors, ← and_falseₓ, ← false_andₓ]
    
  · simpa only [← mem_singleton] using hn''.ne'
    
  rcases lt_trichotomyₓ 0 (∑ i in range n, x ^ i) with (h | h | h)
  · apply pos_of_mul_pos_left
    · rwa [this]
      
    rw [eval_prod]
    refine' prod_nonneg fun i hi => _
    simp only [← mem_sdiff, ← mem_proper_divisors, ← mem_singleton] at hi
    rw [geom_sum_pos_iff hn''] at h
    cases' h with hk hx
    · refine' (ih _ hi.1.2 (Nat.two_lt_of_ne _ hi.2 _)).le <;> rintro rfl
      · exact hn'.ne' (zero_dvd_iff.mp hi.1.1)
        
      · exact even_iff_not_odd.mp (even_iff_two_dvd.mpr hi.1.1) hk
        
      
    · rcases eq_or_ne i 2 with (rfl | hk)
      · simpa only [← eval_X, ← eval_one, ← cyclotomic_two, ← eval_add] using hx.le
        
      refine' (ih _ hi.1.2 (Nat.two_lt_of_ne _ hi.2 hk)).le
      rintro rfl
      exact hn'.ne' <| zero_dvd_iff.mp hi.1.1
      
    
  · rw [eq_comm, geom_sum_eq_zero_iff_neg_one hn''] at h
    exact h.1.symm ▸ cyclotomic_neg_one_pos hn
    
  · apply pos_of_mul_neg_left
    · rwa [this]
      
    rw [geom_sum_neg_iff hn''] at h
    have h2 : {2} ⊆ n.proper_divisors \ {1} := by
      rw [singleton_subset_iff, mem_sdiff, mem_proper_divisors, not_mem_singleton]
      exact ⟨⟨even_iff_two_dvd.mp h.1, hn⟩, (Nat.one_lt_bit0 one_ne_zero).ne'⟩
    rw [eval_prod, ← prod_sdiff h2, prod_singleton] <;>
      try
        infer_instance
    apply mul_nonpos_of_nonneg_of_nonpos
    · refine' prod_nonneg fun i hi => le_of_ltₓ _
      simp only [← mem_sdiff, ← mem_proper_divisors, ← mem_singleton] at hi
      refine' ih _ hi.1.1.2 (Nat.two_lt_of_ne _ hi.1.2 hi.2)
      rintro rfl
      rw [zero_dvd_iff] at hi
      exact hn'.ne' hi.1.1.1
      
    · simpa only [← eval_X, ← eval_one, ← cyclotomic_two, ← eval_add] using h.right.le
      
    

theorem cyclotomic_pos_and_nonneg (n : ℕ) {R} [LinearOrderedCommRing R] (x : R) :
    (1 < x → 0 < eval x (cyclotomic n R)) ∧ (1 ≤ x → 0 ≤ eval x (cyclotomic n R)) := by
  rcases n with (_ | _ | _ | n) <;>
    simp only [← cyclotomic_zero, ← cyclotomic_one, ← cyclotomic_two, ← succ_eq_add_one, ← eval_X, ← eval_one, ←
      eval_add, ← eval_sub, ← sub_nonneg, ← sub_pos, ← zero_lt_one, ← zero_le_one, ← implies_true_iff, ← imp_self, ←
      and_selfₓ]
  · constructor <;> intro <;> linarith
    
  · have : 2 < n + 3 := by
      decide
    constructor <;> intro <;> [skip, apply le_of_ltₓ] <;> apply cyclotomic_pos this
    

/-- Cyclotomic polynomials are always positive on inputs larger than one.
Similar to `cyclotomic_pos` but with the condition on the input rather than index of the
cyclotomic polynomial. -/
theorem cyclotomic_pos' (n : ℕ) {R} [LinearOrderedCommRing R] {x : R} (hx : 1 < x) : 0 < eval x (cyclotomic n R) :=
  (cyclotomic_pos_and_nonneg n x).1 hx

/-- Cyclotomic polynomials are always nonnegative on inputs one or more. -/
theorem cyclotomic_nonneg (n : ℕ) {R} [LinearOrderedCommRing R] {x : R} (hx : 1 ≤ x) : 0 ≤ eval x (cyclotomic n R) :=
  (cyclotomic_pos_and_nonneg n x).2 hx

-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:51:50: missing argument
theorem eval_one_cyclotomic_not_prime_pow {R : Type _} [Ringₓ R] {n : ℕ} (h : ∀ {p : ℕ}, p.Prime → ∀ k : ℕ, p ^ k ≠ n) :
    eval 1 (cyclotomic n R) = 1 := by
  rcases n.eq_zero_or_pos with (rfl | hn')
  · simp
    
  have hn : 1 < n := one_lt_iff_ne_zero_and_ne_one.mpr ⟨hn'.ne', (h Nat.prime_two 0).symm⟩
  suffices eval 1 (cyclotomic n ℤ) = 1 ∨ eval 1 (cyclotomic n ℤ) = -1 by
    cases' this with h h
    · have := eval_int_cast_map (Int.castRingHom R) (cyclotomic n ℤ) 1
      simpa only [← map_cyclotomic, ← Int.cast_oneₓ, ← h, ← RingHom.eq_int_cast] using this
      
    · exfalso
      linarith [cyclotomic_nonneg n (le_reflₓ (1 : ℤ))]
      
  rw [← Int.nat_abs_eq_nat_abs_iff, Int.nat_abs_one, Nat.eq_one_iff_not_exists_prime_dvd]
  intro p hp hpe
  have := Fact.mk hp
  have hpn : p ∣ n := by
    apply hpe.trans
    nth_rw 1[← Int.nat_abs_of_nat n]
    rw [Int.nat_abs_dvd_iff_dvd, ← one_geom_sum, ← eval_geom_sum, ← prod_cyclotomic_eq_geom_sum hn']
    apply eval_dvd
    apply Finset.dvd_prod_of_mem
    simpa using And.intro hn'.ne' hn.ne'
  have := prod_cyclotomic_eq_geom_sum hn' ℤ
  apply_fun eval 1  at this
  rw [eval_geom_sum, one_geom_sum, eval_prod, eq_comm, ←
    Finset.prod_sdiff <| range_pow_padic_val_nat_subset_divisors' p, Finset.prod_image] at this
  simp_rw [eval_one_cyclotomic_prime_pow, Finset.prod_const, Finset.card_range, mul_comm] at this
  rw [← Finset.prod_sdiff <| show {n} ⊆ _ from _] at this
  any_goals {
  }
  swap
  · simp only [← not_exists, ← true_andₓ, ← exists_prop, ← dvd_rfl, ← Finset.mem_image, ← Finset.mem_range, ←
      Finset.mem_singleton, ← Finset.singleton_subset_iff, ← Finset.mem_sdiff, ← Nat.mem_divisors, ← not_and]
    exact ⟨⟨hn'.ne', hn.ne'⟩, fun t _ => h hp _⟩
    
  rw [← Int.nat_abs_of_nat p, Int.nat_abs_dvd_iff_dvd] at hpe
  obtain ⟨t, ht⟩ := hpe
  rw [Finset.prod_singleton, ht, mul_left_commₓ, mul_comm, ← mul_assoc, mul_assoc] at this
  have : (p ^ padicValNat p n * p : ℤ) ∣ n := ⟨_, this⟩
  simp only [pow_succ'ₓ, Int.nat_abs_dvd_iff_dvd, ← Int.nat_abs_of_nat, ← Int.nat_abs_pow] at this
  exact pow_succ_padic_val_nat_not_dvd hn' this
  · rintro x - y - hxy
    apply Nat.succ_injective
    exact Nat.pow_right_injective hp.two_le hxy
    

theorem sub_one_pow_totient_lt_cyclotomic_eval {n : ℕ} {q : ℝ} (hn' : 2 ≤ n) (hq' : 1 < q) :
    (q - 1) ^ totient n < (cyclotomic n ℝ).eval q := by
  have hn : 0 < n := pos_of_gt hn'
  have hq := zero_lt_one.trans hq'
  have hfor : ∀, ∀ ζ' ∈ primitiveRoots n ℂ, ∀, q - 1 ≤ ∥↑q - ζ'∥ := by
    intro ζ' hζ'
    rw [mem_primitive_roots hn] at hζ'
    convert norm_sub_norm_le (↑q) ζ'
    · rw [Complex.norm_real, Real.norm_of_nonneg hq.le]
      
    · rw [hζ'.norm'_eq_one hn.ne']
      
  let ζ := Complex.exp (2 * ↑Real.pi * Complex.i / ↑n)
  have hζ : IsPrimitiveRoot ζ n := Complex.is_primitive_root_exp n hn.ne'
  have hex : ∃ ζ' ∈ primitiveRoots n ℂ, q - 1 < ∥↑q - ζ'∥ := by
    refine' ⟨ζ, (mem_primitive_roots hn).mpr hζ, _⟩
    suffices ¬SameRay ℝ (q : ℂ) ζ by
      convert lt_norm_sub_of_not_same_ray this <;> simp [← Real.norm_of_nonneg hq.le, ← hζ.norm'_eq_one hn.ne']
    rw [Complex.same_ray_iff]
    push_neg
    refine'
      ⟨by
        exact_mod_cast hq.ne', hζ.ne_zero hn.ne', _⟩
    rw [Complex.arg_of_real_of_nonneg hq.le, Ne.def, eq_comm, hζ.arg_eq_zero_iff hn.ne']
    clear_value ζ
    rintro rfl
    linarith [hζ.unique IsPrimitiveRoot.one]
  have : ¬eval (↑q) (cyclotomic n ℂ) = 0 := by
    erw [cyclotomic.eval_apply q n (algebraMap ℝ ℂ)]
    simpa using (cyclotomic_pos' n hq').ne'
  suffices
    Units.mk0 (Real.toNnreal (q - 1))
          (by
            simp [← hq']) ^
        totient n <
      Units.mk0 ∥(cyclotomic n ℂ).eval q∥₊
        (by
          simp [← this])
    by
    simp only [Units.coe_lt_coe, ← Units.coe_pow, ← Units.coe_mk0, Nnreal.coe_lt_coe, ← hq'.le, ←
      Real.to_nnreal_lt_to_nnreal_iff_of_nonneg, ← coe_nnnorm, ← Complex.norm_eq_abs, ← Nnreal.coe_pow, ←
      Real.coe_to_nnreal', ← max_eq_leftₓ, ← sub_nonneg] at this
    convert this
    erw [cyclotomic.eval_apply q n (algebraMap ℝ ℂ), eq_comm]
    simp [← cyclotomic_nonneg n hq'.le]
  simp only [← cyclotomic_eq_prod_X_sub_primitive_roots hζ, ← eval_prod, ← eval_C, ← eval_X, ← eval_sub, ← nnnorm_prod,
    ← Units.mk0_prod]
  convert prod_lt_prod' _ _
  swap
  · exact fun _ =>
      Units.mk0 (Real.toNnreal (q - 1))
        (by
          simp [← hq'])
    
  · simp [← Complex.card_primitive_roots]
    
  · simp only [← Subtype.coe_mk, ← mem_attach, ← forall_true_left, ← Subtype.forall, Units.coe_le_coe,
      Nnreal.coe_le_coe, ← Complex.abs_nonneg, ← hq'.le, ← Units.coe_mk0, ← Real.coe_to_nnreal', ← coe_nnnorm, ←
      Complex.norm_eq_abs, ← max_le_iff, ← tsub_le_iff_right]
    intro x hx
    simpa using hfor x hx
    
  · simp only [← Subtype.coe_mk, ← mem_attach, ← exists_true_left, ← Subtype.exists, Nnreal.coe_lt_coe,
      Units.coe_lt_coe, ← Units.coe_mk0 _, ← coe_nnnorm]
    simpa [← hq'.le] using hex
    

theorem cyclotomic_eval_lt_sub_one_pow_totient {n : ℕ} {q : ℝ} (hn' : 3 ≤ n) (hq' : 1 < q) :
    (cyclotomic n ℝ).eval q < (q + 1) ^ totient n := by
  have hn : 0 < n := pos_of_gt hn'
  have hq := zero_lt_one.trans hq'
  have hfor : ∀, ∀ ζ' ∈ primitiveRoots n ℂ, ∀, ∥↑q - ζ'∥ ≤ q + 1 := by
    intro ζ' hζ'
    rw [mem_primitive_roots hn] at hζ'
    convert norm_sub_le (↑q) ζ'
    · rw [Complex.norm_real, Real.norm_of_nonneg (zero_le_one.trans_lt hq').le]
      
    · rw [hζ'.norm'_eq_one hn.ne']
      
  let ζ := Complex.exp (2 * ↑Real.pi * Complex.i / ↑n)
  have hζ : IsPrimitiveRoot ζ n := Complex.is_primitive_root_exp n hn.ne'
  have hex : ∃ ζ' ∈ primitiveRoots n ℂ, ∥↑q - ζ'∥ < q + 1 := by
    refine' ⟨ζ, (mem_primitive_roots hn).mpr hζ, _⟩
    suffices ¬SameRay ℝ (q : ℂ) (-ζ) by
      convert norm_add_lt_of_not_same_ray this <;>
        simp [← Real.norm_of_nonneg hq.le, ← hζ.norm'_eq_one hn.ne', -Complex.norm_eq_abs]
    rw [Complex.same_ray_iff]
    push_neg
    refine'
      ⟨by
        exact_mod_cast hq.ne', neg_ne_zero.mpr <| hζ.ne_zero hn.ne', _⟩
    rw [Complex.arg_of_real_of_nonneg hq.le, Ne.def, eq_comm]
    intro h
    rw [Complex.arg_eq_zero_iff, Complex.neg_re, neg_nonneg, Complex.neg_im, neg_eq_zero] at h
    have hζ₀ : ζ ≠ 0 := by
      clear_value ζ
      rintro rfl
      exact hn.ne' (hζ.unique IsPrimitiveRoot.zero)
    have : ζ.re < 0 ∧ ζ.im = 0 := ⟨h.1.lt_of_ne _, h.2⟩
    rw [← Complex.arg_eq_pi_iff, hζ.arg_eq_pi_iff hn.ne'] at this
    rw [this] at hζ
    linarith [hζ.unique <| IsPrimitiveRoot.neg_one 0 two_ne_zero.symm]
    · contrapose! hζ₀
      ext <;> simp [← hζ₀, ← h.2]
      
  have : ¬eval (↑q) (cyclotomic n ℂ) = 0 := by
    erw [cyclotomic.eval_apply q n (algebraMap ℝ ℂ)]
    simp only [← Complex.coe_algebra_map, ← Complex.of_real_eq_zero]
    exact (cyclotomic_pos' n hq').Ne.symm
  suffices
    Units.mk0 ∥(cyclotomic n ℂ).eval q∥₊
        (by
          simp [← this]) <
      Units.mk0 (Real.toNnreal (q + 1))
          (by
            simp <;> linarith) ^
        totient n
    by
    simp only [Units.coe_lt_coe, ← Units.coe_pow, ← Units.coe_mk0, Nnreal.coe_lt_coe, ← hq'.le, ←
      Real.to_nnreal_lt_to_nnreal_iff_of_nonneg, ← coe_nnnorm, ← Complex.norm_eq_abs, ← Nnreal.coe_pow, ←
      Real.coe_to_nnreal', ← max_eq_leftₓ, ← sub_nonneg] at this
    convert this
    · erw [cyclotomic.eval_apply q n (algebraMap ℝ ℂ), eq_comm]
      simp [← cyclotomic_nonneg n hq'.le]
      
    rw [eq_comm, max_eq_left_iff]
    linarith
  simp only [← cyclotomic_eq_prod_X_sub_primitive_roots hζ, ← eval_prod, ← eval_C, ← eval_X, ← eval_sub, ← nnnorm_prod,
    ← Units.mk0_prod]
  convert prod_lt_prod' _ _
  swap
  · exact fun _ =>
      Units.mk0 (Real.toNnreal (q + 1))
        (by
          simp <;> linarith only [hq'])
    
  · simp [← Complex.card_primitive_roots]
    
  · simp only [← Subtype.coe_mk, ← mem_attach, ← forall_true_left, ← Subtype.forall, Units.coe_le_coe,
      Nnreal.coe_le_coe, ← Complex.abs_nonneg, ← hq'.le, ← Units.coe_mk0, ← Real.coe_to_nnreal, ← coe_nnnorm, ←
      Complex.norm_eq_abs, ← max_le_iff]
    intro x hx
    have : Complex.abs _ ≤ _ := hfor x hx
    simp [← this]
    
  · simp only [← Subtype.coe_mk, ← mem_attach, ← exists_true_left, ← Subtype.exists, Nnreal.coe_lt_coe,
      Units.coe_lt_coe, ← Units.coe_mk0 _, ← coe_nnnorm]
    obtain ⟨ζ, hζ, hhζ : Complex.abs _ < _⟩ := hex
    exact
      ⟨ζ, hζ, by
        simp [← hhζ]⟩
    

theorem sub_one_lt_nat_abs_cyclotomic_eval {n : ℕ} {q : ℕ} (hn' : 1 < n) (hq' : q ≠ 1) :
    q - 1 < ((cyclotomic n ℤ).eval ↑q).natAbs := by
  rcases q with (_ | _ | q)
  iterate 2 
    rw [pos_iff_ne_zero, Ne.def, Int.nat_abs_eq_zero]
    intro h
    have := degree_eq_one_of_irreducible_of_root (cyclotomic.irreducible (pos_of_gt hn')) h
    rw [degree_cyclotomic, WithTop.coe_eq_one, totient_eq_one_iff] at this
    rcases this with (rfl | rfl) <;> simpa using h
  suffices (q.succ : ℝ) < (eval (↑q + 1 + 1) (cyclotomic n ℤ)).natAbs by
    exact_mod_cast this
  calc _ ≤ ((q + 2 - 1) ^ n.totient : ℝ) := _ _ < _ := _
  · norm_num
    convert
      pow_mono
        (by
          simp : 1 ≤ (q : ℝ) + 1)
        (totient_pos (pos_of_gt hn') : 1 ≤ n.totient)
    · simp
      
    · ring
      
    
  convert
    sub_one_pow_totient_lt_cyclotomic_eval
      (show 2 ≤ n by
        linarith)
      (show (1 : ℝ) < q + 2 by
        norm_cast
        linarith)
  norm_cast
  erw [cyclotomic.eval_apply (q + 2 : ℤ) n (algebraMap ℤ ℝ)]
  simp only [← Int.coe_nat_succ, ← RingHom.eq_int_cast]
  norm_cast
  rw [Int.coe_nat_abs_eq_normalize, Int.normalize_of_nonneg]
  simp only [← Int.coe_nat_succ]
  exact
    cyclotomic_nonneg n
      (by
        linarith)

end Polynomial

