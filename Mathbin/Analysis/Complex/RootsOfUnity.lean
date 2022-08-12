/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathbin.Analysis.SpecialFunctions.Complex.Log
import Mathbin.RingTheory.RootsOfUnity

/-!
# Complex roots of unity

In this file we show that the `n`-th complex roots of unity
are exactly the complex numbers `e ^ (2 * real.pi * complex.I * (i / n))` for `i ∈ finset.range n`.

## Main declarations

* `complex.mem_roots_of_unity`: the complex `n`-th roots of unity are exactly the
  complex numbers of the form `e ^ (2 * real.pi * complex.I * (i / n))` for some `i < n`.
* `complex.card_roots_of_unity`: the number of `n`-th roots of unity is exactly `n`.

-/


namespace Complex

open Polynomial Real

open Nat Real

theorem is_primitive_root_exp_of_coprime (i n : ℕ) (h0 : n ≠ 0) (hi : i.Coprime n) :
    IsPrimitiveRoot (exp (2 * π * I * (i / n))) n := by
  rw [IsPrimitiveRoot.iff_def]
  simp only [exp_nat_mul, ← exp_eq_one_iff]
  have hn0 : (n : ℂ) ≠ 0 := by
    exact_mod_cast h0
  constructor
  · use i
    field_simp [← hn0, ← mul_comm (i : ℂ), ← mul_comm (n : ℂ)]
    
  · simp' only [← hn0, ← mul_right_commₓ _ _ ↑n, ← mul_left_inj' two_pi_I_ne_zero, ← Ne.def, ← not_false_iff, ←
      mul_comm _ (i : ℂ), mul_assoc _ (i : ℂ), ← exists_imp_distrib] with field_simps
    norm_cast
    rintro l k hk
    have : n ∣ i * l := by
      rw [← Int.coe_nat_dvd, hk]
      apply dvd_mul_left
    exact hi.symm.dvd_of_dvd_mul_left this
    

theorem is_primitive_root_exp (n : ℕ) (h0 : n ≠ 0) : IsPrimitiveRoot (exp (2 * π * I / n)) n := by
  simpa only [← Nat.cast_oneₓ, ← one_div] using is_primitive_root_exp_of_coprime 1 n h0 n.coprime_one_left

theorem is_primitive_root_iff (ζ : ℂ) (n : ℕ) (hn : n ≠ 0) :
    IsPrimitiveRoot ζ n ↔ ∃ i < (n : ℕ), ∃ hi : i.Coprime n, exp (2 * π * I * (i / n)) = ζ := by
  have hn0 : (n : ℂ) ≠ 0 := by
    exact_mod_cast hn
  constructor
  swap
  · rintro ⟨i, -, hi, rfl⟩
    exact is_primitive_root_exp_of_coprime i n hn hi
    
  intro h
  obtain ⟨i, hi, rfl⟩ := (is_primitive_root_exp n hn).eq_pow_of_pow_eq_one h.pow_eq_one (Nat.pos_of_ne_zeroₓ hn)
  refine' ⟨i, hi, ((is_primitive_root_exp n hn).pow_iff_coprime (Nat.pos_of_ne_zeroₓ hn) i).mp h, _⟩
  rw [← exp_nat_mul]
  congr 1
  field_simp [← hn0, ← mul_comm (i : ℂ)]

/-- The complex `n`-th roots of unity are exactly the
complex numbers of the form `e ^ (2 * real.pi * complex.I * (i / n))` for some `i < n`. -/
theorem mem_roots_of_unity (n : ℕ+) (x : Units ℂ) :
    x ∈ rootsOfUnity n ℂ ↔ ∃ i < (n : ℕ), exp (2 * π * I * (i / n)) = x := by
  rw [mem_roots_of_unity, Units.ext_iff, Units.coe_pow, Units.coe_one]
  have hn0 : (n : ℂ) ≠ 0 := by
    exact_mod_cast n.ne_zero
  constructor
  · intro h
    obtain ⟨i, hi, H⟩ : ∃ i < (n : ℕ), exp (2 * π * I / n) ^ i = x := by
      simpa only using (is_primitive_root_exp n n.ne_zero).eq_pow_of_pow_eq_one h n.pos
    refine' ⟨i, hi, _⟩
    rw [← H, ← exp_nat_mul]
    congr 1
    field_simp [← hn0, ← mul_comm (i : ℂ)]
    
  · rintro ⟨i, hi, H⟩
    rw [← H, ← exp_nat_mul, exp_eq_one_iff]
    use i
    field_simp [← hn0, ← mul_comm ((n : ℕ) : ℂ), ← mul_comm (i : ℂ)]
    

theorem card_roots_of_unity (n : ℕ+) : Fintype.card (rootsOfUnity n ℂ) = n :=
  (is_primitive_root_exp n n.ne_zero).card_roots_of_unity

theorem card_primitive_roots (k : ℕ) : (primitiveRoots k ℂ).card = φ k := by
  by_cases' h : k = 0
  · simp [← h]
    
  exact (is_primitive_root_exp k h).card_primitive_roots

end Complex

theorem IsPrimitiveRoot.norm'_eq_one {ζ : ℂ} {n : ℕ} (h : IsPrimitiveRoot ζ n) (hn : n ≠ 0) : ∥ζ∥ = 1 :=
  Complex.norm_eq_one_of_pow_eq_one h.pow_eq_one hn

theorem IsPrimitiveRoot.nnnorm_eq_one {ζ : ℂ} {n : ℕ} (h : IsPrimitiveRoot ζ n) (hn : n ≠ 0) : ∥ζ∥₊ = 1 :=
  Subtype.ext <| h.norm'_eq_one hn

theorem IsPrimitiveRoot.arg_ext {n m : ℕ} {ζ μ : ℂ} (hζ : IsPrimitiveRoot ζ n) (hμ : IsPrimitiveRoot μ m) (hn : n ≠ 0)
    (hm : m ≠ 0) (h : ζ.arg = μ.arg) : ζ = μ :=
  Complex.ext_abs_arg ((hζ.norm'_eq_one hn).trans (hμ.norm'_eq_one hm).symm) h

theorem IsPrimitiveRoot.arg_eq_zero_iff {n : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ n) (hn : n ≠ 0) : ζ.arg = 0 ↔ ζ = 1 :=
  ⟨fun h => hζ.arg_ext IsPrimitiveRoot.one hn one_ne_zero (h.trans Complex.arg_one.symm), fun h =>
    h.symm ▸ Complex.arg_one⟩

theorem IsPrimitiveRoot.arg_eq_pi_iff {n : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ n) (hn : n ≠ 0) :
    ζ.arg = Real.pi ↔ ζ = -1 :=
  ⟨fun h => hζ.arg_ext (IsPrimitiveRoot.neg_one 0 two_ne_zero.symm) hn two_ne_zero (h.trans Complex.arg_neg_one.symm),
    fun h => h.symm ▸ Complex.arg_neg_one⟩

theorem IsPrimitiveRoot.arg {n : ℕ} {ζ : ℂ} (h : IsPrimitiveRoot ζ n) (hn : n ≠ 0) :
    ∃ i : ℤ, ζ.arg = i / n * (2 * Real.pi) ∧ IsCoprime i n ∧ i.natAbs < n := by
  rw [Complex.is_primitive_root_iff _ _ hn] at h
  obtain ⟨i, h, hin, rfl⟩ := h
  rw [mul_comm, ← mul_assoc, Complex.exp_mul_I]
  refine' ⟨if i * 2 ≤ n then i else i - n, _, _, _⟩
  on_goal 2 =>
    replace hin := nat.is_coprime_iff_coprime.mpr hin
    split_ifs with _
    · exact hin
      
    · convert hin.add_mul_left_left (-1)
      rw [mul_neg_one, sub_eq_add_neg]
      
  on_goal 2 =>
    split_ifs with h₂
    · exact_mod_cast h
      
    suffices (i - n : ℤ).natAbs = n - i by
      rw [this]
      apply tsub_lt_self hn.bot_lt
      contrapose! h₂
      rw [Nat.eq_zero_of_le_zeroₓ h₂, zero_mul]
      exact zero_le _
    rw [← Int.nat_abs_neg, neg_sub, Int.nat_abs_eq_iff]
    exact Or.inl (Int.coe_nat_subₓ h.le).symm
  split_ifs with h₂
  · convert Complex.arg_cos_add_sin_mul_I _
    · push_cast
      
    · push_cast
      
    field_simp [← hn]
    refine' ⟨(neg_lt_neg Real.pi_pos).trans_le _, _⟩
    · rw [neg_zero]
      exact
        mul_nonneg
          (mul_nonneg i.cast_nonneg <| by
            simp [← real.pi_pos.le])
          (by
            simp )
      
    rw [← mul_rotate', mul_div_assoc]
    rw [← mul_oneₓ n] at h₂
    exact
      mul_le_of_le_one_right real.pi_pos.le
        ((div_le_iff' <| by
              exact_mod_cast pos_of_gt h).mpr <|
          by
          exact_mod_cast h₂)
    
  rw [← Complex.cos_sub_two_pi, ← Complex.sin_sub_two_pi]
  convert Complex.arg_cos_add_sin_mul_I _
  · push_cast
    rw [← sub_one_mul, sub_div, div_self]
    exact_mod_cast hn
    
  · push_cast
    rw [← sub_one_mul, sub_div, div_self]
    exact_mod_cast hn
    
  field_simp [← hn]
  refine' ⟨_, le_transₓ _ real.pi_pos.le⟩
  on_goal 2 =>
    rw [mul_div_assoc]
    exact
      mul_nonpos_of_nonpos_of_nonneg
        (sub_nonpos.mpr <| by
          exact_mod_cast h.le)
        (div_nonneg
            (by
              simp [← real.pi_pos.le]) <|
          by
          simp )
  rw [← mul_rotate', mul_div_assoc, neg_lt, ← mul_neg, mul_lt_iff_lt_one_right Real.pi_pos, ← neg_div, ← neg_mul,
    neg_sub, div_lt_iff, one_mulₓ, sub_mul, sub_lt, ← mul_sub_one]
  norm_num
  exact_mod_cast not_le.mp h₂
  · exact nat.cast_pos.mpr hn.bot_lt
    

