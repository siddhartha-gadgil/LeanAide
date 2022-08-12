/-
Copyright (c) 2018 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis
-/
import Mathbin.Algebra.Order.AbsoluteValue
import Mathbin.Algebra.FieldPower
import Mathbin.RingTheory.Int.Basic
import Mathbin.Tactic.Basic
import Mathbin.Tactic.RingExp
import Mathbin.NumberTheory.Divisors
import Mathbin.Data.Nat.Factorization.Basic

/-!
# p-adic Valuation

This file defines the p-adic valuation on ℕ, ℤ, and ℚ.

The p-adic valuation on ℚ is the difference of the multiplicities of `p` in the numerator and
denominator of `q`. This function obeys the standard properties of a valuation, with the appropriate
assumptions on p. The p-adic valuations on ℕ and ℤ agree with that on ℚ.

The valuation induces a norm on ℚ. This norm is defined in padic_norm.lean.

## Notations

This file uses the local notation `/.` for `rat.mk`.

## Implementation notes

Much, but not all, of this file assumes that `p` is prime. This assumption is inferred automatically
by taking `[fact (prime p)]` as a type class argument.

## References

* [F. Q. Gouvêa, *p-adic numbers*][gouvea1997]
* [R. Y. Lewis, *A formal proof of Hensel's lemma over the p-adic integers*][lewis2019]
* <https://en.wikipedia.org/wiki/P-adic_number>

## Tags

p-adic, p adic, padic, norm, valuation
-/


universe u

open Nat

open Rat

open multiplicity

/-- For `p ≠ 1`, the p-adic valuation of a natural `n ≠ 0` is the largest natural number `k` such that
p^k divides z.
If `n = 0` or `p = 1`, then `padic_val_nat p q` defaults to 0.
-/
def padicValNat (p : ℕ) (n : ℕ) : ℕ :=
  if h : p ≠ 1 ∧ 0 < n then (multiplicity p n).get (multiplicity.finite_nat_iff.2 h) else 0

namespace padicValNat

open multiplicity

variable {p : ℕ}

/-- `padic_val_nat p 0` is 0 for any `p`. -/
@[simp]
protected theorem zero : padicValNat p 0 = 0 := by
  simp [← padicValNat]

/-- `padic_val_nat p 1` is 0 for any `p`. -/
@[simp]
protected theorem one : padicValNat p 1 = 0 := by
  unfold padicValNat <;> split_ifs <;> simp [*]

/-- For `p ≠ 0, p ≠ 1, `padic_val_rat p p` is 1. -/
@[simp]
theorem self (hp : 1 < p) : padicValNat p p = 1 := by
  have neq_one : ¬p = 1 ↔ True := iff_of_true (ne_of_ltₓ hp).symm trivialₓ
  have eq_zero_false : p = 0 ↔ False := iff_false_intro (ne_of_ltₓ (trans zero_lt_one hp)).symm
  simp [← padicValNat, ← neq_one, ← eq_zero_false]

theorem eq_zero_of_not_dvd {n : ℕ} (h : ¬p ∣ n) : padicValNat p n = 0 := by
  rw [padicValNat]
  split_ifs
  · simp [← multiplicity_eq_zero_of_not_dvd h]
    
  rfl

end padicValNat

/-- For `p ≠ 1`, the p-adic valuation of an integer `z ≠ 0` is the largest natural number `k` such that
p^k divides z.
If `x = 0` or `p = 1`, then `padic_val_int p q` defaults to 0.
-/
def padicValInt (p : ℕ) (z : ℤ) : ℕ :=
  padicValNat p z.natAbs

namespace padicValInt

open multiplicity

variable {p : ℕ}

theorem of_ne_one_ne_zero {z : ℤ} (hp : p ≠ 1) (hz : z ≠ 0) :
    padicValInt p z =
      (multiplicity (p : ℤ) z).get
        (by
          apply multiplicity.finite_int_iff.2
          simp [← hp, ← hz]) :=
  by
  rw [padicValInt, padicValNat, dif_pos (And.intro hp (Int.nat_abs_pos_of_ne_zero hz))]
  simp_rw [multiplicity.Int.nat_abs p z]
  rfl

/-- `padic_val_int p 0` is 0 for any `p`. -/
@[simp]
protected theorem zero : padicValInt p 0 = 0 := by
  simp [← padicValInt]

/-- `padic_val_int p 1` is 0 for any `p`. -/
@[simp]
protected theorem one : padicValInt p 1 = 0 := by
  simp [← padicValInt]

/-- The p-adic value of an natural is its p-adic_value as an integer -/
@[simp]
theorem of_nat {n : ℕ} : padicValInt p (n : ℤ) = padicValNat p n := by
  simp [← padicValInt]

/-- For `p ≠ 0, p ≠ 1, `padic_val_int p p` is 1. -/
theorem self (hp : 1 < p) : padicValInt p p = 1 := by
  simp [← padicValNat.self hp]

theorem eq_zero_of_not_dvd {z : ℤ} (h : ¬(p : ℤ) ∣ z) : padicValInt p z = 0 := by
  rw [padicValInt, padicValNat]
  split_ifs
  · simp_rw [multiplicity.Int.nat_abs]
    simp [← multiplicity_eq_zero_of_not_dvd h]
    
  rfl

end padicValInt

/-- `padic_val_rat` defines the valuation of a rational `q` to be the valuation of `q.num` minus the
valuation of `q.denom`.
If `q = 0` or `p = 1`, then `padic_val_rat p q` defaults to 0.
-/
def padicValRat (p : ℕ) (q : ℚ) : ℤ :=
  padicValInt p q.num - padicValNat p q.denom

namespace padicValRat

open multiplicity

variable {p : ℕ}

/-- `padic_val_rat p q` is symmetric in `q`. -/
@[simp]
protected theorem neg (q : ℚ) : padicValRat p (-q) = padicValRat p q := by
  simp [← padicValRat, ← padicValInt]

/-- `padic_val_rat p 0` is 0 for any `p`. -/
@[simp]
protected theorem zero (m : Nat) : padicValRat m 0 = 0 := by
  simp [← padicValRat, ← padicValInt]

/-- `padic_val_rat p 1` is 0 for any `p`. -/
@[simp]
protected theorem one : padicValRat p 1 = 0 := by
  simp [← padicValRat, ← padicValInt]

/-- The p-adic value of an integer `z ≠ 0` is its p-adic_value as a rational -/
@[simp]
theorem of_int {z : ℤ} : padicValRat p (z : ℚ) = padicValInt p z := by
  simp [← padicValRat]

/-- The p-adic value of an integer `z ≠ 0` is the multiplicity of `p` in `z`. -/
theorem of_int_multiplicity (z : ℤ) (hp : p ≠ 1) (hz : z ≠ 0) :
    padicValRat p (z : ℚ) = (multiplicity (p : ℤ) z).get (finite_int_iff.2 ⟨hp, hz⟩) := by
  rw [of_int, padicValInt.of_ne_one_ne_zero hp hz]

theorem multiplicity_sub_multiplicity {q : ℚ} (hp : p ≠ 1) (hq : q ≠ 0) :
    padicValRat p q =
      (multiplicity (p : ℤ) q.num).get (finite_int_iff.2 ⟨hp, Rat.num_ne_zero_of_ne_zero hq⟩) -
        (multiplicity p q.denom).get
          (by
            rw [← finite_iff_dom, finite_nat_iff, and_iff_right hp]
            exact q.pos) :=
  by
  rw [padicValRat, padicValInt.of_ne_one_ne_zero hp, padicValNat, dif_pos]
  · rfl
    
  · exact ⟨hp, q.pos⟩
    
  · exact Rat.num_ne_zero_of_ne_zero hq
    

/-- The p-adic value of an integer `z ≠ 0` is its p-adic_value as a rational -/
@[simp]
theorem of_nat {n : ℕ} : padicValRat p (n : ℚ) = padicValNat p n := by
  simp [← padicValRat, ← padicValInt]

/-- For `p ≠ 0, p ≠ 1, `padic_val_rat p p` is 1. -/
theorem self (hp : 1 < p) : padicValRat p p = 1 := by
  simp [← of_nat, ← hp]

end padicValRat

section padicValNat

theorem zero_le_padic_val_rat_of_nat (p n : ℕ) : 0 ≤ padicValRat p n := by
  simp

-- /-- `padic_val_rat` coincides with `padic_val_nat`. -/
@[norm_cast]
theorem padic_val_rat_of_nat (p n : ℕ) : ↑(padicValNat p n) = padicValRat p n := by
  simp [← padicValRat, ← padicValInt]

/-- A simplification of `padic_val_nat` when one input is prime, by analogy with `padic_val_rat_def`.
-/
theorem padic_val_nat_def {p : ℕ} [hp : Fact p.Prime] {n : ℕ} (hn : 0 < n) :
    padicValNat p n = (multiplicity p n).get (multiplicity.finite_nat_iff.2 ⟨Nat.Prime.ne_one hp.1, hn⟩) := by
  simp [← padicValNat]
  split_ifs
  · rfl
    
  · exfalso
    apply h ⟨hp.out.ne_one, hn⟩
    

theorem padic_val_nat_def' {n p : ℕ} (hp : p ≠ 1) (hn : 0 < n) : ↑(padicValNat p n) = multiplicity p n := by
  simp [← padicValNat, ← hp, ← hn]

@[simp]
theorem padic_val_nat_self (p : ℕ) [Fact p.Prime] : padicValNat p p = 1 := by
  simp [← padic_val_nat_def (Fact.out p.prime).Pos]

theorem one_le_padic_val_nat_of_dvd {n p : Nat} [prime : Fact p.Prime] (n_pos : 0 < n) (div : p ∣ n) :
    1 ≤ padicValNat p n := by
  rw [@padic_val_nat_def _ Prime _ n_pos]
  let one_le_mul : _ ≤ multiplicity p n :=
    @multiplicity.le_multiplicity_of_pow_dvd _ _ _ p n 1
      (by
        norm_num
        exact div)
  simp only [← Nat.cast_oneₓ] at one_le_mul
  rcases one_le_mul with ⟨_, q⟩
  dsimp'  at q
  solve_by_elim

end padicValNat

namespace padicValRat

open multiplicity

variable (p : ℕ) [p_prime : Fact p.Prime]

include p_prime

/-- The multiplicity of `p : ℕ` in `a : ℤ` is finite exactly when `a ≠ 0`. -/
theorem finite_int_prime_iff {p : ℕ} [p_prime : Fact p.Prime] {a : ℤ} : Finite (p : ℤ) a ↔ a ≠ 0 := by
  simp [← finite_int_iff, ← Ne.symm (ne_of_ltₓ p_prime.1.one_lt)]

/-- A rewrite lemma for `padic_val_rat p q` when `q` is expressed in terms of `rat.mk`. -/
protected theorem defn {q : ℚ} {n d : ℤ} (hqz : q ≠ 0) (qdf : q = n /. d) :
    padicValRat p q =
      (multiplicity (p : ℤ) n).get
          (finite_int_iff.2
            ⟨Ne.symm <| ne_of_ltₓ p_prime.1.one_lt, fun hn => by
              simp_all ⟩) -
        (multiplicity (p : ℤ) d).get
          (finite_int_iff.2
            ⟨Ne.symm <| ne_of_ltₓ p_prime.1.one_lt, fun hd => by
              simp_all ⟩) :=
  by
  have hd : d ≠ 0 := Rat.mk_denom_ne_zero_of_ne_zero hqz qdf
  let ⟨c, hc1, hc2⟩ := Rat.num_denom_mk hd qdf
  rw [padicValRat.multiplicity_sub_multiplicity] <;>
    simp [← hc1, ← hc2, ← multiplicity.mul' (Nat.prime_iff_prime_int.1 p_prime.1), ←
      Ne.symm (ne_of_ltₓ p_prime.1.one_lt), ← hqz, ← pos_iff_ne_zero]
  simp_rw [int.coe_nat_multiplicity p q.denom]

/-- A rewrite lemma for `padic_val_rat p (q * r)` with conditions `q ≠ 0`, `r ≠ 0`. -/
protected theorem mul {q r : ℚ} (hq : q ≠ 0) (hr : r ≠ 0) : padicValRat p (q * r) = padicValRat p q + padicValRat p r :=
  by
  have : q * r = q.num * r.num /. (↑q.denom * ↑r.denom) := by
    rw_mod_cast[Rat.mul_num_denom]
  have hq' : q.num /. q.denom ≠ 0 := by
    rw [Rat.num_denom] <;> exact hq
  have hr' : r.num /. r.denom ≠ 0 := by
    rw [Rat.num_denom] <;> exact hr
  have hp' : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 p_prime.1
  rw [padicValRat.defn p (mul_ne_zero hq hr) this]
  conv_rhs => rw [← @Rat.num_denom q, padicValRat.defn p hq', ← @Rat.num_denom r, padicValRat.defn p hr']
  rw [multiplicity.mul' hp', multiplicity.mul' hp'] <;> simp [← add_commₓ, ← add_left_commₓ, ← sub_eq_add_neg]

/-- A rewrite lemma for `padic_val_rat p (q^k)` with condition `q ≠ 0`. -/
protected theorem pow {q : ℚ} (hq : q ≠ 0) {k : ℕ} : padicValRat p (q ^ k) = k * padicValRat p q := by
  induction k <;> simp [*, ← padicValRat.mul _ hq (pow_ne_zero _ hq), ← pow_succₓ, ← add_mulₓ, ← add_commₓ]

/-- A rewrite lemma for `padic_val_rat p (q⁻¹)` with condition `q ≠ 0`.
-/
protected theorem inv (q : ℚ) : padicValRat p q⁻¹ = -padicValRat p q := by
  by_cases' hq : q = 0
  · simp [← hq]
    
  · rw [eq_neg_iff_add_eq_zero, ← padicValRat.mul p (inv_ne_zero hq) hq, inv_mul_cancel hq, padicValRat.one]
    

/-- A rewrite lemma for `padic_val_rat p (q / r)` with conditions `q ≠ 0`, `r ≠ 0`. -/
protected theorem div {q r : ℚ} (hq : q ≠ 0) (hr : r ≠ 0) : padicValRat p (q / r) = padicValRat p q - padicValRat p r :=
  by
  rw [div_eq_mul_inv, padicValRat.mul p hq (inv_ne_zero hr), padicValRat.inv p r, sub_eq_add_neg]

/-- A condition for `padic_val_rat p (n₁ / d₁) ≤ padic_val_rat p (n₂ / d₂),
in terms of divisibility by `p^n`.
-/
theorem padic_val_rat_le_padic_val_rat_iff {n₁ n₂ d₁ d₂ : ℤ} (hn₁ : n₁ ≠ 0) (hn₂ : n₂ ≠ 0) (hd₁ : d₁ ≠ 0)
    (hd₂ : d₂ ≠ 0) :
    padicValRat p (n₁ /. d₁) ≤ padicValRat p (n₂ /. d₂) ↔ ∀ n : ℕ, ↑p ^ n ∣ n₁ * d₂ → ↑p ^ n ∣ n₂ * d₁ := by
  have hf1 : Finite (p : ℤ) (n₁ * d₂) := finite_int_prime_iff.2 (mul_ne_zero hn₁ hd₂)
  have hf2 : Finite (p : ℤ) (n₂ * d₁) := finite_int_prime_iff.2 (mul_ne_zero hn₂ hd₁)
  conv =>
    lhs rw [padicValRat.defn p (Rat.mk_ne_zero_of_ne_zero hn₁ hd₁) rfl,
      padicValRat.defn p (Rat.mk_ne_zero_of_ne_zero hn₂ hd₂) rfl, sub_le_iff_le_add', ← add_sub_assoc,
      le_sub_iff_add_le]norm_cast rw [← multiplicity.mul' (Nat.prime_iff_prime_int.1 p_prime.1) hf1, add_commₓ, ←
      multiplicity.mul' (Nat.prime_iff_prime_int.1 p_prime.1) hf2, PartEnat.get_le_get,
      multiplicity_le_multiplicity_iff]

/-- Sufficient conditions to show that the p-adic valuation of `q` is less than or equal to the
p-adic vlauation of `q + r`.
-/
theorem le_padic_val_rat_add_of_le {q r : ℚ} (hqr : q + r ≠ 0) (h : padicValRat p q ≤ padicValRat p r) :
    padicValRat p q ≤ padicValRat p (q + r) :=
  if hq : q = 0 then by
    simpa [← hq] using h
  else
    if hr : r = 0 then by
      simp [← hr]
    else by
      have hqn : q.num ≠ 0 := Rat.num_ne_zero_of_ne_zero hq
      have hqd : (q.denom : ℤ) ≠ 0 := by
        exact_mod_cast Rat.denom_ne_zero _
      have hrn : r.num ≠ 0 := Rat.num_ne_zero_of_ne_zero hr
      have hrd : (r.denom : ℤ) ≠ 0 := by
        exact_mod_cast Rat.denom_ne_zero _
      have hqreq : q + r = (q.num * r.denom + q.denom * r.num : ℤ) /. (↑q.denom * ↑r.denom : ℤ) := Rat.add_num_denom _ _
      have hqrd : q.num * ↑r.denom + ↑q.denom * r.num ≠ 0 := Rat.mk_num_ne_zero_of_ne_zero hqr hqreq
      conv_lhs => rw [← @Rat.num_denom q]
      rw [hqreq, padic_val_rat_le_padic_val_rat_iff p hqn hqrd hqd (mul_ne_zero hqd hrd), ←
        multiplicity_le_multiplicity_iff, mul_left_commₓ, multiplicity.mul (Nat.prime_iff_prime_int.1 p_prime.1),
        add_mulₓ]
      rw [← @Rat.num_denom q, ← @Rat.num_denom r, padic_val_rat_le_padic_val_rat_iff p hqn hrn hqd hrd, ←
        multiplicity_le_multiplicity_iff] at h
      calc
        _ ≤ min (multiplicity (↑p) (q.num * ↑r.denom * ↑q.denom)) (multiplicity (↑p) (↑q.denom * r.num * ↑q.denom)) :=
          le_minₓ
            (by
              rw [@multiplicity.mul _ _ _ _ (_ * _) _ (Nat.prime_iff_prime_int.1 p_prime.1), add_commₓ])
            (by
              rw [mul_assoc, @multiplicity.mul _ _ _ _ (q.denom : ℤ) (_ * _) (Nat.prime_iff_prime_int.1 p_prime.1)] <;>
                exact add_le_add_left h _)_ ≤ _ :=
          min_le_multiplicity_add

/-- The minimum of the valuations of `q` and `r` is less than or equal to the valuation of `q + r`.
-/
theorem min_le_padic_val_rat_add {q r : ℚ} (hqr : q + r ≠ 0) :
    min (padicValRat p q) (padicValRat p r) ≤ padicValRat p (q + r) :=
  (le_totalₓ (padicValRat p q) (padicValRat p r)).elim
    (fun h => by
      rw [min_eq_leftₓ h] <;> exact le_padic_val_rat_add_of_le _ hqr h)
    fun h => by
    rw [min_eq_rightₓ h, add_commₓ] <;>
      exact
        le_padic_val_rat_add_of_le _
          (by
            rwa [add_commₓ])
          h

open BigOperators

/-- A finite sum of rationals with positive p-adic valuation has positive p-adic valuation
  (if the sum is non-zero). -/
theorem sum_pos_of_pos {n : ℕ} {F : ℕ → ℚ} (hF : ∀ i, i < n → 0 < padicValRat p (F i))
    (hn0 : (∑ i in Finset.range n, F i) ≠ 0) : 0 < padicValRat p (∑ i in Finset.range n, F i) := by
  induction' n with d hd
  · exact False.elim (hn0 rfl)
    
  · rw [Finset.sum_range_succ] at hn0⊢
    by_cases' h : (∑ x : ℕ in Finset.range d, F x) = 0
    · rw [h, zero_addₓ]
      exact hF d (lt_add_one _)
      
    · refine' lt_of_lt_of_leₓ _ (min_le_padic_val_rat_add p hn0)
      · refine' lt_minₓ (hd (fun i hi => _) h) (hF d (lt_add_one _))
        exact hF _ (lt_transₓ hi (lt_add_one _))
        
      
    

end padicValRat

namespace padicValNat

/-- A rewrite lemma for `padic_val_nat p (q * r)` with conditions `q ≠ 0`, `r ≠ 0`. -/
protected theorem mul (p : ℕ) [p_prime : Fact p.Prime] {q r : ℕ} (hq : q ≠ 0) (hr : r ≠ 0) :
    padicValNat p (q * r) = padicValNat p q + padicValNat p r := by
  apply Int.coe_nat_inj
  simp only [← padic_val_rat_of_nat, ← Nat.cast_mulₓ]
  rw [padicValRat.mul]
  norm_cast
  exact cast_ne_zero.mpr hq
  exact cast_ne_zero.mpr hr

protected theorem div_of_dvd (p : ℕ) [hp : Fact p.Prime] {a b : ℕ} (h : b ∣ a) :
    padicValNat p (a / b) = padicValNat p a - padicValNat p b := by
  rcases eq_or_ne a 0 with (rfl | ha)
  · simp
    
  obtain ⟨k, rfl⟩ := h
  obtain ⟨hb, hk⟩ := mul_ne_zero_iff.mp ha
  rw [mul_comm, k.mul_div_cancel hb.bot_lt, padicValNat.mul p hk hb, Nat.add_sub_cancel]

/-- Dividing out by a prime factor reduces the padic_val_nat by 1. -/
protected theorem div {p : ℕ} [p_prime : Fact p.Prime] {b : ℕ} (dvd : p ∣ b) :
    padicValNat p (b / p) = padicValNat p b - 1 := by
  convert padicValNat.div_of_dvd p dvd
  rw [padic_val_nat_self p]

/-- A version of `padic_val_rat.pow` for `padic_val_nat` -/
protected theorem pow (p q n : ℕ) [Fact p.Prime] (hq : q ≠ 0) : padicValNat p (q ^ n) = n * padicValNat p q := by
  apply @Nat.cast_injective ℤ
  push_cast
  exact padicValRat.pow _ (cast_ne_zero.mpr hq)

@[simp]
protected theorem prime_pow (p n : ℕ) [Fact p.Prime] : padicValNat p (p ^ n) = n := by
  rw [padicValNat.pow p _ _ (Fact.out p.prime).ne_zero, padic_val_nat_self p, mul_oneₓ]

protected theorem div_pow {p : ℕ} [p_prime : Fact p.Prime] {b k : ℕ} (dvd : p ^ k ∣ b) :
    padicValNat p (b / p ^ k) = padicValNat p b - k := by
  convert padicValNat.div_of_dvd p dvd
  rw [padicValNat.prime_pow]

end padicValNat

section padicValNat

theorem dvd_of_one_le_padic_val_nat {n p : Nat} (hp : 1 ≤ padicValNat p n) : p ∣ n := by
  by_contra h
  rw [padicValNat.eq_zero_of_not_dvd h] at hp
  exact lt_irreflₓ 0 (lt_of_lt_of_leₓ zero_lt_one hp)

theorem pow_padic_val_nat_dvd {p n : ℕ} : p ^ padicValNat p n ∣ n := by
  rcases n.eq_zero_or_pos with (rfl | hn)
  · simp
    
  rcases eq_or_ne p 1 with (rfl | hp)
  · simp
    
  rw [multiplicity.pow_dvd_iff_le_multiplicity, padic_val_nat_def'] <;> assumption

theorem pow_succ_padic_val_nat_not_dvd {p n : ℕ} [hp : Fact (Nat.Prime p)] (hn : 0 < n) :
    ¬p ^ (padicValNat p n + 1) ∣ n := by
  rw [multiplicity.pow_dvd_iff_le_multiplicity]
  rw [padic_val_nat_def hn]
  · rw [Nat.cast_addₓ, PartEnat.coe_get]
    simp only [← Nat.cast_oneₓ, ← not_leₓ]
    exact PartEnat.lt_add_one (ne_top_iff_finite.mpr (finite_nat_iff.mpr ⟨(Fact.elim hp).ne_one, hn⟩))
    
  · infer_instance
    

theorem padic_val_nat_dvd_iff (p : ℕ) [hp : Fact p.Prime] (n : ℕ) (a : ℕ) : p ^ n ∣ a ↔ a = 0 ∨ n ≤ padicValNat p a :=
  by
  constructor
  · rw [pow_dvd_iff_le_multiplicity, padicValNat]
    split_ifs
    · rw [PartEnat.coe_le_iff]
      exact fun hn => Or.inr (hn _)
      
    · simp only [← true_andₓ, ← not_ltₓ, ← Ne.def, ← not_false_iff, ← Nat.le_zero_iffₓ, ← hp.out.ne_one] at h
      exact fun hn => Or.inl h
      
    
  · rintro (rfl | h)
    · exact dvd_zero (p ^ n)
      
    · exact dvd_trans (pow_dvd_pow p h) pow_padic_val_nat_dvd
      
    

theorem padic_val_nat_primes {p q : ℕ} [p_prime : Fact p.Prime] [q_prime : Fact q.Prime] (neq : p ≠ q) :
    padicValNat p q = 0 :=
  @padicValNat.eq_zero_of_not_dvd p q <| (not_congr (Iff.symm (prime_dvd_prime_iff_eq p_prime.1 q_prime.1))).mp neq

protected theorem padicValNat.div' {p : ℕ} [p_prime : Fact p.Prime] :
    ∀ {m : ℕ} (cpm : Coprime p m) {b : ℕ} (dvd : m ∣ b), padicValNat p (b / m) = padicValNat p b
  | 0 => fun cpm b dvd => by
    rw [zero_dvd_iff] at dvd
    rw [dvd, Nat.zero_divₓ]
  | n + 1 => fun cpm b dvd => by
    rcases dvd with ⟨c, rfl⟩
    rw [mul_div_right c (Nat.succ_posₓ _)]
    by_cases' hc : c = 0
    · rw [hc, mul_zero]
      
    · rw [padicValNat.mul]
      · suffices ¬p ∣ n + 1 by
          rw [padicValNat.eq_zero_of_not_dvd this, zero_addₓ]
        contrapose! cpm
        exact p_prime.1.dvd_iff_not_coprime.mp cpm
        
      · exact Nat.succ_ne_zero _
        
      · exact hc
        
      

theorem padic_val_nat_eq_factorization (p n : ℕ) [hp : Fact p.Prime] : padicValNat p n = n.factorization p := by
  by_cases' hn : n = 0
  · subst hn
    simp
    
  rw [@padic_val_nat_def p _ n (Nat.pos_of_ne_zeroₓ hn)]
  simp [← @multiplicity_eq_factorization n p hp.elim hn]

open BigOperators

theorem prod_pow_prime_padic_val_nat (n : Nat) (hn : n ≠ 0) (m : Nat) (pr : n < m) :
    (∏ p in Finset.filter Nat.Prime (Finset.range m), p ^ padicValNat p n) = n := by
  nth_rw_rhs 0[← factorization_prod_pow_eq_self hn]
  rw [eq_comm]
  apply Finset.prod_subset_one_on_sdiff
  · exact fun p hp =>
      finset.mem_filter.mpr
        ⟨finset.mem_range.mpr (gt_of_gt_of_geₓ pr (le_of_mem_factorization hp)), prime_of_mem_factorization hp⟩
    
  · intro p hp
    cases' finset.mem_sdiff.mp hp with hp1 hp2
    have := fact_iff.mpr (finset.mem_filter.mp hp1).2
    rw [padic_val_nat_eq_factorization p n]
    simp [← finsupp.not_mem_support_iff.mp hp2]
    
  · intro p hp
    have := fact_iff.mpr (prime_of_mem_factorization hp)
    simp [← padic_val_nat_eq_factorization]
    

theorem range_pow_padic_val_nat_subset_divisors {n : ℕ} (p : ℕ) (hn : n ≠ 0) :
    (Finset.range (padicValNat p n + 1)).Image (pow p) ⊆ n.divisors := by
  intro t ht
  simp only [← exists_prop, ← Finset.mem_image, ← Finset.mem_range] at ht
  obtain ⟨k, hk, rfl⟩ := ht
  rw [Nat.mem_divisors]
  exact
    ⟨(pow_dvd_pow p <| by
            linarith).trans
        pow_padic_val_nat_dvd,
      hn⟩

theorem range_pow_padic_val_nat_subset_divisors' {n : ℕ} (p : ℕ) [h : Fact p.Prime] :
    ((Finset.range (padicValNat p n)).Image fun t => p ^ (t + 1)) ⊆ n.divisors \ {1} := by
  rcases eq_or_ne n 0 with (rfl | hn)
  · simp
    
  intro t ht
  simp only [← exists_prop, ← Finset.mem_image, ← Finset.mem_range] at ht
  obtain ⟨k, hk, rfl⟩ := ht
  rw [Finset.mem_sdiff, Nat.mem_divisors]
  refine'
    ⟨⟨(pow_dvd_pow p <| by
              linarith).trans
          pow_padic_val_nat_dvd,
        hn⟩,
      _⟩
  rw [Finset.mem_singleton]
  nth_rw 1[← one_pow (k + 1)]
  exact (Nat.pow_lt_pow_of_lt_left h.1.one_lt <| Nat.succ_posₓ k).ne'

end padicValNat

section padicValInt

variable (p : ℕ) [p_prime : Fact p.Prime]

theorem padic_val_int_dvd_iff (p : ℕ) [Fact p.Prime] (n : ℕ) (a : ℤ) : ↑p ^ n ∣ a ↔ a = 0 ∨ n ≤ padicValInt p a := by
  rw [padicValInt, ← Int.nat_abs_eq_zero, ← padic_val_nat_dvd_iff, ← Int.coe_nat_dvd_left, Int.coe_nat_pow]

theorem padic_val_int_dvd (p : ℕ) [Fact p.Prime] (a : ℤ) : ↑p ^ padicValInt p a ∣ a := by
  rw [padic_val_int_dvd_iff]
  exact Or.inr le_rfl

theorem padic_val_int_self (p : ℕ) [pp : Fact p.Prime] : padicValInt p p = 1 :=
  padicValInt.self pp.out.one_lt

theorem padicValInt.mul (p : ℕ) [Fact p.Prime] {a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) :
    padicValInt p (a * b) = padicValInt p a + padicValInt p b := by
  simp_rw [padicValInt]
  rw [Int.nat_abs_mul, padicValNat.mul] <;> rwa [Int.nat_abs_ne_zero]

theorem padic_val_int_mul_eq_succ (p : ℕ) [pp : Fact p.Prime] (a : ℤ) (ha : a ≠ 0) :
    padicValInt p (a * p) = padicValInt p a + 1 := by
  rw [padicValInt.mul p ha (int.coe_nat_ne_zero.mpr pp.out.ne_zero)]
  simp only [← eq_self_iff_true, ← padicValInt.of_nat, ← padic_val_nat_self]

end padicValInt

