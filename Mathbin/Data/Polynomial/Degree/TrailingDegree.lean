/-
Copyright (c) 2020 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Mathbin.Data.Polynomial.Degree.Definitions

/-!
# Trailing degree of univariate polynomials

## Main definitions

* `trailing_degree p`: the multiplicity of `X` in the polynomial `p`
* `nat_trailing_degree`: a variant of `trailing_degree` that takes values in the natural numbers
* `trailing_coeff`: the coefficient at index `nat_trailing_degree p`

Converts most results about `degree`, `nat_degree` and `leading_coeff` to results about the bottom
end of a polynomial
-/


noncomputable section

open Function Polynomial Finsupp Finset

open BigOperators Classical Polynomial

namespace Polynomial

universe u v

variable {R : Type u} {S : Type v} {a b : R} {n m : ℕ}

section Semiringₓ

variable [Semiringₓ R] {p q r : R[X]}

/-- `trailing_degree p` is the multiplicity of `x` in the polynomial `p`, i.e. the smallest
`X`-exponent in `p`.
`trailing_degree p = some n` when `p ≠ 0` and `n` is the smallest power of `X` that appears
in `p`, otherwise
`trailing_degree 0 = ⊤`. -/
def trailingDegree (p : R[X]) : WithTop ℕ :=
  p.Support.inf some

theorem trailing_degree_lt_wf : WellFounded fun p q : R[X] => trailingDegree p < trailingDegree q :=
  InvImage.wfₓ trailingDegree (WithTop.well_founded_lt Nat.lt_wf)

/-- `nat_trailing_degree p` forces `trailing_degree p` to `ℕ`, by defining
`nat_trailing_degree ⊤ = 0`. -/
def natTrailingDegree (p : R[X]) : ℕ :=
  (trailingDegree p).getOrElse 0

/-- `trailing_coeff p` gives the coefficient of the smallest power of `X` in `p`-/
def trailingCoeff (p : R[X]) : R :=
  coeff p (natTrailingDegree p)

/-- a polynomial is `monic_at` if its trailing coefficient is 1 -/
def TrailingMonic (p : R[X]) :=
  trailingCoeff p = (1 : R)

theorem TrailingMonic.def : TrailingMonic p ↔ trailingCoeff p = 1 :=
  Iff.rfl

instance TrailingMonic.decidable [DecidableEq R] : Decidable (TrailingMonic p) := by
  unfold trailing_monic <;> infer_instance

@[simp]
theorem TrailingMonic.trailing_coeff {p : R[X]} (hp : p.TrailingMonic) : trailingCoeff p = 1 :=
  hp

@[simp]
theorem trailing_degree_zero : trailingDegree (0 : R[X]) = ⊤ :=
  rfl

@[simp]
theorem trailing_coeff_zero : trailingCoeff (0 : R[X]) = 0 :=
  rfl

@[simp]
theorem nat_trailing_degree_zero : natTrailingDegree (0 : R[X]) = 0 :=
  rfl

theorem trailing_degree_eq_top : trailingDegree p = ⊤ ↔ p = 0 :=
  ⟨fun h => support_eq_empty.1 (Finset.min_eq_top.1 h), fun h => by
    simp [← h]⟩

theorem trailing_degree_eq_nat_trailing_degree (hp : p ≠ 0) : trailingDegree p = (natTrailingDegree p : WithTop ℕ) := by
  let ⟨n, hn⟩ := not_forall.1 (mt Option.eq_none_iff_forall_not_mem.2 (mt trailing_degree_eq_top.1 hp))
  have hn : trailingDegree p = some n := not_not.1 hn
  rw [nat_trailing_degree, hn] <;> rfl

theorem trailing_degree_eq_iff_nat_trailing_degree_eq {p : R[X]} {n : ℕ} (hp : p ≠ 0) :
    p.trailingDegree = n ↔ p.natTrailingDegree = n := by
  rw [trailing_degree_eq_nat_trailing_degree hp, WithTop.coe_eq_coe]

theorem trailing_degree_eq_iff_nat_trailing_degree_eq_of_pos {p : R[X]} {n : ℕ} (hn : 0 < n) :
    p.trailingDegree = n ↔ p.natTrailingDegree = n := by
  constructor
  · intro H
    rwa [← trailing_degree_eq_iff_nat_trailing_degree_eq]
    rintro rfl
    rw [trailing_degree_zero] at H
    exact Option.noConfusion H
    
  · intro H
    rwa [trailing_degree_eq_iff_nat_trailing_degree_eq]
    rintro rfl
    rw [nat_trailing_degree_zero] at H
    rw [H] at hn
    exact lt_irreflₓ _ hn
    

theorem nat_trailing_degree_eq_of_trailing_degree_eq_some {p : R[X]} {n : ℕ} (h : trailingDegree p = n) :
    natTrailingDegree p = n :=
  have hp0 : p ≠ 0 := fun hp0 => by
    rw [hp0] at h <;> exact Option.noConfusion h
  Option.some_inj.1 <|
    show (natTrailingDegree p : WithTop ℕ) = n by
      rwa [← trailing_degree_eq_nat_trailing_degree hp0]

@[simp]
theorem nat_trailing_degree_le_trailing_degree : ↑(natTrailingDegree p) ≤ trailingDegree p := by
  by_cases' hp : p = 0
  · rw [hp, trailing_degree_zero]
    exact le_top
    
  rw [trailing_degree_eq_nat_trailing_degree hp]
  exact le_rfl

theorem nat_trailing_degree_eq_of_trailing_degree_eq [Semiringₓ S] {q : S[X]}
    (h : trailingDegree p = trailingDegree q) : natTrailingDegree p = natTrailingDegree q := by
  unfold nat_trailing_degree <;> rw [h]

theorem le_trailing_degree_of_ne_zero (h : coeff p n ≠ 0) : trailingDegree p ≤ n :=
  show @LE.le (WithTop ℕ) _ (p.Support.inf some : WithTop ℕ) (some n : WithTop ℕ) from
    Finset.inf_le (mem_support_iff.2 h)

theorem nat_trailing_degree_le_of_ne_zero (h : coeff p n ≠ 0) : natTrailingDegree p ≤ n := by
  rw [← WithTop.coe_le_coe, ← trailing_degree_eq_nat_trailing_degree]
  · exact le_trailing_degree_of_ne_zero h
    
  · intro h
    subst h
    exact h rfl
    

theorem trailing_degree_le_trailing_degree (h : coeff q (natTrailingDegree p) ≠ 0) :
    trailingDegree q ≤ trailingDegree p := by
  by_cases' hp : p = 0
  · rw [hp]
    exact le_top
    
  · rw [trailing_degree_eq_nat_trailing_degree hp]
    exact le_trailing_degree_of_ne_zero h
    

theorem trailing_degree_ne_of_nat_trailing_degree_ne {n : ℕ} : p.natTrailingDegree ≠ n → trailingDegree p ≠ n :=
  mt fun h => by
    rw [nat_trailing_degree, h, Option.get_or_else_coe]

theorem nat_trailing_degree_le_of_trailing_degree_le {n : ℕ} {hp : p ≠ 0} (H : (n : WithTop ℕ) ≤ trailingDegree p) :
    n ≤ natTrailingDegree p := by
  rw [trailing_degree_eq_nat_trailing_degree hp] at H
  exact with_top.coe_le_coe.mp H

theorem nat_trailing_degree_le_nat_trailing_degree {hq : q ≠ 0} (hpq : p.trailingDegree ≤ q.trailingDegree) :
    p.natTrailingDegree ≤ q.natTrailingDegree := by
  by_cases' hp : p = 0
  · rw [hp, nat_trailing_degree_zero]
    exact zero_le _
    
  rwa [trailing_degree_eq_nat_trailing_degree hp, trailing_degree_eq_nat_trailing_degree hq, WithTop.coe_le_coe] at hpq

@[simp]
theorem trailing_degree_monomial (ha : a ≠ 0) : trailingDegree (monomial n a) = n := by
  rw [trailing_degree, support_monomial n ha, inf_singleton, WithTop.some_eq_coe]

theorem nat_trailing_degree_monomial (ha : a ≠ 0) : natTrailingDegree (monomial n a) = n := by
  rw [nat_trailing_degree, trailing_degree_monomial ha] <;> rfl

theorem nat_trailing_degree_monomial_le : natTrailingDegree (monomial n a) ≤ n :=
  if ha : a = 0 then by
    simp [← ha]
  else (nat_trailing_degree_monomial ha).le

theorem le_trailing_degree_monomial : ↑n ≤ trailingDegree (monomial n a) :=
  if ha : a = 0 then by
    simp [← ha]
  else (trailing_degree_monomial ha).Ge

@[simp]
theorem trailing_degree_C (ha : a ≠ 0) : trailingDegree (c a) = (0 : WithTop ℕ) :=
  trailing_degree_monomial ha

theorem le_trailing_degree_C : (0 : WithTop ℕ) ≤ trailingDegree (c a) :=
  le_trailing_degree_monomial

theorem trailing_degree_one_le : (0 : WithTop ℕ) ≤ trailingDegree (1 : R[X]) := by
  rw [← C_1] <;> exact le_trailing_degree_C

@[simp]
theorem nat_trailing_degree_C (a : R) : natTrailingDegree (c a) = 0 :=
  nonpos_iff_eq_zero.1 nat_trailing_degree_monomial_le

@[simp]
theorem nat_trailing_degree_one : natTrailingDegree (1 : R[X]) = 0 :=
  nat_trailing_degree_C 1

@[simp]
theorem nat_trailing_degree_nat_cast (n : ℕ) : natTrailingDegree (n : R[X]) = 0 := by
  simp only [C_eq_nat_cast, ← nat_trailing_degree_C]

@[simp]
theorem trailing_degree_C_mul_X_pow (n : ℕ) (ha : a ≠ 0) : trailingDegree (c a * X ^ n) = n := by
  rw [C_mul_X_pow_eq_monomial, trailing_degree_monomial ha]

theorem le_trailing_degree_C_mul_X_pow (n : ℕ) (a : R) : (n : WithTop ℕ) ≤ trailingDegree (c a * X ^ n) := by
  rw [C_mul_X_pow_eq_monomial]
  exact le_trailing_degree_monomial

theorem coeff_eq_zero_of_trailing_degree_lt (h : (n : WithTop ℕ) < trailingDegree p) : coeff p n = 0 :=
  not_not.1 (mt le_trailing_degree_of_ne_zero (not_le_of_gtₓ h))

theorem coeff_eq_zero_of_lt_nat_trailing_degree {p : R[X]} {n : ℕ} (h : n < p.natTrailingDegree) : p.coeff n = 0 := by
  apply coeff_eq_zero_of_trailing_degree_lt
  by_cases' hp : p = 0
  · rw [hp, trailing_degree_zero]
    exact WithTop.coe_lt_top n
    
  · rwa [trailing_degree_eq_nat_trailing_degree hp, WithTop.coe_lt_coe]
    

@[simp]
theorem coeff_nat_trailing_degree_pred_eq_zero {p : R[X]} {hp : (0 : WithTop ℕ) < natTrailingDegree p} :
    p.coeff (p.natTrailingDegree - 1) = 0 :=
  coeff_eq_zero_of_lt_nat_trailing_degree <|
    Nat.sub_ltₓ ((WithTop.zero_lt_coe (natTrailingDegree p)).mp hp) Nat.one_posₓ

theorem le_trailing_degree_X_pow (n : ℕ) : (n : WithTop ℕ) ≤ trailingDegree (X ^ n : R[X]) := by
  simpa only [← C_1, ← one_mulₓ] using le_trailing_degree_C_mul_X_pow n (1 : R)

theorem le_trailing_degree_X : (1 : WithTop ℕ) ≤ trailingDegree (x : R[X]) :=
  le_trailing_degree_monomial

theorem nat_trailing_degree_X_le : (x : R[X]).natTrailingDegree ≤ 1 :=
  nat_trailing_degree_monomial_le

@[simp]
theorem trailing_coeff_eq_zero : trailingCoeff p = 0 ↔ p = 0 :=
  ⟨fun h =>
    by_contradiction fun hp =>
      mt mem_support_iff.1 (not_not.2 h) (mem_of_min (trailing_degree_eq_nat_trailing_degree hp)),
    fun h => h.symm ▸ leading_coeff_zero⟩

theorem trailing_coeff_nonzero_iff_nonzero : trailingCoeff p ≠ 0 ↔ p ≠ 0 :=
  not_congr trailing_coeff_eq_zero

theorem nat_trailing_degree_mem_support_of_nonzero : p ≠ 0 → natTrailingDegree p ∈ p.Support :=
  mem_support_iff.mpr ∘ trailing_coeff_nonzero_iff_nonzero.mpr

theorem nat_trailing_degree_le_of_mem_supp (a : ℕ) : a ∈ p.Support → natTrailingDegree p ≤ a :=
  nat_trailing_degree_le_of_ne_zero ∘ mem_support_iff.mp

theorem nat_trailing_degree_eq_support_min' (h : p ≠ 0) :
    natTrailingDegree p = p.Support.min' (nonempty_support_iff.mpr h) := by
  apply le_antisymmₓ
  · apply le_min'
    intro y hy
    exact nat_trailing_degree_le_of_mem_supp y hy
    
  · apply Finset.min'_le
    exact mem_support_iff.mpr (trailing_coeff_nonzero_iff_nonzero.mpr h)
    

theorem nat_trailing_degree_le_nat_degree (p : R[X]) : p.natTrailingDegree ≤ p.natDegree := by
  by_cases' hp : p = 0
  · rw [hp, nat_degree_zero, nat_trailing_degree_zero]
    
  · exact le_nat_degree_of_ne_zero (mt trailing_coeff_eq_zero.mp hp)
    

theorem nat_trailing_degree_mul_X_pow {p : R[X]} (hp : p ≠ 0) (n : ℕ) :
    (p * X ^ n).natTrailingDegree = p.natTrailingDegree + n := by
  apply le_antisymmₓ
  · refine' nat_trailing_degree_le_of_ne_zero fun h => mt trailing_coeff_eq_zero.mp hp _
    rwa [trailing_coeff, ← coeff_mul_X_pow]
    
  · rw [nat_trailing_degree_eq_support_min' fun h => hp (mul_X_pow_eq_zero h), Finset.le_min'_iff]
    intro y hy
    have key : n ≤ y := by
      rw [mem_support_iff, coeff_mul_X_pow'] at hy
      exact by_contra fun h => hy (if_neg h)
    rw [mem_support_iff, coeff_mul_X_pow', if_pos key] at hy
    exact (le_tsub_iff_right key).mp (nat_trailing_degree_le_of_ne_zero hy)
    

theorem le_trailing_degree_mul : p.trailingDegree + q.trailingDegree ≤ (p * q).trailingDegree := by
  refine' le_inf fun n hn => _
  rw [mem_support_iff, coeff_mul] at hn
  obtain ⟨⟨i, j⟩, hij, hpq⟩ := exists_ne_zero_of_sum_ne_zero hn
  refine'
    (add_le_add (inf_le (mem_support_iff.mpr (left_ne_zero_of_mul hpq)))
          (inf_le (mem_support_iff.mpr (right_ne_zero_of_mul hpq)))).trans
      (le_of_eqₓ _)
  rwa [WithTop.some_eq_coe, WithTop.some_eq_coe, WithTop.some_eq_coe, ← WithTop.coe_add, WithTop.coe_eq_coe, ←
    nat.mem_antidiagonal]

theorem le_nat_trailing_degree_mul (h : p * q ≠ 0) :
    p.natTrailingDegree + q.natTrailingDegree ≤ (p * q).natTrailingDegree := by
  have hp : p ≠ 0 := fun hp =>
    h
      (by
        rw [hp, zero_mul])
  have hq : q ≠ 0 := fun hq =>
    h
      (by
        rw [hq, mul_zero])
  rw [← WithTop.coe_le_coe, WithTop.coe_add, ← trailing_degree_eq_nat_trailing_degree hp, ←
    trailing_degree_eq_nat_trailing_degree hq, ← trailing_degree_eq_nat_trailing_degree h]
  exact le_trailing_degree_mul

theorem coeff_mul_nat_trailing_degree_add_nat_trailing_degree :
    (p * q).coeff (p.natTrailingDegree + q.natTrailingDegree) = p.trailingCoeff * q.trailingCoeff := by
  rw [coeff_mul]
  refine'
    Finset.sum_eq_single (p.nat_trailing_degree, q.nat_trailing_degree) _ fun h =>
      (h (nat.mem_antidiagonal.mpr rfl)).elim
  rintro ⟨i, j⟩ h₁ h₂
  rw [nat.mem_antidiagonal] at h₁
  by_cases' hi : i < p.nat_trailing_degree
  · rw [coeff_eq_zero_of_lt_nat_trailing_degree hi, zero_mul]
    
  by_cases' hj : j < q.nat_trailing_degree
  · rw [coeff_eq_zero_of_lt_nat_trailing_degree hj, mul_zero]
    
  rw [not_ltₓ] at hi hj
  refine' (h₂ (prod.ext_iff.mpr _).symm).elim
  exact (add_eq_add_iff_eq_and_eq hi hj).mp h₁.symm

theorem trailing_degree_mul' (h : p.trailingCoeff * q.trailingCoeff ≠ 0) :
    (p * q).trailingDegree = p.trailingDegree + q.trailingDegree := by
  have hp : p ≠ 0 := fun hp =>
    h
      (by
        rw [hp, trailing_coeff_zero, zero_mul])
  have hq : q ≠ 0 := fun hq =>
    h
      (by
        rw [hq, trailing_coeff_zero, mul_zero])
  refine' le_antisymmₓ _ le_trailing_degree_mul
  rw [trailing_degree_eq_nat_trailing_degree hp, trailing_degree_eq_nat_trailing_degree hq]
  apply le_trailing_degree_of_ne_zero
  rwa [coeff_mul_nat_trailing_degree_add_nat_trailing_degree]

theorem nat_trailing_degree_mul' (h : p.trailingCoeff * q.trailingCoeff ≠ 0) :
    (p * q).natTrailingDegree = p.natTrailingDegree + q.natTrailingDegree := by
  have hp : p ≠ 0 := fun hp =>
    h
      (by
        rw [hp, trailing_coeff_zero, zero_mul])
  have hq : q ≠ 0 := fun hq =>
    h
      (by
        rw [hq, trailing_coeff_zero, mul_zero])
  apply nat_trailing_degree_eq_of_trailing_degree_eq_some
  rw [trailing_degree_mul' h, WithTop.coe_add, ← trailing_degree_eq_nat_trailing_degree hp, ←
    trailing_degree_eq_nat_trailing_degree hq]

theorem nat_trailing_degree_mul [NoZeroDivisors R] (hp : p ≠ 0) (hq : q ≠ 0) :
    (p * q).natTrailingDegree = p.natTrailingDegree + q.natTrailingDegree :=
  nat_trailing_degree_mul' (mul_ne_zero (mt trailing_coeff_eq_zero.mp hp) (mt trailing_coeff_eq_zero.mp hq))

end Semiringₓ

section NonzeroSemiring

variable [Semiringₓ R] [Nontrivial R] {p q : R[X]}

@[simp]
theorem trailing_degree_one : trailingDegree (1 : R[X]) = (0 : WithTop ℕ) :=
  trailing_degree_C one_ne_zero

@[simp]
theorem trailing_degree_X : trailingDegree (x : R[X]) = 1 :=
  trailing_degree_monomial one_ne_zero

@[simp]
theorem nat_trailing_degree_X : (x : R[X]).natTrailingDegree = 1 :=
  nat_trailing_degree_monomial one_ne_zero

end NonzeroSemiring

section Ringₓ

variable [Ringₓ R]

@[simp]
theorem trailing_degree_neg (p : R[X]) : trailingDegree (-p) = trailingDegree p := by
  unfold trailing_degree <;> rw [support_neg]

@[simp]
theorem nat_trailing_degree_neg (p : R[X]) : natTrailingDegree (-p) = natTrailingDegree p := by
  simp [← nat_trailing_degree]

@[simp]
theorem nat_trailing_degree_int_cast (n : ℤ) : natTrailingDegree (n : R[X]) = 0 := by
  simp only [C_eq_int_cast, ← nat_trailing_degree_C]

end Ringₓ

section Semiringₓ

variable [Semiringₓ R]

/-- The second-lowest coefficient, or 0 for constants -/
def nextCoeffUp (p : R[X]) : R :=
  if p.natTrailingDegree = 0 then 0 else p.coeff (p.natTrailingDegree + 1)

@[simp]
theorem next_coeff_up_C_eq_zero (c : R) : nextCoeffUp (c c) = 0 := by
  rw [next_coeff_up]
  simp

theorem next_coeff_up_of_pos_nat_trailing_degree (p : R[X]) (hp : 0 < p.natTrailingDegree) :
    nextCoeffUp p = p.coeff (p.natTrailingDegree + 1) := by
  rw [next_coeff_up, if_neg]
  contrapose! hp
  simpa

end Semiringₓ

section Semiringₓ

variable [Semiringₓ R] {p q : R[X]} {ι : Type _}

theorem coeff_nat_trailing_degree_eq_zero_of_trailing_degree_lt (h : trailingDegree p < trailingDegree q) :
    coeff q (natTrailingDegree p) = 0 :=
  coeff_eq_zero_of_trailing_degree_lt <| nat_trailing_degree_le_trailing_degree.trans_lt h

theorem ne_zero_of_trailing_degree_lt {n : WithTop ℕ} (h : trailingDegree p < n) : p ≠ 0 := fun h₀ =>
  h.not_le
    (by
      simp [← h₀])

end Semiringₓ

end Polynomial

