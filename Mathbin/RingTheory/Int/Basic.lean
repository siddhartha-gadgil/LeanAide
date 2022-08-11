/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jens Wagemaker, Aaron Anderson
-/
import Mathbin.RingTheory.Coprime.Basic
import Mathbin.RingTheory.PrincipalIdealDomain

/-!
# Divisibility over ℕ and ℤ

This file collects results for the integers and natural numbers that use abstract algebra in
their proofs or cases of ℕ and ℤ being examples of structures in abstract algebra.

## Main statements

* `nat.factors_eq`: the multiset of elements of `nat.factors` is equal to the factors
   given by the `unique_factorization_monoid` instance
* ℤ is a `normalization_monoid`
* ℤ is a `gcd_monoid`

## Tags

prime, irreducible, natural numbers, integers, normalization monoid, gcd monoid,
greatest common divisor, prime factorization, prime factors, unique factorization,
unique factors
-/


namespace Nat

instance : WfDvdMonoid ℕ :=
  ⟨by
    refine'
      RelHomClass.well_founded (⟨fun x : ℕ => if x = 0 then (⊤ : WithTop ℕ) else x, _⟩ : DvdNotUnit →r (· < ·))
        (WithTop.well_founded_lt Nat.lt_wf)
    intro a b h
    cases a
    · exfalso
      revert h
      simp [← DvdNotUnit]
      
    cases b
    · simpa [← succ_ne_zero] using WithTop.coe_lt_top (a + 1)
      
    cases' dvd_and_not_dvd_iff.2 h with h1 h2
    simp only [← succ_ne_zero, ← WithTop.coe_lt_coe, ← if_false]
    apply lt_of_le_of_neₓ (Nat.le_of_dvdₓ (Nat.succ_posₓ _) h1) fun con => h2 _
    rw [Con]⟩

instance : UniqueFactorizationMonoid ℕ :=
  ⟨fun _ => Nat.irreducible_iff_prime⟩

end Nat

/-- `ℕ` is a gcd_monoid. -/
instance : GcdMonoid ℕ where
  gcd := Nat.gcdₓ
  lcm := Nat.lcmₓ
  gcd_dvd_left := Nat.gcd_dvd_leftₓ
  gcd_dvd_right := Nat.gcd_dvd_rightₓ
  dvd_gcd := fun a b c => Nat.dvd_gcdₓ
  gcd_mul_lcm := fun a b => by
    rw [Nat.gcd_mul_lcmₓ]
  lcm_zero_left := Nat.lcm_zero_leftₓ
  lcm_zero_right := Nat.lcm_zero_rightₓ

instance : NormalizedGcdMonoid ℕ :=
  { (inferInstance : GcdMonoid ℕ), (inferInstance : NormalizationMonoid ℕ) with
    normalize_gcd := fun a b => normalize_eq _, normalize_lcm := fun a b => normalize_eq _ }

theorem gcd_eq_nat_gcd (m n : ℕ) : gcd m n = Nat.gcdₓ m n :=
  rfl

theorem lcm_eq_nat_lcm (m n : ℕ) : lcm m n = Nat.lcmₓ m n :=
  rfl

namespace Int

section NormalizationMonoid

instance : NormalizationMonoid ℤ where
  normUnit := fun a : ℤ => if 0 ≤ a then 1 else -1
  norm_unit_zero := if_pos le_rfl
  norm_unit_mul := fun a b hna hnb => by
    cases' hna.lt_or_lt with ha ha <;>
      cases' hnb.lt_or_lt with hb hb <;> simp [← mul_nonneg_iff, ← ha.le, ← ha.not_le, ← hb.le, ← hb.not_le]
  norm_unit_coe_units := fun u =>
    (units_eq_one_or u).elim (fun eq => Eq.symm ▸ if_pos zero_le_one) fun eq =>
      Eq.symm ▸
        if_neg
          (not_le_of_gtₓ <|
            show (-1 : ℤ) < 0 by
              decide)

theorem normalize_of_nonneg {z : ℤ} (h : 0 ≤ z) : normalize z = z :=
  show z * ↑(ite _ _ _) = z by
    rw [if_pos h, Units.coe_one, mul_oneₓ]

theorem normalize_of_neg {z : ℤ} (h : z < 0) : normalize z = -z :=
  show z * ↑(ite _ _ _) = -z by
    rw [if_neg (not_le_of_gtₓ h), Units.coe_neg, Units.coe_one, mul_neg_one]

theorem normalize_coe_nat (n : ℕ) : normalize (n : ℤ) = n :=
  normalize_of_nonneg (coe_nat_le_coe_nat_of_le <| Nat.zero_leₓ n)

theorem coe_nat_abs_eq_normalize (z : ℤ) : (z.natAbs : ℤ) = normalize z := by
  by_cases' 0 ≤ z
  · simp [← nat_abs_of_nonneg h, ← normalize_of_nonneg h]
    
  · simp [← of_nat_nat_abs_of_nonpos (le_of_not_geₓ h), ← normalize_of_neg (lt_of_not_geₓ h)]
    

theorem nonneg_of_normalize_eq_self {z : ℤ} (hz : normalize z = z) : 0 ≤ z :=
  calc
    0 ≤ (z.natAbs : ℤ) := coe_zero_le _
    _ = normalize z := coe_nat_abs_eq_normalize _
    _ = z := hz
    

theorem nonneg_iff_normalize_eq_self (z : ℤ) : normalize z = z ↔ 0 ≤ z :=
  ⟨nonneg_of_normalize_eq_self, normalize_of_nonneg⟩

theorem eq_of_associated_of_nonneg {a b : ℤ} (h : Associated a b) (ha : 0 ≤ a) (hb : 0 ≤ b) : a = b :=
  dvd_antisymm_of_normalize_eq (normalize_of_nonneg ha) (normalize_of_nonneg hb) h.Dvd h.symm.Dvd

end NormalizationMonoid

section GcdMonoid

instance : GcdMonoid ℤ where
  gcd := fun a b => Int.gcdₓ a b
  lcm := fun a b => Int.lcm a b
  gcd_dvd_left := fun a b => Int.gcd_dvd_left _ _
  gcd_dvd_right := fun a b => Int.gcd_dvd_right _ _
  dvd_gcd := fun a b c => dvd_gcd
  gcd_mul_lcm := fun a b => by
    rw [← Int.coe_nat_mul, gcd_mul_lcm, coe_nat_abs_eq_normalize]
    exact normalize_associated (a * b)
  lcm_zero_left := fun a => coe_nat_eq_zero.2 <| Nat.lcm_zero_leftₓ _
  lcm_zero_right := fun a => coe_nat_eq_zero.2 <| Nat.lcm_zero_rightₓ _

instance : NormalizedGcdMonoid ℤ :=
  { Int.normalizationMonoid, (inferInstance : GcdMonoid ℤ) with normalize_gcd := fun a b => normalize_coe_nat _,
    normalize_lcm := fun a b => normalize_coe_nat _ }

theorem coe_gcd (i j : ℤ) : ↑(Int.gcdₓ i j) = GcdMonoid.gcd i j :=
  rfl

theorem coe_lcm (i j : ℤ) : ↑(Int.lcm i j) = GcdMonoid.lcm i j :=
  rfl

theorem nat_abs_gcd (i j : ℤ) : natAbs (GcdMonoid.gcd i j) = Int.gcdₓ i j :=
  rfl

theorem nat_abs_lcm (i j : ℤ) : natAbs (GcdMonoid.lcm i j) = Int.lcm i j :=
  rfl

end GcdMonoid

theorem exists_unit_of_abs (a : ℤ) : ∃ (u : ℤ)(h : IsUnit u), (Int.natAbs a : ℤ) = u * a := by
  cases' nat_abs_eq a with h
  · use 1, is_unit_one
    rw [← h, one_mulₓ]
    
  · use -1, is_unit_one.neg
    rw [← neg_eq_iff_neg_eq.mp (Eq.symm h)]
    simp only [← neg_mul, ← one_mulₓ]
    

theorem gcd_eq_nat_abs {a b : ℤ} : Int.gcdₓ a b = Nat.gcdₓ a.natAbs b.natAbs :=
  rfl

theorem gcd_eq_one_iff_coprime {a b : ℤ} : Int.gcdₓ a b = 1 ↔ IsCoprime a b := by
  constructor
  · intro hg
    obtain ⟨ua, hua, ha⟩ := exists_unit_of_abs a
    obtain ⟨ub, hub, hb⟩ := exists_unit_of_abs b
    use Nat.gcdA (Int.natAbs a) (Int.natAbs b) * ua, Nat.gcdB (Int.natAbs a) (Int.natAbs b) * ub
    rw [mul_assoc, ← ha, mul_assoc, ← hb, mul_comm, mul_comm _ (Int.natAbs b : ℤ), ← Nat.gcd_eq_gcd_ab, ←
      gcd_eq_nat_abs, hg, Int.coe_nat_one]
    
  · rintro ⟨r, s, h⟩
    by_contra hg
    obtain ⟨p, ⟨hp, ha, hb⟩⟩ := nat.prime.not_coprime_iff_dvd.mp hg
    apply Nat.Prime.not_dvd_one hp
    rw [← coe_nat_dvd, Int.coe_nat_one, ← h]
    exact dvd_add ((coe_nat_dvd_left.mpr ha).mul_left _) ((coe_nat_dvd_left.mpr hb).mul_left _)
    

theorem coprime_iff_nat_coprime {a b : ℤ} : IsCoprime a b ↔ Nat.Coprime a.natAbs b.natAbs := by
  rw [← gcd_eq_one_iff_coprime, Nat.coprime_iff_gcd_eq_oneₓ, gcd_eq_nat_abs]

theorem sq_of_gcd_eq_one {a b c : ℤ} (h : Int.gcdₓ a b = 1) (heq : a * b = c ^ 2) :
    ∃ a0 : ℤ, a = a0 ^ 2 ∨ a = -(a0 ^ 2) := by
  have h' : IsUnit (GcdMonoid.gcd a b) := by
    rw [← coe_gcd, h, Int.coe_nat_one]
    exact is_unit_one
  obtain ⟨d, ⟨u, hu⟩⟩ := exists_associated_pow_of_mul_eq_pow h' HEq
  use d
  rw [← hu]
  cases' Int.units_eq_one_or u with hu' hu' <;>
    · rw [hu']
      simp
      

theorem sq_of_coprime {a b c : ℤ} (h : IsCoprime a b) (heq : a * b = c ^ 2) : ∃ a0 : ℤ, a = a0 ^ 2 ∨ a = -(a0 ^ 2) :=
  sq_of_gcd_eq_one (gcd_eq_one_iff_coprime.mpr h) HEq

theorem nat_abs_euclidean_domain_gcd (a b : ℤ) : Int.natAbs (EuclideanDomain.gcd a b) = Int.gcdₓ a b := by
  apply Nat.dvd_antisymm <;> rw [← Int.coe_nat_dvd]
  · rw [Int.nat_abs_dvd]
    exact Int.dvd_gcd (EuclideanDomain.gcd_dvd_left _ _) (EuclideanDomain.gcd_dvd_right _ _)
    
  · rw [Int.dvd_nat_abs]
    exact EuclideanDomain.dvd_gcd (Int.gcd_dvd_left _ _) (Int.gcd_dvd_right _ _)
    

end Int

/-- Maps an associate class of integers consisting of `-n, n` to `n : ℕ` -/
def associatesIntEquivNat : Associates ℤ ≃ ℕ := by
  refine' ⟨fun z => z.out.nat_abs, fun n => Associates.mk n, _, _⟩
  · refine' fun a =>
      (Quotientₓ.induction_on' a) fun a => Associates.mk_eq_mk_iff_associated.2 <| Associated.symm <| ⟨norm_unit a, _⟩
    show normalize a = Int.natAbs (normalize a)
    rw [Int.coe_nat_abs_eq_normalize, normalize_idem]
    
  · intro n
    dsimp'
    rw [← normalize_apply, ← Int.coe_nat_abs_eq_normalize, Int.nat_abs_of_nat, Int.nat_abs_of_nat]
    

theorem Int.Prime.dvd_mul {m n : ℤ} {p : ℕ} (hp : Nat.Prime p) (h : (p : ℤ) ∣ m * n) : p ∣ m.natAbs ∨ p ∣ n.natAbs := by
  apply (Nat.Prime.dvd_mul hp).mp
  rw [← Int.nat_abs_mul]
  exact int.coe_nat_dvd_left.mp h

theorem Int.Prime.dvd_mul' {m n : ℤ} {p : ℕ} (hp : Nat.Prime p) (h : (p : ℤ) ∣ m * n) : (p : ℤ) ∣ m ∨ (p : ℤ) ∣ n := by
  rw [Int.coe_nat_dvd_left, Int.coe_nat_dvd_left]
  exact Int.Prime.dvd_mul hp h

theorem Int.Prime.dvd_pow {n : ℤ} {k p : ℕ} (hp : Nat.Prime p) (h : (p : ℤ) ∣ n ^ k) : p ∣ n.natAbs := by
  apply @Nat.Prime.dvd_of_dvd_pow _ _ k hp
  rw [← Int.nat_abs_pow]
  exact int.coe_nat_dvd_left.mp h

theorem Int.Prime.dvd_pow' {n : ℤ} {k p : ℕ} (hp : Nat.Prime p) (h : (p : ℤ) ∣ n ^ k) : (p : ℤ) ∣ n := by
  rw [Int.coe_nat_dvd_left]
  exact Int.Prime.dvd_pow hp h

theorem prime_two_or_dvd_of_dvd_two_mul_pow_self_two {m : ℤ} {p : ℕ} (hp : Nat.Prime p) (h : (p : ℤ) ∣ 2 * m ^ 2) :
    p = 2 ∨ p ∣ Int.natAbs m := by
  cases' Int.Prime.dvd_mul hp h with hp2 hpp
  · apply Or.intro_left
    exact le_antisymmₓ (Nat.le_of_dvdₓ zero_lt_two hp2) (Nat.Prime.two_le hp)
    
  · apply Or.intro_rightₓ
    rw [sq, Int.nat_abs_mul] at hpp
    exact (or_selfₓ _).mp ((Nat.Prime.dvd_mul hp).mp hpp)
    

theorem Int.exists_prime_and_dvd {n : ℤ} (hn : n.natAbs ≠ 1) : ∃ p, Prime p ∧ p ∣ n := by
  obtain ⟨p, pp, pd⟩ := Nat.exists_prime_and_dvd hn
  exact ⟨p, nat.prime_iff_prime_int.mp pp, int.coe_nat_dvd_left.mpr pd⟩

open UniqueFactorizationMonoid

theorem Nat.factors_eq {n : ℕ} : normalizedFactors n = n.factors := by
  cases n
  · simp
    
  rw [← Multiset.rel_eq, ← associated_eq_eq]
  apply factors_unique irreducible_of_normalized_factor _
  · rw [Multiset.coe_prod, Nat.prod_factors n.succ_ne_zero]
    apply normalized_factors_prod (Nat.succ_ne_zero _)
    
  · infer_instance
    
  · intro x hx
    rw [Nat.irreducible_iff_prime, ← Nat.prime_iff]
    exact Nat.prime_of_mem_factors hx
    

theorem Nat.factors_multiset_prod_of_irreducible {s : Multiset ℕ} (h : ∀ x : ℕ, x ∈ s → Irreducible x) :
    normalizedFactors s.Prod = s := by
  rw [← Multiset.rel_eq, ← associated_eq_eq]
  apply UniqueFactorizationMonoid.factors_unique irreducible_of_normalized_factor h (normalized_factors_prod _)
  rw [Ne.def, Multiset.prod_eq_zero_iff]
  intro con
  exact not_irreducible_zero (h 0 Con)

namespace multiplicity

theorem finite_int_iff_nat_abs_finite {a b : ℤ} : Finite a b ↔ Finite a.natAbs b.natAbs := by
  simp only [← finite_def, Int.nat_abs_dvd_iff_dvd, ← Int.nat_abs_pow]

theorem finite_int_iff {a b : ℤ} : Finite a b ↔ a.natAbs ≠ 1 ∧ b ≠ 0 := by
  rw [finite_int_iff_nat_abs_finite, finite_nat_iff, pos_iff_ne_zero, Int.nat_abs_ne_zero]

instance decidableNat : DecidableRel fun a b : ℕ => (multiplicity a b).Dom := fun a b =>
  decidableOfIff _ finite_nat_iff.symm

instance decidableInt : DecidableRel fun a b : ℤ => (multiplicity a b).Dom := fun a b =>
  decidableOfIff _ finite_int_iff.symm

end multiplicity

theorem induction_on_primes {P : ℕ → Prop} (h₀ : P 0) (h₁ : P 1) (h : ∀ p a : ℕ, p.Prime → P a → P (p * a)) (n : ℕ) :
    P n := by
  apply UniqueFactorizationMonoid.induction_on_prime
  exact h₀
  · intro n h
    rw [Nat.is_unit_iff.1 h]
    exact h₁
    
  · intro a p _ hp ha
    exact h p a (Nat.prime_iff.2 hp) ha
    

theorem Int.associated_nat_abs (k : ℤ) : Associated k k.natAbs :=
  associated_of_dvd_dvd (Int.coe_nat_dvd_right.mpr dvd_rfl) (Int.nat_abs_dvd.mpr dvd_rfl)

theorem Int.prime_iff_nat_abs_prime {k : ℤ} : Prime k ↔ Nat.Prime k.natAbs :=
  (Int.associated_nat_abs k).prime_iff.trans Nat.prime_iff_prime_int.symm

theorem Int.associated_iff_nat_abs {a b : ℤ} : Associated a b ↔ a.natAbs = b.natAbs := by
  rw [← dvd_dvd_iff_associated, ← Int.nat_abs_dvd_iff_dvd, ← Int.nat_abs_dvd_iff_dvd, dvd_dvd_iff_associated]
  exact associated_iff_eq

theorem Int.associated_iff {a b : ℤ} : Associated a b ↔ a = b ∨ a = -b := by
  rw [Int.associated_iff_nat_abs]
  exact Int.nat_abs_eq_nat_abs_iff

namespace Int

theorem zmultiples_nat_abs (a : ℤ) : AddSubgroup.zmultiples (a.natAbs : ℤ) = AddSubgroup.zmultiples a :=
  le_antisymmₓ (AddSubgroup.zmultiples_subset (mem_zmultiples_iff.mpr (dvd_nat_abs.mpr (dvd_refl a))))
    (AddSubgroup.zmultiples_subset (mem_zmultiples_iff.mpr (nat_abs_dvd.mpr (dvd_refl a))))

theorem span_nat_abs (a : ℤ) : Ideal.span ({a.natAbs} : Set ℤ) = Ideal.span {a} := by
  rw [Ideal.span_singleton_eq_span_singleton]
  exact (associated_nat_abs _).symm

theorem eq_pow_of_mul_eq_pow_bit1_left {a b c : ℤ} (hab : IsCoprime a b) {k : ℕ} (h : a * b = c ^ bit1 k) :
    ∃ d, a = d ^ bit1 k := by
  obtain ⟨d, hd⟩ := exists_associated_pow_of_mul_eq_pow' hab h
  replace hd := hd.symm
  rw [associated_iff_nat_abs, nat_abs_eq_nat_abs_iff, ← neg_pow_bit1] at hd
  obtain rfl | rfl := hd <;> exact ⟨_, rfl⟩

theorem eq_pow_of_mul_eq_pow_bit1_right {a b c : ℤ} (hab : IsCoprime a b) {k : ℕ} (h : a * b = c ^ bit1 k) :
    ∃ d, b = d ^ bit1 k :=
  eq_pow_of_mul_eq_pow_bit1_left hab.symm
    (by
      rwa [mul_comm] at h)

theorem eq_pow_of_mul_eq_pow_bit1 {a b c : ℤ} (hab : IsCoprime a b) {k : ℕ} (h : a * b = c ^ bit1 k) :
    (∃ d, a = d ^ bit1 k) ∧ ∃ e, b = e ^ bit1 k :=
  ⟨eq_pow_of_mul_eq_pow_bit1_left hab h, eq_pow_of_mul_eq_pow_bit1_right hab h⟩

end Int

