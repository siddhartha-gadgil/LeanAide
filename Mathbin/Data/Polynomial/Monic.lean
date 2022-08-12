/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Scott Morrison, Jens Wagemaker
-/
import Mathbin.Data.Polynomial.Reverse
import Mathbin.Algebra.Associated
import Mathbin.Algebra.Regular.Smul

/-!
# Theory of monic polynomials

We give several tools for proving that polynomials are monic, e.g.
`monic.mul`, `monic.map`, `monic.pow`.
-/


noncomputable section

open Finset

open BigOperators Classical Polynomial

namespace Polynomial

universe u v y

variable {R : Type u} {S : Type v} {a b : R} {m n : ℕ} {ι : Type y}

section Semiringₓ

variable [Semiringₓ R] {p q r : R[X]}

theorem Monic.as_sum (hp : p.Monic) : p = X ^ p.natDegree + ∑ i in range p.natDegree, c (p.coeff i) * X ^ i := by
  conv_lhs => rw [p.as_sum_range_C_mul_X_pow, sum_range_succ_comm]
  suffices C (p.coeff p.nat_degree) = 1 by
    rw [this, one_mulₓ]
  exact congr_arg C hp

theorem ne_zero_of_ne_zero_of_monic (hp : p ≠ 0) (hq : Monic q) : q ≠ 0 := by
  rintro rfl
  rw [monic.def, leading_coeff_zero] at hq
  rw [← mul_oneₓ p, ← C_1, ← hq, C_0, mul_zero] at hp
  exact hp rfl

theorem Monic.map [Semiringₓ S] (f : R →+* S) (hp : Monic p) : Monic (p.map f) := by
  nontriviality
  have : f (leading_coeff p) ≠ 0 := by
    rw [show _ = _ from hp, f.map_one]
    exact one_ne_zero
  rw [monic, leading_coeff, coeff_map]
  suffices p.coeff (map f p).natDegree = 1 by
    simp [← this]
  rwa [nat_degree_eq_of_degree_eq (degree_map_eq_of_leading_coeff_ne_zero f this)]

theorem monic_C_mul_of_mul_leading_coeff_eq_one {b : R} (hp : b * p.leadingCoeff = 1) : Monic (c b * p) := by
  nontriviality
  rw [monic, leading_coeff_mul' _] <;> simp [← leading_coeff_C b, ← hp]

theorem monic_mul_C_of_leading_coeff_mul_eq_one {b : R} (hp : p.leadingCoeff * b = 1) : Monic (p * c b) := by
  nontriviality
  rw [monic, leading_coeff_mul' _] <;> simp [← leading_coeff_C b, ← hp]

theorem monic_of_degree_le (n : ℕ) (H1 : degree p ≤ n) (H2 : coeff p n = 1) : Monic p :=
  Decidable.byCases (fun H : degree p < n => eq_of_zero_eq_one (H2 ▸ (coeff_eq_zero_of_degree_lt H).symm) _ _)
    fun H : ¬degree p < n => by
    rwa [monic, leading_coeff, nat_degree, (lt_or_eq_of_leₓ H1).resolve_left H]

theorem monic_X_pow_add {n : ℕ} (H : degree p ≤ n) : Monic (X ^ (n + 1) + p) :=
  have H1 : degree p < n + 1 := lt_of_le_of_ltₓ H (WithBot.coe_lt_coe.2 (Nat.lt_succ_selfₓ n))
  monic_of_degree_le (n + 1) (le_transₓ (degree_add_le _ _) (max_leₓ (degree_X_pow_le _) (le_of_ltₓ H1)))
    (by
      rw [coeff_add, coeff_X_pow, if_pos rfl, coeff_eq_zero_of_degree_lt H1, add_zeroₓ])

theorem monic_X_add_C (x : R) : Monic (X + c x) :=
  pow_oneₓ (x : R[X]) ▸ monic_X_pow_add degree_C_le

theorem Monic.mul (hp : Monic p) (hq : Monic q) : Monic (p * q) :=
  if h0 : (0 : R) = 1 then
    have := subsingleton_of_zero_eq_one h0
    Subsingleton.elimₓ _ _
  else by
    have : leadingCoeff p * leadingCoeff q ≠ 0 := by
      simp [← monic.def.1 hp, ← monic.def.1 hq, ← Ne.symm h0]
    rw [monic.def, leading_coeff_mul' this, monic.def.1 hp, monic.def.1 hq, one_mulₓ]

theorem Monic.pow (hp : Monic p) : ∀ n : ℕ, Monic (p ^ n)
  | 0 => monic_one
  | n + 1 => by
    rw [pow_succₓ]
    exact hp.mul (monic.pow n)

theorem Monic.add_of_left (hp : Monic p) (hpq : degree q < degree p) : Monic (p + q) := by
  rwa [monic, add_commₓ, leading_coeff_add_of_degree_lt hpq]

theorem Monic.add_of_right (hq : Monic q) (hpq : degree p < degree q) : Monic (p + q) := by
  rwa [monic, leading_coeff_add_of_degree_lt hpq]

theorem Monic.of_mul_monic_left (hp : p.Monic) (hpq : (p * q).Monic) : q.Monic := by
  contrapose! hpq
  rw [monic.def] at hpq⊢
  rwa [leading_coeff_monic_mul hp]

theorem Monic.of_mul_monic_right (hq : q.Monic) (hpq : (p * q).Monic) : p.Monic := by
  contrapose! hpq
  rw [monic.def] at hpq⊢
  rwa [leading_coeff_mul_monic hq]

namespace Monic

@[simp]
theorem nat_degree_eq_zero_iff_eq_one {p : R[X]} (hp : p.Monic) : p.natDegree = 0 ↔ p = 1 := by
  constructor <;> intro h
  swap
  · rw [h]
    exact nat_degree_one
    
  have : p = C (p.coeff 0) := by
    rw [← Polynomial.degree_le_zero_iff]
    rwa [Polynomial.nat_degree_eq_zero_iff_degree_le_zero] at h
  rw [this]
  convert C_1
  rw [← h]
  apply hp

@[simp]
theorem degree_le_zero_iff_eq_one {p : R[X]} (hp : p.Monic) : p.degree ≤ 0 ↔ p = 1 := by
  rw [← hp.nat_degree_eq_zero_iff_eq_one, nat_degree_eq_zero_iff_degree_le_zero]

theorem nat_degree_mul {p q : R[X]} (hp : p.Monic) (hq : q.Monic) : (p * q).natDegree = p.natDegree + q.natDegree := by
  nontriviality R
  apply nat_degree_mul'
  simp [← hp.leading_coeff, ← hq.leading_coeff]

theorem degree_mul_comm {p : R[X]} (hp : p.Monic) (q : R[X]) : (p * q).degree = (q * p).degree := by
  by_cases' h : q = 0
  · simp [← h]
    
  rw [degree_mul', hp.degree_mul]
  · exact add_commₓ _ _
    
  · rwa [hp.leading_coeff, one_mulₓ, leading_coeff_ne_zero]
    

theorem nat_degree_mul' {p q : R[X]} (hp : p.Monic) (hq : q ≠ 0) : (p * q).natDegree = p.natDegree + q.natDegree := by
  rw [nat_degree_mul', add_commₓ]
  simpa [← hp.leading_coeff, ← leading_coeff_ne_zero]

theorem nat_degree_mul_comm {p : R[X]} (hp : p.Monic) (q : R[X]) : (p * q).natDegree = (q * p).natDegree := by
  by_cases' h : q = 0
  · simp [← h]
    
  rw [hp.nat_degree_mul' h, Polynomial.nat_degree_mul', add_commₓ]
  simpa [← hp.leading_coeff, ← leading_coeff_ne_zero]

theorem next_coeff_mul {p q : R[X]} (hp : Monic p) (hq : Monic q) : nextCoeff (p * q) = nextCoeff p + nextCoeff q := by
  nontriviality
  simp only [coeff_one_reverse]
  rw [reverse_mul] <;> simp [← coeff_mul, ← nat.antidiagonal, ← hp.leading_coeff, ← hq.leading_coeff, ← add_commₓ]

theorem eq_one_of_map_eq_one {S : Type _} [Semiringₓ S] [Nontrivial S] (f : R →+* S) (hp : p.Monic)
    (map_eq : p.map f = 1) : p = 1 := by
  nontriviality R
  have hdeg : p.degree = 0 := by
    rw [← degree_map_eq_of_leading_coeff_ne_zero f _, map_eq, degree_one]
    · rw [hp.leading_coeff, f.map_one]
      exact one_ne_zero
      
  have hndeg : p.nat_degree = 0 := with_bot.coe_eq_coe.mp ((degree_eq_nat_degree hp.ne_zero).symm.trans hdeg)
  convert eq_C_of_degree_eq_zero hdeg
  rw [← hndeg, ← Polynomial.leadingCoeff, hp.leading_coeff, C.map_one]

theorem nat_degree_pow (hp : p.Monic) (n : ℕ) : (p ^ n).natDegree = n * p.natDegree := by
  induction' n with n hn
  · simp
    
  · rw [pow_succₓ, hp.nat_degree_mul (hp.pow n), hn]
    ring
    

end Monic

@[simp]
theorem nat_degree_pow_X_add_C [Nontrivial R] (n : ℕ) (r : R) : ((X + c r) ^ n).natDegree = n := by
  rw [(monic_X_add_C r).nat_degree_pow, nat_degree_X_add_C, mul_oneₓ]

end Semiringₓ

section CommSemiringₓ

variable [CommSemiringₓ R] {p : R[X]}

theorem monic_multiset_prod_of_monic (t : Multiset ι) (f : ι → R[X]) (ht : ∀, ∀ i ∈ t, ∀, Monic (f i)) :
    Monic (t.map f).Prod := by
  revert ht
  refine' t.induction_on _ _
  · simp
    
  intro a t ih ht
  rw [Multiset.map_cons, Multiset.prod_cons]
  exact (ht _ (Multiset.mem_cons_self _ _)).mul (ih fun _ hi => ht _ (Multiset.mem_cons_of_mem hi))

theorem monic_prod_of_monic (s : Finset ι) (f : ι → R[X]) (hs : ∀, ∀ i ∈ s, ∀, Monic (f i)) : Monic (∏ i in s, f i) :=
  monic_multiset_prod_of_monic s.1 f hs

theorem is_unit_C {x : R} : IsUnit (c x) ↔ IsUnit x := by
  rw [is_unit_iff_dvd_one, is_unit_iff_dvd_one]
  constructor
  · rintro ⟨g, hg⟩
    replace hg := congr_arg (eval 0) hg
    rw [eval_one, eval_mul, eval_C] at hg
    exact ⟨g.eval 0, hg⟩
    
  · rintro ⟨y, hy⟩
    exact
      ⟨C y, by
        rw [← C_mul, ← hy, C_1]⟩
    

theorem eq_one_of_is_unit_of_monic (hm : Monic p) (hpu : IsUnit p) : p = 1 := by
  have : degree p ≤ 0 :=
    calc
      degree p ≤ degree (1 : R[X]) :=
        let ⟨u, hu⟩ := is_unit_iff_dvd_one.1 hpu
        if hu0 : u = 0 then by
          rw [hu0, mul_zero] at hu
          rw [← mul_oneₓ p, hu, mul_zero]
          simp
        else by
          have : p.leadingCoeff * u.leadingCoeff ≠ 0 := by
            rw [hm.leading_coeff, one_mulₓ, Ne.def, leading_coeff_eq_zero] <;> exact hu0
          rw [hu, degree_mul' this] <;> exact le_add_of_nonneg_right (degree_nonneg_iff_ne_zero.2 hu0)
      _ ≤ 0 := degree_one_le
      
  rw [eq_C_of_degree_le_zero this, ← nat_degree_eq_zero_iff_degree_le_zero.2 this, ← leading_coeff, hm.leading_coeff,
    C_1]

theorem Monic.next_coeff_multiset_prod (t : Multiset ι) (f : ι → R[X]) (h : ∀, ∀ i ∈ t, ∀, Monic (f i)) :
    nextCoeff (t.map f).Prod = (t.map fun i => nextCoeff (f i)).Sum := by
  revert h
  refine' Multiset.induction_on t _ fun a t ih ht => _
  · simp only [← Multiset.not_mem_zero, ← forall_prop_of_true, ← forall_prop_of_false, ← Multiset.map_zero, ←
      Multiset.prod_zero, ← Multiset.sum_zero, ← not_false_iff, ← forall_true_iff]
    rw [← C_1]
    rw [next_coeff_C_eq_zero]
    
  · rw [Multiset.map_cons, Multiset.prod_cons, Multiset.map_cons, Multiset.sum_cons, monic.next_coeff_mul, ih]
    exacts[fun i hi => ht i (Multiset.mem_cons_of_mem hi), ht a (Multiset.mem_cons_self _ _),
      monic_multiset_prod_of_monic _ _ fun b bs => ht _ (Multiset.mem_cons_of_mem bs)]
    

theorem Monic.next_coeff_prod (s : Finset ι) (f : ι → R[X]) (h : ∀, ∀ i ∈ s, ∀, Monic (f i)) :
    nextCoeff (∏ i in s, f i) = ∑ i in s, nextCoeff (f i) :=
  Monic.next_coeff_multiset_prod s.1 f h

end CommSemiringₓ

section Semiringₓ

variable [Semiringₓ R]

@[simp]
theorem Monic.nat_degree_map [Semiringₓ S] [Nontrivial S] {P : Polynomial R} (hmo : P.Monic) (f : R →+* S) :
    (P.map f).natDegree = P.natDegree := by
  refine' le_antisymmₓ (nat_degree_map_le _ _) (le_nat_degree_of_ne_zero _)
  rw [coeff_map, monic.coeff_nat_degree hmo, RingHom.map_one]
  exact one_ne_zero

@[simp]
theorem Monic.degree_map [Semiringₓ S] [Nontrivial S] {P : Polynomial R} (hmo : P.Monic) (f : R →+* S) :
    (P.map f).degree = P.degree := by
  by_cases' hP : P = 0
  · simp [← hP]
    
  · refine' le_antisymmₓ (degree_map_le _ _) _
    rw [degree_eq_nat_degree hP]
    refine' le_degree_of_ne_zero _
    rw [coeff_map, monic.coeff_nat_degree hmo, RingHom.map_one]
    exact one_ne_zero
    

section Injective

open Function

variable [Semiringₓ S] {f : R →+* S} (hf : Injective f)

include hf

theorem degree_map_eq_of_injective (p : R[X]) : degree (p.map f) = degree p :=
  if h : p = 0 then by
    simp [← h]
  else
    degree_map_eq_of_leading_coeff_ne_zero _
      (by
        rw [← f.map_zero] <;> exact mt hf.eq_iff.1 (mt leading_coeff_eq_zero.1 h))

theorem nat_degree_map_eq_of_injective (p : R[X]) : natDegree (p.map f) = natDegree p :=
  nat_degree_eq_of_degree_eq (degree_map_eq_of_injective hf p)

theorem leading_coeff_map' (p : R[X]) : leadingCoeff (p.map f) = f (leadingCoeff p) := by
  unfold leading_coeff
  rw [coeff_map, nat_degree_map_eq_of_injective hf p]

theorem next_coeff_map (p : R[X]) : (p.map f).nextCoeff = f p.nextCoeff := by
  unfold next_coeff
  rw [nat_degree_map_eq_of_injective hf]
  split_ifs <;> simp

theorem leading_coeff_of_injective (p : R[X]) : leadingCoeff (p.map f) = f (leadingCoeff p) := by
  delta' leading_coeff
  rw [coeff_map f, nat_degree_map_eq_of_injective hf p]

theorem monic_of_injective {p : R[X]} (hp : (p.map f).Monic) : p.Monic := by
  apply hf
  rw [← leading_coeff_of_injective hf, hp.leading_coeff, f.map_one]

end Injective

end Semiringₓ

section Ringₓ

variable [Ringₓ R] {p : R[X]}

theorem monic_X_sub_C (x : R) : Monic (X - c x) := by
  simpa only [← sub_eq_add_neg, ← C_neg] using monic_X_add_C (-x)

theorem monic_X_pow_sub {n : ℕ} (H : degree p ≤ n) : Monic (X ^ (n + 1) - p) := by
  simpa [← sub_eq_add_neg] using
    monic_X_pow_add
      (show degree (-p) ≤ n by
        rwa [← degree_neg p] at H)

/-- `X ^ n - a` is monic. -/
theorem monic_X_pow_sub_C {R : Type u} [Ringₓ R] (a : R) {n : ℕ} (h : n ≠ 0) : (X ^ n - c a).Monic := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero h
  convert monic_X_pow_sub _
  exact le_transₓ degree_C_le Nat.WithBot.coe_nonneg

theorem not_is_unit_X_pow_sub_one (R : Type _) [CommRingₓ R] [Nontrivial R] (n : ℕ) : ¬IsUnit (X ^ n - 1 : R[X]) := by
  intro h
  rcases eq_or_ne n 0 with (rfl | hn)
  · simpa using h
    
  apply hn
  rwa [← @nat_degree_X_pow_sub_C _ _ _ n (1 : R), eq_one_of_is_unit_of_monic (monic_X_pow_sub_C (1 : R) hn),
    nat_degree_one]

theorem Monic.sub_of_left {p q : R[X]} (hp : Monic p) (hpq : degree q < degree p) : Monic (p - q) := by
  rw [sub_eq_add_neg]
  apply hp.add_of_left
  rwa [degree_neg]

theorem Monic.sub_of_right {p q : R[X]} (hq : q.leadingCoeff = -1) (hpq : degree p < degree q) : Monic (p - q) := by
  have : (-q).coeff (-q).natDegree = 1 := by
    rw [nat_degree_neg, coeff_neg, show q.coeff q.nat_degree = -1 from hq, neg_negₓ]
  rw [sub_eq_add_neg]
  apply monic.add_of_right this
  rwa [degree_neg]

end Ringₓ

section NonzeroSemiring

variable [Semiringₓ R] [Nontrivial R] {p q : R[X]}

@[simp]
theorem not_monic_zero : ¬Monic (0 : R[X]) := by
  simpa only [← monic, ← leading_coeff_zero] using (zero_ne_one : (0 : R) ≠ 1)

end NonzeroSemiring

section NotZeroDivisor

-- TODO: using gh-8537, rephrase lemmas that involve commutation around `*` using the op-ring
variable [Semiringₓ R] {p : R[X]}

theorem Monic.mul_left_ne_zero (hp : Monic p) {q : R[X]} (hq : q ≠ 0) : q * p ≠ 0 := by
  by_cases' h : p = 1
  · simpa [← h]
    
  rw [Ne.def, ← degree_eq_bot, hp.degree_mul, WithBot.add_eq_bot, not_or_distrib, degree_eq_bot]
  refine' ⟨hq, _⟩
  rw [← hp.degree_le_zero_iff_eq_one, not_leₓ] at h
  refine' (lt_transₓ _ h).ne'
  simp

theorem Monic.mul_right_ne_zero (hp : Monic p) {q : R[X]} (hq : q ≠ 0) : p * q ≠ 0 := by
  by_cases' h : p = 1
  · simpa [← h]
    
  rw [Ne.def, ← degree_eq_bot, hp.degree_mul_comm, hp.degree_mul, WithBot.add_eq_bot, not_or_distrib, degree_eq_bot]
  refine' ⟨hq, _⟩
  rw [← hp.degree_le_zero_iff_eq_one, not_leₓ] at h
  refine' (lt_transₓ _ h).ne'
  simp

theorem Monic.mul_nat_degree_lt_iff (h : Monic p) {q : R[X]} : (p * q).natDegree < p.natDegree ↔ p ≠ 1 ∧ q = 0 := by
  by_cases' hq : q = 0
  · suffices 0 < p.nat_degree ↔ p.nat_degree ≠ 0 by
      simpa [← hq, h.nat_degree_eq_zero_iff_eq_one]
    exact ⟨fun h => h.ne', fun h => lt_of_le_of_neₓ (Nat.zero_leₓ _) h.symm⟩
    
  · simp [← h.nat_degree_mul', ← hq]
    

theorem Monic.mul_right_eq_zero_iff (h : Monic p) {q : R[X]} : p * q = 0 ↔ q = 0 := by
  by_cases' hq : q = 0 <;> simp [← h.mul_right_ne_zero, ← hq]

theorem Monic.mul_left_eq_zero_iff (h : Monic p) {q : R[X]} : q * p = 0 ↔ q = 0 := by
  by_cases' hq : q = 0 <;> simp [← h.mul_left_ne_zero, ← hq]

theorem Monic.is_regular {R : Type _} [Ringₓ R] {p : R[X]} (hp : Monic p) : IsRegular p := by
  constructor
  · intro q r h
    rw [← sub_eq_zero, ← hp.mul_right_eq_zero_iff, mul_sub, h, sub_self]
    
  · intro q r h
    simp only at h
    rw [← sub_eq_zero, ← hp.mul_left_eq_zero_iff, sub_mul, h, sub_self]
    

theorem degree_smul_of_smul_regular {S : Type _} [Monoidₓ S] [DistribMulAction S R] {k : S} (p : R[X])
    (h : IsSmulRegular R k) : (k • p).degree = p.degree := by
  refine' le_antisymmₓ _ _
  · rw [degree_le_iff_coeff_zero]
    intro m hm
    rw [degree_lt_iff_coeff_zero] at hm
    simp [← hm m le_rfl]
    
  · rw [degree_le_iff_coeff_zero]
    intro m hm
    rw [degree_lt_iff_coeff_zero] at hm
    refine' h _
    simpa using hm m le_rfl
    

theorem nat_degree_smul_of_smul_regular {S : Type _} [Monoidₓ S] [DistribMulAction S R] {k : S} (p : R[X])
    (h : IsSmulRegular R k) : (k • p).natDegree = p.natDegree := by
  by_cases' hp : p = 0
  · simp [← hp]
    
  rw [← WithBot.coe_eq_coe, ← degree_eq_nat_degree hp, ← degree_eq_nat_degree, degree_smul_of_smul_regular p h]
  contrapose! hp
  rw [← smul_zero k] at hp
  exact h.polynomial hp

theorem leading_coeff_smul_of_smul_regular {S : Type _} [Monoidₓ S] [DistribMulAction S R] {k : S} (p : R[X])
    (h : IsSmulRegular R k) : (k • p).leadingCoeff = k • p.leadingCoeff := by
  rw [leading_coeff, leading_coeff, coeff_smul, nat_degree_smul_of_smul_regular p h]

theorem monic_of_is_unit_leading_coeff_inv_smul (h : IsUnit p.leadingCoeff) : Monic (h.Unit⁻¹ • p) := by
  rw [monic.def, leading_coeff_smul_of_smul_regular _ (is_smul_regular_of_group _), Units.smul_def]
  obtain ⟨k, hk⟩ := h
  simp only [hk, ← smul_eq_mul, Units.coe_mul, ← Units.coe_eq_one, ← inv_mul_eq_iff_eq_mul]
  simp [← Units.ext_iff, ← IsUnit.unit_spec]

theorem is_unit_leading_coeff_mul_right_eq_zero_iff (h : IsUnit p.leadingCoeff) {q : R[X]} : p * q = 0 ↔ q = 0 := by
  constructor
  · intro hp
    rw [← smul_eq_zero_iff_eq h.unit⁻¹] at hp
    have : h.unit⁻¹ • (p * q) = h.unit⁻¹ • p * q := by
      ext
      simp only [← Units.smul_def, ← coeff_smul, ← coeff_mul, ← smul_eq_mul, ← mul_sum]
      refine' sum_congr rfl fun x hx => _
      rw [← mul_assoc]
    rwa [this, monic.mul_right_eq_zero_iff] at hp
    exact monic_of_is_unit_leading_coeff_inv_smul _
    
  · rintro rfl
    simp
    

theorem is_unit_leading_coeff_mul_left_eq_zero_iff (h : IsUnit p.leadingCoeff) {q : R[X]} : q * p = 0 ↔ q = 0 := by
  constructor
  · intro hp
    replace hp := congr_arg (· * C ↑h.unit⁻¹) hp
    simp only [← zero_mul] at hp
    rwa [mul_assoc, monic.mul_left_eq_zero_iff] at hp
    refine' monic_mul_C_of_leading_coeff_mul_eq_one _
    simp [← Units.mul_inv_eq_iff_eq_mul, ← IsUnit.unit_spec]
    
  · rintro rfl
    rw [zero_mul]
    

end NotZeroDivisor

end Polynomial

