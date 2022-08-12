/-
Copyright (c) 2020 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
import Mathbin.Algebra.Polynomial.BigOperators
import Mathbin.Analysis.Complex.RootsOfUnity
import Mathbin.Data.Polynomial.Lifts
import Mathbin.FieldTheory.Separable
import Mathbin.FieldTheory.SplittingField
import Mathbin.NumberTheory.ArithmeticFunction
import Mathbin.RingTheory.RootsOfUnity
import Mathbin.FieldTheory.Ratfunc
import Mathbin.Algebra.NeZero

/-!
# Cyclotomic polynomials.

For `n : ℕ` and an integral domain `R`, we define a modified version of the `n`-th cyclotomic
polynomial with coefficients in `R`, denoted `cyclotomic' n R`, as `∏ (X - μ)`, where `μ` varies
over the primitive `n`th roots of unity. If there is a primitive `n`th root of unity in `R` then
this the standard definition. We then define the standard cyclotomic polynomial `cyclotomic n R`
with coefficients in any ring `R`.

## Main definition

* `cyclotomic n R` : the `n`-th cyclotomic polynomial with coefficients in `R`.

## Main results

* `int_coeff_of_cycl` : If there is a primitive `n`-th root of unity in `K`, then `cyclotomic' n K`
comes from a polynomial with integer coefficients.
* `deg_of_cyclotomic` : The degree of `cyclotomic n` is `totient n`.
* `prod_cyclotomic_eq_X_pow_sub_one` : `X ^ n - 1 = ∏ (cyclotomic i)`, where `i` divides `n`.
* `cyclotomic_eq_prod_X_pow_sub_one_pow_moebius` : The Möbius inversion formula for
  `cyclotomic n R` over an abstract fraction field for `polynomial R`.
* `cyclotomic.irreducible` : `cyclotomic n ℤ` is irreducible.

## Implementation details

Our definition of `cyclotomic' n R` makes sense in any integral domain `R`, but the interesting
results hold if there is a primitive `n`-th root of unity in `R`. In particular, our definition is
not the standard one unless there is a primitive `n`th root of unity in `R`. For example,
`cyclotomic' 3 ℤ = 1`, since there are no primitive cube roots of unity in `ℤ`. The main example is
`R = ℂ`, we decided to work in general since the difficulties are essentially the same.
To get the standard cyclotomic polynomials, we use `int_coeff_of_cycl`, with `R = ℂ`, to get a
polynomial with integer coefficients and then we map it to `polynomial R`, for any ring `R`.
To prove `cyclotomic.irreducible`, the irreducibility of `cyclotomic n ℤ`, we show in
`cyclotomic_eq_minpoly` that `cyclotomic n ℤ` is the minimal polynomial of any `n`-th primitive root
of unity `μ : K`, where `K` is a field of characteristic `0`.
-/


open Classical BigOperators Polynomial

noncomputable section

universe u

namespace Polynomial

section Cyclotomic'

section IsDomain

variable {R : Type _} [CommRingₓ R] [IsDomain R]

/-- The modified `n`-th cyclotomic polynomial with coefficients in `R`, it is the usual cyclotomic
polynomial if there is a primitive `n`-th root of unity in `R`. -/
def cyclotomic' (n : ℕ) (R : Type _) [CommRingₓ R] [IsDomain R] : R[X] :=
  ∏ μ in primitiveRoots n R, X - c μ

/-- The zeroth modified cyclotomic polyomial is `1`. -/
@[simp]
theorem cyclotomic'_zero (R : Type _) [CommRingₓ R] [IsDomain R] : cyclotomic' 0 R = 1 := by
  simp only [← cyclotomic', ← Finset.prod_empty, ← IsPrimitiveRoot.primitive_roots_zero]

/-- The first modified cyclotomic polyomial is `X - 1`. -/
@[simp]
theorem cyclotomic'_one (R : Type _) [CommRingₓ R] [IsDomain R] : cyclotomic' 1 R = X - 1 := by
  simp only [← cyclotomic', ← Finset.prod_singleton, ← RingHom.map_one, ← IsPrimitiveRoot.primitive_roots_one]

/-- The second modified cyclotomic polyomial is `X + 1` if the characteristic of `R` is not `2`. -/
@[simp]
theorem cyclotomic'_two (R : Type _) [CommRingₓ R] [IsDomain R] (p : ℕ) [CharP R p] (hp : p ≠ 2) :
    cyclotomic' 2 R = X + 1 := by
  rw [cyclotomic']
  have prim_root_two : primitiveRoots 2 R = {(-1 : R)} := by
    apply Finset.eq_singleton_iff_unique_mem.2
    constructor
    · simp only [← IsPrimitiveRoot.neg_one p hp, ← Nat.succ_pos', ← mem_primitive_roots]
      
    · intro x hx
      rw [mem_primitive_roots zero_lt_two] at hx
      exact IsPrimitiveRoot.eq_neg_one_of_two_right hx
      
  simp only [← prim_root_two, ← Finset.prod_singleton, ← RingHom.map_neg, ← RingHom.map_one, ← sub_neg_eq_add]

/-- `cyclotomic' n R` is monic. -/
theorem cyclotomic'.monic (n : ℕ) (R : Type _) [CommRingₓ R] [IsDomain R] : (cyclotomic' n R).Monic :=
  (monic_prod_of_monic _ _) fun z hz => monic_X_sub_C _

/-- `cyclotomic' n R` is different from `0`. -/
theorem cyclotomic'_ne_zero (n : ℕ) (R : Type _) [CommRingₓ R] [IsDomain R] : cyclotomic' n R ≠ 0 :=
  (cyclotomic'.monic n R).ne_zero

/-- The natural degree of `cyclotomic' n R` is `totient n` if there is a primitive root of
unity in `R`. -/
theorem nat_degree_cyclotomic' {ζ : R} {n : ℕ} (h : IsPrimitiveRoot ζ n) :
    (cyclotomic' n R).natDegree = Nat.totient n := by
  rw [cyclotomic']
  rw [nat_degree_prod (primitiveRoots n R) fun z : R => X - C z]
  simp only [← IsPrimitiveRoot.card_primitive_roots h, ← mul_oneₓ, ← nat_degree_X_sub_C, ← Nat.cast_id, ←
    Finset.sum_const, ← nsmul_eq_mul]
  intro z hz
  exact X_sub_C_ne_zero z

/-- The degree of `cyclotomic' n R` is `totient n` if there is a primitive root of unity in `R`. -/
theorem degree_cyclotomic' {ζ : R} {n : ℕ} (h : IsPrimitiveRoot ζ n) : (cyclotomic' n R).degree = Nat.totient n := by
  simp only [← degree_eq_nat_degree (cyclotomic'_ne_zero n R), ← nat_degree_cyclotomic' h]

/-- The roots of `cyclotomic' n R` are the primitive `n`-th roots of unity. -/
theorem roots_of_cyclotomic (n : ℕ) (R : Type _) [CommRingₓ R] [IsDomain R] :
    (cyclotomic' n R).roots = (primitiveRoots n R).val := by
  rw [cyclotomic']
  exact roots_prod_X_sub_C (primitiveRoots n R)

/-- If there is a primitive `n`th root of unity in `K`, then `X ^ n - 1 = ∏ (X - μ)`, where `μ`
varies over the `n`-th roots of unity. -/
theorem X_pow_sub_one_eq_prod {ζ : R} {n : ℕ} (hpos : 0 < n) (h : IsPrimitiveRoot ζ n) :
    X ^ n - 1 = ∏ ζ in nthRootsFinset n R, X - c ζ := by
  rw [nth_roots_finset, ← Multiset.to_finset_eq (IsPrimitiveRoot.nth_roots_nodup h)]
  simp only [← Finset.prod_mk, ← RingHom.map_one]
  rw [nth_roots]
  have hmonic : (X ^ n - C (1 : R)).Monic := monic_X_pow_sub_C (1 : R) (ne_of_ltₓ hpos).symm
  symm
  apply prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmonic
  rw [@nat_degree_X_pow_sub_C R _ _ n 1, ← nth_roots]
  exact IsPrimitiveRoot.card_nth_roots h

end IsDomain

section Field

variable {K : Type _} [Field K]

/-- `cyclotomic' n K` splits. -/
theorem cyclotomic'_splits (n : ℕ) : Splits (RingHom.id K) (cyclotomic' n K) := by
  apply splits_prod (RingHom.id K)
  intro z hz
  simp only [← splits_X_sub_C (RingHom.id K)]

/-- If there is a primitive `n`-th root of unity in `K`, then `X ^ n - 1`splits. -/
theorem X_pow_sub_one_splits {ζ : K} {n : ℕ} (h : IsPrimitiveRoot ζ n) : Splits (RingHom.id K) (X ^ n - c (1 : K)) := by
  rw [splits_iff_card_roots, ← nth_roots, IsPrimitiveRoot.card_nth_roots h, nat_degree_X_pow_sub_C]

/-- If there is a primitive `n`-th root of unity in `K`, then
`∏ i in nat.divisors n, cyclotomic' i K = X ^ n - 1`. -/
theorem prod_cyclotomic'_eq_X_pow_sub_one {K : Type _} [CommRingₓ K] [IsDomain K] {ζ : K} {n : ℕ} (hpos : 0 < n)
    (h : IsPrimitiveRoot ζ n) : (∏ i in Nat.divisors n, cyclotomic' i K) = X ^ n - 1 := by
  rw [X_pow_sub_one_eq_prod hpos h]
  have rwcyc : ∀, ∀ i ∈ Nat.divisors n, ∀, cyclotomic' i K = ∏ μ in primitiveRoots i K, X - C μ := by
    intro i hi
    simp only [← cyclotomic']
  conv_lhs => apply_congr skip simp [← rwcyc, ← H]
  rw [← Finset.prod_bUnion]
  · simp only [← IsPrimitiveRoot.nth_roots_one_eq_bUnion_primitive_roots h]
    
  intro x hx y hy hdiff
  exact IsPrimitiveRoot.disjoint hdiff

/-- If there is a primitive `n`-th root of unity in `K`, then
`cyclotomic' n K = (X ^ k - 1) /ₘ (∏ i in nat.proper_divisors k, cyclotomic' i K)`. -/
theorem cyclotomic'_eq_X_pow_sub_one_div {K : Type _} [CommRingₓ K] [IsDomain K] {ζ : K} {n : ℕ} (hpos : 0 < n)
    (h : IsPrimitiveRoot ζ n) : cyclotomic' n K = (X ^ n - 1) /ₘ ∏ i in Nat.properDivisors n, cyclotomic' i K := by
  rw [← prod_cyclotomic'_eq_X_pow_sub_one hpos h, Nat.divisors_eq_proper_divisors_insert_self_of_pos hpos,
    Finset.prod_insert Nat.properDivisors.not_self_mem]
  have prod_monic : (∏ i in Nat.properDivisors n, cyclotomic' i K).Monic := by
    apply monic_prod_of_monic
    intro i hi
    exact cyclotomic'.monic i K
  rw [(div_mod_by_monic_unique (cyclotomic' n K) 0 prod_monic _).1]
  simp only [← degree_zero, ← zero_addₓ]
  refine'
    ⟨by
      rw [mul_comm], _⟩
  rw [bot_lt_iff_ne_bot]
  intro h
  exact monic.ne_zero prod_monic (degree_eq_bot.1 h)

/-- If there is a primitive `n`-th root of unity in `K`, then `cyclotomic' n K` comes from a
monic polynomial with integer coefficients. -/
theorem int_coeff_of_cyclotomic' {K : Type _} [CommRingₓ K] [IsDomain K] {ζ : K} {n : ℕ} (h : IsPrimitiveRoot ζ n) :
    ∃ P : ℤ[X], map (Int.castRingHom K) P = cyclotomic' n K ∧ P.degree = (cyclotomic' n K).degree ∧ P.Monic := by
  refine' lifts_and_degree_eq_and_monic _ (cyclotomic'.monic n K)
  induction' n using Nat.strong_induction_onₓ with k hk generalizing ζ h
  cases' Nat.eq_zero_or_posₓ k with hzero hpos
  · use 1
    simp only [← hzero, ← cyclotomic'_zero, ← Set.mem_univ, ← Subsemiring.coe_top, ← eq_self_iff_true, ←
      coe_map_ring_hom, ← Polynomial.map_one, ← and_selfₓ]
    
  let B : K[X] := ∏ i in Nat.properDivisors k, cyclotomic' i K
  have Bmo : B.monic := by
    apply monic_prod_of_monic
    intro i hi
    exact cyclotomic'.monic i K
  have Bint : B ∈ lifts (Int.castRingHom K) := by
    refine' Subsemiring.prod_mem (lifts (Int.castRingHom K)) _
    intro x hx
    have xsmall := (Nat.mem_proper_divisors.1 hx).2
    obtain ⟨d, hd⟩ := (Nat.mem_proper_divisors.1 hx).1
    rw [mul_comm] at hd
    exact hk x xsmall (IsPrimitiveRoot.pow hpos h hd)
  replace Bint := lifts_and_degree_eq_and_monic Bint Bmo
  obtain ⟨B₁, hB₁, hB₁deg, hB₁mo⟩ := Bint
  let Q₁ : ℤ[X] := (X ^ k - 1) /ₘ B₁
  have huniq : 0 + B * cyclotomic' k K = X ^ k - 1 ∧ (0 : K[X]).degree < B.degree := by
    constructor
    · rw [zero_addₓ, mul_comm, ← prod_cyclotomic'_eq_X_pow_sub_one hpos h,
        Nat.divisors_eq_proper_divisors_insert_self_of_pos hpos]
      simp only [← true_andₓ, ← Finset.prod_insert, ← not_ltₓ, ← Nat.mem_proper_divisors, ← dvd_refl]
      
    rw [degree_zero, bot_lt_iff_ne_bot]
    intro habs
    exact (monic.ne_zero Bmo) (degree_eq_bot.1 habs)
  replace huniq := div_mod_by_monic_unique (cyclotomic' k K) (0 : K[X]) Bmo huniq
  simp only [← lifts, ← RingHom.mem_srange]
  use Q₁
  rw [coe_map_ring_hom, map_div_by_monic (Int.castRingHom K) hB₁mo, hB₁, ← huniq.1]
  simp

/-- If `K` is of characteristic `0` and there is a primitive `n`-th root of unity in `K`,
then `cyclotomic n K` comes from a unique polynomial with integer coefficients. -/
theorem unique_int_coeff_of_cycl {K : Type _} [CommRingₓ K] [IsDomain K] [CharZero K] {ζ : K} {n : ℕ+}
    (h : IsPrimitiveRoot ζ n) : ∃! P : ℤ[X], map (Int.castRingHom K) P = cyclotomic' n K := by
  obtain ⟨P, hP⟩ := int_coeff_of_cyclotomic' h
  refine' ⟨P, hP.1, fun Q hQ => _⟩
  apply map_injective (Int.castRingHom K) Int.cast_injective
  rw [hP.1, hQ]

end Field

end Cyclotomic'

section Cyclotomic

/-- The `n`-th cyclotomic polynomial with coefficients in `R`. -/
def cyclotomic (n : ℕ) (R : Type _) [Ringₓ R] : R[X] :=
  if h : n = 0 then 1 else map (Int.castRingHom R) (int_coeff_of_cyclotomic' (Complex.is_primitive_root_exp n h)).some

theorem int_cyclotomic_rw {n : ℕ} (h : n ≠ 0) :
    cyclotomic n ℤ = (int_coeff_of_cyclotomic' (Complex.is_primitive_root_exp n h)).some := by
  simp only [← cyclotomic, ← h, ← dif_neg, ← not_false_iff]
  ext i
  simp only [← coeff_map, ← Int.cast_id, ← RingHom.eq_int_cast]

/-- `cyclotomic n R` comes from `cyclotomic n ℤ`. -/
theorem map_cyclotomic_int (n : ℕ) (R : Type _) [Ringₓ R] : map (Int.castRingHom R) (cyclotomic n ℤ) = cyclotomic n R :=
  by
  by_cases' hzero : n = 0
  · simp only [← hzero, ← cyclotomic, ← dif_pos, ← Polynomial.map_one]
    
  simp only [← cyclotomic, ← int_cyclotomic_rw, ← hzero, ← Ne.def, ← dif_neg, ← not_false_iff]

theorem int_cyclotomic_spec (n : ℕ) :
    map (Int.castRingHom ℂ) (cyclotomic n ℤ) = cyclotomic' n ℂ ∧
      (cyclotomic n ℤ).degree = (cyclotomic' n ℂ).degree ∧ (cyclotomic n ℤ).Monic :=
  by
  by_cases' hzero : n = 0
  · simp only [← hzero, ← cyclotomic, ← degree_one, ← monic_one, ← cyclotomic'_zero, ← dif_pos, ← eq_self_iff_true, ←
      Polynomial.map_one, ← and_selfₓ]
    
  rw [int_cyclotomic_rw hzero]
  exact (int_coeff_of_cyclotomic' (Complex.is_primitive_root_exp n hzero)).some_spec

theorem int_cyclotomic_unique {n : ℕ} {P : ℤ[X]} (h : map (Int.castRingHom ℂ) P = cyclotomic' n ℂ) :
    P = cyclotomic n ℤ := by
  apply map_injective (Int.castRingHom ℂ) Int.cast_injective
  rw [h, (int_cyclotomic_spec n).1]

/-- The definition of `cyclotomic n R` commutes with any ring homomorphism. -/
@[simp]
theorem map_cyclotomic (n : ℕ) {R S : Type _} [Ringₓ R] [Ringₓ S] (f : R →+* S) :
    map f (cyclotomic n R) = cyclotomic n S := by
  rw [← map_cyclotomic_int n R, ← map_cyclotomic_int n S]
  ext i
  simp only [← coeff_map, ← RingHom.eq_int_cast, ← RingHom.map_int_cast]

theorem cyclotomic.eval_apply {R S : Type _} (q : R) (n : ℕ) [Ringₓ R] [Ringₓ S] (f : R →+* S) :
    eval (f q) (cyclotomic n S) = f (eval q (cyclotomic n R)) := by
  rw [← map_cyclotomic n f, eval_map, eval₂_at_apply]

/-- The zeroth cyclotomic polyomial is `1`. -/
@[simp]
theorem cyclotomic_zero (R : Type _) [Ringₓ R] : cyclotomic 0 R = 1 := by
  simp only [← cyclotomic, ← dif_pos]

/-- The first cyclotomic polyomial is `X - 1`. -/
@[simp]
theorem cyclotomic_one (R : Type _) [Ringₓ R] : cyclotomic 1 R = X - 1 := by
  have hspec : map (Int.castRingHom ℂ) (X - 1) = cyclotomic' 1 ℂ := by
    simp only [← cyclotomic'_one, ← Pnat.one_coe, ← map_X, ← Polynomial.map_one, ← Polynomial.map_sub]
  symm
  rw [← map_cyclotomic_int, ← int_cyclotomic_unique hspec]
  simp only [← map_X, ← Polynomial.map_one, ← Polynomial.map_sub]

/-- The second cyclotomic polyomial is `X + 1`. -/
@[simp]
theorem cyclotomic_two (R : Type _) [Ringₓ R] : cyclotomic 2 R = X + 1 := by
  have hspec : map (Int.castRingHom ℂ) (X + 1) = cyclotomic' 2 ℂ := by
    simp only [← cyclotomic'_two ℂ 0 two_ne_zero.symm, ← Polynomial.map_add, ← map_X, ← Polynomial.map_one]
  symm
  rw [← map_cyclotomic_int, ← int_cyclotomic_unique hspec]
  simp only [← Polynomial.map_add, ← map_X, ← Polynomial.map_one]

/-- `cyclotomic n` is monic. -/
theorem cyclotomic.monic (n : ℕ) (R : Type _) [Ringₓ R] : (cyclotomic n R).Monic := by
  rw [← map_cyclotomic_int]
  exact (int_cyclotomic_spec n).2.2.map _

/-- `cyclotomic n` is primitive. -/
theorem cyclotomic.is_primitive (n : ℕ) (R : Type _) [CommRingₓ R] : (cyclotomic n R).IsPrimitive :=
  (cyclotomic.monic n R).IsPrimitive

/-- `cyclotomic n R` is different from `0`. -/
theorem cyclotomic_ne_zero (n : ℕ) (R : Type _) [Ringₓ R] [Nontrivial R] : cyclotomic n R ≠ 0 :=
  (cyclotomic.monic n R).ne_zero

/-- The degree of `cyclotomic n` is `totient n`. -/
theorem degree_cyclotomic (n : ℕ) (R : Type _) [Ringₓ R] [Nontrivial R] : (cyclotomic n R).degree = Nat.totient n := by
  rw [← map_cyclotomic_int]
  rw [degree_map_eq_of_leading_coeff_ne_zero (Int.castRingHom R) _]
  · cases' n with k
    · simp only [← cyclotomic, ← degree_one, ← dif_pos, ← Nat.totient_zero, ← WithTop.coe_zero]
      
    rw [← degree_cyclotomic' (Complex.is_primitive_root_exp k.succ (Nat.succ_ne_zero k))]
    exact (int_cyclotomic_spec k.succ).2.1
    
  simp only [← (int_cyclotomic_spec n).right.right, ← RingHom.eq_int_cast, ← monic.leading_coeff, ← Int.cast_oneₓ, ←
    Ne.def, ← not_false_iff, ← one_ne_zero]

/-- The natural degree of `cyclotomic n` is `totient n`. -/
theorem nat_degree_cyclotomic (n : ℕ) (R : Type _) [Ringₓ R] [Nontrivial R] :
    (cyclotomic n R).natDegree = Nat.totient n := by
  have hdeg := degree_cyclotomic n R
  rw [degree_eq_nat_degree (cyclotomic_ne_zero n R)] at hdeg
  exact_mod_cast hdeg

/-- The degree of `cyclotomic n R` is positive. -/
theorem degree_cyclotomic_pos (n : ℕ) (R : Type _) (hpos : 0 < n) [Ringₓ R] [Nontrivial R] :
    0 < (cyclotomic n R).degree := by
  rw [degree_cyclotomic n R]
  exact_mod_cast Nat.totient_pos hpos

/-- `∏ i in nat.divisors n, cyclotomic i R = X ^ n - 1`. -/
theorem prod_cyclotomic_eq_X_pow_sub_one {n : ℕ} (hpos : 0 < n) (R : Type _) [CommRingₓ R] :
    (∏ i in Nat.divisors n, cyclotomic i R) = X ^ n - 1 := by
  have integer : (∏ i in Nat.divisors n, cyclotomic i ℤ) = X ^ n - 1 := by
    apply map_injective (Int.castRingHom ℂ) Int.cast_injective
    rw [Polynomial.map_prod (Int.castRingHom ℂ) fun i => cyclotomic i ℤ]
    simp only [← int_cyclotomic_spec, ← Polynomial.map_pow, ← Nat.cast_id, ← map_X, ← Polynomial.map_one, ←
      Polynomial.map_sub]
    exact prod_cyclotomic'_eq_X_pow_sub_one hpos (Complex.is_primitive_root_exp n (ne_of_ltₓ hpos).symm)
  have coerc : X ^ n - 1 = map (Int.castRingHom R) (X ^ n - 1) := by
    simp only [← Polynomial.map_pow, ← Polynomial.map_X, ← Polynomial.map_one, ← Polynomial.map_sub]
  have h : ∀, ∀ i ∈ n.divisors, ∀, cyclotomic i R = map (Int.castRingHom R) (cyclotomic i ℤ) := by
    intro i hi
    exact (map_cyclotomic_int i R).symm
  rw [Finset.prod_congr (refl n.divisors) h, coerc, ← Polynomial.map_prod (Int.castRingHom R) fun i => cyclotomic i ℤ,
    integer]

theorem cyclotomic.dvd_X_pow_sub_one (n : ℕ) (R : Type _) [CommRingₓ R] : cyclotomic n R ∣ X ^ n - 1 := by
  rcases n.eq_zero_or_pos with (rfl | hn)
  · simp
    
  refine' ⟨∏ i in n.proper_divisors, cyclotomic i R, _⟩
  rw [← prod_cyclotomic_eq_X_pow_sub_one hn, Nat.divisors_eq_proper_divisors_insert_self_of_pos hn, Finset.prod_insert]
  exact Nat.properDivisors.not_self_mem

open BigOperators

open Finset

theorem prod_cyclotomic_eq_geom_sum {n : ℕ} (h : 0 < n) (R) [CommRingₓ R] [IsDomain R] :
    (∏ i in n.divisors \ {1}, cyclotomic i R) = ∑ i in range n, X ^ i := by
  apply_fun (· * cyclotomic 1 R) using mul_left_injective₀ (cyclotomic_ne_zero 1 R)
  have : (∏ i in {1}, cyclotomic i R) = cyclotomic 1 R := Finset.prod_singleton
  simp_rw [← this,
    Finset.prod_sdiff <|
      show {1} ⊆ n.divisors by
        simp [← h.ne'],
    this, cyclotomic_one, geom_sum_mul, prod_cyclotomic_eq_X_pow_sub_one h]

theorem cyclotomic_dvd_geom_sum_of_dvd (R) [CommRingₓ R] {d n : ℕ} (hdn : d ∣ n) (hd : d ≠ 1) :
    cyclotomic d R ∣ ∑ i in range n, X ^ i := by
  suffices (cyclotomic d ℤ).map (Int.castRingHom R) ∣ (∑ i in range n, X ^ i).map (Int.castRingHom R) by
    have key := (map_ring_hom (Int.castRingHom R)).map_geom_sum X n
    simp only [← coe_map_ring_hom, ← map_X] at key
    rwa [map_cyclotomic, key] at this
  apply map_dvd
  rcases n.eq_zero_or_pos with (rfl | hn)
  · simp
    
  rw [← prod_cyclotomic_eq_geom_sum hn]
  apply Finset.dvd_prod_of_mem
  simp [← hd, ← hdn, ← hn.ne']

theorem X_pow_sub_one_mul_prod_cyclotomic_eq_X_pow_sub_one_of_dvd (R) [CommRingₓ R] {d n : ℕ}
    (h : d ∈ n.properDivisors) : ((X ^ d - 1) * ∏ x in n.divisors \ d.divisors, cyclotomic x R) = X ^ n - 1 := by
  obtain ⟨hd, hdn⟩ := nat.mem_proper_divisors.mp h
  have h0n := pos_of_gt hdn
  rcases d.eq_zero_or_pos with (rfl | h0d)
  · exfalso
    linarith [eq_zero_of_zero_dvd hd]
    
  rw [← prod_cyclotomic_eq_X_pow_sub_one h0d, ← prod_cyclotomic_eq_X_pow_sub_one h0n, mul_comm,
    Finset.prod_sdiff (Nat.divisors_subset_of_dvd h0n.ne' hd)]

theorem X_pow_sub_one_mul_cyclotomic_dvd_X_pow_sub_one_of_dvd (R) [CommRingₓ R] {d n : ℕ} (h : d ∈ n.properDivisors) :
    (X ^ d - 1) * cyclotomic n R ∣ X ^ n - 1 := by
  have hdn := (nat.mem_proper_divisors.mp h).2
  use ∏ x in n.proper_divisors \ d.divisors, cyclotomic x R
  symm
  convert X_pow_sub_one_mul_prod_cyclotomic_eq_X_pow_sub_one_of_dvd R h using 1
  rw [mul_assoc]
  congr 1
  rw [Nat.divisors_eq_proper_divisors_insert_self_of_pos <| pos_of_gt hdn, Finset.insert_sdiff_of_not_mem,
    Finset.prod_insert]
  · exact Finset.not_mem_sdiff_of_not_mem_left Nat.properDivisors.not_self_mem
    
  · exact fun hk => hdn.not_le <| Nat.divisor_le hk
    

theorem _root_.is_root_of_unity_iff {n : ℕ} (h : 0 < n) (R : Type _) [CommRingₓ R] [IsDomain R] {ζ : R} :
    ζ ^ n = 1 ↔ ∃ i ∈ n.divisors, (cyclotomic i R).IsRoot ζ := by
  rw [← mem_nth_roots h, nth_roots, mem_roots <| X_pow_sub_C_ne_zero h _, C_1, ← prod_cyclotomic_eq_X_pow_sub_one h,
      is_root_prod] <;>
    infer_instance

theorem is_root_of_unity_of_root_cyclotomic {n : ℕ} {R} [CommRingₓ R] {ζ : R} {i : ℕ} (hi : i ∈ n.divisors)
    (h : (cyclotomic i R).IsRoot ζ) : ζ ^ n = 1 := by
  rcases n.eq_zero_or_pos with (rfl | hn)
  · exact pow_zeroₓ _
    
  have := congr_arg (eval ζ) (prod_cyclotomic_eq_X_pow_sub_one hn R).symm
  rw [eval_sub, eval_pow, eval_X, eval_one] at this
  convert eq_add_of_sub_eq' this
  convert (add_zeroₓ _).symm
  apply eval_eq_zero_of_dvd_of_eval_eq_zero _ h
  exact Finset.dvd_prod_of_mem _ hi

section ArithmeticFunction

open Nat.ArithmeticFunction

open ArithmeticFunction

/-- `cyclotomic n R` can be expressed as a product in a fraction field of `polynomial R`
  using Möbius inversion. -/
theorem cyclotomic_eq_prod_X_pow_sub_one_pow_moebius {n : ℕ} (R : Type _) [CommRingₓ R] [IsDomain R] :
    algebraMap _ (Ratfunc R) (cyclotomic n R) =
      ∏ i in n.divisorsAntidiagonal, algebraMap R[X] _ (X ^ i.snd - 1) ^ μ i.fst :=
  by
  rcases n.eq_zero_or_pos with (rfl | hpos)
  · simp
    
  have h :
    ∀ n : ℕ, 0 < n → (∏ i in Nat.divisors n, algebraMap _ (Ratfunc R) (cyclotomic i R)) = algebraMap _ _ (X ^ n - 1) :=
    by
    intro n hn
    rw [← prod_cyclotomic_eq_X_pow_sub_one hn R, RingHom.map_prod]
  rw [(prod_eq_iff_prod_pow_moebius_eq_of_nonzero (fun n hn => _) fun n hn => _).1 h n hpos] <;>
    rw [Ne.def, IsFractionRing.to_map_eq_zero_iff]
  · apply cyclotomic_ne_zero
    
  · apply monic.ne_zero
    apply monic_X_pow_sub_C _ (ne_of_gtₓ hn)
    

end ArithmeticFunction

/-- We have
`cyclotomic n R = (X ^ k - 1) /ₘ (∏ i in nat.proper_divisors k, cyclotomic i K)`. -/
theorem cyclotomic_eq_X_pow_sub_one_div {R : Type _} [CommRingₓ R] {n : ℕ} (hpos : 0 < n) :
    cyclotomic n R = (X ^ n - 1) /ₘ ∏ i in Nat.properDivisors n, cyclotomic i R := by
  nontriviality R
  rw [← prod_cyclotomic_eq_X_pow_sub_one hpos, Nat.divisors_eq_proper_divisors_insert_self_of_pos hpos,
    Finset.prod_insert Nat.properDivisors.not_self_mem]
  have prod_monic : (∏ i in Nat.properDivisors n, cyclotomic i R).Monic := by
    apply monic_prod_of_monic
    intro i hi
    exact cyclotomic.monic i R
  rw [(div_mod_by_monic_unique (cyclotomic n R) 0 prod_monic _).1]
  simp only [← degree_zero, ← zero_addₓ]
  constructor
  · rw [mul_comm]
    
  rw [bot_lt_iff_ne_bot]
  intro h
  exact monic.ne_zero prod_monic (degree_eq_bot.1 h)

/-- If `m` is a proper divisor of `n`, then `X ^ m - 1` divides
`∏ i in nat.proper_divisors n, cyclotomic i R`. -/
theorem X_pow_sub_one_dvd_prod_cyclotomic (R : Type _) [CommRingₓ R] {n m : ℕ} (hpos : 0 < n) (hm : m ∣ n)
    (hdiff : m ≠ n) : X ^ m - 1 ∣ ∏ i in Nat.properDivisors n, cyclotomic i R := by
  replace hm :=
    Nat.mem_proper_divisors.2
      ⟨hm, lt_of_le_of_neₓ (Nat.divisor_le (Nat.mem_divisors.2 ⟨hm, (ne_of_ltₓ hpos).symm⟩)) hdiff⟩
  rw [←
    Finset.sdiff_union_of_subset
      (Nat.divisors_subset_proper_divisors (ne_of_ltₓ hpos).symm (Nat.mem_proper_divisors.1 hm).1
        (ne_of_ltₓ (Nat.mem_proper_divisors.1 hm).2)),
    Finset.prod_union Finset.sdiff_disjoint, prod_cyclotomic_eq_X_pow_sub_one (Nat.pos_of_mem_proper_divisors hm)]
  exact
    ⟨∏ x : ℕ in n.proper_divisors \ m.divisors, cyclotomic x R, by
      rw [mul_comm]⟩

/-- If there is a primitive `n`-th root of unity in `K`, then
`cyclotomic n K = ∏ μ in primitive_roots n R, (X - C μ)`. In particular,
`cyclotomic n K = cyclotomic' n K` -/
theorem cyclotomic_eq_prod_X_sub_primitive_roots {K : Type _} [CommRingₓ K] [IsDomain K] {ζ : K} {n : ℕ}
    (hz : IsPrimitiveRoot ζ n) : cyclotomic n K = ∏ μ in primitiveRoots n K, X - c μ := by
  rw [← cyclotomic']
  induction' n using Nat.strong_induction_onₓ with k hk generalizing ζ hz
  obtain hzero | hpos := k.eq_zero_or_pos
  · simp only [← hzero, ← cyclotomic'_zero, ← cyclotomic_zero]
    
  have h : ∀, ∀ i ∈ k.proper_divisors, ∀, cyclotomic i K = cyclotomic' i K := by
    intro i hi
    obtain ⟨d, hd⟩ := (Nat.mem_proper_divisors.1 hi).1
    rw [mul_comm] at hd
    exact hk i (Nat.mem_proper_divisors.1 hi).2 (IsPrimitiveRoot.pow hpos hz hd)
  rw [@cyclotomic_eq_X_pow_sub_one_div _ _ _ hpos, cyclotomic'_eq_X_pow_sub_one_div hpos hz,
    Finset.prod_congr (refl k.proper_divisors) h]

section Roots

variable {R : Type _} {n : ℕ} [CommRingₓ R] [IsDomain R]

/-- Any `n`-th primitive root of unity is a root of `cyclotomic n K`.-/
theorem _root_.is_primitive_root.is_root_cyclotomic (hpos : 0 < n) {μ : R} (h : IsPrimitiveRoot μ n) :
    IsRoot (cyclotomic n R) μ := by
  rw [← mem_roots (cyclotomic_ne_zero n R), cyclotomic_eq_prod_X_sub_primitive_roots h, roots_prod_X_sub_C, ←
    Finset.mem_def]
  rwa [← mem_primitive_roots hpos] at h

private theorem is_root_cyclotomic_iff' {n : ℕ} {K : Type _} [Field K] {μ : K} [NeZero (n : K)] :
    IsRoot (cyclotomic n K) μ ↔ IsPrimitiveRoot μ n := by
  -- in this proof, `o` stands for `order_of μ`
  have hnpos : 0 < n := (NeZero.of_ne_zero_coe K).out.bot_lt
  refine' ⟨fun hμ => _, IsPrimitiveRoot.is_root_cyclotomic hnpos⟩
  have hμn : μ ^ n = 1 := by
    rw [is_root_of_unity_iff hnpos]
    exact ⟨n, n.mem_divisors_self hnpos.ne', hμ⟩
  by_contra hnμ
  have ho : 0 < orderOf μ := by
    apply order_of_pos'
    rw [is_of_fin_order_iff_pow_eq_one]
    exact ⟨n, hnpos, hμn⟩
  have := pow_order_of_eq_one μ
  rw [is_root_of_unity_iff ho] at this
  obtain ⟨i, hio, hiμ⟩ := this
  replace hio := Nat.dvd_of_mem_divisors hio
  rw [IsPrimitiveRoot.not_iff] at hnμ
  rw [← order_of_dvd_iff_pow_eq_one] at hμn
  have key : i < n := (Nat.le_of_dvdₓ ho hio).trans_lt ((Nat.le_of_dvdₓ hnpos hμn).lt_of_ne hnμ)
  have key' : i ∣ n := hio.trans hμn
  rw [← Polynomial.dvd_iff_is_root] at hμ hiμ
  have hni : {i, n} ⊆ n.divisors := by
    simpa [← Finset.insert_subset, ← key'] using hnpos.ne'
  obtain ⟨k, hk⟩ := hiμ
  obtain ⟨j, hj⟩ := hμ
  have := prod_cyclotomic_eq_X_pow_sub_one hnpos K
  rw [← Finset.prod_sdiff hni, Finset.prod_pair key.ne, hk, hj] at this
  have hn := (X_pow_sub_one_separable_iff.mpr <| NeZero.ne' n K).Squarefree
  rw [← this, Squarefree] at hn
  contrapose! hn
  refine'
    ⟨X - C μ,
      ⟨(∏ x in n.divisors \ {i, n}, cyclotomic x K) * k * j, by
        ring⟩,
      _⟩
  simp [← Polynomial.is_unit_iff_degree_eq_zero]

theorem is_root_cyclotomic_iff [NeZero (n : R)] {μ : R} : IsRoot (cyclotomic n R) μ ↔ IsPrimitiveRoot μ n := by
  have hf : Function.Injective _ := IsFractionRing.injective R (FractionRing R)
  have : NeZero (n : FractionRing R) := NeZero.nat_of_injective hf
  rw [← is_root_map_iff hf, ← IsPrimitiveRoot.map_iff_of_injective hf, map_cyclotomic, ← is_root_cyclotomic_iff']

theorem roots_cyclotomic_nodup [NeZero (n : R)] : (cyclotomic n R).roots.Nodup := by
  obtain h | ⟨ζ, hζ⟩ := (cyclotomic n R).roots.empty_or_exists_mem
  · exact h.symm ▸ Multiset.nodup_zero
    
  rw [mem_roots <| cyclotomic_ne_zero n R, is_root_cyclotomic_iff] at hζ
  refine'
    Multiset.nodup_of_le
      (roots.le_of_dvd (X_pow_sub_C_ne_zero (NeZero.pos_of_ne_zero_coe R) 1) <| cyclotomic.dvd_X_pow_sub_one n R)
      hζ.nth_roots_nodup

theorem cyclotomic.roots_to_finset_eq_primitive_roots [NeZero (n : R)] :
    (⟨(cyclotomic n R).roots, roots_cyclotomic_nodup⟩ : Finset _) = primitiveRoots n R := by
  ext
  simp [← cyclotomic_ne_zero n R, ← is_root_cyclotomic_iff, ← mem_primitive_roots, ← NeZero.pos_of_ne_zero_coe R]

theorem cyclotomic.roots_eq_primitive_roots_val [NeZero (n : R)] : (cyclotomic n R).roots = (primitiveRoots n R).val :=
  by
  rw [← cyclotomic.roots_to_finset_eq_primitive_roots]

end Roots

/-- If `R` is of characteristic zero, then `ζ` is a root of `cyclotomic n R` if and only if it is a
primitive `n`-th root of unity. -/
theorem is_root_cyclotomic_iff_char_zero {n : ℕ} {R : Type _} [CommRingₓ R] [IsDomain R] [CharZero R] {μ : R}
    (hn : 0 < n) : (Polynomial.cyclotomic n R).IsRoot μ ↔ IsPrimitiveRoot μ n := by
  let this := NeZero.of_gt hn
  exact is_root_cyclotomic_iff

/-- Over a ring `R` of characteristic zero, `λ n, cyclotomic n R` is injective. -/
theorem cyclotomic_injective {R : Type _} [CommRingₓ R] [CharZero R] : Function.Injective fun n => cyclotomic n R := by
  intro n m hnm
  simp only at hnm
  rcases eq_or_ne n 0 with (rfl | hzero)
  · rw [cyclotomic_zero] at hnm
    replace hnm := congr_arg nat_degree hnm
    rw [nat_degree_one, nat_degree_cyclotomic] at hnm
    by_contra
    exact (Nat.totient_pos (zero_lt_iff.2 (Ne.symm h))).Ne hnm
    
  · have := NeZero.mk hzero
    rw [← map_cyclotomic_int _ R, ← map_cyclotomic_int _ R] at hnm
    replace hnm := map_injective (Int.castRingHom R) Int.cast_injective hnm
    replace hnm := congr_arg (map (Int.castRingHom ℂ)) hnm
    rw [map_cyclotomic_int, map_cyclotomic_int] at hnm
    have hprim := Complex.is_primitive_root_exp _ hzero
    have hroot := is_root_cyclotomic_iff.2 hprim
    rw [hnm] at hroot
    have hmzero : NeZero m :=
      ⟨fun h => by
        simpa [← h] using hroot⟩
    rw [is_root_cyclotomic_iff] at hroot
    replace hprim := hprim.eq_order_of
    rwa [← IsPrimitiveRoot.eq_order_of hroot] at hprim
    

theorem eq_cyclotomic_iff {R : Type _} [CommRingₓ R] {n : ℕ} (hpos : 0 < n) (P : R[X]) :
    P = cyclotomic n R ↔ (P * ∏ i in Nat.properDivisors n, Polynomial.cyclotomic i R) = X ^ n - 1 := by
  nontriviality R
  refine' ⟨fun hcycl => _, fun hP => _⟩
  · rw [hcycl, ← Finset.prod_insert (@Nat.properDivisors.not_self_mem n), ←
      Nat.divisors_eq_proper_divisors_insert_self_of_pos hpos]
    exact prod_cyclotomic_eq_X_pow_sub_one hpos R
    
  · have prod_monic : (∏ i in Nat.properDivisors n, cyclotomic i R).Monic := by
      apply monic_prod_of_monic
      intro i hi
      exact cyclotomic.monic i R
    rw [@cyclotomic_eq_X_pow_sub_one_div R _ _ hpos, (div_mod_by_monic_unique P 0 prod_monic _).1]
    refine'
      ⟨by
        rwa [zero_addₓ, mul_comm], _⟩
    rw [degree_zero, bot_lt_iff_ne_bot]
    intro h
    exact monic.ne_zero prod_monic (degree_eq_bot.1 h)
    

/-- If `p` is prime, then `cyclotomic p R = ∑ i in range p, X ^ i`. -/
theorem cyclotomic_eq_geom_sum {R : Type _} [CommRingₓ R] {p : ℕ} (hp : Nat.Prime p) :
    cyclotomic p R = ∑ i in range p, X ^ i := by
  refine' ((eq_cyclotomic_iff hp.pos _).mpr _).symm
  simp only [← Nat.Prime.proper_divisors hp, ← geom_sum_mul, ← Finset.prod_singleton, ← cyclotomic_one]

theorem cyclotomic_prime_mul_X_sub_one (R : Type _) [CommRingₓ R] (p : ℕ) [hn : Fact (Nat.Prime p)] :
    cyclotomic p R * (X - 1) = X ^ p - 1 := by
  rw [cyclotomic_eq_geom_sum hn.out, geom_sum_mul]

/-- If `p ^ k` is a prime power, then
`cyclotomic (p ^ (n + 1)) R = ∑ i in range p, (X ^ (p ^ n)) ^ i`. -/
theorem cyclotomic_prime_pow_eq_geom_sum {R : Type _} [CommRingₓ R] {p n : ℕ} (hp : Nat.Prime p) :
    cyclotomic (p ^ (n + 1)) R = ∑ i in range p, (X ^ p ^ n) ^ i := by
  have :
    ∀ m,
      (cyclotomic (p ^ (m + 1)) R = ∑ i in range p, (X ^ p ^ m) ^ i) ↔
        ((∑ i in range p, (X ^ p ^ m) ^ i) * ∏ x : ℕ in Finset.range (m + 1), cyclotomic (p ^ x) R) =
          X ^ p ^ (m + 1) - 1 :=
    by
    intro m
    have := eq_cyclotomic_iff (pow_pos hp.pos (m + 1)) _
    rw [eq_comm] at this
    rw [this, Nat.prod_proper_divisors_prime_pow hp]
  induction' n with n_n n_ih
  · simp [← cyclotomic_eq_geom_sum hp]
    
  rw [((eq_cyclotomic_iff (pow_pos hp.pos (n_n.succ + 1)) _).mpr _).symm]
  rw [Nat.prod_proper_divisors_prime_pow hp, Finset.prod_range_succ, n_ih]
  rw [this] at n_ih
  rw [mul_comm _ (∑ i in _, _), n_ih, geom_sum_mul, sub_left_inj, ← pow_mulₓ, pow_addₓ, pow_oneₓ]

theorem cyclotomic_prime_pow_mul_X_pow_sub_one (R : Type _) [CommRingₓ R] (p k : ℕ) [hn : Fact (Nat.Prime p)] :
    cyclotomic (p ^ (k + 1)) R * (X ^ p ^ k - 1) = X ^ p ^ (k + 1) - 1 := by
  rw [cyclotomic_prime_pow_eq_geom_sum hn.out, geom_sum_mul, ← pow_mulₓ, pow_succₓ, mul_comm]

/-- The constant term of `cyclotomic n R` is `1` if `2 ≤ n`. -/
theorem cyclotomic_coeff_zero (R : Type _) [CommRingₓ R] {n : ℕ} (hn : 2 ≤ n) : (cyclotomic n R).coeff 0 = 1 := by
  induction' n using Nat.strong_induction_onₓ with n hi
  have hprod : (∏ i in Nat.properDivisors n, (Polynomial.cyclotomic i R).coeff 0) = -1 := by
    rw [← Finset.insert_erase (Nat.one_mem_proper_divisors_iff_one_lt.2 (lt_of_lt_of_leₓ one_lt_two hn)),
      Finset.prod_insert (Finset.not_mem_erase 1 _), cyclotomic_one R]
    have hleq : ∀, ∀ j ∈ n.proper_divisors.erase 1, ∀, 2 ≤ j := by
      intro j hj
      apply Nat.succ_le_of_ltₓ
      exact
        (Ne.le_iff_lt (Finset.mem_erase.1 hj).1.symm).mp
          (Nat.succ_le_of_ltₓ (Nat.pos_of_mem_proper_divisors (Finset.mem_erase.1 hj).2))
    have hcongr : ∀, ∀ j ∈ n.proper_divisors.erase 1, ∀, (cyclotomic j R).coeff 0 = 1 := by
      intro j hj
      exact hi j (Nat.mem_proper_divisors.1 (Finset.mem_erase.1 hj).2).2 (hleq j hj)
    have hrw : (∏ x : ℕ in n.proper_divisors.erase 1, (cyclotomic x R).coeff 0) = 1 := by
      rw [Finset.prod_congr (refl (n.proper_divisors.erase 1)) hcongr]
      simp only [← Finset.prod_const_one]
    simp only [← hrw, ← mul_oneₓ, ← zero_sub, ← coeff_one_zero, ← coeff_X_zero, ← coeff_sub]
  have heq : (X ^ n - 1).coeff 0 = -(cyclotomic n R).coeff 0 := by
    rw [← prod_cyclotomic_eq_X_pow_sub_one (lt_of_lt_of_leₓ zero_lt_two hn),
      Nat.divisors_eq_proper_divisors_insert_self_of_pos (lt_of_lt_of_leₓ zero_lt_two hn),
      Finset.prod_insert Nat.properDivisors.not_self_mem, mul_coeff_zero, coeff_zero_prod, hprod, mul_neg, mul_oneₓ]
  have hzero : (X ^ n - 1).coeff 0 = (-1 : R) := by
    rw [coeff_zero_eq_eval_zero _]
    simp only [← zero_pow (lt_of_lt_of_leₓ zero_lt_two hn), ← eval_X, ← eval_one, ← zero_sub, ← eval_pow, ← eval_sub]
  rw [hzero] at heq
  exact neg_inj.mp (Eq.symm HEq)

/-- If `(a : ℕ)` is a root of `cyclotomic n (zmod p)`, where `p` is a prime, then `a` and `p` are
coprime. -/
theorem coprime_of_root_cyclotomic {n : ℕ} (hpos : 0 < n) {p : ℕ} [hprime : Fact p.Prime] {a : ℕ}
    (hroot : IsRoot (cyclotomic n (Zmod p)) (Nat.castRingHom (Zmod p) a)) : a.Coprime p := by
  apply Nat.Coprime.symm
  rw [hprime.1.coprime_iff_not_dvd]
  intro h
  replace h := (Zmod.nat_coe_zmod_eq_zero_iff_dvd a p).2 h
  rw [is_root.def, eq_nat_cast, h, ← coeff_zero_eq_eval_zero] at hroot
  by_cases' hone : n = 1
  · simp only [← hone, ← cyclotomic_one, ← zero_sub, ← coeff_one_zero, ← coeff_X_zero, ← neg_eq_zero, ← one_ne_zero, ←
      coeff_sub] at hroot
    exact hroot
    
  rw [cyclotomic_coeff_zero (Zmod p) (Nat.succ_le_of_ltₓ (lt_of_le_of_neₓ (Nat.succ_le_of_ltₓ hpos) (Ne.symm hone)))] at
    hroot
  exact one_ne_zero hroot

end Cyclotomic

section Order

/-- If `(a : ℕ)` is a root of `cyclotomic n (zmod p)`, then the multiplicative order of `a` modulo
`p` divides `n`. -/
theorem order_of_root_cyclotomic_dvd {n : ℕ} (hpos : 0 < n) {p : ℕ} [Fact p.Prime] {a : ℕ}
    (hroot : IsRoot (cyclotomic n (Zmod p)) (Nat.castRingHom (Zmod p) a)) :
    orderOf (Zmod.unitOfCoprime a (coprime_of_root_cyclotomic hpos hroot)) ∣ n := by
  apply order_of_dvd_of_pow_eq_one
  suffices hpow : eval (Nat.castRingHom (Zmod p) a) (X ^ n - 1 : (Zmod p)[X]) = 0
  · simp only [← eval_X, ← eval_one, ← eval_pow, ← eval_sub, ← eq_nat_cast] at hpow
    apply Units.coe_eq_one.1
    simp only [← sub_eq_zero.mp hpow, ← Zmod.coe_unit_of_coprime, ← Units.coe_pow]
    
  rw [is_root.def] at hroot
  rw [← prod_cyclotomic_eq_X_pow_sub_one hpos (Zmod p), Nat.divisors_eq_proper_divisors_insert_self_of_pos hpos,
    Finset.prod_insert Nat.properDivisors.not_self_mem, eval_mul, hroot, zero_mul]

end Order

section minpoly

open IsPrimitiveRoot Complex

/-- The minimal polynomial of a primitive `n`-th root of unity `μ` divides `cyclotomic n ℤ`. -/
theorem _root_.is_primitive_root.minpoly_dvd_cyclotomic {n : ℕ} {K : Type _} [Field K] {μ : K} (h : IsPrimitiveRoot μ n)
    (hpos : 0 < n) [CharZero K] : minpoly ℤ μ ∣ cyclotomic n ℤ := by
  apply minpoly.gcd_domain_dvd (IsIntegral h hpos) (cyclotomic_ne_zero n ℤ)
  simpa [← aeval_def, ← eval₂_eq_eval_map, ← is_root.def] using is_root_cyclotomic hpos h

theorem _root_.is_primitive_root.minpoly_eq_cyclotomic_of_irreducible {K : Type _} [Field K] {R : Type _} [CommRingₓ R]
    [IsDomain R] {μ : R} {n : ℕ} [Algebra K R] (hμ : IsPrimitiveRoot μ n) (h : Irreducible <| cyclotomic n K)
    [NeZero (n : K)] : cyclotomic n K = minpoly K μ := by
  have := NeZero.of_no_zero_smul_divisors K R n
  refine' minpoly.eq_of_irreducible_of_monic h _ (cyclotomic.monic n K)
  rwa [aeval_def, eval₂_eq_eval_map, map_cyclotomic, ← is_root.def, is_root_cyclotomic_iff]

/-- `cyclotomic n ℤ` is the minimal polynomial of a primitive `n`-th root of unity `μ`. -/
theorem cyclotomic_eq_minpoly {n : ℕ} {K : Type _} [Field K] {μ : K} (h : IsPrimitiveRoot μ n) (hpos : 0 < n)
    [CharZero K] : cyclotomic n ℤ = minpoly ℤ μ := by
  refine'
    eq_of_monic_of_dvd_of_nat_degree_le (minpoly.monic (IsIntegral h hpos)) (cyclotomic.monic n ℤ)
      (h.minpoly_dvd_cyclotomic hpos) _
  simpa [← nat_degree_cyclotomic n ℤ] using totient_le_degree_minpoly h

/-- `cyclotomic n ℚ` is the minimal polynomial of a primitive `n`-th root of unity `μ`. -/
theorem cyclotomic_eq_minpoly_rat {n : ℕ} {K : Type _} [Field K] {μ : K} (h : IsPrimitiveRoot μ n) (hpos : 0 < n)
    [CharZero K] : cyclotomic n ℚ = minpoly ℚ μ := by
  rw [← map_cyclotomic_int, cyclotomic_eq_minpoly h hpos]
  exact (minpoly.gcd_domain_eq_field_fractions' _ (IsIntegral h hpos)).symm

/-- `cyclotomic n ℤ` is irreducible. -/
theorem cyclotomic.irreducible {n : ℕ} (hpos : 0 < n) : Irreducible (cyclotomic n ℤ) := by
  rw [cyclotomic_eq_minpoly (is_primitive_root_exp n hpos.ne') hpos]
  apply minpoly.irreducible
  exact (is_primitive_root_exp n hpos.ne').IsIntegral hpos

/-- `cyclotomic n ℚ` is irreducible. -/
theorem cyclotomic.irreducible_rat {n : ℕ} (hpos : 0 < n) : Irreducible (cyclotomic n ℚ) := by
  rw [← map_cyclotomic_int]
  exact
    (is_primitive.int.irreducible_iff_irreducible_map_cast (cyclotomic.is_primitive n ℤ)).1
      (cyclotomic.irreducible hpos)

/-- If `n ≠ m`, then `(cyclotomic n ℚ)` and `(cyclotomic m ℚ)` are coprime. -/
theorem cyclotomic.is_coprime_rat {n m : ℕ} (h : n ≠ m) : IsCoprime (cyclotomic n ℚ) (cyclotomic m ℚ) := by
  rcases n.eq_zero_or_pos with (rfl | hnzero)
  · exact is_coprime_one_left
    
  rcases m.eq_zero_or_pos with (rfl | hmzero)
  · exact is_coprime_one_right
    
  rw [Irreducible.coprime_iff_not_dvd <| cyclotomic.irreducible_rat <| hnzero]
  exact fun hdiv =>
    h <|
      cyclotomic_injective <|
        eq_of_monic_of_associated (cyclotomic.monic n ℚ) (cyclotomic.monic m ℚ) <|
          Irreducible.associated_of_dvd (cyclotomic.irreducible_rat hnzero) (cyclotomic.irreducible_rat hmzero) hdiv

end minpoly

section Expand

/-- If `p` is a prime such that `¬ p ∣ n`, then
`expand R p (cyclotomic n R) = (cyclotomic (n * p) R) * (cyclotomic n R)`. -/
@[simp]
theorem cyclotomic_expand_eq_cyclotomic_mul {p n : ℕ} (hp : Nat.Prime p) (hdiv : ¬p ∣ n) (R : Type _) [CommRingₓ R] :
    expand R p (cyclotomic n R) = cyclotomic (n * p) R * cyclotomic n R := by
  rcases Nat.eq_zero_or_posₓ n with (rfl | hnpos)
  · simp
    
  have := NeZero.of_pos hnpos
  suffices expand ℤ p (cyclotomic n ℤ) = cyclotomic (n * p) ℤ * cyclotomic n ℤ by
    rw [← map_cyclotomic_int, ← map_expand, this, Polynomial.map_mul, map_cyclotomic_int]
  refine'
    eq_of_monic_of_dvd_of_nat_degree_le ((cyclotomic.monic _ _).mul (cyclotomic.monic _ _))
      ((cyclotomic.monic n ℤ).expand hp.pos) _ _
  · refine'
      (is_primitive.int.dvd_iff_map_cast_dvd_map_cast _ _
            (is_primitive.mul (cyclotomic.is_primitive (n * p) ℤ) (cyclotomic.is_primitive n ℤ))
            ((cyclotomic.monic n ℤ).expand hp.pos).IsPrimitive).2
        _
    rw [Polynomial.map_mul, map_cyclotomic_int, map_cyclotomic_int, map_expand, map_cyclotomic_int]
    refine' IsCoprime.mul_dvd (cyclotomic.is_coprime_rat fun h => _) _ _
    · replace h : n * p = n * 1 := by
        simp [← h]
      exact Nat.Prime.ne_one hp (Nat.eq_of_mul_eq_mul_leftₓ hnpos h)
      
    · have hpos : 0 < n * p := mul_pos hnpos hp.pos
      have hprim := Complex.is_primitive_root_exp _ hpos.ne'
      rw [cyclotomic_eq_minpoly_rat hprim hpos]
      refine' @minpoly.dvd ℚ ℂ _ _ algebraRat _ _ _
      rw [aeval_def, ← eval_map, map_expand, map_cyclotomic, expand_eval, ← is_root.def, is_root_cyclotomic_iff]
      convert IsPrimitiveRoot.pow_of_dvd hprim hp.ne_zero (dvd_mul_left p n)
      rw [Nat.mul_div_cancelₓ _ (Nat.Prime.pos hp)]
      
    · have hprim := Complex.is_primitive_root_exp _ hnpos.ne.symm
      rw [cyclotomic_eq_minpoly_rat hprim hnpos]
      refine' @minpoly.dvd ℚ ℂ _ _ algebraRat _ _ _
      rw [aeval_def, ← eval_map, map_expand, expand_eval, ← is_root.def, ← cyclotomic_eq_minpoly_rat hprim hnpos,
        map_cyclotomic, is_root_cyclotomic_iff]
      exact IsPrimitiveRoot.pow_of_prime hprim hp hdiv
      
    
  · rw [nat_degree_expand, nat_degree_cyclotomic, nat_degree_mul (cyclotomic_ne_zero _ ℤ) (cyclotomic_ne_zero _ ℤ),
      nat_degree_cyclotomic, nat_degree_cyclotomic, mul_comm n,
      Nat.totient_mul ((Nat.Prime.coprime_iff_not_dvd hp).2 hdiv), Nat.totient_prime hp, mul_comm (p - 1), ←
      Nat.mul_succ, Nat.sub_one, Nat.succ_pred_eq_of_posₓ hp.pos]
    

/-- If `p` is a prime such that `p ∣ n`, then
`expand R p (cyclotomic n R) = cyclotomic (p * n) R`. -/
@[simp]
theorem cyclotomic_expand_eq_cyclotomic {p n : ℕ} (hp : Nat.Prime p) (hdiv : p ∣ n) (R : Type _) [CommRingₓ R] :
    expand R p (cyclotomic n R) = cyclotomic (n * p) R := by
  rcases n.eq_zero_or_pos with (rfl | hzero)
  · simp
    
  have := NeZero.of_pos hzero
  suffices expand ℤ p (cyclotomic n ℤ) = cyclotomic (n * p) ℤ by
    rw [← map_cyclotomic_int, ← map_expand, this, map_cyclotomic_int]
  refine' eq_of_monic_of_dvd_of_nat_degree_le (cyclotomic.monic _ _) ((cyclotomic.monic n ℤ).expand hp.pos) _ _
  · have hpos := Nat.mul_posₓ hzero hp.pos
    have hprim := Complex.is_primitive_root_exp _ hpos.ne.symm
    rw [cyclotomic_eq_minpoly hprim hpos]
    refine' minpoly.gcd_domain_dvd (hprim.is_integral hpos) ((cyclotomic.monic n ℤ).expand hp.pos).ne_zero _
    rw [aeval_def, ← eval_map, map_expand, map_cyclotomic, expand_eval, ← is_root.def, is_root_cyclotomic_iff]
    · convert IsPrimitiveRoot.pow_of_dvd hprim hp.ne_zero (dvd_mul_left p n)
      rw [Nat.mul_div_cancelₓ _ hp.pos]
      
    
  · rw [nat_degree_expand, nat_degree_cyclotomic, nat_degree_cyclotomic, mul_comm n,
      Nat.totient_mul_of_prime_of_dvd hp hdiv, mul_comm]
    

/-- If the `p ^ n`th cyclotomic polynomial is irreducible, so is the `p ^ m`th, for `m ≤ n`. -/
theorem cyclotomic_irreducible_pow_of_irreducible_pow {p : ℕ} (hp : Nat.Prime p) {R} [CommRingₓ R] [IsDomain R]
    {n m : ℕ} (hmn : m ≤ n) (h : Irreducible (cyclotomic (p ^ n) R)) : Irreducible (cyclotomic (p ^ m) R) := by
  rcases m.eq_zero_or_pos with (rfl | hm)
  · simpa using irreducible_X_sub_C (1 : R)
    
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  induction' k with k hk
  · simpa using h
    
  have : m + k ≠ 0 := (add_pos_of_pos_of_nonneg hm k.zero_le).ne'
  rw [Nat.add_succ, pow_succ'ₓ, ← cyclotomic_expand_eq_cyclotomic hp <| dvd_pow_self p this] at h
  exact
    hk
      (by
        linarith)
      (of_irreducible_expand hp.ne_zero h)

/-- If `irreducible (cyclotomic (p ^ n) R)` then `irreducible (cyclotomic p R).` -/
theorem cyclotomic_irreducible_of_irreducible_pow {p : ℕ} (hp : Nat.Prime p) {R} [CommRingₓ R] [IsDomain R] {n : ℕ}
    (hn : n ≠ 0) (h : Irreducible (cyclotomic (p ^ n) R)) : Irreducible (cyclotomic p R) :=
  pow_oneₓ p ▸ cyclotomic_irreducible_pow_of_irreducible_pow hp hn.bot_lt h

end Expand

section CharP

/-- If `R` is of characteristic `p` and `¬p ∣ n`, then
`cyclotomic (n * p) R = (cyclotomic n R) ^ (p - 1)`. -/
theorem cyclotomic_mul_prime_eq_pow_of_not_dvd (R : Type _) {p n : ℕ} [hp : Fact (Nat.Prime p)] [Ringₓ R] [CharP R p]
    (hn : ¬p ∣ n) : cyclotomic (n * p) R = cyclotomic n R ^ (p - 1) := by
  suffices cyclotomic (n * p) (Zmod p) = cyclotomic n (Zmod p) ^ (p - 1) by
    rw [← map_cyclotomic _ (algebraMap (Zmod p) R), ← map_cyclotomic _ (algebraMap (Zmod p) R), this,
      Polynomial.map_pow]
  apply mul_right_injective₀ (cyclotomic_ne_zero n <| Zmod p)
  rw [← pow_succₓ, tsub_add_cancel_of_le hp.out.one_lt.le, mul_comm, ← Zmod.expand_card]
  nth_rw 2[← map_cyclotomic_int]
  rw [← map_expand, cyclotomic_expand_eq_cyclotomic_mul hp.out hn, Polynomial.map_mul, map_cyclotomic, map_cyclotomic]

/-- If `R` is of characteristic `p` and `p ∣ n`, then
`cyclotomic (n * p) R = (cyclotomic n R) ^ p`. -/
theorem cyclotomic_mul_prime_dvd_eq_pow (R : Type _) {p n : ℕ} [hp : Fact (Nat.Prime p)] [Ringₓ R] [CharP R p]
    (hn : p ∣ n) : cyclotomic (n * p) R = cyclotomic n R ^ p := by
  suffices cyclotomic (n * p) (Zmod p) = cyclotomic n (Zmod p) ^ p by
    rw [← map_cyclotomic _ (algebraMap (Zmod p) R), ← map_cyclotomic _ (algebraMap (Zmod p) R), this,
      Polynomial.map_pow]
  rw [← Zmod.expand_card, ← map_cyclotomic_int n, ← map_expand, cyclotomic_expand_eq_cyclotomic hp.out hn,
    map_cyclotomic, mul_comm]

/-- If `R` is of characteristic `p` and `¬p ∣ m`, then
`cyclotomic (p ^ k * m) R = (cyclotomic m R) ^ (p ^ k - p ^ (k - 1))`. -/
theorem cyclotomic_mul_prime_pow_eq (R : Type _) {p m : ℕ} [Fact (Nat.Prime p)] [Ringₓ R] [CharP R p] (hm : ¬p ∣ m) :
    ∀ {k}, 0 < k → cyclotomic (p ^ k * m) R = cyclotomic m R ^ (p ^ k - p ^ (k - 1))
  | 1, _ => by
    rw [pow_oneₓ, Nat.sub_self, pow_zeroₓ, mul_comm, cyclotomic_mul_prime_eq_pow_of_not_dvd R hm]
  | a + 2, _ => by
    have hdiv : p ∣ p ^ a.succ * m :=
      ⟨p ^ a * m, by
        rw [← mul_assoc, pow_succₓ]⟩
    rw [pow_succₓ, mul_assoc, mul_comm, cyclotomic_mul_prime_dvd_eq_pow R hdiv, cyclotomic_mul_prime_pow_eq a.succ_pos,
      ← pow_mulₓ]
    congr 1
    simp only [← tsub_zero, ← Nat.succ_sub_succ_eq_sub]
    rw [Nat.mul_sub_right_distrib, mul_comm, pow_succ'ₓ]

/-- If `R` is of characteristic `p` and `¬p ∣ m`, then `ζ` is a root of `cyclotomic (p ^ k * m) R`
 if and only if it is a primitive `m`-th root of unity. -/
theorem is_root_cyclotomic_prime_pow_mul_iff_of_char_p {m k p : ℕ} {R : Type _} [CommRingₓ R] [IsDomain R]
    [hp : Fact (Nat.Prime p)] [hchar : CharP R p] {μ : R} [NeZero (m : R)] :
    (Polynomial.cyclotomic (p ^ k * m) R).IsRoot μ ↔ IsPrimitiveRoot μ m := by
  rcases k.eq_zero_or_pos with (rfl | hk)
  · rw [pow_zeroₓ, one_mulₓ, is_root_cyclotomic_iff]
    
  refine' ⟨fun h => _, fun h => _⟩
  · rw [is_root.def, cyclotomic_mul_prime_pow_eq R (NeZero.not_char_dvd R p m) hk, eval_pow] at h
    replace h := pow_eq_zero h
    rwa [← is_root.def, is_root_cyclotomic_iff] at h
    
  · rw [← is_root_cyclotomic_iff, is_root.def] at h
    rw [cyclotomic_mul_prime_pow_eq R (NeZero.not_char_dvd R p m) hk, is_root.def, eval_pow, h, zero_pow]
    simp only [← tsub_pos_iff_lt]
    apply strict_mono_pow hp.out.one_lt (Nat.pred_ltₓ hk.ne')
    

end CharP

end Polynomial

