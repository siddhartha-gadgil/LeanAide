/-
Copyright (c) 2022 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Heather Macbeth
-/
import Mathbin.FieldTheory.IsAlgClosed.Basic
import Mathbin.RingTheory.WittVector.DiscreteValuationRing

/-!
# Solving equations about the Frobenius map on the field of fractions of `𝕎 k`

The goal of this file is to prove `witt_vector.exists_frobenius_solution_fraction_ring`,
which says that for an algebraically closed field `k` of characteristic `p` and `a, b` in the
field of fractions of Witt vectors over `k`,
there is a solution `b` to the equation `φ b * a = p ^ m * b`, where `φ` is the Frobenius map.

Most of this file builds up the equivalent theorem over `𝕎 k` directly,
moving to the field of fractions at the end.
See `witt_vector.frobenius_rotation` and its specification.

The construction proceeds by recursively defining a sequence of coefficients as solutions to a
polynomial equation in `k`. We must define these as generic polynomials using Witt vector API
(`witt_vector.witt_mul`, `witt_polynomial`) to show that they satisfy the desired equation.

Preliminary work is done in the dependency `ring_theory.witt_vector.mul_coeff`
to isolate the `n+1`st coefficients of `x` and `y` in the `n+1`st coefficient of `x*y`.

This construction is described in Dupuis, Lewis, and Macbeth,
[Formalized functional analysis via semilinear maps][dupuis-lewis-macbeth2022].
We approximately follow an approach sketched on MathOverflow:
<https://mathoverflow.net/questions/62468/about-frobenius-of-witt-vectors>

The result is a dependency for the proof of `witt_vector.isocrystal_classification`,
the classification of one-dimensional isocrystals over an algebraically closed field.
-/


noncomputable section

namespace WittVector

variable (p : ℕ) [hp : Fact p.Prime]

-- mathport name: «expr𝕎»
local notation "𝕎" => WittVector p

namespace RecursionMain

/-!

## The recursive case of the vector coefficients

The first coefficient of our solution vector is easy to define below.
In this section we focus on the recursive case.
The goal is to turn `witt_poly_prod n` into a univariate polynomial
whose variable represents the `n`th coefficient of `x` in `x * a`.

-/


section CommRingₓ

include hp

variable {k : Type _} [CommRingₓ k] [CharP k p]

open Polynomial

/-- The root of this polynomial determines the `n+1`st coefficient of our solution. -/
def succNthDefiningPoly (n : ℕ) (a₁ a₂ : 𝕎 k) (bs : Finₓ (n + 1) → k) : Polynomial k :=
  X ^ p * c (a₁.coeff 0 ^ p ^ (n + 1)) - X * c (a₂.coeff 0 ^ p ^ (n + 1)) +
    c
      (a₁.coeff (n + 1) * (bs 0 ^ p) ^ p ^ (n + 1) + nthRemainder p n (fun v => bs v ^ p) (truncateFun (n + 1) a₁) -
          a₂.coeff (n + 1) * bs 0 ^ p ^ (n + 1) -
        nthRemainder p n bs (truncateFun (n + 1) a₂))

theorem succ_nth_defining_poly_degree [IsDomain k] (n : ℕ) (a₁ a₂ : 𝕎 k) (bs : Finₓ (n + 1) → k) (ha₁ : a₁.coeff 0 ≠ 0)
    (ha₂ : a₂.coeff 0 ≠ 0) : (succNthDefiningPoly p n a₁ a₂ bs).degree = p := by
  have : (X ^ p * C (a₁.coeff 0 ^ p ^ (n + 1))).degree = p := by
    rw [degree_mul, degree_C]
    · simp only [← Nat.cast_with_bot, ← add_zeroₓ, ← degree_X, ← degree_pow, ← Nat.smul_one_eq_coe]
      
    · exact pow_ne_zero _ ha₁
      
  have : (X ^ p * C (a₁.coeff 0 ^ p ^ (n + 1)) - X * C (a₂.coeff 0 ^ p ^ (n + 1))).degree = p := by
    rw [degree_sub_eq_left_of_degree_lt, this]
    rw [this, degree_mul, degree_C, degree_X, add_zeroₓ]
    · exact_mod_cast hp.out.one_lt
      
    · exact pow_ne_zero _ ha₂
      
  rw [succ_nth_defining_poly, degree_add_eq_left_of_degree_lt, this]
  apply lt_of_le_of_ltₓ degree_C_le
  rw [this]
  exact_mod_cast hp.out.pos

end CommRingₓ

section IsAlgClosed

include hp

variable {k : Type _} [Field k] [CharP k p] [IsAlgClosed k]

theorem root_exists (n : ℕ) (a₁ a₂ : 𝕎 k) (bs : Finₓ (n + 1) → k) (ha₁ : a₁.coeff 0 ≠ 0) (ha₂ : a₂.coeff 0 ≠ 0) :
    ∃ b : k, (succNthDefiningPoly p n a₁ a₂ bs).IsRoot b :=
  IsAlgClosed.exists_root _ <| by
    simp [← succ_nth_defining_poly_degree p n a₁ a₂ bs ha₁ ha₂, ← hp.out.ne_zero]

/-- This is the `n+1`st coefficient of our solution, projected from `root_exists`. -/
def succNthVal (n : ℕ) (a₁ a₂ : 𝕎 k) (bs : Finₓ (n + 1) → k) (ha₁ : a₁.coeff 0 ≠ 0) (ha₂ : a₂.coeff 0 ≠ 0) : k :=
  Classical.some (root_exists p n a₁ a₂ bs ha₁ ha₂)

theorem succ_nth_val_spec (n : ℕ) (a₁ a₂ : 𝕎 k) (bs : Finₓ (n + 1) → k) (ha₁ : a₁.coeff 0 ≠ 0) (ha₂ : a₂.coeff 0 ≠ 0) :
    (succNthDefiningPoly p n a₁ a₂ bs).IsRoot (succNthVal p n a₁ a₂ bs ha₁ ha₂) :=
  Classical.some_spec (root_exists p n a₁ a₂ bs ha₁ ha₂)

theorem succ_nth_val_spec' (n : ℕ) (a₁ a₂ : 𝕎 k) (bs : Finₓ (n + 1) → k) (ha₁ : a₁.coeff 0 ≠ 0) (ha₂ : a₂.coeff 0 ≠ 0) :
    succNthVal p n a₁ a₂ bs ha₁ ha₂ ^ p * a₁.coeff 0 ^ p ^ (n + 1) + a₁.coeff (n + 1) * (bs 0 ^ p) ^ p ^ (n + 1) +
        nthRemainder p n (fun v => bs v ^ p) (truncateFun (n + 1) a₁) =
      succNthVal p n a₁ a₂ bs ha₁ ha₂ * a₂.coeff 0 ^ p ^ (n + 1) + a₂.coeff (n + 1) * bs 0 ^ p ^ (n + 1) +
        nthRemainder p n bs (truncateFun (n + 1) a₂) :=
  by
  rw [← sub_eq_zero]
  have := succ_nth_val_spec p n a₁ a₂ bs ha₁ ha₂
  simp only [← Polynomial.map_add, ← Polynomial.eval_X, ← Polynomial.map_pow, ← Polynomial.eval_C, ←
    Polynomial.eval_pow, ← succ_nth_defining_poly, ← Polynomial.eval_mul, ← Polynomial.eval_add, ← Polynomial.eval_sub,
    ← Polynomial.map_mul, ← Polynomial.map_sub, ← Polynomial.IsRoot.def] at this
  convert this using 1
  ring

end IsAlgClosed

end RecursionMain

namespace RecursionBase

include hp

variable {k : Type _} [Field k] [IsAlgClosed k]

theorem solution_pow (a₁ a₂ : 𝕎 k) : ∃ x : k, x ^ (p - 1) = a₂.coeff 0 / a₁.coeff 0 :=
  IsAlgClosed.exists_pow_nat_eq _ <| by
    linarith [hp.out.one_lt, le_of_ltₓ hp.out.one_lt]

/-- The base case (0th coefficient) of our solution vector. -/
def solution (a₁ a₂ : 𝕎 k) : k :=
  Classical.some <| solution_pow p a₁ a₂

theorem solution_spec (a₁ a₂ : 𝕎 k) : solution p a₁ a₂ ^ (p - 1) = a₂.coeff 0 / a₁.coeff 0 :=
  Classical.some_spec <| solution_pow p a₁ a₂

theorem solution_nonzero {a₁ a₂ : 𝕎 k} (ha₁ : a₁.coeff 0 ≠ 0) (ha₂ : a₂.coeff 0 ≠ 0) : solution p a₁ a₂ ≠ 0 := by
  intro h
  have := solution_spec p a₁ a₂
  rw [h, zero_pow] at this
  · simpa [← ha₁, ← ha₂] using _root_.div_eq_zero_iff.mp this.symm
    
  · linarith [hp.out.one_lt, le_of_ltₓ hp.out.one_lt]
    

theorem solution_spec' {a₁ : 𝕎 k} (ha₁ : a₁.coeff 0 ≠ 0) (a₂ : 𝕎 k) :
    solution p a₁ a₂ ^ p * a₁.coeff 0 = solution p a₁ a₂ * a₂.coeff 0 := by
  have := solution_spec p a₁ a₂
  cases' Nat.exists_eq_succ_of_ne_zero hp.out.ne_zero with q hq
  have hq' : q = p - 1 := by
    simp only [← hq, ← tsub_zero, ← Nat.succ_sub_succ_eq_sub]
  conv_lhs => congr congr skip rw [hq]
  rw [pow_succ'ₓ, hq', this]
  field_simp [← ha₁, ← mul_comm]

end RecursionBase

open RecursionMain RecursionBase

section FrobeniusRotation

section IsAlgClosed

include hp

variable {k : Type _} [Field k] [CharP k p] [IsAlgClosed k]

/-- Recursively defines the sequence of coefficients for `witt_vector.frobenius_rotation`.
-/
noncomputable def frobeniusRotationCoeff {a₁ a₂ : 𝕎 k} (ha₁ : a₁.coeff 0 ≠ 0) (ha₂ : a₂.coeff 0 ≠ 0) : ℕ → k
  | 0 => solution p a₁ a₂
  | n + 1 => succNthVal p n a₁ a₂ (fun i => frobenius_rotation_coeff i.val) ha₁ ha₂

/-- For nonzero `a₁` and `a₂`, `frobenius_rotation a₁ a₂` is a Witt vector that satisfies the
equation `frobenius (frobenius_rotation a₁ a₂) * a₁ = (frobenius_rotation a₁ a₂) * a₂`.
-/
def frobeniusRotation {a₁ a₂ : 𝕎 k} (ha₁ : a₁.coeff 0 ≠ 0) (ha₂ : a₂.coeff 0 ≠ 0) : 𝕎 k :=
  WittVector.mk p (frobeniusRotationCoeff p ha₁ ha₂)

theorem frobenius_rotation_nonzero {a₁ a₂ : 𝕎 k} (ha₁ : a₁.coeff 0 ≠ 0) (ha₂ : a₂.coeff 0 ≠ 0) :
    frobeniusRotation p ha₁ ha₂ ≠ 0 := by
  intro h
  apply solution_nonzero p ha₁ ha₂
  simpa [h, ← frobenius_rotation, ← frobenius_rotation_coeff] using WittVector.zero_coeff p k 0

theorem frobenius_frobenius_rotation {a₁ a₂ : 𝕎 k} (ha₁ : a₁.coeff 0 ≠ 0) (ha₂ : a₂.coeff 0 ≠ 0) :
    frobenius (frobeniusRotation p ha₁ ha₂) * a₁ = frobeniusRotation p ha₁ ha₂ * a₂ := by
  ext n
  induction' n with n ih
  · simp only [← WittVector.mul_coeff_zero, ← WittVector.coeff_frobenius_char_p, ← frobenius_rotation, ←
      frobenius_rotation_coeff]
    apply solution_spec' _ ha₁
    
  · simp only [← nth_remainder_spec, ← WittVector.coeff_frobenius_char_p, ← frobenius_rotation_coeff, ←
      frobenius_rotation, ← Finₓ.val_eq_coe]
    have := succ_nth_val_spec' p n a₁ a₂ (fun i : Finₓ (n + 1) => frobenius_rotation_coeff p ha₁ ha₂ i.val) ha₁ ha₂
    simp only [← frobenius_rotation_coeff, ← Finₓ.val_eq_coe, ← Finₓ.val_zero] at this
    convert this using 4
    apply TruncatedWittVector.ext
    intro i
    simp only [← Finₓ.val_eq_coe, ← WittVector.coeff_truncate_fun, ← WittVector.coeff_frobenius_char_p]
    rfl
    

-- mathport name: «exprφ»
local notation "φ" => IsFractionRing.fieldEquivOfRingEquiv (frobeniusEquiv p k)

theorem exists_frobenius_solution_fraction_ring_aux (m n : ℕ) (r' q' : 𝕎 k) (hr' : r'.coeff 0 ≠ 0)
    (hq' : q'.coeff 0 ≠ 0) (hq : ↑p ^ n * q' ∈ nonZeroDivisors (𝕎 k)) :
    let b : 𝕎 k := frobeniusRotation p hr' hq'
    IsFractionRing.fieldEquivOfRingEquiv (frobeniusEquiv p k) (algebraMap (𝕎 k) (FractionRing (𝕎 k)) b) *
        Localization.mk (↑p ^ m * r') ⟨↑p ^ n * q', hq⟩ =
      ↑p ^ (m - n : ℤ) * algebraMap (𝕎 k) (FractionRing (𝕎 k)) b :=
  by
  intro b
  have key : WittVector.frobenius b * p ^ m * r' * p ^ n = p ^ m * b * (p ^ n * q') := by
    have H := congr_arg (fun x : 𝕎 k => x * p ^ m * p ^ n) (frobenius_frobenius_rotation p hr' hq')
    dsimp'  at H
    refine' (Eq.trans _ H).trans _ <;> ring
  have hq'' : algebraMap (𝕎 k) (FractionRing (𝕎 k)) q' ≠ 0 := by
    have hq''' : q' ≠ 0 := fun h =>
      hq'
        (by
          simp [← h])
    simpa only [← Ne.def, ← map_zero] using (IsFractionRing.injective (𝕎 k) (FractionRing (𝕎 k))).Ne hq'''
  rw [zpow_sub₀ (fraction_ring.p_nonzero p k)]
  field_simp [← fraction_ring.p_nonzero p k]
  simp only [← IsFractionRing.fieldEquivOfRingEquiv, ← IsLocalization.ring_equiv_of_ring_equiv_eq, ←
    RingEquiv.coe_of_bijective]
  convert congr_arg (fun x => algebraMap (𝕎 k) (FractionRing (𝕎 k)) x) key using 1
  · simp only [← RingHom.map_mul, ← RingHom.map_pow, ← map_nat_cast, ← frobenius_equiv_apply]
    ring
    
  · simp only [← RingHom.map_mul, ← RingHom.map_pow, ← map_nat_cast]
    

theorem exists_frobenius_solution_fraction_ring {a : FractionRing (𝕎 k)} (ha : a ≠ 0) :
    ∃ (b : FractionRing (𝕎 k))(hb : b ≠ 0)(m : ℤ), φ b * a = p ^ m * b := by
  revert ha
  refine' Localization.induction_on a _
  rintro ⟨r, q, hq⟩ hrq
  have hq0 : q ≠ 0 := mem_non_zero_divisors_iff_ne_zero.1 hq
  have hr0 : r ≠ 0 := fun h =>
    hrq
      (by
        simp [← h])
  obtain ⟨m, r', hr', rfl⟩ := exists_eq_pow_p_mul r hr0
  obtain ⟨n, q', hq', rfl⟩ := exists_eq_pow_p_mul q hq0
  let b := frobenius_rotation p hr' hq'
  refine' ⟨algebraMap (𝕎 k) _ b, _, m - n, _⟩
  · simpa only [← map_zero] using
      (IsFractionRing.injective (WittVector p k) (FractionRing (WittVector p k))).Ne
        (frobenius_rotation_nonzero p hr' hq')
    
  exact exists_frobenius_solution_fraction_ring_aux p m n r' q' hr' hq' hq

end IsAlgClosed

end FrobeniusRotation

end WittVector

