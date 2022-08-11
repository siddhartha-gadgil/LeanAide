/-
Copyright (c) 2022 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata
-/
import Mathbin.FieldTheory.SplittingField

/-!
# Cubics and discriminants

This file defines cubic polynomials over a semiring and their discriminants over a splitting field.

## Main definitions

* `cubic`: the structure representing a cubic polynomial.
* `disc`: the discriminant of a cubic polynomial.

## Main statements

* `disc_ne_zero_iff_roots_nodup`: the cubic discriminant is not equal to zero if and only if
  the cubic has no duplicate roots.

## References

* https://en.wikipedia.org/wiki/Cubic_equation
* https://en.wikipedia.org/wiki/Discriminant

## Tags

cubic, discriminant, polynomial, root
-/


noncomputable section

/-- The structure representing a cubic polynomial. -/
@[ext]
structure Cubic (R : Type _) where
  (a b c d : R)

namespace Cubic

open Cubic Polynomial

open Polynomial

variable {R S F K : Type _}

instance [Inhabited R] : Inhabited (Cubic R) :=
  ⟨⟨default, default, default, default⟩⟩

instance [Zero R] : Zero (Cubic R) :=
  ⟨⟨0, 0, 0, 0⟩⟩

section Basic

variable {P : Cubic R} [Semiringₓ R]

/-- Convert a cubic polynomial to a polynomial. -/
def toPoly (P : Cubic R) : R[X] :=
  c P.a * X ^ 3 + c P.b * X ^ 2 + c P.c * X + c P.d

/-! ### Coefficients -/


section Coeff

-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:51:50: missing argument
private theorem coeffs :
    (∀, ∀ n > 3, ∀, P.toPoly.coeff n = 0) ∧
      P.toPoly.coeff 3 = P.a ∧ P.toPoly.coeff 2 = P.b ∧ P.toPoly.coeff 1 = P.c ∧ P.toPoly.coeff 0 = P.d :=
  by
  simp only [← to_poly, ← coeff_add, ← coeff_C, ← coeff_C_mul_X, ← coeff_C_mul_X_pow]
  norm_num
  intro n hn
  repeat'
    rw [if_neg]
  any_goals {
  }
  repeat'
    rw [zero_addₓ]

@[simp]
theorem coeff_gt_three (n : ℕ) (hn : 3 < n) : P.toPoly.coeff n = 0 :=
  coeffs.1 n hn

@[simp]
theorem coeff_three : P.toPoly.coeff 3 = P.a :=
  coeffs.2.1

@[simp]
theorem coeff_two : P.toPoly.coeff 2 = P.b :=
  coeffs.2.2.1

@[simp]
theorem coeff_one : P.toPoly.coeff 1 = P.c :=
  coeffs.2.2.2.1

@[simp]
theorem coeff_zero : P.toPoly.coeff 0 = P.d :=
  coeffs.2.2.2.2

theorem a_of_eq {Q : Cubic R} (h : P.toPoly = Q.toPoly) : P.a = Q.a := by
  rw [← coeff_three, h, coeff_three]

theorem b_of_eq {Q : Cubic R} (h : P.toPoly = Q.toPoly) : P.b = Q.b := by
  rw [← coeff_two, h, coeff_two]

theorem c_of_eq {Q : Cubic R} (h : P.toPoly = Q.toPoly) : P.c = Q.c := by
  rw [← coeff_one, h, coeff_one]

theorem d_of_eq {Q : Cubic R} (h : P.toPoly = Q.toPoly) : P.d = Q.d := by
  rw [← coeff_zero, h, coeff_zero]

@[simp]
theorem to_poly_injective (P Q : Cubic R) : P.toPoly = Q.toPoly ↔ P = Q :=
  ⟨fun h => Cubic.ext _ _ (a_of_eq h) (b_of_eq h) (c_of_eq h) (d_of_eq h), congr_arg _⟩

@[simp]
theorem of_a_eq_zero (ha : P.a = 0) : P.toPoly = c P.b * X ^ 2 + c P.c * X + c P.d := by
  rw [to_poly, C_eq_zero.mpr ha, zero_mul, zero_addₓ]

@[simp]
theorem of_a_b_eq_zero (ha : P.a = 0) (hb : P.b = 0) : P.toPoly = c P.c * X + c P.d := by
  rw [of_a_eq_zero ha, C_eq_zero.mpr hb, zero_mul, zero_addₓ]

@[simp]
theorem of_a_b_c_eq_zero (ha : P.a = 0) (hb : P.b = 0) (hc : P.c = 0) : P.toPoly = c P.d := by
  rw [of_a_b_eq_zero ha hb, C_eq_zero.mpr hc, zero_mul, zero_addₓ]

@[simp]
theorem of_zero (ha : P.a = 0) (hb : P.b = 0) (hc : P.c = 0) (hd : P.d = 0) : P.toPoly = 0 := by
  rw [of_a_b_c_eq_zero ha hb hc, C_eq_zero.mpr hd]

@[simp]
theorem zero : (0 : Cubic R).toPoly = 0 :=
  of_zero rfl rfl rfl rfl

@[simp]
theorem eq_zero_iff : P.toPoly = 0 ↔ P = 0 := by
  rw [← zero, to_poly_injective]

theorem ne_zero (h0 : ¬P.a = 0 ∨ ¬P.b = 0 ∨ ¬P.c = 0 ∨ ¬P.d = 0) : P.toPoly ≠ 0 := by
  contrapose! h0
  rw [eq_zero_iff.mp h0]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem ne_zero_of_a_ne_zero (ha : P.a ≠ 0) : P.toPoly ≠ 0 :=
  (or_imp_distrib.mp ne_zero).1 ha

theorem ne_zero_of_b_ne_zero (hb : P.b ≠ 0) : P.toPoly ≠ 0 :=
  (or_imp_distrib.mp (or_imp_distrib.mp ne_zero).2).1 hb

theorem ne_zero_of_c_ne_zero (hc : P.c ≠ 0) : P.toPoly ≠ 0 :=
  (or_imp_distrib.mp (or_imp_distrib.mp (or_imp_distrib.mp ne_zero).2).2).1 hc

theorem ne_zero_of_d_ne_zero (hd : P.d ≠ 0) : P.toPoly ≠ 0 :=
  (or_imp_distrib.mp (or_imp_distrib.mp (or_imp_distrib.mp ne_zero).2).2).2 hd

end Coeff

/-! ### Degrees -/


section Degree

/-- The equivalence between cubic polynomials and polynomials of degree at most three. -/
@[simps]
def equiv : Cubic R ≃ { p : R[X] // p.degree ≤ 3 } where
  toFun := fun P => ⟨P.toPoly, degree_cubic_le⟩
  invFun := fun f => ⟨coeff f 3, coeff f 2, coeff f 1, coeff f 0⟩
  left_inv := fun P => by
    ext <;> simp only [← Subtype.coe_mk, ← coeffs]
  right_inv := fun f => by
    ext (_ | _ | _ | _ | n) <;> simp only [← Subtype.coe_mk, ← coeffs]
    have h3 : 3 < n + 4 := by
      linarith only
    rw [coeff_gt_three _ h3, (degree_le_iff_coeff_zero (f : R[X]) 3).mp f.2 _ <| with_bot.coe_lt_coe.mpr h3]

theorem degree (ha : P.a ≠ 0) : P.toPoly.degree = 3 :=
  degree_cubic ha

theorem degree_of_a_eq_zero (ha : P.a = 0) (hb : P.b ≠ 0) : P.toPoly.degree = 2 := by
  rw [of_a_eq_zero ha, degree_quadratic hb]

theorem degree_of_a_b_eq_zero (ha : P.a = 0) (hb : P.b = 0) (hc : P.c ≠ 0) : P.toPoly.degree = 1 := by
  rw [of_a_b_eq_zero ha hb, degree_linear hc]

theorem degree_of_a_b_c_eq_zero (ha : P.a = 0) (hb : P.b = 0) (hc : P.c = 0) (hd : P.d ≠ 0) : P.toPoly.degree = 0 := by
  rw [of_a_b_c_eq_zero ha hb hc, degree_C hd]

theorem degree_of_zero (ha : P.a = 0) (hb : P.b = 0) (hc : P.c = 0) (hd : P.d = 0) : P.toPoly.degree = ⊥ := by
  rw [of_zero ha hb hc hd, degree_zero]

theorem leading_coeff (ha : P.a ≠ 0) : P.toPoly.leadingCoeff = P.a :=
  leading_coeff_cubic ha

theorem leading_coeff_of_a_eq_zero (ha : P.a = 0) (hb : P.b ≠ 0) : P.toPoly.leadingCoeff = P.b := by
  rw [of_a_eq_zero ha, leading_coeff_quadratic hb]

theorem leading_coeff_of_a_b_eq_zero (ha : P.a = 0) (hb : P.b = 0) (hc : P.c ≠ 0) : P.toPoly.leadingCoeff = P.c := by
  rw [of_a_b_eq_zero ha hb, leading_coeff_linear hc]

theorem leading_coeff_of_a_b_c_eq_zero (ha : P.a = 0) (hb : P.b = 0) (hc : P.c = 0) : P.toPoly.leadingCoeff = P.d := by
  rw [of_a_b_c_eq_zero ha hb hc, leading_coeff_C]

end Degree

/-! ### Map across a homomorphism -/


section Map

variable [Semiringₓ S] {φ : R →+* S}

/-- Map a cubic polynomial across a semiring homomorphism. -/
def map (φ : R →+* S) (P : Cubic R) : Cubic S :=
  ⟨φ P.a, φ P.b, φ P.c, φ P.d⟩

theorem map_to_poly : (map φ P).toPoly = Polynomial.map φ P.toPoly := by
  simp only [← map, ← to_poly, ← map_C, ← map_X, ← Polynomial.map_add, ← Polynomial.map_mul, ← Polynomial.map_pow]

end Map

end Basic

section Roots

open Multiset

/-! ### Roots over an extension -/


section Extension

variable {P : Cubic R} [CommRingₓ R] [CommRingₓ S] {φ : R →+* S}

/-- The roots of a cubic polynomial. -/
def roots [IsDomain R] (P : Cubic R) : Multiset R :=
  P.toPoly.roots

theorem map_roots [IsDomain S] : (map φ P).roots = (Polynomial.map φ P.toPoly).roots := by
  rw [roots, map_to_poly]

theorem mem_roots_iff [IsDomain R] (h0 : P.toPoly ≠ 0) (x : R) :
    x ∈ P.roots ↔ P.a * x ^ 3 + P.b * x ^ 2 + P.c * x + P.d = 0 := by
  rw [roots, mem_roots h0, is_root, to_poly]
  simp only [← eval_C, ← eval_X, ← eval_add, ← eval_mul, ← eval_pow]

theorem card_roots_le [IsDomain R] [DecidableEq R] : P.roots.toFinset.card ≤ 3 := by
  apply (to_finset_card_le P.to_poly.roots).trans
  by_cases' hP : P.to_poly = 0
  · exact
      (card_roots' P.to_poly).trans
        (by
          rw [hP, nat_degree_zero]
          exact zero_le 3)
    
  · exact WithBot.coe_le_coe.1 ((card_roots hP).trans degree_cubic_le)
    

end Extension

variable {P : Cubic F} [Field F] [Field K] {φ : F →+* K} {x y z : K}

/-! ### Roots over a splitting field -/


section Split

theorem splits_iff_card_roots (ha : P.a ≠ 0) : Splits φ P.toPoly ↔ (map φ P).roots.card = 3 := by
  replace ha : (map φ P).a ≠ 0 := (RingHom.map_ne_zero φ).mpr ha
  nth_rw_lhs 0[← RingHom.id_comp φ]
  rw [roots, ← splits_map_iff, ← map_to_poly, splits_iff_card_roots, ←
    ((degree_eq_iff_nat_degree_eq <| ne_zero_of_a_ne_zero ha).mp <| degree ha : _ = 3)]

theorem splits_iff_roots_eq_three (ha : P.a ≠ 0) : Splits φ P.toPoly ↔ ∃ x y z : K, (map φ P).roots = {x, y, z} := by
  rw [splits_iff_card_roots ha, card_eq_three]

theorem eq_prod_three_roots (ha : P.a ≠ 0) (h3 : (map φ P).roots = {x, y, z}) :
    (map φ P).toPoly = c (φ P.a) * (X - c x) * (X - c y) * (X - c z) := by
  rw [map_to_poly,
    eq_prod_roots_of_splits <|
      (splits_iff_roots_eq_three ha).mpr <| Exists.introₓ x <| Exists.introₓ y <| Exists.introₓ z h3,
    leading_coeff ha, ← map_roots, h3]
  change C (φ P.a) * ((X - C x) ::ₘ (X - C y) ::ₘ {X - C z}).Prod = _
  rw [prod_cons, prod_cons, prod_singleton, mul_assoc, mul_assoc]

-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:51:50: missing argument
theorem eq_sum_three_roots (ha : P.a ≠ 0) (h3 : (map φ P).roots = {x, y, z}) :
    map φ P = ⟨φ P.a, φ P.a * -(x + y + z), φ P.a * (x * y + x * z + y * z), φ P.a * -(x * y * z)⟩ := by
  apply_fun to_poly
  any_goals {
  }
  rw [eq_prod_three_roots ha h3, to_poly]
  simp only [← C_neg, ← C_add, ← C_mul]
  ring1

theorem b_eq_three_roots (ha : P.a ≠ 0) (h3 : (map φ P).roots = {x, y, z}) : φ P.b = φ P.a * -(x + y + z) := by
  injection eq_sum_three_roots ha h3

theorem c_eq_three_roots (ha : P.a ≠ 0) (h3 : (map φ P).roots = {x, y, z}) : φ P.c = φ P.a * (x * y + x * z + y * z) :=
  by
  injection eq_sum_three_roots ha h3

theorem d_eq_three_roots (ha : P.a ≠ 0) (h3 : (map φ P).roots = {x, y, z}) : φ P.d = φ P.a * -(x * y * z) := by
  injection eq_sum_three_roots ha h3

end Split

/-! ### Discriminant over a splitting field -/


section Discriminant

/-- The discriminant of a cubic polynomial. -/
def disc {R : Type _} [Ringₓ R] (P : Cubic R) : R :=
  P.b ^ 2 * P.c ^ 2 - 4 * P.a * P.c ^ 3 - 4 * P.b ^ 3 * P.d - 27 * P.a ^ 2 * P.d ^ 2 + 18 * P.a * P.b * P.c * P.d

theorem disc_eq_prod_three_roots (ha : P.a ≠ 0) (h3 : (map φ P).roots = {x, y, z}) :
    φ P.disc = (φ P.a * φ P.a * (x - y) * (x - z) * (y - z)) ^ 2 := by
  simp only [← disc, ← RingHom.map_add, ← RingHom.map_sub, ← RingHom.map_mul, ← map_pow]
  simp only [← RingHom.map_one, ← map_bit0, ← map_bit1]
  rw [b_eq_three_roots ha h3, c_eq_three_roots ha h3, d_eq_three_roots ha h3]
  ring1

theorem disc_ne_zero_iff_roots_ne (ha : P.a ≠ 0) (h3 : (map φ P).roots = {x, y, z}) :
    P.disc ≠ 0 ↔ x ≠ y ∧ x ≠ z ∧ y ≠ z := by
  rw [← RingHom.map_ne_zero φ, disc_eq_prod_three_roots ha h3, pow_two]
  simp only [← mul_ne_zero_iff, ← sub_ne_zero]
  rw [RingHom.map_ne_zero]
  tauto

theorem disc_ne_zero_iff_roots_nodup (ha : P.a ≠ 0) (h3 : (map φ P).roots = {x, y, z}) :
    P.disc ≠ 0 ↔ (map φ P).roots.Nodup := by
  rw [disc_ne_zero_iff_roots_ne ha h3, h3]
  change _ ↔ (x ::ₘ y ::ₘ {z}).Nodup
  rw [nodup_cons, nodup_cons, mem_cons, mem_singleton, mem_singleton]
  simp only [← nodup_singleton]
  tauto

theorem card_roots_of_disc_ne_zero [DecidableEq K] (ha : P.a ≠ 0) (h3 : (map φ P).roots = {x, y, z}) (hd : P.disc ≠ 0) :
    (map φ P).roots.toFinset.card = 3 := by
  rw [to_finset_card_of_nodup <| (disc_ne_zero_iff_roots_nodup ha h3).mp hd, ← splits_iff_card_roots ha,
    splits_iff_roots_eq_three ha]
  exact ⟨x, ⟨y, ⟨z, h3⟩⟩⟩

end Discriminant

end Roots

end Cubic

