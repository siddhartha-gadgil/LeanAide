/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathbin.RingTheory.Int.Basic
import Mathbin.RingTheory.Localization.Integral

/-!
# Gauss's Lemma

Gauss's Lemma is one of a few results pertaining to irreducibility of primitive polynomials.

## Main Results
 - `polynomial.is_primitive.irreducible_iff_irreducible_map_fraction_map`:
  A primitive polynomial is irreducible iff it is irreducible in a fraction field.
 - `polynomial.is_primitive.int.irreducible_iff_irreducible_map_cast`:
  A primitive polynomial over `ℤ` is irreducible iff it is irreducible over `ℚ`.
 - `polynomial.is_primitive.dvd_iff_fraction_map_dvd_fraction_map`:
  Two primitive polynomials divide each other iff they do in a fraction field.
 - `polynomial.is_primitive.int.dvd_iff_map_cast_dvd_map_cast`:
  Two primitive polynomials over `ℤ` divide each other if they do in `ℚ`.

-/


open nonZeroDivisors Polynomial

variable {R : Type _} [CommRingₓ R] [IsDomain R]

namespace Polynomial

section NormalizedGcdMonoid

variable [NormalizedGcdMonoid R]

section

variable {S : Type _} [CommRingₓ S] [IsDomain S] {φ : R →+* S} (hinj : Function.Injective φ)

variable {f : R[X]} (hf : f.IsPrimitive)

include hinj hf

theorem IsPrimitive.is_unit_iff_is_unit_map_of_injective : IsUnit f ↔ IsUnit (map φ f) := by
  refine' ⟨(map_ring_hom φ).is_unit_map, fun h => _⟩
  rcases is_unit_iff.1 h with ⟨_, ⟨u, rfl⟩, hu⟩
  have hdeg := degree_C u.ne_zero
  rw [hu, degree_map_eq_of_injective hinj] at hdeg
  rw [eq_C_of_degree_eq_zero hdeg, is_primitive_iff_content_eq_one, content_C, normalize_eq_one] at hf
  rwa [eq_C_of_degree_eq_zero hdeg, is_unit_C]

theorem IsPrimitive.irreducible_of_irreducible_map_of_injective (h_irr : Irreducible (map φ f)) : Irreducible f := by
  refine' ⟨fun h => h_irr.not_unit (IsUnit.map (map_ring_hom φ) h), _⟩
  intro a b h
  rcases h_irr.is_unit_or_is_unit
      (by
        rw [h, Polynomial.map_mul]) with
    (hu | hu)
  · left
    rwa [(hf.is_primitive_of_dvd (Dvd.intro _ h.symm)).is_unit_iff_is_unit_map_of_injective hinj]
    
  right
  rwa [(hf.is_primitive_of_dvd (Dvd.intro_left _ h.symm)).is_unit_iff_is_unit_map_of_injective hinj]

end

section FractionMap

variable {K : Type _} [Field K] [Algebra R K] [IsFractionRing R K]

theorem IsPrimitive.is_unit_iff_is_unit_map {p : R[X]} (hp : p.IsPrimitive) :
    IsUnit p ↔ IsUnit (p.map (algebraMap R K)) :=
  hp.is_unit_iff_is_unit_map_of_injective (IsFractionRing.injective _ _)

open IsLocalization

theorem is_unit_or_eq_zero_of_is_unit_integer_normalization_prim_part {p : K[X]} (h0 : p ≠ 0)
    (h : IsUnit (integerNormalization R⁰ p).primPart) : IsUnit p := by
  rcases is_unit_iff.1 h with ⟨_, ⟨u, rfl⟩, hu⟩
  obtain ⟨⟨c, c0⟩, hc⟩ := integer_normalization_map_to_map R⁰ p
  rw [Subtype.coe_mk, Algebra.smul_def, algebra_map_apply] at hc
  apply is_unit_of_mul_is_unit_right
  rw [← hc, (integer_normalization R⁰ p).eq_C_content_mul_prim_part, ← hu, ← RingHom.map_mul, is_unit_iff]
  refine'
    ⟨algebraMap R K ((integer_normalization R⁰ p).content * ↑u), is_unit_iff_ne_zero.2 fun con => _, by
      simp ⟩
  replace con := (injective_iff_map_eq_zero (algebraMap R K)).1 (IsFractionRing.injective _ _) _ Con
  rw [mul_eq_zero, content_eq_zero_iff, IsFractionRing.integer_normalization_eq_zero_iff] at con
  rcases Con with (con | con)
  · apply h0 Con
    
  · apply Units.ne_zero _ Con
    

/-- **Gauss's Lemma** states that a primitive polynomial is irreducible iff it is irreducible in the
  fraction field. -/
theorem IsPrimitive.irreducible_iff_irreducible_map_fraction_map {p : R[X]} (hp : p.IsPrimitive) :
    Irreducible p ↔ Irreducible (p.map (algebraMap R K)) := by
  refine'
    ⟨fun hi => ⟨fun h => hi.not_unit (hp.is_unit_iff_is_unit_map.2 h), fun a b hab => _⟩,
      hp.irreducible_of_irreducible_map_of_injective (IsFractionRing.injective _ _)⟩
  obtain ⟨⟨c, c0⟩, hc⟩ := integer_normalization_map_to_map R⁰ a
  obtain ⟨⟨d, d0⟩, hd⟩ := integer_normalization_map_to_map R⁰ b
  rw [Algebra.smul_def, algebra_map_apply, Subtype.coe_mk] at hc hd
  rw [mem_non_zero_divisors_iff_ne_zero] at c0 d0
  have hcd0 : c * d ≠ 0 := mul_ne_zero c0 d0
  rw [Ne.def, ← C_eq_zero] at hcd0
  have h1 : C c * C d * p = integer_normalization R⁰ a * integer_normalization R⁰ b := by
    apply map_injective (algebraMap R K) (IsFractionRing.injective _ _) _
    rw [Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_mul, hc, hd, map_C, map_C, hab]
    ring
  obtain ⟨u, hu⟩ : Associated (c * d) (content (integer_normalization R⁰ a) * content (integer_normalization R⁰ b)) :=
    by
    rw [← dvd_dvd_iff_associated, ← normalize_eq_normalize_iff, normalize.map_mul, normalize.map_mul, normalize_content,
      normalize_content, ← mul_oneₓ (normalize c * normalize d), ← hp.content_eq_one, ← content_C, ← content_C, ←
      content_mul, ← content_mul, ← content_mul, h1]
  rw [← RingHom.map_mul, eq_comm, (integer_normalization R⁰ a).eq_C_content_mul_prim_part,
    (integer_normalization R⁰ b).eq_C_content_mul_prim_part, mul_assoc, mul_comm _ (C _ * _), ← mul_assoc, ← mul_assoc,
    ← RingHom.map_mul, ← hu, RingHom.map_mul, mul_assoc, mul_assoc, ← mul_assoc (C ↑u)] at h1
  have h0 : a ≠ 0 ∧ b ≠ 0 := by
    classical
    rw [Ne.def, Ne.def, ← Decidable.not_or_iff_and_not, ← mul_eq_zero, ← hab]
    intro con
    apply hp.ne_zero (map_injective (algebraMap R K) (IsFractionRing.injective _ _) _)
    simp [← Con]
  rcases hi.is_unit_or_is_unit (mul_left_cancel₀ hcd0 h1).symm with (h | h)
  · right
    apply is_unit_or_eq_zero_of_is_unit_integer_normalization_prim_part h0.2 (is_unit_of_mul_is_unit_right h)
    
  · left
    apply is_unit_or_eq_zero_of_is_unit_integer_normalization_prim_part h0.1 h
    

theorem IsPrimitive.dvd_of_fraction_map_dvd_fraction_map {p q : R[X]} (hp : p.IsPrimitive) (hq : q.IsPrimitive)
    (h_dvd : p.map (algebraMap R K) ∣ q.map (algebraMap R K)) : p ∣ q := by
  rcases h_dvd with ⟨r, hr⟩
  obtain ⟨⟨s, s0⟩, hs⟩ := integer_normalization_map_to_map R⁰ r
  rw [Subtype.coe_mk, Algebra.smul_def, algebra_map_apply] at hs
  have h : p ∣ q * C s := by
    use integer_normalization R⁰ r
    apply map_injective (algebraMap R K) (IsFractionRing.injective _ _)
    rw [Polynomial.map_mul, Polynomial.map_mul, hs, hr, mul_assoc, mul_comm r]
    simp
  rw [← hp.dvd_prim_part_iff_dvd, prim_part_mul, hq.prim_part_eq, Associated.dvd_iff_dvd_right] at h
  · exact h
    
  · symm
    rcases is_unit_prim_part_C s with ⟨u, hu⟩
    use u
    rw [hu]
    
  iterate 2 
    apply mul_ne_zero hq.ne_zero
    rw [Ne.def, C_eq_zero]
    contrapose! s0
    simp [← s0, ← mem_non_zero_divisors_iff_ne_zero]

variable (K)

theorem IsPrimitive.dvd_iff_fraction_map_dvd_fraction_map {p q : R[X]} (hp : p.IsPrimitive) (hq : q.IsPrimitive) :
    p ∣ q ↔ p.map (algebraMap R K) ∣ q.map (algebraMap R K) :=
  ⟨fun ⟨a, b⟩ => ⟨a.map (algebraMap R K), b.symm ▸ Polynomial.map_mul (algebraMap R K)⟩, fun h =>
    hp.dvd_of_fraction_map_dvd_fraction_map hq h⟩

end FractionMap

/-- **Gauss's Lemma** for `ℤ` states that a primitive integer polynomial is irreducible iff it is
  irreducible over `ℚ`. -/
theorem IsPrimitive.Int.irreducible_iff_irreducible_map_cast {p : ℤ[X]} (hp : p.IsPrimitive) :
    Irreducible p ↔ Irreducible (p.map (Int.castRingHom ℚ)) :=
  hp.irreducible_iff_irreducible_map_fraction_map

theorem IsPrimitive.Int.dvd_iff_map_cast_dvd_map_cast (p q : ℤ[X]) (hp : p.IsPrimitive) (hq : q.IsPrimitive) :
    p ∣ q ↔ p.map (Int.castRingHom ℚ) ∣ q.map (Int.castRingHom ℚ) :=
  hp.dvd_iff_fraction_map_dvd_fraction_map ℚ hq

end NormalizedGcdMonoid

end Polynomial

