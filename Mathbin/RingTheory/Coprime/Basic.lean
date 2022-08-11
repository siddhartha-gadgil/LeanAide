/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Ken Lee, Chris Hughes
-/
import Mathbin.Tactic.Ring
import Mathbin.Algebra.Ring.Basic
import Mathbin.GroupTheory.GroupAction.Units

/-!
# Coprime elements of a ring

## Main definitions

* `is_coprime x y`: that `x` and `y` are coprime, defined to be the existence of `a` and `b` such
that `a * x + b * y = 1`. Note that elements with no common divisors are not necessarily coprime,
e.g., the multivariate polynomials `x₁` and `x₂` are not coprime.

See also `ring_theory.coprime.lemmas` for further development of coprime elements.
-/


open Classical

universe u v

section CommSemiringₓ

variable {R : Type u} [CommSemiringₓ R] (x y z : R)

/-- The proposition that `x` and `y` are coprime, defined to be the existence of `a` and `b` such
that `a * x + b * y = 1`. Note that elements with no common divisors are not necessarily coprime,
e.g., the multivariate polynomials `x₁` and `x₂` are not coprime. -/
@[simp]
def IsCoprime : Prop :=
  ∃ a b, a * x + b * y = 1

variable {x y z}

theorem IsCoprime.symm (H : IsCoprime x y) : IsCoprime y x :=
  let ⟨a, b, H⟩ := H
  ⟨b, a, by
    rw [add_commₓ, H]⟩

theorem is_coprime_comm : IsCoprime x y ↔ IsCoprime y x :=
  ⟨IsCoprime.symm, IsCoprime.symm⟩

theorem is_coprime_self : IsCoprime x x ↔ IsUnit x :=
  ⟨fun ⟨a, b, h⟩ =>
    is_unit_of_mul_eq_one x (a + b) <| by
      rwa [mul_comm, add_mulₓ],
    fun h =>
    let ⟨b, hb⟩ := is_unit_iff_exists_inv'.1 h
    ⟨b, 0, by
      rwa [zero_mul, add_zeroₓ]⟩⟩

theorem is_coprime_zero_left : IsCoprime 0 x ↔ IsUnit x :=
  ⟨fun ⟨a, b, H⟩ =>
    is_unit_of_mul_eq_one x b <| by
      rwa [mul_zero, zero_addₓ, mul_comm] at H,
    fun H =>
    let ⟨b, hb⟩ := is_unit_iff_exists_inv'.1 H
    ⟨1, b, by
      rwa [one_mulₓ, zero_addₓ]⟩⟩

theorem is_coprime_zero_right : IsCoprime x 0 ↔ IsUnit x :=
  is_coprime_comm.trans is_coprime_zero_left

theorem not_coprime_zero_zero [Nontrivial R] : ¬IsCoprime (0 : R) 0 :=
  mt is_coprime_zero_right.mp not_is_unit_zero

/-- If a 2-vector `p` satisfies `is_coprime (p 0) (p 1)`, then `p ≠ 0`. -/
theorem IsCoprime.ne_zero [Nontrivial R] {p : Finₓ 2 → R} (h : IsCoprime (p 0) (p 1)) : p ≠ 0 := by
  rintro rfl
  exact not_coprime_zero_zero h

theorem is_coprime_one_left : IsCoprime 1 x :=
  ⟨1, 0, by
    rw [one_mulₓ, zero_mul, add_zeroₓ]⟩

theorem is_coprime_one_right : IsCoprime x 1 :=
  ⟨0, 1, by
    rw [one_mulₓ, zero_mul, zero_addₓ]⟩

theorem IsCoprime.dvd_of_dvd_mul_right (H1 : IsCoprime x z) (H2 : x ∣ y * z) : x ∣ y := by
  let ⟨a, b, H⟩ := H1
  rw [← mul_oneₓ y, ← H, mul_addₓ, ← mul_assoc, mul_left_commₓ]
  exact dvd_add (dvd_mul_left _ _) (H2.mul_left _)

theorem IsCoprime.dvd_of_dvd_mul_left (H1 : IsCoprime x y) (H2 : x ∣ y * z) : x ∣ z := by
  let ⟨a, b, H⟩ := H1
  rw [← one_mulₓ z, ← H, add_mulₓ, mul_right_commₓ, mul_assoc b]
  exact dvd_add (dvd_mul_left _ _) (H2.mul_left _)

theorem IsCoprime.mul_left (H1 : IsCoprime x z) (H2 : IsCoprime y z) : IsCoprime (x * y) z :=
  let ⟨a, b, h1⟩ := H1
  let ⟨c, d, h2⟩ := H2
  ⟨a * c, a * x * d + b * c * y + b * d * z,
    calc
      a * c * (x * y) + (a * x * d + b * c * y + b * d * z) * z = (a * x + b * z) * (c * y + d * z) := by
        ring
      _ = 1 := by
        rw [h1, h2, mul_oneₓ]
      ⟩

theorem IsCoprime.mul_right (H1 : IsCoprime x y) (H2 : IsCoprime x z) : IsCoprime x (y * z) := by
  rw [is_coprime_comm] at H1 H2⊢
  exact H1.mul_left H2

theorem IsCoprime.mul_dvd (H : IsCoprime x y) (H1 : x ∣ z) (H2 : y ∣ z) : x * y ∣ z := by
  obtain ⟨a, b, h⟩ := H
  rw [← mul_oneₓ z, ← h, mul_addₓ]
  apply dvd_add
  · rw [mul_comm z, mul_assoc]
    exact (mul_dvd_mul_left _ H2).mul_left _
    
  · rw [mul_comm b, ← mul_assoc]
    exact (mul_dvd_mul_right H1 _).mul_right _
    

theorem IsCoprime.of_mul_left_left (H : IsCoprime (x * y) z) : IsCoprime x z :=
  let ⟨a, b, h⟩ := H
  ⟨a * y, b, by
    rwa [mul_right_commₓ, mul_assoc]⟩

theorem IsCoprime.of_mul_left_right (H : IsCoprime (x * y) z) : IsCoprime y z := by
  rw [mul_comm] at H
  exact H.of_mul_left_left

theorem IsCoprime.of_mul_right_left (H : IsCoprime x (y * z)) : IsCoprime x y := by
  rw [is_coprime_comm] at H⊢
  exact H.of_mul_left_left

theorem IsCoprime.of_mul_right_right (H : IsCoprime x (y * z)) : IsCoprime x z := by
  rw [mul_comm] at H
  exact H.of_mul_right_left

theorem IsCoprime.mul_left_iff : IsCoprime (x * y) z ↔ IsCoprime x z ∧ IsCoprime y z :=
  ⟨fun H => ⟨H.of_mul_left_left, H.of_mul_left_right⟩, fun ⟨H1, H2⟩ => H1.mul_left H2⟩

theorem IsCoprime.mul_right_iff : IsCoprime x (y * z) ↔ IsCoprime x y ∧ IsCoprime x z := by
  rw [is_coprime_comm, IsCoprime.mul_left_iff, is_coprime_comm, @is_coprime_comm _ _ z]

theorem IsCoprime.of_coprime_of_dvd_left (h : IsCoprime y z) (hdvd : x ∣ y) : IsCoprime x z := by
  obtain ⟨d, rfl⟩ := hdvd
  exact IsCoprime.of_mul_left_left h

theorem IsCoprime.of_coprime_of_dvd_right (h : IsCoprime z y) (hdvd : x ∣ y) : IsCoprime z x :=
  (h.symm.of_coprime_of_dvd_left hdvd).symm

theorem IsCoprime.is_unit_of_dvd (H : IsCoprime x y) (d : x ∣ y) : IsUnit x :=
  let ⟨k, hk⟩ := d
  is_coprime_self.1 <| IsCoprime.of_mul_right_left <| show IsCoprime x (x * k) from hk ▸ H

theorem IsCoprime.is_unit_of_dvd' {a b x : R} (h : IsCoprime a b) (ha : x ∣ a) (hb : x ∣ b) : IsUnit x :=
  (h.of_coprime_of_dvd_left ha).is_unit_of_dvd hb

theorem IsCoprime.map (H : IsCoprime x y) {S : Type v} [CommSemiringₓ S] (f : R →+* S) : IsCoprime (f x) (f y) :=
  let ⟨a, b, h⟩ := H
  ⟨f a, f b, by
    rw [← f.map_mul, ← f.map_mul, ← f.map_add, h, f.map_one]⟩

variable {x y z}

theorem IsCoprime.of_add_mul_left_left (h : IsCoprime (x + y * z) y) : IsCoprime x y :=
  let ⟨a, b, H⟩ := h
  ⟨a, a * z + b, by
    simpa only [← add_mulₓ, ← mul_addₓ, ← add_assocₓ, ← add_commₓ, ← add_left_commₓ, ← mul_assoc, ← mul_comm, ←
      mul_left_commₓ] using H⟩

theorem IsCoprime.of_add_mul_right_left (h : IsCoprime (x + z * y) y) : IsCoprime x y := by
  rw [mul_comm] at h
  exact h.of_add_mul_left_left

theorem IsCoprime.of_add_mul_left_right (h : IsCoprime x (y + x * z)) : IsCoprime x y := by
  rw [is_coprime_comm] at h⊢
  exact h.of_add_mul_left_left

theorem IsCoprime.of_add_mul_right_right (h : IsCoprime x (y + z * x)) : IsCoprime x y := by
  rw [mul_comm] at h
  exact h.of_add_mul_left_right

theorem IsCoprime.of_mul_add_left_left (h : IsCoprime (y * z + x) y) : IsCoprime x y := by
  rw [add_commₓ] at h
  exact h.of_add_mul_left_left

theorem IsCoprime.of_mul_add_right_left (h : IsCoprime (z * y + x) y) : IsCoprime x y := by
  rw [add_commₓ] at h
  exact h.of_add_mul_right_left

theorem IsCoprime.of_mul_add_left_right (h : IsCoprime x (x * z + y)) : IsCoprime x y := by
  rw [add_commₓ] at h
  exact h.of_add_mul_left_right

theorem IsCoprime.of_mul_add_right_right (h : IsCoprime x (z * x + y)) : IsCoprime x y := by
  rw [add_commₓ] at h
  exact h.of_add_mul_right_right

end CommSemiringₓ

section ScalarTower

variable {R G : Type _} [CommSemiringₓ R] [Groupₓ G] [MulAction G R] [SmulCommClass G R R] [IsScalarTower G R R] (x : G)
  (y z : R)

theorem is_coprime_group_smul_left : IsCoprime (x • y) z ↔ IsCoprime y z :=
  ⟨fun ⟨a, b, h⟩ =>
    ⟨x • a, b, by
      rwa [smul_mul_assoc, ← mul_smul_comm]⟩,
    fun ⟨a, b, h⟩ =>
    ⟨x⁻¹ • a, b, by
      rwa [smul_mul_smul, inv_mul_selfₓ, one_smul]⟩⟩

theorem is_coprime_group_smul_right : IsCoprime y (x • z) ↔ IsCoprime y z :=
  is_coprime_comm.trans <| (is_coprime_group_smul_left x z y).trans is_coprime_comm

theorem is_coprime_group_smul : IsCoprime (x • y) (x • z) ↔ IsCoprime y z :=
  (is_coprime_group_smul_left x y (x • z)).trans (is_coprime_group_smul_right x y z)

end ScalarTower

section CommSemiringUnit

variable {R : Type _} [CommSemiringₓ R] {x : R} (hu : IsUnit x) (y z : R)

theorem is_coprime_mul_unit_left_left : IsCoprime (x * y) z ↔ IsCoprime y z :=
  let ⟨u, hu⟩ := hu
  hu ▸ is_coprime_group_smul_left u y z

theorem is_coprime_mul_unit_left_right : IsCoprime y (x * z) ↔ IsCoprime y z :=
  let ⟨u, hu⟩ := hu
  hu ▸ is_coprime_group_smul_right u y z

theorem is_coprime_mul_unit_left : IsCoprime (x * y) (x * z) ↔ IsCoprime y z :=
  (is_coprime_mul_unit_left_left hu y (x * z)).trans (is_coprime_mul_unit_left_right hu y z)

theorem is_coprime_mul_unit_right_left : IsCoprime (y * x) z ↔ IsCoprime y z :=
  mul_comm x y ▸ is_coprime_mul_unit_left_left hu y z

theorem is_coprime_mul_unit_right_right : IsCoprime y (z * x) ↔ IsCoprime y z :=
  mul_comm x z ▸ is_coprime_mul_unit_left_right hu y z

theorem is_coprime_mul_unit_right : IsCoprime (y * x) (z * x) ↔ IsCoprime y z :=
  (is_coprime_mul_unit_right_left hu y (z * x)).trans (is_coprime_mul_unit_right_right hu y z)

end CommSemiringUnit

namespace IsCoprime

section CommRingₓ

variable {R : Type u} [CommRingₓ R]

theorem add_mul_left_left {x y : R} (h : IsCoprime x y) (z : R) : IsCoprime (x + y * z) y :=
  @of_add_mul_left_left R _ _ _ (-z) <| by
    simpa only [← mul_neg, ← add_neg_cancel_rightₓ] using h

theorem add_mul_right_left {x y : R} (h : IsCoprime x y) (z : R) : IsCoprime (x + z * y) y := by
  rw [mul_comm]
  exact h.add_mul_left_left z

theorem add_mul_left_right {x y : R} (h : IsCoprime x y) (z : R) : IsCoprime x (y + x * z) := by
  rw [is_coprime_comm]
  exact h.symm.add_mul_left_left z

theorem add_mul_right_right {x y : R} (h : IsCoprime x y) (z : R) : IsCoprime x (y + z * x) := by
  rw [is_coprime_comm]
  exact h.symm.add_mul_right_left z

theorem mul_add_left_left {x y : R} (h : IsCoprime x y) (z : R) : IsCoprime (y * z + x) y := by
  rw [add_commₓ]
  exact h.add_mul_left_left z

theorem mul_add_right_left {x y : R} (h : IsCoprime x y) (z : R) : IsCoprime (z * y + x) y := by
  rw [add_commₓ]
  exact h.add_mul_right_left z

theorem mul_add_left_right {x y : R} (h : IsCoprime x y) (z : R) : IsCoprime x (x * z + y) := by
  rw [add_commₓ]
  exact h.add_mul_left_right z

theorem mul_add_right_right {x y : R} (h : IsCoprime x y) (z : R) : IsCoprime x (z * x + y) := by
  rw [add_commₓ]
  exact h.add_mul_right_right z

theorem add_mul_left_left_iff {x y z : R} : IsCoprime (x + y * z) y ↔ IsCoprime x y :=
  ⟨of_add_mul_left_left, fun h => h.add_mul_left_left z⟩

theorem add_mul_right_left_iff {x y z : R} : IsCoprime (x + z * y) y ↔ IsCoprime x y :=
  ⟨of_add_mul_right_left, fun h => h.add_mul_right_left z⟩

theorem add_mul_left_right_iff {x y z : R} : IsCoprime x (y + x * z) ↔ IsCoprime x y :=
  ⟨of_add_mul_left_right, fun h => h.add_mul_left_right z⟩

theorem add_mul_right_right_iff {x y z : R} : IsCoprime x (y + z * x) ↔ IsCoprime x y :=
  ⟨of_add_mul_right_right, fun h => h.add_mul_right_right z⟩

theorem mul_add_left_left_iff {x y z : R} : IsCoprime (y * z + x) y ↔ IsCoprime x y :=
  ⟨of_mul_add_left_left, fun h => h.mul_add_left_left z⟩

theorem mul_add_right_left_iff {x y z : R} : IsCoprime (z * y + x) y ↔ IsCoprime x y :=
  ⟨of_mul_add_right_left, fun h => h.mul_add_right_left z⟩

theorem mul_add_left_right_iff {x y z : R} : IsCoprime x (x * z + y) ↔ IsCoprime x y :=
  ⟨of_mul_add_left_right, fun h => h.mul_add_left_right z⟩

theorem mul_add_right_right_iff {x y z : R} : IsCoprime x (z * x + y) ↔ IsCoprime x y :=
  ⟨of_mul_add_right_right, fun h => h.mul_add_right_right z⟩

theorem neg_left {x y : R} (h : IsCoprime x y) : IsCoprime (-x) y := by
  obtain ⟨a, b, h⟩ := h
  use -a, b
  rwa [neg_mul_neg]

theorem neg_left_iff (x y : R) : IsCoprime (-x) y ↔ IsCoprime x y :=
  ⟨fun h => neg_negₓ x ▸ h.neg_left, neg_left⟩

theorem neg_right {x y : R} (h : IsCoprime x y) : IsCoprime x (-y) :=
  h.symm.neg_left.symm

theorem neg_right_iff (x y : R) : IsCoprime x (-y) ↔ IsCoprime x y :=
  ⟨fun h => neg_negₓ y ▸ h.neg_right, neg_right⟩

theorem neg_neg {x y : R} (h : IsCoprime x y) : IsCoprime (-x) (-y) :=
  h.neg_left.neg_right

theorem neg_neg_iff (x y : R) : IsCoprime (-x) (-y) ↔ IsCoprime x y :=
  (neg_left_iff _ _).trans (neg_right_iff _ _)

end CommRingₓ

theorem sq_add_sq_ne_zero {R : Type _} [LinearOrderedCommRing R] {a b : R} (h : IsCoprime a b) : a ^ 2 + b ^ 2 ≠ 0 := by
  intro h'
  obtain ⟨ha, hb⟩ := (add_eq_zero_iff' (sq_nonneg a) (sq_nonneg b)).mp h'
  obtain rfl := pow_eq_zero ha
  obtain rfl := pow_eq_zero hb
  exact not_coprime_zero_zero h

end IsCoprime

