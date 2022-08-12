/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Amelia Livingston, Yury Kudryashov,
Neil Strickland, Aaron Anderson
-/
import Mathbin.Algebra.GroupWithZero.Basic

/-!
# Divisibility

This file defines the basics of the divisibility relation in the context of `(comm_)` `monoid`s
`(_with_zero)`.

## Main definitions

 * `monoid.has_dvd`

## Implementation notes

The divisibility relation is defined for all monoids, and as such, depends on the order of
  multiplication if the monoid is not commutative. There are two possible conventions for
  divisibility in the noncommutative context, and this relation follows the convention for ordinals,
  so `a | b` is defined as `∃ c, b = a * c`.

## Tags

divisibility, divides
-/


variable {α : Type _}

section Semigroupₓ

variable [Semigroupₓ α] {a b c : α}

/-- There are two possible conventions for divisibility, which coincide in a `comm_monoid`.
    This matches the convention for ordinals. -/
instance (priority := 100) semigroupHasDvd : Dvd α :=
  Dvd.mk fun a b => ∃ c, b = a * c

-- TODO: this used to not have `c` explicit, but that seems to be important
--       for use with tactics, similar to `exists.intro`
theorem Dvd.intro (c : α) (h : a * c = b) : a ∣ b :=
  Exists.introₓ c h

alias Dvd.intro ← dvd_of_mul_right_eq

theorem exists_eq_mul_right_of_dvd (h : a ∣ b) : ∃ c, b = a * c :=
  h

theorem Dvd.elim {P : Prop} {a b : α} (H₁ : a ∣ b) (H₂ : ∀ c, b = a * c → P) : P :=
  Exists.elim H₁ H₂

attribute [local simp] mul_assoc mul_comm mul_left_commₓ

@[trans]
theorem dvd_trans : a ∣ b → b ∣ c → a ∣ c
  | ⟨d, h₁⟩, ⟨e, h₂⟩ => ⟨d * e, h₁ ▸ h₂.trans <| mul_assoc a d e⟩

alias dvd_trans ← Dvd.Dvd.trans

instance : IsTrans α (· ∣ ·) :=
  ⟨fun a b c => dvd_trans⟩

@[simp]
theorem dvd_mul_right (a b : α) : a ∣ a * b :=
  Dvd.intro b rfl

theorem dvd_mul_of_dvd_left (h : a ∣ b) (c : α) : a ∣ b * c :=
  h.trans (dvd_mul_right b c)

alias dvd_mul_of_dvd_left ← Dvd.Dvd.mul_right

theorem dvd_of_mul_right_dvd (h : a * b ∣ c) : a ∣ c :=
  (dvd_mul_right a b).trans h

section map_dvd

variable {M N : Type _} [Monoidₓ M] [Monoidₓ N]

theorem map_dvd {F : Type _} [MulHomClass F M N] (f : F) {a b} : a ∣ b → f a ∣ f b
  | ⟨c, h⟩ => ⟨f c, h.symm ▸ map_mul f a c⟩

theorem MulHom.map_dvd (f : M →ₙ* N) {a b} : a ∣ b → f a ∣ f b :=
  map_dvd f

theorem MonoidHom.map_dvd (f : M →* N) {a b} : a ∣ b → f a ∣ f b :=
  map_dvd f

end map_dvd

end Semigroupₓ

section Monoidₓ

variable [Monoidₓ α]

@[refl, simp]
theorem dvd_refl (a : α) : a ∣ a :=
  Dvd.intro 1 (mul_oneₓ a)

theorem dvd_rfl : ∀ {a : α}, a ∣ a :=
  dvd_refl

instance : IsRefl α (· ∣ ·) :=
  ⟨dvd_refl⟩

theorem one_dvd (a : α) : 1 ∣ a :=
  Dvd.intro a (one_mulₓ a)

end Monoidₓ

section CommSemigroupₓ

variable [CommSemigroupₓ α] {a b c : α}

theorem Dvd.intro_left (c : α) (h : c * a = b) : a ∣ b :=
  Dvd.intro _
    (by
      rw [mul_comm] at h
      apply h)

alias Dvd.intro_left ← dvd_of_mul_left_eq

theorem exists_eq_mul_left_of_dvd (h : a ∣ b) : ∃ c, b = c * a :=
  Dvd.elim h fun c => fun H1 : b = a * c => Exists.introₓ c (Eq.trans H1 (mul_comm a c))

theorem dvd_iff_exists_eq_mul_left : a ∣ b ↔ ∃ c, b = c * a :=
  ⟨exists_eq_mul_left_of_dvd, by
    rintro ⟨c, rfl⟩
    exact ⟨c, mul_comm _ _⟩⟩

theorem Dvd.elim_left {P : Prop} (h₁ : a ∣ b) (h₂ : ∀ c, b = c * a → P) : P :=
  Exists.elim (exists_eq_mul_left_of_dvd h₁) fun c => fun h₃ : b = c * a => h₂ c h₃

@[simp]
theorem dvd_mul_left (a b : α) : a ∣ b * a :=
  Dvd.intro b (mul_comm a b)

theorem dvd_mul_of_dvd_right (h : a ∣ b) (c : α) : a ∣ c * b := by
  rw [mul_comm]
  exact h.mul_right _

alias dvd_mul_of_dvd_right ← Dvd.Dvd.mul_left

attribute [local simp] mul_assoc mul_comm mul_left_commₓ

theorem mul_dvd_mul : ∀ {a b c d : α}, a ∣ b → c ∣ d → a * c ∣ b * d
  | a, _, c, _, ⟨e, rfl⟩, ⟨f, rfl⟩ =>
    ⟨e * f, by
      simp ⟩

theorem dvd_of_mul_left_dvd (h : a * b ∣ c) : b ∣ c :=
  Dvd.elim h fun d ceq =>
    Dvd.intro (a * d)
      (by
        simp [← ceq])

end CommSemigroupₓ

section CommMonoidₓ

variable [CommMonoidₓ α] {a b : α}

theorem mul_dvd_mul_left (a : α) {b c : α} (h : b ∣ c) : a * b ∣ a * c :=
  mul_dvd_mul (dvd_refl a) h

theorem mul_dvd_mul_right (h : a ∣ b) (c : α) : a * c ∣ b * c :=
  mul_dvd_mul h (dvd_refl c)

end CommMonoidₓ

section SemigroupWithZeroₓ

variable [SemigroupWithZeroₓ α] {a : α}

theorem eq_zero_of_zero_dvd (h : 0 ∣ a) : a = 0 :=
  Dvd.elim h fun c H' => H'.trans (zero_mul c)

/-- Given an element `a` of a commutative semigroup with zero, there exists another element whose
    product with zero equals `a` iff `a` equals zero. -/
@[simp]
theorem zero_dvd_iff : 0 ∣ a ↔ a = 0 :=
  ⟨eq_zero_of_zero_dvd, fun h => by
    rw [h]
    use 0
    simp ⟩

@[simp]
theorem dvd_zero (a : α) : a ∣ 0 :=
  Dvd.intro 0
    (by
      simp )

end SemigroupWithZeroₓ

/-- Given two elements `b`, `c` of a `cancel_monoid_with_zero` and a nonzero element `a`,
 `a*b` divides `a*c` iff `b` divides `c`. -/
theorem mul_dvd_mul_iff_left [CancelMonoidWithZero α] {a b c : α} (ha : a ≠ 0) : a * b ∣ a * c ↔ b ∣ c :=
  exists_congr fun d => by
    rw [mul_assoc, mul_right_inj' ha]

/-- Given two elements `a`, `b` of a commutative `cancel_monoid_with_zero` and a nonzero
  element `c`, `a*c` divides `b*c` iff `a` divides `b`. -/
theorem mul_dvd_mul_iff_right [CancelCommMonoidWithZero α] {a b c : α} (hc : c ≠ 0) : a * c ∣ b * c ↔ a ∣ b :=
  exists_congr fun d => by
    rw [mul_right_commₓ, mul_left_inj' hc]

/-!
### Units in various monoids
-/


namespace Units

section Monoidₓ

variable [Monoidₓ α] {a b : α} {u : αˣ}

/-- Elements of the unit group of a monoid represented as elements of the monoid
    divide any element of the monoid. -/
theorem coe_dvd : ↑u ∣ a :=
  ⟨↑u⁻¹ * a, by
    simp ⟩

/-- In a monoid, an element `a` divides an element `b` iff `a` divides all
    associates of `b`. -/
theorem dvd_mul_right : a ∣ b * u ↔ a ∣ b :=
  Iff.intro
    (fun ⟨c, Eq⟩ =>
      ⟨c * ↑u⁻¹, by
        rw [← mul_assoc, ← Eq, Units.mul_inv_cancel_right]⟩)
    fun ⟨c, Eq⟩ => Eq.symm ▸ (dvd_mul_right _ _).mul_right _

/-- In a monoid, an element `a` divides an element `b` iff all associates of `a` divide `b`. -/
theorem mul_right_dvd : a * u ∣ b ↔ a ∣ b :=
  Iff.intro (fun ⟨c, Eq⟩ => ⟨↑u * c, Eq.trans (mul_assoc _ _ _)⟩) fun h =>
    dvd_trans
      (Dvd.intro (↑u⁻¹)
        (by
          rw [mul_assoc, u.mul_inv, mul_oneₓ]))
      h

end Monoidₓ

section CommMonoidₓ

variable [CommMonoidₓ α] {a b : α} {u : αˣ}

/-- In a commutative monoid, an element `a` divides an element `b` iff `a` divides all left
    associates of `b`. -/
theorem dvd_mul_left : a ∣ u * b ↔ a ∣ b := by
  rw [mul_comm]
  apply dvd_mul_right

/-- In a commutative monoid, an element `a` divides an element `b` iff all
  left associates of `a` divide `b`.-/
theorem mul_left_dvd : ↑u * a ∣ b ↔ a ∣ b := by
  rw [mul_comm]
  apply mul_right_dvd

end CommMonoidₓ

end Units

namespace IsUnit

section Monoidₓ

variable [Monoidₓ α] {a b u : α} (hu : IsUnit u)

include hu

/-- Units of a monoid divide any element of the monoid. -/
@[simp]
theorem dvd : u ∣ a := by
  rcases hu with ⟨u, rfl⟩
  apply Units.coe_dvd

@[simp]
theorem dvd_mul_right : a ∣ b * u ↔ a ∣ b := by
  rcases hu with ⟨u, rfl⟩
  apply Units.dvd_mul_right

/-- In a monoid, an element a divides an element b iff all associates of `a` divide `b`.-/
@[simp]
theorem mul_right_dvd : a * u ∣ b ↔ a ∣ b := by
  rcases hu with ⟨u, rfl⟩
  apply Units.mul_right_dvd

end Monoidₓ

section CommMonoidₓ

variable [CommMonoidₓ α] (a b u : α) (hu : IsUnit u)

include hu

/-- In a commutative monoid, an element `a` divides an element `b` iff `a` divides all left
    associates of `b`. -/
@[simp]
theorem dvd_mul_left : a ∣ u * b ↔ a ∣ b := by
  rcases hu with ⟨u, rfl⟩
  apply Units.dvd_mul_left

/-- In a commutative monoid, an element `a` divides an element `b` iff all
  left associates of `a` divide `b`.-/
@[simp]
theorem mul_left_dvd : u * a ∣ b ↔ a ∣ b := by
  rcases hu with ⟨u, rfl⟩
  apply Units.mul_left_dvd

end CommMonoidₓ

end IsUnit

section CommMonoidₓ

variable [CommMonoidₓ α]

theorem is_unit_iff_dvd_one {x : α} : IsUnit x ↔ x ∣ 1 :=
  ⟨by
    rintro ⟨u, rfl⟩ <;> exact ⟨_, u.mul_inv.symm⟩, fun ⟨y, h⟩ =>
    ⟨⟨x, y, h.symm, by
        rw [h, mul_comm]⟩,
      rfl⟩⟩

theorem is_unit_iff_forall_dvd {x : α} : IsUnit x ↔ ∀ y, x ∣ y :=
  is_unit_iff_dvd_one.trans ⟨fun h y => h.trans (one_dvd _), fun h => h _⟩

theorem is_unit_of_dvd_unit {x y : α} (xy : x ∣ y) (hu : IsUnit y) : IsUnit x :=
  is_unit_iff_dvd_one.2 <| xy.trans <| is_unit_iff_dvd_one.1 hu

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (a «expr ∣ » 1)
theorem is_unit_of_dvd_one : ∀ (a) (_ : a ∣ 1), IsUnit (a : α)
  | a, ⟨b, Eq⟩ => ⟨Units.mkOfMulEqOne a b Eq.symm, rfl⟩

theorem not_is_unit_of_not_is_unit_dvd {a b : α} (ha : ¬IsUnit a) (hb : a ∣ b) : ¬IsUnit b :=
  mt (is_unit_of_dvd_unit hb) ha

end CommMonoidₓ

section CommMonoidWithZero

variable [CommMonoidWithZero α]

/-- `dvd_not_unit a b` expresses that `a` divides `b` "strictly", i.e. that `b` divided by `a`
is not a unit. -/
def DvdNotUnit (a b : α) : Prop :=
  a ≠ 0 ∧ ∃ x, ¬IsUnit x ∧ b = a * x

theorem dvd_not_unit_of_dvd_of_not_dvd {a b : α} (hd : a ∣ b) (hnd : ¬b ∣ a) : DvdNotUnit a b := by
  constructor
  · rintro rfl
    exact hnd (dvd_zero _)
    
  · rcases hd with ⟨c, rfl⟩
    refine' ⟨c, _, rfl⟩
    rintro ⟨u, rfl⟩
    simpa using hnd
    

end CommMonoidWithZero

theorem dvd_and_not_dvd_iff [CancelCommMonoidWithZero α] {x y : α} : x ∣ y ∧ ¬y ∣ x ↔ DvdNotUnit x y :=
  ⟨fun ⟨⟨d, hd⟩, hyx⟩ =>
    ⟨fun hx0 => by
      simpa [← hx0] using hyx,
      ⟨d,
        mt is_unit_iff_dvd_one.1 fun ⟨e, he⟩ =>
          hyx
            ⟨e, by
              rw [hd, mul_assoc, ← he, mul_oneₓ]⟩,
        hd⟩⟩,
    fun ⟨hx0, d, hdu, hdx⟩ =>
    ⟨⟨d, hdx⟩, fun ⟨e, he⟩ =>
      hdu
        (is_unit_of_dvd_one _
          ⟨e,
            mul_left_cancel₀ hx0 <| by
              conv => lhs rw [he, hdx] <;> simp [← mul_assoc]⟩)⟩⟩

section MonoidWithZeroₓ

variable [MonoidWithZeroₓ α]

theorem ne_zero_of_dvd_ne_zero {p q : α} (h₁ : q ≠ 0) (h₂ : p ∣ q) : p ≠ 0 := by
  rcases h₂ with ⟨u, rfl⟩
  exact left_ne_zero_of_mul h₁

end MonoidWithZeroₓ

