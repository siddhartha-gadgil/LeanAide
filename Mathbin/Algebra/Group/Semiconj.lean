/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

Some proofs and docs came from `algebra/commute` (c) Neil Strickland
-/
import Mathbin.Algebra.Group.Units

/-!
# Semiconjugate elements of a semigroup

## Main definitions

We say that `x` is semiconjugate to `y` by `a` (`semiconj_by a x y`), if `a * x = y * a`.
In this file we  provide operations on `semiconj_by _ _ _`.

In the names of these operations, we treat `a` as the “left” argument, and both `x` and `y` as
“right” arguments. This way most names in this file agree with the names of the corresponding lemmas
for `commute a b = semiconj_by a b b`. As a side effect, some lemmas have only `_right` version.

Lean does not immediately recognise these terms as equations, so for rewriting we need syntax like
`rw [(h.pow_right 5).eq]` rather than just `rw [h.pow_right 5]`.

This file provides only basic operations (`mul_left`, `mul_right`, `inv_right` etc). Other
operations (`pow_right`, field inverse etc) are in the files that define corresponding notions.
-/


universe u v

variable {G : Type _}

/-- `x` is semiconjugate to `y` by `a`, if `a * x = y * a`. -/
@[to_additive AddSemiconjBy "`x` is additive semiconjugate to `y` by `a` if `a + x = y + a`"]
def SemiconjBy {M : Type u} [Mul M] (a x y : M) : Prop :=
  a * x = y * a

namespace SemiconjBy

/-- Equality behind `semiconj_by a x y`; useful for rewriting. -/
@[to_additive "Equality behind `add_semiconj_by a x y`; useful for rewriting."]
protected theorem eq {S : Type u} [Mul S] {a x y : S} (h : SemiconjBy a x y) : a * x = y * a :=
  h

section Semigroupₓ

variable {S : Type u} [Semigroupₓ S] {a b x y z x' y' : S}

/-- If `a` semiconjugates `x` to `y` and `x'` to `y'`,
then it semiconjugates `x * x'` to `y * y'`. -/
@[simp, to_additive "If `a` semiconjugates `x` to `y` and `x'` to `y'`, then it semiconjugates\n`x + x'` to `y + y'`."]
theorem mul_right (h : SemiconjBy a x y) (h' : SemiconjBy a x' y') : SemiconjBy a (x * x') (y * y') := by
  unfold SemiconjBy <;> assoc_rw [h.eq, h'.eq]

/-- If both `a` and `b` semiconjugate `x` to `y`, then so does `a * b`. -/
@[to_additive "If both `a` and `b` semiconjugate `x` to `y`, then so does `a + b`."]
theorem mul_left (ha : SemiconjBy a y z) (hb : SemiconjBy b x y) : SemiconjBy (a * b) x z := by
  unfold SemiconjBy <;> assoc_rw [hb.eq, ha.eq, mul_assoc]

/-- The relation “there exists an element that semiconjugates `a` to `b`” on a semigroup
is transitive. -/
@[to_additive
      "The relation “there exists an element that semiconjugates `a` to `b`” on an additive\nsemigroup is transitive."]
protected theorem transitive : Transitive fun a b : S => ∃ c, SemiconjBy c a b := fun a b c ⟨x, hx⟩ ⟨y, hy⟩ =>
  ⟨y * x, hy.mul_left hx⟩

end Semigroupₓ

section MulOneClassₓ

variable {M : Type u} [MulOneClassₓ M]

/-- Any element semiconjugates `1` to `1`. -/
@[simp, to_additive "Any element additively semiconjugates `0` to `0`."]
theorem one_right (a : M) : SemiconjBy a 1 1 := by
  rw [SemiconjBy, mul_oneₓ, one_mulₓ]

/-- One semiconjugates any element to itself. -/
@[simp, to_additive "Zero additively semiconjugates any element to itself."]
theorem one_left (x : M) : SemiconjBy 1 x x :=
  Eq.symm <| one_right x

/-- The relation “there exists an element that semiconjugates `a` to `b`” on a monoid (or, more
generally, on ` mul_one_class` type) is reflexive. -/
@[to_additive
      "The relation “there exists an element that semiconjugates `a` to `b`” on an additive\nmonoid (or, more generally, on a `add_zero_class` type) is reflexive."]
protected theorem reflexive : Reflexive fun a b : M => ∃ c, SemiconjBy c a b := fun a => ⟨1, one_left a⟩

end MulOneClassₓ

section Monoidₓ

variable {M : Type u} [Monoidₓ M]

/-- If `a` semiconjugates a unit `x` to a unit `y`, then it semiconjugates `x⁻¹` to `y⁻¹`. -/
@[to_additive
      "If `a` semiconjugates an additive unit `x` to an additive unit `y`, then it\nsemiconjugates `-x` to `-y`."]
theorem units_inv_right {a : M} {x y : Mˣ} (h : SemiconjBy a x y) : SemiconjBy a ↑x⁻¹ ↑y⁻¹ :=
  calc
    a * ↑x⁻¹ = ↑y⁻¹ * (y * a) * ↑x⁻¹ := by
      rw [Units.inv_mul_cancel_left]
    _ = ↑y⁻¹ * a := by
      rw [← h.eq, mul_assoc, Units.mul_inv_cancel_right]
    

@[simp, to_additive]
theorem units_inv_right_iff {a : M} {x y : Mˣ} : SemiconjBy a ↑x⁻¹ ↑y⁻¹ ↔ SemiconjBy a x y :=
  ⟨units_inv_right, units_inv_right⟩

/-- If a unit `a` semiconjugates `x` to `y`, then `a⁻¹` semiconjugates `y` to `x`. -/
@[to_additive "If an additive unit `a` semiconjugates `x` to `y`, then `-a` semiconjugates `y` to\n`x`."]
theorem units_inv_symm_left {a : Mˣ} {x y : M} (h : SemiconjBy (↑a) x y) : SemiconjBy (↑a⁻¹) y x :=
  calc
    ↑a⁻¹ * y = ↑a⁻¹ * (y * a * ↑a⁻¹) := by
      rw [Units.mul_inv_cancel_right]
    _ = x * ↑a⁻¹ := by
      rw [← h.eq, ← mul_assoc, Units.inv_mul_cancel_left]
    

@[simp, to_additive]
theorem units_inv_symm_left_iff {a : Mˣ} {x y : M} : SemiconjBy (↑a⁻¹) y x ↔ SemiconjBy (↑a) x y :=
  ⟨units_inv_symm_left, units_inv_symm_left⟩

@[to_additive]
theorem units_coe {a x y : Mˣ} (h : SemiconjBy a x y) : SemiconjBy (a : M) x y :=
  congr_arg Units.val h

@[to_additive]
theorem units_of_coe {a x y : Mˣ} (h : SemiconjBy (a : M) x y) : SemiconjBy a x y :=
  Units.ext h

@[simp, to_additive]
theorem units_coe_iff {a x y : Mˣ} : SemiconjBy (a : M) x y ↔ SemiconjBy a x y :=
  ⟨units_of_coe, units_coe⟩

@[simp, to_additive]
theorem pow_right {a x y : M} (h : SemiconjBy a x y) (n : ℕ) : SemiconjBy a (x ^ n) (y ^ n) := by
  induction' n with n ih
  · rw [pow_zeroₓ, pow_zeroₓ]
    exact SemiconjBy.one_right _
    
  · rw [pow_succₓ, pow_succₓ]
    exact h.mul_right ih
    

end Monoidₓ

section DivisionMonoid

variable [DivisionMonoid G] {a x y : G}

@[simp, to_additive]
theorem inv_inv_symm_iff : SemiconjBy a⁻¹ x⁻¹ y⁻¹ ↔ SemiconjBy a y x :=
  inv_involutive.Injective.eq_iff.symm.trans <| by
    simp_rw [mul_inv_rev, inv_invₓ, eq_comm, SemiconjBy]

@[to_additive]
theorem inv_inv_symm : SemiconjBy a x y → SemiconjBy a⁻¹ y⁻¹ x⁻¹ :=
  inv_inv_symm_iff.2

end DivisionMonoid

section Groupₓ

variable [Groupₓ G] {a x y : G}

@[simp, to_additive]
theorem inv_right_iff : SemiconjBy a x⁻¹ y⁻¹ ↔ SemiconjBy a x y :=
  @units_inv_right_iff G _ a ⟨x, x⁻¹, mul_inv_selfₓ x, inv_mul_selfₓ x⟩ ⟨y, y⁻¹, mul_inv_selfₓ y, inv_mul_selfₓ y⟩

@[to_additive]
theorem inv_right : SemiconjBy a x y → SemiconjBy a x⁻¹ y⁻¹ :=
  inv_right_iff.2

@[simp, to_additive]
theorem inv_symm_left_iff : SemiconjBy a⁻¹ y x ↔ SemiconjBy a x y :=
  @units_inv_symm_left_iff G _ ⟨a, a⁻¹, mul_inv_selfₓ a, inv_mul_selfₓ a⟩ _ _

@[to_additive]
theorem inv_symm_left : SemiconjBy a x y → SemiconjBy a⁻¹ y x :=
  inv_symm_left_iff.2

/-- `a` semiconjugates `x` to `a * x * a⁻¹`. -/
@[to_additive "`a` semiconjugates `x` to `a + x + -a`."]
theorem conj_mk (a x : G) : SemiconjBy a x (a * x * a⁻¹) := by
  unfold SemiconjBy <;> rw [mul_assoc, inv_mul_selfₓ, mul_oneₓ]

end Groupₓ

end SemiconjBy

@[simp, to_additive add_semiconj_by_iff_eq]
theorem semiconj_by_iff_eq {M : Type u} [CancelCommMonoid M] {a x y : M} : SemiconjBy a x y ↔ x = y :=
  ⟨fun h => mul_left_cancelₓ (h.trans (mul_comm _ _)), fun h => by
    rw [h, SemiconjBy, mul_comm]⟩

/-- `a` semiconjugates `x` to `a * x * a⁻¹`. -/
@[to_additive "`a` semiconjugates `x` to `a + x + -a`."]
theorem Units.mk_semiconj_by {M : Type u} [Monoidₓ M] (u : Mˣ) (x : M) : SemiconjBy (↑u) x (u * x * ↑u⁻¹) := by
  unfold SemiconjBy <;> rw [Units.inv_mul_cancel_right]

