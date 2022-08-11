/-
Copyright (c) 2019 Neil Strickland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Neil Strickland, Yury Kudryashov
-/
import Mathbin.Algebra.Group.Semiconj

/-!
# Commuting pairs of elements in monoids

We define the predicate `commute a b := a * b = b * a` and provide some operations on terms `(h :
commute a b)`. E.g., if `a`, `b`, and c are elements of a semiring, and that `hb : commute a b` and
`hc : commute a c`.  Then `hb.pow_left 5` proves `commute (a ^ 5) b` and `(hb.pow_right 2).add_right
(hb.mul_right hc)` proves `commute a (b ^ 2 + b * c)`.

Lean does not immediately recognise these terms as equations, so for rewriting we need syntax like
`rw [(hb.pow_left 5).eq]` rather than just `rw [hb.pow_left 5]`.

This file defines only a few operations (`mul_left`, `inv_right`, etc).  Other operations
(`pow_right`, field inverse etc) are in the files that define corresponding notions.

## Implementation details

Most of the proofs come from the properties of `semiconj_by`.
-/


variable {G : Type _}

/-- Two elements commute if `a * b = b * a`. -/
@[to_additive AddCommute "Two elements additively commute if `a + b = b + a`"]
def Commute {S : Type _} [Mul S] (a b : S) : Prop :=
  SemiconjBy a b b

namespace Commute

section Mul

variable {S : Type _} [Mul S]

/-- Equality behind `commute a b`; useful for rewriting. -/
@[to_additive "Equality behind `add_commute a b`; useful for rewriting."]
protected theorem eq {a b : S} (h : Commute a b) : a * b = b * a :=
  h

/-- Any element commutes with itself. -/
@[refl, simp, to_additive "Any element commutes with itself."]
protected theorem refl (a : S) : Commute a a :=
  Eq.refl (a * a)

/-- If `a` commutes with `b`, then `b` commutes with `a`. -/
@[symm, to_additive "If `a` commutes with `b`, then `b` commutes with `a`."]
protected theorem symm {a b : S} (h : Commute a b) : Commute b a :=
  Eq.symm h

@[to_additive]
protected theorem semiconj_by {a b : S} (h : Commute a b) : SemiconjBy a b b :=
  h

@[to_additive]
protected theorem symm_iff {a b : S} : Commute a b ↔ Commute b a :=
  ⟨Commute.symm, Commute.symm⟩

end Mul

section Semigroupₓ

variable {S : Type _} [Semigroupₓ S] {a b c : S}

/-- If `a` commutes with both `b` and `c`, then it commutes with their product. -/
@[simp, to_additive "If `a` commutes with both `b` and `c`, then it commutes with their sum."]
theorem mul_right (hab : Commute a b) (hac : Commute a c) : Commute a (b * c) :=
  hab.mul_right hac

/-- If both `a` and `b` commute with `c`, then their product commutes with `c`. -/
@[simp, to_additive "If both `a` and `b` commute with `c`, then their product commutes with `c`."]
theorem mul_left (hac : Commute a c) (hbc : Commute b c) : Commute (a * b) c :=
  hac.mul_left hbc

@[to_additive]
protected theorem right_comm (h : Commute b c) (a : S) : a * b * c = a * c * b := by
  simp only [← mul_assoc, ← h.eq]

@[to_additive]
protected theorem left_comm (h : Commute a b) (c) : a * (b * c) = b * (a * c) := by
  simp only [mul_assoc, ← h.eq]

end Semigroupₓ

@[to_additive]
protected theorem all {S : Type _} [CommSemigroupₓ S] (a b : S) : Commute a b :=
  mul_comm a b

section MulOneClassₓ

variable {M : Type _} [MulOneClassₓ M]

@[simp, to_additive]
theorem one_right (a : M) : Commute a 1 :=
  SemiconjBy.one_right a

@[simp, to_additive]
theorem one_left (a : M) : Commute 1 a :=
  SemiconjBy.one_left a

end MulOneClassₓ

section Monoidₓ

variable {M : Type _} [Monoidₓ M] {a b : M} {u u₁ u₂ : Mˣ}

@[simp, to_additive]
theorem pow_right (h : Commute a b) (n : ℕ) : Commute a (b ^ n) :=
  h.pow_right n

@[simp, to_additive]
theorem pow_left (h : Commute a b) (n : ℕ) : Commute (a ^ n) b :=
  (h.symm.pow_right n).symm

@[simp, to_additive]
theorem pow_pow (h : Commute a b) (m n : ℕ) : Commute (a ^ m) (b ^ n) :=
  (h.pow_left m).pow_right n

@[simp, to_additive]
theorem self_pow (a : M) (n : ℕ) : Commute a (a ^ n) :=
  (Commute.refl a).pow_right n

@[simp, to_additive]
theorem pow_self (a : M) (n : ℕ) : Commute (a ^ n) a :=
  (Commute.refl a).pow_left n

@[simp, to_additive]
theorem pow_pow_self (a : M) (m n : ℕ) : Commute (a ^ m) (a ^ n) :=
  (Commute.refl a).pow_pow m n

@[to_additive succ_nsmul']
theorem _root_.pow_succ' (a : M) (n : ℕ) : a ^ (n + 1) = a ^ n * a :=
  (pow_succₓ a n).trans (self_pow _ _)

@[to_additive]
theorem units_inv_right : Commute a u → Commute a ↑u⁻¹ :=
  SemiconjBy.units_inv_right

@[simp, to_additive]
theorem units_inv_right_iff : Commute a ↑u⁻¹ ↔ Commute a u :=
  SemiconjBy.units_inv_right_iff

@[to_additive]
theorem units_inv_left : Commute (↑u) a → Commute (↑u⁻¹) a :=
  SemiconjBy.units_inv_symm_left

@[simp, to_additive]
theorem units_inv_left_iff : Commute (↑u⁻¹) a ↔ Commute (↑u) a :=
  SemiconjBy.units_inv_symm_left_iff

@[to_additive]
theorem units_coe : Commute u₁ u₂ → Commute (u₁ : M) u₂ :=
  SemiconjBy.units_coe

@[to_additive]
theorem units_of_coe : Commute (u₁ : M) u₂ → Commute u₁ u₂ :=
  SemiconjBy.units_of_coe

@[simp, to_additive]
theorem units_coe_iff : Commute (u₁ : M) u₂ ↔ Commute u₁ u₂ :=
  SemiconjBy.units_coe_iff

@[to_additive]
theorem is_unit_mul_iff (h : Commute a b) : IsUnit (a * b) ↔ IsUnit a ∧ IsUnit b := by
  refine' ⟨_, fun H => H.1.mul H.2⟩
  rintro ⟨u, hu⟩
  have : b * ↑u⁻¹ * a = 1 := by
    have : Commute a u := hu.symm ▸ (Commute.refl _).mul_right h
    rw [← this.units_inv_right.right_comm, ← h.eq, ← hu, u.mul_inv]
  constructor
  · refine' ⟨⟨a, b * ↑u⁻¹, _, this⟩, rfl⟩
    rw [← mul_assoc, ← hu, u.mul_inv]
    
  · rw [mul_assoc] at this
    refine' ⟨⟨b, ↑u⁻¹ * a, this, _⟩, rfl⟩
    rw [mul_assoc, ← hu, u.inv_mul]
    

@[simp, to_additive]
theorem _root_.is_unit_mul_self_iff : IsUnit (a * a) ↔ IsUnit a :=
  (Commute.refl a).is_unit_mul_iff.trans (and_selfₓ _)

end Monoidₓ

section DivisionMonoid

variable [DivisionMonoid G] {a b : G}

@[to_additive]
theorem inv_inv : Commute a b → Commute a⁻¹ b⁻¹ :=
  SemiconjBy.inv_inv_symm

@[simp, to_additive]
theorem inv_inv_iff : Commute a⁻¹ b⁻¹ ↔ Commute a b :=
  SemiconjBy.inv_inv_symm_iff

end DivisionMonoid

section Groupₓ

variable [Groupₓ G] {a b : G}

@[to_additive]
theorem inv_right : Commute a b → Commute a b⁻¹ :=
  SemiconjBy.inv_right

@[simp, to_additive]
theorem inv_right_iff : Commute a b⁻¹ ↔ Commute a b :=
  SemiconjBy.inv_right_iff

@[to_additive]
theorem inv_left : Commute a b → Commute a⁻¹ b :=
  SemiconjBy.inv_symm_left

@[simp, to_additive]
theorem inv_left_iff : Commute a⁻¹ b ↔ Commute a b :=
  SemiconjBy.inv_symm_left_iff

@[to_additive]
protected theorem inv_mul_cancel (h : Commute a b) : a⁻¹ * b * a = b := by
  rw [h.inv_left.eq, inv_mul_cancel_right]

@[to_additive]
theorem inv_mul_cancel_assoc (h : Commute a b) : a⁻¹ * (b * a) = b := by
  rw [← mul_assoc, h.inv_mul_cancel]

@[to_additive]
protected theorem mul_inv_cancel (h : Commute a b) : a * b * a⁻¹ = b := by
  rw [h.eq, mul_inv_cancel_rightₓ]

@[to_additive]
theorem mul_inv_cancel_assoc (h : Commute a b) : a * (b * a⁻¹) = b := by
  rw [← mul_assoc, h.mul_inv_cancel]

end Groupₓ

end Commute

section CommGroupₓ

variable [CommGroupₓ G] (a b : G)

@[simp, to_additive]
theorem mul_inv_cancel_comm : a * b * a⁻¹ = b :=
  (Commute.all a b).mul_inv_cancel

@[simp, to_additive]
theorem mul_inv_cancel_comm_assoc : a * (b * a⁻¹) = b :=
  (Commute.all a b).mul_inv_cancel_assoc

@[simp, to_additive]
theorem inv_mul_cancel_comm : a⁻¹ * b * a = b :=
  (Commute.all a b).inv_mul_cancel

@[simp, to_additive]
theorem inv_mul_cancel_comm_assoc : a⁻¹ * (b * a) = b :=
  (Commute.all a b).inv_mul_cancel_assoc

end CommGroupₓ

