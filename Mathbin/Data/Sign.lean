/-
Copyright (c) 2022 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez
-/
import Mathbin.Order.Basic
import Mathbin.Algebra.Algebra.Basic
import Mathbin.Tactic.DeriveFintype

/-!
# Sign function

This file defines the sign function for types with zero and a decidable less-than relation, and
proves some basic theorems about it.
-/


/-- The type of signs. -/
inductive SignType
  | zero
  | neg
  | Pos
  deriving DecidableEq, Inhabited, Fintype

namespace SignType

instance : Zero SignType :=
  ⟨zero⟩

instance : One SignType :=
  ⟨pos⟩

instance : Neg SignType :=
  ⟨fun s =>
    match s with
    | neg => pos
    | zero => zero
    | Pos => neg⟩

@[simp]
theorem zero_eq_zero : zero = 0 :=
  rfl

@[simp]
theorem neg_eq_neg_one : neg = -1 :=
  rfl

@[simp]
theorem pos_eq_one : Pos = 1 :=
  rfl

/-- The multiplication on `sign_type`. -/
def mul : SignType → SignType → SignType
  | neg, neg => pos
  | neg, zero => zero
  | neg, Pos => neg
  | zero, _ => zero
  | Pos, h => h

instance : Mul SignType :=
  ⟨mul⟩

/-- The less-than relation on signs. -/
inductive Le : SignType → SignType → Prop
  | of_neg (a) : le neg a
  | zero : le zero zero
  | of_pos (a) : le a pos

instance : LE SignType :=
  ⟨Le⟩

instance : DecidableRel Le := fun a b => by
  cases a <;>
    cases b <;>
      first |
        exact
          is_false
            (by
              rintro ⟨⟩)|
        exact
          is_true
            (by
              constructor)

/- We can define a `field` instance on `sign_type`, but it's not mathematically sensible,
so we only define the `comm_group_with_zero`. -/
instance : CommGroupWithZero SignType where
  zero := 0
  one := 1
  mul := (· * ·)
  inv := id
  mul_zero := fun a => by
    cases a <;> rfl
  zero_mul := fun a => by
    cases a <;> rfl
  mul_one := fun a => by
    cases a <;> rfl
  one_mul := fun a => by
    cases a <;> rfl
  mul_inv_cancel := fun a ha => by
    cases a <;> trivial
  mul_comm := fun a b => by
    casesm* _ <;> rfl
  mul_assoc := fun a b c => by
    casesm* _ <;> rfl
  exists_pair_ne :=
    ⟨0, 1, by
      rintro ⟨⟩⟩
  inv_zero := rfl

instance : LinearOrderₓ SignType where
  le := (· ≤ ·)
  le_refl := fun a => by
    cases a <;> constructor
  le_total := fun a b => by
    casesm* _ <;> decide
  le_antisymm := fun a b ha hb => by
    casesm* _ <;> rfl
  le_trans := fun a b c hab hbc => by
    casesm* _ <;> constructor
  decidableLe := Le.decidableRel

instance : HasDistribNeg SignType :=
  { SignType.hasNeg with
    neg_neg := fun x => by
      cases x <;> rfl,
    neg_mul := fun x y => by
      casesm* _ <;> rfl,
    mul_neg := fun x y => by
      casesm* _ <;> rfl }

/-- `sign_type` is equivalent to `fin 3`. -/
def fin3Equiv : SignType ≃* Finₓ 3 where
  toFun := fun a => a.recOn 0 (-1) 1
  invFun := fun a =>
    match a with
    | ⟨0, h⟩ => 0
    | ⟨1, h⟩ => 1
    | ⟨2, h⟩ => -1
    | ⟨n + 3, h⟩ => (h.not_le le_add_self).elim
  left_inv := fun a => by
    cases a <;> rfl
  right_inv := fun a =>
    match a with
    | ⟨0, h⟩ => rfl
    | ⟨1, h⟩ => rfl
    | ⟨2, h⟩ => rfl
    | ⟨n + 3, h⟩ => (h.not_le le_add_self).elim
  map_mul' := fun x y => by
    casesm* _ <;> rfl

section cast

variable {α : Type _} [Zero α] [One α] [Neg α]

/-- Turn a `sign_type` into zero, one, or minus one. This is a coercion instance, but note it is
only a `has_coe_t` instance: see note [use has_coe_t]. -/
def cast : SignType → α
  | zero => 0
  | Pos => 1
  | neg => -1

instance : CoeTₓ SignType α :=
  ⟨cast⟩

@[simp]
theorem cast_eq_coe (a : SignType) : (cast a : α) = a :=
  rfl

@[simp]
theorem coe_zero : ↑(0 : SignType) = (0 : α) :=
  rfl

@[simp]
theorem coe_one : ↑(1 : SignType) = (1 : α) :=
  rfl

@[simp]
theorem coe_neg_one : ↑(-1 : SignType) = (-1 : α) :=
  rfl

end cast

/-- `sign_type.cast` as a `mul_with_zero_hom`. -/
@[simps]
def castHom {α} [MulZeroOneClassₓ α] [HasDistribNeg α] : SignType →*₀ α where
  toFun := cast
  map_zero' := rfl
  map_one' := rfl
  map_mul' := fun x y => by
    cases x <;> cases y <;> simp

end SignType

variable {α : Type _}

open SignType

section Preorderₓ

variable [Zero α] [Preorderₓ α] [DecidableRel ((· < ·) : α → α → Prop)] {a : α}

/-- The sign of an element is 1 if it's positive, -1 if negative, 0 otherwise. -/
def sign : α →o SignType :=
  ⟨fun a => if 0 < a then 1 else if a < 0 then -1 else 0, fun a b h => by
    dsimp'
    split_ifs with h₁ h₂ h₃ h₄ _ _ h₂ h₃ <;>
      try
        constructor
    · cases lt_irreflₓ 0 (h₁.trans <| h.trans_lt h₃)
      
    · cases h₂ (h₁.trans_le h)
      
    · cases h₄ (h.trans_lt h₃)
      ⟩

theorem sign_apply : sign a = ite (0 < a) 1 (ite (a < 0) (-1) 0) :=
  rfl

@[simp]
theorem sign_zero : sign (0 : α) = 0 := by
  simp [← sign_apply]

@[simp]
theorem sign_pos (ha : 0 < a) : sign a = 1 := by
  rwa [sign_apply, if_pos]

@[simp]
theorem sign_neg (ha : a < 0) : sign a = -1 := by
  rwa [sign_apply, if_neg <| asymm ha, if_pos]

end Preorderₓ

section LinearOrderₓ

variable [Zero α] [LinearOrderₓ α] {a : α}

@[simp]
theorem sign_eq_zero_iff : sign a = 0 ↔ a = 0 := by
  refine' ⟨fun h => _, fun h => h.symm ▸ sign_zero⟩
  rw [sign_apply] at h
  split_ifs  at h <;> cases h
  exact (le_of_not_ltₓ h_1).eq_of_not_lt h_2

theorem sign_ne_zero : sign a ≠ 0 ↔ a ≠ 0 :=
  sign_eq_zero_iff.Not

end LinearOrderₓ

section LinearOrderedRing

variable [LinearOrderedRing α] {a b : α}

/- I'm not sure why this is necessary, see https://leanprover.zulipchat.com/#narrow/stream/
113488-general/topic/type.20class.20inference.20issues/near/276937942 -/
attribute [local instance] LinearOrderedRing.decidableLt

/-- `sign` as a `monoid_with_zero_hom` for a nontrivial ordered semiring. Note that linearity
is required; consider ℂ with the order `z ≤ w` iff they have the same imaginary part and
`z - w ≤ 0` in the reals; then `1 + i` and `1 - i` are incomparable to zero, and thus we have:
`0 * 0 = sign (1 + i) * sign (1 - i) ≠ sign 2 = 1`. (`complex.ordered_comm_ring`) -/
def signHom : α →*₀ SignType where
  toFun := sign
  map_zero' := sign_zero
  map_one' := sign_pos zero_lt_one
  map_mul' := fun x y => by
    rcases lt_trichotomyₓ x 0 with (hx | hx | hx) <;>
      rcases lt_trichotomyₓ y 0 with (hy | hy | hy) <;>
        simp only [← sign_zero, ← mul_zero, ← zero_mul, ← sign_pos, ← sign_neg, ← hx, ← hy, ← mul_oneₓ, ← neg_one_mul, ←
          neg_negₓ, ← one_mulₓ, ← mul_pos_of_neg_of_neg, ← mul_neg_of_neg_of_pos, ← neg_zero', ← mul_neg_of_pos_of_neg,
          ← mul_pos]

end LinearOrderedRing

