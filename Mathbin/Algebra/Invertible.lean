/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import Mathbin.Algebra.Group.Units
import Mathbin.Algebra.Ring.Basic

/-!
# Invertible elements

This file defines a typeclass `invertible a` for elements `a` with a two-sided
multiplicative inverse.

The intent of the typeclass is to provide a way to write e.g. `⅟2` in a ring
like `ℤ[1/2]` where some inverses exist but there is no general `⁻¹` operator;
or to specify that a field has characteristic `≠ 2`.
It is the `Type`-valued analogue to the `Prop`-valued `is_unit`.

For constructions of the invertible element given a characteristic, see
`algebra/char_p/invertible` and other lemmas in that file.

## Notation

 * `⅟a` is `invertible.inv_of a`, the inverse of `a`

## Implementation notes

The `invertible` class lives in `Type`, not `Prop`, to make computation easier.
If multiplication is associative, `invertible` is a subsingleton anyway.

The `simp` normal form tries to normalize `⅟a` to `a ⁻¹`. Otherwise, it pushes
`⅟` inside the expression as much as possible.

Since `invertible a` is not a `Prop` (but it is a `subsingleton`), we have to be careful about
coherence issues: we should avoid having multiple non-defeq instances for `invertible a` in the
same context.  This file plays it safe and uses `def` rather than `instance` for most definitions,
users can choose which instances to use at the point of use.

For example, here's how you can use an `invertible 1` instance:
```lean
variables {α : Type*} [monoid α]

def something_that_needs_inverses (x : α) [invertible x] := sorry

section
local attribute [instance] invertible_one
def something_one := something_that_needs_inverses 1
end
```

## Tags

invertible, inverse element, inv_of, a half, one half, a third, one third, ½, ⅓

-/


universe u

variable {α : Type u}

/-- `invertible a` gives a two-sided multiplicative inverse of `a`. -/
class Invertible [Mul α] [One α] (a : α) : Type u where
  invOf : α
  inv_of_mul_self : inv_of * a = 1
  mul_inv_of_self : a * inv_of = 1

-- mathport name: «expr⅟»
notation:1034
  "⅟" =>-- This notation has the same precedence as `has_inv.inv`.
  Invertible.invOf

@[simp]
theorem inv_of_mul_self [Mul α] [One α] (a : α) [Invertible a] : ⅟ a * a = 1 :=
  Invertible.inv_of_mul_self

@[simp]
theorem mul_inv_of_self [Mul α] [One α] (a : α) [Invertible a] : a * ⅟ a = 1 :=
  Invertible.mul_inv_of_self

@[simp]
theorem inv_of_mul_self_assoc [Monoidₓ α] (a b : α) [Invertible a] : ⅟ a * (a * b) = b := by
  rw [← mul_assoc, inv_of_mul_self, one_mulₓ]

@[simp]
theorem mul_inv_of_self_assoc [Monoidₓ α] (a b : α) [Invertible a] : a * (⅟ a * b) = b := by
  rw [← mul_assoc, mul_inv_of_self, one_mulₓ]

@[simp]
theorem mul_inv_of_mul_self_cancel [Monoidₓ α] (a b : α) [Invertible b] : a * ⅟ b * b = a := by
  simp [← mul_assoc]

@[simp]
theorem mul_mul_inv_of_self_cancel [Monoidₓ α] (a b : α) [Invertible b] : a * b * ⅟ b = a := by
  simp [← mul_assoc]

theorem inv_of_eq_right_inv [Monoidₓ α] {a b : α} [Invertible a] (hac : a * b = 1) : ⅟ a = b :=
  left_inv_eq_right_invₓ (inv_of_mul_self _) hac

theorem inv_of_eq_left_inv [Monoidₓ α] {a b : α} [Invertible a] (hac : b * a = 1) : ⅟ a = b :=
  (left_inv_eq_right_invₓ hac (mul_inv_of_self _)).symm

theorem invertible_unique {α : Type u} [Monoidₓ α] (a b : α) [Invertible a] [Invertible b] (h : a = b) : ⅟ a = ⅟ b := by
  apply inv_of_eq_right_inv
  rw [h, mul_inv_of_self]

instance [Monoidₓ α] (a : α) : Subsingleton (Invertible a) :=
  ⟨fun ⟨b, hba, hab⟩ ⟨c, hca, hac⟩ => by
    congr
    exact left_inv_eq_right_invₓ hba hac⟩

/-- If `r` is invertible and `s = r`, then `s` is invertible. -/
def Invertible.copy [Monoidₓ α] {r : α} (hr : Invertible r) (s : α) (hs : s = r) : Invertible s where
  invOf := ⅟ r
  inv_of_mul_self := by
    rw [hs, inv_of_mul_self]
  mul_inv_of_self := by
    rw [hs, mul_inv_of_self]

/-- An `invertible` element is a unit. -/
@[simps]
def unitOfInvertible [Monoidₓ α] (a : α) [Invertible a] : αˣ where
  val := a
  inv := ⅟ a
  val_inv := by
    simp
  inv_val := by
    simp

theorem is_unit_of_invertible [Monoidₓ α] (a : α) [Invertible a] : IsUnit a :=
  ⟨unitOfInvertible a, rfl⟩

/-- Units are invertible in their associated monoid. -/
def Units.invertible [Monoidₓ α] (u : αˣ) : Invertible (u : α) where
  invOf := ↑u⁻¹
  inv_of_mul_self := u.inv_mul
  mul_inv_of_self := u.mul_inv

@[simp]
theorem inv_of_units [Monoidₓ α] (u : αˣ) [Invertible (u : α)] : ⅟ (u : α) = ↑u⁻¹ :=
  inv_of_eq_right_inv u.mul_inv

theorem IsUnit.nonempty_invertible [Monoidₓ α] {a : α} (h : IsUnit a) : Nonempty (Invertible a) :=
  let ⟨x, hx⟩ := h
  ⟨x.Invertible.copy _ hx.symm⟩

/-- Convert `is_unit` to `invertible` using `classical.choice`.

Prefer `casesI h.nonempty_invertible` over `letI := h.invertible` if you want to avoid choice. -/
noncomputable def IsUnit.invertible [Monoidₓ α] {a : α} (h : IsUnit a) : Invertible a :=
  Classical.choice h.nonempty_invertible

@[simp]
theorem nonempty_invertible_iff_is_unit [Monoidₓ α] (a : α) : Nonempty (Invertible a) ↔ IsUnit a :=
  ⟨Nonempty.ndrec <| @is_unit_of_invertible _ _ _, IsUnit.nonempty_invertible⟩

/-- Each element of a group is invertible. -/
def invertibleOfGroup [Groupₓ α] (a : α) : Invertible a :=
  ⟨a⁻¹, inv_mul_selfₓ a, mul_inv_selfₓ a⟩

@[simp]
theorem inv_of_eq_group_inv [Groupₓ α] (a : α) [Invertible a] : ⅟ a = a⁻¹ :=
  inv_of_eq_right_inv (mul_inv_selfₓ a)

/-- `1` is the inverse of itself -/
def invertibleOne [Monoidₓ α] : Invertible (1 : α) :=
  ⟨1, mul_oneₓ _, one_mulₓ _⟩

@[simp]
theorem inv_of_one [Monoidₓ α] [Invertible (1 : α)] : ⅟ (1 : α) = 1 :=
  inv_of_eq_right_inv (mul_oneₓ _)

/-- `-⅟a` is the inverse of `-a` -/
def invertibleNeg [Mul α] [One α] [HasDistribNeg α] (a : α) [Invertible a] : Invertible (-a) :=
  ⟨-⅟ a, by
    simp , by
    simp ⟩

@[simp]
theorem inv_of_neg [Monoidₓ α] [HasDistribNeg α] (a : α) [Invertible a] [Invertible (-a)] : ⅟ (-a) = -⅟ a :=
  inv_of_eq_right_inv
    (by
      simp )

@[simp]
theorem one_sub_inv_of_two [Ringₓ α] [Invertible (2 : α)] : 1 - (⅟ 2 : α) = ⅟ 2 :=
  (is_unit_of_invertible (2 : α)).mul_right_inj.1 <| by
    rw [mul_sub, mul_inv_of_self, mul_oneₓ, bit0, add_sub_cancel]

@[simp]
theorem inv_of_two_add_inv_of_two [NonAssocSemiringₓ α] [Invertible (2 : α)] : (⅟ 2 : α) + (⅟ 2 : α) = 1 := by
  rw [← two_mul, mul_inv_of_self]

/-- `a` is the inverse of `⅟a`. -/
instance invertibleInvOf [One α] [Mul α] {a : α} [Invertible a] : Invertible (⅟ a) :=
  ⟨a, mul_inv_of_self a, inv_of_mul_self a⟩

@[simp]
theorem inv_of_inv_of [Monoidₓ α] (a : α) [Invertible a] [Invertible (⅟ a)] : ⅟ (⅟ a) = a :=
  inv_of_eq_right_inv (inv_of_mul_self _)

@[simp]
theorem inv_of_inj [Monoidₓ α] {a b : α} [Invertible a] [Invertible b] : ⅟ a = ⅟ b ↔ a = b :=
  ⟨invertible_unique _ _, invertible_unique _ _⟩

/-- `⅟b * ⅟a` is the inverse of `a * b` -/
def invertibleMul [Monoidₓ α] (a b : α) [Invertible a] [Invertible b] : Invertible (a * b) :=
  ⟨⅟ b * ⅟ a, by
    simp [mul_assoc], by
    simp [mul_assoc]⟩

@[simp]
theorem inv_of_mul [Monoidₓ α] (a b : α) [Invertible a] [Invertible b] [Invertible (a * b)] : ⅟ (a * b) = ⅟ b * ⅟ a :=
  inv_of_eq_right_inv
    (by
      simp [mul_assoc])

theorem Commute.inv_of_right [Monoidₓ α] {a b : α} [Invertible b] (h : Commute a b) : Commute a (⅟ b) :=
  calc
    a * ⅟ b = ⅟ b * (b * a * ⅟ b) := by
      simp [← mul_assoc]
    _ = ⅟ b * (a * b * ⅟ b) := by
      rw [h.eq]
    _ = ⅟ b * a := by
      simp [← mul_assoc]
    

theorem Commute.inv_of_left [Monoidₓ α] {a b : α} [Invertible b] (h : Commute b a) : Commute (⅟ b) a :=
  calc
    ⅟ b * a = ⅟ b * (a * b * ⅟ b) := by
      simp [← mul_assoc]
    _ = ⅟ b * (b * a * ⅟ b) := by
      rw [h.eq]
    _ = a * ⅟ b := by
      simp [← mul_assoc]
    

theorem commute_inv_of {M : Type _} [One M] [Mul M] (m : M) [Invertible m] : Commute m (⅟ m) :=
  calc
    m * ⅟ m = 1 := mul_inv_of_self m
    _ = ⅟ m * m := (inv_of_mul_self m).symm
    

theorem nonzero_of_invertible [MulZeroOneClassₓ α] (a : α) [Nontrivial α] [Invertible a] : a ≠ 0 := fun ha =>
  zero_ne_one <|
    calc
      0 = ⅟ a * a := by
        simp [← ha]
      _ = 1 := inv_of_mul_self a
      

section MonoidWithZeroₓ

variable [MonoidWithZeroₓ α]

/-- A variant of `ring.inverse_unit`. -/
@[simp]
theorem Ringₓ.inverse_invertible (x : α) [Invertible x] : Ring.inverse x = ⅟ x :=
  Ring.inverse_unit (unitOfInvertible _)

end MonoidWithZeroₓ

section GroupWithZeroₓ

variable [GroupWithZeroₓ α]

/-- `a⁻¹` is an inverse of `a` if `a ≠ 0` -/
def invertibleOfNonzero {a : α} (h : a ≠ 0) : Invertible a :=
  ⟨a⁻¹, inv_mul_cancel h, mul_inv_cancel h⟩

@[simp]
theorem inv_of_eq_inv (a : α) [Invertible a] : ⅟ a = a⁻¹ :=
  inv_of_eq_right_inv (mul_inv_cancel (nonzero_of_invertible a))

@[simp]
theorem inv_mul_cancel_of_invertible (a : α) [Invertible a] : a⁻¹ * a = 1 :=
  inv_mul_cancel (nonzero_of_invertible a)

@[simp]
theorem mul_inv_cancel_of_invertible (a : α) [Invertible a] : a * a⁻¹ = 1 :=
  mul_inv_cancel (nonzero_of_invertible a)

@[simp]
theorem div_mul_cancel_of_invertible (a b : α) [Invertible b] : a / b * b = a :=
  div_mul_cancel a (nonzero_of_invertible b)

@[simp]
theorem mul_div_cancel_of_invertible (a b : α) [Invertible b] : a * b / b = a :=
  mul_div_cancel a (nonzero_of_invertible b)

@[simp]
theorem div_self_of_invertible (a : α) [Invertible a] : a / a = 1 :=
  div_self (nonzero_of_invertible a)

/-- `b / a` is the inverse of `a / b` -/
def invertibleDiv (a b : α) [Invertible a] [Invertible b] : Invertible (a / b) :=
  ⟨b / a, by
    simp [mul_div_assoc], by
    simp [mul_div_assoc]⟩

@[simp]
theorem inv_of_div (a b : α) [Invertible a] [Invertible b] [Invertible (a / b)] : ⅟ (a / b) = b / a :=
  inv_of_eq_right_inv
    (by
      simp [mul_div_assoc])

/-- `a` is the inverse of `a⁻¹` -/
def invertibleInv {a : α} [Invertible a] : Invertible a⁻¹ :=
  ⟨a, by
    simp , by
    simp ⟩

end GroupWithZeroₓ

/-- Monoid homs preserve invertibility. -/
def Invertible.map {R : Type _} {S : Type _} {F : Type _} [MulOneClassₓ R] [MulOneClassₓ S] [MonoidHomClass F R S]
    (f : F) (r : R) [Invertible r] : Invertible (f r) where
  invOf := f (⅟ r)
  inv_of_mul_self := by
    rw [← map_mul, inv_of_mul_self, map_one]
  mul_inv_of_self := by
    rw [← map_mul, mul_inv_of_self, map_one]

