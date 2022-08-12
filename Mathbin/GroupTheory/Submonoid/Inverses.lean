/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathbin.GroupTheory.Submonoid.Pointwise

/-!

# Submonoid of inverses

Given a submonoid `N` of a monoid `M`, we define the submonoid `N.left_inv` as the submonoid of
left inverses of `N`. When `M` is commutative, we may define `from_comm_left_inv : N.left_inv →* N`
since the inverses are unique. When `N ≤ is_unit.submonoid M`, this is precisely
the pointwise inverse of `N`, and we may define `left_inv_equiv : S.left_inv ≃* S`.

For the pointwise inverse of submonoids of groups, please refer to
`group_theory.submonoid.pointwise`.

## TODO

Define the submonoid of right inverses and two-sided inverses.
See the comments of #10679 for a possible implementation.

-/


variable {M : Type _}

namespace Submonoid

@[to_additive]
noncomputable instance [Monoidₓ M] : Groupₓ (IsUnit.submonoid M) :=
  { show Monoidₓ (IsUnit.submonoid M) by
      infer_instance with
    inv := fun x => ⟨_, x.Prop.Unit⁻¹.IsUnit⟩, mul_left_inv := fun x => Subtype.eq x.Prop.Unit.inv_val }

@[to_additive]
noncomputable instance [CommMonoidₓ M] : CommGroupₓ (IsUnit.submonoid M) :=
  { show Groupₓ (IsUnit.submonoid M) by
      infer_instance with
    mul_comm := fun a b => mul_comm a b }

@[to_additive]
theorem IsUnit.Submonoid.coe_inv [Monoidₓ M] (x : IsUnit.submonoid M) : ↑x⁻¹ = (↑x.Prop.Unit⁻¹ : M) :=
  rfl

section Monoidₓ

variable [Monoidₓ M] (S : Submonoid M)

/-- `S.left_inv` is the submonoid containing all the left inverses of `S`. -/
@[to_additive "`S.left_neg` is the additive submonoid containing all the left additive inverses\nof `S`."]
def leftInv : Submonoid M where
  Carrier := { x : M | ∃ y : S, x * y = 1 }
  one_mem' := ⟨1, mul_oneₓ 1⟩
  mul_mem' := fun a b ⟨a', ha⟩ ⟨b', hb⟩ =>
    ⟨b' * a', by
      rw [coe_mul, ← mul_assoc, mul_assoc a, hb, mul_oneₓ, ha]⟩

@[to_additive]
theorem left_inv_left_inv_le : S.left_inv.left_inv ≤ S := by
  rintro x ⟨⟨y, z, h₁⟩, h₂ : x * y = 1⟩
  convert z.prop
  rw [← mul_oneₓ x, ← h₁, ← mul_assoc, h₂, one_mulₓ]

@[to_additive]
theorem unit_mem_left_inv (x : Mˣ) (hx : (x : M) ∈ S) : ((x⁻¹ : _) : M) ∈ S.left_inv :=
  ⟨⟨x, hx⟩, x.inv_val⟩

@[to_additive]
theorem left_inv_left_inv_eq (hS : S ≤ IsUnit.submonoid M) : S.left_inv.left_inv = S := by
  refine' le_antisymmₓ S.left_inv_left_inv_le _
  intro x hx
  have : x = ((hS hx).Unit⁻¹⁻¹ : Mˣ) := by
    rw [inv_invₓ (hS hx).Unit]
    rfl
  rw [this]
  exact S.left_inv.unit_mem_left_inv _ (S.unit_mem_left_inv _ hx)

/-- The function from `S.left_inv` to `S` sending an element to its right inverse in `S`.
This is a `monoid_hom` when `M` is commutative. -/
@[to_additive
      "The function from `S.left_add` to `S` sending an element to its right additive\ninverse in `S`. This is an `add_monoid_hom` when `M` is commutative."]
noncomputable def fromLeftInv : S.left_inv → S := fun x => x.Prop.some

@[simp, to_additive]
theorem mul_from_left_inv (x : S.left_inv) : (x : M) * S.fromLeftInv x = 1 :=
  x.Prop.some_spec

@[simp, to_additive]
theorem from_left_inv_one : S.fromLeftInv 1 = 1 :=
  (one_mulₓ _).symm.trans (Subtype.eq <| S.mul_from_left_inv 1)

end Monoidₓ

section CommMonoidₓ

variable [CommMonoidₓ M] (S : Submonoid M)

@[simp, to_additive]
theorem from_left_inv_mul (x : S.left_inv) : (S.fromLeftInv x : M) * x = 1 := by
  rw [mul_comm, mul_from_left_inv]

@[to_additive]
theorem left_inv_le_is_unit : S.left_inv ≤ IsUnit.submonoid M := fun x ⟨y, hx⟩ => ⟨⟨x, y, hx, mul_comm x y ▸ hx⟩, rfl⟩

@[to_additive]
theorem from_left_inv_eq_iff (a : S.left_inv) (b : M) : (S.fromLeftInv a : M) = b ↔ (a : M) * b = 1 := by
  rw [← IsUnit.mul_right_inj (left_inv_le_is_unit _ a.prop), S.mul_from_left_inv, eq_comm]

/-- The `monoid_hom` from `S.left_inv` to `S` sending an element to its right inverse in `S`. -/
@[to_additive "The `add_monoid_hom` from `S.left_neg` to `S` sending an element to its\nright additive inverse in `S`.",
  simps]
noncomputable def fromCommLeftInv : S.left_inv →* S where
  toFun := S.fromLeftInv
  map_one' := S.from_left_inv_one
  map_mul' := fun x y =>
    Subtype.ext <| by
      rw [from_left_inv_eq_iff, mul_comm x, Submonoid.coe_mul, Submonoid.coe_mul, mul_assoc, ← mul_assoc (x : M),
        mul_from_left_inv, one_mulₓ, mul_from_left_inv]

variable (hS : S ≤ IsUnit.submonoid M)

include hS

/-- The submonoid of pointwise inverse of `S` is `mul_equiv` to `S`. -/
@[to_additive "The additive submonoid of pointwise additive inverse of `S` is\n`add_equiv` to `S`.", simps apply]
noncomputable def leftInvEquiv : S.left_inv ≃* S :=
  { S.fromCommLeftInv with
    invFun := fun x => by
      choose x' hx using hS x.prop
      exact ⟨x'.inv, x, hx ▸ x'.inv_val⟩,
    left_inv := fun x =>
      Subtype.eq <| by
        dsimp'
        generalize_proofs h
        rw [← h.some.mul_left_inj]
        exact
          h.some.inv_val.trans
            ((S.mul_from_left_inv x).symm.trans
              (by
                rw [h.some_spec])),
    right_inv := fun x => by
      dsimp'
      ext
      rw [from_left_inv_eq_iff]
      convert (hS x.prop).some.inv_val
      exact (hS x.prop).some_spec.symm }

@[simp, to_additive]
theorem from_left_inv_left_inv_equiv_symm (x : S) : S.fromLeftInv ((S.leftInvEquiv hS).symm x) = x :=
  (S.leftInvEquiv hS).right_inv x

@[simp, to_additive]
theorem left_inv_equiv_symm_from_left_inv (x : S.left_inv) : (S.leftInvEquiv hS).symm (S.fromLeftInv x) = x :=
  (S.leftInvEquiv hS).left_inv x

@[to_additive]
theorem left_inv_equiv_mul (x : S.left_inv) : (S.leftInvEquiv hS x : M) * x = 1 := by
  simp

@[to_additive]
theorem mul_left_inv_equiv (x : S.left_inv) : (x : M) * S.leftInvEquiv hS x = 1 := by
  simp

@[simp, to_additive]
theorem left_inv_equiv_symm_mul (x : S) : ((S.leftInvEquiv hS).symm x : M) * x = 1 := by
  convert S.mul_left_inv_equiv hS ((S.left_inv_equiv hS).symm x)
  simp

@[simp, to_additive]
theorem mul_left_inv_equiv_symm (x : S) : (x : M) * (S.leftInvEquiv hS).symm x = 1 := by
  convert S.left_inv_equiv_mul hS ((S.left_inv_equiv hS).symm x)
  simp

end CommMonoidₓ

section Groupₓ

variable [Groupₓ M] (S : Submonoid M)

open Pointwise

@[to_additive]
theorem left_inv_eq_inv : S.left_inv = S⁻¹ :=
  Submonoid.ext fun x =>
    ⟨fun h => Submonoid.mem_inv.mpr ((inv_eq_of_mul_eq_one_right h.some_spec).symm ▸ h.some.Prop), fun h =>
      ⟨⟨_, h⟩, mul_right_invₓ _⟩⟩

@[simp, to_additive]
theorem from_left_inv_eq_inv (x : S.left_inv) : (S.fromLeftInv x : M) = x⁻¹ := by
  rw [← mul_right_injₓ (x : M), mul_right_invₓ, mul_from_left_inv]

end Groupₓ

section CommGroupₓ

variable [CommGroupₓ M] (S : Submonoid M) (hS : S ≤ IsUnit.submonoid M)

@[simp, to_additive]
theorem left_inv_equiv_symm_eq_inv (x : S) : ((S.leftInvEquiv hS).symm x : M) = x⁻¹ := by
  rw [← mul_right_injₓ (x : M), mul_right_invₓ, mul_left_inv_equiv_symm]

end CommGroupₓ

end Submonoid

