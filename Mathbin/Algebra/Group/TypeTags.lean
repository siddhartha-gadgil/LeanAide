/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathbin.Algebra.Hom.Group
import Mathbin.Logic.Equiv.Basic

/-!
# Type tags that turn additive structures into multiplicative, and vice versa

We define two type tags:

* `additive α`: turns any multiplicative structure on `α` into the corresponding
  additive structure on `additive α`;
* `multiplicative α`: turns any additive structure on `α` into the corresponding
  multiplicative structure on `multiplicative α`.

We also define instances `additive.*` and `multiplicative.*` that actually transfer the structures.

## See also

This file is similar to `order.synonym`.
-/


universe u v

variable {α : Type u} {β : Type v}

/-- If `α` carries some multiplicative structure, then `additive α` carries the corresponding
additive structure. -/
def Additive (α : Type _) :=
  α

/-- If `α` carries some additive structure, then `multiplicative α` carries the corresponding
multiplicative structure. -/
def Multiplicative (α : Type _) :=
  α

namespace Additive

/-- Reinterpret `x : α` as an element of `additive α`. -/
def ofMul : α ≃ Additive α :=
  ⟨fun x => x, fun x => x, fun x => rfl, fun x => rfl⟩

/-- Reinterpret `x : additive α` as an element of `α`. -/
def toMul : Additive α ≃ α :=
  ofMul.symm

@[simp]
theorem of_mul_symm_eq : (@ofMul α).symm = to_mul :=
  rfl

@[simp]
theorem to_mul_symm_eq : (@toMul α).symm = of_mul :=
  rfl

end Additive

namespace Multiplicative

/-- Reinterpret `x : α` as an element of `multiplicative α`. -/
def ofAdd : α ≃ Multiplicative α :=
  ⟨fun x => x, fun x => x, fun x => rfl, fun x => rfl⟩

/-- Reinterpret `x : multiplicative α` as an element of `α`. -/
def toAdd : Multiplicative α ≃ α :=
  ofAdd.symm

@[simp]
theorem of_add_symm_eq : (@ofAdd α).symm = to_add :=
  rfl

@[simp]
theorem to_add_symm_eq : (@toAdd α).symm = of_add :=
  rfl

end Multiplicative

@[simp]
theorem to_add_of_add (x : α) : (Multiplicative.ofAdd x).toAdd = x :=
  rfl

@[simp]
theorem of_add_to_add (x : Multiplicative α) : Multiplicative.ofAdd x.toAdd = x :=
  rfl

@[simp]
theorem to_mul_of_mul (x : α) : (Additive.ofMul x).toMul = x :=
  rfl

@[simp]
theorem of_mul_to_mul (x : Additive α) : Additive.ofMul x.toMul = x :=
  rfl

instance [Inhabited α] : Inhabited (Additive α) :=
  ⟨Additive.ofMul default⟩

instance [Inhabited α] : Inhabited (Multiplicative α) :=
  ⟨Multiplicative.ofAdd default⟩

instance [Nontrivial α] : Nontrivial (Additive α) :=
  Additive.ofMul.Injective.Nontrivial

instance [Nontrivial α] : Nontrivial (Multiplicative α) :=
  Multiplicative.ofAdd.Injective.Nontrivial

instance Additive.hasAdd [Mul α] : Add (Additive α) where add := fun x y => Additive.ofMul (x.toMul * y.toMul)

instance [Add α] : Mul (Multiplicative α) where mul := fun x y => Multiplicative.ofAdd (x.toAdd + y.toAdd)

@[simp]
theorem of_add_add [Add α] (x y : α) : Multiplicative.ofAdd (x + y) = Multiplicative.ofAdd x * Multiplicative.ofAdd y :=
  rfl

@[simp]
theorem to_add_mul [Add α] (x y : Multiplicative α) : (x * y).toAdd = x.toAdd + y.toAdd :=
  rfl

@[simp]
theorem of_mul_mul [Mul α] (x y : α) : Additive.ofMul (x * y) = Additive.ofMul x + Additive.ofMul y :=
  rfl

@[simp]
theorem to_mul_add [Mul α] (x y : Additive α) : (x + y).toMul = x.toMul * y.toMul :=
  rfl

instance [Semigroupₓ α] : AddSemigroupₓ (Additive α) :=
  { Additive.hasAdd with add_assoc := @mul_assoc α _ }

instance [AddSemigroupₓ α] : Semigroupₓ (Multiplicative α) :=
  { Multiplicative.hasMul with mul_assoc := @add_assocₓ α _ }

instance [CommSemigroupₓ α] : AddCommSemigroupₓ (Additive α) :=
  { Additive.addSemigroup with add_comm := @mul_comm _ _ }

instance [AddCommSemigroupₓ α] : CommSemigroupₓ (Multiplicative α) :=
  { Multiplicative.semigroup with mul_comm := @add_commₓ _ _ }

instance [LeftCancelSemigroup α] : AddLeftCancelSemigroup (Additive α) :=
  { Additive.addSemigroup with add_left_cancel := @mul_left_cancelₓ _ _ }

instance [AddLeftCancelSemigroup α] : LeftCancelSemigroup (Multiplicative α) :=
  { Multiplicative.semigroup with mul_left_cancel := @add_left_cancelₓ _ _ }

instance [RightCancelSemigroup α] : AddRightCancelSemigroup (Additive α) :=
  { Additive.addSemigroup with add_right_cancel := @mul_right_cancelₓ _ _ }

instance [AddRightCancelSemigroup α] : RightCancelSemigroup (Multiplicative α) :=
  { Multiplicative.semigroup with mul_right_cancel := @add_right_cancelₓ _ _ }

instance [One α] : Zero (Additive α) :=
  ⟨Additive.ofMul 1⟩

@[simp]
theorem of_mul_one [One α] : @Additive.ofMul α 1 = 0 :=
  rfl

@[simp]
theorem of_mul_eq_zero {A : Type _} [One A] {x : A} : Additive.ofMul x = 0 ↔ x = 1 :=
  Iff.rfl

@[simp]
theorem to_mul_zero [One α] : (0 : Additive α).toMul = 1 :=
  rfl

instance [Zero α] : One (Multiplicative α) :=
  ⟨Multiplicative.ofAdd 0⟩

@[simp]
theorem of_add_zero [Zero α] : @Multiplicative.ofAdd α 0 = 1 :=
  rfl

@[simp]
theorem of_add_eq_one {A : Type _} [Zero A] {x : A} : Multiplicative.ofAdd x = 1 ↔ x = 0 :=
  Iff.rfl

@[simp]
theorem to_add_one [Zero α] : (1 : Multiplicative α).toAdd = 0 :=
  rfl

instance [MulOneClassₓ α] : AddZeroClassₓ (Additive α) where
  zero := 0
  add := (· + ·)
  zero_add := one_mulₓ
  add_zero := mul_oneₓ

instance [AddZeroClassₓ α] : MulOneClassₓ (Multiplicative α) where
  one := 1
  mul := (· * ·)
  one_mul := zero_addₓ
  mul_one := add_zeroₓ

instance [h : Monoidₓ α] : AddMonoidₓ (Additive α) :=
  { Additive.addZeroClass, Additive.addSemigroup with zero := 0, add := (· + ·), nsmul := @Monoidₓ.npow α h,
    nsmul_zero' := Monoidₓ.npow_zero', nsmul_succ' := Monoidₓ.npow_succ' }

instance [h : AddMonoidₓ α] : Monoidₓ (Multiplicative α) :=
  { Multiplicative.mulOneClass, Multiplicative.semigroup with one := 1, mul := (· * ·), npow := @AddMonoidₓ.nsmul α h,
    npow_zero' := AddMonoidₓ.nsmul_zero', npow_succ' := AddMonoidₓ.nsmul_succ' }

instance [LeftCancelMonoid α] : AddLeftCancelMonoid (Additive α) :=
  { Additive.addMonoid, Additive.addLeftCancelSemigroup with zero := 0, add := (· + ·) }

instance [AddLeftCancelMonoid α] : LeftCancelMonoid (Multiplicative α) :=
  { Multiplicative.monoid, Multiplicative.leftCancelSemigroup with one := 1, mul := (· * ·) }

instance [RightCancelMonoid α] : AddRightCancelMonoid (Additive α) :=
  { Additive.addMonoid, Additive.addRightCancelSemigroup with zero := 0, add := (· + ·) }

instance [AddRightCancelMonoid α] : RightCancelMonoid (Multiplicative α) :=
  { Multiplicative.monoid, Multiplicative.rightCancelSemigroup with one := 1, mul := (· * ·) }

instance [CommMonoidₓ α] : AddCommMonoidₓ (Additive α) :=
  { Additive.addMonoid, Additive.addCommSemigroup with zero := 0, add := (· + ·) }

instance [AddCommMonoidₓ α] : CommMonoidₓ (Multiplicative α) :=
  { Multiplicative.monoid, Multiplicative.commSemigroup with one := 1, mul := (· * ·) }

instance [Inv α] : Neg (Additive α) :=
  ⟨fun x => Multiplicative.ofAdd x.toMul⁻¹⟩

@[simp]
theorem of_mul_inv [Inv α] (x : α) : Additive.ofMul x⁻¹ = -Additive.ofMul x :=
  rfl

@[simp]
theorem to_mul_neg [Inv α] (x : Additive α) : (-x).toMul = x.toMul⁻¹ :=
  rfl

instance [Neg α] : Inv (Multiplicative α) :=
  ⟨fun x => Additive.ofMul (-x.toAdd)⟩

@[simp]
theorem of_add_neg [Neg α] (x : α) : Multiplicative.ofAdd (-x) = (Multiplicative.ofAdd x)⁻¹ :=
  rfl

@[simp]
theorem to_add_inv [Neg α] (x : Multiplicative α) : x⁻¹.toAdd = -x.toAdd :=
  rfl

instance Additive.hasSub [Div α] : Sub (Additive α) where sub := fun x y => Additive.ofMul (x.toMul / y.toMul)

instance Multiplicative.hasDiv [Sub α] :
    Div (Multiplicative α) where div := fun x y => Multiplicative.ofAdd (x.toAdd - y.toAdd)

@[simp]
theorem of_add_sub [Sub α] (x y : α) : Multiplicative.ofAdd (x - y) = Multiplicative.ofAdd x / Multiplicative.ofAdd y :=
  rfl

@[simp]
theorem to_add_div [Sub α] (x y : Multiplicative α) : (x / y).toAdd = x.toAdd - y.toAdd :=
  rfl

@[simp]
theorem of_mul_div [Div α] (x y : α) : Additive.ofMul (x / y) = Additive.ofMul x - Additive.ofMul y :=
  rfl

@[simp]
theorem to_mul_sub [Div α] (x y : Additive α) : (x - y).toMul = x.toMul / y.toMul :=
  rfl

instance [HasInvolutiveInv α] : HasInvolutiveNeg (Additive α) :=
  { Additive.hasNeg with neg_neg := @inv_invₓ _ _ }

instance [HasInvolutiveNeg α] : HasInvolutiveInv (Multiplicative α) :=
  { Multiplicative.hasInv with inv_inv := @neg_negₓ _ _ }

instance [DivInvMonoidₓ α] : SubNegMonoidₓ (Additive α) :=
  { Additive.hasNeg, Additive.hasSub, Additive.addMonoid with sub_eq_add_neg := @div_eq_mul_inv α _,
    zsmul := @DivInvMonoidₓ.zpow α _, zsmul_zero' := DivInvMonoidₓ.zpow_zero', zsmul_succ' := DivInvMonoidₓ.zpow_succ',
    zsmul_neg' := DivInvMonoidₓ.zpow_neg' }

instance [SubNegMonoidₓ α] : DivInvMonoidₓ (Multiplicative α) :=
  { Multiplicative.hasInv, Multiplicative.hasDiv, Multiplicative.monoid with div_eq_mul_inv := @sub_eq_add_neg α _,
    zpow := @SubNegMonoidₓ.zsmul α _, zpow_zero' := SubNegMonoidₓ.zsmul_zero', zpow_succ' := SubNegMonoidₓ.zsmul_succ',
    zpow_neg' := SubNegMonoidₓ.zsmul_neg' }

instance [DivisionMonoid α] : SubtractionMonoid (Additive α) :=
  { Additive.subNegMonoid, Additive.hasInvolutiveNeg with neg_add_rev := @mul_inv_rev _ _,
    neg_eq_of_add := @inv_eq_of_mul_eq_one_right _ _ }

instance [SubtractionMonoid α] : DivisionMonoid (Multiplicative α) :=
  { Multiplicative.divInvMonoid, Multiplicative.hasInvolutiveInv with mul_inv_rev := @neg_add_rev _ _,
    inv_eq_of_mul := @neg_eq_of_add_eq_zero_right _ _ }

instance [DivisionCommMonoid α] : SubtractionCommMonoid (Additive α) :=
  { Additive.subtractionMonoid, Additive.addCommSemigroup with }

instance [SubtractionCommMonoid α] : DivisionCommMonoid (Multiplicative α) :=
  { Multiplicative.divisionMonoid, Multiplicative.commSemigroup with }

instance [Groupₓ α] : AddGroupₓ (Additive α) :=
  { Additive.subNegMonoid with add_left_neg := @mul_left_invₓ α _ }

instance [AddGroupₓ α] : Groupₓ (Multiplicative α) :=
  { Multiplicative.divInvMonoid with mul_left_inv := @add_left_negₓ α _ }

instance [CommGroupₓ α] : AddCommGroupₓ (Additive α) :=
  { Additive.addGroup, Additive.addCommMonoid with }

instance [AddCommGroupₓ α] : CommGroupₓ (Multiplicative α) :=
  { Multiplicative.group, Multiplicative.commMonoid with }

open Multiplicative (ofAdd)

open Additive (ofMul)

/-- Reinterpret `α →+ β` as `multiplicative α →* multiplicative β`. -/
@[simps]
def AddMonoidHom.toMultiplicative [AddZeroClassₓ α] [AddZeroClassₓ β] :
    (α →+ β) ≃ (Multiplicative α →* Multiplicative β) where
  toFun := fun f => ⟨fun a => ofAdd (f a.toAdd), f.2, f.3⟩
  invFun := fun f => ⟨fun a => (f (ofAdd a)).toAdd, f.2, f.3⟩
  left_inv := fun x => by
    ext
    rfl
  right_inv := fun x => by
    ext
    rfl

/-- Reinterpret `α →* β` as `additive α →+ additive β`. -/
@[simps]
def MonoidHom.toAdditive [MulOneClassₓ α] [MulOneClassₓ β] : (α →* β) ≃ (Additive α →+ Additive β) where
  toFun := fun f => ⟨fun a => ofMul (f a.toMul), f.2, f.3⟩
  invFun := fun f => ⟨fun a => (f (ofMul a)).toMul, f.2, f.3⟩
  left_inv := fun x => by
    ext
    rfl
  right_inv := fun x => by
    ext
    rfl

/-- Reinterpret `additive α →+ β` as `α →* multiplicative β`. -/
@[simps]
def AddMonoidHom.toMultiplicative' [MulOneClassₓ α] [AddZeroClassₓ β] :
    (Additive α →+ β) ≃ (α →* Multiplicative β) where
  toFun := fun f => ⟨fun a => ofAdd (f (ofMul a)), f.2, f.3⟩
  invFun := fun f => ⟨fun a => (f a.toMul).toAdd, f.2, f.3⟩
  left_inv := fun x => by
    ext
    rfl
  right_inv := fun x => by
    ext
    rfl

/-- Reinterpret `α →* multiplicative β` as `additive α →+ β`. -/
@[simps]
def MonoidHom.toAdditive' [MulOneClassₓ α] [AddZeroClassₓ β] : (α →* Multiplicative β) ≃ (Additive α →+ β) :=
  AddMonoidHom.toMultiplicative'.symm

/-- Reinterpret `α →+ additive β` as `multiplicative α →* β`. -/
@[simps]
def AddMonoidHom.toMultiplicative'' [AddZeroClassₓ α] [MulOneClassₓ β] :
    (α →+ Additive β) ≃ (Multiplicative α →* β) where
  toFun := fun f => ⟨fun a => (f a.toAdd).toMul, f.2, f.3⟩
  invFun := fun f => ⟨fun a => ofMul (f (ofAdd a)), f.2, f.3⟩
  left_inv := fun x => by
    ext
    rfl
  right_inv := fun x => by
    ext
    rfl

/-- Reinterpret `multiplicative α →* β` as `α →+ additive β`. -/
@[simps]
def MonoidHom.toAdditive'' [AddZeroClassₓ α] [MulOneClassₓ β] : (Multiplicative α →* β) ≃ (α →+ Additive β) :=
  AddMonoidHom.toMultiplicative''.symm

/-- If `α` has some multiplicative structure and coerces to a function,
then `additive α` should also coerce to the same function.

This allows `additive` to be used on bundled function types with a multiplicative structure, which
is often used for composition, without affecting the behavior of the function itself.
-/
instance Additive.hasCoeToFun {α : Type _} {β : α → Sort _} [CoeFun α β] : CoeFun (Additive α) fun a => β a.toMul :=
  ⟨fun a => coeFn a.toMul⟩

/-- If `α` has some additive structure and coerces to a function,
then `multiplicative α` should also coerce to the same function.

This allows `multiplicative` to be used on bundled function types with an additive structure, which
is often used for composition, without affecting the behavior of the function itself.
-/
instance Multiplicative.hasCoeToFun {α : Type _} {β : α → Sort _} [CoeFun α β] :
    CoeFun (Multiplicative α) fun a => β a.toAdd :=
  ⟨fun a => coeFn a.toAdd⟩

