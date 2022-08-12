/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathbin.Algebra.Category.Ring.Basic
import Mathbin.Algebra.Ring.BooleanRing
import Mathbin.Order.Category.BoolAlg

/-!
# The category of Boolean rings

This file defines `BoolRing`, the category of Boolean rings.

## TODO

Finish the equivalence with `BoolAlg`.
-/


universe u

open CategoryTheory Order

/-- The category of Boolean rings. -/
def BoolRing :=
  Bundled BooleanRing

namespace BoolRing

instance : CoeSort BoolRing (Type _) :=
  bundled.has_coe_to_sort

instance (X : BoolRing) : BooleanRing X :=
  X.str

/-- Construct a bundled `BoolRing` from a `boolean_ring`. -/
def of (α : Type _) [BooleanRing α] : BoolRing :=
  Bundled.of α

@[simp]
theorem coe_of (α : Type _) [BooleanRing α] : ↥(of α) = α :=
  rfl

instance : Inhabited BoolRing :=
  ⟨of PUnit⟩

instance : BundledHom.ParentProjection @BooleanRing.toCommRing :=
  ⟨⟩

deriving instance LargeCategory, ConcreteCategory for BoolRing

@[simps]
instance hasForgetToCommRing : HasForget₂ BoolRing CommRingₓₓ :=
  BundledHom.forget₂ _ _

/-- Constructs an isomorphism of Boolean rings from a ring isomorphism between them. -/
@[simps]
def Iso.mk {α β : BoolRing.{u}} (e : α ≃+* β) : α ≅ β where
  Hom := e
  inv := e.symm
  hom_inv_id' := by
    ext
    exact e.symm_apply_apply _
  inv_hom_id' := by
    ext
    exact e.apply_symm_apply _

end BoolRing

/-! ### Equivalence between `BoolAlg` and `BoolRing` -/


@[simps]
instance BoolRing.hasForgetToBoolAlg :
    HasForget₂ BoolRing
      BoolAlg where forget₂ := { obj := fun X => BoolAlg.of (AsBoolalg X), map := fun X Y => RingHom.asBoolalg }

@[simps]
instance BoolAlg.hasForgetToBoolRing :
    HasForget₂ BoolAlg
      BoolRing where forget₂ :=
    { obj := fun X => BoolRing.of (AsBoolring X), map := fun X Y => BoundedLatticeHom.asBoolring }

/-- The equivalence between Boolean rings and Boolean algebras. This is actually an isomorphism. -/
@[simps Functor inverse]
def boolRingEquivBoolAlg : BoolRing ≌ BoolAlg :=
  Equivalence.mk (forget₂ BoolRing BoolAlg) (forget₂ BoolAlg BoolRing)
    ((NatIso.ofComponents fun X => BoolRing.Iso.mk <| (RingEquiv.asBoolringAsBoolalg X).symm) fun X Y f => rfl)
    ((NatIso.ofComponents fun X => BoolAlg.Iso.mk <| OrderIso.asBoolalgAsBoolring X) fun X Y f => rfl)

