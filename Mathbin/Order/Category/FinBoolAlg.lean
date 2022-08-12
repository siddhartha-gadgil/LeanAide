/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathbin.Order.Category.BoolAlg
import Mathbin.Order.Category.FinPartialOrder
import Mathbin.Order.Hom.CompleteLattice

/-!
# The category of finite boolean algebras

This file defines `FinBoolAlg`, the category of finite boolean algebras.

## TODO

Birkhoff's representation for finite Boolean algebras.

`Fintype_to_FinBoolAlg_op.left_op ⋙ FinBoolAlg.dual ≅ Fintype_to_FinBoolAlg_op.left_op`

`FinBoolAlg` is essentially small.
-/


universe u

open CategoryTheory OrderDual Opposite

/-- The category of finite boolean algebras with bounded lattice morphisms. -/
structure FinBoolAlg where
  toBoolAlg : BoolAlg
  [isFintype : Fintype to_BoolAlg]

namespace FinBoolAlg

instance : CoeSort FinBoolAlg (Type _) :=
  ⟨fun X => X.toBoolAlg⟩

instance (X : FinBoolAlg) : BooleanAlgebra X :=
  X.toBoolAlg.str

attribute [instance] FinBoolAlg.isFintype

@[simp]
theorem coe_to_BoolAlg (X : FinBoolAlg) : ↥X.toBoolAlg = ↥X :=
  rfl

/-- Construct a bundled `FinBoolAlg` from `boolean_algebra` + `fintype`. -/
def of (α : Type _) [BooleanAlgebra α] [Fintype α] : FinBoolAlg :=
  ⟨⟨α⟩⟩

@[simp]
theorem coe_of (α : Type _) [BooleanAlgebra α] [Fintype α] : ↥(of α) = α :=
  rfl

instance : Inhabited FinBoolAlg :=
  ⟨of PUnit⟩

instance largeCategory : LargeCategory FinBoolAlg :=
  InducedCategory.category FinBoolAlg.toBoolAlg

instance concreteCategory : ConcreteCategory FinBoolAlg :=
  InducedCategory.concreteCategory FinBoolAlg.toBoolAlg

instance hasForgetToBoolAlg : HasForget₂ FinBoolAlg BoolAlg :=
  InducedCategory.hasForget₂ FinBoolAlg.toBoolAlg

instance forgetToBoolAlgFull : Full (forget₂ FinBoolAlg BoolAlg) :=
  InducedCategory.full _

instance forget_to_BoolAlg_faithful : Faithful (forget₂ FinBoolAlg BoolAlg) :=
  InducedCategory.faithful _

@[simps]
instance hasForgetToFinPartialOrder :
    HasForget₂ FinBoolAlg
      FinPartialOrder where forget₂ :=
    { obj := fun X => FinPartialOrder.of X,
      map := fun X Y f => show OrderHom X Y from ↑(show BoundedLatticeHom X Y from f) }

instance forget_to_FinPartialOrder_faithful : Faithful (forget₂ FinBoolAlg FinPartialOrder) :=
  ⟨fun X Y f g h => by
    have := congr_arg (coeFn : _ → X → Y) h
    exact FunLike.coe_injective this⟩

/-- Constructs an equivalence between finite Boolean algebras from an order isomorphism between
them. -/
@[simps]
def Iso.mk {α β : FinBoolAlg.{u}} (e : α ≃o β) : α ≅ β where
  Hom := (e : BoundedLatticeHom α β)
  inv := (e.symm : BoundedLatticeHom β α)
  hom_inv_id' := by
    ext
    exact e.symm_apply_apply _
  inv_hom_id' := by
    ext
    exact e.apply_symm_apply _

/-- `order_dual` as a functor. -/
@[simps]
def dual : FinBoolAlg ⥤ FinBoolAlg where
  obj := fun X => of Xᵒᵈ
  map := fun X Y => BoundedLatticeHom.dual

/-- The equivalence between `FinBoolAlg` and itself induced by `order_dual` both ways. -/
@[simps Functor inverse]
def dualEquiv : FinBoolAlg ≌ FinBoolAlg :=
  Equivalence.mk dual dual ((NatIso.ofComponents fun X => iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)
    ((NatIso.ofComponents fun X => iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)

end FinBoolAlg

/-- The powerset functor. `set` as a functor. -/
@[simps]
def fintypeToFinBoolAlgOp : Fintypeₓ ⥤ FinBoolAlgᵒᵖ where
  obj := fun X => op <| FinBoolAlg.of (Set X)
  map := fun X Y f => Quiver.Hom.op <| (CompleteLatticeHom.setPreimage f : BoundedLatticeHom (Set Y) (Set X))

