/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathbin.CategoryTheory.Fintype
import Mathbin.Order.Category.PartialOrder

/-!
# The category of finite partial orders

This defines `FinPartialOrder`, the category of finite partial orders.

Note: `FinPartialOrder` is NOT a subcategory of `BoundedOrder` because its morphisms do not
preserve `⊥` and `⊤`.

## TODO

`FinPartialOrder` is equivalent to a small category.
-/


universe u v

open CategoryTheory

/-- The category of finite partial orders with monotone functions. -/
structure FinPartialOrder where
  toPartialOrder : PartialOrderₓₓ
  [isFintype : Fintype to_PartialOrder]

namespace FinPartialOrder

instance : CoeSort FinPartialOrder (Type _) :=
  ⟨fun X => X.toPartialOrder⟩

instance (X : FinPartialOrder) : PartialOrderₓ X :=
  X.toPartialOrder.str

attribute [instance] FinPartialOrder.isFintype

@[simp]
theorem coe_to_PartialOrder (X : FinPartialOrder) : ↥X.toPartialOrder = ↥X :=
  rfl

/-- Construct a bundled `FinPartialOrder` from `fintype` + `partial_order`. -/
def of (α : Type _) [PartialOrderₓ α] [Fintype α] : FinPartialOrder :=
  ⟨⟨α⟩⟩

@[simp]
theorem coe_of (α : Type _) [PartialOrderₓ α] [Fintype α] : ↥(of α) = α :=
  rfl

instance : Inhabited FinPartialOrder :=
  ⟨of PUnit⟩

instance largeCategory : LargeCategory FinPartialOrder :=
  InducedCategory.category FinPartialOrder.toPartialOrder

instance concreteCategory : ConcreteCategory FinPartialOrder :=
  InducedCategory.concreteCategory FinPartialOrder.toPartialOrder

instance hasForgetToPartialOrder : HasForget₂ FinPartialOrder PartialOrderₓₓ :=
  InducedCategory.hasForget₂ FinPartialOrder.toPartialOrder

instance hasForgetToFintype :
    HasForget₂ FinPartialOrder Fintypeₓ where forget₂ := { obj := fun X => ⟨X⟩, map := fun X Y => coeFn }

/-- Constructs an isomorphism of finite partial orders from an order isomorphism between them. -/
@[simps]
def Iso.mk {α β : FinPartialOrder.{u}} (e : α ≃o β) : α ≅ β where
  Hom := e
  inv := e.symm
  hom_inv_id' := by
    ext
    exact e.symm_apply_apply _
  inv_hom_id' := by
    ext
    exact e.apply_symm_apply _

/-- `order_dual` as a functor. -/
@[simps]
def dual : FinPartialOrder ⥤ FinPartialOrder where
  obj := fun X => of Xᵒᵈ
  map := fun X Y => OrderHom.dual

/-- The equivalence between `FinPartialOrder` and itself induced by `order_dual` both ways. -/
@[simps Functor inverse]
def dualEquiv : FinPartialOrder ≌ FinPartialOrder :=
  Equivalence.mk dual dual ((NatIso.ofComponents fun X => iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)
    ((NatIso.ofComponents fun X => iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)

end FinPartialOrder

theorem FinPartialOrder_dual_comp_forget_to_PartialOrder :
    FinPartialOrder.dual ⋙ forget₂ FinPartialOrder PartialOrderₓₓ =
      forget₂ FinPartialOrder PartialOrderₓₓ ⋙ PartialOrderₓₓ.dual :=
  rfl

