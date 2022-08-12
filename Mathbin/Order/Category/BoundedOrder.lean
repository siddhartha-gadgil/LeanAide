/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathbin.CategoryTheory.Category.Bipointed
import Mathbin.Order.Category.PartialOrder
import Mathbin.Order.Hom.Bounded

/-!
# The category of bounded orders

This defines `BoundedOrder`, the category of bounded orders.
-/


universe u v

open CategoryTheory

/-- The category of bounded orders with monotone functions. -/
structure BoundedOrderCat where
  toPartialOrder : PartialOrderₓₓ
  [isBoundedOrder : BoundedOrder to_PartialOrder]

namespace BoundedOrderCat

instance : CoeSort BoundedOrderCat (Type _) :=
  InducedCategory.hasCoeToSort toPartialOrder

instance (X : BoundedOrderCat) : PartialOrderₓ X :=
  X.toPartialOrder.str

attribute [instance] BoundedOrderCat.isBoundedOrder

/-- Construct a bundled `BoundedOrder` from a `fintype` `partial_order`. -/
def of (α : Type _) [PartialOrderₓ α] [BoundedOrder α] : BoundedOrderCat :=
  ⟨⟨α⟩⟩

@[simp]
theorem coe_of (α : Type _) [PartialOrderₓ α] [BoundedOrder α] : ↥(of α) = α :=
  rfl

instance : Inhabited BoundedOrderCat :=
  ⟨of PUnit⟩

instance largeCategory : LargeCategory.{u} BoundedOrderCat where
  Hom := fun X Y => BoundedOrderHom X Y
  id := fun X => BoundedOrderHom.id X
  comp := fun X Y Z f g => g.comp f
  id_comp' := fun X Y => BoundedOrderHom.comp_id
  comp_id' := fun X Y => BoundedOrderHom.id_comp
  assoc' := fun W X Y Z _ _ _ => BoundedOrderHom.comp_assoc _ _ _

instance concreteCategory : ConcreteCategory BoundedOrderCat where
  forget := ⟨coeSort, fun X Y => coeFn, fun X => rfl, fun X Y Z f g => rfl⟩
  forget_faithful :=
    ⟨fun X Y => by
      convert FunLike.coe_injective⟩

instance hasForgetToPartialOrder :
    HasForget₂ BoundedOrderCat
      PartialOrderₓₓ where forget₂ := { obj := fun X => X.toPartialOrder, map := fun X Y => BoundedOrderHom.toOrderHom }

instance hasForgetToBipointed : HasForget₂ BoundedOrderCat Bipointed where
  forget₂ := { obj := fun X => ⟨X, ⊥, ⊤⟩, map := fun X Y f => ⟨f, map_bot f, map_top f⟩ }
  forget_comp := rfl

/-- `order_dual` as a functor. -/
@[simps]
def dual : BoundedOrderCat ⥤ BoundedOrderCat where
  obj := fun X => of Xᵒᵈ
  map := fun X Y => BoundedOrderHom.dual

/-- Constructs an equivalence between bounded orders from an order isomorphism between them. -/
@[simps]
def Iso.mk {α β : BoundedOrderCat.{u}} (e : α ≃o β) : α ≅ β where
  Hom := e
  inv := e.symm
  hom_inv_id' := by
    ext
    exact e.symm_apply_apply _
  inv_hom_id' := by
    ext
    exact e.apply_symm_apply _

/-- The equivalence between `BoundedOrder` and itself induced by `order_dual` both ways. -/
@[simps Functor inverse]
def dualEquiv : BoundedOrderCat ≌ BoundedOrderCat :=
  Equivalence.mk dual dual ((NatIso.ofComponents fun X => iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)
    ((NatIso.ofComponents fun X => iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)

end BoundedOrderCat

theorem BoundedOrder_dual_comp_forget_to_PartialOrder :
    BoundedOrderCat.dual ⋙ forget₂ BoundedOrderCat PartialOrderₓₓ =
      forget₂ BoundedOrderCat PartialOrderₓₓ ⋙ PartialOrderₓₓ.dual :=
  rfl

theorem BoundedOrder_dual_comp_forget_to_Bipointed :
    BoundedOrderCat.dual ⋙ forget₂ BoundedOrderCat Bipointed = forget₂ BoundedOrderCat Bipointed ⋙ Bipointed.swap :=
  rfl

