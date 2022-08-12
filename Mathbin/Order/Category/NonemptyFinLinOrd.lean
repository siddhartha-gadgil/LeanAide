/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathbin.Data.Fintype.Order
import Mathbin.Order.Category.LinearOrder

/-!
# Nonempty finite linear orders

This defines `NonemptyFinLinOrd`, the category of nonempty finite linear orders with monotone maps.
This is the index category for simplicial objects.
-/


universe u v

open CategoryTheory

/-- A typeclass for nonempty finite linear orders. -/
class NonemptyFinLinOrd (α : Type _) extends Fintype α, LinearOrderₓ α where
  Nonempty : Nonempty α := by
    run_tac
      tactic.apply_instance

attribute [instance] NonemptyFinLinOrd.nonempty

instance (priority := 100) NonemptyFinLinOrd.toBoundedOrder (α : Type _) [NonemptyFinLinOrd α] : BoundedOrder α :=
  Fintype.toBoundedOrder α

instance PUnit.nonemptyFinLinOrd : NonemptyFinLinOrd PUnit where

instance Finₓ.nonemptyFinLinOrd (n : ℕ) : NonemptyFinLinOrd (Finₓ (n + 1)) where

instance ULift.nonemptyFinLinOrd (α : Type u) [NonemptyFinLinOrd α] : NonemptyFinLinOrd (ULift.{v} α) :=
  { LinearOrderₓ.lift' Equivₓ.ulift (Equivₓ.injective _) with }

instance (α : Type _) [NonemptyFinLinOrd α] : NonemptyFinLinOrd αᵒᵈ :=
  { OrderDual.fintype α with }

/-- The category of nonempty finite linear orders. -/
def NonemptyFinLinOrdₓ :=
  Bundled NonemptyFinLinOrd

namespace NonemptyFinLinOrdₓ

instance : BundledHom.ParentProjection @NonemptyFinLinOrd.toLinearOrder :=
  ⟨⟩

deriving instance LargeCategory, ConcreteCategory for NonemptyFinLinOrdₓ

instance : CoeSort NonemptyFinLinOrdₓ (Type _) :=
  bundled.has_coe_to_sort

/-- Construct a bundled `NonemptyFinLinOrd` from the underlying type and typeclass. -/
def of (α : Type _) [NonemptyFinLinOrd α] : NonemptyFinLinOrdₓ :=
  Bundled.of α

@[simp]
theorem coe_of (α : Type _) [NonemptyFinLinOrd α] : ↥(of α) = α :=
  rfl

instance : Inhabited NonemptyFinLinOrdₓ :=
  ⟨of PUnit⟩

instance (α : NonemptyFinLinOrdₓ) : NonemptyFinLinOrd α :=
  α.str

instance hasForgetToLinearOrder : HasForget₂ NonemptyFinLinOrdₓ LinearOrderₓₓ :=
  BundledHom.forget₂ _ _

/-- Constructs an equivalence between nonempty finite linear orders from an order isomorphism
between them. -/
@[simps]
def Iso.mk {α β : NonemptyFinLinOrdₓ.{u}} (e : α ≃o β) : α ≅ β where
  hom := e
  inv := e.symm
  hom_inv_id' := by
    ext
    exact e.symm_apply_apply x
  inv_hom_id' := by
    ext
    exact e.apply_symm_apply x

/-- `order_dual` as a functor. -/
@[simps]
def dual : NonemptyFinLinOrdₓ ⥤ NonemptyFinLinOrdₓ where
  obj := fun X => of Xᵒᵈ
  map := fun X Y => OrderHom.dual

/-- The equivalence between `FinPartialOrder` and itself induced by `order_dual` both ways. -/
@[simps Functor inverse]
def dualEquiv : NonemptyFinLinOrdₓ ≌ NonemptyFinLinOrdₓ :=
  Equivalence.mk dual dual ((NatIso.ofComponents fun X => iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)
    ((NatIso.ofComponents fun X => iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)

end NonemptyFinLinOrdₓ

theorem NonemptyFinLinOrd_dual_comp_forget_to_LinearOrder :
    NonemptyFinLinOrdₓ.dual ⋙ forget₂ NonemptyFinLinOrdₓ LinearOrderₓₓ =
      forget₂ NonemptyFinLinOrdₓ LinearOrderₓₓ ⋙ LinearOrderₓₓ.dual :=
  rfl

