/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathbin.Order.Category.BoundedDistribLattice

/-!
# The category of boolean algebras

This defines `BoolAlg`, the category of boolean algebras.
-/


open OrderDual Opposite Set

universe u

open CategoryTheory

/-- The category of boolean algebras. -/
def BoolAlg :=
  Bundled BooleanAlgebra

namespace BoolAlg

instance : CoeSort BoolAlg (Type _) :=
  bundled.has_coe_to_sort

instance (X : BoolAlg) : BooleanAlgebra X :=
  X.str

/-- Construct a bundled `BoolAlg` from a `boolean_algebra`. -/
def of (α : Type _) [BooleanAlgebra α] : BoolAlg :=
  Bundled.of α

@[simp]
theorem coe_of (α : Type _) [BooleanAlgebra α] : ↥(of α) = α :=
  rfl

instance : Inhabited BoolAlg :=
  ⟨of PUnit⟩

/-- Turn a `BoolAlg` into a `BoundedDistribLattice` by forgetting its complement operation. -/
def toBoundedDistribLattice (X : BoolAlg) : BoundedDistribLattice :=
  BoundedDistribLattice.of X

@[simp]
theorem coe_to_BoundedDistribLattice (X : BoolAlg) : ↥X.toBoundedDistribLattice = ↥X :=
  rfl

instance : LargeCategory.{u} BoolAlg :=
  InducedCategory.category toBoundedDistribLattice

instance : ConcreteCategory BoolAlg :=
  InducedCategory.concreteCategory toBoundedDistribLattice

instance hasForgetToBoundedDistribLattice : HasForget₂ BoolAlg BoundedDistribLattice :=
  InducedCategory.hasForget₂ toBoundedDistribLattice

/-- Constructs an equivalence between boolean algebras from an order isomorphism
between them. -/
@[simps]
def Iso.mk {α β : BoolAlg.{u}} (e : α ≃o β) : α ≅ β where
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
def dual : BoolAlg ⥤ BoolAlg where
  obj := fun X => of Xᵒᵈ
  map := fun X Y => BoundedLatticeHom.dual

/-- The equivalence between `BoolAlg` and itself induced by `order_dual` both ways. -/
@[simps Functor inverse]
def dualEquiv : BoolAlg ≌ BoolAlg :=
  Equivalence.mk dual dual ((NatIso.ofComponents fun X => iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)
    ((NatIso.ofComponents fun X => iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)

end BoolAlg

theorem BoolAlg_dual_comp_forget_to_BoundedDistribLattice :
    BoolAlg.dual ⋙ forget₂ BoolAlg BoundedDistribLattice =
      forget₂ BoolAlg BoundedDistribLattice ⋙ BoundedDistribLattice.dual :=
  rfl

