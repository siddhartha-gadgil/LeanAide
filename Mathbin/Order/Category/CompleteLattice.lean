/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathbin.Order.Category.BoundedLattice
import Mathbin.Order.Hom.CompleteLattice

/-!
# The category of complete lattices

This file defines `CompleteLattice`, the category of complete lattices.
-/


universe u

open CategoryTheory

/-- The category of complete lattices. -/
def CompleteLatticeₓ :=
  Bundled CompleteLattice

namespace CompleteLatticeₓ

instance : CoeSort CompleteLatticeₓ (Type _) :=
  bundled.has_coe_to_sort

instance (X : CompleteLatticeₓ) : CompleteLattice X :=
  X.str

/-- Construct a bundled `CompleteLattice` from a `complete_lattice`. -/
def of (α : Type _) [CompleteLattice α] : CompleteLatticeₓ :=
  Bundled.of α

@[simp]
theorem coe_of (α : Type _) [CompleteLattice α] : ↥(of α) = α :=
  rfl

instance : Inhabited CompleteLatticeₓ :=
  ⟨of PUnit⟩

instance : BundledHom @CompleteLatticeHom where
  toFun := fun _ _ _ _ => coeFn
  id := @CompleteLatticeHom.id
  comp := @CompleteLatticeHom.comp
  hom_ext := fun X Y _ _ => FunLike.coe_injective

instance : LargeCategory.{u} CompleteLatticeₓ :=
  BundledHom.category CompleteLatticeHom

instance : ConcreteCategory CompleteLatticeₓ :=
  BundledHom.concreteCategory CompleteLatticeHom

instance hasForgetToBoundedLattice : HasForget₂ CompleteLatticeₓ BoundedLattice where
  forget₂ := { obj := fun X => BoundedLattice.of X, map := fun X Y => CompleteLatticeHom.toBoundedLatticeHom }
  forget_comp := rfl

/-- Constructs an isomorphism of complete lattices from an order isomorphism between them. -/
@[simps]
def Iso.mk {α β : CompleteLatticeₓ.{u}} (e : α ≃o β) : α ≅ β where
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
def dual : CompleteLatticeₓ ⥤ CompleteLatticeₓ where
  obj := fun X => of Xᵒᵈ
  map := fun X Y => CompleteLatticeHom.dual

/-- The equivalence between `CompleteLattice` and itself induced by `order_dual` both ways. -/
@[simps Functor inverse]
def dualEquiv : CompleteLatticeₓ ≌ CompleteLatticeₓ :=
  Equivalence.mk dual dual ((NatIso.ofComponents fun X => iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)
    ((NatIso.ofComponents fun X => iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)

end CompleteLatticeₓ

theorem CompleteLattice_dual_comp_forget_to_BoundedLattice :
    CompleteLatticeₓ.dual ⋙ forget₂ CompleteLatticeₓ BoundedLattice =
      forget₂ CompleteLatticeₓ BoundedLattice ⋙ BoundedLattice.dual :=
  rfl

