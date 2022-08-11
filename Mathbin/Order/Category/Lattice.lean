/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathbin.Order.Category.PartialOrder
import Mathbin.Order.Hom.Lattice

/-!
# The category of lattices

This defines `Lattice`, the category of lattices.

Note that `Lattice` doesn't correspond to the literature definition of [`Lat`]
(https://ncatlab.org/nlab/show/Lat) as we don't require bottom or top elements. Instead, `Lat`
corresponds to `BoundedLattice` (not yet in mathlib).

## TODO

The free functor from `Lattice` to `BoundedLattice` is `X → with_top (with_bot X)`.
-/


universe u

open CategoryTheory

/-- The category of lattices. -/
def Latticeₓ :=
  Bundled Lattice

namespace Latticeₓ

instance : CoeSort Latticeₓ (Type _) :=
  bundled.has_coe_to_sort

instance (X : Latticeₓ) : Lattice X :=
  X.str

/-- Construct a bundled `Lattice` from a `lattice`. -/
def of (α : Type _) [Lattice α] : Latticeₓ :=
  Bundled.of α

@[simp]
theorem coe_of (α : Type _) [Lattice α] : ↥(of α) = α :=
  rfl

instance : Inhabited Latticeₓ :=
  ⟨of Bool⟩

instance : BundledHom @LatticeHom where
  toFun := fun _ _ _ _ => coeFn
  id := @LatticeHom.id
  comp := @LatticeHom.comp
  hom_ext := fun X Y _ _ => FunLike.coe_injective

instance : LargeCategory.{u} Latticeₓ :=
  BundledHom.category LatticeHom

instance : ConcreteCategory Latticeₓ :=
  BundledHom.concreteCategory LatticeHom

instance hasForgetToPartialOrder : HasForget₂ Latticeₓ PartialOrderₓₓ where
  forget₂ := { obj := fun X => ⟨X⟩, map := fun X Y f => f }
  forget_comp := rfl

/-- Constructs an isomorphism of lattices from an order isomorphism between them. -/
@[simps]
def Iso.mk {α β : Latticeₓ.{u}} (e : α ≃o β) : α ≅ β where
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
def dual : Latticeₓ ⥤ Latticeₓ where
  obj := fun X => of Xᵒᵈ
  map := fun X Y => LatticeHom.dual

/-- The equivalence between `Lattice` and itself induced by `order_dual` both ways. -/
@[simps Functor inverse]
def dualEquiv : Latticeₓ ≌ Latticeₓ :=
  Equivalence.mk dual dual ((NatIso.ofComponents fun X => iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)
    ((NatIso.ofComponents fun X => iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)

end Latticeₓ

theorem Lattice_dual_comp_forget_to_PartialOrder :
    Latticeₓ.dual ⋙ forget₂ Latticeₓ PartialOrderₓₓ = forget₂ Latticeₓ PartialOrderₓₓ ⋙ PartialOrderₓₓ.dual :=
  rfl

