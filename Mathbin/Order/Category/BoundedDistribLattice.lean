/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathbin.Order.Category.BoundedLattice
import Mathbin.Order.Category.DistribLattice

/-!
# The category of bounded distributive lattices

This defines `BoundedDistribLattice`, the category of bounded distributive lattices.

Note that this category is sometimes called [`DistLat`](https://ncatlab.org/nlab/show/DistLat) when
being a lattice is understood to entail having a bottom and a top element.
-/


universe u

open CategoryTheory

/-- The category of bounded distributive lattices with bounded lattice morphisms. -/
structure BoundedDistribLattice where
  toDistribLattice : DistribLatticeₓ
  [isBoundedOrder : BoundedOrder to_DistribLattice]

namespace BoundedDistribLattice

instance : CoeSort BoundedDistribLattice (Type _) :=
  ⟨fun X => X.toDistribLattice⟩

instance (X : BoundedDistribLattice) : DistribLattice X :=
  X.toDistribLattice.str

attribute [instance] BoundedDistribLattice.isBoundedOrder

/-- Construct a bundled `BoundedDistribLattice` from a `bounded_order` `distrib_lattice`. -/
def of (α : Type _) [DistribLattice α] [BoundedOrder α] : BoundedDistribLattice :=
  ⟨⟨α⟩⟩

@[simp]
theorem coe_of (α : Type _) [DistribLattice α] [BoundedOrder α] : ↥(of α) = α :=
  rfl

instance : Inhabited BoundedDistribLattice :=
  ⟨of PUnit⟩

/-- Turn a `BoundedDistribLattice` into a `BoundedLattice` by forgetting it is distributive. -/
def toBoundedLattice (X : BoundedDistribLattice) : BoundedLattice :=
  BoundedLattice.of X

@[simp]
theorem coe_to_BoundedLattice (X : BoundedDistribLattice) : ↥X.toBoundedLattice = ↥X :=
  rfl

instance : LargeCategory.{u} BoundedDistribLattice :=
  InducedCategory.category toBoundedLattice

instance : ConcreteCategory BoundedDistribLattice :=
  InducedCategory.concreteCategory toBoundedLattice

instance hasForgetToDistribLattice :
    HasForget₂ BoundedDistribLattice
      DistribLatticeₓ where forget₂ := { obj := fun X => ⟨X⟩, map := fun X Y => BoundedLatticeHom.toLatticeHom }

instance hasForgetToBoundedLattice : HasForget₂ BoundedDistribLattice BoundedLattice :=
  InducedCategory.hasForget₂ toBoundedLattice

theorem forget_BoundedLattice_Lattice_eq_forget_DistribLattice_Lattice :
    forget₂ BoundedDistribLattice BoundedLattice ⋙ forget₂ BoundedLattice Latticeₓ =
      forget₂ BoundedDistribLattice DistribLatticeₓ ⋙ forget₂ DistribLatticeₓ Latticeₓ :=
  rfl

/-- Constructs an equivalence between bounded distributive lattices from an order isomorphism
between them. -/
@[simps]
def Iso.mk {α β : BoundedDistribLattice.{u}} (e : α ≃o β) : α ≅ β where
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
def dual : BoundedDistribLattice ⥤ BoundedDistribLattice where
  obj := fun X => of Xᵒᵈ
  map := fun X Y => BoundedLatticeHom.dual

/-- The equivalence between `BoundedDistribLattice` and itself induced by `order_dual` both ways. -/
@[simps Functor inverse]
def dualEquiv : BoundedDistribLattice ≌ BoundedDistribLattice :=
  Equivalence.mk dual dual ((NatIso.ofComponents fun X => iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)
    ((NatIso.ofComponents fun X => iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)

end BoundedDistribLattice

theorem BoundedDistribLattice_dual_comp_forget_to_DistribLattice :
    BoundedDistribLattice.dual ⋙ forget₂ BoundedDistribLattice DistribLatticeₓ =
      forget₂ BoundedDistribLattice DistribLatticeₓ ⋙ DistribLatticeₓ.dual :=
  rfl

