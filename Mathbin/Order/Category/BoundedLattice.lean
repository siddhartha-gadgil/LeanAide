/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathbin.Order.Category.BoundedOrder
import Mathbin.Order.Category.Lattice
import Mathbin.Order.Category.Semilattice

/-!
# The category of bounded lattices

This file defines `BoundedLattice`, the category of bounded lattices.

In literature, this is sometimes called `Lat`, the category of lattices, because being a lattice is
understood to entail having a bottom and a top element.
-/


universe u

open CategoryTheory

/-- The category of bounded lattices with bounded lattice morphisms. -/
structure BoundedLattice where
  toLattice : Latticeₓ
  [isBoundedOrder : BoundedOrder to_Lattice]

namespace BoundedLattice

instance : CoeSort BoundedLattice (Type _) :=
  ⟨fun X => X.toLattice⟩

instance (X : BoundedLattice) : Lattice X :=
  X.toLattice.str

attribute [instance] BoundedLattice.isBoundedOrder

/-- Construct a bundled `BoundedLattice` from `lattice` + `bounded_order`. -/
def of (α : Type _) [Lattice α] [BoundedOrder α] : BoundedLattice :=
  ⟨⟨α⟩⟩

@[simp]
theorem coe_of (α : Type _) [Lattice α] [BoundedOrder α] : ↥(of α) = α :=
  rfl

instance : Inhabited BoundedLattice :=
  ⟨of PUnit⟩

instance : LargeCategory.{u} BoundedLattice where
  Hom := fun X Y => BoundedLatticeHom X Y
  id := fun X => BoundedLatticeHom.id X
  comp := fun X Y Z f g => g.comp f
  id_comp' := fun X Y => BoundedLatticeHom.comp_id
  comp_id' := fun X Y => BoundedLatticeHom.id_comp
  assoc' := fun W X Y Z _ _ _ => BoundedLatticeHom.comp_assoc _ _ _

instance : ConcreteCategory BoundedLattice where
  forget := ⟨coeSort, fun X Y => coeFn, fun X => rfl, fun X Y Z f g => rfl⟩
  forget_faithful :=
    ⟨fun X Y => by
      convert FunLike.coe_injective⟩

instance hasForgetToBoundedOrder :
    HasForget₂ BoundedLattice
      BoundedOrderCat where forget₂ :=
    { obj := fun X => BoundedOrderCat.of X, map := fun X Y => BoundedLatticeHom.toBoundedOrderHom }

instance hasForgetToLattice :
    HasForget₂ BoundedLattice
      Latticeₓ where forget₂ := { obj := fun X => ⟨X⟩, map := fun X Y => BoundedLatticeHom.toLatticeHom }

instance hasForgetToSemilatticeSup :
    HasForget₂ BoundedLattice
      SemilatticeSupCat where forget₂ := { obj := fun X => ⟨X⟩, map := fun X Y => BoundedLatticeHom.toSupBotHom }

instance hasForgetToSemilatticeInf :
    HasForget₂ BoundedLattice
      SemilatticeInfCat where forget₂ := { obj := fun X => ⟨X⟩, map := fun X Y => BoundedLatticeHom.toInfTopHom }

@[simp]
theorem coe_forget_to_BoundedOrder (X : BoundedLattice) : ↥((forget₂ BoundedLattice BoundedOrderCat).obj X) = ↥X :=
  rfl

@[simp]
theorem coe_forget_to_Lattice (X : BoundedLattice) : ↥((forget₂ BoundedLattice Latticeₓ).obj X) = ↥X :=
  rfl

@[simp]
theorem coe_forget_to_SemilatticeSup (X : BoundedLattice) : ↥((forget₂ BoundedLattice SemilatticeSupCat).obj X) = ↥X :=
  rfl

@[simp]
theorem coe_forget_to_SemilatticeInf (X : BoundedLattice) : ↥((forget₂ BoundedLattice SemilatticeInfCat).obj X) = ↥X :=
  rfl

theorem forget_Lattice_PartialOrder_eq_forget_BoundedOrder_PartialOrder :
    forget₂ BoundedLattice Latticeₓ ⋙ forget₂ Latticeₓ PartialOrderₓₓ =
      forget₂ BoundedLattice BoundedOrderCat ⋙ forget₂ BoundedOrderCat PartialOrderₓₓ :=
  rfl

theorem forget_SemilatticeSup_PartialOrder_eq_forget_BoundedOrder_PartialOrder :
    forget₂ BoundedLattice SemilatticeSupCat ⋙ forget₂ SemilatticeSupCat PartialOrderₓₓ =
      forget₂ BoundedLattice BoundedOrderCat ⋙ forget₂ BoundedOrderCat PartialOrderₓₓ :=
  rfl

theorem forget_SemilatticeInf_PartialOrder_eq_forget_BoundedOrder_PartialOrder :
    forget₂ BoundedLattice SemilatticeInfCat ⋙ forget₂ SemilatticeInfCat PartialOrderₓₓ =
      forget₂ BoundedLattice BoundedOrderCat ⋙ forget₂ BoundedOrderCat PartialOrderₓₓ :=
  rfl

/-- Constructs an equivalence between bounded lattices from an order isomorphism
between them. -/
@[simps]
def Iso.mk {α β : BoundedLattice.{u}} (e : α ≃o β) : α ≅ β where
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
def dual : BoundedLattice ⥤ BoundedLattice where
  obj := fun X => of Xᵒᵈ
  map := fun X Y => BoundedLatticeHom.dual

/-- The equivalence between `BoundedLattice` and itself induced by `order_dual` both ways. -/
@[simps Functor inverse]
def dualEquiv : BoundedLattice ≌ BoundedLattice :=
  Equivalence.mk dual dual ((NatIso.ofComponents fun X => iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)
    ((NatIso.ofComponents fun X => iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)

end BoundedLattice

theorem BoundedLattice_dual_comp_forget_to_BoundedOrder :
    BoundedLattice.dual ⋙ forget₂ BoundedLattice BoundedOrderCat =
      forget₂ BoundedLattice BoundedOrderCat ⋙ BoundedOrderCat.dual :=
  rfl

theorem BoundedLattice_dual_comp_forget_to_Lattice :
    BoundedLattice.dual ⋙ forget₂ BoundedLattice Latticeₓ = forget₂ BoundedLattice Latticeₓ ⋙ Latticeₓ.dual :=
  rfl

theorem BoundedLattice_dual_comp_forget_to_SemilatticeSup :
    BoundedLattice.dual ⋙ forget₂ BoundedLattice SemilatticeSupCat =
      forget₂ BoundedLattice SemilatticeInfCat ⋙ SemilatticeInfCat.dual :=
  rfl

theorem BoundedLattice_dual_comp_forget_to_SemilatticeInf :
    BoundedLattice.dual ⋙ forget₂ BoundedLattice SemilatticeInfCat =
      forget₂ BoundedLattice SemilatticeSupCat ⋙ SemilatticeSupCat.dual :=
  rfl

