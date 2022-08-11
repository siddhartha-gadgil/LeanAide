/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathbin.Order.Category.PartialOrder
import Mathbin.Order.Hom.Lattice

/-!
# The categories of semilattices

This defines `SemilatticeSup` and `SemilatticeInf`, the categories of sup-semilattices with a bottom
element and inf-semilattices with a top element.

## References

* [nLab, *semilattice*](https://ncatlab.org/nlab/show/semilattice)
-/


universe u

open CategoryTheory

/-- The category of sup-semilattices with a bottom element. -/
structure SemilatticeSupCat : Type (u + 1) where
  X : Type u
  [isSemilatticeSup : SemilatticeSup X]
  [isOrderBot : OrderBot X]

/-- The category of inf-semilattices with a top element. -/
structure SemilatticeInfCat : Type (u + 1) where
  X : Type u
  [isSemilatticeInf : SemilatticeInf X]
  [isOrderTop : OrderTop X]

attribute [protected] SemilatticeSupCat.X SemilatticeInfCat.X

namespace SemilatticeSupCat

instance : CoeSort SemilatticeSupCat (Type _) :=
  ⟨SemilatticeSupCat.X⟩

attribute [instance] is_semilattice_sup is_order_bot

/-- Construct a bundled `SemilatticeSup` from a `semilattice_sup`. -/
def of (α : Type _) [SemilatticeSup α] [OrderBot α] : SemilatticeSupCat :=
  ⟨α⟩

@[simp]
theorem coe_of (α : Type _) [SemilatticeSup α] [OrderBot α] : ↥(of α) = α :=
  rfl

instance : Inhabited SemilatticeSupCat :=
  ⟨of PUnit⟩

instance : LargeCategory.{u} SemilatticeSupCat where
  Hom := fun X Y => SupBotHom X Y
  id := fun X => SupBotHom.id X
  comp := fun X Y Z f g => g.comp f
  id_comp' := fun X Y => SupBotHom.comp_id
  comp_id' := fun X Y => SupBotHom.id_comp
  assoc' := fun W X Y Z _ _ _ => SupBotHom.comp_assoc _ _ _

instance : ConcreteCategory SemilatticeSupCat where
  forget := { obj := SemilatticeSupCat.X, map := fun X Y => coeFn }
  forget_faithful := ⟨fun X Y => FunLike.coe_injective⟩

instance hasForgetToPartialOrder :
    HasForget₂ SemilatticeSupCat PartialOrderₓₓ where forget₂ := { obj := fun X => ⟨X⟩, map := fun X Y f => f }

@[simp]
theorem coe_forget_to_PartialOrder (X : SemilatticeSupCat) : ↥((forget₂ SemilatticeSupCat PartialOrderₓₓ).obj X) = ↥X :=
  rfl

end SemilatticeSupCat

namespace SemilatticeInfCat

instance : CoeSort SemilatticeInfCat (Type _) :=
  ⟨SemilatticeInfCat.X⟩

attribute [instance] is_semilattice_inf is_order_top

/-- Construct a bundled `SemilatticeInf` from a `semilattice_inf`. -/
def of (α : Type _) [SemilatticeInf α] [OrderTop α] : SemilatticeInfCat :=
  ⟨α⟩

@[simp]
theorem coe_of (α : Type _) [SemilatticeInf α] [OrderTop α] : ↥(of α) = α :=
  rfl

instance : Inhabited SemilatticeInfCat :=
  ⟨of PUnit⟩

instance : LargeCategory.{u} SemilatticeInfCat where
  Hom := fun X Y => InfTopHom X Y
  id := fun X => InfTopHom.id X
  comp := fun X Y Z f g => g.comp f
  id_comp' := fun X Y => InfTopHom.comp_id
  comp_id' := fun X Y => InfTopHom.id_comp
  assoc' := fun W X Y Z _ _ _ => InfTopHom.comp_assoc _ _ _

instance : ConcreteCategory SemilatticeInfCat where
  forget := { obj := SemilatticeInfCat.X, map := fun X Y => coeFn }
  forget_faithful := ⟨fun X Y => FunLike.coe_injective⟩

instance hasForgetToPartialOrder :
    HasForget₂ SemilatticeInfCat PartialOrderₓₓ where forget₂ := { obj := fun X => ⟨X⟩, map := fun X Y f => f }

@[simp]
theorem coe_forget_to_PartialOrder (X : SemilatticeInfCat) : ↥((forget₂ SemilatticeInfCat PartialOrderₓₓ).obj X) = ↥X :=
  rfl

end SemilatticeInfCat

/-! ### Order dual -/


namespace SemilatticeSupCat

/-- Constructs an isomorphism of lattices from an order isomorphism between them. -/
@[simps]
def Iso.mk {α β : SemilatticeSupCat.{u}} (e : α ≃o β) : α ≅ β where
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
def dual : SemilatticeSupCat ⥤ SemilatticeInfCat where
  obj := fun X => SemilatticeInfCat.of Xᵒᵈ
  map := fun X Y => SupBotHom.dual

end SemilatticeSupCat

namespace SemilatticeInfCat

/-- Constructs an isomorphism of lattices from an order isomorphism between them. -/
@[simps]
def Iso.mk {α β : SemilatticeInfCat.{u}} (e : α ≃o β) : α ≅ β where
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
def dual : SemilatticeInfCat ⥤ SemilatticeSupCat where
  obj := fun X => SemilatticeSupCat.of Xᵒᵈ
  map := fun X Y => InfTopHom.dual

end SemilatticeInfCat

/-- The equivalence between `SemilatticeSup` and `SemilatticeInf` induced by `order_dual` both ways.
-/
@[simps Functor inverse]
def semilatticeSupEquivSemilatticeInf : SemilatticeSupCat ≌ SemilatticeInfCat :=
  Equivalence.mk SemilatticeSupCat.dual SemilatticeInfCat.dual
    ((NatIso.ofComponents fun X => SemilatticeSupCat.Iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)
    ((NatIso.ofComponents fun X => SemilatticeInfCat.Iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)

theorem SemilatticeSup_dual_comp_forget_to_PartialOrder :
    SemilatticeSupCat.dual ⋙ forget₂ SemilatticeInfCat PartialOrderₓₓ =
      forget₂ SemilatticeSupCat PartialOrderₓₓ ⋙ PartialOrderₓₓ.dual :=
  rfl

theorem SemilatticeInf_dual_comp_forget_to_PartialOrder :
    SemilatticeInfCat.dual ⋙ forget₂ SemilatticeSupCat PartialOrderₓₓ =
      forget₂ SemilatticeInfCat PartialOrderₓₓ ⋙ PartialOrderₓₓ.dual :=
  rfl

