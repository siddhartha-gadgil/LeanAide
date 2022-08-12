/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathbin.Order.Category.Lattice

/-!
# Category of linear orders

This defines `LinearOrder`, the category of linear orders with monotone maps.
-/


open CategoryTheory

universe u

/-- The category of linear orders. -/
def LinearOrderₓₓ :=
  Bundled LinearOrderₓ

namespace LinearOrderₓₓ

instance : BundledHom.ParentProjection @LinearOrderₓ.toPartialOrder :=
  ⟨⟩

deriving instance LargeCategory, ConcreteCategory for LinearOrderₓₓ

instance : CoeSort LinearOrderₓₓ (Type _) :=
  bundled.has_coe_to_sort

/-- Construct a bundled `LinearOrder` from the underlying type and typeclass. -/
def of (α : Type _) [LinearOrderₓ α] : LinearOrderₓₓ :=
  Bundled.of α

@[simp]
theorem coe_of (α : Type _) [LinearOrderₓ α] : ↥(of α) = α :=
  rfl

instance : Inhabited LinearOrderₓₓ :=
  ⟨of PUnit⟩

instance (α : LinearOrderₓₓ) : LinearOrderₓ α :=
  α.str

instance hasForgetToLattice :
    HasForget₂ LinearOrderₓₓ
      Latticeₓ where forget₂ :=
    { obj := fun X => Latticeₓ.of X, map := fun X Y f => (OrderHomClass.toLatticeHom X Y f : LatticeHom X Y) }

/-- Constructs an equivalence between linear orders from an order isomorphism between them. -/
@[simps]
def Iso.mk {α β : LinearOrderₓₓ.{u}} (e : α ≃o β) : α ≅ β where
  Hom := e
  inv := e.symm
  hom_inv_id' := by
    ext
    exact e.symm_apply_apply x
  inv_hom_id' := by
    ext
    exact e.apply_symm_apply x

/-- `order_dual` as a functor. -/
@[simps]
def dual : LinearOrderₓₓ ⥤ LinearOrderₓₓ where
  obj := fun X => of Xᵒᵈ
  map := fun X Y => OrderHom.dual

/-- The equivalence between `LinearOrder` and itself induced by `order_dual` both ways. -/
@[simps Functor inverse]
def dualEquiv : LinearOrderₓₓ ≌ LinearOrderₓₓ :=
  Equivalence.mk dual dual ((NatIso.ofComponents fun X => iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)
    ((NatIso.ofComponents fun X => iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)

end LinearOrderₓₓ

theorem LinearOrder_dual_comp_forget_to_Lattice :
    LinearOrderₓₓ.dual ⋙ forget₂ LinearOrderₓₓ Latticeₓ = forget₂ LinearOrderₓₓ Latticeₓ ⋙ Latticeₓ.dual :=
  rfl

