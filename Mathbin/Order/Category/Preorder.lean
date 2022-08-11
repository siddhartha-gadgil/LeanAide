/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathbin.CategoryTheory.ConcreteCategory.BundledHom
import Mathbin.Algebra.PunitInstances
import Mathbin.Order.Hom.Basic
import Mathbin.CategoryTheory.Category.Cat
import Mathbin.CategoryTheory.Category.Preorder

/-!
# Category of preorders

This defines `Preorder`, the category of preorders with monotone maps.
-/


universe u

open CategoryTheory

/-- The category of preorders. -/
def Preorderₓₓ :=
  Bundled Preorderₓ

namespace Preorderₓₓ

instance : BundledHom @OrderHom where
  toFun := @OrderHom.toFun
  id := @OrderHom.id
  comp := @OrderHom.comp
  hom_ext := @OrderHom.ext

deriving instance LargeCategory, ConcreteCategory for Preorderₓₓ

instance : CoeSort Preorderₓₓ (Type _) :=
  bundled.has_coe_to_sort

/-- Construct a bundled Preorder from the underlying type and typeclass. -/
def of (α : Type _) [Preorderₓ α] : Preorderₓₓ :=
  Bundled.of α

@[simp]
theorem coe_of (α : Type _) [Preorderₓ α] : ↥(of α) = α :=
  rfl

instance : Inhabited Preorderₓₓ :=
  ⟨of PUnit⟩

instance (α : Preorderₓₓ) : Preorderₓ α :=
  α.str

/-- Constructs an equivalence between preorders from an order isomorphism between them. -/
@[simps]
def Iso.mk {α β : Preorderₓₓ.{u}} (e : α ≃o β) : α ≅ β where
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
def dual : Preorderₓₓ ⥤ Preorderₓₓ where
  obj := fun X => of Xᵒᵈ
  map := fun X Y => OrderHom.dual

/-- The equivalence between `Preorder` and itself induced by `order_dual` both ways. -/
@[simps Functor inverse]
def dualEquiv : Preorderₓₓ ≌ Preorderₓₓ :=
  Equivalence.mk dual dual ((NatIso.ofComponents fun X => iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)
    ((NatIso.ofComponents fun X => iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)

end Preorderₓₓ

/-- The embedding of `Preorder` into `Cat`.
-/
@[simps]
def preorderToCat : Preorderₓₓ.{u} ⥤ Cat where
  obj := fun X => Cat.of X.1
  map := fun X Y f => f.Monotone.Functor
  map_id' := fun X => by
    apply CategoryTheory.Functor.ext
    tidy
  map_comp' := fun X Y Z f g => by
    apply CategoryTheory.Functor.ext
    tidy

instance :
    Faithful preorderToCat.{u} where map_injective' := fun X Y f g h => by
    ext x
    exact functor.congr_obj h x

instance : Full preorderToCat.{u} where
  preimage := fun X Y f => ⟨f.obj, f.Monotone⟩
  witness' := fun X Y f => by
    apply CategoryTheory.Functor.ext
    tidy

