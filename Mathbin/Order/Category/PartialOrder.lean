/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathbin.Order.Antisymmetrization
import Mathbin.Order.Category.Preorder

/-!
# Category of partial orders

This defines `PartialOrder`, the category of partial orders with monotone maps.
-/


open CategoryTheory

universe u

/-- The category of partially ordered types. -/
def PartialOrderₓₓ :=
  Bundled PartialOrderₓ

namespace PartialOrderₓₓ

instance : BundledHom.ParentProjection @PartialOrderₓ.toPreorder :=
  ⟨⟩

deriving instance LargeCategory, ConcreteCategory for PartialOrderₓₓ

instance : CoeSort PartialOrderₓₓ (Type _) :=
  bundled.has_coe_to_sort

/-- Construct a bundled PartialOrder from the underlying type and typeclass. -/
def of (α : Type _) [PartialOrderₓ α] : PartialOrderₓₓ :=
  Bundled.of α

@[simp]
theorem coe_of (α : Type _) [PartialOrderₓ α] : ↥(of α) = α :=
  rfl

instance : Inhabited PartialOrderₓₓ :=
  ⟨of PUnit⟩

instance (α : PartialOrderₓₓ) : PartialOrderₓ α :=
  α.str

instance hasForgetToPreorder : HasForget₂ PartialOrderₓₓ Preorderₓₓ :=
  BundledHom.forget₂ _ _

/-- Constructs an equivalence between partial orders from an order isomorphism between them. -/
@[simps]
def Iso.mk {α β : PartialOrderₓₓ.{u}} (e : α ≃o β) : α ≅ β where
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
def dual : PartialOrderₓₓ ⥤ PartialOrderₓₓ where
  obj := fun X => of Xᵒᵈ
  map := fun X Y => OrderHom.dual

/-- The equivalence between `PartialOrder` and itself induced by `order_dual` both ways. -/
@[simps Functor inverse]
def dualEquiv : PartialOrderₓₓ ≌ PartialOrderₓₓ :=
  Equivalence.mk dual dual ((NatIso.ofComponents fun X => iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)
    ((NatIso.ofComponents fun X => iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)

end PartialOrderₓₓ

theorem PartialOrder_dual_comp_forget_to_Preorder :
    PartialOrderₓₓ.dual ⋙ forget₂ PartialOrderₓₓ Preorderₓₓ = forget₂ PartialOrderₓₓ Preorderₓₓ ⋙ Preorderₓₓ.dual :=
  rfl

/-- `antisymmetrization` as a functor. It is the free functor. -/
def preorderToPartialOrder : Preorderₓₓ.{u} ⥤ PartialOrderₓₓ where
  obj := fun X => PartialOrderₓₓ.of (Antisymmetrization X (· ≤ ·))
  map := fun X Y f => f.Antisymmetrization
  map_id' := fun X => by
    ext
    exact Quotientₓ.induction_on' x fun x => Quotientₓ.map'_mk' _ (fun a b => id) _
  map_comp' := fun X Y Z f g => by
    ext
    exact Quotientₓ.induction_on' x fun x => OrderHom.antisymmetrization_apply_mk _ _

/-- `Preorder_to_PartialOrder` is left adjoint to the forgetful functor, meaning it is the free
functor from `Preorder` to `PartialOrder`. -/
def preorderToPartialOrderForgetAdjunction : preorderToPartialOrder.{u} ⊣ forget₂ PartialOrderₓₓ Preorderₓₓ :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y =>
        { toFun := fun f => ⟨f ∘ toAntisymmetrization (· ≤ ·), f.mono.comp to_antisymmetrization_mono⟩,
          invFun := fun f =>
            ⟨fun a => (Quotientₓ.liftOn' a f) fun a b h => (AntisymmRel.image h f.mono).Eq, fun a b =>
              (Quotientₓ.induction_on₂' a b) fun a b h => f.mono h⟩,
          left_inv := fun f => OrderHom.ext _ _ <| funext fun x => (Quotientₓ.induction_on' x) fun x => rfl,
          right_inv := fun f => OrderHom.ext _ _ <| funext fun x => rfl },
      hom_equiv_naturality_left_symm' := fun X Y Z f g =>
        OrderHom.ext _ _ <| funext fun x => (Quotientₓ.induction_on' x) fun x => rfl,
      hom_equiv_naturality_right' := fun X Y Z f g => OrderHom.ext _ _ <| funext fun x => rfl }

/-- `Preorder_to_PartialOrder` and `order_dual` commute. -/
@[simps]
def preorderToPartialOrderCompToDualIsoToDualCompPreorderToPartialOrder :
    preorderToPartialOrder.{u} ⋙ PartialOrderₓₓ.dual ≅ Preorderₓₓ.dual ⋙ preorderToPartialOrder :=
  (NatIso.ofComponents fun X => PartialOrderₓₓ.Iso.mk <| OrderIso.dualAntisymmetrization _) fun X Y f =>
    OrderHom.ext _ _ <| funext fun x => (Quotientₓ.induction_on' x) fun x => rfl

