/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathbin.CategoryTheory.Category.Bipointed
import Mathbin.Data.TwoPointing

/-!
# The category of two-pointed types

This defines `Twop`, the category of two-pointed types.

## References

* [nLab, *coalgebra of the real interval*]
  (https://ncatlab.org/nlab/show/coalgebra+of+the+real+interval)
-/


open CategoryTheory Option

universe u

variable {α β : Type _}

/-- The category of two-pointed types. -/
structure Twop : Type (u + 1) where
  X : Type u
  toTwoPointing : TwoPointing X

namespace Twop

instance : CoeSort Twop (Type _) :=
  ⟨X⟩

attribute [protected] Twop.X

/-- Turns a two-pointing into a two-pointed type. -/
def of {X : Type _} (to_two_pointing : TwoPointing X) : Twop :=
  ⟨X, to_two_pointing⟩

@[simp]
theorem coe_of {X : Type _} (to_two_pointing : TwoPointing X) : ↥(of to_two_pointing) = X :=
  rfl

alias of ← _root_.two_pointing.Twop

instance : Inhabited Twop :=
  ⟨of TwoPointing.bool⟩

/-- Turns a two-pointed type into a bipointed type, by forgetting that the pointed elements are
distinct. -/
def toBipointed (X : Twop) : Bipointed :=
  X.toTwoPointing.toProd.Bipointed

@[simp]
theorem coe_to_Bipointed (X : Twop) : ↥X.toBipointed = ↥X :=
  rfl

instance largeCategory : LargeCategory Twop :=
  InducedCategory.category toBipointed

instance concreteCategory : ConcreteCategory Twop :=
  InducedCategory.concreteCategory toBipointed

instance hasForgetToBipointed : HasForget₂ Twop Bipointed :=
  InducedCategory.hasForget₂ toBipointed

/-- Swaps the pointed elements of a two-pointed type. `two_pointing.swap` as a functor. -/
@[simps]
def swap : Twop ⥤ Twop where
  obj := fun X => ⟨X, X.toTwoPointing.swap⟩
  map := fun X Y f => ⟨f.toFun, f.map_snd, f.map_fst⟩

/-- The equivalence between `Twop` and itself induced by `prod.swap` both ways. -/
@[simps]
def swapEquiv : Twop ≌ Twop :=
  Equivalence.mk swap swap
    ((NatIso.ofComponents fun X => { Hom := ⟨id, rfl, rfl⟩, inv := ⟨id, rfl, rfl⟩ }) fun X Y f => rfl)
    ((NatIso.ofComponents fun X => { Hom := ⟨id, rfl, rfl⟩, inv := ⟨id, rfl, rfl⟩ }) fun X Y f => rfl)

@[simp]
theorem swap_equiv_symm : swapEquiv.symm = swap_equiv :=
  rfl

end Twop

@[simp]
theorem Twop_swap_comp_forget_to_Bipointed :
    Twop.swap ⋙ forget₂ Twop Bipointed = forget₂ Twop Bipointed ⋙ Bipointed.swap :=
  rfl

/-- The functor from `Pointed` to `Twop` which adds a second point. -/
@[simps]
def pointedToTwopFst : Pointed.{u} ⥤ Twop where
  obj := fun X => ⟨Option X, ⟨X.point, none⟩, some_ne_none _⟩
  map := fun X Y f => ⟨Option.map f.toFun, congr_arg _ f.map_point, rfl⟩
  map_id' := fun X => Bipointed.Hom.ext _ _ Option.map_id
  map_comp' := fun X Y Z f g => Bipointed.Hom.ext _ _ (Option.map_comp_mapₓ _ _).symm

/-- The functor from `Pointed` to `Twop` which adds a first point. -/
@[simps]
def pointedToTwopSnd : Pointed.{u} ⥤ Twop where
  obj := fun X => ⟨Option X, ⟨none, X.point⟩, (some_ne_none _).symm⟩
  map := fun X Y f => ⟨Option.map f.toFun, rfl, congr_arg _ f.map_point⟩
  map_id' := fun X => Bipointed.Hom.ext _ _ Option.map_id
  map_comp' := fun X Y Z f g => Bipointed.Hom.ext _ _ (Option.map_comp_mapₓ _ _).symm

@[simp]
theorem Pointed_to_Twop_fst_comp_swap : pointedToTwopFst ⋙ Twop.swap = pointedToTwopSnd :=
  rfl

@[simp]
theorem Pointed_to_Twop_snd_comp_swap : pointedToTwopSnd ⋙ Twop.swap = pointedToTwopFst :=
  rfl

@[simp]
theorem Pointed_to_Twop_fst_comp_forget_to_Bipointed :
    pointedToTwopFst ⋙ forget₂ Twop Bipointed = pointedToBipointedFst :=
  rfl

@[simp]
theorem Pointed_to_Twop_snd_comp_forget_to_Bipointed :
    pointedToTwopSnd ⋙ forget₂ Twop Bipointed = pointedToBipointedSnd :=
  rfl

/-- Adding a second point is left adjoint to forgetting the second point. -/
def pointedToTwopFstForgetCompBipointedToPointedFstAdjunction :
    pointedToTwopFst ⊣ forget₂ Twop Bipointed ⋙ bipointedToPointedFst :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y =>
        { toFun := fun f => ⟨f.toFun ∘ Option.some, f.map_fst⟩,
          invFun := fun f => ⟨fun o => o.elim Y.toTwoPointing.toProd.2 f.toFun, f.map_point, rfl⟩,
          left_inv := fun f => by
            ext
            cases x
            exact f.map_snd.symm
            rfl,
          right_inv := fun f => Pointed.Hom.ext _ _ rfl },
      hom_equiv_naturality_left_symm' := fun X' X Y f g => by
        ext
        cases x <;> rfl }

/-- Adding a first point is left adjoint to forgetting the first point. -/
def pointedToTwopSndForgetCompBipointedToPointedSndAdjunction :
    pointedToTwopSnd ⊣ forget₂ Twop Bipointed ⋙ bipointedToPointedSnd :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y =>
        { toFun := fun f => ⟨f.toFun ∘ Option.some, f.map_snd⟩,
          invFun := fun f => ⟨fun o => o.elim Y.toTwoPointing.toProd.1 f.toFun, rfl, f.map_point⟩,
          left_inv := fun f => by
            ext
            cases x
            exact f.map_fst.symm
            rfl,
          right_inv := fun f => Pointed.Hom.ext _ _ rfl },
      hom_equiv_naturality_left_symm' := fun X' X Y f g => by
        ext
        cases x <;> rfl }

