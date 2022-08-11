/-
Copyright (c) 2018 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Reid Barton, Bhavik Mehta
-/
import Mathbin.CategoryTheory.Over
import Mathbin.CategoryTheory.Adjunction.Opposites
import Mathbin.CategoryTheory.Limits.Preserves.Basic
import Mathbin.CategoryTheory.Limits.Shapes.Pullbacks
import Mathbin.CategoryTheory.Limits.Creates
import Mathbin.CategoryTheory.Limits.Comma

/-!
# Limits and colimits in the over and under categories

Show that the forgetful functor `forget X : over X ⥤ C` creates colimits, and hence `over X` has
any colimits that `C` has (as well as the dual that `forget X : under X ⟶ C` creates limits).

Note that the folder `category_theory.limits.shapes.constructions.over` further shows that
`forget X : over X ⥤ C` creates connected limits (so `over X` has connected limits), and that
`over X` has `J`-indexed products if `C` has `J`-indexed wide pullbacks.

TODO: If `C` has binary products, then `forget X : over X ⥤ C` has a right adjoint.
-/


noncomputable section

universe v u

-- morphism levels before object levels. See note [category_theory universes].
open CategoryTheory CategoryTheory.Limits

variable {J : Type v} [SmallCategory J]

variable {C : Type u} [Category.{v} C]

variable {X : C}

namespace CategoryTheory.Over

instance has_colimit_of_has_colimit_comp_forget (F : J ⥤ Over X) [i : HasColimit (F ⋙ forget X)] : HasColimit F :=
  @CostructuredArrow.has_colimit _ _ _ _ i _

instance [HasColimitsOfShape J C] : HasColimitsOfShape J (Over X) where

instance [HasColimits C] : HasColimits (Over X) :=
  ⟨inferInstance⟩

instance createsColimits : CreatesColimits (forget X) :=
  costructured_arrow.creates_colimits

-- We can automatically infer that the forgetful functor preserves and reflects colimits.
example [HasColimits C] : PreservesColimits (forget X) :=
  inferInstance

example : ReflectsColimits (forget X) :=
  inferInstance

section

variable [HasPullbacks C]

open Tactic

/-- When `C` has pullbacks, a morphism `f : X ⟶ Y` induces a functor `over Y ⥤ over X`,
by pulling back a morphism along `f`. -/
@[simps]
def pullback {X Y : C} (f : X ⟶ Y) : Over Y ⥤ Over X where
  obj := fun g => Over.mk (pullback.snd : pullback g.Hom f ⟶ X)
  map := fun g h k =>
    Over.homMk
      (pullback.lift (pullback.fst ≫ k.left) pullback.snd
        (by
          simp [← pullback.condition]))
      (by
        tidy)

/-- `over.map f` is left adjoint to `over.pullback f`. -/
def mapPullbackAdj {A B : C} (f : A ⟶ B) : Over.map f ⊣ pullback f :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun g h =>
        { toFun := fun X => Over.homMk (pullback.lift X.left g.Hom (Over.w X)) (pullback.lift_snd _ _ _),
          invFun := fun Y => by
            refine' over.hom_mk _ _
            refine' Y.left ≫ pullback.fst
            dsimp'
            rw [← over.w Y, category.assoc, pullback.condition, category.assoc]
            rfl,
          left_inv := fun X => by
            ext
            dsimp'
            simp ,
          right_inv := fun Y => by
            ext
            dsimp'
            simp only [← pullback.lift_fst]
            dsimp'
            rw [pullback.lift_snd, ← over.w Y]
            rfl } }

/-- pullback (𝟙 A) : over A ⥤ over A is the identity functor. -/
def pullbackId {A : C} : pullback (𝟙 A) ≅ 𝟭 _ :=
  Adjunction.rightAdjointUniq (mapPullbackAdj _) (Adjunction.id.ofNatIsoLeft Over.mapId.symm)

/-- pullback commutes with composition (up to natural isomorphism). -/
def pullbackComp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : pullback (f ≫ g) ≅ pullback g ⋙ pullback f :=
  Adjunction.rightAdjointUniq (mapPullbackAdj _)
    (((mapPullbackAdj _).comp (mapPullbackAdj _)).ofNatIsoLeft (Over.mapComp _ _).symm)

instance pullbackIsRightAdjoint {A B : C} (f : A ⟶ B) : IsRightAdjoint (pullback f) :=
  ⟨_, mapPullbackAdj f⟩

end

end CategoryTheory.Over

namespace CategoryTheory.Under

instance has_limit_of_has_limit_comp_forget (F : J ⥤ Under X) [i : HasLimit (F ⋙ forget X)] : HasLimit F :=
  @StructuredArrow.has_limit _ _ _ _ i _

instance [HasLimitsOfShape J C] : HasLimitsOfShape J (Under X) where

instance [HasLimits C] : HasLimits (Under X) :=
  ⟨inferInstance⟩

instance createsLimits : CreatesLimits (forget X) :=
  structured_arrow.creates_limits

-- We can automatically infer that the forgetful functor preserves and reflects limits.
example [HasLimits C] : PreservesLimits (forget X) :=
  inferInstance

example : ReflectsLimits (forget X) :=
  inferInstance

section

variable [HasPushouts C]

/-- When `C` has pushouts, a morphism `f : X ⟶ Y` induces a functor `under X ⥤ under Y`,
by pushing a morphism forward along `f`. -/
@[simps]
def pushout {X Y : C} (f : X ⟶ Y) : Under X ⥤ Under Y where
  obj := fun g => Under.mk (pushout.inr : Y ⟶ pushout g.Hom f)
  map := fun g h k =>
    Under.homMk
      (pushout.desc (k.right ≫ pushout.inl) pushout.inr
        (by
          simp [pushout.condition]))
      (by
        tidy)

end

end CategoryTheory.Under

