/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Andrew Yang
-/
import Mathbin.CategoryTheory.Limits.Shapes.Terminal
import Mathbin.CategoryTheory.Limits.Shapes.Pullbacks
import Mathbin.CategoryTheory.Limits.Shapes.BinaryProducts

/-!
# Constructing binary product from pullbacks and terminal object.

The product is the pullback over the terminal objects. In particular, if a category
has pullbacks and a terminal object, then it has binary products.

We also provide the dual.
-/


universe v u

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]

/-- The pullback over the terminal object is the product -/
def isProductOfIsTerminalIsPullback {W X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) (h : W ⟶ X) (k : W ⟶ Y) (H₁ : IsTerminal Z)
    (H₂ : IsLimit (PullbackCone.mk _ _ (show h ≫ f = k ≫ g from H₁.hom_ext _ _))) : IsLimit (BinaryFan.mk h k) where
  lift := fun c => H₂.lift (PullbackCone.mk (c.π.app ⟨WalkingPair.left⟩) (c.π.app ⟨WalkingPair.right⟩) (H₁.hom_ext _ _))
  fac' := fun c j => by
    cases j
    convert
      H₂.fac (pullback_cone.mk (c.π.app ⟨walking_pair.left⟩) (c.π.app ⟨walking_pair.right⟩) (H₁.hom_ext _ _))
        (some j) using
      1
    rcases j with ⟨⟩ <;> rfl
  uniq' := fun c m hm => by
    apply pullback_cone.is_limit.hom_ext H₂
    · exact
        (hm ⟨walking_pair.left⟩).trans
          (H₂.fac (pullback_cone.mk (c.π.app ⟨walking_pair.left⟩) (c.π.app ⟨walking_pair.right⟩) (H₁.hom_ext _ _))
              walking_cospan.left).symm
      
    · exact
        (hm ⟨walking_pair.right⟩).trans
          (H₂.fac (pullback_cone.mk (c.π.app ⟨walking_pair.left⟩) (c.π.app ⟨walking_pair.right⟩) (H₁.hom_ext _ _))
              walking_cospan.right).symm
      

/-- The product is the pullback over the terminal object. -/
def isPullbackOfIsTerminalIsProduct {W X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) (h : W ⟶ X) (k : W ⟶ Y) (H₁ : IsTerminal Z)
    (H₂ : IsLimit (BinaryFan.mk h k)) : IsLimit (PullbackCone.mk _ _ (show h ≫ f = k ≫ g from H₁.hom_ext _ _)) := by
  apply pullback_cone.is_limit_aux'
  intro s
  use H₂.lift (binary_fan.mk s.fst s.snd)
  use H₂.fac (binary_fan.mk s.fst s.snd) ⟨walking_pair.left⟩
  use H₂.fac (binary_fan.mk s.fst s.snd) ⟨walking_pair.right⟩
  intro m h₁ h₂
  apply H₂.hom_ext
  rintro ⟨⟨⟩⟩
  · exact h₁.trans (H₂.fac (binary_fan.mk s.fst s.snd) ⟨walking_pair.left⟩).symm
    
  · exact h₂.trans (H₂.fac (binary_fan.mk s.fst s.snd) ⟨walking_pair.right⟩).symm
    

/-- Any category with pullbacks and a terminal object has a limit cone for each walking pair. -/
noncomputable def limitConeOfTerminalAndPullbacks [HasTerminal C] [HasPullbacks C] (F : Discrete WalkingPair ⥤ C) :
    LimitCone F where
  Cone :=
    { x := pullback (terminal.from (F.obj ⟨WalkingPair.left⟩)) (terminal.from (F.obj ⟨WalkingPair.right⟩)),
      π := Discrete.natTrans fun x => Discrete.casesOn x fun x => WalkingPair.casesOn x pullback.fst pullback.snd }
  IsLimit :=
    { lift := fun c =>
        pullback.lift (c.π.app ⟨WalkingPair.left⟩) (c.π.app ⟨WalkingPair.right⟩) (Subsingleton.elimₓ _ _),
      fac' := fun s c => Discrete.casesOn c fun c => WalkingPair.casesOn c (limit.lift_π _ _) (limit.lift_π _ _),
      uniq' := fun s m J => by
        rw [← J, ← J]
        ext <;> rw [limit.lift_π] <;> rfl }

variable (C)

/-- Any category with pullbacks and terminal object has binary products. -/
-- This is not an instance, as it is not always how one wants to construct binary products!
theorem has_binary_products_of_terminal_and_pullbacks [HasTerminal C] [HasPullbacks C] : HasBinaryProducts C :=
  { HasLimit := fun F => HasLimit.mk (limitConeOfTerminalAndPullbacks F) }

/-- In a category with a terminal object and pullbacks,
a product of objects `X` and `Y` is isomorphic to a pullback. -/
noncomputable def prodIsoPullback [HasTerminal C] [HasPullbacks C] (X Y : C) [HasBinaryProduct X Y] :
    X ⨯ Y ≅ pullback (terminal.from X) (terminal.from Y) :=
  limit.isoLimitCone (limitConeOfTerminalAndPullbacks _)

variable {C}

/-- The pushout under the initial object is the coproduct -/
def isCoproductOfIsInitialIsPushout {W X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) (h : W ⟶ X) (k : W ⟶ Y) (H₁ : IsInitial W)
    (H₂ : IsColimit (PushoutCocone.mk _ _ (show h ≫ f = k ≫ g from H₁.hom_ext _ _))) :
    IsColimit (BinaryCofan.mk f g) where
  desc := fun c =>
    H₂.desc (PushoutCocone.mk (c.ι.app ⟨WalkingPair.left⟩) (c.ι.app ⟨WalkingPair.right⟩) (H₁.hom_ext _ _))
  fac' := fun c j => by
    cases j
    convert
      H₂.fac (pushout_cocone.mk (c.ι.app ⟨walking_pair.left⟩) (c.ι.app ⟨walking_pair.right⟩) (H₁.hom_ext _ _))
        (some j) using
      1
    cases j <;> rfl
  uniq' := fun c m hm => by
    apply pushout_cocone.is_colimit.hom_ext H₂
    · exact
        (hm ⟨walking_pair.left⟩).trans
          (H₂.fac (pushout_cocone.mk (c.ι.app ⟨walking_pair.left⟩) (c.ι.app ⟨walking_pair.right⟩) (H₁.hom_ext _ _))
              walking_cospan.left).symm
      
    · exact
        (hm ⟨walking_pair.right⟩).trans
          (H₂.fac (pushout_cocone.mk (c.ι.app ⟨walking_pair.left⟩) (c.ι.app ⟨walking_pair.right⟩) (H₁.hom_ext _ _))
              walking_cospan.right).symm
      

/-- The coproduct is the pushout under the initial object. -/
def isPushoutOfIsInitialIsCoproduct {W X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) (h : W ⟶ X) (k : W ⟶ Y) (H₁ : IsInitial W)
    (H₂ : IsColimit (BinaryCofan.mk f g)) : IsColimit (PushoutCocone.mk _ _ (show h ≫ f = k ≫ g from H₁.hom_ext _ _)) :=
  by
  apply pushout_cocone.is_colimit_aux'
  intro s
  use H₂.desc (binary_cofan.mk s.inl s.inr)
  use H₂.fac (binary_cofan.mk s.inl s.inr) ⟨walking_pair.left⟩
  use H₂.fac (binary_cofan.mk s.inl s.inr) ⟨walking_pair.right⟩
  intro m h₁ h₂
  apply H₂.hom_ext
  rintro ⟨⟨⟩⟩
  · exact h₁.trans (H₂.fac (binary_cofan.mk s.inl s.inr) ⟨walking_pair.left⟩).symm
    
  · exact h₂.trans (H₂.fac (binary_cofan.mk s.inl s.inr) ⟨walking_pair.right⟩).symm
    

/-- Any category with pushouts and an initial object has a colimit cocone for each walking pair. -/
noncomputable def colimitCoconeOfInitialAndPushouts [HasInitial C] [HasPushouts C] (F : Discrete WalkingPair ⥤ C) :
    ColimitCocone F where
  Cocone :=
    { x := pushout (initial.to (F.obj ⟨WalkingPair.left⟩)) (initial.to (F.obj ⟨WalkingPair.right⟩)),
      ι := Discrete.natTrans fun x => Discrete.casesOn x fun x => WalkingPair.casesOn x pushout.inl pushout.inr }
  IsColimit :=
    { desc := fun c => pushout.desc (c.ι.app ⟨WalkingPair.left⟩) (c.ι.app ⟨WalkingPair.right⟩) (Subsingleton.elimₓ _ _),
      fac' := fun s c => Discrete.casesOn c fun c => WalkingPair.casesOn c (colimit.ι_desc _ _) (colimit.ι_desc _ _),
      uniq' := fun s m J => by
        rw [← J, ← J]
        ext <;> rw [colimit.ι_desc] <;> rfl }

variable (C)

/-- Any category with pushouts and initial object has binary coproducts. -/
-- This is not an instance, as it is not always how one wants to construct binary coproducts!
theorem has_binary_coproducts_of_initial_and_pushouts [HasInitial C] [HasPushouts C] : HasBinaryCoproducts C :=
  { HasColimit := fun F => HasColimit.mk (colimitCoconeOfInitialAndPushouts F) }

/-- In a category with an initial object and pushouts,
a coproduct of objects `X` and `Y` is isomorphic to a pushout. -/
noncomputable def coprodIsoPushout [HasInitial C] [HasPushouts C] (X Y : C) [HasBinaryCoproduct X Y] :
    X ⨿ Y ≅ pushout (initial.to X) (initial.to Y) :=
  colimit.isoColimitCocone (colimitCoconeOfInitialAndPushouts _)

