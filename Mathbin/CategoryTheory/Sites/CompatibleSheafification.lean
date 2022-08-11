/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import Mathbin.CategoryTheory.Sites.CompatiblePlus

/-!

In this file, we prove that sheafification is compatible with functors which
preserve the correct limits and colimits.

-/


namespace CategoryTheory.GrothendieckTopology

open CategoryTheory

open CategoryTheory.Limits

open Opposite

universe w₁ w₂ v u

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

variable {D : Type w₁} [Category.{max v u} D]

variable {E : Type w₂} [Category.{max v u} E]

variable (F : D ⥤ E)

noncomputable section

variable [∀ (α β : Type max v u) (fst snd : β → α), HasLimitsOfShape (WalkingMulticospan fst snd) D]

variable [∀ (α β : Type max v u) (fst snd : β → α), HasLimitsOfShape (WalkingMulticospan fst snd) E]

variable [∀ X : C, HasColimitsOfShape (J.cover X)ᵒᵖ D]

variable [∀ X : C, HasColimitsOfShape (J.cover X)ᵒᵖ E]

variable [∀ X : C, PreservesColimitsOfShape (J.cover X)ᵒᵖ F]

variable [∀ (X : C) (W : J.cover X) (P : Cᵒᵖ ⥤ D), PreservesLimit (W.index P).multicospan F]

variable (P : Cᵒᵖ ⥤ D)

/-- The isomorphism between the sheafification of `P` composed with `F` and
the sheafification of `P ⋙ F`.

Use the lemmas `whisker_right_to_sheafify_sheafify_comp_iso_hom`,
`to_sheafify_comp_sheafify_comp_iso_inv` and `sheafify_comp_iso_inv_eq_sheafify_lift` to reduce
the components of this isomorphisms to a state that can be handled using the universal property
of sheafification. -/
def sheafifyCompIso : J.sheafify P ⋙ F ≅ J.sheafify (P ⋙ F) :=
  J.plusCompIso _ _ ≪≫ (J.plusFunctor _).mapIso (J.plusCompIso _ _)

/-- The isomorphism between the sheafification of `P` composed with `F` and
the sheafification of `P ⋙ F`, functorially in `F`. -/
def sheafificationWhiskerLeftIso (P : Cᵒᵖ ⥤ D) [∀ (F : D ⥤ E) (X : C), PreservesColimitsOfShape (J.cover X)ᵒᵖ F]
    [∀ (F : D ⥤ E) (X : C) (W : J.cover X) (P : Cᵒᵖ ⥤ D), PreservesLimit (W.index P).multicospan F] :
    (whiskeringLeft _ _ E).obj (J.sheafify P) ≅ (whiskeringLeft _ _ _).obj P ⋙ J.sheafification E := by
  refine' J.plus_functor_whisker_left_iso _ ≪≫ _ ≪≫ functor.associator _ _ _
  refine' iso_whisker_right _ _
  refine' J.plus_functor_whisker_left_iso _

@[simp]
theorem sheafification_whisker_left_iso_hom_app (P : Cᵒᵖ ⥤ D) (F : D ⥤ E)
    [∀ (F : D ⥤ E) (X : C), PreservesColimitsOfShape (J.cover X)ᵒᵖ F]
    [∀ (F : D ⥤ E) (X : C) (W : J.cover X) (P : Cᵒᵖ ⥤ D), PreservesLimit (W.index P).multicospan F] :
    (sheafificationWhiskerLeftIso J P).Hom.app F = (J.sheafifyCompIso F P).Hom := by
  dsimp' [← sheafification_whisker_left_iso, ← sheafify_comp_iso]
  rw [category.comp_id]

@[simp]
theorem sheafification_whisker_left_iso_inv_app (P : Cᵒᵖ ⥤ D) (F : D ⥤ E)
    [∀ (F : D ⥤ E) (X : C), PreservesColimitsOfShape (J.cover X)ᵒᵖ F]
    [∀ (F : D ⥤ E) (X : C) (W : J.cover X) (P : Cᵒᵖ ⥤ D), PreservesLimit (W.index P).multicospan F] :
    (sheafificationWhiskerLeftIso J P).inv.app F = (J.sheafifyCompIso F P).inv := by
  dsimp' [← sheafification_whisker_left_iso, ← sheafify_comp_iso]
  erw [category.id_comp]

/-- The isomorphism between the sheafification of `P` composed with `F` and
the sheafification of `P ⋙ F`, functorially in `P`. -/
def sheafificationWhiskerRightIso :
    J.sheafification D ⋙ (whiskeringRight _ _ _).obj F ≅ (whiskeringRight _ _ _).obj F ⋙ J.sheafification E := by
  refine' functor.associator _ _ _ ≪≫ _
  refine' iso_whisker_left (J.plus_functor D) (J.plus_functor_whisker_right_iso _) ≪≫ _
  refine' _ ≪≫ functor.associator _ _ _
  refine' (functor.associator _ _ _).symm ≪≫ _
  exact iso_whisker_right (J.plus_functor_whisker_right_iso _) (J.plus_functor E)

@[simp]
theorem sheafification_whisker_right_iso_hom_app :
    (J.sheafificationWhiskerRightIso F).Hom.app P = (J.sheafifyCompIso F P).Hom := by
  dsimp' [← sheafification_whisker_right_iso, ← sheafify_comp_iso]
  simp only [← category.id_comp, ← category.comp_id]
  erw [category.id_comp]

@[simp]
theorem sheafification_whisker_right_iso_inv_app :
    (J.sheafificationWhiskerRightIso F).inv.app P = (J.sheafifyCompIso F P).inv := by
  dsimp' [← sheafification_whisker_right_iso, ← sheafify_comp_iso]
  simp only [← category.id_comp, ← category.comp_id]
  erw [category.id_comp]

@[simp, reassoc]
theorem whisker_right_to_sheafify_sheafify_comp_iso_hom :
    whiskerRight (J.toSheafify _) _ ≫ (J.sheafifyCompIso F P).Hom = J.toSheafify _ := by
  dsimp' [← sheafify_comp_iso]
  erw [whisker_right_comp, category.assoc]
  slice_lhs 2 3 => rw [plus_comp_iso_whisker_right]
  rw [category.assoc, ← J.plus_map_comp, whisker_right_to_plus_comp_plus_comp_iso_hom, ← category.assoc,
    whisker_right_to_plus_comp_plus_comp_iso_hom]
  rfl

@[simp, reassoc]
theorem to_sheafify_comp_sheafify_comp_iso_inv :
    J.toSheafify _ ≫ (J.sheafifyCompIso F P).inv = whiskerRight (J.toSheafify _) _ := by
  rw [iso.comp_inv_eq]
  simp

section

-- We will sheafify `D`-valued presheaves in this section.
variable [ConcreteCategory.{max v u} D] [PreservesLimits (forget D)]
  [∀ X : C, PreservesColimitsOfShape (J.cover X)ᵒᵖ (forget D)] [ReflectsIsomorphisms (forget D)]

@[simp]
theorem sheafify_comp_iso_inv_eq_sheafify_lift :
    (J.sheafifyCompIso F P).inv = J.sheafifyLift (whiskerRight (J.toSheafify _) _) ((J.sheafify_is_sheaf _).comp _) :=
  by
  apply J.sheafify_lift_unique
  rw [iso.comp_inv_eq]
  simp

end

end CategoryTheory.GrothendieckTopology

