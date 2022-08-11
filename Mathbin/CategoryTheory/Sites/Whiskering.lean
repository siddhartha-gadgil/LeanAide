/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import Mathbin.CategoryTheory.Sites.Sheaf

/-!

In this file we construct the functor `Sheaf J A ⥤ Sheaf J B` between sheaf categories
obtained by composition with a functor `F : A ⥤ B`.

In order for the sheaf condition to be preserved, `F` must preserve the correct limits.
The lemma `presheaf.is_sheaf.comp` says that composition with such an `F` indeed preserves the
sheaf condition.

The functor between sheaf categories is called `Sheaf_compose J F`.
Given a natural transformation `η : F ⟶ G`, we obtain a natural transformation
`Sheaf_compose J F ⟶ Sheaf_compose J G`, which we call `Sheaf_compose_map J η`.

-/


namespace CategoryTheory

open CategoryTheory.Limits

universe v₁ v₂ u₁ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C]

variable {A : Type u₂} [Category.{max v₁ u₁} A]

variable {B : Type u₃} [Category.{max v₁ u₁} B]

variable {J : GrothendieckTopology C}

variable {U : C} (R : Presieve U)

variable (F : A ⥤ B)

namespace GrothendieckTopology.Cover

variable (P : Cᵒᵖ ⥤ A) {X : C} (S : J.cover X)

-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:51:50: missing argument
-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:51:50: missing argument
/-- The multicospan associated to a cover `S : J.cover X` and a presheaf of the form `P ⋙ F`
is isomorphic to the composition of the multicospan associated to `S` and `P`,
composed with `F`. -/
def multicospanComp : (S.index (P ⋙ F)).multicospan ≅ (S.index P).multicospan ⋙ F :=
  NatIso.ofComponents
    (fun t =>
      match t with
      | walking_multicospan.left a => eqToIso rfl
      | walking_multicospan.right b => eqToIso rfl)
    (by
      rintro (a | b) (a | b) (f | f | f)
      any_goals {
      }
      any_goals {
      })

@[simp]
theorem multicospan_comp_app_left (a) : (S.multicospanComp F P).app (WalkingMulticospan.left a) = eqToIso rfl :=
  rfl

@[simp]
theorem multicospan_comp_app_right (b) : (S.multicospanComp F P).app (WalkingMulticospan.right b) = eqToIso rfl :=
  rfl

@[simp]
theorem multicospan_comp_hom_app_left (a) : (S.multicospanComp F P).Hom.app (WalkingMulticospan.left a) = eqToHom rfl :=
  rfl

@[simp]
theorem multicospan_comp_hom_app_right (b) :
    (S.multicospanComp F P).Hom.app (WalkingMulticospan.right b) = eqToHom rfl :=
  rfl

@[simp]
theorem multicospan_comp_hom_inv_left (P : Cᵒᵖ ⥤ A) {X : C} (S : J.cover X) (a) :
    (S.multicospanComp F P).inv.app (WalkingMulticospan.left a) = eqToHom rfl :=
  rfl

@[simp]
theorem multicospan_comp_hom_inv_right (P : Cᵒᵖ ⥤ A) {X : C} (S : J.cover X) (b) :
    (S.multicospanComp F P).inv.app (WalkingMulticospan.right b) = eqToHom rfl :=
  rfl

/-- Mapping the multifork associated to a cover `S : J.cover X` and a presheaf `P` with
respect to a functor `F` is isomorphic (upto a natural isomorphism of the underlying functors)
to the multifork associated to `S` and `P ⋙ F`. -/
def mapMultifork :
    F.mapCone (S.Multifork P) ≅ (Limits.Cones.postcompose (S.multicospanComp F P).Hom).obj (S.Multifork (P ⋙ F)) :=
  Cones.ext (eqToIso rfl)
    (by
      rintro (a | b)
      · dsimp'
        simpa
        
      · dsimp'
        simp
        dsimp' [← multifork.of_ι]
        simpa
        )

end GrothendieckTopology.Cover

variable [∀ (X : C) (S : J.cover X) (P : Cᵒᵖ ⥤ A), PreservesLimit (S.index P).multicospan F]

theorem Presheaf.IsSheaf.comp {P : Cᵒᵖ ⥤ A} (hP : Presheaf.IsSheaf J P) : Presheaf.IsSheaf J (P ⋙ F) := by
  rw [presheaf.is_sheaf_iff_multifork] at hP⊢
  intro X S
  obtain ⟨h⟩ := hP X S
  replace h := is_limit_of_preserves F h
  replace h := limits.is_limit.of_iso_limit h (S.map_multifork F P)
  exact ⟨limits.is_limit.postcompose_hom_equiv (S.multicospan_comp F P) _ h⟩

variable (J)

/-- Composing a sheaf with a functor preserving the appropriate limits yields a functor
between sheaf categories. -/
@[simps]
def sheafCompose : Sheaf J A ⥤ Sheaf J B where
  obj := fun G => ⟨G.val ⋙ F, Presheaf.IsSheaf.comp _ G.2⟩
  map := fun G H η => ⟨whiskerRight η.val _⟩
  map_id' := fun G => Sheaf.Hom.ext _ _ <| whisker_right_id _
  map_comp' := fun G H W f g => Sheaf.Hom.ext _ _ <| whisker_right_comp _ _ _

end CategoryTheory

