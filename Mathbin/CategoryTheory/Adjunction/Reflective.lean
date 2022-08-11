/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathbin.CategoryTheory.Adjunction.FullyFaithful
import Mathbin.CategoryTheory.Functor.ReflectsIsomorphisms
import Mathbin.CategoryTheory.EpiMono

/-!
# Reflective functors

Basic properties of reflective functors, especially those relating to their essential image.

Note properties of reflective functors relating to limits and colimits are included in
`category_theory.monad.limits`.
-/


universe v₁ v₂ v₃ u₁ u₂ u₃

noncomputable section

namespace CategoryTheory

open Category Adjunction

variable {C : Type u₁} {D : Type u₂} {E : Type u₃}

variable [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E]

/-- A functor is *reflective*, or *a reflective inclusion*, if it is fully faithful and right adjoint.
-/
class Reflective (R : D ⥤ C) extends IsRightAdjoint R, Full R, Faithful R

variable {i : D ⥤ C}

/-- For a reflective functor `i` (with left adjoint `L`), with unit `η`, we have `η_iL = iL η`.
-/
-- TODO: This holds more generally for idempotent adjunctions, not just reflective adjunctions.
theorem unit_obj_eq_map_unit [Reflective i] (X : C) :
    (ofRightAdjoint i).Unit.app (i.obj ((leftAdjoint i).obj X)) =
      i.map ((leftAdjoint i).map ((ofRightAdjoint i).Unit.app X)) :=
  by
  rw [← cancel_mono (i.map ((of_right_adjoint i).counit.app ((left_adjoint i).obj X))), ← i.map_comp]
  simp

/-- When restricted to objects in `D` given by `i : D ⥤ C`, the unit is an isomorphism. In other words,
`η_iX` is an isomorphism for any `X` in `D`.
More generally this applies to objects essentially in the reflective subcategory, see
`functor.ess_image.unit_iso`.
-/
instance is_iso_unit_obj [Reflective i] {B : D} : IsIso ((ofRightAdjoint i).Unit.app (i.obj B)) := by
  have : (of_right_adjoint i).Unit.app (i.obj B) = inv (i.map ((of_right_adjoint i).counit.app B)) := by
    rw [← comp_hom_eq_id]
    apply (of_right_adjoint i).right_triangle_components
  rw [this]
  exact is_iso.inv_is_iso

/-- If `A` is essentially in the image of a reflective functor `i`, then `η_A` is an isomorphism.
This gives that the "witness" for `A` being in the essential image can instead be given as the
reflection of `A`, with the isomorphism as `η_A`.

(For any `B` in the reflective subcategory, we automatically have that `ε_B` is an iso.)
-/
theorem Functor.EssImage.unit_is_iso [Reflective i] {A : C} (h : A ∈ i.EssImage) :
    IsIso ((ofRightAdjoint i).Unit.app A) := by
  suffices
    (of_right_adjoint i).Unit.app A =
      h.get_iso.inv ≫ (of_right_adjoint i).Unit.app (i.obj h.witness) ≫ (left_adjoint i ⋙ i).map h.get_iso.hom
    by
    rw [this]
    infer_instance
  rw [← nat_trans.naturality]
  simp

/-- If `η_A` is an isomorphism, then `A` is in the essential image of `i`. -/
theorem mem_ess_image_of_unit_is_iso [IsRightAdjoint i] (A : C) [IsIso ((ofRightAdjoint i).Unit.app A)] :
    A ∈ i.EssImage :=
  ⟨(leftAdjoint i).obj A, ⟨(asIso ((ofRightAdjoint i).Unit.app A)).symm⟩⟩

/-- If `η_A` is a split monomorphism, then `A` is in the reflective subcategory. -/
theorem mem_ess_image_of_unit_split_mono [Reflective i] {A : C} [SplitMono ((ofRightAdjoint i).Unit.app A)] :
    A ∈ i.EssImage := by
  let η : 𝟭 C ⟶ left_adjoint i ⋙ i := (of_right_adjoint i).Unit
  have : is_iso (η.app (i.obj ((left_adjoint i).obj A))) := (i.obj_mem_ess_image _).unit_is_iso
  have : epi (η.app A) := by
    apply epi_of_epi (retraction (η.app A)) _
    rw [show retraction _ ≫ η.app A = _ from η.naturality (retraction (η.app A))]
    apply epi_comp (η.app (i.obj ((left_adjoint i).obj A)))
  skip
  have := is_iso_of_epi_of_split_mono (η.app A)
  exact mem_ess_image_of_unit_is_iso A

/-- Composition of reflective functors. -/
instance Reflective.comp (F : C ⥤ D) (G : D ⥤ E) [Fr : Reflective F] [Gr : Reflective G] :
    Reflective (F ⋙ G) where to_faithful := Faithful.comp F G

/-- (Implementation) Auxiliary definition for `unit_comp_partial_bijective`. -/
def unitCompPartialBijectiveAux [Reflective i] (A : C) (B : D) :
    (A ⟶ i.obj B) ≃ (i.obj ((leftAdjoint i).obj A) ⟶ i.obj B) :=
  ((Adjunction.ofRightAdjoint i).homEquiv _ _).symm.trans (equivOfFullyFaithful i)

/-- The description of the inverse of the bijection `unit_comp_partial_bijective_aux`. -/
theorem unit_comp_partial_bijective_aux_symm_apply [Reflective i] {A : C} {B : D}
    (f : i.obj ((leftAdjoint i).obj A) ⟶ i.obj B) :
    (unitCompPartialBijectiveAux _ _).symm f = (ofRightAdjoint i).Unit.app A ≫ f := by
  simp [← unit_comp_partial_bijective_aux]

/-- If `i` has a reflector `L`, then the function `(i.obj (L.obj A) ⟶ B) → (A ⟶ B)` given by
precomposing with `η.app A` is a bijection provided `B` is in the essential image of `i`.
That is, the function `λ (f : i.obj (L.obj A) ⟶ B), η.app A ≫ f` is bijective, as long as `B` is in
the essential image of `i`.
This definition gives an equivalence: the key property that the inverse can be described
nicely is shown in `unit_comp_partial_bijective_symm_apply`.

This establishes there is a natural bijection `(A ⟶ B) ≃ (i.obj (L.obj A) ⟶ B)`. In other words,
from the point of view of objects in `D`, `A` and `i.obj (L.obj A)` look the same: specifically
that `η.app A` is an isomorphism.
-/
def unitCompPartialBijective [Reflective i] (A : C) {B : C} (hB : B ∈ i.EssImage) :
    (A ⟶ B) ≃ (i.obj ((leftAdjoint i).obj A) ⟶ B) :=
  calc
    (A ⟶ B) ≃ (A ⟶ i.obj hB.witness) := Iso.homCongr (Iso.refl _) hB.getIso.symm
    _ ≃ (i.obj _ ⟶ i.obj hB.witness) := unitCompPartialBijectiveAux _ _
    _ ≃ (i.obj ((leftAdjoint i).obj A) ⟶ B) := Iso.homCongr (Iso.refl _) hB.getIso
    

@[simp]
theorem unit_comp_partial_bijective_symm_apply [Reflective i] (A : C) {B : C} (hB : B ∈ i.EssImage) (f) :
    (unitCompPartialBijective A hB).symm f = (ofRightAdjoint i).Unit.app A ≫ f := by
  simp [← unit_comp_partial_bijective, ← unit_comp_partial_bijective_aux_symm_apply]

theorem unit_comp_partial_bijective_symm_natural [Reflective i] (A : C) {B B' : C} (h : B ⟶ B') (hB : B ∈ i.EssImage)
    (hB' : B' ∈ i.EssImage) (f : i.obj ((leftAdjoint i).obj A) ⟶ B) :
    (unitCompPartialBijective A hB').symm (f ≫ h) = (unitCompPartialBijective A hB).symm f ≫ h := by
  simp

theorem unit_comp_partial_bijective_natural [Reflective i] (A : C) {B B' : C} (h : B ⟶ B') (hB : B ∈ i.EssImage)
    (hB' : B' ∈ i.EssImage) (f : A ⟶ B) :
    (unitCompPartialBijective A hB') (f ≫ h) = unitCompPartialBijective A hB f ≫ h := by
  rw [← Equivₓ.eq_symm_apply, unit_comp_partial_bijective_symm_natural A h, Equivₓ.symm_apply_apply]

/-- If `i : D ⥤ C` is reflective, the inverse functor of `i ≌ F.ess_image` can be explicitly
defined by the reflector. -/
@[simps]
def equivEssImageOfReflective [Reflective i] : D ≌ i.EssImage where
  Functor := i.toEssImage
  inverse := i.essImageInclusion ⋙ (leftAdjoint i : _)
  unitIso :=
    NatIso.ofComponents (fun X => (as_iso <| (ofRightAdjoint i).counit.app X).symm)
      (by
        intro X Y f
        dsimp'
        simp only [← is_iso.eq_inv_comp, ← is_iso.comp_inv_eq, ← category.assoc]
        exact ((of_right_adjoint i).counit.naturality _).symm)
  counitIso :=
    NatIso.ofComponents
      (fun X => by
        refine' iso.symm <| as_iso _
        exact (of_right_adjoint i).Unit.app X
        apply is_iso_of_reflects_iso _ i.ess_image_inclusion with { instances := false }
        exact functor.ess_image.unit_is_iso X.prop)
      (by
        intro X Y f
        dsimp'
        simp only [← is_iso.eq_inv_comp, ← is_iso.comp_inv_eq, ← category.assoc]
        exact ((of_right_adjoint i).Unit.naturality f).symm)

end CategoryTheory

