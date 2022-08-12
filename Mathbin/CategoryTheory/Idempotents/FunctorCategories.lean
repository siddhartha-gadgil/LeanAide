/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathbin.CategoryTheory.Idempotents.Karoubi

/-!
# Idempotent completeness and functor categories

In this file we define an instance `functor_category_is_idempotent_complete` expressing
that a functor category `J ⥤ C` is idempotent complete when the target category `C` is.

We also provide a fully faithful functor
`karoubi_functor_category_embedding : karoubi (J ⥤ C)) : J ⥤ karoubi C` for all categories
`J` and `C`.

-/


open CategoryTheory

open CategoryTheory.Category

open CategoryTheory.Idempotents.Karoubi

open CategoryTheory.Limits

namespace CategoryTheory

namespace Idempotents

variable (J C : Type _) [Category J] [Category C]

instance functor_category_is_idempotent_complete [IsIdempotentComplete C] : IsIdempotentComplete (J ⥤ C) := by
  refine' ⟨_⟩
  intro F p hp
  have hC := (is_idempotent_complete_iff_has_equalizer_of_id_and_idempotent C).mp inferInstance
  have : ∀ j : J, has_equalizer (𝟙 _) (p.app j) := fun j => hC _ _ (congr_app hp j)
  /- We construct the direct factor `Y` associated to `p : F ⟶ F` by computing
      the equalizer of the identity and `p.app j` on each object `(j : J)`.  -/
  let Y : J ⥤ C :=
    { obj := fun j => limits.equalizer (𝟙 _) (p.app j),
      map := fun j j' φ =>
        equalizer.lift (limits.equalizer.ι (𝟙 _) (p.app j) ≫ F.map φ)
          (by
            rw [comp_id, assoc, p.naturality φ, ← assoc, ← limits.equalizer.condition, comp_id]),
      map_id' := fun j => by
        ext
        simp only [← comp_id, ← Functor.map_id, ← equalizer.lift_ι, ← id_comp],
      map_comp' := fun j j' j'' φ φ' => by
        ext
        simp only [← assoc, ← functor.map_comp, ← equalizer.lift_ι, ← equalizer.lift_ι_assoc] }
  let i : Y ⟶ F :=
    { app := fun j => equalizer.ι _ _,
      naturality' := fun j j' φ => by
        rw [equalizer.lift_ι] }
  let e : F ⟶ Y :=
    { app := fun j =>
        equalizer.lift (p.app j)
          (by
            rw [comp_id]
            exact (congr_app hp j).symm),
      naturality' := fun j j' φ => by
        ext
        simp only [← assoc, ← equalizer.lift_ι, ← nat_trans.naturality, ← equalizer.lift_ι_assoc] }
  use Y, i, e
  constructor <;> ext j
  · simp only [← nat_trans.comp_app, ← assoc, ← equalizer.lift_ι, ← nat_trans.id_app, ← id_comp, equalizer.condition, ←
      comp_id]
    
  · simp only [← nat_trans.comp_app, ← equalizer.lift_ι]
    

namespace KaroubiFunctorCategoryEmbedding

variable {J C}

/-- On objects, the functor which sends a formal direct factor `P` of a
functor `F : J ⥤ C` to the functor `J ⥤ karoubi C` which sends `(j : J)` to
the corresponding direct factor of `F.obj j`. -/
@[simps]
def obj (P : Karoubi (J ⥤ C)) : J ⥤ Karoubi C where
  obj := fun j => ⟨P.x.obj j, P.p.app j, congr_app P.idem j⟩
  map := fun j j' φ =>
    { f := P.p.app j ≫ P.x.map φ,
      comm := by
        simp only [← nat_trans.naturality, ← assoc]
        have h := congr_app P.idem j
        rw [nat_trans.comp_app] at h
        slice_rhs 1 3 => erw [h, h] }
  map_id' := fun j => by
    ext
    simp only [← Functor.map_id, ← comp_id, ← id_eq]
  map_comp' := fun j j' j'' φ φ' => by
    ext
    have h := congr_app P.idem j
    rw [nat_trans.comp_app] at h
    simp only [← assoc, ← nat_trans.naturality_assoc, ← functor.map_comp, ← comp]
    slice_rhs 1 2 => rw [h]
    rw [assoc]

/-- Tautological action on maps of the functor `karoubi (J ⥤ C) ⥤ (J ⥤ karoubi C)`. -/
@[simps]
def map {P Q : Karoubi (J ⥤ C)} (f : P ⟶ Q) : obj P ⟶ obj Q where
  app := fun j => ⟨f.f.app j, congr_app f.comm j⟩
  naturality' := fun j j' φ => by
    ext
    simp only [← comp]
    have h := congr_app (comp_p f) j
    have h' := congr_app (p_comp f) j'
    dsimp'  at h h'⊢
    slice_rhs 1 2 => erw [h]
    rw [← P.p.naturality]
    slice_lhs 2 3 => erw [h']
    rw [f.f.naturality]

end KaroubiFunctorCategoryEmbedding

variable (J C)

/-- The tautological fully faithful functor `karoubi (J ⥤ C) ⥤ (J ⥤ karoubi C)`. -/
@[simps]
def karoubiFunctorCategoryEmbedding : Karoubi (J ⥤ C) ⥤ J ⥤ Karoubi C where
  obj := KaroubiFunctorCategoryEmbedding.obj
  map := fun P Q => KaroubiFunctorCategoryEmbedding.map
  map_id' := fun P => rfl
  map_comp' := fun P Q R f g => rfl

instance : Full (karoubiFunctorCategoryEmbedding J C) where
  preimage := fun P Q f =>
    { f :=
        { app := fun j => (f.app j).f,
          naturality' := fun j j' φ => by
            slice_rhs 1 1 => rw [← karoubi.comp_p]
            have h := hom_ext.mp (f.naturality φ)
            simp only [← comp] at h
            dsimp' [← karoubi_functor_category_embedding]  at h⊢
            erw [assoc, ← h, ← P.p.naturality φ, assoc, p_comp (f.app j')] },
      comm := by
        ext j
        exact (f.app j).comm }
  witness' := fun P Q f => by
    ext j
    rfl

instance :
    Faithful (karoubiFunctorCategoryEmbedding J C) where map_injective' := fun P Q f f' h => by
    ext j
    exact hom_ext.mp (congr_app h j)

/-- The composition of `(J ⥤ C) ⥤ karoubi (J ⥤ C)` and `karoubi (J ⥤ C) ⥤ (J ⥤ karoubi C)`
equals the functor `(J ⥤ C) ⥤ (J ⥤ karoubi C)` given by the composition with
`to_karoubi C : C ⥤ karoubi C`. -/
theorem to_karoubi_comp_karoubi_functor_category_embedding :
    toKaroubi _ ⋙ karoubiFunctorCategoryEmbedding J C = (whiskeringRight J _ _).obj (toKaroubi C) := by
  apply Functor.ext
  · intro X Y f
    ext j
    dsimp' [← to_karoubi]
    simp only [← eq_to_hom_app, ← eq_to_hom_refl, ← id_comp]
    erw [comp_id]
    
  · intro X
    apply Functor.ext
    · intro j j' φ
      ext
      dsimp'
      simpa only [← comp_id, ← id_comp]
      
    · intro j
      rfl
      
    

end Idempotents

end CategoryTheory

