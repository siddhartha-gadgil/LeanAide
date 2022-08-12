/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
import Mathbin.CategoryTheory.Limits.Shapes.Images
import Mathbin.CategoryTheory.Limits.Constructions.EpiMono

/-!
# Preserving images

In this file, we show that if a functor preserves span and cospan, then it preserves images.
-/


noncomputable section

namespace CategoryTheory

namespace PreservesImage

open CategoryTheory

open CategoryTheory.Limits

universe u₁ u₂ v₁ v₂

variable {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Category.{v₂} B]

variable [HasEqualizers A] [HasImages A]

variable [StrongEpiCategory B] [HasImages B]

variable (L : A ⥤ B)

variable [∀ {X Y Z : A} (f : X ⟶ Z) (g : Y ⟶ Z), PreservesLimit (cospan f g) L]

variable [∀ {X Y Z : A} (f : X ⟶ Y) (g : X ⟶ Z), PreservesColimit (span f g) L]

/-- If a functor preserves span and cospan, then it preserves images.
-/
@[simps]
def iso {X Y : A} (f : X ⟶ Y) : image (L.map f) ≅ L.obj (image f) :=
  let aux1 : StrongEpiMonoFactorisation (L.map f) :=
    { i := L.obj (Limits.image f), m := L.map <| Limits.image.ι _, m_mono := preserves_mono_of_preserves_limit _ _,
      e := L.map <| factorThruImage _,
      e_strong_epi := @strong_epi_of_epi _ _ _ <| preserves_epi_of_preserves_colimit L _,
      fac' := by
        rw [← L.map_comp, limits.image.fac] }
  IsImage.isoExt (Image.isImage (L.map f)) aux1.toMonoIsImage

@[reassoc]
theorem factor_thru_image_comp_hom {X Y : A} (f : X ⟶ Y) :
    factorThruImage (L.map f) ≫ (iso L f).Hom = L.map (factorThruImage f) := by
  simp

@[reassoc]
theorem hom_comp_map_image_ι {X Y : A} (f : X ⟶ Y) : (iso L f).Hom ≫ L.map (image.ι f) = image.ι (L.map f) := by
  simp

@[reassoc]
theorem inv_comp_image_ι_map {X Y : A} (f : X ⟶ Y) : (iso L f).inv ≫ image.ι (L.map f) = L.map (image.ι f) := by
  simp

end PreservesImage

end CategoryTheory

