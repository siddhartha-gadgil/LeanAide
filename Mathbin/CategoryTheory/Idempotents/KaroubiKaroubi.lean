/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathbin.CategoryTheory.Idempotents.Karoubi

/-!
# Idempotence of the Karoubi envelope

In this file, we construct the equivalence of categories
`karoubi_karoubi.equivalence C : karoubi C ≌ karoubi (karoubi C)` for any category `C`.

-/


open CategoryTheory.Category

open CategoryTheory.Idempotents.Karoubi

namespace CategoryTheory

namespace Idempotents

namespace KaroubiKaroubi

variable (C : Type _) [Category C]

/-- The canonical functor `karoubi (karoubi C) ⥤ karoubi C` -/
@[simps]
def inverse : Karoubi (Karoubi C) ⥤ Karoubi C where
  obj := fun P =>
    ⟨P.x.x, P.p.f, by
      simpa only [← hom_ext] using P.idem⟩
  map := fun P Q f =>
    ⟨f.f.f, by
      simpa only [← hom_ext] using f.comm⟩

instance [Preadditive C] : Functor.Additive (inverse C) where

/-- The unit isomorphism of the equivalence -/
@[simps]
def unitIso : 𝟭 (Karoubi C) ≅ toKaroubi (Karoubi C) ⋙ inverse C :=
  eqToIso
    (by
      apply Functor.ext
      · intro P Q f
        ext
        simp only [← functor.id_map, ← inverse_map_f, ← to_karoubi_map_f, ← eq_to_hom_f, ← eq_to_hom_refl, ← comp_id, ←
          p_comp_assoc, ← functor.comp_map, ← comp]
        dsimp'
        simp only [← id_eq, ← comp_p]
        
      · intro P
        ext
        · simpa only [← eq_to_hom_refl, ← comp_id, ← id_comp]
          
        · rfl
          
        )

/-- The counit isomorphism of the equivalence -/
@[simps]
def counitIso : inverse C ⋙ toKaroubi (Karoubi C) ≅ 𝟭 (Karoubi (Karoubi C)) where
  Hom :=
    { app := fun P =>
        { f :=
            { f := P.p.1,
              comm := by
                have h := P.idem
                simp only [← hom_ext, ← comp] at h
                erw [← assoc, h, comp_p] },
          comm := by
            have h := P.idem
            simp only [← hom_ext, ← comp] at h⊢
            erw [h, h] },
      naturality' := fun P Q f => by
        simpa only [← hom_ext] using (p_comm f).symm }
  inv :=
    { app := fun P =>
        { f :=
            { f := P.p.1,
              comm := by
                have h := P.idem
                simp only [← hom_ext, ← comp] at h
                erw [h, p_comp] },
          comm := by
            have h := P.idem
            simp only [← hom_ext, ← comp] at h⊢
            erw [h, h] },
      naturality' := fun P Q f => by
        simpa [← hom_ext] using (p_comm f).symm }
  hom_inv_id' := by
    ext P
    simpa only [← hom_ext, ← id_eq] using P.idem
  inv_hom_id' := by
    ext P
    simpa only [← hom_ext, ← id_eq] using P.idem

/-- The equivalence `karoubi C ≌ karoubi (karoubi C)` -/
@[simps]
def equivalence : Karoubi C ≌ Karoubi (Karoubi C) where
  Functor := toKaroubi (Karoubi C)
  inverse := KaroubiKaroubi.inverse C
  unitIso := KaroubiKaroubi.unitIso C
  counitIso := KaroubiKaroubi.counitIso C
  functor_unit_iso_comp' := fun P => by
    ext
    simp only [← eq_to_hom_f, ← eq_to_hom_refl, ← comp_id, ← counit_iso_hom_app_f_f, ← to_karoubi_obj_p, ← id_eq, ←
      assoc, ← comp, ← unit_iso_hom, ← eq_to_hom_app, ← eq_to_hom_map]
    erw [P.idem, P.idem]

instance equivalence.additive_functor [Preadditive C] : Functor.Additive (equivalence C).Functor := by
  dsimp'
  infer_instance

instance equivalence.additive_inverse [Preadditive C] : Functor.Additive (equivalence C).inverse := by
  dsimp'
  infer_instance

end KaroubiKaroubi

end Idempotents

end CategoryTheory

