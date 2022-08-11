/-
Copyright (c) 2021 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathbin.CategoryTheory.Limits.Shapes.Pullbacks
import Mathbin.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathbin.CategoryTheory.Limits.Preserves.Shapes.Pullbacks

/-!
# Relating monomorphisms and epimorphisms to limits and colimits

If `F` preserves (resp. reflects) pullbacks, then it preserves (resp. reflects) monomorphisms.

We also provide the dual version for epimorphisms.

-/


universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Category Limits

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]

variable (F : C ⥤ D)

/-- If `F` preserves pullbacks, then it preserves monomorphisms. -/
theorem preserves_mono_of_preserves_limit {X Y : C} (f : X ⟶ Y) [PreservesLimit (cospan f f) F] [Mono f] :
    Mono (F.map f) := by
  have := is_limit_pullback_cone_map_of_is_limit F _ (pullback_cone.is_limit_mk_id_id f)
  simp_rw [F.map_id] at this
  apply pullback_cone.mono_of_is_limit_mk_id_id _ this

instance (priority := 100) preserves_monomorphisms_of_preserves_limits_of_shape
    [PreservesLimitsOfShape WalkingCospan F] :
    F.PreservesMonomorphisms where preserves := fun X Y f hf => preserves_mono_of_preserves_limit F f

/-- If `F` reflects pullbacks, then it reflects monomorphisms. -/
theorem reflects_mono_of_reflects_limit {X Y : C} (f : X ⟶ Y) [ReflectsLimit (cospan f f) F] [Mono (F.map f)] :
    Mono f := by
  have := pullback_cone.is_limit_mk_id_id (F.map f)
  simp_rw [← F.map_id] at this
  apply pullback_cone.mono_of_is_limit_mk_id_id _ (is_limit_of_is_limit_pullback_cone_map F _ this)

instance (priority := 100) reflects_monomorphisms_of_reflects_limits_of_shape [ReflectsLimitsOfShape WalkingCospan F] :
    F.ReflectsMonomorphisms where reflects := fun X Y f hf => reflects_mono_of_reflects_limit F f

/-- If `F` preserves pushouts, then it preserves epimorphisms. -/
theorem preserves_epi_of_preserves_colimit {X Y : C} (f : X ⟶ Y) [PreservesColimit (span f f) F] [Epi f] :
    Epi (F.map f) := by
  have := is_colimit_pushout_cocone_map_of_is_colimit F _ (pushout_cocone.is_colimit_mk_id_id f)
  simp_rw [F.map_id] at this
  apply pushout_cocone.epi_of_is_colimit_mk_id_id _ this

instance (priority := 100) preserves_epimorphisms_of_preserves_colimits_of_shape
    [PreservesColimitsOfShape WalkingSpan F] :
    F.PreservesEpimorphisms where preserves := fun X Y f hf => preserves_epi_of_preserves_colimit F f

/-- If `F` reflects pushouts, then it reflects epimorphisms. -/
theorem reflects_epi_of_reflects_colimit {X Y : C} (f : X ⟶ Y) [ReflectsColimit (span f f) F] [Epi (F.map f)] : Epi f :=
  by
  have := pushout_cocone.is_colimit_mk_id_id (F.map f)
  simp_rw [← F.map_id] at this
  apply pushout_cocone.epi_of_is_colimit_mk_id_id _ (is_colimit_of_is_colimit_pushout_cocone_map F _ this)

instance (priority := 100) reflects_epimorphisms_of_reflects_colimits_of_shape [ReflectsColimitsOfShape WalkingSpan F] :
    F.ReflectsEpimorphisms where reflects := fun X Y f hf => reflects_epi_of_reflects_colimit F f

end CategoryTheory

