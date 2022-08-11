/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathbin.CategoryTheory.EpiMono

/-!
# Preservation and reflection of monomorphisms and epimorphisms

We provide typeclasses that state that a functor preserves or reflects monomorphisms or
epimorphisms.
-/


open CategoryTheory

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] {E : Type u₃} [Category.{v₃} E]

/-- A functor preserves monomorphisms if it maps monomorphisms to monomorphisms. -/
class PreservesMonomorphisms (F : C ⥤ D) : Prop where
  preserves : ∀ {X Y : C} (f : X ⟶ Y) [Mono f], Mono (F.map f)

instance map_mono (F : C ⥤ D) [PreservesMonomorphisms F] {X Y : C} (f : X ⟶ Y) [Mono f] : Mono (F.map f) :=
  PreservesMonomorphisms.preserves f

/-- A functor preserves epimorphisms if it maps epimorphisms to epimorphisms. -/
class PreservesEpimorphisms (F : C ⥤ D) : Prop where
  preserves : ∀ {X Y : C} (f : X ⟶ Y) [Epi f], Epi (F.map f)

instance map_epi (F : C ⥤ D) [PreservesEpimorphisms F] {X Y : C} (f : X ⟶ Y) [Epi f] : Epi (F.map f) :=
  PreservesEpimorphisms.preserves f

/-- A functor reflects monomorphisms if morphisms that are mapped to monomorphisms are themselves
    monomorphisms. -/
class ReflectsMonomorphisms (F : C ⥤ D) : Prop where
  reflects : ∀ {X Y : C} (f : X ⟶ Y), Mono (F.map f) → Mono f

theorem mono_of_mono_map (F : C ⥤ D) [ReflectsMonomorphisms F] {X Y : C} {f : X ⟶ Y} (h : Mono (F.map f)) : Mono f :=
  ReflectsMonomorphisms.reflects f h

/-- A functor reflects epimorphisms if morphisms that are mapped to epimorphisms are themselves
    epimorphisms. -/
class ReflectsEpimorphisms (F : C ⥤ D) : Prop where
  reflects : ∀ {X Y : C} (f : X ⟶ Y), Epi (F.map f) → Epi f

theorem epi_of_epi_map (F : C ⥤ D) [ReflectsEpimorphisms F] {X Y : C} {f : X ⟶ Y} (h : Epi (F.map f)) : Epi f :=
  ReflectsEpimorphisms.reflects f h

instance preserves_monomorphisms_comp (F : C ⥤ D) (G : D ⥤ E) [PreservesMonomorphisms F] [PreservesMonomorphisms G] :
    PreservesMonomorphisms (F ⋙ G) where preserves := fun X Y f h => by
    rw [comp_map]
    exact inferInstance

instance preserves_epimorphisms_comp (F : C ⥤ D) (G : D ⥤ E) [PreservesEpimorphisms F] [PreservesEpimorphisms G] :
    PreservesEpimorphisms (F ⋙ G) where preserves := fun X Y f h => by
    rw [comp_map]
    exact inferInstance

instance reflects_monomorphisms_comp (F : C ⥤ D) (G : D ⥤ E) [ReflectsMonomorphisms F] [ReflectsMonomorphisms G] :
    ReflectsMonomorphisms (F ⋙ G) where reflects := fun X Y f h => F.mono_of_mono_map (G.mono_of_mono_map h)

instance reflects_epimorphisms_comp (F : C ⥤ D) (G : D ⥤ E) [ReflectsEpimorphisms F] [ReflectsEpimorphisms G] :
    ReflectsEpimorphisms (F ⋙ G) where reflects := fun X Y f h => F.epi_of_epi_map (G.epi_of_epi_map h)

theorem PreservesMonomorphisms.of_iso {F G : C ⥤ D} [PreservesMonomorphisms F] (α : F ≅ G) : PreservesMonomorphisms G :=
  { preserves := fun X Y f h => by
      have : mono (F.map f ≫ (α.app Y).Hom) := mono_comp _ _
      convert (mono_comp _ _ : mono ((α.app X).inv ≫ F.map f ≫ (α.app Y).Hom))
      rw [iso.eq_inv_comp, iso.app_hom, iso.app_hom, nat_trans.naturality] }

theorem PreservesMonomorphisms.iso_iff {F G : C ⥤ D} (α : F ≅ G) :
    PreservesMonomorphisms F ↔ PreservesMonomorphisms G :=
  ⟨fun h => preserves_monomorphisms.of_iso α, fun h => preserves_monomorphisms.of_iso α.symm⟩

theorem PreservesEpimorphisms.of_iso {F G : C ⥤ D} [PreservesEpimorphisms F] (α : F ≅ G) : PreservesEpimorphisms G :=
  { preserves := fun X Y f h => by
      have : epi (F.map f ≫ (α.app Y).Hom) := epi_comp _ _
      convert (epi_comp _ _ : epi ((α.app X).inv ≫ F.map f ≫ (α.app Y).Hom))
      rw [iso.eq_inv_comp, iso.app_hom, iso.app_hom, nat_trans.naturality] }

theorem PreservesEpimorphisms.iso_iff {F G : C ⥤ D} (α : F ≅ G) : PreservesEpimorphisms F ↔ PreservesEpimorphisms G :=
  ⟨fun h => preserves_epimorphisms.of_iso α, fun h => preserves_epimorphisms.of_iso α.symm⟩

theorem ReflectsMonomorphisms.of_iso {F G : C ⥤ D} [ReflectsMonomorphisms F] (α : F ≅ G) : ReflectsMonomorphisms G :=
  { reflects := fun X Y f h => by
      apply F.mono_of_mono_map
      have : mono (G.map f ≫ (α.app Y).inv) := mono_comp _ _
      convert (mono_comp _ _ : mono ((α.app X).Hom ≫ G.map f ≫ (α.app Y).inv))
      rw [← category.assoc, iso.eq_comp_inv, iso.app_hom, iso.app_hom, nat_trans.naturality] }

theorem ReflectsMonomorphisms.iso_iff {F G : C ⥤ D} (α : F ≅ G) : ReflectsMonomorphisms F ↔ ReflectsMonomorphisms G :=
  ⟨fun h => reflects_monomorphisms.of_iso α, fun h => reflects_monomorphisms.of_iso α.symm⟩

theorem ReflectsEpimorphisms.of_iso {F G : C ⥤ D} [ReflectsEpimorphisms F] (α : F ≅ G) : ReflectsEpimorphisms G :=
  { reflects := fun X Y f h => by
      apply F.epi_of_epi_map
      have : epi (G.map f ≫ (α.app Y).inv) := epi_comp _ _
      convert (epi_comp _ _ : epi ((α.app X).Hom ≫ G.map f ≫ (α.app Y).inv))
      rw [← category.assoc, iso.eq_comp_inv, iso.app_hom, iso.app_hom, nat_trans.naturality] }

theorem ReflectsEpimorphisms.iso_iff {F G : C ⥤ D} (α : F ≅ G) : ReflectsEpimorphisms F ↔ ReflectsEpimorphisms G :=
  ⟨fun h => reflects_epimorphisms.of_iso α, fun h => reflects_epimorphisms.of_iso α.symm⟩

theorem preserves_epimorphsisms_of_adjunction {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) : PreservesEpimorphisms F :=
  { preserves := fun X Y f hf =>
      ⟨by
        intro Z g h H
        replace H := congr_arg (adj.hom_equiv X Z) H
        rwa [adj.hom_equiv_naturality_left, adj.hom_equiv_naturality_left, cancel_epi, Equivₓ.apply_eq_iff_eq] at H⟩ }

instance (priority := 100) preserves_epimorphisms_of_is_left_adjoint (F : C ⥤ D) [IsLeftAdjoint F] :
    PreservesEpimorphisms F :=
  preserves_epimorphsisms_of_adjunction (Adjunction.ofLeftAdjoint F)

theorem preserves_monomorphisms_of_adjunction {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) : PreservesMonomorphisms G :=
  { preserves := fun X Y f hf =>
      ⟨by
        intro Z g h H
        replace H := congr_arg (adj.hom_equiv Z Y).symm H
        rwa [adj.hom_equiv_naturality_right_symm, adj.hom_equiv_naturality_right_symm, cancel_mono,
          Equivₓ.apply_eq_iff_eq] at H⟩ }

instance (priority := 100) preserves_monomorphisms_of_is_right_adjoint (F : C ⥤ D) [IsRightAdjoint F] :
    PreservesMonomorphisms F :=
  preserves_monomorphisms_of_adjunction (Adjunction.ofRightAdjoint F)

instance (priority := 100) reflects_monomorphisms_of_faithful (F : C ⥤ D) [Faithful F] :
    ReflectsMonomorphisms
      F where reflects := fun X Y f hf =>
    ⟨fun Z g h hgh =>
      F.map_injective
        ((cancel_mono (F.map f)).1
          (by
            rw [← F.map_comp, hgh, F.map_comp]))⟩

instance (priority := 100) reflects_epimorphisms_of_faithful (F : C ⥤ D) [Faithful F] :
    ReflectsEpimorphisms
      F where reflects := fun X Y f hf =>
    ⟨fun Z g h hgh =>
      F.map_injective
        ((cancel_epi (F.map f)).1
          (by
            rw [← F.map_comp, hgh, F.map_comp]))⟩

end CategoryTheory.Functor

