/-
Copyright (c) 2019 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton, Scott Morrison
-/
import Mathbin.CategoryTheory.Adjunction.Basic
import Mathbin.CategoryTheory.Opposites
import Mathbin.CategoryTheory.Groupoid

/-!
# Facts about epimorphisms and monomorphisms.

The definitions of `epi` and `mono` are in `category_theory.category`,
since they are used by some lemmas for `iso`, which is used everywhere.
-/


universe v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]

instance unop_mono_of_epi {A B : Cᵒᵖ} (f : A ⟶ B) [Epi f] : Mono f.unop :=
  ⟨fun Z g h eq => Quiver.Hom.op_inj ((cancel_epi f).1 (Quiver.Hom.unop_inj Eq))⟩

instance unop_epi_of_mono {A B : Cᵒᵖ} (f : A ⟶ B) [Mono f] : Epi f.unop :=
  ⟨fun Z g h eq => Quiver.Hom.op_inj ((cancel_mono f).1 (Quiver.Hom.unop_inj Eq))⟩

instance op_mono_of_epi {A B : C} (f : A ⟶ B) [Epi f] : Mono f.op :=
  ⟨fun Z g h eq => Quiver.Hom.unop_inj ((cancel_epi f).1 (Quiver.Hom.op_inj Eq))⟩

instance op_epi_of_mono {A B : C} (f : A ⟶ B) [Mono f] : Epi f.op :=
  ⟨fun Z g h eq => Quiver.Hom.unop_inj ((cancel_mono f).1 (Quiver.Hom.op_inj Eq))⟩

/-- A split monomorphism is a morphism `f : X ⟶ Y` admitting a retraction `retraction f : Y ⟶ X`
such that `f ≫ retraction f = 𝟙 X`.

Every split monomorphism is a monomorphism.
-/
class SplitMono {X Y : C} (f : X ⟶ Y) where
  retraction : Y ⟶ X
  id' : f ≫ retraction = 𝟙 X := by
    run_tac
      obviously

/-- A split epimorphism is a morphism `f : X ⟶ Y` admitting a section `section_ f : Y ⟶ X`
such that `section_ f ≫ f = 𝟙 Y`.
(Note that `section` is a reserved keyword, so we append an underscore.)

Every split epimorphism is an epimorphism.
-/
class SplitEpi {X Y : C} (f : X ⟶ Y) where
  section_ : Y ⟶ X
  id' : section_ ≫ f = 𝟙 Y := by
    run_tac
      obviously

/-- The chosen retraction of a split monomorphism. -/
def retraction {X Y : C} (f : X ⟶ Y) [SplitMono f] : Y ⟶ X :=
  SplitMono.retraction f

@[simp, reassoc]
theorem SplitMono.id {X Y : C} (f : X ⟶ Y) [SplitMono f] : f ≫ retraction f = 𝟙 X :=
  split_mono.id'

/-- The retraction of a split monomorphism is itself a split epimorphism. -/
instance retractionSplitEpi {X Y : C} (f : X ⟶ Y) [SplitMono f] : SplitEpi (retraction f) where section_ := f

/-- A split mono which is epi is an iso. -/
theorem is_iso_of_epi_of_split_mono {X Y : C} (f : X ⟶ Y) [SplitMono f] [Epi f] : IsIso f :=
  ⟨⟨retraction f,
      ⟨by
        simp , by
        simp [cancel_epi f]⟩⟩⟩

/-- The chosen section of a split epimorphism.
(Note that `section` is a reserved keyword, so we append an underscore.)
-/
def section_ {X Y : C} (f : X ⟶ Y) [SplitEpi f] : Y ⟶ X :=
  SplitEpi.section_ f

@[simp, reassoc]
theorem SplitEpi.id {X Y : C} (f : X ⟶ Y) [SplitEpi f] : section_ f ≫ f = 𝟙 Y :=
  split_epi.id'

/-- The section of a split epimorphism is itself a split monomorphism. -/
instance sectionSplitMono {X Y : C} (f : X ⟶ Y) [SplitEpi f] : SplitMono (section_ f) where retraction := f

/-- A split epi which is mono is an iso. -/
theorem is_iso_of_mono_of_split_epi {X Y : C} (f : X ⟶ Y) [Mono f] [SplitEpi f] : IsIso f :=
  ⟨⟨section_ f,
      ⟨by
        simp [cancel_mono f], by
        simp ⟩⟩⟩

/-- Every iso is a split mono. -/
noncomputable instance (priority := 100) SplitMono.ofIso {X Y : C} (f : X ⟶ Y) [IsIso f] :
    SplitMono f where retraction := inv f

/-- Every iso is a split epi. -/
noncomputable instance (priority := 100) SplitEpi.ofIso {X Y : C} (f : X ⟶ Y) [IsIso f] :
    SplitEpi f where section_ := inv f

/-- Every split mono is a mono. -/
instance (priority := 100) SplitMono.mono {X Y : C} (f : X ⟶ Y) [SplitMono f] :
    Mono f where right_cancellation := fun Z g h w => by
    replace w := w =≫ retraction f
    simpa using w

/-- Every split epi is an epi. -/
instance (priority := 100) SplitEpi.epi {X Y : C} (f : X ⟶ Y) [SplitEpi f] :
    Epi f where left_cancellation := fun Z g h w => by
    replace w := section_ f ≫= w
    simpa using w

/-- Every split mono whose retraction is mono is an iso. -/
theorem IsIso.of_mono_retraction {X Y : C} {f : X ⟶ Y} [SplitMono f] [mono <| retraction f] : IsIso f :=
  ⟨⟨retraction f,
      ⟨by
        simp ,
        (cancel_mono_id <| retraction f).mp
          (by
            simp )⟩⟩⟩

/-- Every split epi whose section is epi is an iso. -/
theorem IsIso.of_epi_section {X Y : C} {f : X ⟶ Y} [SplitEpi f] [epi <| section_ f] : IsIso f :=
  ⟨⟨section_ f,
      ⟨(cancel_epi_id <| section_ f).mp
          (by
            simp ),
        by
        simp ⟩⟩⟩

/-- A category where every morphism has a `trunc` retraction is computably a groupoid. -/
-- FIXME this has unnecessarily become noncomputable!
noncomputable def Groupoid.ofTruncSplitMono (all_split_mono : ∀ {X Y : C} (f : X ⟶ Y), Trunc (SplitMono f)) :
    Groupoid.{v₁} C := by
  apply groupoid.of_is_iso
  intro X Y f
  trunc_cases all_split_mono f
  trunc_cases all_split_mono (retraction f)
  apply is_iso.of_mono_retraction

section

variable (C)

/-- A split mono category is a category in which every monomorphism is split. -/
class SplitMonoCategory where
  splitMonoOfMono : ∀ {X Y : C} (f : X ⟶ Y) [Mono f], SplitMono f

/-- A split epi category is a category in which every epimorphism is split. -/
class SplitEpiCategory where
  splitEpiOfEpi : ∀ {X Y : C} (f : X ⟶ Y) [Epi f], SplitEpi f

end

/-- In a category in which every monomorphism is split, every monomorphism splits. This is not an
    instance because it would create an instance loop. -/
def splitMonoOfMono [SplitMonoCategory C] {X Y : C} (f : X ⟶ Y) [Mono f] : SplitMono f :=
  SplitMonoCategory.splitMonoOfMono _

/-- In a category in which every epimorphism is split, every epimorphism splits. This is not an
    instance because it would create an instance loop. -/
def splitEpiOfEpi [SplitEpiCategory C] {X Y : C} (f : X ⟶ Y) [Epi f] : SplitEpi f :=
  SplitEpiCategory.splitEpiOfEpi _

section

variable {D : Type u₂} [Category.{v₂} D]

/-- Split monomorphisms are also absolute monomorphisms. -/
instance {X Y : C} (f : X ⟶ Y) [SplitMono f] (F : C ⥤ D) : SplitMono (F.map f) where
  retraction := F.map (retraction f)
  id' := by
    rw [← functor.map_comp, split_mono.id, Functor.map_id]

/-- Split epimorphisms are also absolute epimorphisms. -/
instance {X Y : C} (f : X ⟶ Y) [SplitEpi f] (F : C ⥤ D) : SplitEpi (F.map f) where
  section_ := F.map (section_ f)
  id' := by
    rw [← functor.map_comp, split_epi.id, Functor.map_id]

end

end CategoryTheory

