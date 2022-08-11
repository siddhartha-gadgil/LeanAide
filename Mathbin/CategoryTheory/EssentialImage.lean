/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathbin.CategoryTheory.NaturalIsomorphism
import Mathbin.CategoryTheory.FullSubcategory
import Mathbin.Data.Set.Basic

/-!
# Essential image of a functor

The essential image `ess_image` of a functor consists of the objects in the target category which
are isomorphic to an object in the image of the object function.
This, for instance, allows us to talk about objects belonging to a subcategory expressed as a
functor rather than a subtype, preserving the principle of equivalence. For example this lets us
define exponential ideals.

The essential image can also be seen as a subcategory of the target category, and witnesses that
a functor decomposes into a essentially surjective functor and a fully faithful functor.
(TODO: show that this decomposition forms an orthogonal factorisation system).
-/


universe v₁ v₂ u₁ u₂

noncomputable section

namespace CategoryTheory

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D] {F : C ⥤ D}

namespace Functor

/-- The essential image of a functor `F` consists of those objects in the target category which are
isomorphic to an object in the image of the function `F.obj`. In other words, this is the closure
under isomorphism of the function `F.obj`.
This is the "non-evil" way of describing the image of a functor.
-/
def EssImage (F : C ⥤ D) : Set D := fun Y => ∃ X : C, Nonempty (F.obj X ≅ Y)

/-- Get the witnessing object that `Y` is in the subcategory given by `F`. -/
def EssImage.witness {Y : D} (h : Y ∈ F.EssImage) : C :=
  h.some

/-- Extract the isomorphism between `F.obj h.witness` and `Y` itself. -/
def EssImage.getIso {Y : D} (h : Y ∈ F.EssImage) : F.obj h.witness ≅ Y :=
  Classical.choice h.some_spec

/-- Being in the essential image is a "hygenic" property: it is preserved under isomorphism. -/
theorem EssImage.of_iso {Y Y' : D} (h : Y ≅ Y') (hY : Y ∈ EssImage F) : Y' ∈ EssImage F :=
  hY.imp fun B => Nonempty.map (· ≪≫ h)

/-- If `Y` is in the essential image of `F` then it is in the essential image of `F'` as long as
`F ≅ F'`.
-/
theorem EssImage.of_nat_iso {F' : C ⥤ D} (h : F ≅ F') {Y : D} (hY : Y ∈ EssImage F) : Y ∈ EssImage F' :=
  hY.imp fun X => Nonempty.map fun t => h.symm.app X ≪≫ t

/-- Isomorphic functors have equal essential images. -/
theorem ess_image_eq_of_nat_iso {F' : C ⥤ D} (h : F ≅ F') : EssImage F = EssImage F' :=
  Set.ext fun A => ⟨EssImage.of_nat_iso h, EssImage.of_nat_iso h.symm⟩

/-- An object in the image is in the essential image. -/
theorem obj_mem_ess_image (F : D ⥤ C) (Y : D) : F.obj Y ∈ EssImage F :=
  ⟨Y, ⟨Iso.refl _⟩⟩

instance : Category F.EssImage :=
  CategoryTheory.fullSubcategory _

/-- The essential image as a subcategory has a fully faithful inclusion into the target category. -/
@[simps]
def essImageInclusion (F : C ⥤ D) : F.EssImage ⥤ D :=
  fullSubcategoryInclusion _ deriving Full, Faithful

/-- Given a functor `F : C ⥤ D`, we have an (essentially surjective) functor from `C` to the essential
image of `F`.
-/
@[simps]
def toEssImage (F : C ⥤ D) : C ⥤ F.EssImage where
  obj := fun X => ⟨_, obj_mem_ess_image _ X⟩
  map := fun X Y f => (essImageInclusion F).preimage (F.map f)

/-- The functor `F` factorises through its essential image, where the first functor is essentially
surjective and the second is fully faithful.
-/
@[simps]
def toEssImageCompEssentialImageInclusion (F : C ⥤ D) : F.toEssImage ⋙ F.essImageInclusion ≅ F :=
  NatIso.ofComponents (fun X => Iso.refl _)
    (by
      tidy)

end Functor

-- ./././Mathport/Syntax/Translate/Basic.lean:1440:30: infer kinds are unsupported in Lean 4: #[`mem_ess_image] []
/-- A functor `F : C ⥤ D` is essentially surjective if every object of `D` is in the essential image
of `F`. In other words, for every `Y : D`, there is some `X : C` with `F.obj X ≅ Y`.

See <https://stacks.math.columbia.edu/tag/001C>.
-/
class EssSurj (F : C ⥤ D) : Prop where
  mem_ess_image (Y : D) : Y ∈ F.EssImage

instance :
    EssSurj F.toEssImage where mem_ess_image := fun ⟨Y, hY⟩ => ⟨_, ⟨⟨_, _, hY.getIso.hom_inv_id, hY.getIso.inv_hom_id⟩⟩⟩

variable (F) [EssSurj F]

/-- Given an essentially surjective functor, we can find a preimage for every object `Y` in the
    codomain. Applying the functor to this preimage will yield an object isomorphic to `Y`, see
    `obj_obj_preimage_iso`. -/
def Functor.objPreimage (Y : D) : C :=
  (EssSurj.mem_ess_image F Y).witness

/-- Applying an essentially surjective functor to a preimage of `Y` yields an object that is
    isomorphic to `Y`. -/
def Functor.objObjPreimageIso (Y : D) : F.obj (F.objPreimage Y) ≅ Y :=
  (EssSurj.mem_ess_image F Y).getIso

/-- The induced functor of a faithful functor is faithful -/
instance Faithful.to_ess_image (F : C ⥤ D) [Faithful F] : Faithful F.toEssImage :=
  Faithful.of_comp_iso F.toEssImageCompEssentialImageInclusion

/-- The induced functor of a full functor is full -/
instance Full.toEssImage (F : C ⥤ D) [Full F] : Full F.toEssImage := by
  have := full.of_iso F.to_ess_image_comp_essential_image_inclusion.symm
  exact full.of_comp_faithful F.to_ess_image F.ess_image_inclusion

end CategoryTheory

