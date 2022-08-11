/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.Algebra.Category.Group.Abelian
import Mathbin.CategoryTheory.Limits.Shapes.Images
import Mathbin.CategoryTheory.Limits.Types

/-!
# The category of commutative additive groups has images.

Note that we don't need to register any of the constructions here as instances, because we get them
from the fact that `AddCommGroup` is an abelian category.
-/


open CategoryTheory

open CategoryTheory.Limits

universe u

namespace AddCommGroupₓₓ

-- Note that because `injective_of_mono` is currently only proved in `Type 0`,
-- we restrict to the lowest universe here for now.
variable {G H : AddCommGroupₓₓ.{0}} (f : G ⟶ H)

attribute [local ext] Subtype.ext_val

section

/-- the image of a morphism in AddCommGroup is just the bundling of `add_monoid_hom.range f` -/
-- implementation details of `has_image` for AddCommGroup; use the API, not these
def image : AddCommGroupₓₓ :=
  AddCommGroupₓₓ.of (AddMonoidHom.range f)

/-- the inclusion of `image f` into the target -/
def image.ι : image f ⟶ H :=
  f.range.Subtype

instance : Mono (image.ι f) :=
  ConcreteCategory.mono_of_injective (image.ι f) Subtype.val_injective

/-- the corestriction map to the image -/
def factorThruImage : G ⟶ image f :=
  f.range_restrict

theorem image.fac : factorThruImage f ≫ image.ι f = f := by
  ext
  rfl

attribute [local simp] image.fac

variable {f}

/-- the universal property for the image factorisation -/
noncomputable def image.lift (F' : MonoFactorisation f) : image f ⟶ F'.i where
  toFun := (fun x => F'.e (Classical.indefiniteDescription _ x.2).1 : image f → F'.i)
  map_zero' := by
    have := F'.m_mono
    apply injective_of_mono F'.m
    change (F'.e ≫ F'.m) _ = _
    rw [F'.fac, AddMonoidHom.map_zero]
    exact (Classical.indefiniteDescription (fun y => f y = 0) _).2
  map_add' := by
    intro x y
    have := F'.m_mono
    apply injective_of_mono F'.m
    rw [AddMonoidHom.map_add]
    change (F'.e ≫ F'.m) _ = (F'.e ≫ F'.m) _ + (F'.e ≫ F'.m) _
    rw [F'.fac]
    rw [(Classical.indefiniteDescription (fun z => f z = _) _).2]
    rw [(Classical.indefiniteDescription (fun z => f z = _) _).2]
    rw [(Classical.indefiniteDescription (fun z => f z = _) _).2]
    rfl

theorem image.lift_fac (F' : MonoFactorisation f) : image.lift F' ≫ F'.m = image.ι f := by
  ext x
  change (F'.e ≫ F'.m) _ = _
  rw [F'.fac, (Classical.indefiniteDescription _ x.2).2]
  rfl

end

/-- the factorisation of any morphism in AddCommGroup through a mono. -/
def monoFactorisation : MonoFactorisation f where
  i := image f
  m := image.ι f
  e := factorThruImage f

/-- the factorisation of any morphism in AddCommGroup through a mono has the universal property of
the image. -/
noncomputable def isImage : IsImage (monoFactorisation f) where
  lift := image.lift
  lift_fac' := image.lift_fac

/-- The categorical image of a morphism in `AddCommGroup`
agrees with the usual group-theoretical range.
-/
noncomputable def imageIsoRange {G H : AddCommGroupₓₓ.{0}} (f : G ⟶ H) : Limits.image f ≅ AddCommGroupₓₓ.of f.range :=
  IsImage.isoExt (Image.isImage f) (isImage f)

end AddCommGroupₓₓ

