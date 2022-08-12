/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.Logic.Small
import Mathbin.CategoryTheory.Skeletal

/-!
# Essentially small categories.

A category given by `(C : Type u) [category.{v} C]` is `w`-essentially small
if there exists a `small_model C : Type w` equipped with `[small_category (small_model C)]`.

A category is `w`-locally small if every hom type is `w`-small.

The main theorem here is that a category is `w`-essentially small iff
the type `skeleton C` is `w`-small, and `C` is `w`-locally small.
-/


universe w v v' u u'

open CategoryTheory

variable (C : Type u) [Category.{v} C]

namespace CategoryTheory

/-- A category is `essentially_small.{w}` if there exists
an equivalence to some `S : Type w` with `[small_category S]`. -/
class EssentiallySmall (C : Type u) [Category.{v} C] : Prop where
  equiv_small_category : ∃ (S : Type w)(_ : SmallCategory S), Nonempty (C ≌ S)

/-- Constructor for `essentially_small C` from an explicit small category witness. -/
theorem EssentiallySmall.mk' {C : Type u} [Category.{v} C] {S : Type w} [SmallCategory S] (e : C ≌ S) :
    EssentiallySmall.{w} C :=
  ⟨⟨S, _, ⟨e⟩⟩⟩

/-- An arbitrarily chosen small model for an essentially small category.
-/
@[nolint has_inhabited_instance]
def SmallModel (C : Type u) [Category.{v} C] [EssentiallySmall.{w} C] : Type w :=
  Classical.some (@EssentiallySmall.equiv_small_category C _ _)

noncomputable instance smallCategorySmallModel (C : Type u) [Category.{v} C] [EssentiallySmall.{w} C] :
    SmallCategory (SmallModel C) :=
  Classical.some (Classical.some_spec (@EssentiallySmall.equiv_small_category C _ _))

/-- The (noncomputable) categorical equivalence between
an essentially small category and its small model.
-/
noncomputable def equivSmallModel (C : Type u) [Category.{v} C] [EssentiallySmall.{w} C] : C ≌ SmallModel C :=
  Nonempty.some (Classical.some_spec (Classical.some_spec (@EssentiallySmall.equiv_small_category C _ _)))

theorem essentially_small_congr {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D] (e : C ≌ D) :
    EssentiallySmall.{w} C ↔ EssentiallySmall.{w} D := by
  fconstructor
  · rintro ⟨S, 𝒮, ⟨f⟩⟩
    skip
    exact essentially_small.mk' (e.symm.trans f)
    
  · rintro ⟨S, 𝒮, ⟨f⟩⟩
    skip
    exact essentially_small.mk' (e.trans f)
    

theorem Discrete.essentially_small_of_small {α : Type u} [Small.{w} α] : EssentiallySmall.{w} (Discrete α) :=
  ⟨⟨Discrete (Shrink α), ⟨inferInstance, ⟨Discrete.equivalence (equivShrink _)⟩⟩⟩⟩

/-- A category is `w`-locally small if every hom set is `w`-small.

See `shrink_homs C` for a category instance where every hom set has been replaced by a small model.
-/
class LocallySmall (C : Type u) [Category.{v} C] : Prop where
  hom_small : ∀ X Y : C, Small.{w} (X ⟶ Y) := by
    run_tac
      tactic.apply_instance

instance (C : Type u) [Category.{v} C] [LocallySmall.{w} C] (X Y : C) : Small (X ⟶ Y) :=
  LocallySmall.hom_small X Y

theorem locally_small_congr {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D] (e : C ≌ D) :
    LocallySmall.{w} C ↔ LocallySmall.{w} D := by
  fconstructor
  · rintro ⟨L⟩
    fconstructor
    intro X Y
    specialize L (e.inverse.obj X) (e.inverse.obj Y)
    refine' (small_congr _).mpr L
    exact equiv_of_fully_faithful e.inverse
    
  · rintro ⟨L⟩
    fconstructor
    intro X Y
    specialize L (e.functor.obj X) (e.functor.obj Y)
    refine' (small_congr _).mpr L
    exact equiv_of_fully_faithful e.functor
    

instance (priority := 100) locally_small_self (C : Type u) [Category.{v} C] : LocallySmall.{v} C where

instance (priority := 100) locally_small_of_essentially_small (C : Type u) [Category.{v} C] [EssentiallySmall.{w} C] :
    LocallySmall.{w} C :=
  (locally_small_congr (equivSmallModel C)).mpr (CategoryTheory.locally_small_self _)

/-- We define a type alias `shrink_homs C` for `C`. When we have `locally_small.{w} C`,
we'll put a `category.{w}` instance on `shrink_homs C`.
-/
@[nolint has_inhabited_instance]
def ShrinkHoms (C : Type u) :=
  C

namespace ShrinkHoms

section

variable {C' : Type _}

/-- Help the typechecker by explicitly translating from `C` to `shrink_homs C`. -/
-- a fresh variable with no category instance attached
def toShrinkHoms {C' : Type _} (X : C') : ShrinkHoms C' :=
  X

/-- Help the typechecker by explicitly translating from `shrink_homs C` to `C`. -/
def fromShrinkHoms {C' : Type _} (X : ShrinkHoms C') : C' :=
  X

@[simp]
theorem to_from (X : C') : fromShrinkHoms (toShrinkHoms X) = X :=
  rfl

@[simp]
theorem from_to (X : ShrinkHoms C') : toShrinkHoms (fromShrinkHoms X) = X :=
  rfl

end

variable (C) [LocallySmall.{w} C]

@[simps]
noncomputable instance : Category.{w} (ShrinkHoms C) where
  hom := fun X Y => Shrink (fromShrinkHoms X ⟶ fromShrinkHoms Y)
  id := fun X => equivShrink _ (𝟙 (fromShrinkHoms X))
  comp := fun X Y Z f g => equivShrink _ ((equivShrink _).symm f ≫ (equivShrink _).symm g)

/-- Implementation of `shrink_homs.equivalence`. -/
@[simps]
noncomputable def functor : C ⥤ ShrinkHoms C where
  obj := fun X => toShrinkHoms X
  map := fun X Y f => equivShrink (X ⟶ Y) f

/-- Implementation of `shrink_homs.equivalence`. -/
@[simps]
noncomputable def inverse : ShrinkHoms C ⥤ C where
  obj := fun X => fromShrinkHoms X
  map := fun X Y f => (equivShrink (fromShrinkHoms X ⟶ fromShrinkHoms Y)).symm f

/-- The categorical equivalence between `C` and `shrink_homs C`, when `C` is locally small.
-/
@[simps]
noncomputable def equivalence : C ≌ ShrinkHoms C :=
  Equivalence.mk (functor C) (inverse C)
    (NatIso.ofComponents (fun X => Iso.refl X)
      (by
        tidy))
    (NatIso.ofComponents (fun X => Iso.refl X)
      (by
        tidy))

end ShrinkHoms

/-- A category is essentially small if and only if
the underlying type of its skeleton (i.e. the "set" of isomorphism classes) is small,
and it is locally small.
-/
theorem essentially_small_iff (C : Type u) [Category.{v} C] :
    EssentiallySmall.{w} C ↔ Small.{w} (Skeleton C) ∧ LocallySmall.{w} C := by
  -- This theorem is the only bit of real work in this file.
  fconstructor
  · intro h
    fconstructor
    · rcases h with ⟨S, 𝒮, ⟨e⟩⟩
      skip
      refine' ⟨⟨skeleton S, ⟨_⟩⟩⟩
      exact e.skeleton_equiv
      
    · skip
      infer_instance
      
    
  · rintro ⟨⟨S, ⟨e⟩⟩, L⟩
    skip
    let e' := (shrink_homs.equivalence C).skeletonEquiv.symm
    refine' ⟨⟨S, _, ⟨_⟩⟩⟩
    apply induced_category.category (e'.trans e).symm
    refine'
      (shrink_homs.equivalence C).trans
        ((skeleton_equivalence _).symm.trans (induced_functor (e'.trans e).symm).asEquivalence.symm)
    

/-- Any thin category is locally small.
-/
instance (priority := 100) locally_small_of_thin {C : Type u} [Category.{v} C] [∀ X Y : C, Subsingleton (X ⟶ Y)] :
    LocallySmall.{w} C where

/-- A thin category is essentially small if and only if the underlying type of its skeleton is small.
-/
theorem essentially_small_iff_of_thin {C : Type u} [Category.{v} C] [∀ X Y : C, Subsingleton (X ⟶ Y)] :
    EssentiallySmall.{w} C ↔ Small.{w} (Skeleton C) := by
  simp [← essentially_small_iff, ← CategoryTheory.locally_small_of_thin]

end CategoryTheory

