/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Markus Himmel, Bhavik Mehta, Andrew Yang
-/
import Mathbin.CategoryTheory.Limits.Shapes.WidePullbacks
import Mathbin.CategoryTheory.Limits.Shapes.BinaryProducts

/-!
# Pullbacks

We define a category `walking_cospan` (resp. `walking_span`), which is the index category
for the given data for a pullback (resp. pushout) diagram. Convenience methods `cospan f g`
and `span f g` construct functors from the walking (co)span, hitting the given morphisms.

We define `pullback f g` and `pushout f g` as limits and colimits of such functors.

## References
* [Stacks: Fibre products](https://stacks.math.columbia.edu/tag/001U)
* [Stacks: Pushouts](https://stacks.math.columbia.edu/tag/0025)
-/


noncomputable section

open CategoryTheory

namespace CategoryTheory.Limits

universe w v₁ v₂ v u u₂

attribute [local tidy] tactic.case_bash

/-- The type of objects for the diagram indexing a pullback, defined as a special case of
`wide_pullback_shape`.
-/
abbrev WalkingCospan : Type :=
  WidePullbackShape WalkingPair

/-- The left point of the walking cospan. -/
@[matchPattern]
abbrev WalkingCospan.left : WalkingCospan :=
  some WalkingPair.left

/-- The right point of the walking cospan. -/
@[matchPattern]
abbrev WalkingCospan.right : WalkingCospan :=
  some WalkingPair.right

/-- The central point of the walking cospan. -/
@[matchPattern]
abbrev WalkingCospan.one : WalkingCospan :=
  none

/-- The type of objects for the diagram indexing a pushout, defined as a special case of
`wide_pushout_shape`.
-/
abbrev WalkingSpan : Type :=
  WidePushoutShape WalkingPair

/-- The left point of the walking span. -/
@[matchPattern]
abbrev WalkingSpan.left : WalkingSpan :=
  some WalkingPair.left

/-- The right point of the walking span. -/
@[matchPattern]
abbrev WalkingSpan.right : WalkingSpan :=
  some WalkingPair.right

/-- The central point of the walking span. -/
@[matchPattern]
abbrev WalkingSpan.zero : WalkingSpan :=
  none

namespace WalkingCospan

/-- The type of arrows for the diagram indexing a pullback. -/
abbrev Hom : WalkingCospan → WalkingCospan → Type :=
  wide_pullback_shape.hom

/-- The left arrow of the walking cospan. -/
@[matchPattern]
abbrev Hom.inl : left ⟶ one :=
  WidePullbackShape.Hom.term _

/-- The right arrow of the walking cospan. -/
@[matchPattern]
abbrev Hom.inr : right ⟶ one :=
  WidePullbackShape.Hom.term _

/-- The identity arrows of the walking cospan. -/
@[matchPattern]
abbrev Hom.id (X : WalkingCospan) : X ⟶ X :=
  WidePullbackShape.Hom.id X

instance (X Y : WalkingCospan) : Subsingleton (X ⟶ Y) := by
  tidy

end WalkingCospan

namespace WalkingSpan

/-- The type of arrows for the diagram indexing a pushout. -/
abbrev Hom : WalkingSpan → WalkingSpan → Type :=
  wide_pushout_shape.hom

/-- The left arrow of the walking span. -/
@[matchPattern]
abbrev Hom.fst : zero ⟶ left :=
  WidePushoutShape.Hom.init _

/-- The right arrow of the walking span. -/
@[matchPattern]
abbrev Hom.snd : zero ⟶ right :=
  WidePushoutShape.Hom.init _

/-- The identity arrows of the walking span. -/
@[matchPattern]
abbrev Hom.id (X : WalkingSpan) : X ⟶ X :=
  WidePushoutShape.Hom.id X

instance (X Y : WalkingSpan) : Subsingleton (X ⟶ Y) := by
  tidy

end WalkingSpan

open WalkingSpan.Hom WalkingCospan.Hom WidePullbackShape.Hom WidePushoutShape.Hom

variable {C : Type u} [Category.{v} C]

/-- To construct an isomorphism of cones over the walking cospan,
it suffices to construct an isomorphism
of the cone points and check it commutes with the legs to `left` and `right`. -/
def WalkingCospan.ext {F : walking_cospan ⥤ C} {s t : Cone F} (i : s.x ≅ t.x)
    (w₁ : s.π.app WalkingCospan.left = i.Hom ≫ t.π.app WalkingCospan.left)
    (w₂ : s.π.app WalkingCospan.right = i.Hom ≫ t.π.app WalkingCospan.right) : s ≅ t := by
  apply cones.ext i
  rintro (⟨⟩ | ⟨⟨⟩⟩)
  · have h₁ := s.π.naturality walking_cospan.hom.inl
    dsimp'  at h₁
    simp only [← category.id_comp] at h₁
    have h₂ := t.π.naturality walking_cospan.hom.inl
    dsimp'  at h₂
    simp only [← category.id_comp] at h₂
    simp_rw [h₂, ← category.assoc, ← w₁, ← h₁]
    
  · exact w₁
    
  · exact w₂
    

/-- To construct an isomorphism of cocones over the walking span,
it suffices to construct an isomorphism
of the cocone points and check it commutes with the legs from `left` and `right`. -/
def WalkingSpan.ext {F : walking_span ⥤ C} {s t : Cocone F} (i : s.x ≅ t.x)
    (w₁ : s.ι.app WalkingCospan.left ≫ i.Hom = t.ι.app WalkingCospan.left)
    (w₂ : s.ι.app WalkingCospan.right ≫ i.Hom = t.ι.app WalkingCospan.right) : s ≅ t := by
  apply cocones.ext i
  rintro (⟨⟩ | ⟨⟨⟩⟩)
  · have h₁ := s.ι.naturality walking_span.hom.fst
    dsimp'  at h₁
    simp only [← category.comp_id] at h₁
    have h₂ := t.ι.naturality walking_span.hom.fst
    dsimp'  at h₂
    simp only [← category.comp_id] at h₂
    simp_rw [← h₁, category.assoc, w₁, h₂]
    
  · exact w₁
    
  · exact w₂
    

/-- `cospan f g` is the functor from the walking cospan hitting `f` and `g`. -/
def cospan {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) : walking_cospan ⥤ C :=
  WidePullbackShape.wideCospan Z (fun j => WalkingPair.casesOn j X Y) fun j => WalkingPair.casesOn j f g

/-- `span f g` is the functor from the walking span hitting `f` and `g`. -/
def span {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) : walking_span ⥤ C :=
  WidePushoutShape.wideSpan X (fun j => WalkingPair.casesOn j Y Z) fun j => WalkingPair.casesOn j f g

@[simp]
theorem cospan_left {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) : (cospan f g).obj WalkingCospan.left = X :=
  rfl

@[simp]
theorem span_left {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) : (span f g).obj WalkingSpan.left = Y :=
  rfl

@[simp]
theorem cospan_right {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) : (cospan f g).obj WalkingCospan.right = Y :=
  rfl

@[simp]
theorem span_right {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) : (span f g).obj WalkingSpan.right = Z :=
  rfl

@[simp]
theorem cospan_one {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) : (cospan f g).obj WalkingCospan.one = Z :=
  rfl

@[simp]
theorem span_zero {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) : (span f g).obj WalkingSpan.zero = X :=
  rfl

@[simp]
theorem cospan_map_inl {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) : (cospan f g).map WalkingCospan.Hom.inl = f :=
  rfl

@[simp]
theorem span_map_fst {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) : (span f g).map WalkingSpan.Hom.fst = f :=
  rfl

@[simp]
theorem cospan_map_inr {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) : (cospan f g).map WalkingCospan.Hom.inr = g :=
  rfl

@[simp]
theorem span_map_snd {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) : (span f g).map WalkingSpan.Hom.snd = g :=
  rfl

theorem cospan_map_id {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) (w : WalkingCospan) :
    (cospan f g).map (WalkingCospan.Hom.id w) = 𝟙 _ :=
  rfl

theorem span_map_id {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) (w : WalkingSpan) :
    (span f g).map (WalkingSpan.Hom.id w) = 𝟙 _ :=
  rfl

/-- Every diagram indexing an pullback is naturally isomorphic (actually, equal) to a `cospan` -/
@[simps (config := { rhsMd := semireducible })]
def diagramIsoCospan (F : walking_cospan ⥤ C) : F ≅ cospan (F.map inl) (F.map inr) :=
  NatIso.ofComponents
    (fun j =>
      eqToIso
        (by
          tidy))
    (by
      tidy)

/-- Every diagram indexing a pushout is naturally isomorphic (actually, equal) to a `span` -/
@[simps (config := { rhsMd := semireducible })]
def diagramIsoSpan (F : walking_span ⥤ C) : F ≅ span (F.map fst) (F.map snd) :=
  NatIso.ofComponents
    (fun j =>
      eqToIso
        (by
          tidy))
    (by
      tidy)

variable {D : Type u₂} [Category.{v₂} D]

/-- A functor applied to a cospan is a cospan. -/
def cospanCompIso (F : C ⥤ D) {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) : cospan f g ⋙ F ≅ cospan (F.map f) (F.map g) :=
  NatIso.ofComponents
    (by
      rintro (⟨⟩ | ⟨⟨⟩⟩) <;> exact iso.refl _)
    (by
      rintro (⟨⟩ | ⟨⟨⟩⟩) (⟨⟩ | ⟨⟨⟩⟩) ⟨⟩ <;>
        repeat'
          dsimp'
          simp )

section

variable (F : C ⥤ D) {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)

@[simp]
theorem cospan_comp_iso_app_left : (cospanCompIso F f g).app WalkingCospan.left = Iso.refl _ :=
  rfl

@[simp]
theorem cospan_comp_iso_app_right : (cospanCompIso F f g).app WalkingCospan.right = Iso.refl _ :=
  rfl

@[simp]
theorem cospan_comp_iso_app_one : (cospanCompIso F f g).app WalkingCospan.one = Iso.refl _ :=
  rfl

@[simp]
theorem cospan_comp_iso_hom_app_left : (cospanCompIso F f g).Hom.app WalkingCospan.left = 𝟙 _ :=
  rfl

@[simp]
theorem cospan_comp_iso_hom_app_right : (cospanCompIso F f g).Hom.app WalkingCospan.right = 𝟙 _ :=
  rfl

@[simp]
theorem cospan_comp_iso_hom_app_one : (cospanCompIso F f g).Hom.app WalkingCospan.one = 𝟙 _ :=
  rfl

@[simp]
theorem cospan_comp_iso_inv_app_left : (cospanCompIso F f g).inv.app WalkingCospan.left = 𝟙 _ :=
  rfl

@[simp]
theorem cospan_comp_iso_inv_app_right : (cospanCompIso F f g).inv.app WalkingCospan.right = 𝟙 _ :=
  rfl

@[simp]
theorem cospan_comp_iso_inv_app_one : (cospanCompIso F f g).inv.app WalkingCospan.one = 𝟙 _ :=
  rfl

end

/-- A functor applied to a span is a span. -/
def spanCompIso (F : C ⥤ D) {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) : span f g ⋙ F ≅ span (F.map f) (F.map g) :=
  NatIso.ofComponents
    (by
      rintro (⟨⟩ | ⟨⟨⟩⟩) <;> exact iso.refl _)
    (by
      rintro (⟨⟩ | ⟨⟨⟩⟩) (⟨⟩ | ⟨⟨⟩⟩) ⟨⟩ <;>
        repeat'
          dsimp'
          simp )

section

variable (F : C ⥤ D) {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z)

@[simp]
theorem span_comp_iso_app_left : (spanCompIso F f g).app WalkingSpan.left = Iso.refl _ :=
  rfl

@[simp]
theorem span_comp_iso_app_right : (spanCompIso F f g).app WalkingSpan.right = Iso.refl _ :=
  rfl

@[simp]
theorem span_comp_iso_app_zero : (spanCompIso F f g).app WalkingSpan.zero = Iso.refl _ :=
  rfl

@[simp]
theorem span_comp_iso_hom_app_left : (spanCompIso F f g).Hom.app WalkingSpan.left = 𝟙 _ :=
  rfl

@[simp]
theorem span_comp_iso_hom_app_right : (spanCompIso F f g).Hom.app WalkingSpan.right = 𝟙 _ :=
  rfl

@[simp]
theorem span_comp_iso_hom_app_zero : (spanCompIso F f g).Hom.app WalkingSpan.zero = 𝟙 _ :=
  rfl

@[simp]
theorem span_comp_iso_inv_app_left : (spanCompIso F f g).inv.app WalkingSpan.left = 𝟙 _ :=
  rfl

@[simp]
theorem span_comp_iso_inv_app_right : (spanCompIso F f g).inv.app WalkingSpan.right = 𝟙 _ :=
  rfl

@[simp]
theorem span_comp_iso_inv_app_zero : (spanCompIso F f g).inv.app WalkingSpan.zero = 𝟙 _ :=
  rfl

end

section

variable {X Y Z X' Y' Z' : C} (iX : X ≅ X') (iY : Y ≅ Y') (iZ : Z ≅ Z')

section

variable {f : X ⟶ Z} {g : Y ⟶ Z} {f' : X' ⟶ Z'} {g' : Y' ⟶ Z'}

/-- Construct an isomorphism of cospans from components. -/
def cospanExt (wf : iX.Hom ≫ f' = f ≫ iZ.Hom) (wg : iY.Hom ≫ g' = g ≫ iZ.Hom) : cospan f g ≅ cospan f' g' :=
  NatIso.ofComponents
    (by
      rintro (⟨⟩ | ⟨⟨⟩⟩)
      exacts[iZ, iX, iY])
    (by
      rintro (⟨⟩ | ⟨⟨⟩⟩) (⟨⟩ | ⟨⟨⟩⟩) ⟨⟩ <;>
        repeat'
          dsimp'
          simp [← wf, ← wg])

variable (wf : iX.Hom ≫ f' = f ≫ iZ.Hom) (wg : iY.Hom ≫ g' = g ≫ iZ.Hom)

@[simp]
theorem cospan_ext_app_left : (cospanExt iX iY iZ wf wg).app WalkingCospan.left = iX := by
  dsimp' [← cospan_ext]
  simp

@[simp]
theorem cospan_ext_app_right : (cospanExt iX iY iZ wf wg).app WalkingCospan.right = iY := by
  dsimp' [← cospan_ext]
  simp

@[simp]
theorem cospan_ext_app_one : (cospanExt iX iY iZ wf wg).app WalkingCospan.one = iZ := by
  dsimp' [← cospan_ext]
  simp

@[simp]
theorem cospan_ext_hom_app_left : (cospanExt iX iY iZ wf wg).Hom.app WalkingCospan.left = iX.Hom := by
  dsimp' [← cospan_ext]
  simp

@[simp]
theorem cospan_ext_hom_app_right : (cospanExt iX iY iZ wf wg).Hom.app WalkingCospan.right = iY.Hom := by
  dsimp' [← cospan_ext]
  simp

@[simp]
theorem cospan_ext_hom_app_one : (cospanExt iX iY iZ wf wg).Hom.app WalkingCospan.one = iZ.Hom := by
  dsimp' [← cospan_ext]
  simp

@[simp]
theorem cospan_ext_inv_app_left : (cospanExt iX iY iZ wf wg).inv.app WalkingCospan.left = iX.inv := by
  dsimp' [← cospan_ext]
  simp

@[simp]
theorem cospan_ext_inv_app_right : (cospanExt iX iY iZ wf wg).inv.app WalkingCospan.right = iY.inv := by
  dsimp' [← cospan_ext]
  simp

@[simp]
theorem cospan_ext_inv_app_one : (cospanExt iX iY iZ wf wg).inv.app WalkingCospan.one = iZ.inv := by
  dsimp' [← cospan_ext]
  simp

end

section

variable {f : X ⟶ Y} {g : X ⟶ Z} {f' : X' ⟶ Y'} {g' : X' ⟶ Z'}

/-- Construct an isomorphism of spans from components. -/
def spanExt (wf : iX.Hom ≫ f' = f ≫ iY.Hom) (wg : iX.Hom ≫ g' = g ≫ iZ.Hom) : span f g ≅ span f' g' :=
  NatIso.ofComponents
    (by
      rintro (⟨⟩ | ⟨⟨⟩⟩)
      exacts[iX, iY, iZ])
    (by
      rintro (⟨⟩ | ⟨⟨⟩⟩) (⟨⟩ | ⟨⟨⟩⟩) ⟨⟩ <;>
        repeat'
          dsimp'
          simp [← wf, ← wg])

variable (wf : iX.Hom ≫ f' = f ≫ iY.Hom) (wg : iX.Hom ≫ g' = g ≫ iZ.Hom)

@[simp]
theorem span_ext_app_left : (spanExt iX iY iZ wf wg).app WalkingSpan.left = iY := by
  dsimp' [← span_ext]
  simp

@[simp]
theorem span_ext_app_right : (spanExt iX iY iZ wf wg).app WalkingSpan.right = iZ := by
  dsimp' [← span_ext]
  simp

@[simp]
theorem span_ext_app_one : (spanExt iX iY iZ wf wg).app WalkingSpan.zero = iX := by
  dsimp' [← span_ext]
  simp

@[simp]
theorem span_ext_hom_app_left : (spanExt iX iY iZ wf wg).Hom.app WalkingSpan.left = iY.Hom := by
  dsimp' [← span_ext]
  simp

@[simp]
theorem span_ext_hom_app_right : (spanExt iX iY iZ wf wg).Hom.app WalkingSpan.right = iZ.Hom := by
  dsimp' [← span_ext]
  simp

@[simp]
theorem span_ext_hom_app_zero : (spanExt iX iY iZ wf wg).Hom.app WalkingSpan.zero = iX.Hom := by
  dsimp' [← span_ext]
  simp

@[simp]
theorem span_ext_inv_app_left : (spanExt iX iY iZ wf wg).inv.app WalkingSpan.left = iY.inv := by
  dsimp' [← span_ext]
  simp

@[simp]
theorem span_ext_inv_app_right : (spanExt iX iY iZ wf wg).inv.app WalkingSpan.right = iZ.inv := by
  dsimp' [← span_ext]
  simp

@[simp]
theorem span_ext_inv_app_zero : (spanExt iX iY iZ wf wg).inv.app WalkingSpan.zero = iX.inv := by
  dsimp' [← span_ext]
  simp

end

end

variable {W X Y Z : C}

/-- A pullback cone is just a cone on the cospan formed by two morphisms `f : X ⟶ Z` and
    `g : Y ⟶ Z`.-/
abbrev PullbackCone (f : X ⟶ Z) (g : Y ⟶ Z) :=
  Cone (cospan f g)

namespace PullbackCone

variable {f : X ⟶ Z} {g : Y ⟶ Z}

/-- The first projection of a pullback cone. -/
abbrev fst (t : PullbackCone f g) : t.x ⟶ X :=
  t.π.app WalkingCospan.left

/-- The second projection of a pullback cone. -/
abbrev snd (t : PullbackCone f g) : t.x ⟶ Y :=
  t.π.app WalkingCospan.right

@[simp]
theorem condition_one (t : PullbackCone f g) : t.π.app WalkingCospan.one = t.fst ≫ f := by
  have w := t.π.naturality walking_cospan.hom.inl
  dsimp'  at w
  simpa using w

/-- This is a slightly more convenient method to verify that a pullback cone is a limit cone. It
    only asks for a proof of facts that carry any mathematical content -/
def isLimitAux (t : PullbackCone f g) (lift : ∀ s : PullbackCone f g, s.x ⟶ t.x)
    (fac_left : ∀ s : PullbackCone f g, lift s ≫ t.fst = s.fst)
    (fac_right : ∀ s : PullbackCone f g, lift s ≫ t.snd = s.snd)
    (uniq : ∀ (s : PullbackCone f g) (m : s.x ⟶ t.x) (w : ∀ j : WalkingCospan, m ≫ t.π.app j = s.π.app j), m = lift s) :
    IsLimit t :=
  { lift,
    fac' := fun s j =>
      Option.casesOn j
        (by
          rw [← s.w inl, ← t.w inl, ← category.assoc]
          congr
          exact fac_left s)
        fun j' => WalkingPair.casesOn j' (fac_left s) (fac_right s),
    uniq' := uniq }

/-- This is another convenient method to verify that a pullback cone is a limit cone. It
    only asks for a proof of facts that carry any mathematical content, and allows access to the
    same `s` for all parts. -/
def isLimitAux' (t : PullbackCone f g)
    (create :
      ∀ s : PullbackCone f g,
        { l // l ≫ t.fst = s.fst ∧ l ≫ t.snd = s.snd ∧ ∀ {m}, m ≫ t.fst = s.fst → m ≫ t.snd = s.snd → m = l }) :
    Limits.IsLimit t :=
  PullbackCone.isLimitAux t (fun s => (create s).1) (fun s => (create s).2.1) (fun s => (create s).2.2.1) fun s m w =>
    (create s).2.2.2 (w WalkingCospan.left) (w WalkingCospan.right)

/-- A pullback cone on `f` and `g` is determined by morphisms `fst : W ⟶ X` and `snd : W ⟶ Y`
    such that `fst ≫ f = snd ≫ g`. -/
@[simps]
def mk {W : C} (fst : W ⟶ X) (snd : W ⟶ Y) (eq : fst ≫ f = snd ≫ g) : PullbackCone f g where
  x := W
  π := { app := fun j => Option.casesOn j (fst ≫ f) fun j' => WalkingPair.casesOn j' fst snd }

@[simp]
theorem mk_π_app_left {W : C} (fst : W ⟶ X) (snd : W ⟶ Y) (eq : fst ≫ f = snd ≫ g) :
    (mk fst snd Eq).π.app WalkingCospan.left = fst :=
  rfl

@[simp]
theorem mk_π_app_right {W : C} (fst : W ⟶ X) (snd : W ⟶ Y) (eq : fst ≫ f = snd ≫ g) :
    (mk fst snd Eq).π.app WalkingCospan.right = snd :=
  rfl

@[simp]
theorem mk_π_app_one {W : C} (fst : W ⟶ X) (snd : W ⟶ Y) (eq : fst ≫ f = snd ≫ g) :
    (mk fst snd Eq).π.app WalkingCospan.one = fst ≫ f :=
  rfl

@[simp]
theorem mk_fst {W : C} (fst : W ⟶ X) (snd : W ⟶ Y) (eq : fst ≫ f = snd ≫ g) : (mk fst snd Eq).fst = fst :=
  rfl

@[simp]
theorem mk_snd {W : C} (fst : W ⟶ X) (snd : W ⟶ Y) (eq : fst ≫ f = snd ≫ g) : (mk fst snd Eq).snd = snd :=
  rfl

@[reassoc]
theorem condition (t : PullbackCone f g) : fst t ≫ f = snd t ≫ g :=
  (t.w inl).trans (t.w inr).symm

/-- To check whether a morphism is equalized by the maps of a pullback cone, it suffices to check
  it for `fst t` and `snd t` -/
theorem equalizer_ext (t : PullbackCone f g) {W : C} {k l : W ⟶ t.x} (h₀ : k ≫ fst t = l ≫ fst t)
    (h₁ : k ≫ snd t = l ≫ snd t) : ∀ j : WalkingCospan, k ≫ t.π.app j = l ≫ t.π.app j
  | some walking_pair.left => h₀
  | some walking_pair.right => h₁
  | none => by
    rw [← t.w inl, reassoc_of h₀]

theorem IsLimit.hom_ext {t : PullbackCone f g} (ht : IsLimit t) {W : C} {k l : W ⟶ t.x} (h₀ : k ≫ fst t = l ≫ fst t)
    (h₁ : k ≫ snd t = l ≫ snd t) : k = l :=
  ht.hom_ext <| equalizer_ext _ h₀ h₁

theorem mono_snd_of_is_pullback_of_mono {t : PullbackCone f g} (ht : IsLimit t) [Mono f] : Mono t.snd :=
  ⟨fun W h k i =>
    IsLimit.hom_ext ht
      (by
        simp [cancel_mono f, ← t.condition, ← reassoc_of i])
      i⟩

theorem mono_fst_of_is_pullback_of_mono {t : PullbackCone f g} (ht : IsLimit t) [Mono g] : Mono t.fst :=
  ⟨fun W h k i =>
    IsLimit.hom_ext ht i
      (by
        simp [cancel_mono g, t.condition, ← reassoc_of i])⟩

/-- To construct an isomorphism of pullback cones, it suffices to construct an isomorphism
of the cone points and check it commutes with `fst` and `snd`. -/
def ext {s t : PullbackCone f g} (i : s.x ≅ t.x) (w₁ : s.fst = i.Hom ≫ t.fst) (w₂ : s.snd = i.Hom ≫ t.snd) : s ≅ t :=
  WalkingCospan.ext i w₁ w₂

/-- If `t` is a limit pullback cone over `f` and `g` and `h : W ⟶ X` and `k : W ⟶ Y` are such that
    `h ≫ f = k ≫ g`, then we have `l : W ⟶ t.X` satisfying `l ≫ fst t = h` and `l ≫ snd t = k`.
    -/
def IsLimit.lift' {t : PullbackCone f g} (ht : IsLimit t) {W : C} (h : W ⟶ X) (k : W ⟶ Y) (w : h ≫ f = k ≫ g) :
    { l : W ⟶ t.x // l ≫ fst t = h ∧ l ≫ snd t = k } :=
  ⟨ht.lift <| PullbackCone.mk _ _ w, ht.fac _ _, ht.fac _ _⟩

/-- This is a more convenient formulation to show that a `pullback_cone` constructed using
`pullback_cone.mk` is a limit cone.
-/
def IsLimit.mk {W : C} {fst : W ⟶ X} {snd : W ⟶ Y} (eq : fst ≫ f = snd ≫ g) (lift : ∀ s : PullbackCone f g, s.x ⟶ W)
    (fac_left : ∀ s : PullbackCone f g, lift s ≫ fst = s.fst) (fac_right : ∀ s : PullbackCone f g, lift s ≫ snd = s.snd)
    (uniq : ∀ (s : PullbackCone f g) (m : s.x ⟶ W) (w_fst : m ≫ fst = s.fst) (w_snd : m ≫ snd = s.snd), m = lift s) :
    IsLimit (mk fst snd Eq) :=
  isLimitAux _ lift fac_left fac_right fun s m w => uniq s m (w WalkingCospan.left) (w WalkingCospan.right)

/-- The flip of a pullback square is a pullback square. -/
def flipIsLimit {W : C} {h : W ⟶ X} {k : W ⟶ Y} {comm : h ≫ f = k ≫ g} (t : IsLimit (mk _ _ comm.symm)) :
    IsLimit (mk _ _ comm) :=
  (isLimitAux' _) fun s => by
    refine'
      ⟨(is_limit.lift' t _ _ s.condition.symm).1, (is_limit.lift' t _ _ _).2.2, (is_limit.lift' t _ _ _).2.1,
        fun m m₁ m₂ => t.hom_ext _⟩
    apply (mk k h _).equalizer_ext
    · rwa [(is_limit.lift' t _ _ _).2.1]
      
    · rwa [(is_limit.lift' t _ _ _).2.2]
      

/-- The pullback cone `(𝟙 X, 𝟙 X)` for the pair `(f, f)` is a limit if `f` is a mono. The converse is
shown in `mono_of_pullback_is_id`.
-/
def isLimitMkIdId (f : X ⟶ Y) [Mono f] : IsLimit (mk (𝟙 X) (𝟙 X) rfl : PullbackCone f f) :=
  IsLimit.mk _ (fun s => s.fst) (fun s => Category.comp_id _)
    (fun s => by
      rw [← cancel_mono f, category.comp_id, s.condition])
    fun s m m₁ m₂ => by
    simpa using m₁

/-- `f` is a mono if the pullback cone `(𝟙 X, 𝟙 X)` is a limit for the pair `(f, f)`. The converse is
given in `pullback_cone.is_id_of_mono`.
-/
theorem mono_of_is_limit_mk_id_id (f : X ⟶ Y) (t : IsLimit (mk (𝟙 X) (𝟙 X) rfl : PullbackCone f f)) : Mono f :=
  ⟨fun Z g h eq => by
    rcases pullback_cone.is_limit.lift' t _ _ Eq with ⟨_, rfl, rfl⟩
    rfl⟩

/-- Suppose `f` and `g` are two morphisms with a common codomain and `s` is a limit cone over the
    diagram formed by `f` and `g`. Suppose `f` and `g` both factor through a monomorphism `h` via
    `x` and `y`, respectively.  Then `s` is also a limit cone over the diagram formed by `x` and
    `y`.  -/
def isLimitOfFactors (f : X ⟶ Z) (g : Y ⟶ Z) (h : W ⟶ Z) [Mono h] (x : X ⟶ W) (y : Y ⟶ W) (hxh : x ≫ h = f)
    (hyh : y ≫ h = g) (s : PullbackCone f g) (hs : IsLimit s) :
    IsLimit
      (PullbackCone.mk _ _
        (show s.fst ≫ x = s.snd ≫ y from
          (cancel_mono h).1 <| by
            simp only [← category.assoc, ← hxh, ← hyh, ← s.condition])) :=
  (PullbackCone.isLimitAux' _) fun t =>
    ⟨hs.lift
        (PullbackCone.mk t.fst t.snd <| by
          rw [← hxh, ← hyh, reassoc_of t.condition]),
      ⟨hs.fac _ WalkingCospan.left, hs.fac _ WalkingCospan.right, fun r hr hr' => by
        apply pullback_cone.is_limit.hom_ext hs <;>
          simp only [← pullback_cone.mk_fst, ← pullback_cone.mk_snd] at hr hr'⊢ <;> simp only [← hr, ← hr'] <;> symm
        exacts[hs.fac _ walking_cospan.left, hs.fac _ walking_cospan.right]⟩⟩

/-- If `W` is the pullback of `f, g`,
it is also the pullback of `f ≫ i, g ≫ i` for any mono `i`. -/
def isLimitOfCompMono (f : X ⟶ W) (g : Y ⟶ W) (i : W ⟶ Z) [Mono i] (s : PullbackCone f g) (H : IsLimit s) :
    IsLimit
      (PullbackCone.mk _ _
        (show s.fst ≫ f ≫ i = s.snd ≫ g ≫ i by
          rw [← category.assoc, ← category.assoc, s.condition])) :=
  by
  apply pullback_cone.is_limit_aux'
  intro s
  rcases pullback_cone.is_limit.lift' H s.fst s.snd
      ((cancel_mono i).mp
        (by
          simpa using s.condition)) with
    ⟨l, h₁, h₂⟩
  refine' ⟨l, h₁, h₂, _⟩
  intro m hm₁ hm₂
  exact (pullback_cone.is_limit.hom_ext H (hm₁.trans h₁.symm) (hm₂.trans h₂.symm) : _)

end PullbackCone

/-- A pushout cocone is just a cocone on the span formed by two morphisms `f : X ⟶ Y` and
    `g : X ⟶ Z`.-/
abbrev PushoutCocone (f : X ⟶ Y) (g : X ⟶ Z) :=
  Cocone (span f g)

namespace PushoutCocone

variable {f : X ⟶ Y} {g : X ⟶ Z}

/-- The first inclusion of a pushout cocone. -/
abbrev inl (t : PushoutCocone f g) : Y ⟶ t.x :=
  t.ι.app WalkingSpan.left

/-- The second inclusion of a pushout cocone. -/
abbrev inr (t : PushoutCocone f g) : Z ⟶ t.x :=
  t.ι.app WalkingSpan.right

@[simp]
theorem condition_zero (t : PushoutCocone f g) : t.ι.app WalkingSpan.zero = f ≫ t.inl := by
  have w := t.ι.naturality walking_span.hom.fst
  dsimp'  at w
  simpa using w.symm

/-- This is a slightly more convenient method to verify that a pushout cocone is a colimit cocone.
    It only asks for a proof of facts that carry any mathematical content -/
def isColimitAux (t : PushoutCocone f g) (desc : ∀ s : PushoutCocone f g, t.x ⟶ s.x)
    (fac_left : ∀ s : PushoutCocone f g, t.inl ≫ desc s = s.inl)
    (fac_right : ∀ s : PushoutCocone f g, t.inr ≫ desc s = s.inr)
    (uniq : ∀ (s : PushoutCocone f g) (m : t.x ⟶ s.x) (w : ∀ j : WalkingSpan, t.ι.app j ≫ m = s.ι.app j), m = desc s) :
    IsColimit t :=
  { desc,
    fac' := fun s j =>
      Option.casesOn j
        (by
          simp [s.w fst, t.w fst, ← fac_left s])
        fun j' => WalkingPair.casesOn j' (fac_left s) (fac_right s),
    uniq' := uniq }

/-- This is another convenient method to verify that a pushout cocone is a colimit cocone. It
    only asks for a proof of facts that carry any mathematical content, and allows access to the
    same `s` for all parts. -/
def isColimitAux' (t : PushoutCocone f g)
    (create :
      ∀ s : PushoutCocone f g,
        { l // t.inl ≫ l = s.inl ∧ t.inr ≫ l = s.inr ∧ ∀ {m}, t.inl ≫ m = s.inl → t.inr ≫ m = s.inr → m = l }) :
    IsColimit t :=
  isColimitAux t (fun s => (create s).1) (fun s => (create s).2.1) (fun s => (create s).2.2.1) fun s m w =>
    (create s).2.2.2 (w WalkingCospan.left) (w WalkingCospan.right)

/-- A pushout cocone on `f` and `g` is determined by morphisms `inl : Y ⟶ W` and `inr : Z ⟶ W` such
    that `f ≫ inl = g ↠ inr`. -/
@[simps]
def mk {W : C} (inl : Y ⟶ W) (inr : Z ⟶ W) (eq : f ≫ inl = g ≫ inr) : PushoutCocone f g where
  x := W
  ι := { app := fun j => Option.casesOn j (f ≫ inl) fun j' => WalkingPair.casesOn j' inl inr }

@[simp]
theorem mk_ι_app_left {W : C} (inl : Y ⟶ W) (inr : Z ⟶ W) (eq : f ≫ inl = g ≫ inr) :
    (mk inl inr Eq).ι.app WalkingSpan.left = inl :=
  rfl

@[simp]
theorem mk_ι_app_right {W : C} (inl : Y ⟶ W) (inr : Z ⟶ W) (eq : f ≫ inl = g ≫ inr) :
    (mk inl inr Eq).ι.app WalkingSpan.right = inr :=
  rfl

@[simp]
theorem mk_ι_app_zero {W : C} (inl : Y ⟶ W) (inr : Z ⟶ W) (eq : f ≫ inl = g ≫ inr) :
    (mk inl inr Eq).ι.app WalkingSpan.zero = f ≫ inl :=
  rfl

@[simp]
theorem mk_inl {W : C} (inl : Y ⟶ W) (inr : Z ⟶ W) (eq : f ≫ inl = g ≫ inr) : (mk inl inr Eq).inl = inl :=
  rfl

@[simp]
theorem mk_inr {W : C} (inl : Y ⟶ W) (inr : Z ⟶ W) (eq : f ≫ inl = g ≫ inr) : (mk inl inr Eq).inr = inr :=
  rfl

@[reassoc]
theorem condition (t : PushoutCocone f g) : f ≫ inl t = g ≫ inr t :=
  (t.w fst).trans (t.w snd).symm

/-- To check whether a morphism is coequalized by the maps of a pushout cocone, it suffices to check
  it for `inl t` and `inr t` -/
theorem coequalizer_ext (t : PushoutCocone f g) {W : C} {k l : t.x ⟶ W} (h₀ : inl t ≫ k = inl t ≫ l)
    (h₁ : inr t ≫ k = inr t ≫ l) : ∀ j : WalkingSpan, t.ι.app j ≫ k = t.ι.app j ≫ l
  | some walking_pair.left => h₀
  | some walking_pair.right => h₁
  | none => by
    rw [← t.w fst, category.assoc, category.assoc, h₀]

theorem IsColimit.hom_ext {t : PushoutCocone f g} (ht : IsColimit t) {W : C} {k l : t.x ⟶ W}
    (h₀ : inl t ≫ k = inl t ≫ l) (h₁ : inr t ≫ k = inr t ≫ l) : k = l :=
  ht.hom_ext <| coequalizer_ext _ h₀ h₁

/-- If `t` is a colimit pushout cocone over `f` and `g` and `h : Y ⟶ W` and `k : Z ⟶ W` are
    morphisms satisfying `f ≫ h = g ≫ k`, then we have a factorization `l : t.X ⟶ W` such that
    `inl t ≫ l = h` and `inr t ≫ l = k`. -/
def IsColimit.desc' {t : PushoutCocone f g} (ht : IsColimit t) {W : C} (h : Y ⟶ W) (k : Z ⟶ W) (w : f ≫ h = g ≫ k) :
    { l : t.x ⟶ W // inl t ≫ l = h ∧ inr t ≫ l = k } :=
  ⟨ht.desc <| PushoutCocone.mk _ _ w, ht.fac _ _, ht.fac _ _⟩

theorem epi_inr_of_is_pushout_of_epi {t : PushoutCocone f g} (ht : IsColimit t) [Epi f] : Epi t.inr :=
  ⟨fun W h k i =>
    IsColimit.hom_ext ht
      (by
        simp [cancel_epi f, ← t.condition_assoc, ← i])
      i⟩

theorem epi_inl_of_is_pushout_of_epi {t : PushoutCocone f g} (ht : IsColimit t) [Epi g] : Epi t.inl :=
  ⟨fun W h k i =>
    IsColimit.hom_ext ht i
      (by
        simp [cancel_epi g, t.condition_assoc, ← i])⟩

/-- To construct an isomorphism of pushout cocones, it suffices to construct an isomorphism
of the cocone points and check it commutes with `inl` and `inr`. -/
def ext {s t : PushoutCocone f g} (i : s.x ≅ t.x) (w₁ : s.inl ≫ i.Hom = t.inl) (w₂ : s.inr ≫ i.Hom = t.inr) : s ≅ t :=
  WalkingSpan.ext i w₁ w₂

/-- This is a more convenient formulation to show that a `pushout_cocone` constructed using
`pushout_cocone.mk` is a colimit cocone.
-/
def IsColimit.mk {W : C} {inl : Y ⟶ W} {inr : Z ⟶ W} (eq : f ≫ inl = g ≫ inr) (desc : ∀ s : PushoutCocone f g, W ⟶ s.x)
    (fac_left : ∀ s : PushoutCocone f g, inl ≫ desc s = s.inl)
    (fac_right : ∀ s : PushoutCocone f g, inr ≫ desc s = s.inr)
    (uniq : ∀ (s : PushoutCocone f g) (m : W ⟶ s.x) (w_inl : inl ≫ m = s.inl) (w_inr : inr ≫ m = s.inr), m = desc s) :
    IsColimit (mk inl inr Eq) :=
  isColimitAux _ desc fac_left fac_right fun s m w => uniq s m (w WalkingCospan.left) (w WalkingCospan.right)

/-- The flip of a pushout square is a pushout square. -/
def flipIsColimit {W : C} {h : Y ⟶ W} {k : Z ⟶ W} {comm : f ≫ h = g ≫ k} (t : IsColimit (mk _ _ comm.symm)) :
    IsColimit (mk _ _ comm) :=
  (isColimitAux' _) fun s => by
    refine'
      ⟨(is_colimit.desc' t _ _ s.condition.symm).1, (is_colimit.desc' t _ _ _).2.2, (is_colimit.desc' t _ _ _).2.1,
        fun m m₁ m₂ => t.hom_ext _⟩
    apply (mk k h _).coequalizer_ext
    · rwa [(is_colimit.desc' t _ _ _).2.1]
      
    · rwa [(is_colimit.desc' t _ _ _).2.2]
      

/-- The pushout cocone `(𝟙 X, 𝟙 X)` for the pair `(f, f)` is a colimit if `f` is an epi. The converse is
shown in `epi_of_is_colimit_mk_id_id`.
-/
def isColimitMkIdId (f : X ⟶ Y) [Epi f] : IsColimit (mk (𝟙 Y) (𝟙 Y) rfl : PushoutCocone f f) :=
  IsColimit.mk _ (fun s => s.inl) (fun s => Category.id_comp _)
    (fun s => by
      rw [← cancel_epi f, category.id_comp, s.condition])
    fun s m m₁ m₂ => by
    simpa using m₁

/-- `f` is an epi if the pushout cocone `(𝟙 X, 𝟙 X)` is a colimit for the pair `(f, f)`.
The converse is given in `pushout_cocone.is_colimit_mk_id_id`.
-/
theorem epi_of_is_colimit_mk_id_id (f : X ⟶ Y) (t : IsColimit (mk (𝟙 Y) (𝟙 Y) rfl : PushoutCocone f f)) : Epi f :=
  ⟨fun Z g h eq => by
    rcases pushout_cocone.is_colimit.desc' t _ _ Eq with ⟨_, rfl, rfl⟩
    rfl⟩

/-- Suppose `f` and `g` are two morphisms with a common domain and `s` is a colimit cocone over the
    diagram formed by `f` and `g`. Suppose `f` and `g` both factor through an epimorphism `h` via
    `x` and `y`, respectively. Then `s` is also a colimit cocone over the diagram formed by `x` and
    `y`.  -/
def isColimitOfFactors (f : X ⟶ Y) (g : X ⟶ Z) (h : X ⟶ W) [Epi h] (x : W ⟶ Y) (y : W ⟶ Z) (hhx : h ≫ x = f)
    (hhy : h ≫ y = g) (s : PushoutCocone f g) (hs : IsColimit s) :
    IsColimit
      (PushoutCocone.mk _ _
        (show x ≫ s.inl = y ≫ s.inr from
          (cancel_epi h).1 <| by
            rw [reassoc_of hhx, reassoc_of hhy, s.condition])) :=
  (PushoutCocone.isColimitAux' _) fun t =>
    ⟨hs.desc
        (PushoutCocone.mk t.inl t.inr <| by
          rw [← hhx, ← hhy, category.assoc, category.assoc, t.condition]),
      ⟨hs.fac _ WalkingSpan.left, hs.fac _ WalkingSpan.right, fun r hr hr' => by
        apply pushout_cocone.is_colimit.hom_ext hs <;>
          simp only [← pushout_cocone.mk_inl, ← pushout_cocone.mk_inr] at hr hr'⊢ <;> simp only [← hr, ← hr'] <;> symm
        exacts[hs.fac _ walking_span.left, hs.fac _ walking_span.right]⟩⟩

/-- If `W` is the pushout of `f, g`,
it is also the pushout of `h ≫ f, h ≫ g` for any epi `h`. -/
def isColimitOfEpiComp (f : X ⟶ Y) (g : X ⟶ Z) (h : W ⟶ X) [Epi h] (s : PushoutCocone f g) (H : IsColimit s) :
    IsColimit
      (PushoutCocone.mk _ _
        (show (h ≫ f) ≫ s.inl = (h ≫ g) ≫ s.inr by
          rw [category.assoc, category.assoc, s.condition])) :=
  by
  apply pushout_cocone.is_colimit_aux'
  intro s
  rcases pushout_cocone.is_colimit.desc' H s.inl s.inr
      ((cancel_epi h).mp
        (by
          simpa using s.condition)) with
    ⟨l, h₁, h₂⟩
  refine' ⟨l, h₁, h₂, _⟩
  intro m hm₁ hm₂
  exact (pushout_cocone.is_colimit.hom_ext H (hm₁.trans h₁.symm) (hm₂.trans h₂.symm) : _)

end PushoutCocone

/-- This is a helper construction that can be useful when verifying that a category has all
    pullbacks. Given `F : walking_cospan ⥤ C`, which is really the same as
    `cospan (F.map inl) (F.map inr)`, and a pullback cone on `F.map inl` and `F.map inr`, we
    get a cone on `F`.

    If you're thinking about using this, have a look at `has_pullbacks_of_has_limit_cospan`,
    which you may find to be an easier way of achieving your goal. -/
@[simps]
def Cone.ofPullbackCone {F : walking_cospan ⥤ C} (t : PullbackCone (F.map inl) (F.map inr)) : Cone F where
  x := t.x
  π := t.π ≫ (diagramIsoCospan F).inv

/-- This is a helper construction that can be useful when verifying that a category has all
    pushout. Given `F : walking_span ⥤ C`, which is really the same as
    `span (F.map fst) (F.mal snd)`, and a pushout cocone on `F.map fst` and `F.map snd`,
    we get a cocone on `F`.

    If you're thinking about using this, have a look at `has_pushouts_of_has_colimit_span`, which
    you may find to be an easiery way of achieving your goal.  -/
@[simps]
def Cocone.ofPushoutCocone {F : walking_span ⥤ C} (t : PushoutCocone (F.map fst) (F.map snd)) : Cocone F where
  x := t.x
  ι := (diagramIsoSpan F).Hom ≫ t.ι

/-- Given `F : walking_cospan ⥤ C`, which is really the same as `cospan (F.map inl) (F.map inr)`,
    and a cone on `F`, we get a pullback cone on `F.map inl` and `F.map inr`. -/
@[simps]
def PullbackCone.ofCone {F : walking_cospan ⥤ C} (t : Cone F) : PullbackCone (F.map inl) (F.map inr) where
  x := t.x
  π := t.π ≫ (diagramIsoCospan F).Hom

/-- A diagram `walking_cospan ⥤ C` is isomorphic to some `pullback_cone.mk` after
composing with `diagram_iso_cospan`. -/
@[simps]
def PullbackCone.isoMk {F : walking_cospan ⥤ C} (t : Cone F) :
    (Cones.postcompose (diagramIsoCospan.{v} _).Hom).obj t ≅
      PullbackCone.mk (t.π.app WalkingCospan.left) (t.π.app WalkingCospan.right)
        ((t.π.naturality inl).symm.trans (t.π.naturality inr : _)) :=
  Cones.ext (Iso.refl _) <| by
    rintro (_ | (_ | _)) <;>
      · dsimp'
        simp
        

/-- Given `F : walking_span ⥤ C`, which is really the same as `span (F.map fst) (F.map snd)`,
    and a cocone on `F`, we get a pushout cocone on `F.map fst` and `F.map snd`. -/
@[simps]
def PushoutCocone.ofCocone {F : walking_span ⥤ C} (t : Cocone F) : PushoutCocone (F.map fst) (F.map snd) where
  x := t.x
  ι := (diagramIsoSpan F).inv ≫ t.ι

/-- A diagram `walking_span ⥤ C` is isomorphic to some `pushout_cocone.mk` after composing with
`diagram_iso_span`. -/
@[simps]
def PushoutCocone.isoMk {F : walking_span ⥤ C} (t : Cocone F) :
    (Cocones.precompose (diagramIsoSpan.{v} _).inv).obj t ≅
      PushoutCocone.mk (t.ι.app WalkingSpan.left) (t.ι.app WalkingSpan.right)
        ((t.ι.naturality fst).trans (t.ι.naturality snd).symm) :=
  Cocones.ext (Iso.refl _) <| by
    rintro (_ | (_ | _)) <;>
      · dsimp'
        simp
        

/-- `has_pullback f g` represents a particular choice of limiting cone
for the pair of morphisms `f : X ⟶ Z` and `g : Y ⟶ Z`.
-/
abbrev HasPullback {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :=
  HasLimit (cospan f g)

/-- `has_pushout f g` represents a particular choice of colimiting cocone
for the pair of morphisms `f : X ⟶ Y` and `g : X ⟶ Z`.
-/
abbrev HasPushout {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) :=
  HasColimit (span f g)

/-- `pullback f g` computes the pullback of a pair of morphisms with the same target. -/
abbrev pullback {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] :=
  limit (cospan f g)

/-- `pushout f g` computes the pushout of a pair of morphisms with the same source. -/
abbrev pushout {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g] :=
  colimit (span f g)

/-- The first projection of the pullback of `f` and `g`. -/
abbrev pullback.fst {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [HasPullback f g] : pullback f g ⟶ X :=
  limit.π (cospan f g) WalkingCospan.left

/-- The second projection of the pullback of `f` and `g`. -/
abbrev pullback.snd {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [HasPullback f g] : pullback f g ⟶ Y :=
  limit.π (cospan f g) WalkingCospan.right

/-- The first inclusion into the pushout of `f` and `g`. -/
abbrev pushout.inl {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [HasPushout f g] : Y ⟶ pushout f g :=
  colimit.ι (span f g) WalkingSpan.left

/-- The second inclusion into the pushout of `f` and `g`. -/
abbrev pushout.inr {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [HasPushout f g] : Z ⟶ pushout f g :=
  colimit.ι (span f g) WalkingSpan.right

/-- A pair of morphisms `h : W ⟶ X` and `k : W ⟶ Y` satisfying `h ≫ f = k ≫ g` induces a morphism
    `pullback.lift : W ⟶ pullback f g`. -/
abbrev pullback.lift {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [HasPullback f g] (h : W ⟶ X) (k : W ⟶ Y)
    (w : h ≫ f = k ≫ g) : W ⟶ pullback f g :=
  limit.lift _ (PullbackCone.mk h k w)

/-- A pair of morphisms `h : Y ⟶ W` and `k : Z ⟶ W` satisfying `f ≫ h = g ≫ k` induces a morphism
    `pushout.desc : pushout f g ⟶ W`. -/
abbrev pushout.desc {W X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [HasPushout f g] (h : Y ⟶ W) (k : Z ⟶ W) (w : f ≫ h = g ≫ k) :
    pushout f g ⟶ W :=
  colimit.desc _ (PushoutCocone.mk h k w)

@[simp, reassoc]
theorem pullback.lift_fst {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [HasPullback f g] (h : W ⟶ X) (k : W ⟶ Y)
    (w : h ≫ f = k ≫ g) : pullback.lift h k w ≫ pullback.fst = h :=
  limit.lift_π _ _

@[simp, reassoc]
theorem pullback.lift_snd {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [HasPullback f g] (h : W ⟶ X) (k : W ⟶ Y)
    (w : h ≫ f = k ≫ g) : pullback.lift h k w ≫ pullback.snd = k :=
  limit.lift_π _ _

@[simp, reassoc]
theorem pushout.inl_desc {W X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [HasPushout f g] (h : Y ⟶ W) (k : Z ⟶ W)
    (w : f ≫ h = g ≫ k) : pushout.inl ≫ pushout.desc h k w = h :=
  colimit.ι_desc _ _

@[simp, reassoc]
theorem pushout.inr_desc {W X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [HasPushout f g] (h : Y ⟶ W) (k : Z ⟶ W)
    (w : f ≫ h = g ≫ k) : pushout.inr ≫ pushout.desc h k w = k :=
  colimit.ι_desc _ _

/-- A pair of morphisms `h : W ⟶ X` and `k : W ⟶ Y` satisfying `h ≫ f = k ≫ g` induces a morphism
    `l : W ⟶ pullback f g` such that `l ≫ pullback.fst = h` and `l ≫ pullback.snd = k`. -/
def pullback.lift' {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [HasPullback f g] (h : W ⟶ X) (k : W ⟶ Y) (w : h ≫ f = k ≫ g) :
    { l : W ⟶ pullback f g // l ≫ pullback.fst = h ∧ l ≫ pullback.snd = k } :=
  ⟨pullback.lift h k w, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩

/-- A pair of morphisms `h : Y ⟶ W` and `k : Z ⟶ W` satisfying `f ≫ h = g ≫ k` induces a morphism
    `l : pushout f g ⟶ W` such that `pushout.inl ≫ l = h` and `pushout.inr ≫ l = k`. -/
def pullback.desc' {W X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [HasPushout f g] (h : Y ⟶ W) (k : Z ⟶ W) (w : f ≫ h = g ≫ k) :
    { l : pushout f g ⟶ W // pushout.inl ≫ l = h ∧ pushout.inr ≫ l = k } :=
  ⟨pushout.desc h k w, pushout.inl_desc _ _ _, pushout.inr_desc _ _ _⟩

@[reassoc]
theorem pullback.condition {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [HasPullback f g] :
    (pullback.fst : pullback f g ⟶ X) ≫ f = pullback.snd ≫ g :=
  PullbackCone.condition _

@[reassoc]
theorem pushout.condition {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [HasPushout f g] :
    f ≫ (pushout.inl : Y ⟶ pushout f g) = g ≫ pushout.inr :=
  PushoutCocone.condition _

/-- Given such a diagram, then there is a natural morphism `W ×ₛ X ⟶ Y ×ₜ Z`.

    W  ⟶  Y
      ↘      ↘
        S  ⟶  T
      ↗      ↗
    X  ⟶  Z

-/
abbrev pullback.map {W X Y Z S T : C} (f₁ : W ⟶ S) (f₂ : X ⟶ S) [HasPullback f₁ f₂] (g₁ : Y ⟶ T) (g₂ : Z ⟶ T)
    [HasPullback g₁ g₂] (i₁ : W ⟶ Y) (i₂ : X ⟶ Z) (i₃ : S ⟶ T) (eq₁ : f₁ ≫ i₃ = i₁ ≫ g₁) (eq₂ : f₂ ≫ i₃ = i₂ ≫ g₂) :
    pullback f₁ f₂ ⟶ pullback g₁ g₂ :=
  pullback.lift (pullback.fst ≫ i₁) (pullback.snd ≫ i₂)
    (by
      simp [eq₁, eq₂, ← pullback.condition_assoc])

/-- Given such a diagram, then there is a natural morphism `W ⨿ₛ X ⟶ Y ⨿ₜ Z`.

        W  ⟶  Y
      ↗      ↗
    S  ⟶  T
      ↘      ↘
        X  ⟶  Z

-/
abbrev pushout.map {W X Y Z S T : C} (f₁ : S ⟶ W) (f₂ : S ⟶ X) [HasPushout f₁ f₂] (g₁ : T ⟶ Y) (g₂ : T ⟶ Z)
    [HasPushout g₁ g₂] (i₁ : W ⟶ Y) (i₂ : X ⟶ Z) (i₃ : S ⟶ T) (eq₁ : f₁ ≫ i₁ = i₃ ≫ g₁) (eq₂ : f₂ ≫ i₂ = i₃ ≫ g₂) :
    pushout f₁ f₂ ⟶ pushout g₁ g₂ :=
  pushout.desc (i₁ ≫ pushout.inl) (i₂ ≫ pushout.inr)
    (by
      simp only [category.assoc, ← eq₁, ← eq₂]
      simp [← pushout.condition])

/-- Two morphisms into a pullback are equal if their compositions with the pullback morphisms are
    equal -/
@[ext]
theorem pullback.hom_ext {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [HasPullback f g] {W : C} {k l : W ⟶ pullback f g}
    (h₀ : k ≫ pullback.fst = l ≫ pullback.fst) (h₁ : k ≫ pullback.snd = l ≫ pullback.snd) : k = l :=
  limit.hom_ext <| PullbackCone.equalizer_ext _ h₀ h₁

/-- The pullback cone built from the pullback projections is a pullback. -/
def pullbackIsPullback {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] :
    IsLimit (PullbackCone.mk (pullback.fst : pullback f g ⟶ _) pullback.snd pullback.condition) :=
  PullbackCone.IsLimit.mk _ (fun s => pullback.lift s.fst s.snd s.condition)
    (by
      simp )
    (by
      simp )
    (by
      tidy)

/-- The pullback of a monomorphism is a monomorphism -/
instance pullback.fst_of_mono {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [HasPullback f g] [Mono g] :
    Mono (pullback.fst : pullback f g ⟶ X) :=
  PullbackCone.mono_fst_of_is_pullback_of_mono (limit.isLimit _)

/-- The pullback of a monomorphism is a monomorphism -/
instance pullback.snd_of_mono {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [HasPullback f g] [Mono f] :
    Mono (pullback.snd : pullback f g ⟶ Y) :=
  PullbackCone.mono_snd_of_is_pullback_of_mono (limit.isLimit _)

/-- The map `X ×[Z] Y ⟶ X × Y` is mono. -/
instance mono_pullback_to_prod {C : Type _} [Category C] {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g]
    [HasBinaryProduct X Y] : Mono (prod.lift pullback.fst pullback.snd : pullback f g ⟶ _) :=
  ⟨fun W i₁ i₂ h => by
    ext
    · simpa using congr_arg (fun f => f ≫ Prod.fst) h
      
    · simpa using congr_arg (fun f => f ≫ Prod.snd) h
      ⟩

/-- Two morphisms out of a pushout are equal if their compositions with the pushout morphisms are
    equal -/
@[ext]
theorem pushout.hom_ext {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [HasPushout f g] {W : C} {k l : pushout f g ⟶ W}
    (h₀ : pushout.inl ≫ k = pushout.inl ≫ l) (h₁ : pushout.inr ≫ k = pushout.inr ≫ l) : k = l :=
  colimit.hom_ext <| PushoutCocone.coequalizer_ext _ h₀ h₁

/-- The pushout cocone built from the pushout coprojections is a pushout. -/
def pushoutIsPushout {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g] :
    IsColimit (PushoutCocone.mk (pushout.inl : _ ⟶ pushout f g) pushout.inr pushout.condition) :=
  PushoutCocone.IsColimit.mk _ (fun s => pushout.desc s.inl s.inr s.condition)
    (by
      simp )
    (by
      simp )
    (by
      tidy)

/-- The pushout of an epimorphism is an epimorphism -/
instance pushout.inl_of_epi {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [HasPushout f g] [Epi g] :
    Epi (pushout.inl : Y ⟶ pushout f g) :=
  PushoutCocone.epi_inl_of_is_pushout_of_epi (colimit.isColimit _)

/-- The pushout of an epimorphism is an epimorphism -/
instance pushout.inr_of_epi {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [HasPushout f g] [Epi f] :
    Epi (pushout.inr : Z ⟶ pushout f g) :=
  PushoutCocone.epi_inr_of_is_pushout_of_epi (colimit.isColimit _)

/-- The map ` X ⨿ Y ⟶ X ⨿[Z] Y` is epi. -/
instance epi_coprod_to_pushout {C : Type _} [Category C] {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g]
    [HasBinaryCoproduct Y Z] : Epi (coprod.desc pushout.inl pushout.inr : _ ⟶ pushout f g) :=
  ⟨fun W i₁ i₂ h => by
    ext
    · simpa using congr_arg (fun f => coprod.inl ≫ f) h
      
    · simpa using congr_arg (fun f => coprod.inr ≫ f) h
      ⟩

instance pullback.map_is_iso {W X Y Z S T : C} (f₁ : W ⟶ S) (f₂ : X ⟶ S) [HasPullback f₁ f₂] (g₁ : Y ⟶ T) (g₂ : Z ⟶ T)
    [HasPullback g₁ g₂] (i₁ : W ⟶ Y) (i₂ : X ⟶ Z) (i₃ : S ⟶ T) (eq₁ : f₁ ≫ i₃ = i₁ ≫ g₁) (eq₂ : f₂ ≫ i₃ = i₂ ≫ g₂)
    [IsIso i₁] [IsIso i₂] [IsIso i₃] : IsIso (pullback.map f₁ f₂ g₁ g₂ i₁ i₂ i₃ eq₁ eq₂) := by
  refine' ⟨⟨pullback.map _ _ _ _ (inv i₁) (inv i₂) (inv i₃) _ _, _, _⟩⟩
  · rw [is_iso.comp_inv_eq, category.assoc, eq₁, is_iso.inv_hom_id_assoc]
    
  · rw [is_iso.comp_inv_eq, category.assoc, eq₂, is_iso.inv_hom_id_assoc]
    
  tidy

/-- If `f₁ = f₂` and `g₁ = g₂`, we may construct a canonical
isomorphism `pullback f₁ g₁ ≅ pullback f₂ g₂` -/
@[simps Hom]
def pullback.congrHom {X Y Z : C} {f₁ f₂ : X ⟶ Z} {g₁ g₂ : Y ⟶ Z} (h₁ : f₁ = f₂) (h₂ : g₁ = g₂) [HasPullback f₁ g₁]
    [HasPullback f₂ g₂] : pullback f₁ g₁ ≅ pullback f₂ g₂ :=
  as_iso <|
    pullback.map _ _ _ _ (𝟙 _) (𝟙 _) (𝟙 _)
      (by
        simp [← h₁])
      (by
        simp [← h₂])

@[simp]
theorem pullback.congr_hom_inv {X Y Z : C} {f₁ f₂ : X ⟶ Z} {g₁ g₂ : Y ⟶ Z} (h₁ : f₁ = f₂) (h₂ : g₁ = g₂)
    [HasPullback f₁ g₁] [HasPullback f₂ g₂] :
    (pullback.congrHom h₁ h₂).inv =
      pullback.map _ _ _ _ (𝟙 _) (𝟙 _) (𝟙 _)
        (by
          simp [← h₁])
        (by
          simp [← h₂]) :=
  by
  apply pullback.hom_ext
  · erw [pullback.lift_fst]
    rw [iso.inv_comp_eq]
    erw [pullback.lift_fst_assoc]
    rw [category.comp_id, category.comp_id]
    
  · erw [pullback.lift_snd]
    rw [iso.inv_comp_eq]
    erw [pullback.lift_snd_assoc]
    rw [category.comp_id, category.comp_id]
    

instance pushout.map_is_iso {W X Y Z S T : C} (f₁ : S ⟶ W) (f₂ : S ⟶ X) [HasPushout f₁ f₂] (g₁ : T ⟶ Y) (g₂ : T ⟶ Z)
    [HasPushout g₁ g₂] (i₁ : W ⟶ Y) (i₂ : X ⟶ Z) (i₃ : S ⟶ T) (eq₁ : f₁ ≫ i₁ = i₃ ≫ g₁) (eq₂ : f₂ ≫ i₂ = i₃ ≫ g₂)
    [IsIso i₁] [IsIso i₂] [IsIso i₃] : IsIso (pushout.map f₁ f₂ g₁ g₂ i₁ i₂ i₃ eq₁ eq₂) := by
  refine' ⟨⟨pushout.map _ _ _ _ (inv i₁) (inv i₂) (inv i₃) _ _, _, _⟩⟩
  · rw [is_iso.comp_inv_eq, category.assoc, eq₁, is_iso.inv_hom_id_assoc]
    
  · rw [is_iso.comp_inv_eq, category.assoc, eq₂, is_iso.inv_hom_id_assoc]
    
  tidy

/-- If `f₁ = f₂` and `g₁ = g₂`, we may construct a canonical
isomorphism `pushout f₁ g₁ ≅ pullback f₂ g₂` -/
@[simps Hom]
def pushout.congrHom {X Y Z : C} {f₁ f₂ : X ⟶ Y} {g₁ g₂ : X ⟶ Z} (h₁ : f₁ = f₂) (h₂ : g₁ = g₂) [HasPushout f₁ g₁]
    [HasPushout f₂ g₂] : pushout f₁ g₁ ≅ pushout f₂ g₂ :=
  as_iso <|
    pushout.map _ _ _ _ (𝟙 _) (𝟙 _) (𝟙 _)
      (by
        simp [← h₁])
      (by
        simp [← h₂])

@[simp]
theorem pushout.congr_hom_inv {X Y Z : C} {f₁ f₂ : X ⟶ Y} {g₁ g₂ : X ⟶ Z} (h₁ : f₁ = f₂) (h₂ : g₁ = g₂)
    [HasPushout f₁ g₁] [HasPushout f₂ g₂] :
    (pushout.congrHom h₁ h₂).inv =
      pushout.map _ _ _ _ (𝟙 _) (𝟙 _) (𝟙 _)
        (by
          simp [← h₁])
        (by
          simp [← h₂]) :=
  by
  apply pushout.hom_ext
  · erw [pushout.inl_desc]
    rw [iso.comp_inv_eq, category.id_comp]
    erw [pushout.inl_desc]
    rw [category.id_comp]
    
  · erw [pushout.inr_desc]
    rw [iso.comp_inv_eq, category.id_comp]
    erw [pushout.inr_desc]
    rw [category.id_comp]
    

section

variable (G : C ⥤ D)

/-- The comparison morphism for the pullback of `f,g`.
This is an isomorphism iff `G` preserves the pullback of `f,g`; see
`category_theory/limits/preserves/shapes/pullbacks.lean`
-/
def pullbackComparison (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] [HasPullback (G.map f) (G.map g)] :
    G.obj (pullback f g) ⟶ pullback (G.map f) (G.map g) :=
  pullback.lift (G.map pullback.fst) (G.map pullback.snd)
    (by
      simp only [G.map_comp, ← pullback.condition])

@[simp, reassoc]
theorem pullback_comparison_comp_fst (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] [HasPullback (G.map f) (G.map g)] :
    pullbackComparison G f g ≫ pullback.fst = G.map pullback.fst :=
  pullback.lift_fst _ _ _

@[simp, reassoc]
theorem pullback_comparison_comp_snd (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] [HasPullback (G.map f) (G.map g)] :
    pullbackComparison G f g ≫ pullback.snd = G.map pullback.snd :=
  pullback.lift_snd _ _ _

@[simp, reassoc]
theorem map_lift_pullback_comparison (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] [HasPullback (G.map f) (G.map g)] {W : C}
    {h : W ⟶ X} {k : W ⟶ Y} (w : h ≫ f = k ≫ g) :
    G.map (pullback.lift _ _ w) ≫ pullbackComparison G f g =
      pullback.lift (G.map h) (G.map k)
        (by
          simp only [G.map_comp, ← w]) :=
  by
  ext <;> simp [G.map_comp]

/-- The comparison morphism for the pushout of `f,g`.
This is an isomorphism iff `G` preserves the pushout of `f,g`; see
`category_theory/limits/preserves/shapes/pullbacks.lean`
-/
def pushoutComparison (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g] [HasPushout (G.map f) (G.map g)] :
    pushout (G.map f) (G.map g) ⟶ G.obj (pushout f g) :=
  pushout.desc (G.map pushout.inl) (G.map pushout.inr)
    (by
      simp only [G.map_comp, ← pushout.condition])

@[simp, reassoc]
theorem inl_comp_pushout_comparison (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g] [HasPushout (G.map f) (G.map g)] :
    pushout.inl ≫ pushoutComparison G f g = G.map pushout.inl :=
  pushout.inl_desc _ _ _

@[simp, reassoc]
theorem inr_comp_pushout_comparison (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g] [HasPushout (G.map f) (G.map g)] :
    pushout.inr ≫ pushoutComparison G f g = G.map pushout.inr :=
  pushout.inr_desc _ _ _

@[simp, reassoc]
theorem pushout_comparison_map_desc (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g] [HasPushout (G.map f) (G.map g)] {W : C}
    {h : Y ⟶ W} {k : Z ⟶ W} (w : f ≫ h = g ≫ k) :
    pushoutComparison G f g ≫ G.map (pushout.desc _ _ w) =
      pushout.desc (G.map h) (G.map k)
        (by
          simp only [G.map_comp, ← w]) :=
  by
  ext <;> simp [G.map_comp]

end

section PullbackSymmetry

open WalkingCospan

variable (f : X ⟶ Z) (g : Y ⟶ Z)

/-- Making this a global instance would make the typeclass seach go in an infinite loop. -/
theorem has_pullback_symmetry [HasPullback f g] : HasPullback g f :=
  ⟨⟨⟨PullbackCone.mk _ _ pullback.condition.symm, PullbackCone.flipIsLimit (pullbackIsPullback _ _)⟩⟩⟩

attribute [local instance] has_pullback_symmetry

/-- The isomorphism `X ×[Z] Y ≅ Y ×[Z] X`. -/
def pullbackSymmetry [HasPullback f g] : pullback f g ≅ pullback g f :=
  IsLimit.conePointUniqueUpToIso
    (PullbackCone.flipIsLimit (pullbackIsPullback f g) : IsLimit (PullbackCone.mk _ _ pullback.condition.symm))
    (limit.isLimit _)

@[simp, reassoc]
theorem pullback_symmetry_hom_comp_fst [HasPullback f g] : (pullbackSymmetry f g).Hom ≫ pullback.fst = pullback.snd :=
  by
  simp [← pullback_symmetry]

@[simp, reassoc]
theorem pullback_symmetry_hom_comp_snd [HasPullback f g] : (pullbackSymmetry f g).Hom ≫ pullback.snd = pullback.fst :=
  by
  simp [← pullback_symmetry]

@[simp, reassoc]
theorem pullback_symmetry_inv_comp_fst [HasPullback f g] : (pullbackSymmetry f g).inv ≫ pullback.fst = pullback.snd :=
  by
  simp [← iso.inv_comp_eq]

@[simp, reassoc]
theorem pullback_symmetry_inv_comp_snd [HasPullback f g] : (pullbackSymmetry f g).inv ≫ pullback.snd = pullback.fst :=
  by
  simp [← iso.inv_comp_eq]

end PullbackSymmetry

section PushoutSymmetry

open WalkingCospan

variable (f : X ⟶ Y) (g : X ⟶ Z)

/-- Making this a global instance would make the typeclass seach go in an infinite loop. -/
theorem has_pushout_symmetry [HasPushout f g] : HasPushout g f :=
  ⟨⟨⟨PushoutCocone.mk _ _ pushout.condition.symm, PushoutCocone.flipIsColimit (pushoutIsPushout _ _)⟩⟩⟩

attribute [local instance] has_pushout_symmetry

/-- The isomorphism `Y ⨿[X] Z ≅ Z ⨿[X] Y`. -/
def pushoutSymmetry [HasPushout f g] : pushout f g ≅ pushout g f :=
  IsColimit.coconePointUniqueUpToIso
    (PushoutCocone.flipIsColimit (pushoutIsPushout f g) : IsColimit (PushoutCocone.mk _ _ pushout.condition.symm))
    (colimit.isColimit _)

@[simp, reassoc]
theorem inl_comp_pushout_symmetry_hom [HasPushout f g] : pushout.inl ≫ (pushoutSymmetry f g).Hom = pushout.inr :=
  (colimit.isColimit (span f g)).comp_cocone_point_unique_up_to_iso_hom
    (PushoutCocone.flipIsColimit (pushoutIsPushout g f)) _

@[simp, reassoc]
theorem inr_comp_pushout_symmetry_hom [HasPushout f g] : pushout.inr ≫ (pushoutSymmetry f g).Hom = pushout.inl :=
  (colimit.isColimit (span f g)).comp_cocone_point_unique_up_to_iso_hom
    (PushoutCocone.flipIsColimit (pushoutIsPushout g f)) _

@[simp, reassoc]
theorem inl_comp_pushout_symmetry_inv [HasPushout f g] : pushout.inl ≫ (pushoutSymmetry f g).inv = pushout.inr := by
  simp [← iso.comp_inv_eq]

@[simp, reassoc]
theorem inr_comp_pushout_symmetry_inv [HasPushout f g] : pushout.inr ≫ (pushoutSymmetry f g).inv = pushout.inl := by
  simp [← iso.comp_inv_eq]

end PushoutSymmetry

section PullbackLeftIso

open WalkingCospan

/-- The pullback of `f, g` is also the pullback of `f ≫ i, g ≫ i` for any mono `i`. -/
noncomputable def pullbackIsPullbackOfCompMono (f : X ⟶ W) (g : Y ⟶ W) (i : W ⟶ Z) [Mono i] [HasPullback f g] :
    IsLimit (PullbackCone.mk pullback.fst pullback.snd _) :=
  PullbackCone.isLimitOfCompMono f g i _ (limit.isLimit (cospan f g))

instance has_pullback_of_comp_mono (f : X ⟶ W) (g : Y ⟶ W) (i : W ⟶ Z) [Mono i] [HasPullback f g] :
    HasPullback (f ≫ i) (g ≫ i) :=
  ⟨⟨⟨_, pullbackIsPullbackOfCompMono f g i⟩⟩⟩

variable (f : X ⟶ Z) (g : Y ⟶ Z) [IsIso f]

/-- If `f : X ⟶ Z` is iso, then `X ×[Z] Y ≅ Y`. This is the explicit limit cone. -/
def pullbackConeOfLeftIso : PullbackCone f g :=
  PullbackCone.mk (g ≫ inv f) (𝟙 _) <| by
    simp

@[simp]
theorem pullback_cone_of_left_iso_X : (pullbackConeOfLeftIso f g).x = Y :=
  rfl

@[simp]
theorem pullback_cone_of_left_iso_fst : (pullbackConeOfLeftIso f g).fst = g ≫ inv f :=
  rfl

@[simp]
theorem pullback_cone_of_left_iso_snd : (pullbackConeOfLeftIso f g).snd = 𝟙 _ :=
  rfl

@[simp]
theorem pullback_cone_of_left_iso_π_app_none : (pullbackConeOfLeftIso f g).π.app none = g := by
  delta' pullback_cone_of_left_iso
  simp

@[simp]
theorem pullback_cone_of_left_iso_π_app_left : (pullbackConeOfLeftIso f g).π.app left = g ≫ inv f :=
  rfl

@[simp]
theorem pullback_cone_of_left_iso_π_app_right : (pullbackConeOfLeftIso f g).π.app right = 𝟙 _ :=
  rfl

/-- Verify that the constructed limit cone is indeed a limit. -/
def pullbackConeOfLeftIsoIsLimit : IsLimit (pullbackConeOfLeftIso f g) :=
  PullbackCone.isLimitAux' _ fun s =>
    ⟨s.snd, by
      simp [s.condition_assoc]⟩

theorem has_pullback_of_left_iso : HasPullback f g :=
  ⟨⟨⟨_, pullbackConeOfLeftIsoIsLimit f g⟩⟩⟩

attribute [local instance] has_pullback_of_left_iso

instance pullback_snd_iso_of_left_iso : IsIso (pullback.snd : pullback f g ⟶ _) := by
  refine'
    ⟨⟨pullback.lift (g ≫ inv f) (𝟙 _)
          (by
            simp ),
        _, by
        simp ⟩⟩
  ext
  · simp [pullback.condition_assoc]
    
  · simp [← pullback.condition_assoc]
    

variable (i : Z ⟶ W) [Mono i]

instance has_pullback_of_right_factors_mono (f : X ⟶ Z) : HasPullback i (f ≫ i) := by
  conv => congr rw [← category.id_comp i]
  infer_instance

instance pullback_snd_iso_of_right_factors_mono (f : X ⟶ Z) : IsIso (pullback.snd : pullback i (f ≫ i) ⟶ _) := by
  convert
      (congr_arg is_iso
            (show _ ≫ pullback.snd = _ from
              limit.iso_limit_cone_hom_π ⟨_, pullback_is_pullback_of_comp_mono (𝟙 _) f i⟩ walking_cospan.right)).mp
        inferInstance <;>
    exact (category.id_comp _).symm

end PullbackLeftIso

section PullbackRightIso

open WalkingCospan

variable (f : X ⟶ Z) (g : Y ⟶ Z) [IsIso g]

/-- If `g : Y ⟶ Z` is iso, then `X ×[Z] Y ≅ X`. This is the explicit limit cone. -/
def pullbackConeOfRightIso : PullbackCone f g :=
  PullbackCone.mk (𝟙 _) (f ≫ inv g) <| by
    simp

@[simp]
theorem pullback_cone_of_right_iso_X : (pullbackConeOfRightIso f g).x = X :=
  rfl

@[simp]
theorem pullback_cone_of_right_iso_fst : (pullbackConeOfRightIso f g).fst = 𝟙 _ :=
  rfl

@[simp]
theorem pullback_cone_of_right_iso_snd : (pullbackConeOfRightIso f g).snd = f ≫ inv g :=
  rfl

@[simp]
theorem pullback_cone_of_right_iso_π_app_none : (pullbackConeOfRightIso f g).π.app none = f :=
  Category.id_comp _

@[simp]
theorem pullback_cone_of_right_iso_π_app_left : (pullbackConeOfRightIso f g).π.app left = 𝟙 _ :=
  rfl

@[simp]
theorem pullback_cone_of_right_iso_π_app_right : (pullbackConeOfRightIso f g).π.app right = f ≫ inv g :=
  rfl

/-- Verify that the constructed limit cone is indeed a limit. -/
def pullbackConeOfRightIsoIsLimit : IsLimit (pullbackConeOfRightIso f g) :=
  PullbackCone.isLimitAux' _ fun s =>
    ⟨s.fst, by
      simp [← s.condition_assoc]⟩

theorem has_pullback_of_right_iso : HasPullback f g :=
  ⟨⟨⟨_, pullbackConeOfRightIsoIsLimit f g⟩⟩⟩

attribute [local instance] has_pullback_of_right_iso

instance pullback_snd_iso_of_right_iso : IsIso (pullback.fst : pullback f g ⟶ _) := by
  refine'
    ⟨⟨pullback.lift (𝟙 _) (f ≫ inv g)
          (by
            simp ),
        _, by
        simp ⟩⟩
  ext
  · simp
    
  · simp [← pullback.condition_assoc]
    

variable (i : Z ⟶ W) [Mono i]

instance has_pullback_of_left_factors_mono (f : X ⟶ Z) : HasPullback (f ≫ i) i := by
  conv => congr skip rw [← category.id_comp i]
  infer_instance

instance pullback_snd_iso_of_left_factors_mono (f : X ⟶ Z) : IsIso (pullback.fst : pullback (f ≫ i) i ⟶ _) := by
  convert
      (congr_arg is_iso
            (show _ ≫ pullback.fst = _ from
              limit.iso_limit_cone_hom_π ⟨_, pullback_is_pullback_of_comp_mono f (𝟙 _) i⟩ walking_cospan.left)).mp
        inferInstance <;>
    exact (category.id_comp _).symm

end PullbackRightIso

section PushoutLeftIso

open WalkingSpan

/-- The pushout of `f, g` is also the pullback of `h ≫ f, h ≫ g` for any epi `h`. -/
noncomputable def pushoutIsPushoutOfEpiComp (f : X ⟶ Y) (g : X ⟶ Z) (h : W ⟶ X) [Epi h] [HasPushout f g] :
    IsColimit (PushoutCocone.mk pushout.inl pushout.inr _) :=
  PushoutCocone.isColimitOfEpiComp f g h _ (colimit.isColimit (span f g))

instance has_pushout_of_epi_comp (f : X ⟶ Y) (g : X ⟶ Z) (h : W ⟶ X) [Epi h] [HasPushout f g] :
    HasPushout (h ≫ f) (h ≫ g) :=
  ⟨⟨⟨_, pushoutIsPushoutOfEpiComp f g h⟩⟩⟩

variable (f : X ⟶ Y) (g : X ⟶ Z) [IsIso f]

/-- If `f : X ⟶ Y` is iso, then `Y ⨿[X] Z ≅ Z`. This is the explicit colimit cocone. -/
def pushoutCoconeOfLeftIso : PushoutCocone f g :=
  PushoutCocone.mk (inv f ≫ g) (𝟙 _) <| by
    simp

@[simp]
theorem pushout_cocone_of_left_iso_X : (pushoutCoconeOfLeftIso f g).x = Z :=
  rfl

@[simp]
theorem pushout_cocone_of_left_iso_inl : (pushoutCoconeOfLeftIso f g).inl = inv f ≫ g :=
  rfl

@[simp]
theorem pushout_cocone_of_left_iso_inr : (pushoutCoconeOfLeftIso f g).inr = 𝟙 _ :=
  rfl

@[simp]
theorem pushout_cocone_of_left_iso_ι_app_none : (pushoutCoconeOfLeftIso f g).ι.app none = g := by
  delta' pushout_cocone_of_left_iso
  simp

@[simp]
theorem pushout_cocone_of_left_iso_ι_app_left : (pushoutCoconeOfLeftIso f g).ι.app left = inv f ≫ g :=
  rfl

@[simp]
theorem pushout_cocone_of_left_iso_ι_app_right : (pushoutCoconeOfLeftIso f g).ι.app right = 𝟙 _ :=
  rfl

/-- Verify that the constructed cocone is indeed a colimit. -/
def pushoutCoconeOfLeftIsoIsLimit : IsColimit (pushoutCoconeOfLeftIso f g) :=
  PushoutCocone.isColimitAux' _ fun s =>
    ⟨s.inr, by
      simp [s.condition]⟩

theorem has_pushout_of_left_iso : HasPushout f g :=
  ⟨⟨⟨_, pushoutCoconeOfLeftIsoIsLimit f g⟩⟩⟩

attribute [local instance] has_pushout_of_left_iso

instance pushout_inr_iso_of_left_iso : IsIso (pushout.inr : _ ⟶ pushout f g) := by
  refine'
    ⟨⟨pushout.desc (inv f ≫ g) (𝟙 _)
          (by
            simp ),
        by
        simp , _⟩⟩
  ext
  · simp [pushout.condition]
    
  · simp [← pushout.condition_assoc]
    

variable (h : W ⟶ X) [Epi h]

instance has_pushout_of_right_factors_epi (f : X ⟶ Y) : HasPushout h (h ≫ f) := by
  conv => congr rw [← category.comp_id h]
  infer_instance

instance pushout_inr_iso_of_right_factors_epi (f : X ⟶ Y) : IsIso (pushout.inr : _ ⟶ pushout h (h ≫ f)) := by
  convert
      (congr_arg is_iso
            (show pushout.inr ≫ _ = _ from
              colimit.iso_colimit_cocone_ι_inv ⟨_, pushout_is_pushout_of_epi_comp (𝟙 _) f h⟩ walking_span.right)).mp
        inferInstance <;>
    exact (category.comp_id _).symm

end PushoutLeftIso

section PushoutRightIso

open WalkingSpan

variable (f : X ⟶ Y) (g : X ⟶ Z) [IsIso g]

/-- If `f : X ⟶ Z` is iso, then `Y ⨿[X] Z ≅ Y`. This is the explicit colimit cocone. -/
def pushoutCoconeOfRightIso : PushoutCocone f g :=
  PushoutCocone.mk (𝟙 _) (inv g ≫ f) <| by
    simp

@[simp]
theorem pushout_cocone_of_right_iso_X : (pushoutCoconeOfRightIso f g).x = Y :=
  rfl

@[simp]
theorem pushout_cocone_of_right_iso_inl : (pushoutCoconeOfRightIso f g).inl = 𝟙 _ :=
  rfl

@[simp]
theorem pushout_cocone_of_right_iso_inr : (pushoutCoconeOfRightIso f g).inr = inv g ≫ f :=
  rfl

@[simp]
theorem pushout_cocone_of_right_iso_ι_app_none : (pushoutCoconeOfRightIso f g).ι.app none = f := by
  delta' pushout_cocone_of_right_iso
  simp

@[simp]
theorem pushout_cocone_of_right_iso_ι_app_left : (pushoutCoconeOfRightIso f g).ι.app left = 𝟙 _ :=
  rfl

@[simp]
theorem pushout_cocone_of_right_iso_ι_app_right : (pushoutCoconeOfRightIso f g).ι.app right = inv g ≫ f :=
  rfl

/-- Verify that the constructed cocone is indeed a colimit. -/
def pushoutCoconeOfRightIsoIsLimit : IsColimit (pushoutCoconeOfRightIso f g) :=
  PushoutCocone.isColimitAux' _ fun s =>
    ⟨s.inl, by
      simp [s.condition]⟩

theorem has_pushout_of_right_iso : HasPushout f g :=
  ⟨⟨⟨_, pushoutCoconeOfRightIsoIsLimit f g⟩⟩⟩

attribute [local instance] has_pushout_of_right_iso

instance pushout_inl_iso_of_right_iso : IsIso (pushout.inl : _ ⟶ pushout f g) := by
  refine'
    ⟨⟨pushout.desc (𝟙 _) (inv g ≫ f)
          (by
            simp ),
        by
        simp , _⟩⟩
  ext
  · simp [pushout.condition]
    
  · simp [← pushout.condition]
    

variable (h : W ⟶ X) [Epi h]

instance has_pushout_of_left_factors_epi (f : X ⟶ Y) : HasPushout (h ≫ f) h := by
  conv => congr skip rw [← category.comp_id h]
  infer_instance

instance pushout_inl_iso_of_left_factors_epi (f : X ⟶ Y) : IsIso (pushout.inl : _ ⟶ pushout (h ≫ f) h) := by
  convert
      (congr_arg is_iso
            (show pushout.inl ≫ _ = _ from
              colimit.iso_colimit_cocone_ι_inv ⟨_, pushout_is_pushout_of_epi_comp f (𝟙 _) h⟩ walking_span.left)).mp
        inferInstance <;>
    exact (category.comp_id _).symm

end PushoutRightIso

section

open WalkingCospan

variable (f : X ⟶ Y)

instance has_kernel_pair_of_mono [Mono f] : HasPullback f f :=
  ⟨⟨⟨_, PullbackCone.isLimitMkIdId f⟩⟩⟩

theorem fst_eq_snd_of_mono_eq [Mono f] : (pullback.fst : pullback f f ⟶ _) = pullback.snd :=
  ((PullbackCone.isLimitMkIdId f).fac (getLimitCone (cospan f f)).Cone left).symm.trans
    ((PullbackCone.isLimitMkIdId f).fac (getLimitCone (cospan f f)).Cone right : _)

@[simp]
theorem pullback_symmetry_hom_of_mono_eq [Mono f] : (pullbackSymmetry f f).Hom = 𝟙 _ := by
  ext <;> simp [← fst_eq_snd_of_mono_eq]

instance fst_iso_of_mono_eq [Mono f] : IsIso (pullback.fst : pullback f f ⟶ _) := by
  refine'
    ⟨⟨pullback.lift (𝟙 _) (𝟙 _)
          (by
            simp ),
        _, by
        simp ⟩⟩
  ext
  · simp
    
  · simp [← fst_eq_snd_of_mono_eq]
    

instance snd_iso_of_mono_eq [Mono f] : IsIso (pullback.snd : pullback f f ⟶ _) := by
  rw [← fst_eq_snd_of_mono_eq]
  infer_instance

end

section

open WalkingSpan

variable (f : X ⟶ Y)

instance has_cokernel_pair_of_epi [Epi f] : HasPushout f f :=
  ⟨⟨⟨_, PushoutCocone.isColimitMkIdId f⟩⟩⟩

theorem inl_eq_inr_of_epi_eq [Epi f] : (pushout.inl : _ ⟶ pushout f f) = pushout.inr :=
  ((PushoutCocone.isColimitMkIdId f).fac (getColimitCocone (span f f)).Cocone left).symm.trans
    ((PushoutCocone.isColimitMkIdId f).fac (getColimitCocone (span f f)).Cocone right : _)

@[simp]
theorem pullback_symmetry_hom_of_epi_eq [Epi f] : (pushoutSymmetry f f).Hom = 𝟙 _ := by
  ext <;> simp [← inl_eq_inr_of_epi_eq]

instance inl_iso_of_epi_eq [Epi f] : IsIso (pushout.inl : _ ⟶ pushout f f) := by
  refine'
    ⟨⟨pushout.desc (𝟙 _) (𝟙 _)
          (by
            simp ),
        by
        simp , _⟩⟩
  ext
  · simp
    
  · simp [← inl_eq_inr_of_epi_eq]
    

instance inr_iso_of_epi_eq [Epi f] : IsIso (pushout.inr : _ ⟶ pushout f f) := by
  rw [← inl_eq_inr_of_epi_eq]
  infer_instance

end

section PasteLemma

variable {X₁ X₂ X₃ Y₁ Y₂ Y₃ : C} (f₁ : X₁ ⟶ X₂) (f₂ : X₂ ⟶ X₃) (g₁ : Y₁ ⟶ Y₂) (g₂ : Y₂ ⟶ Y₃)

variable (i₁ : X₁ ⟶ Y₁) (i₂ : X₂ ⟶ Y₂) (i₃ : X₃ ⟶ Y₃)

variable (h₁ : i₁ ≫ g₁ = f₁ ≫ i₂) (h₂ : i₂ ≫ g₂ = f₂ ≫ i₃)

/-- Given

X₁ - f₁ -> X₂ - f₂ -> X₃
|          |          |
i₁         i₂         i₃
∨          ∨          ∨
Y₁ - g₁ -> Y₂ - g₂ -> Y₃

Then the big square is a pullback if both the small squares are.
-/
def bigSquareIsPullback (H : IsLimit (PullbackCone.mk _ _ h₂)) (H' : IsLimit (PullbackCone.mk _ _ h₁)) :
    IsLimit
      (PullbackCone.mk _ _
        (show i₁ ≫ g₁ ≫ g₂ = (f₁ ≫ f₂) ≫ i₃ by
          rw [← category.assoc, h₁, category.assoc, h₂, category.assoc])) :=
  by
  fapply pullback_cone.is_limit_aux'
  intro s
  have : (s.fst ≫ g₁) ≫ g₂ = s.snd ≫ i₃ := by
    rw [← s.condition, category.assoc]
  rcases pullback_cone.is_limit.lift' H (s.fst ≫ g₁) s.snd this with ⟨l₁, hl₁, hl₁'⟩
  rcases pullback_cone.is_limit.lift' H' s.fst l₁ hl₁.symm with ⟨l₂, hl₂, hl₂'⟩
  use l₂
  use hl₂
  use
    show l₂ ≫ f₁ ≫ f₂ = s.snd by
      rw [← hl₁', ← hl₂', category.assoc]
      rfl
  intro m hm₁ hm₂
  apply pullback_cone.is_limit.hom_ext H'
  · erw [hm₁, hl₂]
    
  · apply pullback_cone.is_limit.hom_ext H
    · erw [category.assoc, ← h₁, ← category.assoc, hm₁, ← hl₂, category.assoc, category.assoc, h₁]
      rfl
      
    · erw [category.assoc, hm₂, ← hl₁', ← hl₂']
      
    

/-- Given

X₁ - f₁ -> X₂ - f₂ -> X₃
|          |          |
i₁         i₂         i₃
∨          ∨          ∨
Y₁ - g₁ -> Y₂ - g₂ -> Y₃

Then the big square is a pushout if both the small squares are.
-/
def bigSquareIsPushout (H : IsColimit (PushoutCocone.mk _ _ h₂)) (H' : IsColimit (PushoutCocone.mk _ _ h₁)) :
    IsColimit
      (PushoutCocone.mk _ _
        (show i₁ ≫ g₁ ≫ g₂ = (f₁ ≫ f₂) ≫ i₃ by
          rw [← category.assoc, h₁, category.assoc, h₂, category.assoc])) :=
  by
  fapply pushout_cocone.is_colimit_aux'
  intro s
  have : i₁ ≫ s.inl = f₁ ≫ f₂ ≫ s.inr := by
    rw [s.condition, category.assoc]
  rcases pushout_cocone.is_colimit.desc' H' s.inl (f₂ ≫ s.inr) this with ⟨l₁, hl₁, hl₁'⟩
  rcases pushout_cocone.is_colimit.desc' H l₁ s.inr hl₁' with ⟨l₂, hl₂, hl₂'⟩
  use l₂
  use
    show (g₁ ≫ g₂) ≫ l₂ = s.inl by
      rw [← hl₁, ← hl₂, category.assoc]
      rfl
  use hl₂'
  intro m hm₁ hm₂
  apply pushout_cocone.is_colimit.hom_ext H
  · apply pushout_cocone.is_colimit.hom_ext H'
    · erw [← category.assoc, hm₁, hl₂, hl₁]
      
    · erw [← category.assoc, h₂, category.assoc, hm₂, ← hl₂', ← category.assoc, ← category.assoc, ← h₂]
      rfl
      
    
  · erw [hm₂, hl₂']
    

/-- Given

X₁ - f₁ -> X₂ - f₂ -> X₃
|          |          |
i₁         i₂         i₃
∨          ∨          ∨
Y₁ - g₁ -> Y₂ - g₂ -> Y₃

Then the left square is a pullback if the right square and the big square are.
-/
def leftSquareIsPullback (H : IsLimit (PullbackCone.mk _ _ h₂))
    (H' :
      IsLimit
        (PullbackCone.mk _ _
          (show i₁ ≫ g₁ ≫ g₂ = (f₁ ≫ f₂) ≫ i₃ by
            rw [← category.assoc, h₁, category.assoc, h₂, category.assoc]))) :
    IsLimit (PullbackCone.mk _ _ h₁) := by
  fapply pullback_cone.is_limit_aux'
  intro s
  have : s.fst ≫ g₁ ≫ g₂ = (s.snd ≫ f₂) ≫ i₃ := by
    rw [← category.assoc, s.condition, category.assoc, category.assoc, h₂]
  rcases pullback_cone.is_limit.lift' H' s.fst (s.snd ≫ f₂) this with ⟨l₁, hl₁, hl₁'⟩
  use l₁
  use hl₁
  constructor
  · apply pullback_cone.is_limit.hom_ext H
    · erw [category.assoc, ← h₁, ← category.assoc, hl₁, s.condition]
      rfl
      
    · erw [category.assoc, hl₁']
      rfl
      
    
  · intro m hm₁ hm₂
    apply pullback_cone.is_limit.hom_ext H'
    · erw [hm₁, hl₁]
      
    · erw [hl₁', ← hm₂]
      exact (category.assoc _ _ _).symm
      
    

/-- Given

X₁ - f₁ -> X₂ - f₂ -> X₃
|          |          |
i₁         i₂         i₃
∨          ∨          ∨
Y₁ - g₁ -> Y₂ - g₂ -> Y₃

Then the right square is a pushout if the left square and the big square are.
-/
def rightSquareIsPushout (H : IsColimit (PushoutCocone.mk _ _ h₁))
    (H' :
      IsColimit
        (PushoutCocone.mk _ _
          (show i₁ ≫ g₁ ≫ g₂ = (f₁ ≫ f₂) ≫ i₃ by
            rw [← category.assoc, h₁, category.assoc, h₂, category.assoc]))) :
    IsColimit (PushoutCocone.mk _ _ h₂) := by
  fapply pushout_cocone.is_colimit_aux'
  intro s
  have : i₁ ≫ g₁ ≫ s.inl = (f₁ ≫ f₂) ≫ s.inr := by
    rw [category.assoc, ← s.condition, ← category.assoc, ← category.assoc, h₁]
  rcases pushout_cocone.is_colimit.desc' H' (g₁ ≫ s.inl) s.inr this with ⟨l₁, hl₁, hl₁'⟩
  dsimp'  at *
  use l₁
  refine' ⟨_, _, _⟩
  · apply pushout_cocone.is_colimit.hom_ext H
    · erw [← category.assoc, hl₁]
      rfl
      
    · erw [← category.assoc, h₂, category.assoc, hl₁', s.condition]
      
    
  · exact hl₁'
    
  · intro m hm₁ hm₂
    apply pushout_cocone.is_colimit.hom_ext H'
    · erw [hl₁, category.assoc, hm₁]
      
    · erw [hm₂, hl₁']
      
    

end PasteLemma

section

variable (f : X ⟶ Z) (g : Y ⟶ Z) (f' : W ⟶ X)

variable [HasPullback f g] [HasPullback f' (pullback.fst : pullback f g ⟶ _)]

variable [HasPullback (f' ≫ f) g]

/-- The canonical isomorphism `W ×[X] (X ×[Z] Y) ≅ W ×[Z] Y` -/
noncomputable def pullbackRightPullbackFstIso : pullback f' (pullback.fst : pullback f g ⟶ _) ≅ pullback (f' ≫ f) g :=
  by
  let this :=
    big_square_is_pullback (pullback.snd : pullback f' (pullback.fst : pullback f g ⟶ _) ⟶ _) pullback.snd f' f
      pullback.fst pullback.fst g pullback.condition pullback.condition (pullback_is_pullback _ _)
      (pullback_is_pullback _ _)
  exact (this.cone_point_unique_up_to_iso (pullback_is_pullback _ _) : _)

@[simp, reassoc]
theorem pullback_right_pullback_fst_iso_hom_fst :
    (pullbackRightPullbackFstIso f g f').Hom ≫ pullback.fst = pullback.fst :=
  IsLimit.cone_point_unique_up_to_iso_hom_comp _ _ WalkingCospan.left

@[simp, reassoc]
theorem pullback_right_pullback_fst_iso_hom_snd :
    (pullbackRightPullbackFstIso f g f').Hom ≫ pullback.snd = pullback.snd ≫ pullback.snd :=
  IsLimit.cone_point_unique_up_to_iso_hom_comp _ _ WalkingCospan.right

@[simp, reassoc]
theorem pullback_right_pullback_fst_iso_inv_fst :
    (pullbackRightPullbackFstIso f g f').inv ≫ pullback.fst = pullback.fst :=
  IsLimit.cone_point_unique_up_to_iso_inv_comp _ _ WalkingCospan.left

@[simp, reassoc]
theorem pullback_right_pullback_fst_iso_inv_snd_snd :
    (pullbackRightPullbackFstIso f g f').inv ≫ pullback.snd ≫ pullback.snd = pullback.snd :=
  IsLimit.cone_point_unique_up_to_iso_inv_comp _ _ WalkingCospan.right

@[simp, reassoc]
theorem pullback_right_pullback_fst_iso_inv_snd_fst :
    (pullbackRightPullbackFstIso f g f').inv ≫ pullback.snd ≫ pullback.fst = pullback.fst ≫ f' := by
  rw [← pullback.condition]
  exact pullback_right_pullback_fst_iso_inv_fst_assoc _ _ _ _

end

section

variable (f : X ⟶ Y) (g : X ⟶ Z) (g' : Z ⟶ W)

variable [HasPushout f g] [HasPushout (pushout.inr : _ ⟶ pushout f g) g']

variable [HasPushout f (g ≫ g')]

/-- The canonical isomorphism `(Y ⨿[X] Z) ⨿[Z] W ≅ Y ×[X] W` -/
noncomputable def pushoutLeftPushoutInrIso : pushout (pushout.inr : _ ⟶ pushout f g) g' ≅ pushout f (g ≫ g') :=
  ((bigSquareIsPushout g g' _ _ f _ _ pushout.condition pushout.condition (pushoutIsPushout _ _)
        (pushoutIsPushout _ _)).coconePointUniqueUpToIso
    (pushoutIsPushout _ _) :
    _)

@[simp, reassoc]
theorem inl_pushout_left_pushout_inr_iso_inv :
    pushout.inl ≫ (pushoutLeftPushoutInrIso f g g').inv = pushout.inl ≫ pushout.inl :=
  ((bigSquareIsPushout g g' _ _ f _ _ pushout.condition pushout.condition (pushoutIsPushout _ _)
        (pushoutIsPushout _ _)).comp_cocone_point_unique_up_to_iso_inv
    (pushoutIsPushout _ _) WalkingSpan.left :
    _)

@[simp, reassoc]
theorem inr_pushout_left_pushout_inr_iso_hom : pushout.inr ≫ (pushoutLeftPushoutInrIso f g g').Hom = pushout.inr :=
  ((bigSquareIsPushout g g' _ _ f _ _ pushout.condition pushout.condition (pushoutIsPushout _ _)
        (pushoutIsPushout _ _)).comp_cocone_point_unique_up_to_iso_hom
    (pushoutIsPushout _ _) WalkingSpan.right :
    _)

@[simp, reassoc]
theorem inr_pushout_left_pushout_inr_iso_inv : pushout.inr ≫ (pushoutLeftPushoutInrIso f g g').inv = pushout.inr := by
  rw [iso.comp_inv_eq, inr_pushout_left_pushout_inr_iso_hom]

@[simp, reassoc]
theorem inl_inl_pushout_left_pushout_inr_iso_hom :
    pushout.inl ≫ pushout.inl ≫ (pushoutLeftPushoutInrIso f g g').Hom = pushout.inl := by
  rw [← category.assoc, ← iso.eq_comp_inv, inl_pushout_left_pushout_inr_iso_inv]

@[simp, reassoc]
theorem inr_inl_pushout_left_pushout_inr_iso_hom :
    pushout.inr ≫ pushout.inl ≫ (pushoutLeftPushoutInrIso f g g').Hom = g' ≫ pushout.inr := by
  rw [← category.assoc, ← iso.eq_comp_inv, category.assoc, inr_pushout_left_pushout_inr_iso_inv, pushout.condition]

end

section PullbackAssoc

/-
The objects and morphisms are as follows:

           Z₂ - g₄ -> X₃
           |          |
           g₃         f₄
           ∨          ∨
Z₁ - g₂ -> X₂ - f₃ -> Y₂
|          |
g₁         f₂
∨          ∨
X₁ - f₁ -> Y₁

where the two squares are pullbacks.

We can then construct the pullback squares

W  - l₂ -> Z₂ - g₄ -> X₃
|                     |
l₁                    f₄
∨                     ∨
Z₁ - g₂ -> X₂ - f₃ -> Y₂

and

W' - l₂' -> Z₂
|           |
l₁'         g₃
∨           ∨
Z₁          X₂
|           |
g₁          f₂
∨           ∨
X₁ -  f₁ -> Y₁

We will show that both `W` and `W'` are pullbacks over `g₁, g₂`, and thus we may construct a
canonical isomorphism between them. -/
variable {X₁ X₂ X₃ Y₁ Y₂ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₁) (f₃ : X₂ ⟶ Y₂)

variable (f₄ : X₃ ⟶ Y₂) [HasPullback f₁ f₂] [HasPullback f₃ f₄]

include f₁ f₂ f₃ f₄

-- mathport name: «exprZ₁»
local notation "Z₁" => pullback f₁ f₂

-- mathport name: «exprZ₂»
local notation "Z₂" => pullback f₃ f₄

-- mathport name: «exprg₁»
local notation "g₁" => (pullback.fst : Z₁ ⟶ X₁)

-- mathport name: «exprg₂»
local notation "g₂" => (pullback.snd : Z₁ ⟶ X₂)

-- mathport name: «exprg₃»
local notation "g₃" => (pullback.fst : Z₂ ⟶ X₂)

-- mathport name: «exprg₄»
local notation "g₄" => (pullback.snd : Z₂ ⟶ X₃)

-- mathport name: «exprW»
local notation "W" => pullback (g₂ ≫ f₃) f₄

-- mathport name: «exprW'»
local notation "W'" => pullback f₁ (g₃ ≫ f₂)

-- mathport name: «exprl₁»
local notation "l₁" => (pullback.fst : W ⟶ Z₁)

-- mathport name: «exprl₂»
local notation "l₂" =>
  (pullback.lift (pullback.fst ≫ g₂) pullback.snd ((Category.assoc _ _ _).trans pullback.condition) : W ⟶ Z₂)

-- mathport name: «exprl₁'»
local notation "l₁'" =>
  (pullback.lift pullback.fst (pullback.snd ≫ g₃) (pullback.condition.trans (Category.assoc _ _ _).symm) : W' ⟶ Z₁)

-- mathport name: «exprl₂'»
local notation "l₂'" => (pullback.snd : W' ⟶ Z₂)

/-- `(X₁ ×[Y₁] X₂) ×[Y₂] X₃` is the pullback `(X₁ ×[Y₁] X₂) ×[X₂] (X₂ ×[Y₂] X₃)`. -/
def pullbackPullbackLeftIsPullback [HasPullback (g₂ ≫ f₃) f₄] :
    IsLimit (PullbackCone.mk l₁ l₂ (show l₁ ≫ g₂ = l₂ ≫ g₃ from (pullback.lift_fst _ _ _).symm)) := by
  apply left_square_is_pullback
  exact pullback_is_pullback f₃ f₄
  convert pullback_is_pullback (g₂ ≫ f₃) f₄
  rw [pullback.lift_snd]

/-- `(X₁ ×[Y₁] X₂) ×[Y₂] X₃` is the pullback `X₁ ×[Y₁] (X₂ ×[Y₂] X₃)`. -/
def pullbackAssocIsPullback [HasPullback (g₂ ≫ f₃) f₄] :
    IsLimit
      (PullbackCone.mk (l₁ ≫ g₁) l₂
        (show (l₁ ≫ g₁) ≫ f₁ = l₂ ≫ g₃ ≫ f₂ by
          rw [pullback.lift_fst_assoc, category.assoc, category.assoc, pullback.condition])) :=
  by
  apply pullback_cone.flip_is_limit
  apply big_square_is_pullback
  · apply pullback_cone.flip_is_limit
    exact pullback_is_pullback f₁ f₂
    
  · apply pullback_cone.flip_is_limit
    apply pullback_pullback_left_is_pullback
    
  · exact pullback.lift_fst _ _ _
    
  · exact pullback.condition.symm
    

theorem has_pullback_assoc [HasPullback (g₂ ≫ f₃) f₄] : HasPullback f₁ (g₃ ≫ f₂) :=
  ⟨⟨⟨_, pullbackAssocIsPullback f₁ f₂ f₃ f₄⟩⟩⟩

/-- `X₁ ×[Y₁] (X₂ ×[Y₂] X₃)` is the pullback `(X₁ ×[Y₁] X₂) ×[X₂] (X₂ ×[Y₂] X₃)`. -/
def pullbackPullbackRightIsPullback [HasPullback f₁ (g₃ ≫ f₂)] :
    IsLimit (PullbackCone.mk l₁' l₂' (show l₁' ≫ g₂ = l₂' ≫ g₃ from pullback.lift_snd _ _ _)) := by
  apply pullback_cone.flip_is_limit
  apply left_square_is_pullback
  · apply pullback_cone.flip_is_limit
    exact pullback_is_pullback f₁ f₂
    
  · apply pullback_cone.flip_is_limit
    convert pullback_is_pullback f₁ (g₃ ≫ f₂)
    rw [pullback.lift_fst]
    
  · exact pullback.condition.symm
    

/-- `X₁ ×[Y₁] (X₂ ×[Y₂] X₃)` is the pullback `(X₁ ×[Y₁] X₂) ×[Y₂] X₃`. -/
def pullbackAssocSymmIsPullback [HasPullback f₁ (g₃ ≫ f₂)] :
    IsLimit
      (PullbackCone.mk l₁' (l₂' ≫ g₄)
        (show l₁' ≫ g₂ ≫ f₃ = (l₂' ≫ g₄) ≫ f₄ by
          rw [pullback.lift_snd_assoc, category.assoc, category.assoc, pullback.condition])) :=
  by
  apply big_square_is_pullback
  exact pullback_is_pullback f₃ f₄
  apply pullback_pullback_right_is_pullback

theorem has_pullback_assoc_symm [HasPullback f₁ (g₃ ≫ f₂)] : HasPullback (g₂ ≫ f₃) f₄ :=
  ⟨⟨⟨_, pullbackAssocSymmIsPullback f₁ f₂ f₃ f₄⟩⟩⟩

variable [HasPullback (g₂ ≫ f₃) f₄] [HasPullback f₁ (g₃ ≫ f₂)]

/-- The canonical isomorphism `(X₁ ×[Y₁] X₂) ×[Y₂] X₃ ≅ X₁ ×[Y₁] (X₂ ×[Y₂] X₃)`. -/
noncomputable def pullbackAssoc :
    pullback (pullback.snd ≫ f₃ : pullback f₁ f₂ ⟶ _) f₄ ≅ pullback f₁ (pullback.fst ≫ f₂ : pullback f₃ f₄ ⟶ _) :=
  (pullbackPullbackLeftIsPullback f₁ f₂ f₃ f₄).conePointUniqueUpToIso (pullbackPullbackRightIsPullback f₁ f₂ f₃ f₄)

@[simp, reassoc]
theorem pullback_assoc_inv_fst_fst : (pullbackAssoc f₁ f₂ f₃ f₄).inv ≫ pullback.fst ≫ pullback.fst = pullback.fst := by
  trans l₁' ≫ pullback.fst
  rw [← category.assoc]
  congr 1
  exact is_limit.cone_point_unique_up_to_iso_inv_comp _ _ walking_cospan.left
  exact pullback.lift_fst _ _ _

@[simp, reassoc]
theorem pullback_assoc_hom_fst : (pullbackAssoc f₁ f₂ f₃ f₄).Hom ≫ pullback.fst = pullback.fst ≫ pullback.fst := by
  rw [← iso.eq_inv_comp, pullback_assoc_inv_fst_fst]

@[simp, reassoc]
theorem pullback_assoc_hom_snd_fst :
    (pullbackAssoc f₁ f₂ f₃ f₄).Hom ≫ pullback.snd ≫ pullback.fst = pullback.fst ≫ pullback.snd := by
  trans l₂ ≫ pullback.fst
  rw [← category.assoc]
  congr 1
  exact is_limit.cone_point_unique_up_to_iso_hom_comp _ _ walking_cospan.right
  exact pullback.lift_fst _ _ _

@[simp, reassoc]
theorem pullback_assoc_hom_snd_snd : (pullbackAssoc f₁ f₂ f₃ f₄).Hom ≫ pullback.snd ≫ pullback.snd = pullback.snd := by
  trans l₂ ≫ pullback.snd
  rw [← category.assoc]
  congr 1
  exact is_limit.cone_point_unique_up_to_iso_hom_comp _ _ walking_cospan.right
  exact pullback.lift_snd _ _ _

@[simp, reassoc]
theorem pullback_assoc_inv_fst_snd :
    (pullbackAssoc f₁ f₂ f₃ f₄).inv ≫ pullback.fst ≫ pullback.snd = pullback.snd ≫ pullback.fst := by
  rw [iso.inv_comp_eq, pullback_assoc_hom_snd_fst]

@[simp, reassoc]
theorem pullback_assoc_inv_snd : (pullbackAssoc f₁ f₂ f₃ f₄).inv ≫ pullback.snd = pullback.snd ≫ pullback.snd := by
  rw [iso.inv_comp_eq, pullback_assoc_hom_snd_snd]

end PullbackAssoc

section PushoutAssoc

/-
The objects and morphisms are as follows:

           Z₂ - g₄ -> X₃
           |          |
           g₃         f₄
           ∨          ∨
Z₁ - g₂ -> X₂ - f₃ -> Y₂
|          |
g₁         f₂
∨          ∨
X₁ - f₁ -> Y₁

where the two squares are pushouts.

We can then construct the pushout squares

Z₁ - g₂ -> X₂ - f₃ -> Y₂
|                     |
g₁                    l₂
∨                     ∨
X₁ - f₁ -> Y₁ - l₁ -> W

and

Z₂ - g₄  -> X₃
|           |
g₃          f₄
∨           ∨
X₂          Y₂
|           |
f₂          l₂'
∨           ∨
Y₁ - l₁' -> W'

We will show that both `W` and `W'` are pushouts over `f₂, f₃`, and thus we may construct a
canonical isomorphism between them. -/
variable {X₁ X₂ X₃ Z₁ Z₂ : C} (g₁ : Z₁ ⟶ X₁) (g₂ : Z₁ ⟶ X₂) (g₃ : Z₂ ⟶ X₂)

variable (g₄ : Z₂ ⟶ X₃) [HasPushout g₁ g₂] [HasPushout g₃ g₄]

include g₁ g₂ g₃ g₄

-- mathport name: «exprY₁»
local notation "Y₁" => pushout g₁ g₂

-- mathport name: «exprY₂»
local notation "Y₂" => pushout g₃ g₄

-- mathport name: «exprf₁»
local notation "f₁" => (pushout.inl : X₁ ⟶ Y₁)

-- mathport name: «exprf₂»
local notation "f₂" => (pushout.inr : X₂ ⟶ Y₁)

-- mathport name: «exprf₃»
local notation "f₃" => (pushout.inl : X₂ ⟶ Y₂)

-- mathport name: «exprf₄»
local notation "f₄" => (pushout.inr : X₃ ⟶ Y₂)

-- mathport name: «exprW»
local notation "W" => pushout g₁ (g₂ ≫ f₃)

-- mathport name: «exprW'»
local notation "W'" => pushout (g₃ ≫ f₂) g₄

-- mathport name: «exprl₁»
local notation "l₁" =>
  (pushout.desc pushout.inl (f₃ ≫ pushout.inr) (pushout.condition.trans (Category.assoc _ _ _)) : Y₁ ⟶ W)

-- mathport name: «exprl₂»
local notation "l₂" => (pushout.inr : Y₂ ⟶ W)

-- mathport name: «exprl₁'»
local notation "l₁'" => (pushout.inl : Y₁ ⟶ W')

-- mathport name: «exprl₂'»
local notation "l₂'" =>
  (pushout.desc (f₂ ≫ pushout.inl) pushout.inr ((Category.assoc _ _ _).symm.trans pushout.condition) : Y₂ ⟶ W')

/-- `(X₁ ⨿[Z₁] X₂) ⨿[Z₂] X₃` is the pushout `(X₁ ⨿[Z₁] X₂) ×[X₂] (X₂ ⨿[Z₂] X₃)`. -/
def pushoutPushoutLeftIsPushout [HasPushout (g₃ ≫ f₂) g₄] :
    IsColimit (PushoutCocone.mk l₁' l₂' (show f₂ ≫ l₁' = f₃ ≫ l₂' from (pushout.inl_desc _ _ _).symm)) := by
  apply pushout_cocone.flip_is_colimit
  apply right_square_is_pushout
  · apply pushout_cocone.flip_is_colimit
    exact pushout_is_pushout _ _
    
  · apply pushout_cocone.flip_is_colimit
    convert pushout_is_pushout (g₃ ≫ f₂) g₄
    exact pushout.inr_desc _ _ _
    
  · exact pushout.condition.symm
    

/-- `(X₁ ⨿[Z₁] X₂) ⨿[Z₂] X₃` is the pushout `X₁ ⨿[Z₁] (X₂ ⨿[Z₂] X₃)`. -/
def pushoutAssocIsPushout [HasPushout (g₃ ≫ f₂) g₄] :
    IsColimit
      (PushoutCocone.mk (f₁ ≫ l₁') l₂'
        (show g₁ ≫ f₁ ≫ l₁' = (g₂ ≫ f₃) ≫ l₂' by
          rw [category.assoc, pushout.inl_desc, pushout.condition_assoc])) :=
  by
  apply big_square_is_pushout
  · apply pushout_pushout_left_is_pushout
    
  · exact pushout_is_pushout _ _
    

theorem has_pushout_assoc [HasPushout (g₃ ≫ f₂) g₄] : HasPushout g₁ (g₂ ≫ f₃) :=
  ⟨⟨⟨_, pushoutAssocIsPushout g₁ g₂ g₃ g₄⟩⟩⟩

/-- `X₁ ⨿[Z₁] (X₂ ⨿[Z₂] X₃)` is the pushout `(X₁ ⨿[Z₁] X₂) ×[X₂] (X₂ ⨿[Z₂] X₃)`. -/
def pushoutPushoutRightIsPushout [HasPushout g₁ (g₂ ≫ f₃)] :
    IsColimit (PushoutCocone.mk l₁ l₂ (show f₂ ≫ l₁ = f₃ ≫ l₂ from pushout.inr_desc _ _ _)) := by
  apply right_square_is_pushout
  · exact pushout_is_pushout _ _
    
  · convert pushout_is_pushout g₁ (g₂ ≫ f₃)
    rw [pushout.inl_desc]
    

/-- `X₁ ⨿[Z₁] (X₂ ⨿[Z₂] X₃)` is the pushout `(X₁ ⨿[Z₁] X₂) ⨿[Z₂] X₃`. -/
def pushoutAssocSymmIsPushout [HasPushout g₁ (g₂ ≫ f₃)] :
    IsColimit
      (PushoutCocone.mk l₁ (f₄ ≫ l₂)
        (show (g₃ ≫ f₂) ≫ l₁ = g₄ ≫ f₄ ≫ l₂ by
          rw [category.assoc, pushout.inr_desc, pushout.condition_assoc])) :=
  by
  apply pushout_cocone.flip_is_colimit
  apply big_square_is_pushout
  · apply pushout_cocone.flip_is_colimit
    apply pushout_pushout_right_is_pushout
    
  · apply pushout_cocone.flip_is_colimit
    exact pushout_is_pushout _ _
    
  · exact pushout.condition.symm
    
  · exact (pushout.inr_desc _ _ _).symm
    

theorem has_pushout_assoc_symm [HasPushout g₁ (g₂ ≫ f₃)] : HasPushout (g₃ ≫ f₂) g₄ :=
  ⟨⟨⟨_, pushoutAssocSymmIsPushout g₁ g₂ g₃ g₄⟩⟩⟩

variable [HasPushout (g₃ ≫ f₂) g₄] [HasPushout g₁ (g₂ ≫ f₃)]

/-- The canonical isomorphism `(X₁ ⨿[Z₁] X₂) ⨿[Z₂] X₃ ≅ X₁ ⨿[Z₁] (X₂ ⨿[Z₂] X₃)`. -/
noncomputable def pushoutAssoc :
    pushout (g₃ ≫ pushout.inr : _ ⟶ pushout g₁ g₂) g₄ ≅ pushout g₁ (g₂ ≫ pushout.inl : _ ⟶ pushout g₃ g₄) :=
  (pushoutPushoutLeftIsPushout g₁ g₂ g₃ g₄).coconePointUniqueUpToIso (pushoutPushoutRightIsPushout g₁ g₂ g₃ g₄)

@[simp, reassoc]
theorem inl_inl_pushout_assoc_hom : pushout.inl ≫ pushout.inl ≫ (pushoutAssoc g₁ g₂ g₃ g₄).Hom = pushout.inl := by
  trans f₁ ≫ l₁
  · congr 1
    exact (pushout_pushout_left_is_pushout g₁ g₂ g₃ g₄).comp_cocone_point_unique_up_to_iso_hom _ walking_cospan.left
    
  · exact pushout.inl_desc _ _ _
    

@[simp, reassoc]
theorem inr_inl_pushout_assoc_hom :
    pushout.inr ≫ pushout.inl ≫ (pushoutAssoc g₁ g₂ g₃ g₄).Hom = pushout.inl ≫ pushout.inr := by
  trans f₂ ≫ l₁
  · congr 1
    exact (pushout_pushout_left_is_pushout g₁ g₂ g₃ g₄).comp_cocone_point_unique_up_to_iso_hom _ walking_cospan.left
    
  · exact pushout.inr_desc _ _ _
    

@[simp, reassoc]
theorem inr_inr_pushout_assoc_inv : pushout.inr ≫ pushout.inr ≫ (pushoutAssoc g₁ g₂ g₃ g₄).inv = pushout.inr := by
  trans f₄ ≫ l₂'
  · congr 1
    exact
      (pushout_pushout_left_is_pushout g₁ g₂ g₃ g₄).comp_cocone_point_unique_up_to_iso_inv
        (pushout_pushout_right_is_pushout g₁ g₂ g₃ g₄) walking_cospan.right
    
  · exact pushout.inr_desc _ _ _
    

@[simp, reassoc]
theorem inl_pushout_assoc_inv : pushout.inl ≫ (pushoutAssoc g₁ g₂ g₃ g₄).inv = pushout.inl ≫ pushout.inl := by
  rw [iso.comp_inv_eq, category.assoc, inl_inl_pushout_assoc_hom]

@[simp, reassoc]
theorem inl_inr_pushout_assoc_inv :
    pushout.inl ≫ pushout.inr ≫ (pushoutAssoc g₁ g₂ g₃ g₄).inv = pushout.inr ≫ pushout.inl := by
  rw [← category.assoc, iso.comp_inv_eq, category.assoc, inr_inl_pushout_assoc_hom]

@[simp, reassoc]
theorem inr_pushout_assoc_hom : pushout.inr ≫ (pushoutAssoc g₁ g₂ g₃ g₄).Hom = pushout.inr ≫ pushout.inr := by
  rw [← iso.eq_comp_inv, category.assoc, inr_inr_pushout_assoc_inv]

end PushoutAssoc

variable (C)

/-- `has_pullbacks` represents a choice of pullback for every pair of morphisms

See <https://stacks.math.columbia.edu/tag/001W>
-/
abbrev HasPullbacks :=
  HasLimitsOfShape WalkingCospan C

/-- `has_pushouts` represents a choice of pushout for every pair of morphisms -/
abbrev HasPushouts :=
  HasColimitsOfShape WalkingSpan C

/-- If `C` has all limits of diagrams `cospan f g`, then it has all pullbacks -/
theorem has_pullbacks_of_has_limit_cospan [∀ {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}, HasLimit (cospan f g)] :
    HasPullbacks C :=
  { HasLimit := fun F => has_limit_of_iso (diagramIsoCospan F).symm }

/-- If `C` has all colimits of diagrams `span f g`, then it has all pushouts -/
theorem has_pushouts_of_has_colimit_span [∀ {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}, HasColimit (span f g)] :
    HasPushouts C :=
  { HasColimit := fun F => has_colimit_of_iso (diagramIsoSpan F) }

/-- The duality equivalence `walking_spanᵒᵖ ≌ walking_cospan` -/
@[simps]
def walkingSpanOpEquiv : walking_spanᵒᵖ ≌ walking_cospan :=
  widePushoutShapeOpEquiv _

/-- The duality equivalence `walking_cospanᵒᵖ ≌ walking_span` -/
@[simps]
def walkingCospanOpEquiv : walking_cospanᵒᵖ ≌ walking_span :=
  widePullbackShapeOpEquiv _

/-- Having wide pullback at any universe level implies having binary pullbacks. -/
-- see Note [lower instance priority]
instance (priority := 100) has_pullbacks_of_has_wide_pullbacks [HasWidePullbacks.{w} C] : HasPullbacks C := by
  have := has_wide_pullbacks_shrink.{0, w} C
  infer_instance

end CategoryTheory.Limits

