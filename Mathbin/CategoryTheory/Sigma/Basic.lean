/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathbin.CategoryTheory.Whiskering
import Mathbin.CategoryTheory.Functor.FullyFaithful
import Mathbin.CategoryTheory.NaturalIsomorphism
import Mathbin.Data.Sigma.Basic

/-!
# Disjoint union of categories

We define the category structure on a sigma-type (disjoint union) of categories.
-/


namespace CategoryTheory

namespace Sigma

universe w₁ w₂ w₃ v₁ v₂ u₁ u₂

variable {I : Type w₁} {C : I → Type u₁} [∀ i, Category.{v₁} (C i)]

/-- The type of morphisms of a disjoint union of categories: for `X : C i` and `Y : C j`, a morphism
`(i, X) ⟶ (j, Y)` if `i = j` is just a morphism `X ⟶ Y`, and if `i ≠ j` there are no such morphisms.
-/
inductive SigmaHom : (Σi, C i) → (Σi, C i) → Type max w₁ v₁ u₁
  | mk : ∀ {i : I} {X Y : C i}, (X ⟶ Y) → sigma_hom ⟨i, X⟩ ⟨i, Y⟩

namespace SigmaHom

/-- The identity morphism on an object. -/
def idₓ : ∀ X : Σi, C i, SigmaHom X X
  | ⟨i, X⟩ => mk (𝟙 _)

instance (X : Σi, C i) : Inhabited (SigmaHom X X) :=
  ⟨idₓ X⟩

/-- Composition of sigma homomorphisms. -/
def compₓ : ∀ {X Y Z : Σi, C i}, SigmaHom X Y → SigmaHom Y Z → SigmaHom X Z
  | _, _, _, mk f, mk g => mk (f ≫ g)

instance : CategoryStruct (Σi, C i) where
  Hom := SigmaHom
  id := idₓ
  comp := fun X Y Z f g => compₓ f g

@[simp]
theorem comp_def (i : I) (X Y Z : C i) (f : X ⟶ Y) (g : Y ⟶ Z) : compₓ (mk f) (mk g) = mk (f ≫ g) :=
  rfl

theorem assoc : ∀ (X Y Z W : Σi, C i) (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W), (f ≫ g) ≫ h = f ≫ g ≫ h
  | _, _, _, _, mk f, mk g, mk h => congr_arg mk (Category.assoc _ _ _)

theorem id_comp : ∀ (X Y : Σi, C i) (f : X ⟶ Y), 𝟙 X ≫ f = f
  | _, _, mk f => congr_arg mk (Category.id_comp _)

theorem comp_id : ∀ (X Y : Σi, C i) (f : X ⟶ Y), f ≫ 𝟙 Y = f
  | _, _, mk f => congr_arg mk (Category.comp_id _)

end SigmaHom

instance sigma : Category (Σi, C i) where
  id_comp' := SigmaHom.id_comp
  comp_id' := SigmaHom.comp_id
  assoc' := SigmaHom.assoc

/-- The inclusion functor into the disjoint union of categories. -/
@[simps map]
def incl (i : I) : C i ⥤ Σi, C i where
  obj := fun X => ⟨i, X⟩
  map := fun X Y => SigmaHom.mk

@[simp]
theorem incl_obj {i : I} (X : C i) : (incl i).obj X = ⟨i, X⟩ :=
  rfl

instance (i : I) : Full (incl i : C i ⥤ Σi, C i) where
  preimage := fun X Y ⟨f⟩ => f
  witness' := fun X Y ⟨f⟩ => rfl

instance (i : I) : Faithful (incl i : C i ⥤ Σi, C i) where

section

variable {D : Type u₂} [Category.{v₂} D] (F : ∀ i, C i ⥤ D)

/-- To build a natural transformation over the sigma category, it suffices to specify it restricted to
each subcategory.
-/
def natTrans {F G : (Σi, C i) ⥤ D} (h : ∀ i : I, incl i ⋙ F ⟶ incl i ⋙ G) : F ⟶ G where
  app := fun ⟨j, X⟩ => (h j).app X
  naturality' := by
    rintro ⟨j, X⟩ ⟨_, _⟩ ⟨_, _, Y, f⟩
    apply (h j).naturality

@[simp]
theorem nat_trans_app {F G : (Σi, C i) ⥤ D} (h : ∀ i : I, incl i ⋙ F ⟶ incl i ⋙ G) (i : I) (X : C i) :
    (natTrans h).app ⟨i, X⟩ = (h i).app X :=
  rfl

/-- (Implementation). An auxiliary definition to build the functor `desc`. -/
def descMapₓ : ∀ X Y : Σi, C i, (X ⟶ Y) → ((F X.1).obj X.2 ⟶ (F Y.1).obj Y.2)
  | _, _, sigma_hom.mk g => (F _).map g

/-- Given a collection of functors `F i : C i ⥤ D`, we can produce a functor `(Σ i, C i) ⥤ D`.

The produced functor `desc F` satisfies: `incl i ⋙ desc F ≅ F i`, i.e. restricted to just the
subcategory `C i`, `desc F` agrees with `F i`, and it is unique (up to natural isomorphism) with
this property.

This witnesses that the sigma-type is the coproduct in Cat.
-/
@[simps obj]
def desc : (Σi, C i) ⥤ D where
  obj := fun X => (F X.1).obj X.2
  map := fun X Y g => descMapₓ F X Y g
  map_id' := by
    rintro ⟨i, X⟩
    apply (F i).map_id
  map_comp' := by
    rintro ⟨i, X⟩ ⟨_, Y⟩ ⟨_, Z⟩ ⟨i, _, Y, f⟩ ⟨_, _, Z, g⟩
    apply (F i).map_comp

@[simp]
theorem desc_map_mk {i : I} (X Y : C i) (f : X ⟶ Y) : (desc F).map (SigmaHom.mk f) = (F i).map f :=
  rfl

/-- This shows that when `desc F` is restricted to just the subcategory `C i`, `desc F` agrees with
`F i`.
-/
-- We hand-generate the simp lemmas about this since they come out cleaner.
def inclDesc (i : I) : incl i ⋙ desc F ≅ F i :=
  NatIso.ofComponents (fun X => Iso.refl _)
    (by
      tidy)

@[simp]
theorem incl_desc_hom_app (i : I) (X : C i) : (inclDesc F i).Hom.app X = 𝟙 ((F i).obj X) :=
  rfl

@[simp]
theorem incl_desc_inv_app (i : I) (X : C i) : (inclDesc F i).inv.app X = 𝟙 ((F i).obj X) :=
  rfl

/-- If `q` when restricted to each subcategory `C i` agrees with `F i`, then `q` is isomorphic to
`desc F`.
-/
def descUniq (q : (Σi, C i) ⥤ D) (h : ∀ i, incl i ⋙ q ≅ F i) : q ≅ desc F :=
  (NatIso.ofComponents fun ⟨i, X⟩ => (h i).app X) <| by
    rintro ⟨i, X⟩ ⟨_, _⟩ ⟨_, _, Y, f⟩
    apply (h i).Hom.naturality f

@[simp]
theorem desc_uniq_hom_app (q : (Σi, C i) ⥤ D) (h : ∀ i, incl i ⋙ q ≅ F i) (i : I) (X : C i) :
    (descUniq F q h).Hom.app ⟨i, X⟩ = (h i).Hom.app X :=
  rfl

@[simp]
theorem desc_uniq_inv_app (q : (Σi, C i) ⥤ D) (h : ∀ i, incl i ⋙ q ≅ F i) (i : I) (X : C i) :
    (descUniq F q h).inv.app ⟨i, X⟩ = (h i).inv.app X :=
  rfl

/-- If `q₁` and `q₂` when restricted to each subcategory `C i` agree, then `q₁` and `q₂` are isomorphic.
-/
@[simps]
def natIso {q₁ q₂ : (Σi, C i) ⥤ D} (h : ∀ i, incl i ⋙ q₁ ≅ incl i ⋙ q₂) : q₁ ≅ q₂ where
  Hom := natTrans fun i => (h i).Hom
  inv := natTrans fun i => (h i).inv

end

section

variable (C) {J : Type w₂} (g : J → I)

/-- A function `J → I` induces a functor `Σ j, C (g j) ⥤ Σ i, C i`. -/
def map : (Σj : J, C (g j)) ⥤ Σi : I, C i :=
  desc fun j => incl (g j)

@[simp]
theorem map_obj (j : J) (X : C (g j)) : (Sigma.map C g).obj ⟨j, X⟩ = ⟨g j, X⟩ :=
  rfl

@[simp]
theorem map_map {j : J} {X Y : C (g j)} (f : X ⟶ Y) : (Sigma.map C g).map (SigmaHom.mk f) = SigmaHom.mk f :=
  rfl

/-- The functor `sigma.map C g` restricted to the subcategory `C j` acts as the inclusion of `g j`.
-/
@[simps]
def inclCompMap (j : J) : incl j ⋙ map C g ≅ incl (g j) :=
  Iso.refl _

variable (I)

/-- The functor `sigma.map` applied to the identity function is just the identity functor. -/
@[simps]
def mapId : map C (id : I → I) ≅ 𝟭 (Σi, C i) :=
  natIso fun i =>
    NatIso.ofComponents (fun X => Iso.refl _)
      (by
        tidy)

variable {I} {K : Type w₃}

/-- The functor `sigma.map` applied to a composition is a composition of functors. -/
@[simps]
def mapComp (f : K → J) (g : J → I) : map (C ∘ g) f ⋙ (map C g : _) ≅ map C (g ∘ f) :=
  (descUniq _ _) fun k => (isoWhiskerRight (inclCompMap (C ∘ g) f k) (map C g : _) : _) ≪≫ inclCompMap _ _ _

end

namespace Functor

variable {C}

variable {D : I → Type u₁} [∀ i, Category.{v₁} (D i)]

/-- Assemble an `I`-indexed family of functors into a functor between the sigma types.
-/
def sigma (F : ∀ i, C i ⥤ D i) : (Σi, C i) ⥤ Σi, D i :=
  desc fun i => F i ⋙ incl i

end Functor

namespace NatTrans

variable {C}

variable {D : I → Type u₁} [∀ i, Category.{v₁} (D i)]

variable {F G : ∀ i, C i ⥤ D i}

/-- Assemble an `I`-indexed family of natural transformations into a single natural transformation.
-/
def sigma (α : ∀ i, F i ⟶ G i) : Functor.sigma F ⟶ Functor.sigma G where
  app := fun f => SigmaHom.mk ((α f.1).app _)
  naturality' := by
    rintro ⟨i, X⟩ ⟨_, _⟩ ⟨_, _, Y, f⟩
    change sigma_hom.mk _ = sigma_hom.mk _
    rw [(α i).naturality]

end NatTrans

end Sigma

end CategoryTheory

