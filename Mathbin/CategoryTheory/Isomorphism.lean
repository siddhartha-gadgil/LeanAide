/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tim Baumann, Stephen Morgan, Scott Morrison, Floris van Doorn
-/
import Mathbin.CategoryTheory.Functor.Default

/-!
# Isomorphisms

This file defines isomorphisms between objects of a category.

## Main definitions

- `structure iso` : a bundled isomorphism between two objects of a category;
- `class is_iso` : an unbundled version of `iso`;
  note that `is_iso f` is a `Prop`, and only asserts the existence of an inverse.
  Of course, this inverse is unique, so it doesn't cost us much to use choice to retrieve it.
- `inv f`, for the inverse of a morphism with `[is_iso f]`
- `as_iso` : convert from `is_iso` to `iso` (noncomputable);
- `of_iso` : convert from `iso` to `is_iso`;
- standard operations on isomorphisms (composition, inverse etc)

## Notations

- `X ≅ Y` : same as `iso X Y`;
- `α ≪≫ β` : composition of two isomorphisms; it is called `iso.trans`

## Tags

category, category theory, isomorphism
-/


universe v u

-- morphism levels before object levels. See note [category_theory universes].
namespace CategoryTheory

open Category

/-- An isomorphism (a.k.a. an invertible morphism) between two objects of a category.
The inverse morphism is bundled.

See also `category_theory.core` for the category with the same objects and isomorphisms playing
the role of morphisms.

See <https://stacks.math.columbia.edu/tag/0017>.
-/
structure Iso {C : Type u} [Category.{v} C] (X Y : C) where
  Hom : X ⟶ Y
  inv : Y ⟶ X
  hom_inv_id' : hom ≫ inv = 𝟙 X := by
    run_tac
      obviously
  inv_hom_id' : inv ≫ hom = 𝟙 Y := by
    run_tac
      obviously

restate_axiom iso.hom_inv_id'

restate_axiom iso.inv_hom_id'

attribute [simp, reassoc] iso.hom_inv_id iso.inv_hom_id

-- mathport name: «expr ≅ »
infixr:10 " ≅ " => Iso

-- type as \cong or \iso
variable {C : Type u} [Category.{v} C]

variable {X Y Z : C}

namespace Iso

@[ext]
theorem ext ⦃α β : X ≅ Y⦄ (w : α.Hom = β.Hom) : α = β :=
  suffices α.inv = β.inv by
    cases α <;> cases β <;> cc
  calc
    α.inv = α.inv ≫ β.Hom ≫ β.inv := by
      rw [iso.hom_inv_id, category.comp_id]
    _ = (α.inv ≫ α.Hom) ≫ β.inv := by
      rw [category.assoc, ← w]
    _ = β.inv := by
      rw [iso.inv_hom_id, category.id_comp]
    

/-- Inverse isomorphism. -/
@[symm]
def symm (I : X ≅ Y) : Y ≅ X where
  Hom := I.inv
  inv := I.Hom
  hom_inv_id' := I.inv_hom_id'
  inv_hom_id' := I.hom_inv_id'

@[simp]
theorem symm_hom (α : X ≅ Y) : α.symm.Hom = α.inv :=
  rfl

@[simp]
theorem symm_inv (α : X ≅ Y) : α.symm.inv = α.Hom :=
  rfl

@[simp]
theorem symm_mk {X Y : C} (hom : X ⟶ Y) (inv : Y ⟶ X) (hom_inv_id) (inv_hom_id) :
    Iso.symm { Hom, inv, hom_inv_id' := hom_inv_id, inv_hom_id' := inv_hom_id } =
      { Hom := inv, inv := hom, hom_inv_id' := inv_hom_id, inv_hom_id' := hom_inv_id } :=
  rfl

@[simp]
theorem symm_symm_eq {X Y : C} (α : X ≅ Y) : α.symm.symm = α := by
  cases α <;> rfl

@[simp]
theorem symm_eq_iff {X Y : C} {α β : X ≅ Y} : α.symm = β.symm ↔ α = β :=
  ⟨fun h => symm_symm_eq α ▸ symm_symm_eq β ▸ congr_arg symm h, congr_arg symm⟩

/-- Identity isomorphism. -/
@[refl, simps]
def refl (X : C) : X ≅ X where
  Hom := 𝟙 X
  inv := 𝟙 X

instance : Inhabited (X ≅ X) :=
  ⟨Iso.refl X⟩

@[simp]
theorem refl_symm (X : C) : (Iso.refl X).symm = Iso.refl X :=
  rfl

/-- Composition of two isomorphisms -/
@[trans, simps]
def trans (α : X ≅ Y) (β : Y ≅ Z) : X ≅ Z where
  Hom := α.Hom ≫ β.Hom
  inv := β.inv ≫ α.inv

-- mathport name: «expr ≪≫ »
infixr:80 " ≪≫ " => Iso.trans

-- type as `\ll \gg`.
@[simp]
theorem trans_mk {X Y Z : C} (hom : X ⟶ Y) (inv : Y ⟶ X) (hom_inv_id) (inv_hom_id) (hom' : Y ⟶ Z) (inv' : Z ⟶ Y)
    (hom_inv_id') (inv_hom_id') (hom_inv_id'') (inv_hom_id'') :
    Iso.trans { Hom, inv, hom_inv_id' := hom_inv_id, inv_hom_id' := inv_hom_id }
        { Hom := hom', inv := inv', hom_inv_id', inv_hom_id' } =
      { Hom := hom ≫ hom', inv := inv' ≫ inv, hom_inv_id' := hom_inv_id'', inv_hom_id' := inv_hom_id'' } :=
  rfl

@[simp]
theorem trans_symm (α : X ≅ Y) (β : Y ≅ Z) : (α ≪≫ β).symm = β.symm ≪≫ α.symm :=
  rfl

@[simp]
theorem trans_assoc {Z' : C} (α : X ≅ Y) (β : Y ≅ Z) (γ : Z ≅ Z') : (α ≪≫ β) ≪≫ γ = α ≪≫ β ≪≫ γ := by
  ext <;> simp only [← trans_hom, ← category.assoc]

@[simp]
theorem refl_trans (α : X ≅ Y) : Iso.refl X ≪≫ α = α := by
  ext <;> apply category.id_comp

@[simp]
theorem trans_refl (α : X ≅ Y) : α ≪≫ Iso.refl Y = α := by
  ext <;> apply category.comp_id

@[simp]
theorem symm_self_id (α : X ≅ Y) : α.symm ≪≫ α = Iso.refl Y :=
  ext α.inv_hom_id

@[simp]
theorem self_symm_id (α : X ≅ Y) : α ≪≫ α.symm = Iso.refl X :=
  ext α.hom_inv_id

@[simp]
theorem symm_self_id_assoc (α : X ≅ Y) (β : Y ≅ Z) : α.symm ≪≫ α ≪≫ β = β := by
  rw [← trans_assoc, symm_self_id, refl_trans]

@[simp]
theorem self_symm_id_assoc (α : X ≅ Y) (β : X ≅ Z) : α ≪≫ α.symm ≪≫ β = β := by
  rw [← trans_assoc, self_symm_id, refl_trans]

theorem inv_comp_eq (α : X ≅ Y) {f : X ⟶ Z} {g : Y ⟶ Z} : α.inv ≫ f = g ↔ f = α.Hom ≫ g :=
  ⟨fun H => by
    simp [← H.symm], fun H => by
    simp [← H]⟩

theorem eq_inv_comp (α : X ≅ Y) {f : X ⟶ Z} {g : Y ⟶ Z} : g = α.inv ≫ f ↔ α.Hom ≫ g = f :=
  (inv_comp_eq α.symm).symm

theorem comp_inv_eq (α : X ≅ Y) {f : Z ⟶ Y} {g : Z ⟶ X} : f ≫ α.inv = g ↔ f = g ≫ α.Hom :=
  ⟨fun H => by
    simp [← H.symm], fun H => by
    simp [← H]⟩

theorem eq_comp_inv (α : X ≅ Y) {f : Z ⟶ Y} {g : Z ⟶ X} : g = f ≫ α.inv ↔ g ≫ α.Hom = f :=
  (comp_inv_eq α.symm).symm

theorem inv_eq_inv (f g : X ≅ Y) : f.inv = g.inv ↔ f.Hom = g.Hom :=
  have : ∀ {X Y : C} (f g : X ≅ Y), f.Hom = g.Hom → f.inv = g.inv := fun X Y f g h => by
    rw [ext h]
  ⟨this f.symm g.symm, this f g⟩

theorem hom_comp_eq_id (α : X ≅ Y) {f : Y ⟶ X} : α.Hom ≫ f = 𝟙 X ↔ f = α.inv := by
  rw [← eq_inv_comp, comp_id]

theorem comp_hom_eq_id (α : X ≅ Y) {f : Y ⟶ X} : f ≫ α.Hom = 𝟙 Y ↔ f = α.inv := by
  rw [← eq_comp_inv, id_comp]

theorem inv_comp_eq_id (α : X ≅ Y) {f : X ⟶ Y} : α.inv ≫ f = 𝟙 Y ↔ f = α.Hom :=
  hom_comp_eq_id α.symm

theorem comp_inv_eq_id (α : X ≅ Y) {f : X ⟶ Y} : f ≫ α.inv = 𝟙 X ↔ f = α.Hom :=
  comp_hom_eq_id α.symm

theorem hom_eq_inv (α : X ≅ Y) (β : Y ≅ X) : α.Hom = β.inv ↔ β.Hom = α.inv := by
  erw [inv_eq_inv α.symm β, eq_comm]
  rfl

end Iso

/-- `is_iso` typeclass expressing that a morphism is invertible. -/
class IsIso (f : X ⟶ Y) : Prop where
  out : ∃ inv : Y ⟶ X, f ≫ inv = 𝟙 X ∧ inv ≫ f = 𝟙 Y

/-- The inverse of a morphism `f` when we have `[is_iso f]`.
-/
noncomputable def inv (f : X ⟶ Y) [I : IsIso f] :=
  Classical.some I.1

namespace IsIso

@[simp, reassoc]
theorem hom_inv_id (f : X ⟶ Y) [I : IsIso f] : f ≫ inv f = 𝟙 X :=
  (Classical.some_spec I.1).left

@[simp, reassoc]
theorem inv_hom_id (f : X ⟶ Y) [I : IsIso f] : inv f ≫ f = 𝟙 Y :=
  (Classical.some_spec I.1).right

end IsIso

open IsIso

/-- Reinterpret a morphism `f` with an `is_iso f` instance as an `iso`. -/
noncomputable def asIso (f : X ⟶ Y) [h : IsIso f] : X ≅ Y :=
  ⟨f, inv f, hom_inv_id f, inv_hom_id f⟩

@[simp]
theorem as_iso_hom (f : X ⟶ Y) [IsIso f] : (asIso f).Hom = f :=
  rfl

@[simp]
theorem as_iso_inv (f : X ⟶ Y) [IsIso f] : (asIso f).inv = inv f :=
  rfl

namespace IsIso

-- see Note [lower instance priority]
instance (priority := 100) epi_of_iso (f : X ⟶ Y) [IsIso f] :
    Epi f where left_cancellation := fun Z g h w => -- This is an interesting test case for better rewrite automation.
  by
    rw [← is_iso.inv_hom_id_assoc f g, w, is_iso.inv_hom_id_assoc f h]

-- see Note [lower instance priority]
instance (priority := 100) mono_of_iso (f : X ⟶ Y) [IsIso f] :
    Mono f where right_cancellation := fun Z g h w => by
    rw [← category.comp_id g, ← category.comp_id h, ← is_iso.hom_inv_id f, ← category.assoc, w, ← category.assoc]

@[ext]
theorem inv_eq_of_hom_inv_id {f : X ⟶ Y} [IsIso f] {g : Y ⟶ X} (hom_inv_id : f ≫ g = 𝟙 X) : inv f = g := by
  apply (cancel_epi f).mp
  simp [← hom_inv_id]

theorem inv_eq_of_inv_hom_id {f : X ⟶ Y} [IsIso f] {g : Y ⟶ X} (inv_hom_id : g ≫ f = 𝟙 Y) : inv f = g := by
  apply (cancel_mono f).mp
  simp [← inv_hom_id]

@[ext]
theorem eq_inv_of_hom_inv_id {f : X ⟶ Y} [IsIso f] {g : Y ⟶ X} (hom_inv_id : f ≫ g = 𝟙 X) : g = inv f :=
  (inv_eq_of_hom_inv_id hom_inv_id).symm

theorem eq_inv_of_inv_hom_id {f : X ⟶ Y} [IsIso f] {g : Y ⟶ X} (inv_hom_id : g ≫ f = 𝟙 Y) : g = inv f :=
  (inv_eq_of_inv_hom_id inv_hom_id).symm

instance id (X : C) : IsIso (𝟙 X) :=
  ⟨⟨𝟙 X, by
      simp ⟩⟩

instance of_iso (f : X ≅ Y) : IsIso f.Hom :=
  ⟨⟨f.inv, by
      simp ⟩⟩

instance of_iso_inv (f : X ≅ Y) : IsIso f.inv :=
  IsIso.of_iso f.symm

variable {f g : X ⟶ Y} {h : Y ⟶ Z}

instance inv_is_iso [IsIso f] : IsIso (inv f) :=
  IsIso.of_iso_inv (asIso f)

/- The following instance has lower priority for the following reason:
Suppose we are given `f : X ≅ Y` with `X Y : Type u`.
Without the lower priority, typeclass inference cannot deduce `is_iso f.hom`
because `f.hom` is defeq to `(λ x, x) ≫ f.hom`, triggering a loop. -/
instance (priority := 900) comp_is_iso [IsIso f] [IsIso h] : IsIso (f ≫ h) :=
  is_iso.of_iso <| asIso f ≪≫ asIso h

@[simp]
theorem inv_id : inv (𝟙 X) = 𝟙 X := by
  ext
  simp

@[simp]
theorem inv_comp [IsIso f] [IsIso h] : inv (f ≫ h) = inv h ≫ inv f := by
  ext
  simp

@[simp]
theorem inv_inv [IsIso f] : inv (inv f) = f := by
  ext
  simp

@[simp]
theorem Iso.inv_inv (f : X ≅ Y) : inv f.inv = f.Hom := by
  ext
  simp

@[simp]
theorem Iso.inv_hom (f : X ≅ Y) : inv f.Hom = f.inv := by
  ext
  simp

@[simp]
theorem inv_comp_eq (α : X ⟶ Y) [IsIso α] {f : X ⟶ Z} {g : Y ⟶ Z} : inv α ≫ f = g ↔ f = α ≫ g :=
  (asIso α).inv_comp_eq

@[simp]
theorem eq_inv_comp (α : X ⟶ Y) [IsIso α] {f : X ⟶ Z} {g : Y ⟶ Z} : g = inv α ≫ f ↔ α ≫ g = f :=
  (asIso α).eq_inv_comp

@[simp]
theorem comp_inv_eq (α : X ⟶ Y) [IsIso α] {f : Z ⟶ Y} {g : Z ⟶ X} : f ≫ inv α = g ↔ f = g ≫ α :=
  (asIso α).comp_inv_eq

@[simp]
theorem eq_comp_inv (α : X ⟶ Y) [IsIso α] {f : Z ⟶ Y} {g : Z ⟶ X} : g = f ≫ inv α ↔ g ≫ α = f :=
  (asIso α).eq_comp_inv

theorem of_is_iso_comp_left {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso f] [IsIso (f ≫ g)] : IsIso g := by
  rw [← id_comp g, ← inv_hom_id f, assoc]
  infer_instance

theorem of_is_iso_comp_right {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso g] [IsIso (f ≫ g)] : IsIso f := by
  rw [← comp_id f, ← hom_inv_id g, ← assoc]
  infer_instance

theorem of_is_iso_fac_left {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} {h : X ⟶ Z} [IsIso f] [hh : IsIso h] (w : f ≫ g = h) :
    IsIso g := by
  rw [← w] at hh
  have := hh
  exact of_is_iso_comp_left f g

theorem of_is_iso_fac_right {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} {h : X ⟶ Z} [IsIso g] [hh : IsIso h] (w : f ≫ g = h) :
    IsIso f := by
  rw [← w] at hh
  have := hh
  exact of_is_iso_comp_right f g

end IsIso

open IsIso

theorem eq_of_inv_eq_inv {f g : X ⟶ Y} [IsIso f] [IsIso g] (p : inv f = inv g) : f = g := by
  apply (cancel_epi (inv f)).1
  erw [inv_hom_id, p, inv_hom_id]

theorem IsIso.inv_eq_inv {f g : X ⟶ Y} [IsIso f] [IsIso g] : inv f = inv g ↔ f = g :=
  Iso.inv_eq_inv (asIso f) (asIso g)

theorem hom_comp_eq_id (g : X ⟶ Y) [IsIso g] {f : Y ⟶ X} : g ≫ f = 𝟙 X ↔ f = inv g :=
  (asIso g).hom_comp_eq_id

theorem comp_hom_eq_id (g : X ⟶ Y) [IsIso g] {f : Y ⟶ X} : f ≫ g = 𝟙 Y ↔ f = inv g :=
  (asIso g).comp_hom_eq_id

theorem inv_comp_eq_id (g : X ⟶ Y) [IsIso g] {f : X ⟶ Y} : inv g ≫ f = 𝟙 Y ↔ f = g :=
  (asIso g).inv_comp_eq_id

theorem comp_inv_eq_id (g : X ⟶ Y) [IsIso g] {f : X ⟶ Y} : f ≫ inv g = 𝟙 X ↔ f = g :=
  (asIso g).comp_inv_eq_id

theorem is_iso_of_hom_comp_eq_id (g : X ⟶ Y) [IsIso g] {f : Y ⟶ X} (h : g ≫ f = 𝟙 X) : IsIso f := by
  rw [(hom_comp_eq_id _).mp h]
  infer_instance

theorem is_iso_of_comp_hom_eq_id (g : X ⟶ Y) [IsIso g] {f : Y ⟶ X} (h : f ≫ g = 𝟙 Y) : IsIso f := by
  rw [(comp_hom_eq_id _).mp h]
  infer_instance

namespace Iso

@[ext]
theorem inv_ext {f : X ≅ Y} {g : Y ⟶ X} (hom_inv_id : f.Hom ≫ g = 𝟙 X) : f.inv = g :=
  ((hom_comp_eq_id f).1 hom_inv_id).symm

@[ext]
theorem inv_ext' {f : X ≅ Y} {g : Y ⟶ X} (hom_inv_id : f.Hom ≫ g = 𝟙 X) : g = f.inv :=
  (hom_comp_eq_id f).1 hom_inv_id

/-!
All these cancellation lemmas can be solved by `simp [cancel_mono]` (or `simp [cancel_epi]`),
but with the current design `cancel_mono` is not a good `simp` lemma,
because it generates a typeclass search.

When we can see syntactically that a morphism is a `mono` or an `epi`
because it came from an isomorphism, it's fine to do the cancellation via `simp`.

In the longer term, it might be worth exploring making `mono` and `epi` structures,
rather than typeclasses, with coercions back to `X ⟶ Y`.
Presumably we could write `X ↪ Y` and `X ↠ Y`.
-/


@[simp]
theorem cancel_iso_hom_left {X Y Z : C} (f : X ≅ Y) (g g' : Y ⟶ Z) : f.Hom ≫ g = f.Hom ≫ g' ↔ g = g' := by
  simp only [← cancel_epi]

@[simp]
theorem cancel_iso_inv_left {X Y Z : C} (f : Y ≅ X) (g g' : Y ⟶ Z) : f.inv ≫ g = f.inv ≫ g' ↔ g = g' := by
  simp only [← cancel_epi]

@[simp]
theorem cancel_iso_hom_right {X Y Z : C} (f f' : X ⟶ Y) (g : Y ≅ Z) : f ≫ g.Hom = f' ≫ g.Hom ↔ f = f' := by
  simp only [← cancel_mono]

@[simp]
theorem cancel_iso_inv_right {X Y Z : C} (f f' : X ⟶ Y) (g : Z ≅ Y) : f ≫ g.inv = f' ≫ g.inv ↔ f = f' := by
  simp only [← cancel_mono]

/-
Unfortunately cancelling an isomorphism from the right of a chain of compositions is awkward.
We would need separate lemmas for each chain length (worse: for each pair of chain lengths).

We provide two more lemmas, for case of three morphisms, because this actually comes up in practice,
but then stop.
-/
@[simp]
theorem cancel_iso_hom_right_assoc {W X X' Y Z : C} (f : W ⟶ X) (g : X ⟶ Y) (f' : W ⟶ X') (g' : X' ⟶ Y) (h : Y ≅ Z) :
    f ≫ g ≫ h.Hom = f' ≫ g' ≫ h.Hom ↔ f ≫ g = f' ≫ g' := by
  simp only [category.assoc, ← cancel_mono]

@[simp]
theorem cancel_iso_inv_right_assoc {W X X' Y Z : C} (f : W ⟶ X) (g : X ⟶ Y) (f' : W ⟶ X') (g' : X' ⟶ Y) (h : Z ≅ Y) :
    f ≫ g ≫ h.inv = f' ≫ g' ≫ h.inv ↔ f ≫ g = f' ≫ g' := by
  simp only [category.assoc, ← cancel_mono]

end Iso

namespace Functor

universe u₁ v₁ u₂ v₂

variable {D : Type u₂}

variable [Category.{v₂} D]

/-- A functor `F : C ⥤ D` sends isomorphisms `i : X ≅ Y` to isomorphisms `F.obj X ≅ F.obj Y` -/
@[simps]
def mapIso (F : C ⥤ D) {X Y : C} (i : X ≅ Y) : F.obj X ≅ F.obj Y where
  Hom := F.map i.Hom
  inv := F.map i.inv
  hom_inv_id' := by
    rw [← map_comp, iso.hom_inv_id, ← map_id]
  inv_hom_id' := by
    rw [← map_comp, iso.inv_hom_id, ← map_id]

@[simp]
theorem map_iso_symm (F : C ⥤ D) {X Y : C} (i : X ≅ Y) : F.mapIso i.symm = (F.mapIso i).symm :=
  rfl

@[simp]
theorem map_iso_trans (F : C ⥤ D) {X Y Z : C} (i : X ≅ Y) (j : Y ≅ Z) : F.mapIso (i ≪≫ j) = F.mapIso i ≪≫ F.mapIso j :=
  by
  ext <;> apply functor.map_comp

@[simp]
theorem map_iso_refl (F : C ⥤ D) (X : C) : F.mapIso (Iso.refl X) = Iso.refl (F.obj X) :=
  iso.ext <| F.map_id X

instance map_is_iso (F : C ⥤ D) (f : X ⟶ Y) [IsIso f] : IsIso (F.map f) :=
  is_iso.of_iso <| F.mapIso (asIso f)

@[simp]
theorem map_inv (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) [IsIso f] : F.map (inv f) = inv (F.map f) := by
  ext
  simp [F.map_comp]

theorem map_hom_inv (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) [IsIso f] : F.map f ≫ F.map (inv f) = 𝟙 (F.obj X) := by
  simp

theorem map_inv_hom (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) [IsIso f] : F.map (inv f) ≫ F.map f = 𝟙 (F.obj Y) := by
  simp

end Functor

end CategoryTheory

