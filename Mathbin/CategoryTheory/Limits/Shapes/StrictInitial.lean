/-
Copyright (c) 2021 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathbin.CategoryTheory.Limits.Shapes.Terminal
import Mathbin.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathbin.CategoryTheory.EpiMono

/-!
# Strict initial objects

This file sets up the basic theory of strict initial objects: initial objects where every morphism
to it is an isomorphism. This generalises a property of the empty set in the category of sets:
namely that the only function to the empty set is from itself.

We say `C` has strict initial objects if every initial object is strict, ie given any morphism
`f : A ⟶ I` where `I` is initial, then `f` is an isomorphism.
Strictly speaking, this says that *any* initial object must be strict, rather than that strict
initial objects exist, which turns out to be a more useful notion to formalise.

If the binary product of `X` with a strict initial object exists, it is also initial.

To show a category `C` with an initial object has strict initial objects, the most convenient way
is to show any morphism to the (chosen) initial object is an isomorphism and use
`has_strict_initial_objects_of_initial_is_strict`.

The dual notion (strict terminal objects) occurs much less frequently in practice so is ignored.

## TODO

* Construct examples of this: `Type*`, `Top`, `Groupoid`, simplicial types, posets.
* Construct the bottom element of the subobject lattice given strict initials.
* Show cartesian closed categories have strict initials

## References
* https://ncatlab.org/nlab/show/strict+initial+object
-/


universe v u

namespace CategoryTheory

namespace Limits

open Category

variable (C : Type u) [Category.{v} C]

section StrictInitial

/-- We say `C` has strict initial objects if every initial object is strict, ie given any morphism
`f : A ⟶ I` where `I` is initial, then `f` is an isomorphism.

Strictly speaking, this says that *any* initial object must be strict, rather than that strict
initial objects exist.
-/
class HasStrictInitialObjects : Prop where
  out : ∀ {I A : C} (f : A ⟶ I), IsInitial I → IsIso f

variable {C}

section

variable [HasStrictInitialObjects C] {I : C}

theorem IsInitial.is_iso_to (hI : IsInitial I) {A : C} (f : A ⟶ I) : IsIso f :=
  HasStrictInitialObjects.out f hI

theorem IsInitial.strict_hom_ext (hI : IsInitial I) {A : C} (f g : A ⟶ I) : f = g := by
  have := hI.is_iso_to f
  have := hI.is_iso_to g
  exact eq_of_inv_eq_inv (hI.hom_ext (inv f) (inv g))

theorem IsInitial.subsingleton_to (hI : IsInitial I) {A : C} : Subsingleton (A ⟶ I) :=
  ⟨hI.strict_hom_ext⟩

instance (priority := 100) initial_mono_of_strict_initial_objects :
    InitialMonoClass
      C where is_initial_mono_from := fun I A hI => { right_cancellation := fun B g h i => hI.strict_hom_ext _ _ }

/-- If `I` is initial, then `X ⨯ I` is isomorphic to it. -/
@[simps Hom]
noncomputable def mulIsInitial (X : C) [HasBinaryProduct X I] (hI : IsInitial I) : X ⨯ I ≅ I :=
  @asIso _ prod.snd (hI.is_iso_to _)

@[simp]
theorem mul_is_initial_inv (X : C) [HasBinaryProduct X I] (hI : IsInitial I) : (mulIsInitial X hI).inv = hI.to _ :=
  hI.hom_ext _ _

/-- If `I` is initial, then `I ⨯ X` is isomorphic to it. -/
@[simps Hom]
noncomputable def isInitialMul (X : C) [HasBinaryProduct I X] (hI : IsInitial I) : I ⨯ X ≅ I :=
  @asIso _ prod.fst (hI.is_iso_to _)

@[simp]
theorem is_initial_mul_inv (X : C) [HasBinaryProduct I X] (hI : IsInitial I) : (isInitialMul X hI).inv = hI.to _ :=
  hI.hom_ext _ _

variable [HasInitial C]

instance initial_is_iso_to {A : C} (f : A ⟶ ⊥_ C) : IsIso f :=
  initialIsInitial.is_iso_to _

@[ext]
theorem initial.hom_ext {A : C} (f g : A ⟶ ⊥_ C) : f = g :=
  initialIsInitial.strict_hom_ext _ _

theorem initial.subsingleton_to {A : C} : Subsingleton (A ⟶ ⊥_ C) :=
  initialIsInitial.subsingleton_to

/-- The product of `X` with an initial object in a category with strict initial objects is itself
initial.
This is the generalisation of the fact that `X × empty ≃ empty` for types (or `n * 0 = 0`).
-/
@[simps Hom]
noncomputable def mulInitial (X : C) [HasBinaryProduct X (⊥_ C)] : X ⨯ ⊥_ C ≅ ⊥_ C :=
  mulIsInitial _ initialIsInitial

@[simp]
theorem mul_initial_inv (X : C) [HasBinaryProduct X (⊥_ C)] : (mulInitial X).inv = initial.to _ :=
  Subsingleton.elimₓ _ _

/-- The product of `X` with an initial object in a category with strict initial objects is itself
initial.
This is the generalisation of the fact that `empty × X ≃ empty` for types (or `0 * n = 0`).
-/
@[simps Hom]
noncomputable def initialMul (X : C) [HasBinaryProduct (⊥_ C) X] : (⊥_ C) ⨯ X ≅ ⊥_ C :=
  isInitialMul _ initialIsInitial

@[simp]
theorem initial_mul_inv (X : C) [HasBinaryProduct (⊥_ C) X] : (initialMul X).inv = initial.to _ :=
  Subsingleton.elimₓ _ _

end

/-- If `C` has an initial object such that every morphism *to* it is an isomorphism, then `C`
has strict initial objects. -/
theorem has_strict_initial_objects_of_initial_is_strict [HasInitial C] (h : ∀ (A) (f : A ⟶ ⊥_ C), IsIso f) :
    HasStrictInitialObjects C :=
  { out := fun I A f hI => by
      have := h A (f ≫ hI.to _)
      exact
        ⟨⟨hI.to _ ≫ inv (f ≫ hI.to (⊥_ C)), by
            rw [← assoc, is_iso.hom_inv_id], hI.hom_ext _ _⟩⟩ }

end StrictInitial

section StrictTerminal

/-- We say `C` has strict terminal objects if every terminal object is strict, ie given any morphism
`f : I ⟶ A` where `I` is terminal, then `f` is an isomorphism.

Strictly speaking, this says that *any* terminal object must be strict, rather than that strict
terminal objects exist.
-/
class HasStrictTerminalObjects : Prop where
  out : ∀ {I A : C} (f : I ⟶ A), IsTerminal I → IsIso f

variable {C}

section

variable [HasStrictTerminalObjects C] {I : C}

theorem IsTerminal.is_iso_from (hI : IsTerminal I) {A : C} (f : I ⟶ A) : IsIso f :=
  HasStrictTerminalObjects.out f hI

theorem IsTerminal.strict_hom_ext (hI : IsTerminal I) {A : C} (f g : I ⟶ A) : f = g := by
  have := hI.is_iso_from f
  have := hI.is_iso_from g
  exact eq_of_inv_eq_inv (hI.hom_ext (inv f) (inv g))

theorem IsTerminal.subsingleton_to (hI : IsTerminal I) {A : C} : Subsingleton (I ⟶ A) :=
  ⟨hI.strict_hom_ext⟩

variable {J : Type v} [SmallCategory J]

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (j «expr ≠ » i)
/-- If all but one object in a diagram is strict terminal, the the limit is isomorphic to the
said object via `limit.π`. -/
theorem limit_π_is_iso_of_is_strict_terminal (F : J ⥤ C) [HasLimit F] (i : J)
    (H : ∀ (j) (_ : j ≠ i), IsTerminal (F.obj j)) [Subsingleton (i ⟶ i)] : IsIso (limit.π F i) := by
  classical
  refine' ⟨⟨limit.lift _ ⟨_, ⟨_, _⟩⟩, _, _⟩⟩
  · exact fun j =>
      dite (j = i)
        (fun h =>
          eq_to_hom
            (by
              cases h
              rfl))
        fun h => (H _ h).from _
    
  · intro j k f
    split_ifs
    · cases h
      cases h_1
      obtain rfl : f = 𝟙 _ := Subsingleton.elimₓ _ _
      simpa
      
    · cases h
      erw [category.comp_id]
      have : is_iso (F.map f) := (H _ h_1).is_iso_from _
      rw [← is_iso.comp_inv_eq]
      apply (H _ h_1).hom_ext
      
    · cases h_1
      apply (H _ h).hom_ext
      
    · apply (H _ h).hom_ext
      
    
  · ext
    rw [assoc, limit.lift_π]
    dsimp' only
    split_ifs
    · cases h
      rw [id_comp, eq_to_hom_refl]
      exact comp_id _
      
    · apply (H _ h).hom_ext
      
    
  · rw [limit.lift_π]
    simpa
    

variable [HasTerminal C]

instance terminal_is_iso_from {A : C} (f : ⊤_ C ⟶ A) : IsIso f :=
  terminalIsTerminal.is_iso_from _

@[ext]
theorem terminal.hom_ext {A : C} (f g : ⊤_ C ⟶ A) : f = g :=
  terminalIsTerminal.strict_hom_ext _ _

theorem terminal.subsingleton_to {A : C} : Subsingleton (⊤_ C ⟶ A) :=
  terminalIsTerminal.subsingleton_to

end

/-- If `C` has an object such that every morphism *from* it is an isomorphism, then `C`
has strict terminal objects. -/
theorem has_strict_terminal_objects_of_terminal_is_strict (I : C) (h : ∀ (A) (f : I ⟶ A), IsIso f) :
    HasStrictTerminalObjects C :=
  { out := fun I' A f hI' => by
      have := h A (hI'.from _ ≫ f)
      exact
        ⟨⟨inv (hI'.from I ≫ f) ≫ hI'.from I, hI'.hom_ext _ _, by
            rw [assoc, is_iso.inv_hom_id]⟩⟩ }

end StrictTerminal

end Limits

end CategoryTheory

