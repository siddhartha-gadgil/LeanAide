/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
import Mathbin.Control.Functor
import Mathbin.Data.Sum.Basic

/-!
# Functors with two arguments

This file defines bifunctors.

A bifunctor is a function `F : Type* → Type* → Type*` along with a bimap which turns `F α β` into
`F α' β'` given two functions `α → α'` and `β → β'`. It further
* respects the identity: `bimap id id = id`
* composes in the obvious way: `(bimap f' g') ∘ (bimap f g) = bimap (f' ∘ f) (g' ∘ g)`

## Main declarations

* `bifunctor`: A typeclass for the bare bimap of a bifunctor.
* `is_lawful_bifunctor`: A typeclass asserting this bimap respects the bifunctor laws.
-/


universe u₀ u₁ u₂ v₀ v₁ v₂

open Function

/-- Lawless bifunctor. This typeclass only holds the data for the bimap. -/
class Bifunctor (F : Type u₀ → Type u₁ → Type u₂) where
  bimap : ∀ {α α' β β'}, (α → α') → (β → β') → F α β → F α' β'

export Bifunctor (bimap)

/-- Bifunctor. This typeclass asserts that a lawless `bifunctor` is lawful. -/
class IsLawfulBifunctor (F : Type u₀ → Type u₁ → Type u₂) [Bifunctor F] where
  id_bimap : ∀ {α β} (x : F α β), bimap id id x = x
  bimap_bimap :
    ∀ {α₀ α₁ α₂ β₀ β₁ β₂} (f : α₀ → α₁) (f' : α₁ → α₂) (g : β₀ → β₁) (g' : β₁ → β₂) (x : F α₀ β₀),
      bimap f' g' (bimap f g x) = bimap (f' ∘ f) (g' ∘ g) x

export IsLawfulBifunctor (id_bimap bimap_bimap)

attribute [higher_order bimap_id_id] id_bimap

attribute [higher_order bimap_comp_bimap] bimap_bimap

export IsLawfulBifunctor (bimap_id_id bimap_comp_bimap)

variable {F : Type u₀ → Type u₁ → Type u₂} [Bifunctor F]

namespace Bifunctor

/-- Left map of a bifunctor. -/
@[reducible]
def fst {α α' β} (f : α → α') : F α β → F α' β :=
  bimap f id

/-- Right map of a bifunctor. -/
@[reducible]
def snd {α β β'} (f : β → β') : F α β → F α β' :=
  bimap id f

variable [IsLawfulBifunctor F]

@[higher_order fst_id]
theorem id_fst : ∀ {α β} (x : F α β), fst id x = x :=
  @id_bimap _ _ _

@[higher_order snd_id]
theorem id_snd : ∀ {α β} (x : F α β), snd id x = x :=
  @id_bimap _ _ _

@[higher_order fst_comp_fst]
theorem comp_fst {α₀ α₁ α₂ β} (f : α₀ → α₁) (f' : α₁ → α₂) (x : F α₀ β) : fst f' (fst f x) = fst (f' ∘ f) x := by
  simp [← fst, ← bimap_bimap]

@[higher_order fst_comp_snd]
theorem fst_snd {α₀ α₁ β₀ β₁} (f : α₀ → α₁) (f' : β₀ → β₁) (x : F α₀ β₀) : fst f (snd f' x) = bimap f f' x := by
  simp [← fst, ← bimap_bimap]

@[higher_order snd_comp_fst]
theorem snd_fst {α₀ α₁ β₀ β₁} (f : α₀ → α₁) (f' : β₀ → β₁) (x : F α₀ β₀) : snd f' (fst f x) = bimap f f' x := by
  simp [← snd, ← bimap_bimap]

@[higher_order snd_comp_snd]
theorem comp_snd {α β₀ β₁ β₂} (g : β₀ → β₁) (g' : β₁ → β₂) (x : F α β₀) : snd g' (snd g x) = snd (g' ∘ g) x := by
  simp [← snd, ← bimap_bimap]

attribute [functor_norm]
  bimap_bimap comp_snd comp_fst snd_comp_snd snd_comp_fst fst_comp_snd fst_comp_fst bimap_comp_bimap bimap_id_id fst_id snd_id

end Bifunctor

open Functor

instance : Bifunctor Prod where bimap := @Prod.map

instance : IsLawfulBifunctor Prod := by
  refine' { .. } <;> intros <;> cases x <;> rfl

instance Bifunctor.const : Bifunctor Const where bimap := fun α α' β β f _ => f

instance IsLawfulBifunctor.const : IsLawfulBifunctor Const := by
  refine' { .. } <;> intros <;> rfl

instance Bifunctor.flip : Bifunctor (flip F) where bimap := fun α α' β β' f f' x => (bimap f' f x : F β' α')

instance IsLawfulBifunctor.flip [IsLawfulBifunctor F] : IsLawfulBifunctor (flip F) := by
  refine' { .. } <;> intros <;> simp' [← bimap] with functor_norm

instance : Bifunctor Sum where bimap := @Sum.map

instance : IsLawfulBifunctor Sum := by
  refine' { .. } <;> intros <;> cases x <;> rfl

open Bifunctor Functor

instance (priority := 10) Bifunctor.functor {α} : Functor (F α) where map := fun _ _ => snd

instance (priority := 10) Bifunctor.is_lawful_functor [IsLawfulBifunctor F] {α} : IsLawfulFunctor (F α) := by
  refine' { .. } <;> intros <;> simp' [← Functor.map] with functor_norm

section Bicompl

variable (G : Type _ → Type u₀) (H : Type _ → Type u₁) [Functor G] [Functor H]

instance : Bifunctor (bicompl F G H) where bimap := fun α α' β β' f f' x => (bimap (map f) (map f') x : F (G α') (H β'))

instance [IsLawfulFunctor G] [IsLawfulFunctor H] [IsLawfulBifunctor F] : IsLawfulBifunctor (bicompl F G H) := by
  constructor <;> intros <;> simp' [← bimap, ← map_id, ← map_comp_map] with functor_norm

end Bicompl

section Bicompr

variable (G : Type u₂ → Type _) [Functor G]

instance : Bifunctor (bicompr G F) where bimap := fun α α' β β' f f' x => (map (bimap f f') x : G (F α' β'))

instance [IsLawfulFunctor G] [IsLawfulBifunctor F] : IsLawfulBifunctor (bicompr G F) := by
  constructor <;> intros <;> simp' [← bimap] with functor_norm

end Bicompr

