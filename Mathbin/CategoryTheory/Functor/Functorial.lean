/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.CategoryTheory.Functor.Default

/-!
# Unbundled functors, as a typeclass decorating the object-level function.
-/


namespace CategoryTheory

-- declare the `v`'s first; see `category_theory.category` for an explanation
universe v v₁ v₂ v₃ u u₁ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- A unbundled functor. -/
-- Perhaps in the future we could redefine `functor` in terms of this, but that isn't the
-- immediate plan.
class Functorial (F : C → D) : Type max v₁ v₂ u₁ u₂ where
  map : ∀ {X Y : C}, (X ⟶ Y) → (F X ⟶ F Y)
  map_id' : ∀ X : C, map (𝟙 X) = 𝟙 (F X) := by
    run_tac
      obviously
  map_comp' : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z), map (f ≫ g) = map f ≫ map g := by
    run_tac
      obviously

/-- If `F : C → D` (just a function) has `[functorial F]`,
we can write `map F f : F X ⟶ F Y` for the action of `F` on a morphism `f : X ⟶ Y`.
-/
def map (F : C → D) [Functorial.{v₁, v₂} F] {X Y : C} (f : X ⟶ Y) : F X ⟶ F Y :=
  Functorial.map.{v₁, v₂} f

@[simp]
theorem map_as_map {F : C → D} [Functorial.{v₁, v₂} F] {X Y : C} {f : X ⟶ Y} : Functorial.map.{v₁, v₂} f = map F f :=
  rfl

@[simp]
theorem Functorial.map_id {F : C → D} [Functorial.{v₁, v₂} F] {X : C} : map F (𝟙 X) = 𝟙 (F X) :=
  Functorial.map_id' X

@[simp]
theorem Functorial.map_comp {F : C → D} [Functorial.{v₁, v₂} F] {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} :
    map F (f ≫ g) = map F f ≫ map F g :=
  Functorial.map_comp' f g

namespace Functor

/-- Bundle a functorial function as a functor.
-/
def of (F : C → D) [I : Functorial.{v₁, v₂} F] : C ⥤ D :=
  { I with obj := F }

end Functor

instance (F : C ⥤ D) : Functorial.{v₁, v₂} F.obj :=
  { F with }

@[simp]
theorem map_functorial_obj (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) : map F.obj f = F.map f :=
  rfl

instance functorialId : Functorial.{v₁, v₁} (id : C → C) where map := fun X Y f => f

section

variable {E : Type u₃} [Category.{v₃} E]

/-- `G ∘ F` is a functorial if both `F` and `G` are.
-/
-- This is no longer viable as an instance in Lean 3.7,
-- #lint reports an instance loop
-- Will this be a problem?
def functorialComp (F : C → D) [Functorial.{v₁, v₂} F] (G : D → E) [Functorial.{v₂, v₃} G] :
    Functorial.{v₁, v₃} (G ∘ F) :=
  { Functor.of F ⋙ Functor.of G with }

end

end CategoryTheory

