/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stephen Morgan, Scott Morrison, Johannes Hölzl, Reid Barton
-/
import Mathbin.Combinatorics.Quiver.Basic
import Mathbin.Tactic.Basic

/-!
# Categories

Defines a category, as a type class parametrised by the type of objects.

## Notations

Introduces notations
* `X ⟶ Y` for the morphism spaces,
* `f ≫ g` for composition in the 'arrows' convention.

Users may like to add `f ⊚ g` for composition in the standard convention, using
```lean
local notation f ` ⊚ `:80 g:80 := category.comp g f    -- type as \oo
```
-/


library_note "category_theory universes"/--
The typeclass `category C` describes morphisms associated to objects of type `C : Type u`.

The universe levels of the objects and morphisms are independent, and will often need to be
specified explicitly, as `category.{v} C`.

Typically any concrete example will either be a `small_category`, where `v = u`,
which can be introduced as
```
universes u
variables {C : Type u} [small_category C]
```
or a `large_category`, where `u = v+1`, which can be introduced as
```
universes u
variables {C : Type (u+1)} [large_category C]
```

In order for the library to handle these cases uniformly,
we generally work with the unconstrained `category.{v u}`,
for which objects live in `Type u` and morphisms live in `Type v`.

Because the universe parameter `u` for the objects can be inferred from `C`
when we write `category C`, while the universe parameter `v` for the morphisms
can not be automatically inferred, through the category theory library
we introduce universe parameters with morphism levels listed first,
as in
```
universes v u
```
or
```
universes v₁ v₂ u₁ u₂
```
when multiple independent universes are needed.

This has the effect that we can simply write `category.{v} C`
(that is, only specifying a single parameter) while `u` will be inferred.

Often, however, it's not even necessary to include the `.{v}`.
(Although it was in earlier versions of Lean.)
If it is omitted a "free" universe will be used.
-/


universe v u

namespace CategoryTheory

/-- A preliminary structure on the way to defining a category,
containing the data, but none of the axioms. -/
class CategoryStruct (obj : Type u) extends Quiver.{v + 1} obj : Type max u (v + 1) where
  id : ∀ X : obj, hom X X
  comp : ∀ {X Y Z : obj}, (X ⟶ Y) → (Y ⟶ Z) → (X ⟶ Z)

-- mathport name: «expr𝟙»
notation "𝟙" => CategoryStruct.id

-- mathport name: «expr ≫ »
infixr:80
  " ≫ " =>-- type as \b1
  CategoryStruct.comp

/-- The typeclass `category C` describes morphisms associated to objects of type `C`.
The universe levels of the objects and morphisms are unconstrained, and will often need to be
specified explicitly, as `category.{v} C`. (See also `large_category` and `small_category`.)

See <https://stacks.math.columbia.edu/tag/0014>.
-/
-- type as \gg
class Category (obj : Type u) extends CategoryStruct.{v} obj : Type max u (v + 1) where
  id_comp' : ∀ {X Y : obj} (f : hom X Y), 𝟙 X ≫ f = f := by
    run_tac
      obviously
  comp_id' : ∀ {X Y : obj} (f : hom X Y), f ≫ 𝟙 Y = f := by
    run_tac
      obviously
  assoc' : ∀ {W X Y Z : obj} (f : hom W X) (g : hom X Y) (h : hom Y Z), (f ≫ g) ≫ h = f ≫ g ≫ h := by
    run_tac
      obviously

-- `restate_axiom` is a command that creates a lemma from a structure field,
-- discarding any auto_param wrappers from the type.
-- (It removes a backtick from the name, if it finds one, and otherwise adds "_lemma".)
restate_axiom category.id_comp'

restate_axiom category.comp_id'

restate_axiom category.assoc'

attribute [simp] category.id_comp category.comp_id category.assoc

attribute [trans] category_struct.comp

/-- A `large_category` has objects in one universe level higher than the universe level of
the morphisms. It is useful for examples such as the category of types, or the category
of groups, etc.
-/
abbrev LargeCategory (C : Type (u + 1)) : Type (u + 1) :=
  Category.{u} C

/-- A `small_category` has objects and morphisms in the same universe level.
-/
abbrev SmallCategory (C : Type u) : Type (u + 1) :=
  Category.{u} C

section

variable {C : Type u} [Category.{v} C] {X Y Z : C}

initialize_simps_projections category (to_category_struct_to_quiver_hom → Hom, to_category_struct_comp → comp,
  to_category_struct_id → id, -toCategoryStruct)

/-- postcompose an equation between morphisms by another morphism -/
theorem eq_whisker {f g : X ⟶ Y} (w : f = g) (h : Y ⟶ Z) : f ≫ h = g ≫ h := by
  rw [w]

/-- precompose an equation between morphisms by another morphism -/
theorem whisker_eq (f : X ⟶ Y) {g h : Y ⟶ Z} (w : g = h) : f ≫ g = f ≫ h := by
  rw [w]

-- mathport name: «expr =≫ »
infixr:80 " =≫ " => eq_whisker

-- mathport name: «expr ≫= »
infixr:80 " ≫= " => whisker_eq

theorem eq_of_comp_left_eq {f g : X ⟶ Y} (w : ∀ {Z : C} (h : Y ⟶ Z), f ≫ h = g ≫ h) : f = g := by
  convert w (𝟙 Y)
  tidy

theorem eq_of_comp_right_eq {f g : Y ⟶ Z} (w : ∀ {X : C} (h : X ⟶ Y), h ≫ f = h ≫ g) : f = g := by
  convert w (𝟙 Y)
  tidy

theorem eq_of_comp_left_eq' (f g : X ⟶ Y) (w : (fun {Z : C} (h : Y ⟶ Z) => f ≫ h) = fun {Z : C} (h : Y ⟶ Z) => g ≫ h) :
    f = g :=
  eq_of_comp_left_eq fun Z h => by
    convert congr_fun (congr_fun w Z) h

theorem eq_of_comp_right_eq' (f g : Y ⟶ Z) (w : (fun {X : C} (h : X ⟶ Y) => h ≫ f) = fun {X : C} (h : X ⟶ Y) => h ≫ g) :
    f = g :=
  eq_of_comp_right_eq fun X h => by
    convert congr_fun (congr_fun w X) h

theorem id_of_comp_left_id (f : X ⟶ X) (w : ∀ {Y : C} (g : X ⟶ Y), f ≫ g = g) : f = 𝟙 X := by
  convert w (𝟙 X)
  tidy

theorem id_of_comp_right_id (f : X ⟶ X) (w : ∀ {Y : C} (g : Y ⟶ X), g ≫ f = g) : f = 𝟙 X := by
  convert w (𝟙 X)
  tidy

theorem comp_ite {P : Prop} [Decidable P] {X Y Z : C} (f : X ⟶ Y) (g g' : Y ⟶ Z) :
    (f ≫ if P then g else g') = if P then f ≫ g else f ≫ g' := by
  split_ifs <;> rfl

theorem ite_comp {P : Prop} [Decidable P] {X Y Z : C} (f f' : X ⟶ Y) (g : Y ⟶ Z) :
    (if P then f else f') ≫ g = if P then f ≫ g else f' ≫ g := by
  split_ifs <;> rfl

theorem comp_dite {P : Prop} [Decidable P] {X Y Z : C} (f : X ⟶ Y) (g : P → (Y ⟶ Z)) (g' : ¬P → (Y ⟶ Z)) :
    (f ≫ if h : P then g h else g' h) = if h : P then f ≫ g h else f ≫ g' h := by
  split_ifs <;> rfl

theorem dite_comp {P : Prop} [Decidable P] {X Y Z : C} (f : P → (X ⟶ Y)) (f' : ¬P → (X ⟶ Y)) (g : Y ⟶ Z) :
    (if h : P then f h else f' h) ≫ g = if h : P then f h ≫ g else f' h ≫ g := by
  split_ifs <;> rfl

/-- A morphism `f` is an epimorphism if it can be "cancelled" when precomposed:
`f ≫ g = f ≫ h` implies `g = h`.

See <https://stacks.math.columbia.edu/tag/003B>.
-/
class Epi (f : X ⟶ Y) : Prop where
  left_cancellation : ∀ {Z : C} (g h : Y ⟶ Z) (w : f ≫ g = f ≫ h), g = h

/-- A morphism `f` is a monomorphism if it can be "cancelled" when postcomposed:
`g ≫ f = h ≫ f` implies `g = h`.

See <https://stacks.math.columbia.edu/tag/003B>.
-/
class Mono (f : X ⟶ Y) : Prop where
  right_cancellation : ∀ {Z : C} (g h : Z ⟶ X) (w : g ≫ f = h ≫ f), g = h

instance (X : C) : Epi (𝟙 X) :=
  ⟨fun Z g h w => by
    simpa using w⟩

instance (X : C) : Mono (𝟙 X) :=
  ⟨fun Z g h w => by
    simpa using w⟩

theorem cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} : f ≫ g = f ≫ h ↔ g = h :=
  ⟨fun p => Epi.left_cancellation g h p, congr_arg _⟩

theorem cancel_mono (f : X ⟶ Y) [Mono f] {g h : Z ⟶ X} : g ≫ f = h ≫ f ↔ g = h :=
  ⟨fun p => Mono.right_cancellation g h p, congr_arg _⟩

theorem cancel_epi_id (f : X ⟶ Y) [Epi f] {h : Y ⟶ Y} : f ≫ h = f ↔ h = 𝟙 Y := by
  convert cancel_epi f
  simp

theorem cancel_mono_id (f : X ⟶ Y) [Mono f] {g : X ⟶ X} : g ≫ f = f ↔ g = 𝟙 X := by
  convert cancel_mono f
  simp

theorem epi_comp {X Y Z : C} (f : X ⟶ Y) [Epi f] (g : Y ⟶ Z) [Epi g] : Epi (f ≫ g) := by
  constructor
  intro Z a b w
  apply (cancel_epi g).1
  apply (cancel_epi f).1
  simpa using w

theorem mono_comp {X Y Z : C} (f : X ⟶ Y) [Mono f] (g : Y ⟶ Z) [Mono g] : Mono (f ≫ g) := by
  constructor
  intro Z a b w
  apply (cancel_mono f).1
  apply (cancel_mono g).1
  simpa using w

theorem mono_of_mono {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [Mono (f ≫ g)] : Mono f := by
  constructor
  intro Z a b w
  replace w := congr_arg (fun k => k ≫ g) w
  dsimp'  at w
  rw [category.assoc, category.assoc] at w
  exact (cancel_mono _).1 w

theorem mono_of_mono_fac {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} {h : X ⟶ Z} [Mono h] (w : f ≫ g = h) : Mono f := by
  subst h
  exact mono_of_mono f g

theorem epi_of_epi {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [Epi (f ≫ g)] : Epi g := by
  constructor
  intro Z a b w
  replace w := congr_arg (fun k => f ≫ k) w
  dsimp'  at w
  rw [← category.assoc, ← category.assoc] at w
  exact (cancel_epi _).1 w

theorem epi_of_epi_fac {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} {h : X ⟶ Z} [Epi h] (w : f ≫ g = h) : Epi g := by
  subst h <;> exact epi_of_epi f g

end

section

variable (C : Type u)

variable [Category.{v} C]

universe u'

instance uliftCategory : Category.{v} (ULift.{u'} C) where
  Hom := fun X Y => X.down ⟶ Y.down
  id := fun X => 𝟙 X.down
  comp := fun _ _ _ f g => f ≫ g

-- We verify that this previous instance can lift small categories to large categories.
example (D : Type u) [SmallCategory D] : LargeCategory (ULift.{u + 1} D) := by
  infer_instance

end

end CategoryTheory

library_note "dsimp, simp"/-- Many proofs in the category theory library use the `dsimp, simp` pattern,
which typically isn't necessary elsewhere.

One would usually hope that the same effect could be achieved simply with `simp`.

The essential issue is that composition of morphisms involves dependent types.
When you have a chain of morphisms being composed, say `f : X ⟶ Y` and `g : Y ⟶ Z`,
then `simp` can operate succesfully on the morphisms
(e.g. if `f` is the identity it can strip that off).

However if we have an equality of objects, say `Y = Y'`,
then `simp` can't operate because it would break the typing of the composition operations.
We rarely have interesting equalities of objects
(because that would be "evil" --- anything interesting should be expressed as an isomorphism
and tracked explicitly),
except of course that we have plenty of definitional equalities of objects.

`dsimp` can apply these safely, even inside a composition.

After `dsimp` has cleared up the object level, `simp` can resume work on the morphism level ---
but without the `dsimp` step, because `simp` looks at expressions syntactically,
the relevant lemmas might not fire.

There's no bound on how many times you potentially could have to switch back and forth,
if the `simp` introduced new objects we again need to `dsimp`.
In practice this does occur, but only rarely, because `simp` tends to shorten chains of compositions
(i.e. not introduce new objects at all).
-/


