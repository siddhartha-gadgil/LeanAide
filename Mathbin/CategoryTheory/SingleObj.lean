/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathbin.CategoryTheory.Endomorphism
import Mathbin.CategoryTheory.Category.Cat
import Mathbin.Algebra.Category.Mon.Basic

/-!
# Single-object category

Single object category with a given monoid of endomorphisms.
It is defined to facilitate transfering some definitions and lemmas (e.g., conjugacy etc.)
from category theory to monoids and groups.

## Main definitions

Given a type `α` with a monoid structure, `single_obj α` is `unit` type with `category` structure
such that `End (single_obj α).star` is the monoid `α`.  This can be extended to a functor `Mon ⥤
Cat`.

If `α` is a group, then `single_obj α` is a groupoid.

An element `x : α` can be reinterpreted as an element of `End (single_obj.star α)` using
`single_obj.to_End`.

## Implementation notes

- `category_struct.comp` on `End (single_obj.star α)` is `flip (*)`, not `(*)`. This way
  multiplication on `End` agrees with the multiplication on `α`.

- By default, Lean puts instances into `category_theory` namespace instead of
  `category_theory.single_obj`, so we give all names explicitly.
-/


universe u v w

namespace CategoryTheory

/-- Type tag on `unit` used to define single-object categories and groupoids. -/
@[nolint unused_arguments has_inhabited_instance]
def SingleObj (α : Type u) : Type :=
  Unit

namespace SingleObj

variable (α : Type u)

/-- One and `flip (*)` become `id` and `comp` for morphisms of the single object category. -/
instance categoryStruct [One α] [Mul α] : CategoryStruct (SingleObj α) where
  Hom := fun _ _ => α
  comp := fun _ _ _ x y => y * x
  id := fun _ => 1

/-- Monoid laws become category laws for the single object category. -/
instance category [Monoidₓ α] : Category (SingleObj α) where
  comp_id' := fun _ _ => one_mulₓ
  id_comp' := fun _ _ => mul_oneₓ
  assoc' := fun _ _ _ _ x y z => (mul_assoc z y x).symm

theorem id_as_one [Monoidₓ α] (x : SingleObj α) : 𝟙 x = 1 :=
  rfl

theorem comp_as_mul [Monoidₓ α] {x y z : SingleObj α} (f : x ⟶ y) (g : y ⟶ z) : f ≫ g = g * f :=
  rfl

/-- Groupoid structure on `single_obj α`.

See <https://stacks.math.columbia.edu/tag/0019>.
-/
instance groupoid [Groupₓ α] : Groupoid (SingleObj α) where
  inv := fun _ _ x => x⁻¹
  inv_comp' := fun _ _ => mul_right_invₓ
  comp_inv' := fun _ _ => mul_left_invₓ

theorem inv_as_inv [Groupₓ α] {x y : SingleObj α} (f : x ⟶ y) : inv f = f⁻¹ := by
  ext
  rw [comp_as_mul, inv_mul_selfₓ, id_as_one]

/-- The single object in `single_obj α`. -/
protected def star : SingleObj α :=
  Unit.star

/-- The endomorphisms monoid of the only object in `single_obj α` is equivalent to the original
     monoid α. -/
def toEnd [Monoidₓ α] : α ≃* End (SingleObj.star α) :=
  { Equivₓ.refl α with map_mul' := fun x y => rfl }

theorem to_End_def [Monoidₓ α] (x : α) : toEnd α x = x :=
  rfl

/-- There is a 1-1 correspondence between monoid homomorphisms `α → β` and functors between the
    corresponding single-object categories. It means that `single_obj` is a fully faithful
    functor.

See <https://stacks.math.columbia.edu/tag/001F> --
although we do not characterize when the functor is full or faithful.
-/
def mapHom (α : Type u) (β : Type v) [Monoidₓ α] [Monoidₓ β] : (α →* β) ≃ SingleObj α ⥤ SingleObj β where
  toFun := fun f =>
    { obj := id, map := fun _ _ => ⇑f, map_id' := fun _ => f.map_one, map_comp' := fun _ _ _ x y => f.map_mul y x }
  invFun := fun f =>
    { toFun := @Functor.map _ _ _ _ f (SingleObj.star α) (SingleObj.star α), map_one' := f.map_id _,
      map_mul' := fun x y => f.map_comp y x }
  left_inv := fun ⟨f, h₁, h₂⟩ => rfl
  right_inv := fun f => by
    cases f <;>
      run_tac
        obviously

theorem map_hom_id (α : Type u) [Monoidₓ α] : mapHom α α (MonoidHom.id α) = 𝟭 _ :=
  rfl

theorem map_hom_comp {α : Type u} {β : Type v} [Monoidₓ α] [Monoidₓ β] (f : α →* β) {γ : Type w} [Monoidₓ γ]
    (g : β →* γ) : mapHom α γ (g.comp f) = mapHom α β f ⋙ mapHom β γ g :=
  rfl

/-- Given a function `f : C → G` from a category to a group, we get a functor
    `C ⥤ G` sending any morphism `x ⟶ y` to `f y * (f x)⁻¹`. -/
@[simps]
def differenceFunctor {C G} [Category C] [Groupₓ G] (f : C → G) : C ⥤ SingleObj G where
  obj := fun _ => ()
  map := fun x y _ => f y * (f x)⁻¹
  map_id' := by
    intro
    rw [single_obj.id_as_one, mul_right_invₓ]
  map_comp' := by
    intros
    rw [single_obj.comp_as_mul, ← mul_assoc, mul_left_injₓ, mul_assoc, inv_mul_selfₓ, mul_oneₓ]

end SingleObj

end CategoryTheory

open CategoryTheory

namespace MonoidHom

/-- Reinterpret a monoid homomorphism `f : α → β` as a functor `(single_obj α) ⥤ (single_obj β)`.
See also `category_theory.single_obj.map_hom` for an equivalence between these types. -/
@[reducible]
def toFunctor {α : Type u} {β : Type v} [Monoidₓ α] [Monoidₓ β] (f : α →* β) : SingleObj α ⥤ SingleObj β :=
  SingleObj.mapHom α β f

@[simp]
theorem id_to_functor (α : Type u) [Monoidₓ α] : (id α).toFunctor = 𝟭 _ :=
  rfl

@[simp]
theorem comp_to_functor {α : Type u} {β : Type v} [Monoidₓ α] [Monoidₓ β] (f : α →* β) {γ : Type w} [Monoidₓ γ]
    (g : β →* γ) : (g.comp f).toFunctor = f.toFunctor ⋙ g.toFunctor :=
  rfl

end MonoidHom

namespace Units

variable (α : Type u) [Monoidₓ α]

/-- The units in a monoid are (multiplicatively) equivalent to
the automorphisms of `star` when we think of the monoid as a single-object category. -/
def toAut : αˣ ≃* Aut (SingleObj.star α) :=
  (Units.mapEquiv (SingleObj.toEnd α)).trans <| Aut.unitsEndEquivAut _

@[simp]
theorem to_Aut_hom (x : αˣ) : (toAut α x).Hom = SingleObj.toEnd α x :=
  rfl

@[simp]
theorem to_Aut_inv (x : αˣ) : (toAut α x).inv = SingleObj.toEnd α (x⁻¹ : αˣ) :=
  rfl

end Units

namespace Mon

open CategoryTheory

/-- The fully faithful functor from `Mon` to `Cat`. -/
def toCat : Mon ⥤ Cat where
  obj := fun x => Cat.of (SingleObj x)
  map := fun x y f => SingleObj.mapHom x y f

instance toCatFull : Full toCat where
  Preimage := fun x y => (SingleObj.mapHom x y).invFun
  witness' := fun x y => by
    apply Equivₓ.right_inv

instance to_Cat_faithful :
    Faithful toCat where map_injective' := fun x y => by
    apply Equivₓ.injective

end Mon

