/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Johannes Hölzl, Reid Barton, Sean Leather, Yury Kudryashov
-/
import Mathbin.CategoryTheory.Types
import Mathbin.CategoryTheory.Functor.EpiMono

/-!
# Concrete categories

A concrete category is a category `C` with a fixed faithful functor
`forget : C ⥤ Type*`.  We define concrete categories using `class
concrete_category`.  In particular, we impose no restrictions on the
carrier type `C`, so `Type` is a concrete category with the identity
forgetful functor.

Each concrete category `C` comes with a canonical faithful functor
`forget C : C ⥤ Type*`.  We say that a concrete category `C` admits a
*forgetful functor* to a concrete category `D`, if it has a functor
`forget₂ C D : C ⥤ D` such that `(forget₂ C D) ⋙ (forget D) = forget C`,
see `class has_forget₂`.  Due to `faithful.div_comp`, it suffices
to verify that `forget₂.obj` and `forget₂.map` agree with the equality
above; then `forget₂` will satisfy the functor laws automatically, see
`has_forget₂.mk'`.

Two classes helping construct concrete categories in the two most
common cases are provided in the files `bundled_hom` and
`unbundled_hom`, see their documentation for details.

## References

See [Ahrens and Lumsdaine, *Displayed Categories*][ahrens2017] for
related work.
-/


universe w v v' u

namespace CategoryTheory

-- ./././Mathport/Syntax/Translate/Basic.lean:1440:30: infer kinds are unsupported in Lean 4: #[`forget] []
/-- A concrete category is a category `C` with a fixed faithful functor `forget : C ⥤ Type`.

Note that `concrete_category` potentially depends on three independent universe levels,
* the universe level `w` appearing in `forget : C ⥤ Type w`
* the universe level `v` of the morphisms (i.e. we have a `category.{v} C`)
* the universe level `u` of the objects (i.e `C : Type u`)
They are specified that order, to avoid unnecessary universe annotations.
-/
class ConcreteCategory (C : Type u) [Category.{v} C] where
  forget : C ⥤ Type w
  [forget_faithful : Faithful forget]

attribute [instance] concrete_category.forget_faithful

/-- The forgetful functor from a concrete category to `Type u`. -/
@[reducible]
def forget (C : Type v) [Category C] [ConcreteCategory.{u} C] : C ⥤ Type u :=
  ConcreteCategory.forget C

instance ConcreteCategory.types : ConcreteCategory (Type u) where forget := 𝟭 _

/-- Provide a coercion to `Type u` for a concrete category. This is not marked as an instance
as it could potentially apply to every type, and so is too expensive in typeclass search.

You can use it on particular examples as:
```
instance : has_coe_to_sort X := concrete_category.has_coe_to_sort X
```
-/
def ConcreteCategory.hasCoeToSort (C : Type v) [Category C] [ConcreteCategory C] : CoeSort C (Type u) :=
  ⟨(ConcreteCategory.forget C).obj⟩

section

attribute [local instance] concrete_category.has_coe_to_sort

variable {C : Type v} [Category C] [ConcreteCategory C]

@[simp]
theorem forget_obj_eq_coe {X : C} : (forget C).obj X = X :=
  rfl

/-- Usually a bundled hom structure already has a coercion to function
that works with different universes. So we don't use this as a global instance. -/
def ConcreteCategory.hasCoeToFun {X Y : C} : CoeFun (X ⟶ Y) fun f => X → Y :=
  ⟨fun f => (forget _).map f⟩

attribute [local instance] concrete_category.has_coe_to_fun

/-- In any concrete category, we can test equality of morphisms by pointwise evaluations.-/
theorem ConcreteCategory.hom_ext {X Y : C} (f g : X ⟶ Y) (w : ∀ x : X, f x = g x) : f = g := by
  apply faithful.map_injective (forget C)
  ext
  exact w x

@[simp]
theorem forget_map_eq_coe {X Y : C} (f : X ⟶ Y) : (forget C).map f = f :=
  rfl

/-- Analogue of `congr_fun h x`,
when `h : f = g` is an equality between morphisms in a concrete category.
-/
theorem congr_hom {X Y : C} {f g : X ⟶ Y} (h : f = g) (x : X) : f x = g x :=
  congr_fun (congr_arg (fun k : X ⟶ Y => (k : X → Y)) h) x

theorem coe_id {X : C} : (𝟙 X : X → X) = id :=
  (forget _).map_id X

theorem coe_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g : X → Z) = g ∘ f :=
  (forget _).map_comp f g

@[simp]
theorem id_apply {X : C} (x : X) : (𝟙 X : X → X) x = x :=
  congr_fun ((forget _).map_id X) x

@[simp]
theorem comp_apply {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) : (f ≫ g) x = g (f x) :=
  congr_fun ((forget _).map_comp _ _) x

theorem ConcreteCategory.congr_hom {X Y : C} {f g : X ⟶ Y} (h : f = g) (x : X) : f x = g x :=
  congr_fun (congr_arg (fun f : X ⟶ Y => (f : X → Y)) h) x

theorem ConcreteCategory.congr_arg {X Y : C} (f : X ⟶ Y) {x x' : X} (h : x = x') : f x = f x' :=
  congr_arg (f : X → Y) h

/-- In any concrete category, injective morphisms are monomorphisms. -/
theorem ConcreteCategory.mono_of_injective {X Y : C} (f : X ⟶ Y) (i : Function.Injective f) : Mono f :=
  (forget C).mono_of_mono_map ((mono_iff_injective f).2 i)

/-- In any concrete category, surjective morphisms are epimorphisms. -/
theorem ConcreteCategory.epi_of_surjective {X Y : C} (f : X ⟶ Y) (s : Function.Surjective f) : Epi f :=
  (forget C).epi_of_epi_map ((epi_iff_surjective f).2 s)

@[simp]
theorem ConcreteCategory.has_coe_to_fun_Type {X Y : Type u} (f : X ⟶ Y) : coeFn f = f :=
  rfl

end

/-- `has_forget₂ C D`, where `C` and `D` are both concrete categories, provides a functor
`forget₂ C D : C ⥤ D` and a proof that `forget₂ ⋙ (forget D) = forget C`.
-/
class HasForget₂ (C : Type v) (D : Type v') [Category C] [ConcreteCategory.{u} C] [Category D]
  [ConcreteCategory.{u} D] where
  forget₂ : C ⥤ D
  forget_comp : forget₂ ⋙ forget D = forget C := by
    run_tac
      obviously

/-- The forgetful functor `C ⥤ D` between concrete categories for which we have an instance
`has_forget₂ C `. -/
@[reducible]
def forget₂ (C : Type v) (D : Type v') [Category C] [ConcreteCategory C] [Category D] [ConcreteCategory D]
    [HasForget₂ C D] : C ⥤ D :=
  has_forget₂.forget₂

instance forget_faithful (C : Type v) (D : Type v') [Category C] [ConcreteCategory C] [Category D] [ConcreteCategory D]
    [HasForget₂ C D] : Faithful (forget₂ C D) :=
  HasForget₂.forget_comp.faithful_of_comp

instance InducedCategory.concreteCategory {C : Type v} {D : Type v'} [Category D] [ConcreteCategory D] (f : C → D) :
    ConcreteCategory (InducedCategory D f) where forget := inducedFunctor f ⋙ forget D

instance InducedCategory.hasForget₂ {C : Type v} {D : Type v'} [Category D] [ConcreteCategory D] (f : C → D) :
    HasForget₂ (InducedCategory D f) D where
  forget₂ := inducedFunctor f
  forget_comp := rfl

instance fullSubcategory.concreteCategory {C : Type v} [Category C] [ConcreteCategory C] (Z : C → Prop) :
    ConcreteCategory { X : C // Z X } where forget := fullSubcategoryInclusion Z ⋙ forget C

instance fullSubcategory.hasForget₂ {C : Type v} [Category C] [ConcreteCategory C] (Z : C → Prop) :
    HasForget₂ { X : C // Z X } C where
  forget₂ := fullSubcategoryInclusion Z
  forget_comp := rfl

/-- In order to construct a “partially forgetting” functor, we do not need to verify functor laws;
it suffices to ensure that compositions agree with `forget₂ C D ⋙ forget D = forget C`.
-/
def HasForget₂.mk' {C : Type v} {D : Type v'} [Category C] [ConcreteCategory C] [Category D] [ConcreteCategory D]
    (obj : C → D) (h_obj : ∀ X, (forget D).obj (obj X) = (forget C).obj X) (map : ∀ {X Y}, (X ⟶ Y) → (obj X ⟶ obj Y))
    (h_map : ∀ {X Y} {f : X ⟶ Y}, HEq ((forget D).map (map f)) ((forget C).map f)) : HasForget₂ C D where
  forget₂ := Faithful.div _ _ _ @h_obj _ @h_map
  forget_comp := by
    apply faithful.div_comp

instance hasForgetToType (C : Type v) [Category C] [ConcreteCategory C] : HasForget₂ C (Type u) where
  forget₂ := forget C
  forget_comp := Functor.comp_id _

end CategoryTheory

