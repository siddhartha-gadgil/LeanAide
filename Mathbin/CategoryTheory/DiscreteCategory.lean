/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stephen Morgan, Scott Morrison, Floris van Doorn
-/
import Mathbin.CategoryTheory.EqToHom
import Mathbin.Data.Ulift

/-!
# Discrete categories

We define `discrete α` as a structure containing a term `a : α` for any type `α`,
and use this type alias to provide a `small_category` instance
whose only morphisms are the identities.

There is an annoying technical difficulty that it has turned out to be inconvenient
to allow categories with morphisms living in `Prop`,
so instead of defining `X ⟶ Y` in `discrete α` as `X = Y`,
one might define it as `plift (X = Y)`.
In fact, to allow `discrete α` to be a `small_category`
(i.e. with morphisms in the same universe as the objects),
we actually define the hom type `X ⟶ Y` as `ulift (plift (X = Y))`.

`discrete.functor` promotes a function `f : I → C` (for any category `C`) to a functor
`discrete.functor f : discrete I ⥤ C`.

Similarly, `discrete.nat_trans` and `discrete.nat_iso` promote `I`-indexed families of morphisms,
or `I`-indexed families of isomorphisms to natural transformations or natural isomorphism.

We show equivalences of types are the same as (categorical) equivalences of the corresponding
discrete categories.
-/


namespace CategoryTheory

-- morphism levels before object levels. See note [category_theory universes].
universe v₁ v₂ v₃ u₁ u₁' u₂ u₃

/-- A wrapper for promoting any type to a category,
with the only morphisms being equalities.
-/
-- This is intentionally a structure rather than a type synonym
-- to enforce using `discrete_equiv` (or `discrete.mk` and `discrete.as`) to move between
-- `discrete α` and `α`. Otherwise there is too much API leakage.
@[ext]
structure Discrete (α : Type u₁) where
  as : α

@[simp]
theorem Discrete.mk_as {α : Type u₁} (X : Discrete α) : Discrete.mk X.as = X := by
  ext
  rfl

/-- `discrete α` is equivalent to the original type `α`.-/
@[simps]
def discreteEquiv {α : Type u₁} : Discrete α ≃ α where
  toFun := Discrete.as
  invFun := Discrete.mk
  left_inv := by
    tidy
  right_inv := by
    tidy

instance {α : Type u₁} [DecidableEq α] : DecidableEq (Discrete α) :=
  discreteEquiv.DecidableEq

/-- The "discrete" category on a type, whose morphisms are equalities.

Because we do not allow morphisms in `Prop` (only in `Type`),
somewhat annoyingly we have to define `X ⟶ Y` as `ulift (plift (X = Y))`.

See <https://stacks.math.columbia.edu/tag/001A>
-/
instance discreteCategory (α : Type u₁) : SmallCategory (Discrete α) where
  Hom := fun X Y => ULift (Plift (X.as = Y.as))
  id := fun X => ULift.up (Plift.up rfl)
  comp := fun X Y Z g f => by
    cases X
    cases Y
    cases Z
    rcases f with ⟨⟨⟨⟩⟩⟩
    exact g

namespace Discrete

variable {α : Type u₁}

instance [Inhabited α] : Inhabited (Discrete α) :=
  ⟨⟨default⟩⟩

instance [Subsingleton α] : Subsingleton (Discrete α) :=
  ⟨by
    intros
    ext
    apply Subsingleton.elimₓ⟩

-- ./././Mathport/Syntax/Translate/Basic.lean:1087:4: warning: unsupported (TODO): `[tacs]
/-- A simple tactic to run `cases` on any `discrete α` hypotheses. -/
unsafe def _root_.tactic.discrete_cases : tactic Unit :=
  sorry

run_cmd
  add_interactive [`` tactic.discrete_cases]

attribute [local tidy] tactic.discrete_cases

instance [Unique α] : Unique (Discrete α) :=
  Unique.mk' (Discrete α)

/-- Extract the equation from a morphism in a discrete category. -/
theorem eq_of_hom {X Y : Discrete α} (i : X ⟶ Y) : X.as = Y.as :=
  i.down.down

/-- Promote an equation between the wrapped terms in `X Y : discrete α` to a morphism `X ⟶ Y`
in the discrete category. -/
abbrev eqToHom {X Y : Discrete α} (h : X.as = Y.as) : X ⟶ Y :=
  eqToHom
    (by
      ext
      exact h)

/-- Promote an equation between the wrapped terms in `X Y : discrete α` to an isomorphism `X ≅ Y`
in the discrete category. -/
abbrev eqToIso {X Y : Discrete α} (h : X.as = Y.as) : X ≅ Y :=
  eqToIso
    (by
      ext
      exact h)

/-- A variant of `eq_to_hom` that lifts terms to the discrete category. -/
abbrev eqToHom' {a b : α} (h : a = b) : Discrete.mk a ⟶ Discrete.mk b :=
  eqToHom h

/-- A variant of `eq_to_iso` that lifts terms to the discrete category. -/
abbrev eqToIso' {a b : α} (h : a = b) : Discrete.mk a ≅ Discrete.mk b :=
  eqToIso h

@[simp]
theorem id_def (X : Discrete α) : ULift.up (Plift.up (Eq.refl X.as)) = 𝟙 X :=
  rfl

variable {C : Type u₂} [Category.{v₂} C]

instance {I : Type u₁} {i j : Discrete I} (f : i ⟶ j) : IsIso f :=
  ⟨⟨eqToHom (eq_of_hom f).symm, by
      tidy⟩⟩

-- ./././Mathport/Syntax/Translate/Basic.lean:647:16: unsupported tactic `discrete_cases #[]
/-- Any function `I → C` gives a functor `discrete I ⥤ C`.
-/
def functor {I : Type u₁} (F : I → C) : Discrete I ⥤ C where
  obj := F ∘ discrete.as
  map := fun X Y f => by
    trace "./././Mathport/Syntax/Translate/Basic.lean:647:16: unsupported tactic `discrete_cases #[]"
    cases f
    exact 𝟙 (F X)

@[simp]
theorem functor_obj {I : Type u₁} (F : I → C) (i : I) : (Discrete.functor F).obj (Discrete.mk i) = F i :=
  rfl

theorem functor_map {I : Type u₁} (F : I → C) {i : Discrete I} (f : i ⟶ i) : (Discrete.functor F).map f = 𝟙 (F i.as) :=
  by
  tidy

/-- The discrete functor induced by a composition of maps can be written as a
composition of two discrete functors.
-/
@[simps]
def functorComp {I : Type u₁} {J : Type u₁'} (f : J → C) (g : I → J) :
    Discrete.functor (f ∘ g) ≅ Discrete.functor (discrete.mk ∘ g) ⋙ Discrete.functor f :=
  NatIso.ofComponents (fun X => Iso.refl _)
    (by
      tidy)

-- ./././Mathport/Syntax/Translate/Basic.lean:647:16: unsupported tactic `discrete_cases #[]
/-- For functors out of a discrete category,
a natural transformation is just a collection of maps,
as the naturality squares are trivial.
-/
@[simps]
def natTrans {I : Type u₁} {F G : Discrete I ⥤ C} (f : ∀ i : Discrete I, F.obj i ⟶ G.obj i) : F ⟶ G where
  app := f
  naturality' := fun X Y g => by
    trace "./././Mathport/Syntax/Translate/Basic.lean:647:16: unsupported tactic `discrete_cases #[]"
    cases g
    simp

-- ./././Mathport/Syntax/Translate/Basic.lean:647:16: unsupported tactic `discrete_cases #[]
/-- For functors out of a discrete category,
a natural isomorphism is just a collection of isomorphisms,
as the naturality squares are trivial.
-/
@[simps]
def natIso {I : Type u₁} {F G : Discrete I ⥤ C} (f : ∀ i : Discrete I, F.obj i ≅ G.obj i) : F ≅ G :=
  NatIso.ofComponents f fun X Y g => by
    trace "./././Mathport/Syntax/Translate/Basic.lean:647:16: unsupported tactic `discrete_cases #[]"
    cases g
    simp

@[simp]
theorem nat_iso_app {I : Type u₁} {F G : Discrete I ⥤ C} (f : ∀ i : Discrete I, F.obj i ≅ G.obj i) (i : Discrete I) :
    (Discrete.natIso f).app i = f i := by
  tidy

-- ./././Mathport/Syntax/Translate/Basic.lean:647:16: unsupported tactic `discrete_cases #[]
/-- Every functor `F` from a discrete category is naturally isomorphic (actually, equal) to
  `discrete.functor (F.obj)`. -/
@[simp]
def natIsoFunctor {I : Type u₁} {F : Discrete I ⥤ C} : F ≅ Discrete.functor (F.obj ∘ discrete.mk) :=
  nat_iso fun i => by
    trace "./././Mathport/Syntax/Translate/Basic.lean:647:16: unsupported tactic `discrete_cases #[]"
    rfl

/-- Composing `discrete.functor F` with another functor `G` amounts to composing `F` with `G.obj` -/
@[simp]
def compNatIsoDiscrete {I : Type u₁} {D : Type u₃} [Category.{v₃} D] (F : I → C) (G : C ⥤ D) :
    Discrete.functor F ⋙ G ≅ Discrete.functor (G.obj ∘ F) :=
  nat_iso fun i => Iso.refl _

-- ./././Mathport/Syntax/Translate/Basic.lean:647:16: unsupported tactic `discrete_cases #[]
-- ./././Mathport/Syntax/Translate/Basic.lean:647:16: unsupported tactic `discrete_cases #[]
/-- We can promote a type-level `equiv` to
an equivalence between the corresponding `discrete` categories.
-/
@[simps]
def equivalence {I : Type u₁} {J : Type u₂} (e : I ≃ J) : Discrete I ≌ Discrete J where
  Functor := Discrete.functor (discrete.mk ∘ (e : I → J))
  inverse := Discrete.functor (discrete.mk ∘ (e.symm : J → I))
  unitIso :=
    Discrete.natIso fun i =>
      eqToIso
        (by
          trace "./././Mathport/Syntax/Translate/Basic.lean:647:16: unsupported tactic `discrete_cases #[]"
          simp )
  counitIso :=
    Discrete.natIso fun j =>
      eqToIso
        (by
          trace "./././Mathport/Syntax/Translate/Basic.lean:647:16: unsupported tactic `discrete_cases #[]"
          simp )

/-- We can convert an equivalence of `discrete` categories to a type-level `equiv`. -/
@[simps]
def equivOfEquivalence {α : Type u₁} {β : Type u₂} (h : Discrete α ≌ Discrete β) : α ≃ β where
  toFun := discrete.as ∘ h.Functor.obj ∘ discrete.mk
  invFun := discrete.as ∘ h.inverse.obj ∘ discrete.mk
  left_inv := fun a => by
    simpa using eq_of_hom (h.unit_iso.app (discrete.mk a)).2
  right_inv := fun a => by
    simpa using eq_of_hom (h.counit_iso.app (discrete.mk a)).1

end Discrete

namespace Discrete

variable {J : Type v₁}

open Opposite

-- ./././Mathport/Syntax/Translate/Basic.lean:647:16: unsupported tactic `discrete_cases #[]
-- ./././Mathport/Syntax/Translate/Basic.lean:647:16: unsupported tactic `discrete_cases #[]
/-- A discrete category is equivalent to its opposite category. -/
@[simps functor_obj_as inverse_obj]
protected def opposite (α : Type u₁) : (Discrete α)ᵒᵖ ≌ Discrete α := by
  let F : Discrete α ⥤ (Discrete α)ᵒᵖ := Discrete.functor fun x => op (Discrete.mk x)
  refine'
    equivalence.mk (functor.left_op F) F _
      (discrete.nat_iso fun X => by
        trace "./././Mathport/Syntax/Translate/Basic.lean:647:16: unsupported tactic `discrete_cases #[]"
        simp [← F])
  refine'
    nat_iso.of_components
      (fun X => by
        run_tac
          tactic.op_induction'
        trace "./././Mathport/Syntax/Translate/Basic.lean:647:16: unsupported tactic `discrete_cases #[]"
        simp [← F])
      _
  tidy

variable {C : Type u₂} [Category.{v₂} C]

@[simp]
theorem functor_map_id (F : Discrete J ⥤ C) {j : Discrete J} (f : j ⟶ j) : F.map f = 𝟙 (F.obj j) := by
  have h : f = 𝟙 j := by
    cases f
    cases f
    ext
  rw [h]
  simp

end Discrete

end CategoryTheory

