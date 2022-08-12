/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.CategoryTheory.Yoneda
import Mathbin.Topology.Sheaves.Presheaf
import Mathbin.Topology.Category.TopCommRing
import Mathbin.Topology.ContinuousFunction.Algebra

/-!
# Presheaves of functions

We construct some simple examples of presheaves of functions on a topological space.
* `presheaf_to_Types X T`, where `T : X → Type`,
  is the presheaf of dependently-typed (not-necessarily continuous) functions
* `presheaf_to_Type X T`, where `T : Type`,
  is the presheaf of (not-necessarily-continuous) functions to a fixed target type `T`
* `presheaf_to_Top X T`, where `T : Top`,
  is the presheaf of continuous functions into a topological space `T`
* `presheaf_To_TopCommRing X R`, where `R : TopCommRing`
  is the presheaf valued in `CommRing` of functions functions into a topological ring `R`
* as an example of the previous construction,
  `presheaf_to_TopCommRing X (TopCommRing.of ℂ)`
  is the presheaf of rings of continuous complex-valued functions on `X`.
-/


universe v u

open CategoryTheory

open TopologicalSpace

open Opposite

namespace Top

variable (X : Top.{v})

/-- The presheaf of dependently typed functions on `X`, with fibres given by a type family `T`.
There is no requirement that the functions are continuous, here.
-/
def presheafToTypes (T : X → Type v) : X.Presheaf (Type v) where
  obj := fun U => ∀ x : unop U, T x
  map := fun U V i g => fun x : unop V => g (i.unop x)

@[simp]
theorem presheaf_to_Types_obj {T : X → Type v} {U : (Opens X)ᵒᵖ} : (presheafToTypes X T).obj U = ∀ x : unop U, T x :=
  rfl

@[simp]
theorem presheaf_to_Types_map {T : X → Type v} {U V : (Opens X)ᵒᵖ} {i : U ⟶ V} {f} :
    (presheafToTypes X T).map i f = fun x => f (i.unop x) :=
  rfl

/-- The presheaf of functions on `X` with values in a type `T`.
There is no requirement that the functions are continuous, here.
-/
-- We don't just define this in terms of `presheaf_to_Types`,
-- as it's helpful later to see (at a syntactic level) that `(presheaf_to_Type X T).obj U`
-- is a non-dependent function.
-- We don't use `@[simps]` to generate the projection lemmas here,
-- as it turns out to be useful to have `presheaf_to_Type_map`
-- written as an equality of functions (rather than being applied to some argument).
def presheafToType (T : Type v) : X.Presheaf (Type v) where
  obj := fun U => unop U → T
  map := fun U V i g => g ∘ i.unop

@[simp]
theorem presheaf_to_Type_obj {T : Type v} {U : (Opens X)ᵒᵖ} : (presheafToType X T).obj U = (unop U → T) :=
  rfl

@[simp]
theorem presheaf_to_Type_map {T : Type v} {U V : (Opens X)ᵒᵖ} {i : U ⟶ V} {f} :
    (presheafToType X T).map i f = f ∘ i.unop :=
  rfl

/-- The presheaf of continuous functions on `X` with values in fixed target topological space
`T`. -/
def presheafToTop (T : Top.{v}) : X.Presheaf (Type v) :=
  (Opens.toTop X).op ⋙ yoneda.obj T

@[simp]
theorem presheaf_to_Top_obj (T : Top.{v}) (U : (Opens X)ᵒᵖ) :
    (presheafToTop X T).obj U = ((Opens.toTop X).obj (unop U) ⟶ T) :=
  rfl

/-- The (bundled) commutative ring of continuous functions from a topological space
to a topological commutative ring, with pointwise multiplication. -/
-- TODO upgrade the result to TopCommRing?
def continuousFunctions (X : Top.{v}ᵒᵖ) (R : TopCommRing.{v}) : CommRingₓₓ.{v} :=
  CommRingₓₓ.of (unop X ⟶ (forget₂ TopCommRing Top).obj R)

namespace ContinuousFunctions

/-- Pulling back functions into a topological ring along a continuous map is a ring homomorphism. -/
def pullback {X Y : Topᵒᵖ} (f : X ⟶ Y) (R : TopCommRing) : continuousFunctions X R ⟶ continuousFunctions Y R where
  toFun := fun g => f.unop ≫ g
  map_one' := rfl
  map_zero' := rfl
  map_add' := by
    tidy
  map_mul' := by
    tidy

/-- A homomorphism of topological rings can be postcomposed with functions from a source space `X`;
this is a ring homomorphism (with respect to the pointwise ring operations on functions). -/
def map (X : Top.{u}ᵒᵖ) {R S : TopCommRing.{u}} (φ : R ⟶ S) : continuousFunctions X R ⟶ continuousFunctions X S where
  toFun := fun g => g ≫ (forget₂ TopCommRing Top).map φ
  map_one' := by
    ext <;> exact φ.1.map_one
  map_zero' := by
    ext <;> exact φ.1.map_zero
  map_add' := by
    intros <;> ext <;> apply φ.1.map_add
  map_mul' := by
    intros <;> ext <;> apply φ.1.map_mul

end ContinuousFunctions

/-- An upgraded version of the Yoneda embedding, observing that the continuous maps
from `X : Top` to `R : TopCommRing` form a commutative ring, functorial in both `X` and `R`. -/
def commRingYoneda : TopCommRing.{u} ⥤ Top.{u}ᵒᵖ ⥤ CommRingₓₓ.{u} where
  obj := fun R => { obj := fun X => continuousFunctions X R, map := fun X Y f => continuousFunctions.pullback f R }
  map := fun R S φ => { app := fun X => continuousFunctions.map X φ }

/-- The presheaf (of commutative rings), consisting of functions on an open set `U ⊆ X` with
values in some topological commutative ring `T`.

For example, we could construct the presheaf of continuous complex valued functions of `X` as
```
presheaf_to_TopCommRing X (TopCommRing.of ℂ)
```
(this requires `import topology.instances.complex`).
-/
def presheafToTopCommRing (T : TopCommRing.{v}) : X.Presheaf CommRingₓₓ.{v} :=
  (Opens.toTop X).op ⋙ commRingYoneda.obj T

end Top

