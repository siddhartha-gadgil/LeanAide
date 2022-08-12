/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.CategoryTheory.Preadditive.AdditiveFunctor
import Mathbin.CategoryTheory.Linear.Default

/-!
# Linear Functors

An additive functor between two `R`-linear categories is called *linear*
if the induced map on hom types is a morphism of `R`-modules.

# Implementation details

`functor.linear` is a `Prop`-valued class, defined by saying that
for every two objects `X` and `Y`, the map
`F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y)` is a morphism of `R`-modules.

-/


namespace CategoryTheory

variable (R : Type _) [Semiringₓ R]

/-- An additive functor `F` is `R`-linear provided `F.map` is an `R`-module morphism. -/
class Functor.Linear {C D : Type _} [Category C] [Category D] [Preadditive C] [Preadditive D] [Linear R C] [Linear R D]
  (F : C ⥤ D) [F.Additive] : Prop where
  map_smul' : ∀ {X Y : C} {f : X ⟶ Y} {r : R}, F.map (r • f) = r • F.map f := by
    run_tac
      obviously

section Linear

namespace Functor

section

variable {R} {C D : Type _} [Category C] [Category D] [Preadditive C] [Preadditive D] [CategoryTheory.Linear R C]
  [CategoryTheory.Linear R D] (F : C ⥤ D) [Additive F] [Linear R F]

@[simp]
theorem map_smul {X Y : C} (r : R) (f : X ⟶ Y) : F.map (r • f) = r • F.map f :=
  functor.linear.map_smul'

instance : Linear R (𝟭 C) where

instance {E : Type _} [Category E] [Preadditive E] [CategoryTheory.Linear R E] (G : D ⥤ E) [Additive G] [Linear R G] :
    Linear R (F ⋙ G) where

variable (R)

/-- `F.map_linear_map` is an `R`-linear map whose underlying function is `F.map`. -/
@[simps]
def mapLinearMap {X Y : C} : (X ⟶ Y) →ₗ[R] F.obj X ⟶ F.obj Y :=
  { F.mapAddHom with map_smul' := fun r f => F.map_smul r f }

theorem coe_map_linear_map {X Y : C} : ⇑(F.mapLinearMap R : (X ⟶ Y) →ₗ[R] _) = @map C _ D _ F X Y :=
  rfl

end

section InducedCategory

variable {C : Type _} {D : Type _} [Category D] [Preadditive D] [CategoryTheory.Linear R D] (F : C → D)

instance induced_functor_linear : Functor.Linear R (inducedFunctor F) where

end InducedCategory

section

variable {R} {C D : Type _} [Category C] [Category D] [Preadditive C] [Preadditive D] (F : C ⥤ D) [Additive F]

instance nat_linear : F.Linear ℕ where map_smul' := fun X Y f r => F.mapAddHom.map_nsmul f r

instance int_linear :
    F.Linear ℤ where map_smul' := fun X Y f r => (F.mapAddHom : (X ⟶ Y) →+ (F.obj X ⟶ F.obj Y)).map_zsmul f r

variable [CategoryTheory.Linear ℚ C] [CategoryTheory.Linear ℚ D]

instance rat_linear : F.Linear ℚ where map_smul' := fun X Y f r => F.mapAddHom.toRatLinearMap.map_smul r f

end

end Functor

namespace Equivalenceₓ

variable {C D : Type _} [Category C] [Category D] [Preadditive C] [Linear R C] [Preadditive D] [Linear R D]

instance inverse_linear (e : C ≌ D) [e.Functor.Additive] [e.Functor.Linear R] :
    e.inverse.Linear R where map_smul' := fun X Y r f => by
    apply e.functor.map_injective
    simp

end Equivalenceₓ

end Linear

end CategoryTheory

