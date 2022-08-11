/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathbin.Algebra.Homology.HomologicalComplex

/-!
# Complexes in functor categories

We can view a complex valued in a functor category `T ⥤ V` as
a functor from `T` to complexes valued in `V`.

## Future work
In fact this is an equivalence of categories.

-/


universe v u

open CategoryTheory

open CategoryTheory.Limits

namespace HomologicalComplex

variable {V : Type u} [Category.{v} V] [HasZeroMorphisms V]

variable {ι : Type _} {c : ComplexShape ι}

/-- A complex of functors gives a functor to complexes. -/
@[simps obj map]
def asFunctor {T : Type _} [Category T] (C : HomologicalComplex (T ⥤ V) c) : T ⥤ HomologicalComplex V c where
  obj := fun t =>
    { x := fun i => (C.x i).obj t, d := fun i j => (C.d i j).app t,
      d_comp_d' := fun i j k hij hjk => by
        have := C.d_comp_d i j k
        rw [nat_trans.ext_iff, Function.funext_iffₓ] at this
        exact this t,
      shape' := fun i j h => by
        have := C.shape _ _ h
        rw [nat_trans.ext_iff, Function.funext_iffₓ] at this
        exact this t }
  map := fun t₁ t₂ h => { f := fun i => (C.x i).map h, comm' := fun i j hij => NatTrans.naturality _ _ }
  map_id' := fun t => by
    ext i
    dsimp'
    rw [(C.X i).map_id]
  map_comp' := fun t₁ t₂ t₃ h₁ h₂ => by
    ext i
    dsimp'
    rw [functor.map_comp]

/-- The functorial version of `homological_complex.as_functor`. -/
-- TODO in fact, this is an equivalence of categories.
@[simps]
def complexOfFunctorsToFunctorToComplex {T : Type _} [Category T] :
    HomologicalComplex (T ⥤ V) c ⥤ T ⥤ HomologicalComplex V c where
  obj := fun C => C.asFunctor
  map := fun C D f =>
    { app := fun t => { f := fun i => (f.f i).app t, comm' := fun i j w => NatTrans.congr_app (f.comm i j) t },
      naturality' := fun t t' g => by
        ext i
        exact (f.f i).naturality g }

end HomologicalComplex

