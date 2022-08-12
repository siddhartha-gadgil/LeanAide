/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.CategoryTheory.Functor.LeftDerived
import Mathbin.CategoryTheory.Monoidal.Preadditive

/-!
# Tor, the left-derived functor of tensor product

We define `Tor C n : C ⥤ C ⥤ C`, by left-deriving in the second factor of `(X, Y) ↦ X ⊗ Y`.

For now we have almost nothing to say about it!

It would be good to show that this is naturally isomorphic to the functor obtained
by left-deriving in the first factor, instead.
For now we define `Tor'` by left-deriving in the first factor,
but showing `Tor C n ≅ Tor' C n` will require a bit more theory!
Possibly it's best to axiomatize delta functors, and obtain a unique characterisation?

-/


noncomputable section

open CategoryTheory.Limits

open CategoryTheory.MonoidalCategory

namespace CategoryTheory

variable {C : Type _} [Category C] [MonoidalCategory C] [Preadditive C] [MonoidalPreadditive C] [HasZeroObject C]
  [HasEqualizers C] [HasCokernels C] [HasImages C] [HasImageMaps C] [HasProjectiveResolutions C]

variable (C)

/-- We define `Tor C n : C ⥤ C ⥤ C` by left-deriving in the second factor of `(X, Y) ↦ X ⊗ Y`. -/
@[simps]
def tor (n : ℕ) : C ⥤ C ⥤ C where
  obj := fun X => Functor.leftDerived ((tensoringLeft C).obj X) n
  map := fun X Y f => NatTrans.leftDerived ((tensoringLeft C).map f) n
  map_id' := fun X => by
    rw [(tensoring_left C).map_id, nat_trans.left_derived_id]
  map_comp' := fun X Y Z f g => by
    rw [(tensoring_left C).map_comp, nat_trans.left_derived_comp]

/-- An alternative definition of `Tor`, where we left-derive in the first factor instead. -/
@[simps]
def tor' (n : ℕ) : C ⥤ C ⥤ C :=
  Functor.flip
    { obj := fun X => Functor.leftDerived ((tensoringRight C).obj X) n,
      map := fun X Y f => NatTrans.leftDerived ((tensoringRight C).map f) n,
      map_id' := fun X => by
        rw [(tensoring_right C).map_id, nat_trans.left_derived_id],
      map_comp' := fun X Y Z f g => by
        rw [(tensoring_right C).map_comp, nat_trans.left_derived_comp] }

open ZeroObject

/-- The higher `Tor` groups for `X` and `Y` are zero if `Y` is projective. -/
def torSuccOfProjective (X Y : C) [Projective Y] (n : ℕ) : ((tor C (n + 1)).obj X).obj Y ≅ 0 :=
  ((tensoringLeft C).obj X).leftDerivedObjProjectiveSucc n Y

/-- The higher `Tor'` groups for `X` and `Y` are zero if `X` is projective. -/
def tor'SuccOfProjective (X Y : C) [Projective X] (n : ℕ) : ((tor' C (n + 1)).obj X).obj Y ≅ 0 := by
  -- This unfortunately needs a manual `dsimp`, to avoid a slow unification problem.
  dsimp' only [← Tor', ← functor.flip]
  exact ((tensoring_right C).obj Y).leftDerivedObjProjectiveSucc n X

end CategoryTheory

