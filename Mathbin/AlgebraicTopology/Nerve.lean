/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathbin.AlgebraicTopology.SimplicialSet

/-!

# The nerve of a category

This file provides the definition of the nerve of a category `C`,
which is a simplicial set `nerve C` (see [goerss-jardine-2009], Example I.1.4).

## References
* [Paul G. Goerss, John F. Jardine, *Simplical Homotopy Theory*][goerss-jardine-2009]

-/


open CategoryTheory.Category

universe v u

namespace CategoryTheory

/-- The nerve of a category -/
@[simps]
def nerve (C : Type u) [Category.{v} C] : SSet.{max u v} where
  obj := fun Δ => SimplexCategory.toCat.obj Δ.unop ⥤ C
  map := fun Δ₁ Δ₂ f x => SimplexCategory.toCat.map f.unop ⋙ x
  map_id' := fun Δ => by
    rw [unop_id, Functor.map_id]
    ext x
    apply functor.id_comp

instance {C : Type _} [Category C] {Δ : SimplexCategoryᵒᵖ} : Category ((nerve C).obj Δ) :=
  (inferInstance : Category (SimplexCategory.toCat.obj Δ.unop ⥤ C))

/-- The nerve of a category, as a functor `Cat ⥤ sSet` -/
@[simps]
def nerveFunctor : Cat ⥤ SSet where
  obj := fun C => nerve C
  map := fun C C' F => { app := fun Δ x => x ⋙ F }
  map_id' := fun C => by
    ext Δ x
    apply functor.comp_id

end CategoryTheory

