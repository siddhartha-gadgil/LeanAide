/-
Copyright (c) 2021 David Wärn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wärn
-/
import Mathbin.Data.Set.Basic
import Mathbin.Combinatorics.Quiver.Basic

/-!
## Wide subquivers

A wide subquiver `H` of a quiver `H` consists of a subset of the edge set `a ⟶ b` for
every pair of vertices `a b : V`. We include 'wide' in the name to emphasize that these
subquivers by definition contain all vertices.
-/


universe v u

/-- A wide subquiver `H` of `G` picks out a set `H a b` of arrows from `a` to `b`
    for every pair of vertices `a b`.

    NB: this does not work for `Prop`-valued quivers. It requires `G : quiver.{v+1} V`. -/
def WideSubquiver (V) [Quiver.{v + 1} V] :=
  ∀ a b : V, Set (a ⟶ b)

/-- A type synonym for `V`, when thought of as a quiver having only the arrows from
some `wide_subquiver`. -/
@[nolint unused_arguments has_inhabited_instance]
def WideSubquiver.ToType (V) [Quiver V] (H : WideSubquiver V) : Type u :=
  V

instance wideSubquiverHasCoeToSort {V} [Quiver V] :
    CoeSort (WideSubquiver V) (Type u) where coe := fun H => WideSubquiver.ToType V H

/-- A wide subquiver viewed as a quiver on its own. -/
instance WideSubquiver.quiver {V} [Quiver V] (H : WideSubquiver V) : Quiver H :=
  ⟨fun a b => H a b⟩

namespace Quiver

instance {V} [Quiver V] : HasBot (WideSubquiver V) :=
  ⟨fun a b => ∅⟩

instance {V} [Quiver V] : HasTop (WideSubquiver V) :=
  ⟨fun a b => Set.Univ⟩

instance {V} [Quiver V] : Inhabited (WideSubquiver V) :=
  ⟨⊤⟩

/-- `total V` is the type of _all_ arrows of `V`. -/
-- TODO Unify with `category_theory.arrow`? (The fields have been named to match.)
@[ext, nolint has_inhabited_instance]
structure Total (V : Type u) [Quiver.{v} V] : Sort max (u + 1) v where
  left : V
  right : V
  Hom : left ⟶ right

/-- A wide subquiver of `G` can equivalently be viewed as a total set of arrows. -/
def wideSubquiverEquivSetTotal {V} [Quiver V] : WideSubquiver V ≃ Set (Total V) where
  toFun := fun H => { e | e.Hom ∈ H e.left e.right }
  invFun := fun S a b => { e | Total.mk a b e ∈ S }
  left_inv := fun H => rfl
  right_inv := by
    intro S
    ext
    cases x
    rfl

/-- An `L`-labelling of a quiver assigns to every arrow an element of `L`. -/
def Labelling (V : Type u) [Quiver V] (L : Sort _) :=
  ∀ ⦃a b : V⦄, (a ⟶ b) → L

instance {V : Type u} [Quiver V] (L) [Inhabited L] : Inhabited (Labelling V L) :=
  ⟨fun a b e => default⟩

end Quiver

