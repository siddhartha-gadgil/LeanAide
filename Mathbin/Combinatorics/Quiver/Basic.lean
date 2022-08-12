/-
Copyright (c) 2021 David Wärn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wärn, Scott Morrison
-/
import Mathbin.Data.Opposite

/-!
# Quivers

This module defines quivers. A quiver on a type `V` of vertices assigns to every
pair `a b : V` of vertices a type `a ⟶ b` of arrows from `a` to `b`. This
is a very permissive notion of directed graph.

## Implementation notes

Currently `quiver` is defined with `arrow : V → V → Sort v`.
This is different from the category theory setup,
where we insist that morphisms live in some `Type`.
There's some balance here: it's nice to allow `Prop` to ensure there are no multiple arrows,
but it is also results in error-prone universe signatures when constraints require a `Type`.
-/


open Opposite

-- We use the same universe order as in category theory.
-- See note [category_theory universes]
universe v v₁ v₂ u u₁ u₂

/-- A quiver `G` on a type `V` of vertices assigns to every pair `a b : V` of vertices
a type `a ⟶ b` of arrows from `a` to `b`.

For graphs with no repeated edges, one can use `quiver.{0} V`, which ensures
`a ⟶ b : Prop`. For multigraphs, one can use `quiver.{v+1} V`, which ensures
`a ⟶ b : Type v`.

Because `category` will later extend this class, we call the field `hom`.
Except when constructing instances, you should rarely see this, and use the `⟶` notation instead.
-/
class Quiver (V : Type u) where
  Hom : V → V → Sort v

-- mathport name: «expr ⟶ »
infixr:10 " ⟶ " => Quiver.Hom

-- ./././Mathport/Syntax/Translate/Basic.lean:1440:30: infer kinds are unsupported in Lean 4: #[`obj] []
/-- A morphism of quivers. As we will later have categorical functors extend this structure,
we call it a `prefunctor`.
-/
-- type as \h
structure Prefunctor (V : Type u₁) [Quiver.{v₁} V] (W : Type u₂) [Quiver.{v₂} W] where
  obj : V → W
  map : ∀ {X Y : V}, (X ⟶ Y) → (obj X ⟶ obj Y)

namespace Prefunctor

/-- The identity morphism between quivers.
-/
@[simps]
def id (V : Type _) [Quiver V] : Prefunctor V V where
  obj := id
  map := fun X Y f => f

instance (V : Type _) [Quiver V] : Inhabited (Prefunctor V V) :=
  ⟨id V⟩

/-- Composition of morphisms between quivers.
-/
@[simps]
def comp {U : Type _} [Quiver U] {V : Type _} [Quiver V] {W : Type _} [Quiver W] (F : Prefunctor U V)
    (G : Prefunctor V W) : Prefunctor U W where
  obj := fun X => G.obj (F.obj X)
  map := fun X Y f => G.map (F.map f)

end Prefunctor

namespace Quiver

/-- `Vᵒᵖ` reverses the direction of all arrows of `V`. -/
instance opposite {V} [Quiver V] : Quiver Vᵒᵖ :=
  ⟨fun a b => unop b ⟶ unop a⟩

/-- The opposite of an arrow in `V`.
-/
def Hom.op {V} [Quiver V] {X Y : V} (f : X ⟶ Y) : op Y ⟶ op X :=
  f

/-- Given an arrow in `Vᵒᵖ`, we can take the "unopposite" back in `V`.
-/
def Hom.unop {V} [Quiver V] {X Y : Vᵒᵖ} (f : X ⟶ Y) : unop Y ⟶ unop X :=
  f

/-- A type synonym for a quiver with no arrows. -/
@[nolint has_inhabited_instance]
def Empty (V) : Type u :=
  V

instance emptyQuiver (V : Type u) : Quiver.{u} (Empty V) :=
  ⟨fun a b => Pempty⟩

@[simp]
theorem empty_arrow {V : Type u} (a b : Empty V) : (a ⟶ b) = Pempty :=
  rfl

end Quiver

