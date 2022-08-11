/-
Copyright (c) 2021 David Wärn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wärn
-/
import Mathbin.Combinatorics.Quiver.Subquiver
import Mathbin.Combinatorics.Quiver.Path

/-!
## Weakly connected components

For a quiver `V`, we build a quiver `symmetrify V` by adding a reversal of every edge.
Informally, a path in `symmetrify V` corresponds to a 'zigzag' in `V`. This lets us
define the type `weakly_connected_component V` as the quotient of `V` by the relation which
identifies `a` with `b` if there is a path from `a` to `b` in `symmetrify V`. (These
zigzags can be seen as a proof-relevant analogue of `eqv_gen`.)

Strongly connected components have not yet been defined.
-/


universe v u

namespace Quiver

/-- A type synonym for the symmetrized quiver (with an arrow both ways for each original arrow).
    NB: this does not work for `Prop`-valued quivers. It requires `[quiver.{v+1} V]`. -/
@[nolint has_inhabited_instance]
def Symmetrify (V) : Type u :=
  V

instance symmetrifyQuiver (V : Type u) [Quiver V] : Quiver (Symmetrify V) :=
  ⟨fun a b : V => Sum (a ⟶ b) (b ⟶ a)⟩

variable (V : Type u) [Quiver.{v + 1} V]

/-- A quiver `has_reverse` if we can reverse an arrow `p` from `a` to `b` to get an arrow
    `p.reverse` from `b` to `a`.-/
class HasReverse where
  reverse' : ∀ {a b : V}, (a ⟶ b) → (b ⟶ a)

instance : HasReverse (Symmetrify V) :=
  ⟨fun a b e => e.swap⟩

variable {V}

/-- Reverse the direction of an arrow. -/
def reverse [HasReverse V] {a b : V} : (a ⟶ b) → (b ⟶ a) :=
  has_reverse.reverse'

/-- Reverse the direction of a path. -/
def Path.reverseₓ [HasReverse V] {a : V} : ∀ {b}, Path a b → Path b a
  | a, path.nil => Path.nil
  | b, path.cons p e => (reverse e).toPath.comp p.reverse

variable (V)

/-- Two vertices are related in the zigzag setoid if there is a
    zigzag of arrows from one to the other. -/
def zigzagSetoid : Setoidₓ V :=
  ⟨fun a b => Nonempty (@Path (Symmetrify V) _ a b), fun a => ⟨Path.nil⟩, fun a b ⟨p⟩ => ⟨p.reverse⟩,
    fun a b c ⟨p⟩ ⟨q⟩ => ⟨p.comp q⟩⟩

/-- The type of weakly connected components of a directed graph. Two vertices are
    in the same weakly connected component if there is a zigzag of arrows from one
    to the other. -/
def WeaklyConnectedComponent : Type _ :=
  Quotientₓ (zigzagSetoid V)

namespace WeaklyConnectedComponent

variable {V}

/-- The weakly connected component corresponding to a vertex. -/
protected def mk : V → WeaklyConnectedComponent V :=
  Quotientₓ.mk'

instance : CoeTₓ V (WeaklyConnectedComponent V) :=
  ⟨WeaklyConnectedComponent.mk⟩

instance [Inhabited V] : Inhabited (WeaklyConnectedComponent V) :=
  ⟨show V from default⟩

protected theorem eq (a b : V) : (a : WeaklyConnectedComponent V) = b ↔ Nonempty (@Path (Symmetrify V) _ a b) :=
  Quotientₓ.eq'

end WeaklyConnectedComponent

variable {V}

/-- A wide subquiver `H` of `G.symmetrify` determines a wide subquiver of `G`, containing an
    an arrow `e` if either `e` or its reversal is in `H`. -/
-- Without the explicit universe level in `quiver.{v+1}` Lean comes up with
-- `quiver.{max u_2 u_3 + 1}`. This causes problems elsewhere, so we write `quiver.{v+1}`.
def WideSubquiverSymmetrify (H : WideSubquiver (Symmetrify V)) : WideSubquiver V := fun a b =>
  { e | Sum.inl e ∈ H a b ∨ Sum.inr e ∈ H b a }

end Quiver

