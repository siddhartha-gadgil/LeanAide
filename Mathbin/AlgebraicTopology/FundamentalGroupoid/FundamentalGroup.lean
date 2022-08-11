/-
Copyright (c) 2021 Mark Lavrentyev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mark Lavrentyev
-/
import Mathbin.CategoryTheory.Category.Groupoid
import Mathbin.CategoryTheory.Groupoid
import Mathbin.Topology.Category.Top.Basic
import Mathbin.Topology.PathConnected
import Mathbin.Topology.Homotopy.Path
import Mathbin.AlgebraicTopology.FundamentalGroupoid.Basic

/-!
# Fundamental group of a space

Given a topological space `X` and a basepoint `x`, the fundamental group is the automorphism group
of `x` i.e. the group with elements being loops based at `x` (quotiented by homotopy equivalence).
-/


universe u v

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

variable {x₀ x₁ : X}

noncomputable section

open CategoryTheory

/-- The fundamental group is the automorphism group (vertex group) of the basepoint
in the fundamental groupoid. -/
def FundamentalGroup (X : Type u) [TopologicalSpace X] (x : X) :=
  @Aut (FundamentalGroupoid X) _ x deriving Groupₓ, Inhabited

namespace FundamentalGroup

attribute [local instance] Path.Homotopic.setoid

attribute [local reducible] FundamentalGroupoid

/-- Get an isomorphism between the fundamental groups at two points given a path -/
def fundamentalGroupMulEquivOfPath (p : Path x₀ x₁) : FundamentalGroup X x₀ ≃* FundamentalGroup X x₁ :=
  Aut.autMulEquivOfIso (asIso ⟦p⟧)

variable (x₀ x₁)

/-- The fundamental group of a path connected space is independent of the choice of basepoint. -/
def fundamentalGroupMulEquivOfPathConnected [PathConnectedSpace X] : FundamentalGroup X x₀ ≃* FundamentalGroup X x₁ :=
  fundamentalGroupMulEquivOfPath (PathConnectedSpace.somePath x₀ x₁)

/-- An element of the fundamental group as an arrow in the fundamental groupoid. -/
abbrev toArrow {X : Top} {x : X} (p : FundamentalGroup X x) : x ⟶ x :=
  p.Hom

/-- An element of the fundamental group as a quotient of homotopic paths. -/
abbrev toPath {X : Top} {x : X} (p : FundamentalGroup X x) : Path.Homotopic.Quotient x x :=
  toArrow p

/-- An element of the fundamental group, constructed from an arrow in the fundamental groupoid. -/
abbrev fromArrow {X : Top} {x : X} (p : x ⟶ x) : FundamentalGroup X x :=
  ⟨p, CategoryTheory.Groupoid.inv p⟩

/-- An element of the fundamental gorup, constructed from a quotient of homotopic paths. -/
abbrev fromPath {X : Top} {x : X} (p : Path.Homotopic.Quotient x x) : FundamentalGroup X x :=
  fromArrow p

end FundamentalGroup

