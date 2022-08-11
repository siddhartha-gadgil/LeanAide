/-
Copyright (c) 2021 Yourong Zang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yourong Zang
-/
import Mathbin.Analysis.Calculus.Conformal.NormedSpace
import Mathbin.Geometry.Manifold.ChartedSpace

/-!
# Conformal Groupoid

In this file we define the groupoid of conformal maps on normed spaces.

## Main definitions

* `conformal_groupoid`: the groupoid of conformal local homeomorphisms.

## Tags

conformal, groupoid
-/


variable {X : Type _} [NormedGroup X] [NormedSpace ℝ X]

/-- The pregroupoid of conformal maps. -/
def conformalPregroupoid : Pregroupoid X where
  property := fun f u => ∀ x, x ∈ u → ConformalAt f x
  comp := fun f g u v hf hg hu hv huv x hx => (hg (f x) hx.2).comp x (hf x hx.1)
  id_mem := fun x hx => conformal_at_id x
  locality := fun f u hu h x hx =>
    let ⟨v, h₁, h₂, h₃⟩ := h x hx
    h₃ x ⟨hx, h₂⟩
  congr := fun f g u hu h hf x hx => (hf x hx).congr hx hu h

/-- The groupoid of conformal maps. -/
def conformalGroupoid : StructureGroupoid X :=
  conformalPregroupoid.groupoid

