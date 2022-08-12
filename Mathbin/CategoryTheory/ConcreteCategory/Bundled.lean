/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Johannes Hölzl, Reid Barton, Sean Leather
-/
import Mathbin.Tactic.PiInstances

/-!
# Bundled types

`bundled c` provides a uniform structure for bundling a type equipped with a type class.

We provide `category` instances for these in `category_theory/unbundled_hom.lean`
(for categories with unbundled homs, e.g. topological spaces)
and in `category_theory/bundled_hom.lean` (for categories with bundled homs, e.g. monoids).
-/


universe u v

namespace CategoryTheory

variable {c d : Type u → Type v} {α : Type u}

/-- `bundled` is a type bundled with a type class instance for that type. Only
the type class is exposed as a parameter. -/
@[nolint has_inhabited_instance]
structure Bundled (c : Type u → Type v) : Type max (u + 1) v where
  α : Type u
  str : c α := by
    run_tac
      tactic.apply_instance

namespace Bundled

/-- A generic function for lifting a type equipped with an instance to a bundled object. -/
-- Usually explicit instances will provide their own version of this, e.g. `Mon.of` and `Top.of`.
def of {c : Type u → Type v} (α : Type u) [str : c α] : Bundled c :=
  ⟨α, str⟩

instance : CoeSort (Bundled c) (Type u) :=
  ⟨Bundled.α⟩

@[simp]
theorem coe_mk (α) (str) : (@Bundled.mk c α str : Type u) = α :=
  rfl

/-- Map over the bundled structure -/
/-
`bundled.map` is reducible so that, if we define a category

  def Ring : Type (u+1) := induced_category SemiRing (bundled.map @ring.to_semiring)

instance search is able to "see" that a morphism R ⟶ S in Ring is really
a (semi)ring homomorphism from R.α to S.α, and not merely from
`(bundled.map @ring.to_semiring R).α` to `(bundled.map @ring.to_semiring S).α`.
-/
@[reducible]
def map (f : ∀ {α}, c α → d α) (b : Bundled c) : Bundled d :=
  ⟨b, f b.str⟩

end Bundled

end CategoryTheory

