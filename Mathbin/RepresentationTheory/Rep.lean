/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.RepresentationTheory.Action
import Mathbin.Algebra.Category.Module.Abelian
import Mathbin.Algebra.Category.Module.Colimits
import Mathbin.Algebra.Category.Module.Monoidal

/-!
# `Rep k G` is the category of `k`-linear representations of `G`.

If `V : Rep k G`, there is a coercion that allows you to treat `V` as a type,
and this type comes equipped with a `module k V` instance.
Also `V.ρ` gives the homomorphism `G →* (V →ₗ[k] V)`.

Conversely, given a homomorphism `ρ : G →* (V →ₗ[k] V)`,
you can construct the bundled representation as `Rep.of ρ`.

We verify that `Rep k G` is a `k`-linear abelian symmetric monoidal category with all (co)limits.
-/


universe u

open CategoryTheory

open CategoryTheory.Limits

-- ./././Mathport/Syntax/Translate/Basic.lean:1394:31: unsupported: @[derive] abbrev
/-- The category of `k`-linear representations of a monoid `G`. -/
abbrev Rep (k G : Type u) [Ringₓ k] [Monoidₓ G] :=
  Action (ModuleCat.{u} k) (Mon.of G)

instance (k G : Type u) [CommRingₓ k] [Monoidₓ G] : Linear k (Rep k G) := by
  infer_instance

namespace Rep

variable {k G : Type u} [Ringₓ k] [Monoidₓ G]

instance : CoeSort (Rep k G) (Type u) :=
  ConcreteCategory.hasCoeToSort _

instance (V : Rep k G) : AddCommMonoidₓ V := by
  change AddCommMonoidₓ ((forget₂ (Rep k G) (ModuleCat k)).obj V)
  infer_instance

instance (V : Rep k G) : Module k V := by
  change Module k ((forget₂ (Rep k G) (ModuleCat k)).obj V)
  infer_instance

-- This works well with the new design for representations:
example (V : Rep k G) : G →* V →ₗ[k] V :=
  V.ρ

/-- Lift an unbundled representation to `Rep`. -/
@[simps ρ]
def of {V : Type u} [AddCommGroupₓ V] [Module k V] (ρ : G →* V →ₗ[k] V) : Rep k G :=
  ⟨ModuleCat.of k V, ρ⟩

-- Verify that limits are calculated correctly.
noncomputable example : PreservesLimits (forget₂ (Rep k G) (ModuleCat.{u} k)) := by
  infer_instance

noncomputable example : PreservesColimits (forget₂ (Rep k G) (ModuleCat.{u} k)) := by
  infer_instance

end Rep

namespace Rep

variable {k G : Type u} [CommRingₓ k] [Monoidₓ G]

-- Verify that the symmetric monoidal structure is available.
example : SymmetricCategory (Rep k G) := by
  infer_instance

example : MonoidalPreadditive (Rep k G) := by
  infer_instance

example : MonoidalLinear k (Rep k G) := by
  infer_instance

end Rep

