/-
Copyright (c) 2022 Hanting Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hanting Zhang
-/
import Mathbin.LinearAlgebra.AffineSpace.AffineSubspace

/-! # Pointwise instances on `affine_subspace`s

This file provides the additive action `affine_subspace.pointwise_add_action` in the
`pointwise` locale.

-/


open Affine Pointwise

open Set

namespace AffineSubspace

variable {k : Type _} [Ringₓ k]

variable {V P V₁ P₁ V₂ P₂ : Type _}

variable [AddCommGroupₓ V] [Module k V] [affine_space V P]

variable [AddCommGroupₓ V₁] [Module k V₁] [AddTorsor V₁ P₁]

variable [AddCommGroupₓ V₂] [Module k V₂] [AddTorsor V₂ P₂]

include V

/-- The additive action on an affine subspace corresponding to applying the action to every element.

This is available as an instance in the `pointwise` locale. -/
protected def pointwiseAddAction : AddAction V (AffineSubspace k P) where
  vadd := fun x S => S.map (AffineEquiv.constVadd k P x)
  zero_vadd := fun p => ((congr_arg fun f => p.map f) <| AffineMap.ext <| zero_vadd _).trans p.map_id
  add_vadd := fun x y p => ((congr_arg fun f => p.map f) <| AffineMap.ext <| add_vadd _ _).trans (p.map_map _ _).symm

localized [Pointwise] attribute [instance] AffineSubspace.pointwiseAddAction

open Pointwise

@[simp]
theorem coe_pointwise_vadd (v : V) (s : AffineSubspace k P) : ((v +ᵥ s : AffineSubspace k P) : Set P) = v +ᵥ s :=
  rfl

theorem vadd_mem_pointwise_vadd_iff {v : V} {s : AffineSubspace k P} {p : P} : v +ᵥ p ∈ v +ᵥ s ↔ p ∈ s :=
  vadd_mem_vadd_set_iff

theorem pointwise_vadd_bot (v : V) : v +ᵥ (⊥ : AffineSubspace k P) = ⊥ := by
  ext
  simp

theorem pointwise_vadd_direction (v : V) (s : AffineSubspace k P) : (v +ᵥ s).direction = s.direction := by
  unfold HasVadd.vadd
  rw [map_direction]
  exact Submodule.map_id _

theorem pointwise_vadd_span (v : V) (s : Set P) : v +ᵥ affineSpan k s = affineSpan k (v +ᵥ s) :=
  map_span _ s

omit V

include V₁ V₂

theorem map_pointwise_vadd (f : P₁ →ᵃ[k] P₂) (v : V₁) (s : AffineSubspace k P₁) :
    (v +ᵥ s).map f = f.linear v +ᵥ s.map f := by
  unfold HasVadd.vadd
  rw [map_map, map_map]
  congr 1
  ext
  exact f.map_vadd _ _

end AffineSubspace

