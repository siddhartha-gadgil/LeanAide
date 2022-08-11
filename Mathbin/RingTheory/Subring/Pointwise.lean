/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathbin.RingTheory.Subsemiring.Pointwise
import Mathbin.GroupTheory.Subgroup.Pointwise
import Mathbin.RingTheory.Subring.Basic

/-! # Pointwise instances on `subring`s

This file provides the action `subring.pointwise_mul_action` which matches the action of
`mul_action_set`.

This actions is available in the `pointwise` locale.

## Implementation notes

This file is almost identical to `ring_theory/subsemiring/pointwise.lean`. Where possible, try to
keep them in sync.

-/


open Set

variable {M R : Type _}

namespace Subring

section Monoidₓ

variable [Monoidₓ M] [Ringₓ R] [MulSemiringAction M R]

/-- The action on a subring corresponding to applying the action to every element.

This is available as an instance in the `pointwise` locale. -/
protected def pointwiseMulAction : MulAction M (Subring R) where
  smul := fun a S => S.map (MulSemiringAction.toRingHom _ _ a)
  one_smul := fun S => (congr_arg (fun f => S.map f) (RingHom.ext <| one_smul M)).trans S.map_id
  mul_smul := fun a₁ a₂ S => (congr_arg (fun f => S.map f) (RingHom.ext <| mul_smul _ _)).trans (S.map_map _ _).symm

localized [Pointwise] attribute [instance] Subring.pointwiseMulAction

open Pointwise

theorem pointwise_smul_def {a : M} (S : Subring R) : a • S = S.map (MulSemiringAction.toRingHom _ _ a) :=
  rfl

@[simp]
theorem coe_pointwise_smul (m : M) (S : Subring R) : ↑(m • S) = m • (S : Set R) :=
  rfl

@[simp]
theorem pointwise_smul_to_add_subgroup (m : M) (S : Subring R) : (m • S).toAddSubgroup = m • S.toAddSubgroup :=
  rfl

@[simp]
theorem pointwise_smul_to_subsemiring (m : M) (S : Subring R) : (m • S).toSubsemiring = m • S.toSubsemiring :=
  rfl

theorem smul_mem_pointwise_smul (m : M) (r : R) (S : Subring R) : r ∈ S → m • r ∈ m • S :=
  (Set.smul_mem_smul_set : _ → _ ∈ m • (S : Set R))

theorem mem_smul_pointwise_iff_exists (m : M) (r : R) (S : Subring R) : r ∈ m • S ↔ ∃ s : R, s ∈ S ∧ m • s = r :=
  (Set.mem_smul_set : r ∈ m • (S : Set R) ↔ _)

instance pointwise_central_scalar [MulSemiringAction Mᵐᵒᵖ R] [IsCentralScalar M R] : IsCentralScalar M (Subring R) :=
  ⟨fun a S => (congr_arg fun f => S.map f) <| RingHom.ext <| op_smul_eq_smul _⟩

end Monoidₓ

section Groupₓ

variable [Groupₓ M] [Ringₓ R] [MulSemiringAction M R]

open Pointwise

@[simp]
theorem smul_mem_pointwise_smul_iff {a : M} {S : Subring R} {x : R} : a • x ∈ a • S ↔ x ∈ S :=
  smul_mem_smul_set_iff

theorem mem_pointwise_smul_iff_inv_smul_mem {a : M} {S : Subring R} {x : R} : x ∈ a • S ↔ a⁻¹ • x ∈ S :=
  mem_smul_set_iff_inv_smul_mem

theorem mem_inv_pointwise_smul_iff {a : M} {S : Subring R} {x : R} : x ∈ a⁻¹ • S ↔ a • x ∈ S :=
  mem_inv_smul_set_iff

@[simp]
theorem pointwise_smul_le_pointwise_smul_iff {a : M} {S T : Subring R} : a • S ≤ a • T ↔ S ≤ T :=
  set_smul_subset_set_smul_iff

theorem pointwise_smul_subset_iff {a : M} {S T : Subring R} : a • S ≤ T ↔ S ≤ a⁻¹ • T :=
  set_smul_subset_iff

theorem subset_pointwise_smul_iff {a : M} {S T : Subring R} : S ≤ a • T ↔ a⁻¹ • S ≤ T :=
  subset_set_smul_iff

/-! TODO: add `equiv_smul` like we have for subgroup. -/


end Groupₓ

section GroupWithZeroₓ

variable [GroupWithZeroₓ M] [Ringₓ R] [MulSemiringAction M R]

open Pointwise

@[simp]
theorem smul_mem_pointwise_smul_iff₀ {a : M} (ha : a ≠ 0) (S : Subring R) (x : R) : a • x ∈ a • S ↔ x ∈ S :=
  smul_mem_smul_set_iff₀ ha (S : Set R) x

theorem mem_pointwise_smul_iff_inv_smul_mem₀ {a : M} (ha : a ≠ 0) (S : Subring R) (x : R) : x ∈ a • S ↔ a⁻¹ • x ∈ S :=
  mem_smul_set_iff_inv_smul_mem₀ ha (S : Set R) x

theorem mem_inv_pointwise_smul_iff₀ {a : M} (ha : a ≠ 0) (S : Subring R) (x : R) : x ∈ a⁻¹ • S ↔ a • x ∈ S :=
  mem_inv_smul_set_iff₀ ha (S : Set R) x

@[simp]
theorem pointwise_smul_le_pointwise_smul_iff₀ {a : M} (ha : a ≠ 0) {S T : Subring R} : a • S ≤ a • T ↔ S ≤ T :=
  set_smul_subset_set_smul_iff₀ ha

theorem pointwise_smul_le_iff₀ {a : M} (ha : a ≠ 0) {S T : Subring R} : a • S ≤ T ↔ S ≤ a⁻¹ • T :=
  set_smul_subset_iff₀ ha

theorem le_pointwise_smul_iff₀ {a : M} (ha : a ≠ 0) {S T : Subring R} : S ≤ a • T ↔ a⁻¹ • S ≤ T :=
  subset_set_smul_iff₀ ha

end GroupWithZeroₓ

end Subring

