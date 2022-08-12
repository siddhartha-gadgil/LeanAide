/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathbin.GroupTheory.Subgroup.Basic
import Mathbin.GroupTheory.Submonoid.Pointwise

/-! # Pointwise instances on `subgroup` and `add_subgroup`s

This file provides the actions

* `subgroup.pointwise_mul_action`
* `add_subgroup.pointwise_mul_action`

which matches the action of `mul_action_set`.

These actions are available in the `pointwise` locale.

## Implementation notes

This file is almost identical to `group_theory/submonoid/pointwise.lean`. Where possible, try to
keep them in sync.
-/


open Set

variable {α : Type _} {G : Type _} {A : Type _} [Groupₓ G] [AddGroupₓ A]

namespace Subgroup

section Monoidₓ

variable [Monoidₓ α] [MulDistribMulAction α G]

/-- The action on a subgroup corresponding to applying the action to every element.

This is available as an instance in the `pointwise` locale. -/
protected def pointwiseMulAction : MulAction α (Subgroup G) where
  smul := fun a S => S.map (MulDistribMulAction.toMonoidEnd _ _ a)
  one_smul := fun S => (congr_arg (fun f => S.map f) (MonoidHom.map_one _)).trans S.map_id
  mul_smul := fun a₁ a₂ S => (congr_arg (fun f => S.map f) (MonoidHom.map_mul _ _ _)).trans (S.map_map _ _).symm

localized [Pointwise] attribute [instance] Subgroup.pointwiseMulAction

open Pointwise

theorem pointwise_smul_def {a : α} (S : Subgroup G) : a • S = S.map (MulDistribMulAction.toMonoidEnd _ _ a) :=
  rfl

@[simp]
theorem coe_pointwise_smul (a : α) (S : Subgroup G) : ↑(a • S) = a • (S : Set G) :=
  rfl

@[simp]
theorem pointwise_smul_to_submonoid (a : α) (S : Subgroup G) : (a • S).toSubmonoid = a • S.toSubmonoid :=
  rfl

theorem smul_mem_pointwise_smul (m : G) (a : α) (S : Subgroup G) : m ∈ S → a • m ∈ a • S :=
  (Set.smul_mem_smul_set : _ → _ ∈ a • (S : Set G))

theorem mem_smul_pointwise_iff_exists (m : G) (a : α) (S : Subgroup G) : m ∈ a • S ↔ ∃ s : G, s ∈ S ∧ a • s = m :=
  (Set.mem_smul_set : m ∈ a • (S : Set G) ↔ _)

instance pointwise_central_scalar [MulDistribMulAction αᵐᵒᵖ G] [IsCentralScalar α G] : IsCentralScalar α (Subgroup G) :=
  ⟨fun a S => (congr_arg fun f => S.map f) <| MonoidHom.ext <| op_smul_eq_smul _⟩

theorem conj_smul_le_of_le {P H : Subgroup G} (hP : P ≤ H) (h : H) : MulAut.conj (h : G) • P ≤ H := by
  rintro - ⟨g, hg, rfl⟩
  exact H.mul_mem (H.mul_mem h.2 (hP hg)) (H.inv_mem h.2)

theorem conj_smul_subgroup_of {P H : Subgroup G} (hP : P ≤ H) (h : H) :
    MulAut.conj h • P.subgroupOf H = (MulAut.conj (h : G) • P).subgroupOf H := by
  refine' le_antisymmₓ _ _
  · rintro - ⟨g, hg, rfl⟩
    exact ⟨g, hg, rfl⟩
    
  · rintro p ⟨g, hg, hp⟩
    exact ⟨⟨g, hP hg⟩, hg, Subtype.ext hp⟩
    

end Monoidₓ

section Groupₓ

variable [Groupₓ α] [MulDistribMulAction α G]

open Pointwise

@[simp]
theorem smul_mem_pointwise_smul_iff {a : α} {S : Subgroup G} {x : G} : a • x ∈ a • S ↔ x ∈ S :=
  smul_mem_smul_set_iff

theorem mem_pointwise_smul_iff_inv_smul_mem {a : α} {S : Subgroup G} {x : G} : x ∈ a • S ↔ a⁻¹ • x ∈ S :=
  mem_smul_set_iff_inv_smul_mem

theorem mem_inv_pointwise_smul_iff {a : α} {S : Subgroup G} {x : G} : x ∈ a⁻¹ • S ↔ a • x ∈ S :=
  mem_inv_smul_set_iff

@[simp]
theorem pointwise_smul_le_pointwise_smul_iff {a : α} {S T : Subgroup G} : a • S ≤ a • T ↔ S ≤ T :=
  set_smul_subset_set_smul_iff

theorem pointwise_smul_subset_iff {a : α} {S T : Subgroup G} : a • S ≤ T ↔ S ≤ a⁻¹ • T :=
  set_smul_subset_iff

theorem subset_pointwise_smul_iff {a : α} {S T : Subgroup G} : S ≤ a • T ↔ a⁻¹ • S ≤ T :=
  subset_set_smul_iff

/-- Applying a `mul_distrib_mul_action` results in an isomorphic subgroup -/
@[simps]
def equivSmul (a : α) (H : Subgroup G) : H ≃* (a • H : Subgroup G) :=
  (MulDistribMulAction.toMulEquiv G a).subgroupMap H

theorem subgroup_mul_singleton {H : Subgroup G} {h : G} (hh : h ∈ H) : (H : Set G) * {h} = H := by
  refine' le_antisymmₓ _ fun h' hh' => ⟨h' * h⁻¹, h, H.mul_mem hh' (H.inv_mem hh), rfl, inv_mul_cancel_right h' h⟩
  rintro _ ⟨h', h, hh', rfl : _ = _, rfl⟩
  exact H.mul_mem hh' hh

theorem singleton_mul_subgroup {H : Subgroup G} {h : G} (hh : h ∈ H) : {h} * (H : Set G) = H := by
  refine' le_antisymmₓ _ fun h' hh' => ⟨h, h⁻¹ * h', rfl, H.mul_mem (H.inv_mem hh) hh', mul_inv_cancel_left h h'⟩
  rintro _ ⟨h, h', rfl : _ = _, hh', rfl⟩
  exact H.mul_mem hh hh'

end Groupₓ

section GroupWithZeroₓ

variable [GroupWithZeroₓ α] [MulDistribMulAction α G]

open Pointwise

@[simp]
theorem smul_mem_pointwise_smul_iff₀ {a : α} (ha : a ≠ 0) (S : Subgroup G) (x : G) : a • x ∈ a • S ↔ x ∈ S :=
  smul_mem_smul_set_iff₀ ha (S : Set G) x

theorem mem_pointwise_smul_iff_inv_smul_mem₀ {a : α} (ha : a ≠ 0) (S : Subgroup G) (x : G) : x ∈ a • S ↔ a⁻¹ • x ∈ S :=
  mem_smul_set_iff_inv_smul_mem₀ ha (S : Set G) x

theorem mem_inv_pointwise_smul_iff₀ {a : α} (ha : a ≠ 0) (S : Subgroup G) (x : G) : x ∈ a⁻¹ • S ↔ a • x ∈ S :=
  mem_inv_smul_set_iff₀ ha (S : Set G) x

@[simp]
theorem pointwise_smul_le_pointwise_smul_iff₀ {a : α} (ha : a ≠ 0) {S T : Subgroup G} : a • S ≤ a • T ↔ S ≤ T :=
  set_smul_subset_set_smul_iff₀ ha

theorem pointwise_smul_le_iff₀ {a : α} (ha : a ≠ 0) {S T : Subgroup G} : a • S ≤ T ↔ S ≤ a⁻¹ • T :=
  set_smul_subset_iff₀ ha

theorem le_pointwise_smul_iff₀ {a : α} (ha : a ≠ 0) {S T : Subgroup G} : S ≤ a • T ↔ a⁻¹ • S ≤ T :=
  subset_set_smul_iff₀ ha

end GroupWithZeroₓ

end Subgroup

namespace AddSubgroup

section Monoidₓ

variable [Monoidₓ α] [DistribMulAction α A]

/-- The action on an additive subgroup corresponding to applying the action to every element.

This is available as an instance in the `pointwise` locale. -/
protected def pointwiseMulAction : MulAction α (AddSubgroup A) where
  smul := fun a S => S.map (DistribMulAction.toAddMonoidEnd _ _ a)
  one_smul := fun S => (congr_arg (fun f => S.map f) (MonoidHom.map_one _)).trans S.map_id
  mul_smul := fun a₁ a₂ S => (congr_arg (fun f => S.map f) (MonoidHom.map_mul _ _ _)).trans (S.map_map _ _).symm

localized [Pointwise] attribute [instance] AddSubgroup.pointwiseMulAction

open Pointwise

@[simp]
theorem coe_pointwise_smul (a : α) (S : AddSubgroup A) : ↑(a • S) = a • (S : Set A) :=
  rfl

@[simp]
theorem pointwise_smul_to_add_submonoid (a : α) (S : AddSubgroup A) : (a • S).toAddSubmonoid = a • S.toAddSubmonoid :=
  rfl

theorem smul_mem_pointwise_smul (m : A) (a : α) (S : AddSubgroup A) : m ∈ S → a • m ∈ a • S :=
  (Set.smul_mem_smul_set : _ → _ ∈ a • (S : Set A))

theorem mem_smul_pointwise_iff_exists (m : A) (a : α) (S : AddSubgroup A) : m ∈ a • S ↔ ∃ s : A, s ∈ S ∧ a • s = m :=
  (Set.mem_smul_set : m ∈ a • (S : Set A) ↔ _)

instance pointwise_central_scalar [DistribMulAction αᵐᵒᵖ A] [IsCentralScalar α A] : IsCentralScalar α (AddSubgroup A) :=
  ⟨fun a S => (congr_arg fun f => S.map f) <| AddMonoidHom.ext <| op_smul_eq_smul _⟩

end Monoidₓ

section Groupₓ

variable [Groupₓ α] [DistribMulAction α A]

open Pointwise

@[simp]
theorem smul_mem_pointwise_smul_iff {a : α} {S : AddSubgroup A} {x : A} : a • x ∈ a • S ↔ x ∈ S :=
  smul_mem_smul_set_iff

theorem mem_pointwise_smul_iff_inv_smul_mem {a : α} {S : AddSubgroup A} {x : A} : x ∈ a • S ↔ a⁻¹ • x ∈ S :=
  mem_smul_set_iff_inv_smul_mem

theorem mem_inv_pointwise_smul_iff {a : α} {S : AddSubgroup A} {x : A} : x ∈ a⁻¹ • S ↔ a • x ∈ S :=
  mem_inv_smul_set_iff

@[simp]
theorem pointwise_smul_le_pointwise_smul_iff {a : α} {S T : AddSubgroup A} : a • S ≤ a • T ↔ S ≤ T :=
  set_smul_subset_set_smul_iff

theorem pointwise_smul_le_iff {a : α} {S T : AddSubgroup A} : a • S ≤ T ↔ S ≤ a⁻¹ • T :=
  set_smul_subset_iff

theorem le_pointwise_smul_iff {a : α} {S T : AddSubgroup A} : S ≤ a • T ↔ a⁻¹ • S ≤ T :=
  subset_set_smul_iff

end Groupₓ

section GroupWithZeroₓ

variable [GroupWithZeroₓ α] [DistribMulAction α A]

open Pointwise

@[simp]
theorem smul_mem_pointwise_smul_iff₀ {a : α} (ha : a ≠ 0) (S : AddSubgroup A) (x : A) : a • x ∈ a • S ↔ x ∈ S :=
  smul_mem_smul_set_iff₀ ha (S : Set A) x

theorem mem_pointwise_smul_iff_inv_smul_mem₀ {a : α} (ha : a ≠ 0) (S : AddSubgroup A) (x : A) :
    x ∈ a • S ↔ a⁻¹ • x ∈ S :=
  mem_smul_set_iff_inv_smul_mem₀ ha (S : Set A) x

theorem mem_inv_pointwise_smul_iff₀ {a : α} (ha : a ≠ 0) (S : AddSubgroup A) (x : A) : x ∈ a⁻¹ • S ↔ a • x ∈ S :=
  mem_inv_smul_set_iff₀ ha (S : Set A) x

@[simp]
theorem pointwise_smul_le_pointwise_smul_iff₀ {a : α} (ha : a ≠ 0) {S T : AddSubgroup A} : a • S ≤ a • T ↔ S ≤ T :=
  set_smul_subset_set_smul_iff₀ ha

theorem pointwise_smul_le_iff₀ {a : α} (ha : a ≠ 0) {S T : AddSubgroup A} : a • S ≤ T ↔ S ≤ a⁻¹ • T :=
  set_smul_subset_iff₀ ha

theorem le_pointwise_smul_iff₀ {a : α} (ha : a ≠ 0) {S T : AddSubgroup A} : S ≤ a • T ↔ a⁻¹ • S ≤ T :=
  subset_set_smul_iff₀ ha

end GroupWithZeroₓ

end AddSubgroup

