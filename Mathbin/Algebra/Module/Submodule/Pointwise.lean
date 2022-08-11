/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathbin.GroupTheory.Subgroup.Pointwise
import Mathbin.LinearAlgebra.Span

/-! # Pointwise instances on `submodule`s

This file provides:

* `submodule.has_pointwise_neg`

and the actions

* `submodule.pointwise_distrib_mul_action`
* `submodule.pointwise_mul_action_with_zero`

which matches the action of `mul_action_set`.

These actions are available in the `pointwise` locale.

## Implementation notes

Most of the lemmas in this file are direct copies of lemmas from
`group_theory/submonoid/pointwise.lean`.
-/


variable {α : Type _} {R : Type _} {M : Type _}

open Pointwise

namespace Submodule

section Neg

section Semiringₓ

variable [Semiringₓ R] [AddCommGroupₓ M] [Module R M]

/-- The submodule with every element negated. Note if `R` is a ring and not just a semiring, this
is a no-op, as shown by `submodule.neg_eq_self`.

Recall that When `R` is the semiring corresponding to the nonnegative elements of `R'`,
`submodule R' M` is the type of cones of `M`. This instance reflects such cones about `0`.

This is available as an instance in the `pointwise` locale. -/
protected def hasPointwiseNeg :
    Neg
      (Submodule R
        M) where neg := fun p =>
    { -p.toAddSubmonoid with Carrier := -(p : Set M),
      smul_mem' := fun r m hm => Set.mem_neg.2 <| smul_neg r m ▸ p.smul_mem r <| Set.mem_neg.1 hm }

localized [Pointwise] attribute [instance] Submodule.hasPointwiseNeg

open Pointwise

@[simp]
theorem coe_set_neg (S : Submodule R M) : ↑(-S) = -(S : Set M) :=
  rfl

@[simp]
theorem neg_to_add_submonoid (S : Submodule R M) : (-S).toAddSubmonoid = -S.toAddSubmonoid :=
  rfl

@[simp]
theorem mem_neg {g : M} {S : Submodule R M} : g ∈ -S ↔ -g ∈ S :=
  Iff.rfl

/-- `submodule.has_pointwise_neg` is involutive.

This is available as an instance in the `pointwise` locale. -/
protected def hasInvolutivePointwiseNeg : HasInvolutiveNeg (Submodule R M) where
  neg := Neg.neg
  neg_neg := fun S => SetLike.coe_injective <| neg_negₓ _

localized [Pointwise] attribute [instance] Submodule.hasInvolutivePointwiseNeg

@[simp]
theorem neg_le_neg (S T : Submodule R M) : -S ≤ -T ↔ S ≤ T :=
  SetLike.coe_subset_coe.symm.trans Set.neg_subset_neg

theorem neg_le (S T : Submodule R M) : -S ≤ T ↔ S ≤ -T :=
  SetLike.coe_subset_coe.symm.trans Set.neg_subset

/-- `submodule.has_pointwise_neg` as an order isomorphism. -/
def negOrderIso : Submodule R M ≃o Submodule R M where
  toEquiv := Equivₓ.neg _
  map_rel_iff' := neg_le_neg

theorem closure_neg (s : Set M) : span R (-s) = -span R s := by
  apply le_antisymmₓ
  · rw [span_le, coe_set_neg, ← Set.neg_subset, neg_negₓ]
    exact subset_span
    
  · rw [neg_le, span_le, coe_set_neg, ← Set.neg_subset]
    exact subset_span
    

@[simp]
theorem neg_inf (S T : Submodule R M) : -(S⊓T) = -S⊓-T :=
  SetLike.coe_injective Set.inter_neg

@[simp]
theorem neg_sup (S T : Submodule R M) : -(S⊔T) = -S⊔-T :=
  (negOrderIso : Submodule R M ≃o Submodule R M).map_sup S T

@[simp]
theorem neg_bot : -(⊥ : Submodule R M) = ⊥ :=
  SetLike.coe_injective <| (Set.neg_singleton 0).trans <| congr_arg _ neg_zero

@[simp]
theorem neg_top : -(⊤ : Submodule R M) = ⊤ :=
  SetLike.coe_injective <| Set.neg_univ

@[simp]
theorem neg_infi {ι : Sort _} (S : ι → Submodule R M) : (-⨅ i, S i) = ⨅ i, -S i :=
  (negOrderIso : Submodule R M ≃o Submodule R M).map_infi _

@[simp]
theorem neg_supr {ι : Sort _} (S : ι → Submodule R M) : (-⨆ i, S i) = ⨆ i, -S i :=
  (negOrderIso : Submodule R M ≃o Submodule R M).map_supr _

end Semiringₓ

open Pointwise

@[simp]
theorem neg_eq_self [Ringₓ R] [AddCommGroupₓ M] [Module R M] (p : Submodule R M) : -p = p :=
  ext fun _ => p.neg_mem_iff

end Neg

variable [Semiringₓ R] [AddCommMonoidₓ M] [Module R M]

instance pointwiseAddCommMonoid : AddCommMonoidₓ (Submodule R M) where
  add := (·⊔·)
  add_assoc := fun _ _ _ => sup_assoc
  zero := ⊥
  zero_add := fun _ => bot_sup_eq
  add_zero := fun _ => sup_bot_eq
  add_comm := fun _ _ => sup_comm

@[simp]
theorem add_eq_sup (p q : Submodule R M) : p + q = p⊔q :=
  rfl

@[simp]
theorem zero_eq_bot : (0 : Submodule R M) = ⊥ :=
  rfl

instance : CanonicallyOrderedAddMonoid (Submodule R M) :=
  { Submodule.pointwiseAddCommMonoid, Submodule.completeLattice with zero := 0, bot := ⊥, add := (· + ·),
    add_le_add_left := fun a b => sup_le_sup_left, exists_add_of_le := fun a b h => ⟨b, (sup_eq_right.2 h).symm⟩,
    le_self_add := fun a b => le_sup_left }

section

variable [Monoidₓ α] [DistribMulAction α M] [SmulCommClass α R M]

/-- The action on a submodule corresponding to applying the action to every element.

This is available as an instance in the `pointwise` locale. -/
protected def pointwiseDistribMulAction : DistribMulAction α (Submodule R M) where
  smul := fun a S => S.map (DistribMulAction.toLinearMap _ _ a)
  one_smul := fun S => (congr_arg (fun f => S.map f) (LinearMap.ext <| one_smul α)).trans S.map_id
  mul_smul := fun a₁ a₂ S =>
    (congr_arg (fun f : M →ₗ[R] M => S.map f) (LinearMap.ext <| mul_smul _ _)).trans (S.map_comp _ _)
  smul_zero := fun a => map_bot _
  smul_add := fun a S₁ S₂ => map_sup _ _ _

localized [Pointwise] attribute [instance] Submodule.pointwiseDistribMulAction

open Pointwise

@[simp]
theorem coe_pointwise_smul (a : α) (S : Submodule R M) : ↑(a • S) = a • (S : Set M) :=
  rfl

@[simp]
theorem pointwise_smul_to_add_submonoid (a : α) (S : Submodule R M) : (a • S).toAddSubmonoid = a • S.toAddSubmonoid :=
  rfl

@[simp]
theorem pointwise_smul_to_add_subgroup {R M : Type _} [Ringₓ R] [AddCommGroupₓ M] [DistribMulAction α M] [Module R M]
    [SmulCommClass α R M] (a : α) (S : Submodule R M) : (a • S).toAddSubgroup = a • S.toAddSubgroup :=
  rfl

theorem smul_mem_pointwise_smul (m : M) (a : α) (S : Submodule R M) : m ∈ S → a • m ∈ a • S :=
  (Set.smul_mem_smul_set : _ → _ ∈ a • (S : Set M))

instance pointwise_central_scalar [DistribMulAction αᵐᵒᵖ M] [SmulCommClass αᵐᵒᵖ R M] [IsCentralScalar α M] :
    IsCentralScalar α (Submodule R M) :=
  ⟨fun a S => (congr_arg fun f => S.map f) <| LinearMap.ext <| op_smul_eq_smul _⟩

@[simp]
theorem smul_le_self_of_tower {α : Type _} [Semiringₓ α] [Module α R] [Module α M] [SmulCommClass α R M]
    [IsScalarTower α R M] (a : α) (S : Submodule R M) : a • S ≤ S := by
  rintro y ⟨x, hx, rfl⟩
  exact smul_of_tower_mem _ a hx

end

section

variable [Semiringₓ α] [Module α M] [SmulCommClass α R M]

/-- The action on a submodule corresponding to applying the action to every element.

This is available as an instance in the `pointwise` locale.

This is a stronger version of `submodule.pointwise_distrib_mul_action`. Note that `add_smul` does
not hold so this cannot be stated as a `module`. -/
protected def pointwiseMulActionWithZero : MulActionWithZero α (Submodule R M) :=
  { Submodule.pointwiseDistribMulAction with
    zero_smul := fun S => (congr_arg (fun f : M →ₗ[R] M => S.map f) (LinearMap.ext <| zero_smul α)).trans S.map_zero }

localized [Pointwise] attribute [instance] Submodule.pointwiseMulActionWithZero

end

end Submodule

