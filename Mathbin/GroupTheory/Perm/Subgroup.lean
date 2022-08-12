/-
Copyright (c) 2020 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathbin.GroupTheory.Perm.Basic
import Mathbin.Data.Fintype.Basic
import Mathbin.GroupTheory.Subgroup.Basic

/-!
# Lemmas about subgroups within the permutations (self-equivalences) of a type `α`

This file provides extra lemmas about some `subgroup`s that exist within `equiv.perm α`.
`group_theory.subgroup` depends on `group_theory.perm.basic`, so these need to be in a separate
file.

It also provides decidable instances on membership in these subgroups, since
`monoid_hom.decidable_mem_range` cannot be inferred without the help of a lambda.
The presence of these instances induces a `fintype` instance on the `quotient_group.quotient` of
these subgroups.
-/


namespace Equivₓ

namespace Perm

universe u

instance sumCongrHom.decidableMemRange {α β : Type _} [DecidableEq α] [DecidableEq β] [Fintype α] [Fintype β] :
    DecidablePred (· ∈ (sumCongrHom α β).range) := fun x => inferInstance

@[simp]
theorem sumCongrHom.card_range {α β : Type _} [Fintype (sumCongrHom α β).range] [Fintype (Perm α × Perm β)] :
    Fintype.card (sumCongrHom α β).range = Fintype.card (Perm α × Perm β) :=
  Fintype.card_eq.mpr ⟨(ofInjective (sumCongrHom α β) sum_congr_hom_injective).symm⟩

instance sigmaCongrRightHom.decidableMemRange {α : Type _} {β : α → Type _} [DecidableEq α] [∀ a, DecidableEq (β a)]
    [Fintype α] [∀ a, Fintype (β a)] : DecidablePred (· ∈ (sigmaCongrRightHom β).range) := fun x => inferInstance

@[simp]
theorem sigmaCongrRightHom.card_range {α : Type _} {β : α → Type _} [Fintype (sigmaCongrRightHom β).range]
    [Fintype (∀ a, Perm (β a))] : Fintype.card (sigmaCongrRightHom β).range = Fintype.card (∀ a, Perm (β a)) :=
  Fintype.card_eq.mpr ⟨(ofInjective (sigmaCongrRightHom β) sigma_congr_right_hom_injective).symm⟩

instance subtypeCongrHom.decidableMemRange {α : Type _} (p : α → Prop) [DecidablePred p]
    [Fintype (Perm { a // p a } × Perm { a // ¬p a })] [DecidableEq (Perm α)] :
    DecidablePred (· ∈ (subtypeCongrHom p).range) := fun x => inferInstance

@[simp]
theorem subtypeCongrHom.card_range {α : Type _} (p : α → Prop) [DecidablePred p] [Fintype (subtypeCongrHom p).range]
    [Fintype (Perm { a // p a } × Perm { a // ¬p a })] :
    Fintype.card (subtypeCongrHom p).range = Fintype.card (Perm { a // p a } × Perm { a // ¬p a }) :=
  Fintype.card_eq.mpr ⟨(ofInjective (subtypeCongrHom p) (subtype_congr_hom_injective p)).symm⟩

/-- **Cayley's theorem**: Every group G is isomorphic to a subgroup of the symmetric group acting on
`G`. Note that we generalize this to an arbitrary "faithful" group action by `G`. Setting `H = G`
recovers the usual statement of Cayley's theorem via `right_cancel_monoid.to_has_faithful_smul` -/
noncomputable def subgroupOfMulAction (G H : Type _) [Groupₓ G] [MulAction G H] [HasFaithfulSmul G H] :
    G ≃* (MulAction.toPermHom G H).range :=
  MulEquiv.ofLeftInverse' _ (Classical.some_spec MulAction.to_perm_injective.HasLeftInverse)

end Perm

end Equivₓ

