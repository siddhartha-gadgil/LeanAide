/-
Copyright (c) 2021 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
import Mathbin.Topology.Algebra.FilterBasis
import Mathbin.Topology.Algebra.UniformGroup

/-!
# Uniform properties of neighborhood bases in topological algebra

This files contains properties of filter bases on algebraic structures that also require the theory
of uniform spaces.

The only result so far is a characterization of Cauchy filters in topological groups.

-/


open uniformity Filter

open Filter

namespace AddGroupFilterBasis

variable {G : Type _} [AddCommGroupₓ G] (B : AddGroupFilterBasis G)

/-- The uniform space structure associated to an abelian group filter basis via the associated
topological abelian group structure. -/
protected def uniformSpace : UniformSpace G :=
  @TopologicalAddGroup.toUniformSpace G _ B.topology B.is_topological_add_group

/-- The uniform space structure associated to an abelian group filter basis via the associated
topological abelian group structure is compatible with its group structure. -/
protected theorem uniform_add_group : @UniformAddGroup G B.UniformSpace _ :=
  @topological_add_group_is_uniform G _ B.topology B.is_topological_add_group

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (x y «expr ∈ » M)
-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (x y «expr ∈ » M)
theorem cauchy_iff {F : Filter G} :
    @Cauchy G B.UniformSpace F ↔ F.ne_bot ∧ ∀, ∀ U ∈ B, ∀, ∃ M ∈ F, ∀ (x y) (_ : x ∈ M) (_ : y ∈ M), y - x ∈ U := by
  let this := B.uniform_space
  have := B.uniform_add_group
  suffices F ×ᶠ F ≤ 𝓤 G ↔ ∀, ∀ U ∈ B, ∀, ∃ M ∈ F, ∀ (x y) (_ : x ∈ M) (_ : y ∈ M), y - x ∈ U by
    constructor <;> rintro ⟨h', h⟩ <;> refine' ⟨h', _⟩ <;> [rwa [← this], rwa [this]]
  rw [uniformity_eq_comap_nhds_zero G, ← map_le_iff_le_comap]
  change tendsto _ _ _ ↔ _
  simp [← (basis_sets F).prod_self.tendsto_iff B.nhds_zero_has_basis, ← @forall_swap (_ ∈ _) G]

end AddGroupFilterBasis

