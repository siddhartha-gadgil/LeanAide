/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
import Mathbin.Analysis.LocallyConvex.Basic
import Mathbin.Order.Closure

/-!
# Balanced Core and Balanced Hull

## Main definitions

* `balanced_core`: The largest balanced subset of a set `s`.
* `balanced_hull`: The smallest balanced superset of a set `s`.

## Main statements

* `balanced_core_eq_Inter`: Characterization of the balanced core as an intersection over subsets.
* `nhds_basis_closed_balanced`: The closed balanced sets form a basis of the neighborhood filter.

## Implementation details

The balanced core and hull are implemented differently: for the core we take the obvious definition
of the union over all balanced sets that are contained in `s`, whereas for the hull, we take the
union over `r • s`, for `r` the scalars with `∥r∥ ≤ 1`. We show that `balanced_hull` has the
defining properties of a hull in `balanced.hull_minimal` and `subset_balanced_hull`.
For the core we need slightly stronger assumptions to obtain a characterization as an intersection,
this is `balanced_core_eq_Inter`.

## References

* [Bourbaki, *Topological Vector Spaces*][bourbaki1987]

## Tags

balanced
-/


open Set

open Pointwise TopologicalSpace Filter

variable {𝕜 E ι : Type _}

section BalancedHull

section SemiNormedRing

variable [SemiNormedRing 𝕜]

section HasSmul

variable (𝕜) [HasSmul 𝕜 E] {s t : Set E} {x : E}

/-- The largest balanced subset of `s`.-/
def BalancedCore (s : Set E) :=
  ⋃₀{ t : Set E | Balanced 𝕜 t ∧ t ⊆ s }

/-- Helper definition to prove `balanced_core_eq_Inter`-/
def BalancedCoreAux (s : Set E) :=
  ⋂ (r : 𝕜) (hr : 1 ≤ ∥r∥), r • s

/-- The smallest balanced superset of `s`.-/
def BalancedHull (s : Set E) :=
  ⋃ (r : 𝕜) (hr : ∥r∥ ≤ 1), r • s

variable {𝕜}

theorem balanced_core_subset (s : Set E) : BalancedCore 𝕜 s ⊆ s :=
  sUnion_subset fun t ht => ht.2

theorem balanced_core_empty : BalancedCore 𝕜 (∅ : Set E) = ∅ :=
  eq_empty_of_subset_empty (balanced_core_subset _)

theorem mem_balanced_core_iff : x ∈ BalancedCore 𝕜 s ↔ ∃ t, Balanced 𝕜 t ∧ t ⊆ s ∧ x ∈ t := by
  simp_rw [BalancedCore, mem_sUnion, mem_set_of_eq, exists_prop, and_assoc]

theorem smul_balanced_core_subset (s : Set E) {a : 𝕜} (ha : ∥a∥ ≤ 1) : a • BalancedCore 𝕜 s ⊆ BalancedCore 𝕜 s := by
  rintro x ⟨y, hy, rfl⟩
  rw [mem_balanced_core_iff] at hy
  rcases hy with ⟨t, ht1, ht2, hy⟩
  exact ⟨t, ⟨ht1, ht2⟩, ht1 a ha (smul_mem_smul_set hy)⟩

theorem balanced_core_balanced (s : Set E) : Balanced 𝕜 (BalancedCore 𝕜 s) := fun _ => smul_balanced_core_subset s

/-- The balanced core of `t` is maximal in the sense that it contains any balanced subset
`s` of `t`.-/
theorem Balanced.subset_core_of_subset (hs : Balanced 𝕜 s) (h : s ⊆ t) : s ⊆ BalancedCore 𝕜 t :=
  subset_sUnion_of_mem ⟨hs, h⟩

theorem mem_balanced_core_aux_iff : x ∈ BalancedCoreAux 𝕜 s ↔ ∀ r : 𝕜, 1 ≤ ∥r∥ → x ∈ r • s :=
  mem_Inter₂

theorem mem_balanced_hull_iff : x ∈ BalancedHull 𝕜 s ↔ ∃ (r : 𝕜)(hr : ∥r∥ ≤ 1), x ∈ r • s :=
  mem_Union₂

/-- The balanced hull of `s` is minimal in the sense that it is contained in any balanced superset
`t` of `s`. -/
theorem Balanced.hull_subset_of_subset (ht : Balanced 𝕜 t) (h : s ⊆ t) : BalancedHull 𝕜 s ⊆ t := fun x hx => by
  obtain ⟨r, hr, y, hy, rfl⟩ := mem_balanced_hull_iff.1 hx
  exact ht.smul_mem hr (h hy)

end HasSmul

section Module

variable [AddCommGroupₓ E] [Module 𝕜 E] {s : Set E}

theorem balanced_core_zero_mem (hs : (0 : E) ∈ s) : (0 : E) ∈ BalancedCore 𝕜 s :=
  mem_balanced_core_iff.2 ⟨0, balanced_zero, zero_subset.2 hs, zero_mem_zero⟩

theorem balanced_core_nonempty_iff : (BalancedCore 𝕜 s).Nonempty ↔ (0 : E) ∈ s :=
  ⟨fun h =>
    zero_subset.1 <|
      (zero_smul_set h).Superset.trans <|
        (balanced_core_balanced s (0 : 𝕜) <| norm_zero.trans_le zero_le_one).trans <| balanced_core_subset _,
    fun h => ⟨0, balanced_core_zero_mem h⟩⟩

variable (𝕜)

theorem subset_balanced_hull [NormOneClass 𝕜] {s : Set E} : s ⊆ BalancedHull 𝕜 s := fun _ hx =>
  mem_balanced_hull_iff.2 ⟨1, norm_one.le, _, hx, one_smul _ _⟩

variable {𝕜}

theorem BalancedHull.balanced (s : Set E) : Balanced 𝕜 (BalancedHull 𝕜 s) := by
  intro a ha
  simp_rw [BalancedHull, smul_set_Union₂, subset_def, mem_Union₂]
  rintro x ⟨r, hr, hx⟩
  rw [← smul_assoc] at hx
  exact ⟨a • r, (SemiNormedRing.norm_mul _ _).trans (mul_le_one ha (norm_nonneg r) hr), hx⟩

end Module

end SemiNormedRing

section NormedField

variable [NormedField 𝕜] [AddCommGroupₓ E] [Module 𝕜 E] {s t : Set E}

@[simp]
theorem balanced_core_aux_empty : BalancedCoreAux 𝕜 (∅ : Set E) = ∅ := by
  simp_rw [BalancedCoreAux, Inter₂_eq_empty_iff, smul_set_empty]
  exact fun _ => ⟨1, norm_one.ge, not_mem_empty _⟩

theorem balanced_core_aux_subset (s : Set E) : BalancedCoreAux 𝕜 s ⊆ s := fun x hx => by
  simpa only [← one_smul] using mem_balanced_core_aux_iff.1 hx 1 norm_one.ge

theorem balanced_core_aux_balanced (h0 : (0 : E) ∈ BalancedCoreAux 𝕜 s) : Balanced 𝕜 (BalancedCoreAux 𝕜 s) := by
  rintro a ha x ⟨y, hy, rfl⟩
  obtain rfl | h := eq_or_ne a 0
  · rwa [zero_smul]
    
  rw [mem_balanced_core_aux_iff] at hy⊢
  intro r hr
  have h'' : 1 ≤ ∥a⁻¹ • r∥ := by
    rw [norm_smul, norm_inv]
    exact one_le_mul_of_one_le_of_one_le (one_le_inv (norm_pos_iff.mpr h) ha) hr
  have h' := hy (a⁻¹ • r) h''
  rwa [smul_assoc, mem_inv_smul_set_iff₀ h] at h'

theorem balanced_core_aux_maximal (h : t ⊆ s) (ht : Balanced 𝕜 t) : t ⊆ BalancedCoreAux 𝕜 s := by
  refine' fun x hx => mem_balanced_core_aux_iff.2 fun r hr => _
  rw [mem_smul_set_iff_inv_smul_mem₀ (norm_pos_iff.mp <| zero_lt_one.trans_le hr)]
  refine' h (ht.smul_mem _ hx)
  rw [norm_inv]
  exact inv_le_one hr

theorem balanced_core_subset_balanced_core_aux : BalancedCore 𝕜 s ⊆ BalancedCoreAux 𝕜 s :=
  balanced_core_aux_maximal (balanced_core_subset s) (balanced_core_balanced s)

theorem balanced_core_eq_Inter (hs : (0 : E) ∈ s) : BalancedCore 𝕜 s = ⋂ (r : 𝕜) (hr : 1 ≤ ∥r∥), r • s := by
  refine' balanced_core_subset_balanced_core_aux.antisymm _
  refine' (balanced_core_aux_balanced _).subset_core_of_subset (balanced_core_aux_subset s)
  exact balanced_core_subset_balanced_core_aux (balanced_core_zero_mem hs)

theorem subset_balanced_core (ht : (0 : E) ∈ t) (hst : ∀ (a : 𝕜) (ha : ∥a∥ ≤ 1), a • s ⊆ t) : s ⊆ BalancedCore 𝕜 t := by
  rw [balanced_core_eq_Inter ht]
  refine' subset_Inter₂ fun a ha => _
  rw [← smul_inv_smul₀ (norm_pos_iff.mp <| zero_lt_one.trans_le ha) s]
  refine' smul_set_mono (hst _ _)
  rw [norm_inv]
  exact inv_le_one ha

end NormedField

end BalancedHull

/-! ### Topological properties -/


section Topology

variable [NondiscreteNormedField 𝕜] [AddCommGroupₓ E] [Module 𝕜 E] [TopologicalSpace E] [HasContinuousSmul 𝕜 E]
  {U : Set E}

protected theorem IsClosed.balanced_core (hU : IsClosed U) : IsClosed (BalancedCore 𝕜 U) := by
  by_cases' h : (0 : E) ∈ U
  · rw [balanced_core_eq_Inter h]
    refine' is_closed_Inter fun a => _
    refine' is_closed_Inter fun ha => _
    have ha' := lt_of_lt_of_leₓ zero_lt_one ha
    rw [norm_pos_iff] at ha'
    refine' is_closed_map_smul_of_ne_zero ha' U hU
    
  convert is_closed_empty
  contrapose! h
  exact balanced_core_nonempty_iff.mp (set.ne_empty_iff_nonempty.mp h)

theorem balanced_core_mem_nhds_zero (hU : U ∈ 𝓝 (0 : E)) : BalancedCore 𝕜 U ∈ 𝓝 (0 : E) := by
  -- Getting neighborhoods of the origin for `0 : 𝕜` and `0 : E`
  obtain ⟨r, V, hr, hV, hrVU⟩ :
    ∃ (r : ℝ)(V : Set E), 0 < r ∧ V ∈ 𝓝 (0 : E) ∧ ∀ (c : 𝕜) (y : E), ∥c∥ < r → y ∈ V → c • y ∈ U := by
    have h : Filter.Tendsto (fun x : 𝕜 × E => x.fst • x.snd) (𝓝 (0, 0)) (𝓝 0) :=
      continuous_smul.tendsto' (0, 0) _ (smul_zero _)
    simpa only [Prod.exists', Prod.forall', and_imp, And.assoc, ← exists_prop] using
      h.basis_left (normed_group.nhds_zero_basis_norm_lt.prod_nhds (𝓝 _).basis_sets) U hU
  rcases NormedField.exists_norm_lt 𝕜 hr with ⟨y, hy₀, hyr⟩
  rw [norm_pos_iff] at hy₀
  have : y • V ∈ 𝓝 (0 : E) := (set_smul_mem_nhds_zero_iff hy₀).mpr hV
  -- It remains to show that `y • V ⊆ balanced_core 𝕜 U`
  refine' Filter.mem_of_superset this ((subset_balanced_core (mem_of_mem_nhds hU)) fun a ha => _)
  rw [smul_smul]
  rintro _ ⟨z, hz, rfl⟩
  refine' hrVU _ _ _ hz
  rw [norm_mul, ← one_mulₓ r]
  exact mul_lt_mul' ha hyr (norm_nonneg y) one_pos

variable (𝕜 E)

theorem nhds_basis_closed_balanced [T3Space E] :
    (𝓝 (0 : E)).HasBasis (fun s : Set E => s ∈ 𝓝 (0 : E) ∧ IsClosed s ∧ Balanced 𝕜 s) id := by
  refine' (closed_nhds_basis 0).to_has_basis (fun s hs => _) fun s hs => ⟨s, ⟨hs.1, hs.2.1⟩, rfl.subset⟩
  refine' ⟨BalancedCore 𝕜 s, ⟨balanced_core_mem_nhds_zero hs.1, _⟩, balanced_core_subset s⟩
  exact ⟨hs.2.BalancedCore, balanced_core_balanced s⟩

end Topology

