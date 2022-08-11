/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
import Mathbin.Analysis.LocallyConvex.Basic
import Mathbin.Topology.Bornology.Basic
import Mathbin.Topology.Algebra.UniformGroup
import Mathbin.Analysis.LocallyConvex.BalancedCoreHull

/-!
# Von Neumann Boundedness

This file defines natural or von Neumann bounded sets and proves elementary properties.

## Main declarations

* `bornology.is_vonN_bounded`: A set `s` is von Neumann-bounded if every neighborhood of zero
absorbs `s`.
* `bornology.vonN_bornology`: The bornology made of the von Neumann-bounded sets.

## Main results

* `bornology.is_vonN_bounded_of_topological_space_le`: A coarser topology admits more
von Neumann-bounded sets.

## References

* [Bourbaki, *Topological Vector Spaces*][bourbaki1987]

-/


variable {𝕜 E ι : Type _}

open Filter

open TopologicalSpace Pointwise

namespace Bornology

section SemiNormedRing

section Zero

variable (𝕜)

variable [SemiNormedRing 𝕜] [HasSmul 𝕜 E] [Zero E]

variable [TopologicalSpace E]

/-- A set `s` is von Neumann bounded if every neighborhood of 0 absorbs `s`. -/
def IsVonNBounded (s : Set E) : Prop :=
  ∀ ⦃V⦄, V ∈ 𝓝 (0 : E) → Absorbs 𝕜 V s

variable (E)

@[simp]
theorem is_vonN_bounded_empty : IsVonNBounded 𝕜 (∅ : Set E) := fun _ _ => absorbs_empty

variable {𝕜 E}

theorem is_vonN_bounded_iff (s : Set E) : IsVonNBounded 𝕜 s ↔ ∀, ∀ V ∈ 𝓝 (0 : E), ∀, Absorbs 𝕜 V s :=
  Iff.rfl

theorem _root_.filter.has_basis.is_vonN_bounded_basis_iff {q : ι → Prop} {s : ι → Set E} {A : Set E}
    (h : (𝓝 (0 : E)).HasBasis q s) : IsVonNBounded 𝕜 A ↔ ∀ (i) (hi : q i), Absorbs 𝕜 (s i) A := by
  refine' ⟨fun hA i hi => hA (h.mem_of_mem hi), fun hA V hV => _⟩
  rcases h.mem_iff.mp hV with ⟨i, hi, hV⟩
  exact (hA i hi).mono_left hV

/-- Subsets of bounded sets are bounded. -/
theorem IsVonNBounded.subset {s₁ s₂ : Set E} (h : s₁ ⊆ s₂) (hs₂ : IsVonNBounded 𝕜 s₂) : IsVonNBounded 𝕜 s₁ :=
  fun V hV => (hs₂ hV).mono_right h

/-- The union of two bounded sets is bounded. -/
theorem IsVonNBounded.union {s₁ s₂ : Set E} (hs₁ : IsVonNBounded 𝕜 s₁) (hs₂ : IsVonNBounded 𝕜 s₂) :
    IsVonNBounded 𝕜 (s₁ ∪ s₂) := fun V hV => (hs₁ hV).union (hs₂ hV)

end Zero

end SemiNormedRing

section MultipleTopologies

variable [SemiNormedRing 𝕜] [AddCommGroupₓ E] [Module 𝕜 E]

/-- If a topology `t'` is coarser than `t`, then any set `s` that is bounded with respect to
`t` is bounded with respect to `t'`. -/
theorem IsVonNBounded.of_topological_space_le {t t' : TopologicalSpace E} (h : t ≤ t') {s : Set E}
    (hs : @IsVonNBounded 𝕜 E _ _ _ t s) : @IsVonNBounded 𝕜 E _ _ _ t' s := fun V hV =>
  hs <| (le_iff_nhds t t').mp h 0 hV

end MultipleTopologies

section Image

variable {𝕜₁ 𝕜₂ F : Type _} [NormedDivisionRing 𝕜₁] [NormedDivisionRing 𝕜₂] [AddCommGroupₓ E] [Module 𝕜₁ E]
  [AddCommGroupₓ F] [Module 𝕜₂ F] [TopologicalSpace E] [TopologicalSpace F]

/-- A continuous linear image of a bounded set is bounded. -/
theorem IsVonNBounded.image {σ : 𝕜₁ →+* 𝕜₂} [RingHomSurjective σ] [RingHomIsometric σ] {s : Set E}
    (hs : IsVonNBounded 𝕜₁ s) (f : E →SL[σ] F) : IsVonNBounded 𝕜₂ (f '' s) := by
  let σ' := RingEquiv.ofBijective σ ⟨σ.injective, σ.is_surjective⟩
  have σ_iso : Isometry σ := AddMonoidHomClass.isometry_of_norm σ fun x => RingHomIsometric.is_iso
  have σ'_symm_iso : Isometry σ'.symm := σ_iso.right_inv σ'.right_inv
  have f_tendsto_zero := f.continuous.tendsto 0
  rw [map_zero] at f_tendsto_zero
  intro V hV
  rcases hs (f_tendsto_zero hV) with ⟨r, hrpos, hr⟩
  refine' ⟨r, hrpos, fun a ha => _⟩
  rw [← σ'.apply_symm_apply a]
  have hanz : a ≠ 0 := norm_pos_iff.mp (hrpos.trans_le ha)
  have : σ'.symm a ≠ 0 := (RingHom.map_ne_zero σ'.symm.to_ring_hom).mpr hanz
  change _ ⊆ σ _ • _
  rw [Set.image_subset_iff, preimage_smul_setₛₗ _ _ _ f this.is_unit]
  refine' hr (σ'.symm a) _
  rwa [σ'_symm_iso.norm_map_of_map_zero (map_zero _)]

end Image

section NormedField

variable [NormedField 𝕜] [AddCommGroupₓ E] [Module 𝕜 E]

variable [TopologicalSpace E] [HasContinuousSmul 𝕜 E]

/-- Singletons are bounded. -/
theorem is_vonN_bounded_singleton (x : E) : IsVonNBounded 𝕜 ({x} : Set E) := fun V hV =>
  (absorbent_nhds_zero hV).Absorbs

/-- The union of all bounded set is the whole space. -/
theorem is_vonN_bounded_covers : ⋃₀SetOf (IsVonNBounded 𝕜) = (Set.Univ : Set E) :=
  Set.eq_univ_iff_forall.mpr fun x => Set.mem_sUnion.mpr ⟨{x}, is_vonN_bounded_singleton _, Set.mem_singleton _⟩

variable (𝕜 E)

/-- The von Neumann bornology defined by the von Neumann bounded sets.

Note that this is not registered as an instance, in order to avoid diamonds with the
metric bornology.-/
-- See note [reducible non-instances]
@[reducible]
def vonNBornology : Bornology E :=
  Bornology.ofBounded (SetOf (IsVonNBounded 𝕜)) (is_vonN_bounded_empty 𝕜 E) (fun _ hs _ ht => hs.Subset ht)
    (fun _ hs _ => hs.union) is_vonN_bounded_singleton

variable {E}

@[simp]
theorem is_bounded_iff_is_vonN_bounded {s : Set E} : @IsBounded _ (vonNBornology 𝕜 E) s ↔ IsVonNBounded 𝕜 s :=
  is_bounded_of_bounded_iff _

end NormedField

end Bornology

section UniformAddGroup

variable [NondiscreteNormedField 𝕜] [AddCommGroupₓ E] [Module 𝕜 E]

variable [UniformSpace E] [UniformAddGroup E] [HasContinuousSmul 𝕜 E]

variable [T3Space E]

theorem TotallyBounded.is_vonN_bounded {s : Set E} (hs : TotallyBounded s) : Bornology.IsVonNBounded 𝕜 s := by
  rw [totally_bounded_iff_subset_finite_Union_nhds_zero] at hs
  intro U hU
  have h : Filter.Tendsto (fun x : E × E => x.fst + x.snd) (𝓝 (0, 0)) (𝓝 ((0 : E) + (0 : E))) := tendsto_add
  rw [add_zeroₓ] at h
  have h' := (nhds_basis_closed_balanced 𝕜 E).Prod (nhds_basis_closed_balanced 𝕜 E)
  simp_rw [← nhds_prod_eq, id.def] at h'
  rcases h.basis_left h' U hU with ⟨x, hx, h''⟩
  rcases hs x.snd hx.2.1 with ⟨t, ht, hs⟩
  refine' Absorbs.mono_right _ hs
  rw [ht.absorbs_Union]
  have hx_fstsnd : x.fst + x.snd ⊆ U := by
    intro z hz
    rcases set.mem_add.mp hz with ⟨z1, z2, hz1, hz2, hz⟩
    have hz' : (z1, z2) ∈ x.fst ×ˢ x.snd := ⟨hz1, hz2⟩
    simpa only [← hz] using h'' hz'
  refine' fun y hy => Absorbs.mono_left _ hx_fstsnd
  rw [← Set.singleton_vadd, vadd_eq_add]
  exact (absorbent_nhds_zero hx.1.1).Absorbs.add hx.2.2.2.absorbs_self

end UniformAddGroup

