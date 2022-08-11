/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathbin.Topology.Separation
import Mathbin.Topology.ContinuousFunction.Basic

/-!
# Sober spaces

A quasi-sober space is a topological space where every
irreducible closed subset has a generic point.
A sober space is a quasi-sober space where every irreducible closed subset
has a *unique* generic point. This is if and only if the space is T0, and thus sober spaces can be
stated via `[quasi_sober α] [t0_space α]`.

## Main definition

* `is_generic_point` : `x` is the generic point of `S` if `S` is the closure of `x`.
* `quasi_sober` : A space is quasi-sober if every irreducible closed subset has a generic point.

-/


open Set

variable {α β : Type _} [TopologicalSpace α] [TopologicalSpace β]

section genericPoint

/-- `x` is a generic point of `S` if `S` is the closure of `x`. -/
def IsGenericPoint (x : α) (S : Set α) : Prop :=
  Closure ({x} : Set α) = S

theorem is_generic_point_def {x : α} {S : Set α} : IsGenericPoint x S ↔ Closure ({x} : Set α) = S :=
  Iff.rfl

theorem IsGenericPoint.def {x : α} {S : Set α} (h : IsGenericPoint x S) : Closure ({x} : Set α) = S :=
  h

theorem is_generic_point_closure {x : α} : IsGenericPoint x (Closure ({x} : Set α)) :=
  refl _

variable {x y : α} {S U Z : Set α}

theorem is_generic_point_iff_specializes : IsGenericPoint x S ↔ ∀ y, x ⤳ y ↔ y ∈ S := by
  simp only [← specializes_iff_mem_closure, ← IsGenericPoint, ← Set.ext_iff]

namespace IsGenericPoint

theorem specializes_iff_mem (h : IsGenericPoint x S) : x ⤳ y ↔ y ∈ S :=
  is_generic_point_iff_specializes.1 h y

theorem specializes (h : IsGenericPoint x S) (h' : y ∈ S) : x ⤳ y :=
  h.specializes_iff_mem.2 h'

theorem mem (h : IsGenericPoint x S) : x ∈ S :=
  h.specializes_iff_mem.1 specializes_rfl

protected theorem is_closed (h : IsGenericPoint x S) : IsClosed S :=
  h.def ▸ is_closed_closure

protected theorem is_irreducible (h : IsGenericPoint x S) : IsIrreducible S :=
  h.def ▸ is_irreducible_singleton.closure

/-- In a T₀ space, each set has at most one generic point. -/
protected theorem eq [T0Space α] (h : IsGenericPoint x S) (h' : IsGenericPoint y S) : x = y :=
  ((h.Specializes h'.Mem).antisymm (h'.Specializes h.Mem)).Eq

theorem mem_open_set_iff (h : IsGenericPoint x S) (hU : IsOpen U) : x ∈ U ↔ (S ∩ U).Nonempty :=
  ⟨fun h' => ⟨x, h.Mem, h'⟩, fun ⟨y, hyS, hyU⟩ => (h.Specializes hyS).mem_open hU hyU⟩

theorem disjoint_iff (h : IsGenericPoint x S) (hU : IsOpen U) : Disjoint S U ↔ x ∉ U := by
  rw [h.mem_open_set_iff hU, ← not_disjoint_iff_nonempty_inter, not_not]

theorem mem_closed_set_iff (h : IsGenericPoint x S) (hZ : IsClosed Z) : x ∈ Z ↔ S ⊆ Z := by
  rw [← h.def, hZ.closure_subset_iff, singleton_subset_iff]

protected theorem image (h : IsGenericPoint x S) {f : α → β} (hf : Continuous f) :
    IsGenericPoint (f x) (Closure (f '' S)) := by
  rw [is_generic_point_def, ← h.def, ← image_singleton]
  exact
    subset.antisymm (closure_mono (image_subset _ subset_closure))
      (closure_minimal (image_closure_subset_closure_image hf) is_closed_closure)

end IsGenericPoint

theorem is_generic_point_iff_forall_closed (hS : IsClosed S) (hxS : x ∈ S) :
    IsGenericPoint x S ↔ ∀ Z : Set α, IsClosed Z → x ∈ Z → S ⊆ Z := by
  have : Closure {x} ⊆ S := closure_minimal (singleton_subset_iff.2 hxS) hS
  simp_rw [IsGenericPoint, subset_antisymm_iff, this, true_andₓ, Closure, subset_sInter_iff, mem_set_of_eq, and_imp,
    singleton_subset_iff]

end genericPoint

section Sober

/-- A space is sober if every irreducible closed subset has a generic point. -/
@[mk_iff]
class QuasiSober (α : Type _) [TopologicalSpace α] : Prop where
  sober : ∀ {S : Set α} (hS₁ : IsIrreducible S) (hS₂ : IsClosed S), ∃ x, IsGenericPoint x S

/-- A generic point of the closure of an irreducible space. -/
noncomputable def IsIrreducible.genericPoint [QuasiSober α] {S : Set α} (hS : IsIrreducible S) : α :=
  (QuasiSober.sober hS.closure is_closed_closure).some

theorem IsIrreducible.generic_point_spec [QuasiSober α] {S : Set α} (hS : IsIrreducible S) :
    IsGenericPoint hS.genericPoint (Closure S) :=
  (QuasiSober.sober hS.closure is_closed_closure).some_spec

@[simp]
theorem IsIrreducible.generic_point_closure_eq [QuasiSober α] {S : Set α} (hS : IsIrreducible S) :
    Closure ({hS.genericPoint} : Set α) = Closure S :=
  hS.generic_point_spec

variable (α)

/-- A generic point of a sober irreducible space. -/
noncomputable def genericPoint [QuasiSober α] [IrreducibleSpace α] : α :=
  (IrreducibleSpace.is_irreducible_univ α).genericPoint

theorem generic_point_spec [QuasiSober α] [IrreducibleSpace α] : IsGenericPoint (genericPoint α) ⊤ := by
  simpa using (IrreducibleSpace.is_irreducible_univ α).generic_point_spec

@[simp]
theorem generic_point_closure [QuasiSober α] [IrreducibleSpace α] : Closure ({genericPoint α} : Set α) = ⊤ :=
  generic_point_spec α

variable {α}

theorem generic_point_specializes [QuasiSober α] [IrreducibleSpace α] (x : α) : genericPoint α ⤳ x :=
  (IsIrreducible.generic_point_spec _).Specializes
    (by
      simp )

attribute [local instance] specializationOrder

/-- The closed irreducible subsets of a sober space bijects with the points of the space. -/
noncomputable def irreducibleSetEquivPoints [QuasiSober α] [T0Space α] :
    { s : Set α | IsIrreducible s ∧ IsClosed s } ≃o α where
  toFun := fun s => s.Prop.1.genericPoint
  invFun := fun x => ⟨Closure ({x} : Set α), is_irreducible_singleton.closure, is_closed_closure⟩
  left_inv := fun s => Subtype.eq <| Eq.trans s.Prop.1.generic_point_spec <| closure_eq_iff_is_closed.mpr s.2.2
  right_inv := fun x =>
    is_irreducible_singleton.closure.generic_point_spec.Eq
      (by
        convert is_generic_point_closure using 1
        rw [closure_closure])
  map_rel_iff' := fun s t => by
    change _ ⤳ _ ↔ _
    rw [specializes_iff_closure_subset]
    simp [← s.prop.2.closure_eq, ← t.prop.2.closure_eq, Subtype.coe_le_coe]

theorem ClosedEmbedding.quasi_sober {f : α → β} (hf : ClosedEmbedding f) [QuasiSober β] : QuasiSober α := by
  constructor
  intro S hS hS'
  have hS'' := hS.image f hf.continuous.continuous_on
  obtain ⟨x, hx⟩ := QuasiSober.sober hS'' (hf.is_closed_map _ hS')
  obtain ⟨y, hy, rfl⟩ := hx.mem
  use y
  change _ = _ at hx
  apply set.image_injective.mpr hf.inj
  rw [← hx, ← hf.closure_image_eq, Set.image_singleton]

theorem OpenEmbedding.quasi_sober {f : α → β} (hf : OpenEmbedding f) [QuasiSober β] : QuasiSober α := by
  constructor
  intro S hS hS'
  have hS'' := hS.image f hf.continuous.continuous_on
  obtain ⟨x, hx⟩ := QuasiSober.sober hS''.closure is_closed_closure
  obtain ⟨T, hT, rfl⟩ := hf.to_inducing.is_closed_iff.mp hS'
  rw [Set.image_preimage_eq_inter_range] at hx hS''
  have hxT : x ∈ T := by
    rw [← hT.closure_eq]
    exact closure_mono (Set.inter_subset_left _ _) hx.mem
  have hxU : x ∈ Set.Range f := by
    rw [hx.mem_open_set_iff hf.open_range]
    refine' Set.Nonempty.mono _ hS''.1
    simpa using subset_closure
  rcases hxU with ⟨y, rfl⟩
  use y
  change _ = _
  rw [hf.to_embedding.closure_eq_preimage_closure_image, Set.image_singleton, show _ = _ from hx]
  apply set.image_injective.mpr hf.inj
  ext z
  simp only [← Set.image_preimage_eq_inter_range, ← Set.mem_inter_eq, ← And.congr_left_iff]
  exact fun hy => ⟨fun h => hT.closure_eq ▸ closure_mono (Set.inter_subset_left _ _) h, fun h => subset_closure ⟨h, hy⟩⟩

/-- A space is quasi sober if it can be covered by open quasi sober subsets. -/
theorem quasi_sober_of_open_cover (S : Set (Set α)) (hS : ∀ s : S, IsOpen (s : Set α)) [hS' : ∀ s : S, QuasiSober s]
    (hS'' : ⋃₀S = ⊤) : QuasiSober α := by
  rw [quasi_sober_iff]
  intro t h h'
  obtain ⟨x, hx⟩ := h.1
  obtain ⟨U, hU, hU'⟩ : x ∈ ⋃₀S := by
    rw [hS'']
    trivial
  have : QuasiSober U := hS' ⟨U, hU⟩
  have H : IsPreirreducible (coe ⁻¹' t : Set U) := h.2.Preimage (hS ⟨U, hU⟩).open_embedding_subtype_coe
  replace H : IsIrreducible (coe ⁻¹' t : Set U) :=
    ⟨⟨⟨x, hU'⟩, by
        simpa using hx⟩,
      H⟩
  use H.generic_point
  have := continuous_subtype_coe.closure_preimage_subset _ H.generic_point_spec.mem
  rw [h'.closure_eq] at this
  apply le_antisymmₓ
  · apply h'.closure_subset_iff.mpr
    simpa using this
    
  rw [← Set.image_singleton, ← closure_closure]
  have := closure_mono (image_closure_subset_closure_image (@continuous_subtype_coe α _ U))
  refine' Set.Subset.trans _ this
  rw [H.generic_point_spec.def]
  refine' (subset_closure_inter_of_is_preirreducible_of_is_open h.2 (hS ⟨U, hU⟩) ⟨x, hx, hU'⟩).trans (closure_mono _)
  rw [← Subtype.image_preimage_coe]
  exact Set.image_subset _ subset_closure

instance (priority := 100) T2Space.quasi_sober [T2Space α] : QuasiSober α := by
  constructor
  rintro S h -
  obtain ⟨x, rfl⟩ := (is_irreducible_iff_singleton S).mp h
  exact ⟨x, closure_singleton⟩

end Sober

