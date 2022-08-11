/-
Copyright (c) 2020 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
import Mathbin.Topology.UniformSpace.Separation
import Mathbin.Topology.UniformSpace.UniformConvergence

/-!
# Compact separated uniform spaces

## Main statements

* `compact_space_uniformity`: On a separated compact uniform space, the topology determines the
  uniform structure, entourages are exactly the neighborhoods of the diagonal.
* `uniform_space_of_compact_t2`: every compact T2 topological structure is induced by a uniform
  structure. This uniform structure is described in the previous item.
* Heine-Cantor theorem: continuous functions on compact separated uniform spaces with values in
  uniform spaces are automatically uniformly continuous. There are several variations, the main one
  is `compact_space.uniform_continuous_of_continuous`.

## Implementation notes

The construction `uniform_space_of_compact_t2` is not declared as an instance, as it would badly
loop.

## tags

uniform space, uniform continuity, compact space
-/


open Classical uniformity TopologicalSpace Filter

open Filter UniformSpace Set

variable {α β γ : Type _} [UniformSpace α] [UniformSpace β]

/-!
### Uniformity on compact separated spaces
-/


/-- On a separated compact uniform space, the topology determines the uniform structure, entourages
are exactly the neighborhoods of the diagonal. -/
theorem compact_space_uniformity [CompactSpace α] [SeparatedSpace α] : 𝓤 α = ⨆ x : α, 𝓝 (x, x) := by
  symm
  refine' le_antisymmₓ supr_nhds_le_uniformity _
  by_contra H
  obtain ⟨V, hV, h⟩ : ∃ V : Set (α × α), (∀ x : α, V ∈ 𝓝 (x, x)) ∧ 𝓤 α⊓𝓟 (Vᶜ) ≠ ⊥ := by
    simpa [← le_iff_forall_inf_principal_compl] using H
  let F := 𝓤 α⊓𝓟 (Vᶜ)
  have : ne_bot F := ⟨h⟩
  obtain ⟨⟨x, y⟩, hx⟩ : ∃ p : α × α, ClusterPt p F := cluster_point_of_compact F
  have : ClusterPt (x, y) (𝓤 α) := hx.of_inf_left
  obtain rfl : x = y := eq_of_uniformity_inf_nhds this
  have : ClusterPt (x, x) (𝓟 (Vᶜ)) := hx.of_inf_right
  have : (x, x) ∉ Interior V := by
    have : (x, x) ∈ Closure (Vᶜ) := by
      rwa [mem_closure_iff_cluster_pt]
    rwa [closure_compl] at this
  have : (x, x) ∈ Interior V := by
    rw [mem_interior_iff_mem_nhds]
    exact hV x
  contradiction

theorem unique_uniformity_of_compact_t2 [t : TopologicalSpace γ] [CompactSpace γ] [T2Space γ] {u u' : UniformSpace γ}
    (h : u.toTopologicalSpace = t) (h' : u'.toTopologicalSpace = t) : u = u' := by
  apply uniform_space_eq
  change uniformity _ = uniformity _
  have : @CompactSpace γ u.to_topological_space := by
    rw [h] <;> assumption
  have : @CompactSpace γ u'.to_topological_space := by
    rw [h'] <;> assumption
  have : @SeparatedSpace γ u := by
    rwa [separated_iff_t2, h]
  have : @SeparatedSpace γ u' := by
    rwa [separated_iff_t2, h']
  rw [compact_space_uniformity, compact_space_uniformity, h, h']

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (y «expr ≠ » x)
/-- The unique uniform structure inducing a given compact Hausdorff topological structure. -/
def uniformSpaceOfCompactT2 [TopologicalSpace γ] [CompactSpace γ] [T2Space γ] : UniformSpace γ where
  uniformity := ⨆ x, 𝓝 (x, x)
  refl := by
    simp_rw [Filter.principal_le_iff, mem_supr]
    rintro V V_in ⟨x, _⟩ ⟨⟩
    exact mem_of_mem_nhds (V_in x)
  symm := by
    refine' le_of_eqₓ _
    rw [map_supr]
    congr with x : 1
    erw [nhds_prod_eq, ← prod_comm]
  comp := by
    /-
        This is the difficult part of the proof. We need to prove that, for each neighborhood W
        of the diagonal Δ, W ○ W is still a neighborhood of the diagonal.
        -/
    set 𝓝Δ := ⨆ x : γ, 𝓝 (x, x)
    -- The filter of neighborhoods of Δ
    set F := 𝓝Δ.lift' fun s : Set (γ × γ) => s ○ s
    -- Compositions of neighborhoods of Δ
    -- If this weren't true, then there would be V ∈ 𝓝Δ such that F ⊓ 𝓟 Vᶜ ≠ ⊥
    rw [le_iff_forall_inf_principal_compl]
    intro V V_in
    by_contra H
    have : ne_bot (F⊓𝓟 (Vᶜ)) := ⟨H⟩
    -- Hence compactness would give us a cluster point (x, y) for F ⊓ 𝓟 Vᶜ
    obtain ⟨⟨x, y⟩, hxy⟩ : ∃ p : γ × γ, ClusterPt p (F⊓𝓟 (Vᶜ)) := cluster_point_of_compact _
    -- In particular (x, y) is a cluster point of 𝓟 Vᶜ, hence is not in the interior of V,
    -- and a fortiori not in Δ, so x ≠ y
    have clV : ClusterPt (x, y) (𝓟 <| Vᶜ) := hxy.of_inf_right
    have : (x, y) ∉ Interior V := by
      have : (x, y) ∈ Closure (Vᶜ) := by
        rwa [mem_closure_iff_cluster_pt]
      rwa [closure_compl] at this
    have diag_subset : diagonal γ ⊆ Interior V := by
      rw [subset_interior_iff_nhds]
      rintro ⟨x, x⟩ ⟨⟩
      exact (mem_supr.mp V_in : _) x
    have x_ne_y : x ≠ y := by
      intro h
      apply this
      apply diag_subset
      simp [← h]
    -- Since γ is compact and Hausdorff, it is normal, hence T₃.
    have : NormalSpace γ := normal_of_compact_t2
    -- So there are closed neighboords V₁ and V₂ of x and y contained in disjoint open neighborhoods
    -- U₁ and U₂.
    obtain ⟨U₁, U₁_in, V₁, V₁_in, U₂, U₂_in₂, V₂, V₂_in, V₁_cl, V₂_cl, U₁_op, U₂_op, VU₁, VU₂, hU₁₂⟩ :=
      disjoint_nested_nhds x_ne_y
    -- We set U₃ := (V₁ ∪ V₂)ᶜ so that W := U₁ ×ˢ U₁ ∪ U₂ ×ˢ U₂ ∪ U₃ ×ˢ U₃ is an open
    -- neighborhood of Δ.
    let U₃ := (V₁ ∪ V₂)ᶜ
    have U₃_op : IsOpen U₃ := is_open_compl_iff.mpr (IsClosed.union V₁_cl V₂_cl)
    let W := U₁ ×ˢ U₁ ∪ U₂ ×ˢ U₂ ∪ U₃ ×ˢ U₃
    have W_in : W ∈ 𝓝Δ := by
      rw [mem_supr]
      intro x
      apply IsOpen.mem_nhds (IsOpen.union (IsOpen.union _ _) _)
      · by_cases' hx : x ∈ V₁ ∪ V₂
        · left
          cases' hx with hx hx <;> [left, right] <;> constructor <;> tauto
          
        · right
          rw [mem_prod]
          tauto
          
        
      all_goals
        simp only [← IsOpen.prod, *]
    -- So W ○ W ∈ F by definition of F
    have : W ○ W ∈ F := by
      simpa only using mem_lift' W_in
    -- And V₁ ×ˢ V₂ ∈ 𝓝 (x, y)
    have hV₁₂ : V₁ ×ˢ V₂ ∈ 𝓝 (x, y) := prod_mem_nhds V₁_in V₂_in
    -- But (x, y) is also a cluster point of F so (V₁ ×ˢ V₂) ∩ (W ○ W) ≠ ∅
    -- However the construction of W implies (V₁ ×ˢ V₂) ∩ (W ○ W) = ∅.
    -- Indeed assume for contradiction there is some (u, v) in the intersection.
    obtain ⟨⟨u, v⟩, ⟨u_in, v_in⟩, w, huw, hwv⟩ := cluster_pt_iff.mp hxy.of_inf_left hV₁₂ this
    -- So u ∈ V₁, v ∈ V₂, and there exists some w such that (u, w) ∈ W and (w ,v) ∈ W.
    -- Because u is in V₁ which is disjoint from U₂ and U₃, (u, w) ∈ W forces (u, w) ∈ U₁ ×ˢ U₁.
    have uw_in : (u, w) ∈ U₁ ×ˢ U₁ :=
      (huw.resolve_right fun h => h.1 <| Or.inl u_in).resolve_right fun h => hU₁₂ ⟨VU₁ u_in, h.1⟩
    -- Similarly, because v ∈ V₂, (w ,v) ∈ W forces (w, v) ∈ U₂ ×ˢ U₂.
    have wv_in : (w, v) ∈ U₂ ×ˢ U₂ :=
      (hwv.resolve_right fun h => h.2 <| Or.inr v_in).resolve_left fun h => hU₁₂ ⟨h.2, VU₂ v_in⟩
    -- Hence w ∈ U₁ ∩ U₂ which is empty.
    -- So we have a contradiction
    exact hU₁₂ ⟨uw_in.2, wv_in.1⟩
  is_open_uniformity := by
    -- Here we need to prove the topology induced by the constructed uniformity is the
    -- topology we started with.
    suffices ∀ x : γ, Filter.comap (Prod.mk x) (⨆ y, 𝓝 (y, y)) = 𝓝 x by
      intro s
      change IsOpen s ↔ _
      simp_rw [is_open_iff_mem_nhds, nhds_eq_comap_uniformity_aux, this]
    intro x
    simp_rw [comap_supr, nhds_prod_eq, comap_prod,
      show Prod.fst ∘ Prod.mk x = fun y : γ => x by
        ext <;> simp ,
      show Prod.snd ∘ Prod.mk x = (id : γ → γ) by
        ext <;> rfl,
      comap_id]
    rw [supr_split_single _ x, comap_const_of_mem fun V => mem_of_mem_nhds]
    suffices ∀ (y) (_ : y ≠ x), comap (fun y : γ => x) (𝓝 y)⊓𝓝 y ≤ 𝓝 x by
      simpa
    intro y hxy
    simp [←
      comap_const_of_not_mem (compl_singleton_mem_nhds hxy)
        (by
          simp )]

/-!
### Heine-Cantor theorem
-/


/-- Heine-Cantor: a continuous function on a compact separated uniform space is uniformly
continuous. -/
theorem CompactSpace.uniform_continuous_of_continuous [CompactSpace α] [SeparatedSpace α] {f : α → β}
    (h : Continuous f) : UniformContinuous f :=
  calc
    map (Prod.map f f) (𝓤 α) = map (Prod.map f f) (⨆ x, 𝓝 (x, x)) := by
      rw [compact_space_uniformity]
    _ = ⨆ x, map (Prod.map f f) (𝓝 (x, x)) := by
      rw [map_supr]
    _ ≤ ⨆ x, 𝓝 (f x, f x) := supr_mono fun x => (h.prod_map h).ContinuousAt
    _ ≤ ⨆ y, 𝓝 (y, y) := supr_comp_le (fun y => 𝓝 (y, y)) f
    _ ≤ 𝓤 β := supr_nhds_le_uniformity
    

/-- Heine-Cantor: a continuous function on a compact separated set of a uniform space is
uniformly continuous. -/
theorem IsCompact.uniform_continuous_on_of_continuous' {s : Set α} {f : α → β} (hs : IsCompact s) (hs' : IsSeparated s)
    (hf : ContinuousOn f s) : UniformContinuousOn f s := by
  rw [uniform_continuous_on_iff_restrict]
  rw [is_separated_iff_induced] at hs'
  rw [is_compact_iff_compact_space] at hs
  rw [continuous_on_iff_continuous_restrict] at hf
  skip
  exact CompactSpace.uniform_continuous_of_continuous hf

/-- Heine-Cantor: a continuous function on a compact set of a separated uniform space
is uniformly continuous. -/
theorem IsCompact.uniform_continuous_on_of_continuous [SeparatedSpace α] {s : Set α} {f : α → β} (hs : IsCompact s)
    (hf : ContinuousOn f s) : UniformContinuousOn f s :=
  hs.uniform_continuous_on_of_continuous' (is_separated_of_separated_space s) hf

/-- A family of functions `α → β → γ` tends uniformly to its value at `x` if `α` is locally compact,
`β` is compact and separated and `f` is continuous on `U × (univ : set β)` for some separated
neighborhood `U` of `x`. -/
theorem ContinuousOn.tendsto_uniformly [LocallyCompactSpace α] [CompactSpace β] [SeparatedSpace β] [UniformSpace γ]
    {f : α → β → γ} {x : α} {U : Set α} (hxU : U ∈ 𝓝 x) (hU : IsSeparated U)
    (h : ContinuousOn (↿f) (U ×ˢ (Univ : Set β))) : TendstoUniformly f (f x) (𝓝 x) := by
  rcases LocallyCompactSpace.local_compact_nhds _ _ hxU with ⟨K, hxK, hKU, hK⟩
  have : UniformContinuousOn (↿f) (K ×ˢ (univ : Set β)) := by
    refine' IsCompact.uniform_continuous_on_of_continuous' (hK.prod compact_univ) _ (h.mono <| prod_mono hKU subset.rfl)
    exact (hU.mono hKU).Prod (is_separated_of_separated_space _)
  exact this.tendsto_uniformly hxK

/-- A continuous family of functions `α → β → γ` tends uniformly to its value at `x` if `α` is
locally compact and `β` is compact and separated. -/
theorem Continuous.tendsto_uniformly [SeparatedSpace α] [LocallyCompactSpace α] [CompactSpace β] [SeparatedSpace β]
    [UniformSpace γ] (f : α → β → γ) (h : Continuous ↿f) (x : α) : TendstoUniformly f (f x) (𝓝 x) :=
  h.ContinuousOn.TendstoUniformly univ_mem <| is_separated_of_separated_space _

