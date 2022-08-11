/-
Copyright (c) 2019 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathbin.Topology.Constructions

/-!
# Neighborhoods and continuity relative to a subset

This file defines relative versions

* `nhds_within`           of `nhds`
* `continuous_on`         of `continuous`
* `continuous_within_at`  of `continuous_at`

and proves their basic properties, including the relationships between
these restricted notions and the corresponding notions for the subtype
equipped with the subspace topology.

## Notation

* `𝓝 x`: the filter of neighborhoods of a point `x`;
* `𝓟 s`: the principal filter of a set `s`;
* `𝓝[s] x`: the filter `nhds_within x s` of neighborhoods of a point `x` within a set `s`.

-/


open Set Filter Function

open TopologicalSpace Filter

variable {α : Type _} {β : Type _} {γ : Type _} {δ : Type _}

variable [TopologicalSpace α]

@[simp]
theorem nhds_bind_nhds_within {a : α} {s : Set α} : ((𝓝 a).bind fun x => 𝓝[s] x) = 𝓝[s] a :=
  bind_inf_principal.trans <| congr_arg2ₓ _ nhds_bind_nhds rfl

@[simp]
theorem eventually_nhds_nhds_within {a : α} {s : Set α} {p : α → Prop} :
    (∀ᶠ y in 𝓝 a, ∀ᶠ x in 𝓝[s] y, p x) ↔ ∀ᶠ x in 𝓝[s] a, p x :=
  Filter.ext_iff.1 nhds_bind_nhds_within { x | p x }

theorem eventually_nhds_within_iff {a : α} {s : Set α} {p : α → Prop} :
    (∀ᶠ x in 𝓝[s] a, p x) ↔ ∀ᶠ x in 𝓝 a, x ∈ s → p x :=
  eventually_inf_principal

@[simp]
theorem eventually_nhds_within_nhds_within {a : α} {s : Set α} {p : α → Prop} :
    (∀ᶠ y in 𝓝[s] a, ∀ᶠ x in 𝓝[s] y, p x) ↔ ∀ᶠ x in 𝓝[s] a, p x := by
  refine' ⟨fun h => _, fun h => (eventually_nhds_nhds_within.2 h).filter_mono inf_le_left⟩
  simp only [← eventually_nhds_within_iff] at h⊢
  exact h.mono fun x hx hxs => (hx hxs).self_of_nhds hxs

theorem nhds_within_eq (a : α) (s : Set α) : 𝓝[s] a = ⨅ t ∈ { t : Set α | a ∈ t ∧ IsOpen t }, 𝓟 (t ∩ s) :=
  ((nhds_basis_opens a).inf_principal s).eq_binfi

theorem nhds_within_univ (a : α) : 𝓝[Set.Univ] a = 𝓝 a := by
  rw [nhdsWithin, principal_univ, inf_top_eq]

theorem nhds_within_has_basis {p : β → Prop} {s : β → Set α} {a : α} (h : (𝓝 a).HasBasis p s) (t : Set α) :
    (𝓝[t] a).HasBasis p fun i => s i ∩ t :=
  h.inf_principal t

theorem nhds_within_basis_open (a : α) (t : Set α) : (𝓝[t] a).HasBasis (fun u => a ∈ u ∧ IsOpen u) fun u => u ∩ t :=
  nhds_within_has_basis (nhds_basis_opens a) t

theorem mem_nhds_within {t : Set α} {a : α} {s : Set α} : t ∈ 𝓝[s] a ↔ ∃ u, IsOpen u ∧ a ∈ u ∧ u ∩ s ⊆ t := by
  simpa only [← exists_prop, ← and_assoc, ← and_comm] using (nhds_within_basis_open a s).mem_iff

theorem mem_nhds_within_iff_exists_mem_nhds_inter {t : Set α} {a : α} {s : Set α} : t ∈ 𝓝[s] a ↔ ∃ u ∈ 𝓝 a, u ∩ s ⊆ t :=
  (nhds_within_has_basis (𝓝 a).basis_sets s).mem_iff

theorem diff_mem_nhds_within_compl {x : α} {s : Set α} (hs : s ∈ 𝓝 x) (t : Set α) : s \ t ∈ 𝓝[tᶜ] x :=
  diff_mem_inf_principal_compl hs t

theorem diff_mem_nhds_within_diff {x : α} {s t : Set α} (hs : s ∈ 𝓝[t] x) (t' : Set α) : s \ t' ∈ 𝓝[t \ t'] x := by
  rw [nhdsWithin, diff_eq, diff_eq, ← inf_principal, ← inf_assoc]
  exact inter_mem_inf hs (mem_principal_self _)

theorem nhds_of_nhds_within_of_nhds {s t : Set α} {a : α} (h1 : s ∈ 𝓝 a) (h2 : t ∈ 𝓝[s] a) : t ∈ 𝓝 a := by
  rcases mem_nhds_within_iff_exists_mem_nhds_inter.mp h2 with ⟨_, Hw, hw⟩
  exact (nhds a).sets_of_superset ((nhds a).inter_sets Hw h1) hw

theorem mem_nhds_within_iff_eventually {s t : Set α} {x : α} : t ∈ 𝓝[s] x ↔ ∀ᶠ y in 𝓝 x, y ∈ s → y ∈ t := by
  rw [mem_nhds_within_iff_exists_mem_nhds_inter]
  constructor
  · rintro ⟨u, hu, hut⟩
    exact eventually_of_mem hu fun x hxu hxs => hut ⟨hxu, hxs⟩
    
  · refine' fun h => ⟨_, h, fun y hy => hy.1 hy.2⟩
    

theorem mem_nhds_within_iff_eventually_eq {s t : Set α} {x : α} : t ∈ 𝓝[s] x ↔ s =ᶠ[𝓝 x] (s ∩ t : Set α) := by
  simp_rw [mem_nhds_within_iff_eventually, eventually_eq_set, mem_inter_iff, iff_self_and]

theorem nhds_within_eq_iff_eventually_eq {s t : Set α} {x : α} : 𝓝[s] x = 𝓝[t] x ↔ s =ᶠ[𝓝 x] t := by
  simp_rw [Filter.ext_iff, mem_nhds_within_iff_eventually, eventually_eq_set]
  constructor
  · intro h
    filter_upwards [(h t).mpr (eventually_of_forall fun x => id), (h s).mp (eventually_of_forall fun x => id)]
    exact fun x => Iff.intro
    
  · refine' fun h u => eventually_congr (h.mono fun x h => _)
    rw [h]
    

theorem nhds_within_le_iff {s t : Set α} {x : α} : 𝓝[s] x ≤ 𝓝[t] x ↔ t ∈ 𝓝[s] x := by
  simp_rw [Filter.le_def, mem_nhds_within_iff_eventually]
  constructor
  · exact fun h => (h t <| eventually_of_forall fun x => id).mono fun x => id
    
  · exact fun h u hu => (h.And hu).mono fun x hx h => hx.2 <| hx.1 h
    

theorem preimage_nhds_within_coinduced' {π : α → β} {s : Set β} {t : Set α} {a : α} (h : a ∈ t) (ht : IsOpen t)
    (hs : s ∈ @nhds β (TopologicalSpace.coinduced (fun x : t => π x) Subtype.topologicalSpace) (π a)) :
    π ⁻¹' s ∈ 𝓝[t] a := by
  let this := TopologicalSpace.coinduced (fun x : t => π x) Subtype.topologicalSpace
  rcases mem_nhds_iff.mp hs with ⟨V, hVs, V_op, mem_V⟩
  refine'
    mem_nhds_within_iff_exists_mem_nhds_inter.mpr
      ⟨π ⁻¹' V, mem_nhds_iff.mpr ⟨t ∩ π ⁻¹' V, inter_subset_right t (π ⁻¹' V), _, mem_sep h mem_V⟩,
        subset.trans (inter_subset_left _ _) (preimage_mono hVs)⟩
  obtain ⟨u, hu1, hu2⟩ := is_open_induced_iff.mp (is_open_coinduced.1 V_op)
  rw [preimage_comp] at hu2
  rw [Set.inter_comm, ← subtype.preimage_coe_eq_preimage_coe_iff.mp hu2]
  exact hu1.inter ht

theorem mem_nhds_within_of_mem_nhds {s t : Set α} {a : α} (h : s ∈ 𝓝 a) : s ∈ 𝓝[t] a :=
  mem_inf_of_left h

theorem self_mem_nhds_within {a : α} {s : Set α} : s ∈ 𝓝[s] a :=
  mem_inf_of_right (mem_principal_self s)

theorem eventually_mem_nhds_within {a : α} {s : Set α} : ∀ᶠ x in 𝓝[s] a, x ∈ s :=
  self_mem_nhds_within

theorem inter_mem_nhds_within (s : Set α) {t : Set α} {a : α} (h : t ∈ 𝓝 a) : s ∩ t ∈ 𝓝[s] a :=
  inter_mem self_mem_nhds_within (mem_inf_of_left h)

theorem nhds_within_mono (a : α) {s t : Set α} (h : s ⊆ t) : 𝓝[s] a ≤ 𝓝[t] a :=
  inf_le_inf_left _ (principal_mono.mpr h)

theorem pure_le_nhds_within {a : α} {s : Set α} (ha : a ∈ s) : pure a ≤ 𝓝[s] a :=
  le_inf (pure_le_nhds a) (le_principal_iff.2 ha)

theorem mem_of_mem_nhds_within {a : α} {s t : Set α} (ha : a ∈ s) (ht : t ∈ 𝓝[s] a) : a ∈ t :=
  pure_le_nhds_within ha ht

theorem Filter.Eventually.self_of_nhds_within {p : α → Prop} {s : Set α} {x : α} (h : ∀ᶠ y in 𝓝[s] x, p y)
    (hx : x ∈ s) : p x :=
  mem_of_mem_nhds_within hx h

theorem tendsto_const_nhds_within {l : Filter β} {s : Set α} {a : α} (ha : a ∈ s) :
    Tendsto (fun x : β => a) l (𝓝[s] a) :=
  tendsto_const_pure.mono_right <| pure_le_nhds_within ha

theorem nhds_within_restrict'' {a : α} (s : Set α) {t : Set α} (h : t ∈ 𝓝[s] a) : 𝓝[s] a = 𝓝[s ∩ t] a :=
  le_antisymmₓ (le_inf inf_le_left (le_principal_iff.mpr (inter_mem self_mem_nhds_within h)))
    (inf_le_inf_left _ (principal_mono.mpr (Set.inter_subset_left _ _)))

theorem nhds_within_restrict' {a : α} (s : Set α) {t : Set α} (h : t ∈ 𝓝 a) : 𝓝[s] a = 𝓝[s ∩ t] a :=
  nhds_within_restrict'' s <| mem_inf_of_left h

theorem nhds_within_restrict {a : α} (s : Set α) {t : Set α} (h₀ : a ∈ t) (h₁ : IsOpen t) : 𝓝[s] a = 𝓝[s ∩ t] a :=
  nhds_within_restrict' s (IsOpen.mem_nhds h₁ h₀)

theorem nhds_within_le_of_mem {a : α} {s t : Set α} (h : s ∈ 𝓝[t] a) : 𝓝[t] a ≤ 𝓝[s] a :=
  nhds_within_le_iff.mpr h

theorem nhds_within_le_nhds {a : α} {s : Set α} : 𝓝[s] a ≤ 𝓝 a := by
  rw [← nhds_within_univ]
  apply nhds_within_le_of_mem
  exact univ_mem

theorem nhds_within_eq_nhds_within' {a : α} {s t u : Set α} (hs : s ∈ 𝓝 a) (h₂ : t ∩ s = u ∩ s) : 𝓝[t] a = 𝓝[u] a := by
  rw [nhds_within_restrict' t hs, nhds_within_restrict' u hs, h₂]

theorem nhds_within_eq_nhds_within {a : α} {s t u : Set α} (h₀ : a ∈ s) (h₁ : IsOpen s) (h₂ : t ∩ s = u ∩ s) :
    𝓝[t] a = 𝓝[u] a := by
  rw [nhds_within_restrict t h₀ h₁, nhds_within_restrict u h₀ h₁, h₂]

theorem IsOpen.nhds_within_eq {a : α} {s : Set α} (h : IsOpen s) (ha : a ∈ s) : 𝓝[s] a = 𝓝 a :=
  inf_eq_left.2 <| le_principal_iff.2 <| IsOpen.mem_nhds h ha

theorem preimage_nhds_within_coinduced {π : α → β} {s : Set β} {t : Set α} {a : α} (h : a ∈ t) (ht : IsOpen t)
    (hs : s ∈ @nhds β (TopologicalSpace.coinduced (fun x : t => π x) Subtype.topologicalSpace) (π a)) : π ⁻¹' s ∈ 𝓝 a :=
  by
  rw [← ht.nhds_within_eq h]
  exact preimage_nhds_within_coinduced' h ht hs

@[simp]
theorem nhds_within_empty (a : α) : 𝓝[∅] a = ⊥ := by
  rw [nhdsWithin, principal_empty, inf_bot_eq]

theorem nhds_within_union (a : α) (s t : Set α) : 𝓝[s ∪ t] a = 𝓝[s] a⊔𝓝[t] a := by
  delta' nhdsWithin
  rw [← inf_sup_left, sup_principal]

theorem nhds_within_inter (a : α) (s t : Set α) : 𝓝[s ∩ t] a = 𝓝[s] a⊓𝓝[t] a := by
  delta' nhdsWithin
  rw [inf_left_comm, inf_assoc, inf_principal, ← inf_assoc, inf_idem]

theorem nhds_within_inter' (a : α) (s t : Set α) : 𝓝[s ∩ t] a = 𝓝[s] a⊓𝓟 t := by
  delta' nhdsWithin
  rw [← inf_principal, inf_assoc]

theorem nhds_within_inter_of_mem {a : α} {s t : Set α} (h : s ∈ 𝓝[t] a) : 𝓝[s ∩ t] a = 𝓝[t] a := by
  rw [nhds_within_inter, inf_eq_right]
  exact nhds_within_le_of_mem h

@[simp]
theorem nhds_within_singleton (a : α) : 𝓝[{a}] a = pure a := by
  rw [nhdsWithin, principal_singleton, inf_eq_right.2 (pure_le_nhds a)]

@[simp]
theorem nhds_within_insert (a : α) (s : Set α) : 𝓝[insert a s] a = pure a⊔𝓝[s] a := by
  rw [← singleton_union, nhds_within_union, nhds_within_singleton]

theorem mem_nhds_within_insert {a : α} {s t : Set α} : t ∈ 𝓝[insert a s] a ↔ a ∈ t ∧ t ∈ 𝓝[s] a := by
  simp

theorem insert_mem_nhds_within_insert {a : α} {s t : Set α} (h : t ∈ 𝓝[s] a) : insert a t ∈ 𝓝[insert a s] a := by
  simp [← mem_of_superset h]

theorem insert_mem_nhds_iff {a : α} {s : Set α} : insert a s ∈ 𝓝 a ↔ s ∈ 𝓝[≠] a := by
  simp only [← nhdsWithin, ← mem_inf_principal, ← mem_compl_iff, ← mem_singleton_iff, ← or_iff_not_imp_left, ←
    insert_def]

@[simp]
theorem nhds_within_compl_singleton_sup_pure (a : α) : 𝓝[≠] a⊔pure a = 𝓝 a := by
  rw [← nhds_within_singleton, ← nhds_within_union, compl_union_self, nhds_within_univ]

theorem nhds_within_prod_eq {α : Type _} [TopologicalSpace α] {β : Type _} [TopologicalSpace β] (a : α) (b : β)
    (s : Set α) (t : Set β) : 𝓝[s ×ˢ t] (a, b) = 𝓝[s] a ×ᶠ 𝓝[t] b := by
  delta' nhdsWithin
  rw [nhds_prod_eq, ← Filter.prod_inf_prod, Filter.prod_principal_principal]

theorem nhds_within_prod {α : Type _} [TopologicalSpace α] {β : Type _} [TopologicalSpace β] {s u : Set α} {t v : Set β}
    {a : α} {b : β} (hu : u ∈ 𝓝[s] a) (hv : v ∈ 𝓝[t] b) : u ×ˢ v ∈ 𝓝[s ×ˢ t] (a, b) := by
  rw [nhds_within_prod_eq]
  exact prod_mem_prod hu hv

theorem nhds_within_pi_eq' {ι : Type _} {α : ι → Type _} [∀ i, TopologicalSpace (α i)] {I : Set ι} (hI : I.Finite)
    (s : ∀ i, Set (α i)) (x : ∀ i, α i) : 𝓝[pi I s] x = ⨅ i, comap (fun x => x i) (𝓝 (x i)⊓⨅ hi : i ∈ I, 𝓟 (s i)) := by
  simp only [← nhdsWithin, ← nhds_pi, ← Filter.pi, ← comap_inf, ← comap_infi, ← pi_def, ← comap_principal,
    infi_principal_finite hI, infi_inf_eq]

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (i «expr ∉ » I)
theorem nhds_within_pi_eq {ι : Type _} {α : ι → Type _} [∀ i, TopologicalSpace (α i)] {I : Set ι} (hI : I.Finite)
    (s : ∀ i, Set (α i)) (x : ∀ i, α i) :
    𝓝[pi I s] x = (⨅ i ∈ I, comap (fun x => x i) (𝓝[s i] x i))⊓⨅ (i) (_ : i ∉ I), comap (fun x => x i) (𝓝 (x i)) := by
  simp only [← nhdsWithin, ← nhds_pi, ← Filter.pi, ← pi_def, infi_principal_finite hI, ← comap_inf, ← comap_principal, ←
    eval]
  rw [infi_split _ fun i => i ∈ I, inf_right_comm]
  simp only [← infi_inf_eq]

theorem nhds_within_pi_univ_eq {ι : Type _} {α : ι → Type _} [Fintype ι] [∀ i, TopologicalSpace (α i)]
    (s : ∀ i, Set (α i)) (x : ∀ i, α i) : 𝓝[pi Univ s] x = ⨅ i, comap (fun x => x i) (𝓝[s i] x i) := by
  simpa [← nhdsWithin] using nhds_within_pi_eq finite_univ s x

theorem nhds_within_pi_eq_bot {ι : Type _} {α : ι → Type _} [∀ i, TopologicalSpace (α i)] {I : Set ι}
    {s : ∀ i, Set (α i)} {x : ∀ i, α i} : 𝓝[pi I s] x = ⊥ ↔ ∃ i ∈ I, 𝓝[s i] x i = ⊥ := by
  simp only [← nhdsWithin, ← nhds_pi, ← pi_inf_principal_pi_eq_bot]

theorem nhds_within_pi_ne_bot {ι : Type _} {α : ι → Type _} [∀ i, TopologicalSpace (α i)] {I : Set ι}
    {s : ∀ i, Set (α i)} {x : ∀ i, α i} : (𝓝[pi I s] x).ne_bot ↔ ∀, ∀ i ∈ I, ∀, (𝓝[s i] x i).ne_bot := by
  simp [← ne_bot_iff, ← nhds_within_pi_eq_bot]

theorem Filter.Tendsto.piecewise_nhds_within {f g : α → β} {t : Set α} [∀ x, Decidable (x ∈ t)] {a : α} {s : Set α}
    {l : Filter β} (h₀ : Tendsto f (𝓝[s ∩ t] a) l) (h₁ : Tendsto g (𝓝[s ∩ tᶜ] a) l) :
    Tendsto (piecewise t f g) (𝓝[s] a) l := by
  apply tendsto.piecewise <;> rwa [← nhds_within_inter']

theorem Filter.Tendsto.if_nhds_within {f g : α → β} {p : α → Prop} [DecidablePred p] {a : α} {s : Set α} {l : Filter β}
    (h₀ : Tendsto f (𝓝[s ∩ { x | p x }] a) l) (h₁ : Tendsto g (𝓝[s ∩ { x | ¬p x }] a) l) :
    Tendsto (fun x => if p x then f x else g x) (𝓝[s] a) l :=
  h₀.piecewise_nhds_within h₁

theorem map_nhds_within (f : α → β) (a : α) (s : Set α) :
    map f (𝓝[s] a) = ⨅ t ∈ { t : Set α | a ∈ t ∧ IsOpen t }, 𝓟 (f '' (t ∩ s)) :=
  ((nhds_within_basis_open a s).map f).eq_binfi

theorem tendsto_nhds_within_mono_left {f : α → β} {a : α} {s t : Set α} {l : Filter β} (hst : s ⊆ t)
    (h : Tendsto f (𝓝[t] a) l) : Tendsto f (𝓝[s] a) l :=
  h.mono_left <| nhds_within_mono a hst

theorem tendsto_nhds_within_mono_right {f : β → α} {l : Filter β} {a : α} {s t : Set α} (hst : s ⊆ t)
    (h : Tendsto f l (𝓝[s] a)) : Tendsto f l (𝓝[t] a) :=
  h.mono_right (nhds_within_mono a hst)

theorem tendsto_nhds_within_of_tendsto_nhds {f : α → β} {a : α} {s : Set α} {l : Filter β} (h : Tendsto f (𝓝 a) l) :
    Tendsto f (𝓝[s] a) l :=
  h.mono_left inf_le_left

theorem principal_subtype {α : Type _} (s : Set α) (t : Set { x // x ∈ s }) :
    𝓟 t = comap coe (𝓟 ((coe : s → α) '' t)) := by
  rw [comap_principal, Set.preimage_image_eq _ Subtype.coe_injective]

theorem nhds_within_ne_bot_of_mem {s : Set α} {x : α} (hx : x ∈ s) : NeBot (𝓝[s] x) :=
  mem_closure_iff_nhds_within_ne_bot.1 <| subset_closure hx

theorem IsClosed.mem_of_nhds_within_ne_bot {s : Set α} (hs : IsClosed s) {x : α} (hx : ne_bot <| 𝓝[s] x) : x ∈ s := by
  simpa only [← hs.closure_eq] using mem_closure_iff_nhds_within_ne_bot.2 hx

theorem DenseRange.nhds_within_ne_bot {ι : Type _} {f : ι → α} (h : DenseRange f) (x : α) : NeBot (𝓝[Range f] x) :=
  mem_closure_iff_cluster_pt.1 (h x)

theorem mem_closure_pi {ι : Type _} {α : ι → Type _} [∀ i, TopologicalSpace (α i)] {I : Set ι} {s : ∀ i, Set (α i)}
    {x : ∀ i, α i} : x ∈ Closure (pi I s) ↔ ∀, ∀ i ∈ I, ∀, x i ∈ Closure (s i) := by
  simp only [← mem_closure_iff_nhds_within_ne_bot, ← nhds_within_pi_ne_bot]

theorem closure_pi_set {ι : Type _} {α : ι → Type _} [∀ i, TopologicalSpace (α i)] (I : Set ι) (s : ∀ i, Set (α i)) :
    Closure (pi I s) = pi I fun i => Closure (s i) :=
  Set.ext fun x => mem_closure_pi

theorem dense_pi {ι : Type _} {α : ι → Type _} [∀ i, TopologicalSpace (α i)] {s : ∀ i, Set (α i)} (I : Set ι)
    (hs : ∀, ∀ i ∈ I, ∀, Dense (s i)) : Dense (pi I s) := by
  simp only [← dense_iff_closure_eq, ← closure_pi_set, ← pi_congr rfl fun i hi => (hs i hi).closure_eq, ← pi_univ]

theorem eventually_eq_nhds_within_iff {f g : α → β} {s : Set α} {a : α} :
    f =ᶠ[𝓝[s] a] g ↔ ∀ᶠ x in 𝓝 a, x ∈ s → f x = g x :=
  mem_inf_principal

theorem eventually_eq_nhds_within_of_eq_on {f g : α → β} {s : Set α} {a : α} (h : EqOn f g s) : f =ᶠ[𝓝[s] a] g :=
  mem_inf_of_right h

theorem Set.EqOn.eventually_eq_nhds_within {f g : α → β} {s : Set α} {a : α} (h : EqOn f g s) : f =ᶠ[𝓝[s] a] g :=
  eventually_eq_nhds_within_of_eq_on h

theorem tendsto_nhds_within_congr {f g : α → β} {s : Set α} {a : α} {l : Filter β} (hfg : ∀, ∀ x ∈ s, ∀, f x = g x)
    (hf : Tendsto f (𝓝[s] a) l) : Tendsto g (𝓝[s] a) l :=
  (tendsto_congr' <| eventually_eq_nhds_within_of_eq_on hfg).1 hf

theorem eventually_nhds_within_of_forall {s : Set α} {a : α} {p : α → Prop} (h : ∀, ∀ x ∈ s, ∀, p x) :
    ∀ᶠ x in 𝓝[s] a, p x :=
  mem_inf_of_right h

theorem tendsto_nhds_within_of_tendsto_nhds_of_eventually_within {a : α} {l : Filter β} {s : Set α} (f : β → α)
    (h1 : Tendsto f l (𝓝 a)) (h2 : ∀ᶠ x in l, f x ∈ s) : Tendsto f l (𝓝[s] a) :=
  tendsto_inf.2 ⟨h1, tendsto_principal.2 h2⟩

@[simp]
theorem tendsto_nhds_within_range {a : α} {l : Filter β} {f : β → α} : Tendsto f l (𝓝[Range f] a) ↔ Tendsto f l (𝓝 a) :=
  ⟨fun h => h.mono_right inf_le_left, fun h =>
    tendsto_inf.2 ⟨h, tendsto_principal.2 <| eventually_of_forall mem_range_self⟩⟩

theorem Filter.EventuallyEq.eq_of_nhds_within {s : Set α} {f g : α → β} {a : α} (h : f =ᶠ[𝓝[s] a] g) (hmem : a ∈ s) :
    f a = g a :=
  h.self_of_nhds_within hmem

theorem eventually_nhds_within_of_eventually_nhds {α : Type _} [TopologicalSpace α] {s : Set α} {a : α} {p : α → Prop}
    (h : ∀ᶠ x in 𝓝 a, p x) : ∀ᶠ x in 𝓝[s] a, p x :=
  mem_nhds_within_of_mem_nhds h

/-!
### `nhds_within` and subtypes
-/


theorem mem_nhds_within_subtype {s : Set α} {a : { x // x ∈ s }} {t u : Set { x // x ∈ s }} :
    t ∈ 𝓝[u] a ↔ t ∈ comap (coe : s → α) (𝓝[coe '' u] a) := by
  rw [nhdsWithin, nhds_subtype, principal_subtype, ← comap_inf, ← nhdsWithin]

theorem nhds_within_subtype (s : Set α) (a : { x // x ∈ s }) (t : Set { x // x ∈ s }) :
    𝓝[t] a = comap (coe : s → α) (𝓝[coe '' t] a) :=
  Filter.ext fun u => mem_nhds_within_subtype

theorem nhds_within_eq_map_subtype_coe {s : Set α} {a : α} (h : a ∈ s) : 𝓝[s] a = map (coe : s → α) (𝓝 ⟨a, h⟩) := by
  simpa only [← Subtype.range_coe] using (embedding_subtype_coe.map_nhds_eq ⟨a, h⟩).symm

theorem mem_nhds_subtype_iff_nhds_within {s : Set α} {a : s} {t : Set s} : t ∈ 𝓝 a ↔ coe '' t ∈ 𝓝[s] (a : α) := by
  rw [nhds_within_eq_map_subtype_coe a.coe_prop, mem_map, preimage_image_eq _ Subtype.coe_injective, Subtype.coe_eta]

theorem preimage_coe_mem_nhds_subtype {s t : Set α} {a : s} : coe ⁻¹' t ∈ 𝓝 a ↔ t ∈ 𝓝[s] ↑a := by
  simp only [← mem_nhds_subtype_iff_nhds_within, ← Subtype.image_preimage_coe, ← inter_mem_iff, ← self_mem_nhds_within,
    ← and_trueₓ]

theorem tendsto_nhds_within_iff_subtype {s : Set α} {a : α} (h : a ∈ s) (f : α → β) (l : Filter β) :
    Tendsto f (𝓝[s] a) l ↔ Tendsto (s.restrict f) (𝓝 ⟨a, h⟩) l := by
  simp only [← tendsto, ← nhds_within_eq_map_subtype_coe h, ← Filter.map_map, ← restrict]

variable [TopologicalSpace β] [TopologicalSpace γ] [TopologicalSpace δ]

/-- A function between topological spaces is continuous at a point `x₀` within a subset `s`
if `f x` tends to `f x₀` when `x` tends to `x₀` while staying within `s`. -/
def ContinuousWithinAt (f : α → β) (s : Set α) (x : α) : Prop :=
  Tendsto f (𝓝[s] x) (𝓝 (f x))

/-- If a function is continuous within `s` at `x`, then it tends to `f x` within `s` by definition.
We register this fact for use with the dot notation, especially to use `tendsto.comp` as
`continuous_within_at.comp` will have a different meaning. -/
theorem ContinuousWithinAt.tendsto {f : α → β} {s : Set α} {x : α} (h : ContinuousWithinAt f s x) :
    Tendsto f (𝓝[s] x) (𝓝 (f x)) :=
  h

/-- A function between topological spaces is continuous on a subset `s`
when it's continuous at every point of `s` within `s`. -/
def ContinuousOn (f : α → β) (s : Set α) : Prop :=
  ∀, ∀ x ∈ s, ∀, ContinuousWithinAt f s x

theorem ContinuousOn.continuous_within_at {f : α → β} {s : Set α} {x : α} (hf : ContinuousOn f s) (hx : x ∈ s) :
    ContinuousWithinAt f s x :=
  hf x hx

theorem continuous_within_at_univ (f : α → β) (x : α) : ContinuousWithinAt f Set.Univ x ↔ ContinuousAt f x := by
  rw [ContinuousAt, ContinuousWithinAt, nhds_within_univ]

theorem continuous_within_at_iff_continuous_at_restrict (f : α → β) {x : α} {s : Set α} (h : x ∈ s) :
    ContinuousWithinAt f s x ↔ ContinuousAt (s.restrict f) ⟨x, h⟩ :=
  tendsto_nhds_within_iff_subtype h f _

theorem ContinuousWithinAt.tendsto_nhds_within {f : α → β} {x : α} {s : Set α} {t : Set β}
    (h : ContinuousWithinAt f s x) (ht : MapsTo f s t) : Tendsto f (𝓝[s] x) (𝓝[t] f x) :=
  tendsto_inf.2 ⟨h, tendsto_principal.2 <| mem_inf_of_right <| mem_principal.2 <| ht⟩

theorem ContinuousWithinAt.tendsto_nhds_within_image {f : α → β} {x : α} {s : Set α} (h : ContinuousWithinAt f s x) :
    Tendsto f (𝓝[s] x) (𝓝[f '' s] f x) :=
  h.tendsto_nhds_within (maps_to_image _ _)

theorem ContinuousWithinAt.prod_map {f : α → γ} {g : β → δ} {s : Set α} {t : Set β} {x : α} {y : β}
    (hf : ContinuousWithinAt f s x) (hg : ContinuousWithinAt g t y) :
    ContinuousWithinAt (Prod.map f g) (s ×ˢ t) (x, y) := by
  unfold ContinuousWithinAt  at *
  rw [nhds_within_prod_eq, Prod.map, nhds_prod_eq]
  exact hf.prod_map hg

theorem continuous_within_at_pi {ι : Type _} {π : ι → Type _} [∀ i, TopologicalSpace (π i)] {f : α → ∀ i, π i}
    {s : Set α} {x : α} : ContinuousWithinAt f s x ↔ ∀ i, ContinuousWithinAt (fun y => f y i) s x :=
  tendsto_pi_nhds

theorem continuous_on_pi {ι : Type _} {π : ι → Type _} [∀ i, TopologicalSpace (π i)] {f : α → ∀ i, π i} {s : Set α} :
    ContinuousOn f s ↔ ∀ i, ContinuousOn (fun y => f y i) s :=
  ⟨fun h i x hx => tendsto_pi_nhds.1 (h x hx) i, fun h x hx => tendsto_pi_nhds.2 fun i => h i x hx⟩

theorem ContinuousWithinAt.fin_insert_nth {n} {π : Finₓ (n + 1) → Type _} [∀ i, TopologicalSpace (π i)]
    (i : Finₓ (n + 1)) {f : α → π i} {a : α} {s : Set α} (hf : ContinuousWithinAt f s a)
    {g : α → ∀ j : Finₓ n, π (i.succAbove j)} (hg : ContinuousWithinAt g s a) :
    ContinuousWithinAt (fun a => i.insertNth (f a) (g a)) s a :=
  hf.fin_insert_nth i hg

theorem ContinuousOn.fin_insert_nth {n} {π : Finₓ (n + 1) → Type _} [∀ i, TopologicalSpace (π i)] (i : Finₓ (n + 1))
    {f : α → π i} {s : Set α} (hf : ContinuousOn f s) {g : α → ∀ j : Finₓ n, π (i.succAbove j)}
    (hg : ContinuousOn g s) : ContinuousOn (fun a => i.insertNth (f a) (g a)) s := fun a ha =>
  (hf a ha).fin_insert_nth i (hg a ha)

theorem continuous_on_iff {f : α → β} {s : Set α} :
    ContinuousOn f s ↔ ∀, ∀ x ∈ s, ∀, ∀ t : Set β, IsOpen t → f x ∈ t → ∃ u, IsOpen u ∧ x ∈ u ∧ u ∩ s ⊆ f ⁻¹' t := by
  simp only [← ContinuousOn, ← ContinuousWithinAt, ← tendsto_nhds, ← mem_nhds_within]

theorem continuous_on_iff_continuous_restrict {f : α → β} {s : Set α} : ContinuousOn f s ↔ Continuous (s.restrict f) :=
  by
  rw [ContinuousOn, continuous_iff_continuous_at]
  constructor
  · rintro h ⟨x, xs⟩
    exact (continuous_within_at_iff_continuous_at_restrict f xs).mp (h x xs)
    
  intro h x xs
  exact (continuous_within_at_iff_continuous_at_restrict f xs).mpr (h ⟨x, xs⟩)

theorem continuous_on_iff' {f : α → β} {s : Set α} :
    ContinuousOn f s ↔ ∀ t : Set β, IsOpen t → ∃ u, IsOpen u ∧ f ⁻¹' t ∩ s = u ∩ s := by
  have : ∀ t, IsOpen (s.restrict f ⁻¹' t) ↔ ∃ u : Set α, IsOpen u ∧ f ⁻¹' t ∩ s = u ∩ s := by
    intro t
    rw [is_open_induced_iff, Set.restrict_eq, Set.preimage_comp]
    simp only [← Subtype.preimage_coe_eq_preimage_coe_iff]
    constructor <;>
      · rintro ⟨u, ou, useq⟩
        exact ⟨u, ou, useq.symm⟩
        
  rw [continuous_on_iff_continuous_restrict, continuous_def] <;> simp only [← this]

/-- If a function is continuous on a set for some topologies, then it is
continuous on the same set with respect to any finer topology on the source space. -/
theorem ContinuousOn.mono_dom {α β : Type _} {t₁ t₂ : TopologicalSpace α} {t₃ : TopologicalSpace β} (h₁ : t₂ ≤ t₁)
    {s : Set α} {f : α → β} (h₂ : @ContinuousOn α β t₁ t₃ f s) : @ContinuousOn α β t₂ t₃ f s := by
  rw [continuous_on_iff'] at h₂⊢
  intro t ht
  rcases h₂ t ht with ⟨u, hu, h'u⟩
  exact ⟨u, h₁ u hu, h'u⟩

/-- If a function is continuous on a set for some topologies, then it is
continuous on the same set with respect to any coarser topology on the target space. -/
theorem ContinuousOn.mono_rng {α β : Type _} {t₁ : TopologicalSpace α} {t₂ t₃ : TopologicalSpace β} (h₁ : t₂ ≤ t₃)
    {s : Set α} {f : α → β} (h₂ : @ContinuousOn α β t₁ t₂ f s) : @ContinuousOn α β t₁ t₃ f s := by
  rw [continuous_on_iff'] at h₂⊢
  intro t ht
  exact h₂ t (h₁ t ht)

theorem continuous_on_iff_is_closed {f : α → β} {s : Set α} :
    ContinuousOn f s ↔ ∀ t : Set β, IsClosed t → ∃ u, IsClosed u ∧ f ⁻¹' t ∩ s = u ∩ s := by
  have : ∀ t, IsClosed (s.restrict f ⁻¹' t) ↔ ∃ u : Set α, IsClosed u ∧ f ⁻¹' t ∩ s = u ∩ s := by
    intro t
    rw [is_closed_induced_iff, Set.restrict_eq, Set.preimage_comp]
    simp only [← Subtype.preimage_coe_eq_preimage_coe_iff, ← eq_comm]
  rw [continuous_on_iff_continuous_restrict, continuous_iff_is_closed] <;> simp only [← this]

theorem ContinuousOn.prod_map {f : α → γ} {g : β → δ} {s : Set α} {t : Set β} (hf : ContinuousOn f s)
    (hg : ContinuousOn g t) : ContinuousOn (Prod.map f g) (s ×ˢ t) := fun ⟨x, y⟩ ⟨hx, hy⟩ =>
  ContinuousWithinAt.prod_map (hf x hx) (hg y hy)

theorem continuous_on_empty (f : α → β) : ContinuousOn f ∅ := fun x => False.elim

theorem continuous_on_singleton (f : α → β) (a : α) : ContinuousOn f {a} :=
  forall_eq.2 <| by
    simpa only [← ContinuousWithinAt, ← nhds_within_singleton, ← tendsto_pure_left] using fun s => mem_of_mem_nhds

theorem Set.Subsingleton.continuous_on {s : Set α} (hs : s.Subsingleton) (f : α → β) : ContinuousOn f s :=
  hs.induction_on (continuous_on_empty f) (continuous_on_singleton f)

theorem nhds_within_le_comap {x : α} {s : Set α} {f : α → β} (ctsf : ContinuousWithinAt f s x) :
    𝓝[s] x ≤ comap f (𝓝[f '' s] f x) :=
  ctsf.tendsto_nhds_within_image.le_comap

@[simp]
theorem comap_nhds_within_range {α} (f : α → β) (y : β) : comap f (𝓝[Range f] y) = comap f (𝓝 y) :=
  comap_inf_principal_range

theorem continuous_within_at_iff_ptendsto_res (f : α → β) {x : α} {s : Set α} :
    ContinuousWithinAt f s x ↔ Ptendsto (Pfun.res f s) (𝓝 x) (𝓝 (f x)) :=
  tendsto_iff_ptendsto _ _ _ _

theorem continuous_iff_continuous_on_univ {f : α → β} : Continuous f ↔ ContinuousOn f Univ := by
  simp [← continuous_iff_continuous_at, ← ContinuousOn, ← ContinuousAt, ← ContinuousWithinAt, ← nhds_within_univ]

theorem ContinuousWithinAt.mono {f : α → β} {s t : Set α} {x : α} (h : ContinuousWithinAt f t x) (hs : s ⊆ t) :
    ContinuousWithinAt f s x :=
  h.mono_left (nhds_within_mono x hs)

theorem ContinuousWithinAt.mono_of_mem {f : α → β} {s t : Set α} {x : α} (h : ContinuousWithinAt f t x)
    (hs : t ∈ 𝓝[s] x) : ContinuousWithinAt f s x :=
  h.mono_left (nhds_within_le_of_mem hs)

theorem continuous_within_at_inter' {f : α → β} {s t : Set α} {x : α} (h : t ∈ 𝓝[s] x) :
    ContinuousWithinAt f (s ∩ t) x ↔ ContinuousWithinAt f s x := by
  simp [← ContinuousWithinAt, ← nhds_within_restrict'' s h]

theorem continuous_within_at_inter {f : α → β} {s t : Set α} {x : α} (h : t ∈ 𝓝 x) :
    ContinuousWithinAt f (s ∩ t) x ↔ ContinuousWithinAt f s x := by
  simp [← ContinuousWithinAt, ← nhds_within_restrict' s h]

theorem continuous_within_at_union {f : α → β} {s t : Set α} {x : α} :
    ContinuousWithinAt f (s ∪ t) x ↔ ContinuousWithinAt f s x ∧ ContinuousWithinAt f t x := by
  simp only [← ContinuousWithinAt, ← nhds_within_union, ← tendsto_sup]

theorem ContinuousWithinAt.union {f : α → β} {s t : Set α} {x : α} (hs : ContinuousWithinAt f s x)
    (ht : ContinuousWithinAt f t x) : ContinuousWithinAt f (s ∪ t) x :=
  continuous_within_at_union.2 ⟨hs, ht⟩

theorem ContinuousWithinAt.mem_closure_image {f : α → β} {s : Set α} {x : α} (h : ContinuousWithinAt f s x)
    (hx : x ∈ Closure s) : f x ∈ Closure (f '' s) :=
  have := mem_closure_iff_nhds_within_ne_bot.1 hx
  mem_closure_of_tendsto h <| mem_of_superset self_mem_nhds_within (subset_preimage_image f s)

theorem ContinuousWithinAt.mem_closure {f : α → β} {s : Set α} {x : α} {A : Set β} (h : ContinuousWithinAt f s x)
    (hx : x ∈ Closure s) (hA : MapsTo f s A) : f x ∈ Closure A :=
  closure_mono (image_subset_iff.2 hA) (h.mem_closure_image hx)

theorem Set.MapsTo.closure_of_continuous_within_at {f : α → β} {s : Set α} {t : Set β} (h : MapsTo f s t)
    (hc : ∀, ∀ x ∈ Closure s, ∀, ContinuousWithinAt f s x) : MapsTo f (Closure s) (Closure t) := fun x hx =>
  (hc x hx).mem_closure hx h

theorem Set.MapsTo.closure_of_continuous_on {f : α → β} {s : Set α} {t : Set β} (h : MapsTo f s t)
    (hc : ContinuousOn f (Closure s)) : MapsTo f (Closure s) (Closure t) :=
  h.closure_of_continuous_within_at fun x hx => (hc x hx).mono subset_closure

theorem ContinuousWithinAt.image_closure {f : α → β} {s : Set α}
    (hf : ∀, ∀ x ∈ Closure s, ∀, ContinuousWithinAt f s x) : f '' Closure s ⊆ Closure (f '' s) :=
  maps_to'.1 <| (maps_to_image f s).closure_of_continuous_within_at hf

theorem ContinuousOn.image_closure {f : α → β} {s : Set α} (hf : ContinuousOn f (Closure s)) :
    f '' Closure s ⊆ Closure (f '' s) :=
  ContinuousWithinAt.image_closure fun x hx => (hf x hx).mono subset_closure

@[simp]
theorem continuous_within_at_singleton {f : α → β} {x : α} : ContinuousWithinAt f {x} x := by
  simp only [← ContinuousWithinAt, ← nhds_within_singleton, ← tendsto_pure_nhds]

@[simp]
theorem continuous_within_at_insert_self {f : α → β} {x : α} {s : Set α} :
    ContinuousWithinAt f (insert x s) x ↔ ContinuousWithinAt f s x := by
  simp only [singleton_union, ← continuous_within_at_union, ← continuous_within_at_singleton, ← true_andₓ]

alias continuous_within_at_insert_self ↔ _ ContinuousWithinAt.insert_self

theorem ContinuousWithinAt.diff_iff {f : α → β} {s t : Set α} {x : α} (ht : ContinuousWithinAt f t x) :
    ContinuousWithinAt f (s \ t) x ↔ ContinuousWithinAt f s x :=
  ⟨fun h =>
    (h.union ht).mono <| by
      simp only [← diff_union_self, ← subset_union_left],
    fun h => h.mono (diff_subset _ _)⟩

@[simp]
theorem continuous_within_at_diff_self {f : α → β} {s : Set α} {x : α} :
    ContinuousWithinAt f (s \ {x}) x ↔ ContinuousWithinAt f s x :=
  continuous_within_at_singleton.diff_iff

@[simp]
theorem continuous_within_at_compl_self {f : α → β} {a : α} : ContinuousWithinAt f ({a}ᶜ) a ↔ ContinuousAt f a := by
  rw [compl_eq_univ_diff, continuous_within_at_diff_self, continuous_within_at_univ]

@[simp]
theorem continuous_within_at_update_same [DecidableEq α] {f : α → β} {s : Set α} {x : α} {y : β} :
    ContinuousWithinAt (update f x y) s x ↔ Tendsto f (𝓝[s \ {x}] x) (𝓝 y) :=
  calc
    ContinuousWithinAt (update f x y) s x ↔ Tendsto (update f x y) (𝓝[s \ {x}] x) (𝓝 y) := by
      rw [← continuous_within_at_diff_self, ContinuousWithinAt, Function.update_same]
    _ ↔ Tendsto f (𝓝[s \ {x}] x) (𝓝 y) :=
      tendsto_congr' <| eventually_nhds_within_iff.2 <| eventually_of_forall fun z hz => update_noteq hz.2 _ _
    

@[simp]
theorem continuous_at_update_same [DecidableEq α] {f : α → β} {x : α} {y : β} :
    ContinuousAt (Function.update f x y) x ↔ Tendsto f (𝓝[≠] x) (𝓝 y) := by
  rw [← continuous_within_at_univ, continuous_within_at_update_same, compl_eq_univ_diff]

theorem IsOpenMap.continuous_on_image_of_left_inv_on {f : α → β} {s : Set α} (h : IsOpenMap (s.restrict f))
    {finv : β → α} (hleft : LeftInvOn finv f s) : ContinuousOn finv (f '' s) := by
  refine' continuous_on_iff'.2 fun t ht => ⟨f '' (t ∩ s), _, _⟩
  · rw [← image_restrict]
    exact h _ (ht.preimage continuous_subtype_coe)
    
  · rw [inter_eq_self_of_subset_left (image_subset f (inter_subset_right t s)), hleft.image_inter']
    

theorem IsOpenMap.continuous_on_range_of_left_inverse {f : α → β} (hf : IsOpenMap f) {finv : β → α}
    (hleft : Function.LeftInverse finv f) : ContinuousOn finv (Range f) := by
  rw [← image_univ]
  exact (hf.restrict is_open_univ).continuous_on_image_of_left_inv_on fun x _ => hleft x

theorem ContinuousOn.congr_mono {f g : α → β} {s s₁ : Set α} (h : ContinuousOn f s) (h' : EqOn g f s₁) (h₁ : s₁ ⊆ s) :
    ContinuousOn g s₁ := by
  intro x hx
  unfold ContinuousWithinAt
  have A := (h x (h₁ hx)).mono h₁
  unfold ContinuousWithinAt  at A
  rw [← h' hx] at A
  exact A.congr' h'.eventually_eq_nhds_within.symm

theorem ContinuousOn.congr {f g : α → β} {s : Set α} (h : ContinuousOn f s) (h' : EqOn g f s) : ContinuousOn g s :=
  h.congr_mono h' (Subset.refl _)

theorem continuous_on_congr {f g : α → β} {s : Set α} (h' : EqOn g f s) : ContinuousOn g s ↔ ContinuousOn f s :=
  ⟨fun h => ContinuousOn.congr h h'.symm, fun h => h.congr h'⟩

theorem ContinuousAt.continuous_within_at {f : α → β} {s : Set α} {x : α} (h : ContinuousAt f x) :
    ContinuousWithinAt f s x :=
  ContinuousWithinAt.mono ((continuous_within_at_univ f x).2 h) (subset_univ _)

theorem continuous_within_at_iff_continuous_at {f : α → β} {s : Set α} {x : α} (h : s ∈ 𝓝 x) :
    ContinuousWithinAt f s x ↔ ContinuousAt f x := by
  rw [← univ_inter s, continuous_within_at_inter h, continuous_within_at_univ]

theorem ContinuousWithinAt.continuous_at {f : α → β} {s : Set α} {x : α} (h : ContinuousWithinAt f s x) (hs : s ∈ 𝓝 x) :
    ContinuousAt f x :=
  (continuous_within_at_iff_continuous_at hs).mp h

theorem ContinuousOn.continuous_at {f : α → β} {s : Set α} {x : α} (h : ContinuousOn f s) (hx : s ∈ 𝓝 x) :
    ContinuousAt f x :=
  (h x (mem_of_mem_nhds hx)).ContinuousAt hx

theorem ContinuousAt.continuous_on {f : α → β} {s : Set α} (hcont : ∀, ∀ x ∈ s, ∀, ContinuousAt f x) :
    ContinuousOn f s := fun x hx => (hcont x hx).ContinuousWithinAt

theorem ContinuousWithinAt.comp {g : β → γ} {f : α → β} {s : Set α} {t : Set β} {x : α}
    (hg : ContinuousWithinAt g t (f x)) (hf : ContinuousWithinAt f s x) (h : MapsTo f s t) :
    ContinuousWithinAt (g ∘ f) s x :=
  hg.Tendsto.comp (hf.tendsto_nhds_within h)

theorem ContinuousWithinAt.comp' {g : β → γ} {f : α → β} {s : Set α} {t : Set β} {x : α}
    (hg : ContinuousWithinAt g t (f x)) (hf : ContinuousWithinAt f s x) : ContinuousWithinAt (g ∘ f) (s ∩ f ⁻¹' t) x :=
  hg.comp (hf.mono (inter_subset_left _ _)) (inter_subset_right _ _)

theorem ContinuousAt.comp_continuous_within_at {g : β → γ} {f : α → β} {s : Set α} {x : α} (hg : ContinuousAt g (f x))
    (hf : ContinuousWithinAt f s x) : ContinuousWithinAt (g ∘ f) s x :=
  hg.ContinuousWithinAt.comp hf (maps_to_univ _ _)

theorem ContinuousOn.comp {g : β → γ} {f : α → β} {s : Set α} {t : Set β} (hg : ContinuousOn g t)
    (hf : ContinuousOn f s) (h : MapsTo f s t) : ContinuousOn (g ∘ f) s := fun x hx =>
  ContinuousWithinAt.comp (hg _ (h hx)) (hf x hx) h

theorem ContinuousOn.mono {f : α → β} {s t : Set α} (hf : ContinuousOn f s) (h : t ⊆ s) : ContinuousOn f t :=
  fun x hx => (hf x (h hx)).mono_left (nhds_within_mono _ h)

theorem antitone_continuous_on {f : α → β} : Antitone (ContinuousOn f) := fun s t hst hf => hf.mono hst

theorem ContinuousOn.comp' {g : β → γ} {f : α → β} {s : Set α} {t : Set β} (hg : ContinuousOn g t)
    (hf : ContinuousOn f s) : ContinuousOn (g ∘ f) (s ∩ f ⁻¹' t) :=
  hg.comp (hf.mono (inter_subset_left _ _)) (inter_subset_right _ _)

theorem Continuous.continuous_on {f : α → β} {s : Set α} (h : Continuous f) : ContinuousOn f s := by
  rw [continuous_iff_continuous_on_univ] at h
  exact h.mono (subset_univ _)

theorem Continuous.continuous_within_at {f : α → β} {s : Set α} {x : α} (h : Continuous f) : ContinuousWithinAt f s x :=
  h.ContinuousAt.ContinuousWithinAt

theorem Continuous.comp_continuous_on {g : β → γ} {f : α → β} {s : Set α} (hg : Continuous g) (hf : ContinuousOn f s) :
    ContinuousOn (g ∘ f) s :=
  hg.ContinuousOn.comp hf (maps_to_univ _ _)

theorem ContinuousOn.comp_continuous {g : β → γ} {f : α → β} {s : Set β} (hg : ContinuousOn g s) (hf : Continuous f)
    (hs : ∀ x, f x ∈ s) : Continuous (g ∘ f) := by
  rw [continuous_iff_continuous_on_univ] at *
  exact hg.comp hf fun x _ => hs x

theorem ContinuousWithinAt.preimage_mem_nhds_within {f : α → β} {x : α} {s : Set α} {t : Set β}
    (h : ContinuousWithinAt f s x) (ht : t ∈ 𝓝 (f x)) : f ⁻¹' t ∈ 𝓝[s] x :=
  h ht

theorem Set.LeftInvOn.map_nhds_within_eq {f : α → β} {g : β → α} {x : β} {s : Set β} (h : LeftInvOn f g s)
    (hx : f (g x) = x) (hf : ContinuousWithinAt f (g '' s) (g x)) (hg : ContinuousWithinAt g s x) :
    map g (𝓝[s] x) = 𝓝[g '' s] g x := by
  apply le_antisymmₓ
  · exact hg.tendsto_nhds_within (maps_to_image _ _)
    
  · have A : g ∘ f =ᶠ[𝓝[g '' s] g x] id := h.right_inv_on_image.eq_on.eventually_eq_of_mem self_mem_nhds_within
    refine' le_map_of_right_inverse A _
    simpa only [← hx] using hf.tendsto_nhds_within (h.maps_to (surj_on_image _ _))
    

theorem Function.LeftInverse.map_nhds_eq {f : α → β} {g : β → α} {x : β} (h : Function.LeftInverse f g)
    (hf : ContinuousWithinAt f (Range g) (g x)) (hg : ContinuousAt g x) : map g (𝓝 x) = 𝓝[Range g] g x := by
  simpa only [← nhds_within_univ, ← image_univ] using
    (h.left_inv_on univ).map_nhds_within_eq (h x)
      (by
        rwa [image_univ])
      hg.continuous_within_at

theorem ContinuousWithinAt.preimage_mem_nhds_within' {f : α → β} {x : α} {s : Set α} {t : Set β}
    (h : ContinuousWithinAt f s x) (ht : t ∈ 𝓝[f '' s] f x) : f ⁻¹' t ∈ 𝓝[s] x :=
  h.tendsto_nhds_within (maps_to_image _ _) ht

theorem Filter.EventuallyEq.congr_continuous_within_at {f g : α → β} {s : Set α} {x : α} (h : f =ᶠ[𝓝[s] x] g)
    (hx : f x = g x) : ContinuousWithinAt f s x ↔ ContinuousWithinAt g s x := by
  rw [ContinuousWithinAt, hx, tendsto_congr' h, ContinuousWithinAt]

theorem ContinuousWithinAt.congr_of_eventually_eq {f f₁ : α → β} {s : Set α} {x : α} (h : ContinuousWithinAt f s x)
    (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) : ContinuousWithinAt f₁ s x :=
  (h₁.congr_continuous_within_at hx).2 h

theorem ContinuousWithinAt.congr {f f₁ : α → β} {s : Set α} {x : α} (h : ContinuousWithinAt f s x)
    (h₁ : ∀, ∀ y ∈ s, ∀, f₁ y = f y) (hx : f₁ x = f x) : ContinuousWithinAt f₁ s x :=
  h.congr_of_eventually_eq (mem_of_superset self_mem_nhds_within h₁) hx

theorem ContinuousWithinAt.congr_mono {f g : α → β} {s s₁ : Set α} {x : α} (h : ContinuousWithinAt f s x)
    (h' : EqOn g f s₁) (h₁ : s₁ ⊆ s) (hx : g x = f x) : ContinuousWithinAt g s₁ x :=
  (h.mono h₁).congr h' hx

theorem continuous_on_const {s : Set α} {c : β} : ContinuousOn (fun x => c) s :=
  continuous_const.ContinuousOn

theorem continuous_within_at_const {b : β} {s : Set α} {x : α} : ContinuousWithinAt (fun _ : α => b) s x :=
  continuous_const.ContinuousWithinAt

theorem continuous_on_id {s : Set α} : ContinuousOn id s :=
  continuous_id.ContinuousOn

theorem continuous_within_at_id {s : Set α} {x : α} : ContinuousWithinAt id s x :=
  continuous_id.ContinuousWithinAt

theorem continuous_on_open_iff {f : α → β} {s : Set α} (hs : IsOpen s) :
    ContinuousOn f s ↔ ∀ t, IsOpen t → IsOpen (s ∩ f ⁻¹' t) := by
  rw [continuous_on_iff']
  constructor
  · intro h t ht
    rcases h t ht with ⟨u, u_open, hu⟩
    rw [inter_comm, hu]
    apply IsOpen.inter u_open hs
    
  · intro h t ht
    refine' ⟨s ∩ f ⁻¹' t, h t ht, _⟩
    rw [@inter_comm _ s (f ⁻¹' t), inter_assoc, inter_self]
    

theorem ContinuousOn.preimage_open_of_open {f : α → β} {s : Set α} {t : Set β} (hf : ContinuousOn f s) (hs : IsOpen s)
    (ht : IsOpen t) : IsOpen (s ∩ f ⁻¹' t) :=
  (continuous_on_open_iff hs).1 hf t ht

theorem ContinuousOn.is_open_preimage {f : α → β} {s : Set α} {t : Set β} (h : ContinuousOn f s) (hs : IsOpen s)
    (hp : f ⁻¹' t ⊆ s) (ht : IsOpen t) : IsOpen (f ⁻¹' t) := by
  convert (continuous_on_open_iff hs).mp h t ht
  rw [inter_comm, inter_eq_self_of_subset_left hp]

theorem ContinuousOn.preimage_closed_of_closed {f : α → β} {s : Set α} {t : Set β} (hf : ContinuousOn f s)
    (hs : IsClosed s) (ht : IsClosed t) : IsClosed (s ∩ f ⁻¹' t) := by
  rcases continuous_on_iff_is_closed.1 hf t ht with ⟨u, hu⟩
  rw [inter_comm, hu.2]
  apply IsClosed.inter hu.1 hs

theorem ContinuousOn.preimage_interior_subset_interior_preimage {f : α → β} {s : Set α} {t : Set β}
    (hf : ContinuousOn f s) (hs : IsOpen s) : s ∩ f ⁻¹' Interior t ⊆ s ∩ Interior (f ⁻¹' t) :=
  calc
    s ∩ f ⁻¹' Interior t ⊆ Interior (s ∩ f ⁻¹' t) :=
      interior_maximal (inter_subset_inter (Subset.refl _) (preimage_mono interior_subset))
        (hf.preimage_open_of_open hs is_open_interior)
    _ = s ∩ Interior (f ⁻¹' t) := by
      rw [interior_inter, hs.interior_eq]
    

theorem continuous_on_of_locally_continuous_on {f : α → β} {s : Set α}
    (h : ∀, ∀ x ∈ s, ∀, ∃ t, IsOpen t ∧ x ∈ t ∧ ContinuousOn f (s ∩ t)) : ContinuousOn f s := by
  intro x xs
  rcases h x xs with ⟨t, open_t, xt, ct⟩
  have := ct x ⟨xs, xt⟩
  rwa [ContinuousWithinAt, ← nhds_within_restrict _ xt open_t] at this

theorem continuous_on_open_of_generate_from {β : Type _} {s : Set α} {T : Set (Set β)} {f : α → β} (hs : IsOpen s)
    (h : ∀, ∀ t ∈ T, ∀, IsOpen (s ∩ f ⁻¹' t)) : @ContinuousOn α β _ (TopologicalSpace.generateFrom T) f s := by
  rw [continuous_on_open_iff]
  intro t ht
  induction' ht with u hu u v Tu Tv hu hv U hU hU'
  · exact h u hu
    
  · simp only [← preimage_univ, ← inter_univ]
    exact hs
    
  · have : s ∩ f ⁻¹' (u ∩ v) = s ∩ f ⁻¹' u ∩ (s ∩ f ⁻¹' v) := by
      rw [preimage_inter, inter_assoc, inter_left_comm _ s, ← inter_assoc s s, inter_self]
    rw [this]
    exact hu.inter hv
    
  · rw [preimage_sUnion, inter_Union₂]
    exact is_open_bUnion hU'
    
  · exact hs
    

theorem ContinuousWithinAt.prod {f : α → β} {g : α → γ} {s : Set α} {x : α} (hf : ContinuousWithinAt f s x)
    (hg : ContinuousWithinAt g s x) : ContinuousWithinAt (fun x => (f x, g x)) s x :=
  hf.prod_mk_nhds hg

theorem ContinuousOn.prod {f : α → β} {g : α → γ} {s : Set α} (hf : ContinuousOn f s) (hg : ContinuousOn g s) :
    ContinuousOn (fun x => (f x, g x)) s := fun x hx => ContinuousWithinAt.prod (hf x hx) (hg x hx)

theorem Inducing.continuous_within_at_iff {f : α → β} {g : β → γ} (hg : Inducing g) {s : Set α} {x : α} :
    ContinuousWithinAt f s x ↔ ContinuousWithinAt (g ∘ f) s x := by
  simp_rw [ContinuousWithinAt, Inducing.tendsto_nhds_iff hg]

theorem Inducing.continuous_on_iff {f : α → β} {g : β → γ} (hg : Inducing g) {s : Set α} :
    ContinuousOn f s ↔ ContinuousOn (g ∘ f) s := by
  simp_rw [ContinuousOn, hg.continuous_within_at_iff]

theorem Embedding.continuous_on_iff {f : α → β} {g : β → γ} (hg : Embedding g) {s : Set α} :
    ContinuousOn f s ↔ ContinuousOn (g ∘ f) s :=
  Inducing.continuous_on_iff hg.1

theorem Embedding.map_nhds_within_eq {f : α → β} (hf : Embedding f) (s : Set α) (x : α) :
    map f (𝓝[s] x) = 𝓝[f '' s] f x := by
  rw [nhdsWithin, map_inf hf.inj, hf.map_nhds_eq, map_principal, ← nhds_within_inter',
    inter_eq_self_of_subset_right (image_subset_range _ _)]

theorem OpenEmbedding.map_nhds_within_preimage_eq {f : α → β} (hf : OpenEmbedding f) (s : Set β) (x : α) :
    map f (𝓝[f ⁻¹' s] x) = 𝓝[s] f x := by
  rw [hf.to_embedding.map_nhds_within_eq, image_preimage_eq_inter_range]
  apply nhds_within_eq_nhds_within (mem_range_self _) hf.open_range
  rw [inter_assoc, inter_self]

theorem continuous_within_at_of_not_mem_closure {f : α → β} {s : Set α} {x : α} :
    x ∉ Closure s → ContinuousWithinAt f s x := by
  intro hx
  rw [mem_closure_iff_nhds_within_ne_bot, ne_bot_iff, not_not] at hx
  rw [ContinuousWithinAt, hx]
  exact tendsto_bot

theorem ContinuousOn.piecewise' {s t : Set α} {f g : α → β} [∀ a, Decidable (a ∈ t)]
    (hpf : ∀, ∀ a ∈ s ∩ Frontier t, ∀, Tendsto f (𝓝[s ∩ t] a) (𝓝 (piecewise t f g a)))
    (hpg : ∀, ∀ a ∈ s ∩ Frontier t, ∀, Tendsto g (𝓝[s ∩ tᶜ] a) (𝓝 (piecewise t f g a))) (hf : ContinuousOn f <| s ∩ t)
    (hg : ContinuousOn g <| s ∩ tᶜ) : ContinuousOn (piecewise t f g) s := by
  intro x hx
  by_cases' hx' : x ∈ Frontier t
  · exact (hpf x ⟨hx, hx'⟩).piecewise_nhds_within (hpg x ⟨hx, hx'⟩)
    
  · rw [← inter_univ s, ← union_compl_self t, inter_union_distrib_left] at hx⊢
    cases hx
    · apply ContinuousWithinAt.union
      · exact (hf x hx).congr (fun y hy => piecewise_eq_of_mem _ _ _ hy.2) (piecewise_eq_of_mem _ _ _ hx.2)
        
      · have : x ∉ Closure (tᶜ) := fun h =>
          hx'
            ⟨subset_closure hx.2, by
              rwa [closure_compl] at h⟩
        exact continuous_within_at_of_not_mem_closure fun h => this (closure_inter_subset_inter_closure _ _ h).2
        
      
    · apply ContinuousWithinAt.union
      · have : x ∉ Closure t := fun h => hx' ⟨h, fun h' : x ∈ Interior t => hx.2 (interior_subset h')⟩
        exact continuous_within_at_of_not_mem_closure fun h => this (closure_inter_subset_inter_closure _ _ h).2
        
      · exact (hg x hx).congr (fun y hy => piecewise_eq_of_not_mem _ _ _ hy.2) (piecewise_eq_of_not_mem _ _ _ hx.2)
        
      
    

theorem ContinuousOn.if' {s : Set α} {p : α → Prop} {f g : α → β} [∀ a, Decidable (p a)]
    (hpf : ∀, ∀ a ∈ s ∩ Frontier { a | p a }, ∀, Tendsto f (𝓝[s ∩ { a | p a }] a) (𝓝 <| if p a then f a else g a))
    (hpg : ∀, ∀ a ∈ s ∩ Frontier { a | p a }, ∀, Tendsto g (𝓝[s ∩ { a | ¬p a }] a) (𝓝 <| if p a then f a else g a))
    (hf : ContinuousOn f <| s ∩ { a | p a }) (hg : ContinuousOn g <| s ∩ { a | ¬p a }) :
    ContinuousOn (fun a => if p a then f a else g a) s :=
  hf.piecewise' hpf hpg hg

theorem ContinuousOn.if {α β : Type _} [TopologicalSpace α] [TopologicalSpace β] {p : α → Prop} [∀ a, Decidable (p a)]
    {s : Set α} {f g : α → β} (hp : ∀, ∀ a ∈ s ∩ Frontier { a | p a }, ∀, f a = g a)
    (hf : ContinuousOn f <| s ∩ Closure { a | p a }) (hg : ContinuousOn g <| s ∩ Closure { a | ¬p a }) :
    ContinuousOn (fun a => if p a then f a else g a) s := by
  apply ContinuousOn.if'
  · rintro a ha
    simp only [hp a ha, ← if_t_t]
    apply tendsto_nhds_within_mono_left (inter_subset_inter_right s subset_closure)
    exact hf a ⟨ha.1, ha.2.1⟩
    
  · rintro a ha
    simp only [← hp a ha, ← if_t_t]
    apply tendsto_nhds_within_mono_left (inter_subset_inter_right s subset_closure)
    rcases ha with ⟨has, ⟨_, ha⟩⟩
    rw [← mem_compl_iff, ← closure_compl] at ha
    apply hg a ⟨has, ha⟩
    
  · exact hf.mono (inter_subset_inter_right s subset_closure)
    
  · exact hg.mono (inter_subset_inter_right s subset_closure)
    

theorem ContinuousOn.piecewise {s t : Set α} {f g : α → β} [∀ a, Decidable (a ∈ t)]
    (ht : ∀, ∀ a ∈ s ∩ Frontier t, ∀, f a = g a) (hf : ContinuousOn f <| s ∩ Closure t)
    (hg : ContinuousOn g <| s ∩ Closure (tᶜ)) : ContinuousOn (piecewise t f g) s :=
  hf.if ht hg

theorem continuous_if' {p : α → Prop} {f g : α → β} [∀ a, Decidable (p a)]
    (hpf : ∀, ∀ a ∈ Frontier { x | p x }, ∀, Tendsto f (𝓝[{ x | p x }] a) (𝓝 <| ite (p a) (f a) (g a)))
    (hpg : ∀, ∀ a ∈ Frontier { x | p x }, ∀, Tendsto g (𝓝[{ x | ¬p x }] a) (𝓝 <| ite (p a) (f a) (g a)))
    (hf : ContinuousOn f { x | p x }) (hg : ContinuousOn g { x | ¬p x }) : Continuous fun a => ite (p a) (f a) (g a) :=
  by
  rw [continuous_iff_continuous_on_univ]
  apply ContinuousOn.if' <;> simp [*] <;> assumption

theorem continuous_if {p : α → Prop} {f g : α → β} [∀ a, Decidable (p a)]
    (hp : ∀, ∀ a ∈ Frontier { x | p x }, ∀, f a = g a) (hf : ContinuousOn f (Closure { x | p x }))
    (hg : ContinuousOn g (Closure { x | ¬p x })) : Continuous fun a => if p a then f a else g a := by
  rw [continuous_iff_continuous_on_univ]
  apply ContinuousOn.if <;> simp <;> assumption

theorem Continuous.if {p : α → Prop} {f g : α → β} [∀ a, Decidable (p a)]
    (hp : ∀, ∀ a ∈ Frontier { x | p x }, ∀, f a = g a) (hf : Continuous f) (hg : Continuous g) :
    Continuous fun a => if p a then f a else g a :=
  continuous_if hp hf.ContinuousOn hg.ContinuousOn

theorem continuous_if_const (p : Prop) {f g : α → β} [Decidable p] (hf : p → Continuous f) (hg : ¬p → Continuous g) :
    Continuous fun a => if p then f a else g a := by
  split_ifs
  exact hf h
  exact hg h

theorem Continuous.if_const (p : Prop) {f g : α → β} [Decidable p] (hf : Continuous f) (hg : Continuous g) :
    Continuous fun a => if p then f a else g a :=
  continuous_if_const p (fun _ => hf) fun _ => hg

theorem continuous_piecewise {s : Set α} {f g : α → β} [∀ a, Decidable (a ∈ s)] (hs : ∀, ∀ a ∈ Frontier s, ∀, f a = g a)
    (hf : ContinuousOn f (Closure s)) (hg : ContinuousOn g (Closure (sᶜ))) : Continuous (piecewise s f g) :=
  continuous_if hs hf hg

theorem Continuous.piecewise {s : Set α} {f g : α → β} [∀ a, Decidable (a ∈ s)] (hs : ∀, ∀ a ∈ Frontier s, ∀, f a = g a)
    (hf : Continuous f) (hg : Continuous g) : Continuous (piecewise s f g) :=
  hf.if hs hg

theorem IsOpen.ite' {s s' t : Set α} (hs : IsOpen s) (hs' : IsOpen s') (ht : ∀, ∀ x ∈ Frontier t, ∀, x ∈ s ↔ x ∈ s') :
    IsOpen (t.ite s s') := by
  classical
  simp only [← is_open_iff_continuous_mem, ← Set.Ite] at *
  convert continuous_piecewise (fun x hx => propext (ht x hx)) hs.continuous_on hs'.continuous_on
  ext x
  by_cases' hx : x ∈ t <;> simp [← hx]

theorem IsOpen.ite {s s' t : Set α} (hs : IsOpen s) (hs' : IsOpen s') (ht : s ∩ Frontier t = s' ∩ Frontier t) :
    IsOpen (t.ite s s') :=
  (hs.ite' hs') fun x hx => by
    simpa [← hx] using ext_iff.1 ht x

theorem ite_inter_closure_eq_of_inter_frontier_eq {s s' t : Set α} (ht : s ∩ Frontier t = s' ∩ Frontier t) :
    t.ite s s' ∩ Closure t = s ∩ Closure t := by
  rw [closure_eq_self_union_frontier, inter_union_distrib_left, inter_union_distrib_left, ite_inter_self,
    ite_inter_of_inter_eq _ ht]

theorem ite_inter_closure_compl_eq_of_inter_frontier_eq {s s' t : Set α} (ht : s ∩ Frontier t = s' ∩ Frontier t) :
    t.ite s s' ∩ Closure (tᶜ) = s' ∩ Closure (tᶜ) := by
  rw [← ite_compl, ite_inter_closure_eq_of_inter_frontier_eq]
  rwa [frontier_compl, eq_comm]

theorem continuous_on_piecewise_ite' {s s' t : Set α} {f f' : α → β} [∀ x, Decidable (x ∈ t)]
    (h : ContinuousOn f (s ∩ Closure t)) (h' : ContinuousOn f' (s' ∩ Closure (tᶜ)))
    (H : s ∩ Frontier t = s' ∩ Frontier t) (Heq : EqOn f f' (s ∩ Frontier t)) :
    ContinuousOn (t.piecewise f f') (t.ite s s') := by
  apply ContinuousOn.piecewise
  · rwa [ite_inter_of_inter_eq _ H]
    
  · rwa [ite_inter_closure_eq_of_inter_frontier_eq H]
    
  · rwa [ite_inter_closure_compl_eq_of_inter_frontier_eq H]
    

theorem continuous_on_piecewise_ite {s s' t : Set α} {f f' : α → β} [∀ x, Decidable (x ∈ t)] (h : ContinuousOn f s)
    (h' : ContinuousOn f' s') (H : s ∩ Frontier t = s' ∩ Frontier t) (Heq : EqOn f f' (s ∩ Frontier t)) :
    ContinuousOn (t.piecewise f f') (t.ite s s') :=
  continuous_on_piecewise_ite' (h.mono (inter_subset_left _ _)) (h'.mono (inter_subset_left _ _)) H Heq

theorem frontier_inter_open_inter {s t : Set α} (ht : IsOpen t) : Frontier (s ∩ t) ∩ t = Frontier s ∩ t := by
  simp only [Subtype.preimage_coe_eq_preimage_coe_iff, ←
    ht.is_open_map_subtype_coe.preimage_frontier_eq_frontier_preimage continuous_subtype_coe, ←
    Subtype.preimage_coe_inter_self]

theorem continuous_on_fst {s : Set (α × β)} : ContinuousOn Prod.fst s :=
  continuous_fst.ContinuousOn

theorem continuous_within_at_fst {s : Set (α × β)} {p : α × β} : ContinuousWithinAt Prod.fst s p :=
  continuous_fst.ContinuousWithinAt

theorem ContinuousOn.fst {f : α → β × γ} {s : Set α} (hf : ContinuousOn f s) : ContinuousOn (fun x => (f x).1) s :=
  continuous_fst.comp_continuous_on hf

theorem ContinuousWithinAt.fst {f : α → β × γ} {s : Set α} {a : α} (h : ContinuousWithinAt f s a) :
    ContinuousWithinAt (fun x => (f x).fst) s a :=
  continuous_at_fst.comp_continuous_within_at h

theorem continuous_on_snd {s : Set (α × β)} : ContinuousOn Prod.snd s :=
  continuous_snd.ContinuousOn

theorem continuous_within_at_snd {s : Set (α × β)} {p : α × β} : ContinuousWithinAt Prod.snd s p :=
  continuous_snd.ContinuousWithinAt

theorem ContinuousOn.snd {f : α → β × γ} {s : Set α} (hf : ContinuousOn f s) : ContinuousOn (fun x => (f x).2) s :=
  continuous_snd.comp_continuous_on hf

theorem ContinuousWithinAt.snd {f : α → β × γ} {s : Set α} {a : α} (h : ContinuousWithinAt f s a) :
    ContinuousWithinAt (fun x => (f x).snd) s a :=
  continuous_at_snd.comp_continuous_within_at h

theorem continuous_within_at_prod_iff {f : α → β × γ} {s : Set α} {x : α} :
    ContinuousWithinAt f s x ↔ ContinuousWithinAt (Prod.fst ∘ f) s x ∧ ContinuousWithinAt (Prod.snd ∘ f) s x :=
  ⟨fun h => ⟨h.fst, h.snd⟩, by
    rintro ⟨h1, h2⟩
    convert h1.prod h2
    ext
    rfl
    rfl⟩

