/-
Copyright (c) 2020 Jean Lo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean Lo
-/
import Mathbin.Dynamics.Flow

/-!
# ω-limits

For a function `ϕ : τ → α → β` where `β` is a topological space, we
define the ω-limit under `ϕ` of a set `s` in `α` with respect to
filter `f` on `τ`: an element `y : β` is in the ω-limit of `s` if the
forward images of `s` intersect arbitrarily small neighbourhoods of
`y` frequently "in the direction of `f`".

In practice `ϕ` is often a continuous monoid-act, but the definition
requires only that `ϕ` has a coercion to the appropriate function
type. In the case where `τ` is `ℕ` or `ℝ` and `f` is `at_top`, we
recover the usual definition of the ω-limit set as the set of all `y`
such that there exist sequences `(tₙ)`, `(xₙ)` such that `ϕ tₙ xₙ ⟶ y`
as `n ⟶ ∞`.

## Notations

The `omega_limit` locale provides the localised notation `ω` for
`omega_limit`, as well as `ω⁺` and `ω⁻` for `omega_limit at_top` and
`omega_limit at_bot` respectively for when the acting monoid is
endowed with an order.
-/


open Set Function Filter

open TopologicalSpace

/-!
### Definition and notation
-/


section OmegaLimit

variable {τ : Type _} {α : Type _} {β : Type _} {ι : Type _}

/-- The ω-limit of a set `s` under `ϕ` with respect to a filter `f` is
    ⋂ u ∈ f, cl (ϕ u s). -/
def OmegaLimit [TopologicalSpace β] (f : Filter τ) (ϕ : τ → α → β) (s : Set α) : Set β :=
  ⋂ u ∈ f, Closure (Image2 ϕ u s)

-- mathport name: «exprω»
localized [OmegaLimit] notation "ω" => OmegaLimit

-- mathport name: «exprω⁺»
localized [OmegaLimit] notation "ω⁺" => OmegaLimit Filter.atTop

-- mathport name: «exprω⁻»
localized [OmegaLimit] notation "ω⁻" => OmegaLimit Filter.atBot

variable [TopologicalSpace β]

variable (f : Filter τ) (ϕ : τ → α → β) (s s₁ s₂ : Set α)

/-!
### Elementary properties
-/


theorem omega_limit_def : ω f ϕ s = ⋂ u ∈ f, Closure (Image2 ϕ u s) :=
  rfl

theorem omega_limit_subset_of_tendsto {m : τ → τ} {f₁ f₂ : Filter τ} (hf : Tendsto m f₁ f₂) :
    ω f₁ (fun t x => ϕ (m t) x) s ⊆ ω f₂ ϕ s := by
  refine' Inter₂_mono' fun u hu => ⟨m ⁻¹' u, tendsto_def.mp hf _ hu, _⟩
  rw [← image2_image_left]
  exact closure_mono (image2_subset (image_preimage_subset _ _) subset.rfl)

theorem omega_limit_mono_left {f₁ f₂ : Filter τ} (hf : f₁ ≤ f₂) : ω f₁ ϕ s ⊆ ω f₂ ϕ s :=
  omega_limit_subset_of_tendsto ϕ s (tendsto_id'.2 hf)

theorem omega_limit_mono_right {s₁ s₂ : Set α} (hs : s₁ ⊆ s₂) : ω f ϕ s₁ ⊆ ω f ϕ s₂ :=
  Inter₂_mono fun u hu => closure_mono (image2_subset Subset.rfl hs)

theorem is_closed_omega_limit : IsClosed (ω f ϕ s) :=
  is_closed_Inter fun u => is_closed_Inter fun hu => is_closed_closure

theorem maps_to_omega_limit' {α' β' : Type _} [TopologicalSpace β'] {f : Filter τ} {ϕ : τ → α → β} {ϕ' : τ → α' → β'}
    {ga : α → α'} {s' : Set α'} (hs : MapsTo ga s s') {gb : β → β'} (hg : ∀ᶠ t in f, EqOn (gb ∘ ϕ t) (ϕ' t ∘ ga) s)
    (hgc : Continuous gb) : MapsTo gb (ω f ϕ s) (ω f ϕ' s') := by
  simp only [← omega_limit_def, ← mem_Inter, ← maps_to]
  intro y hy u hu
  refine' map_mem_closure hgc (hy _ (inter_mem hu hg)) (forall_image2_iff.2 fun t ht x hx => _)
  calc gb (ϕ t x) = ϕ' t (ga x) := ht.2 hx _ ∈ image2 ϕ' u s' := mem_image2_of_mem ht.1 (hs hx)

theorem maps_to_omega_limit {α' β' : Type _} [TopologicalSpace β'] {f : Filter τ} {ϕ : τ → α → β} {ϕ' : τ → α' → β'}
    {ga : α → α'} {s' : Set α'} (hs : MapsTo ga s s') {gb : β → β'} (hg : ∀ t x, gb (ϕ t x) = ϕ' t (ga x))
    (hgc : Continuous gb) : MapsTo gb (ω f ϕ s) (ω f ϕ' s') :=
  maps_to_omega_limit' _ hs (eventually_of_forall fun t x hx => hg t x) hgc

theorem omega_limit_image_eq {α' : Type _} (ϕ : τ → α' → β) (f : Filter τ) (g : α → α') :
    ω f ϕ (g '' s) = ω f (fun t x => ϕ t (g x)) s := by
  simp only [← OmegaLimit, ← image2_image_right]

theorem omega_limit_preimage_subset {α' : Type _} (ϕ : τ → α' → β) (s : Set α') (f : Filter τ) (g : α → α') :
    ω f (fun t x => ϕ t (g x)) (g ⁻¹' s) ⊆ ω f ϕ s :=
  maps_to_omega_limit _ (maps_to_preimage _ _) (fun t x => rfl) continuous_id

/-!
### Equivalent definitions of the omega limit

The next few lemmas are various versions of the property
characterising ω-limits:
-/


/-- An element `y` is in the ω-limit set of `s` w.r.t. `f` if the
    preimages of an arbitrary neighbourhood of `y` frequently
    (w.r.t. `f`) intersects of `s`. -/
theorem mem_omega_limit_iff_frequently (y : β) : y ∈ ω f ϕ s ↔ ∀, ∀ n ∈ 𝓝 y, ∀, ∃ᶠ t in f, (s ∩ ϕ t ⁻¹' n).Nonempty :=
  by
  simp_rw [frequently_iff, omega_limit_def, mem_Inter, mem_closure_iff_nhds]
  constructor
  · intro h _ hn _ hu
    rcases h _ hu _ hn with ⟨_, _, _, _, ht, hx, hϕtx⟩
    exact
      ⟨_, ht, _, hx, by
        rwa [mem_preimage, hϕtx]⟩
    
  · intro h _ hu _ hn
    rcases h _ hn hu with ⟨_, ht, _, hx, hϕtx⟩
    exact ⟨_, hϕtx, _, _, ht, hx, rfl⟩
    

/-- An element `y` is in the ω-limit set of `s` w.r.t. `f` if the
    forward images of `s` frequently (w.r.t. `f`) intersect arbitrary
    neighbourhoods of `y`. -/
theorem mem_omega_limit_iff_frequently₂ (y : β) : y ∈ ω f ϕ s ↔ ∀, ∀ n ∈ 𝓝 y, ∀, ∃ᶠ t in f, (ϕ t '' s ∩ n).Nonempty :=
  by
  simp_rw [mem_omega_limit_iff_frequently, image_inter_nonempty_iff]

/-- An element `y` is in the ω-limit of `x` w.r.t. `f` if the forward
    images of `x` frequently (w.r.t. `f`) falls within an arbitrary
    neighbourhood of `y`. -/
theorem mem_omega_limit_singleton_iff_map_cluster_point (x : α) (y : β) :
    y ∈ ω f ϕ {x} ↔ MapClusterPt y f fun t => ϕ t x := by
  simp_rw [mem_omega_limit_iff_frequently, map_cluster_pt_iff, singleton_inter_nonempty, mem_preimage]

/-!
### Set operations and omega limits
-/


theorem omega_limit_inter : ω f ϕ (s₁ ∩ s₂) ⊆ ω f ϕ s₁ ∩ ω f ϕ s₂ :=
  subset_inter (omega_limit_mono_right _ _ (inter_subset_left _ _))
    (omega_limit_mono_right _ _ (inter_subset_right _ _))

theorem omega_limit_Inter (p : ι → Set α) : ω f ϕ (⋂ i, p i) ⊆ ⋂ i, ω f ϕ (p i) :=
  subset_Inter fun i => omega_limit_mono_right _ _ (Inter_subset _ _)

theorem omega_limit_union : ω f ϕ (s₁ ∪ s₂) = ω f ϕ s₁ ∪ ω f ϕ s₂ := by
  ext y
  constructor
  · simp only [← mem_union, ← mem_omega_limit_iff_frequently, ← union_inter_distrib_right, ← union_nonempty, ←
      frequently_or_distrib]
    contrapose!
    simp only [← not_frequently, ← not_nonempty_iff_eq_empty, subset_empty_iff]
    rintro ⟨⟨n₁, hn₁, h₁⟩, ⟨n₂, hn₂, h₂⟩⟩
    refine' ⟨n₁ ∩ n₂, inter_mem hn₁ hn₂, h₁.mono fun t => _, h₂.mono fun t => _⟩
    exacts[subset.trans <| inter_subset_inter_right _ <| preimage_mono <| inter_subset_left _ _,
      subset.trans <| inter_subset_inter_right _ <| preimage_mono <| inter_subset_right _ _]
    
  · rintro (hy | hy)
    exacts[omega_limit_mono_right _ _ (subset_union_left _ _) hy,
      omega_limit_mono_right _ _ (subset_union_right _ _) hy]
    

theorem omega_limit_Union (p : ι → Set α) : (⋃ i, ω f ϕ (p i)) ⊆ ω f ϕ (⋃ i, p i) := by
  rw [Union_subset_iff]
  exact fun i => omega_limit_mono_right _ _ (subset_Union _ _)

/-!
Different expressions for omega limits, useful for rewrites. In
particular, one may restrict the intersection to sets in `f` which are
subsets of some set `v` also in `f`.
-/


theorem omega_limit_eq_Inter : ω f ϕ s = ⋂ u : ↥f.Sets, Closure (Image2 ϕ u s) :=
  bInter_eq_Inter _ _

theorem omega_limit_eq_bInter_inter {v : Set τ} (hv : v ∈ f) : ω f ϕ s = ⋂ u ∈ f, Closure (Image2 ϕ (u ∩ v) s) :=
  Subset.antisymm (Inter₂_mono' fun u hu => ⟨u ∩ v, inter_mem hu hv, Subset.rfl⟩)
    (Inter₂_mono fun u hu => closure_mono <| image2_subset (inter_subset_left _ _) Subset.rfl)

theorem omega_limit_eq_Inter_inter {v : Set τ} (hv : v ∈ f) : ω f ϕ s = ⋂ u : ↥f.Sets, Closure (Image2 ϕ (u ∩ v) s) :=
  by
  rw [omega_limit_eq_bInter_inter _ _ _ hv]
  apply bInter_eq_Inter

theorem omega_limit_subset_closure_fw_image {u : Set τ} (hu : u ∈ f) : ω f ϕ s ⊆ Closure (Image2 ϕ u s) := by
  rw [omega_limit_eq_Inter]
  intro _ hx
  rw [mem_Inter] at hx
  exact hx ⟨u, hu⟩

/-!
### `ω-limits and compactness
-/


/-- A set is eventually carried into any open neighbourhood of its ω-limit:
if `c` is a compact set such that `closure {ϕ t x | t ∈ v, x ∈ s} ⊆ c` for some `v ∈ f`
and `n` is an open neighbourhood of `ω f ϕ s`, then for some `u ∈ f` we have
`closure {ϕ t x | t ∈ u, x ∈ s} ⊆ n`. -/
theorem eventually_closure_subset_of_is_compact_absorbing_of_is_open_of_omega_limit_subset' {c : Set β}
    (hc₁ : IsCompact c) (hc₂ : ∃ v ∈ f, Closure (Image2 ϕ v s) ⊆ c) {n : Set β} (hn₁ : IsOpen n) (hn₂ : ω f ϕ s ⊆ n) :
    ∃ u ∈ f, Closure (Image2 ϕ u s) ⊆ n := by
  rcases hc₂ with ⟨v, hv₁, hv₂⟩
  let k := Closure (image2 ϕ v s)
  have hk : IsCompact (k \ n) := IsCompact.diff (compact_of_is_closed_subset hc₁ is_closed_closure hv₂) hn₁
  let j := fun u => Closure (image2 ϕ (u ∩ v) s)ᶜ
  have hj₁ : ∀, ∀ u ∈ f, ∀, IsOpen (j u) := fun _ _ => is_open_compl_iff.mpr is_closed_closure
  have hj₂ : k \ n ⊆ ⋃ u ∈ f, j u := by
    have : (⋃ u ∈ f, j u) = ⋃ u : ↥f.sets, j u := bUnion_eq_Union _ _
    rw [this, diff_subset_comm, diff_Union]
    rw [omega_limit_eq_Inter_inter _ _ _ hv₁] at hn₂
    simp_rw [diff_compl]
    rw [← inter_Inter]
    exact subset.trans (inter_subset_right _ _) hn₂
  rcases hk.elim_finite_subcover_image hj₁ hj₂ with ⟨g, hg₁ : ∀, ∀ u ∈ g, ∀, u ∈ f, hg₂, hg₃⟩
  let w := (⋂ u ∈ g, u) ∩ v
  have hw₂ : w ∈ f := by
    simpa [*]
  have hw₃ : k \ n ⊆ Closure (image2 ϕ w s)ᶜ :=
    calc
      k \ n ⊆ ⋃ u ∈ g, j u := hg₃
      _ ⊆ Closure (image2 ϕ w s)ᶜ := by
        simp only [← Union_subset_iff, ← compl_subset_compl]
        intro u hu
        mono* using ← w
        exact Inter_subset_of_subset u (Inter_subset_of_subset hu subset.rfl)
      
  have hw₄ : kᶜ ⊆ Closure (image2 ϕ w s)ᶜ := by
    rw [compl_subset_compl]
    calc Closure (image2 ϕ w s) ⊆ _ := closure_mono (image2_subset (inter_subset_right _ _) subset.rfl)
  have hnc : nᶜ ⊆ k \ n ∪ kᶜ := by
    rw [union_comm, ← inter_subset, diff_eq, inter_comm]
  have hw : Closure (image2 ϕ w s) ⊆ n := compl_subset_compl.mp (subset.trans hnc (union_subset hw₃ hw₄))
  exact ⟨_, hw₂, hw⟩

/-- A set is eventually carried into any open neighbourhood of its ω-limit:
if `c` is a compact set such that `closure {ϕ t x | t ∈ v, x ∈ s} ⊆ c` for some `v ∈ f`
and `n` is an open neighbourhood of `ω f ϕ s`, then for some `u ∈ f` we have
`closure {ϕ t x | t ∈ u, x ∈ s} ⊆ n`. -/
theorem eventually_closure_subset_of_is_compact_absorbing_of_is_open_of_omega_limit_subset [T2Space β] {c : Set β}
    (hc₁ : IsCompact c) (hc₂ : ∀ᶠ t in f, MapsTo (ϕ t) s c) {n : Set β} (hn₁ : IsOpen n) (hn₂ : ω f ϕ s ⊆ n) :
    ∃ u ∈ f, Closure (Image2 ϕ u s) ⊆ n :=
  eventually_closure_subset_of_is_compact_absorbing_of_is_open_of_omega_limit_subset' f ϕ _ hc₁
    ⟨_, hc₂, closure_minimal (image2_subset_iff.2 fun t => id) hc₁.IsClosed⟩ hn₁ hn₂

theorem eventually_maps_to_of_is_compact_absorbing_of_is_open_of_omega_limit_subset [T2Space β] {c : Set β}
    (hc₁ : IsCompact c) (hc₂ : ∀ᶠ t in f, MapsTo (ϕ t) s c) {n : Set β} (hn₁ : IsOpen n) (hn₂ : ω f ϕ s ⊆ n) :
    ∀ᶠ t in f, MapsTo (ϕ t) s n := by
  rcases eventually_closure_subset_of_is_compact_absorbing_of_is_open_of_omega_limit_subset f ϕ s hc₁ hc₂ hn₁ hn₂ with
    ⟨u, hu_mem, hu⟩
  refine' mem_of_superset hu_mem fun t ht x hx => _
  exact hu (subset_closure <| mem_image2_of_mem ht hx)

theorem eventually_closure_subset_of_is_open_of_omega_limit_subset [CompactSpace β] {v : Set β} (hv₁ : IsOpen v)
    (hv₂ : ω f ϕ s ⊆ v) : ∃ u ∈ f, Closure (Image2 ϕ u s) ⊆ v :=
  eventually_closure_subset_of_is_compact_absorbing_of_is_open_of_omega_limit_subset' _ _ _ compact_univ
    ⟨Univ, univ_mem, subset_univ _⟩ hv₁ hv₂

theorem eventually_maps_to_of_is_open_of_omega_limit_subset [CompactSpace β] {v : Set β} (hv₁ : IsOpen v)
    (hv₂ : ω f ϕ s ⊆ v) : ∀ᶠ t in f, MapsTo (ϕ t) s v := by
  rcases eventually_closure_subset_of_is_open_of_omega_limit_subset f ϕ s hv₁ hv₂ with ⟨u, hu_mem, hu⟩
  refine' mem_of_superset hu_mem fun t ht x hx => _
  exact hu (subset_closure <| mem_image2_of_mem ht hx)

/-- The ω-limit of a nonempty set w.r.t. a nontrivial filter is nonempty. -/
theorem nonempty_omega_limit_of_is_compact_absorbing [NeBot f] {c : Set β} (hc₁ : IsCompact c)
    (hc₂ : ∃ v ∈ f, Closure (Image2 ϕ v s) ⊆ c) (hs : s.Nonempty) : (ω f ϕ s).Nonempty := by
  rcases hc₂ with ⟨v, hv₁, hv₂⟩
  rw [omega_limit_eq_Inter_inter _ _ _ hv₁]
  apply IsCompact.nonempty_Inter_of_directed_nonempty_compact_closed
  · rintro ⟨u₁, hu₁⟩ ⟨u₂, hu₂⟩
    use ⟨u₁ ∩ u₂, inter_mem hu₁ hu₂⟩
    constructor
    all_goals
      exact
        closure_mono
          (image2_subset
            (inter_subset_inter_left _
              (by
                simp ))
            subset.rfl)
    
  · intro u
    have hn : (image2 ϕ (u ∩ v) s).Nonempty := nonempty.image2 (nonempty_of_mem (inter_mem u.prop hv₁)) hs
    exact hn.mono subset_closure
    
  · intro
    apply compact_of_is_closed_subset hc₁ is_closed_closure
    calc _ ⊆ Closure (image2 ϕ v s) := closure_mono (image2_subset (inter_subset_right _ _) subset.rfl)_ ⊆ c := hv₂
    
  · exact fun _ => is_closed_closure
    

theorem nonempty_omega_limit [CompactSpace β] [NeBot f] (hs : s.Nonempty) : (ω f ϕ s).Nonempty :=
  nonempty_omega_limit_of_is_compact_absorbing _ _ _ compact_univ ⟨Univ, univ_mem, subset_univ _⟩ hs

end OmegaLimit

/-!
### ω-limits of Flows by a Monoid
-/


namespace Flow

variable {τ : Type _} [TopologicalSpace τ] [AddMonoidₓ τ] [HasContinuousAdd τ] {α : Type _} [TopologicalSpace α]
  (f : Filter τ) (ϕ : Flow τ α) (s : Set α)

open OmegaLimit

theorem is_invariant_omega_limit (hf : ∀ t, Tendsto ((· + ·) t) f f) : IsInvariant ϕ (ω f ϕ s) := by
  refine' fun t => maps_to.mono_right _ (omega_limit_subset_of_tendsto ϕ s (hf t))
  exact
    maps_to_omega_limit _ (maps_to_id _) (fun t' x => (ϕ.map_add _ _ _).symm) (continuous_const.flow ϕ continuous_id)

theorem omega_limit_image_subset (t : τ) (ht : Tendsto (· + t) f f) : ω f ϕ (ϕ t '' s) ⊆ ω f ϕ s := by
  simp only [← omega_limit_image_eq, map_add]
  exact omega_limit_subset_of_tendsto ϕ s ht

end Flow

/-!
### ω-limits of Flows by a Group
-/


namespace Flow

variable {τ : Type _} [TopologicalSpace τ] [AddCommGroupₓ τ] [TopologicalAddGroup τ] {α : Type _} [TopologicalSpace α]
  (f : Filter τ) (ϕ : Flow τ α) (s : Set α)

open OmegaLimit

/-- the ω-limit of a forward image of `s` is the same as the ω-limit of `s`. -/
@[simp]
theorem omega_limit_image_eq (hf : ∀ t, Tendsto (· + t) f f) (t : τ) : ω f ϕ (ϕ t '' s) = ω f ϕ s :=
  Subset.antisymm (omega_limit_image_subset _ _ _ _ (hf t)) <|
    calc
      ω f ϕ s = ω f ϕ (ϕ (-t) '' (ϕ t '' s)) := by
        simp [← image_image, map_add]
      _ ⊆ ω f ϕ (ϕ t '' s) := omega_limit_image_subset _ _ _ _ (hf _)
      

theorem omega_limit_omega_limit (hf : ∀ t, Tendsto ((· + ·) t) f f) : ω f ϕ (ω f ϕ s) ⊆ ω f ϕ s := by
  simp only [← subset_def, ← mem_omega_limit_iff_frequently₂, ← frequently_iff]
  intro _ h
  rintro n hn u hu
  rcases mem_nhds_iff.mp hn with ⟨o, ho₁, ho₂, ho₃⟩
  rcases h o (IsOpen.mem_nhds ho₂ ho₃) hu with ⟨t, ht₁, ht₂⟩
  have l₁ : (ω f ϕ s ∩ o).Nonempty :=
    ht₂.mono (inter_subset_inter_left _ ((is_invariant_iff_image _ _).mp (is_invariant_omega_limit _ _ _ hf) _))
  have l₂ : (Closure (image2 ϕ u s) ∩ o).Nonempty :=
    l₁.mono fun b hb => ⟨omega_limit_subset_closure_fw_image _ _ _ hu hb.1, hb.2⟩
  have l₃ : (o ∩ image2 ϕ u s).Nonempty := by
    rcases l₂ with ⟨b, hb₁, hb₂⟩
    exact mem_closure_iff_nhds.mp hb₁ o (IsOpen.mem_nhds ho₂ hb₂)
  rcases l₃ with ⟨ϕra, ho, ⟨_, _, hr, ha, hϕra⟩⟩
  exact ⟨_, hr, ϕra, ⟨_, ha, hϕra⟩, ho₁ ho⟩

end Flow

