/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import Mathbin.Topology.Bases
import Mathbin.Topology.UniformSpace.Basic

/-!
# Theory of Cauchy filters in uniform spaces. Complete uniform spaces. Totally bounded subsets.
-/


universe u v

open Filter TopologicalSpace Set Classical UniformSpace Function

open Classical uniformity TopologicalSpace Filter

variable {α : Type u} {β : Type v} [UniformSpace α]

/-- A filter `f` is Cauchy if for every entourage `r`, there exists an
  `s ∈ f` such that `s × s ⊆ r`. This is a generalization of Cauchy
  sequences, because if `a : ℕ → α` then the filter of sets containing
  cofinitely many of the `a n` is Cauchy iff `a` is a Cauchy sequence. -/
def Cauchy (f : Filter α) :=
  NeBot f ∧ f ×ᶠ f ≤ 𝓤 α

/-- A set `s` is called *complete*, if any Cauchy filter `f` such that `s ∈ f`
has a limit in `s` (formally, it satisfies `f ≤ 𝓝 x` for some `x ∈ s`). -/
def IsComplete (s : Set α) :=
  ∀ f, Cauchy f → f ≤ 𝓟 s → ∃ x ∈ s, f ≤ 𝓝 x

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (x y «expr ∈ » t)
theorem Filter.HasBasis.cauchy_iff {ι} {p : ι → Prop} {s : ι → Set (α × α)} (h : (𝓤 α).HasBasis p s) {f : Filter α} :
    Cauchy f ↔ NeBot f ∧ ∀ i, p i → ∃ t ∈ f, ∀ (x y) (_ : x ∈ t) (_ : y ∈ t), (x, y) ∈ s i :=
  and_congr Iff.rfl <|
    (f.basis_sets.prod_self.le_basis_iff h).trans <| by
      simp only [← subset_def, ← Prod.forall, ← mem_prod_eq, ← and_imp, ← id, ← ball_mem_comm]

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (x y «expr ∈ » t)
theorem cauchy_iff' {f : Filter α} :
    Cauchy f ↔ NeBot f ∧ ∀, ∀ s ∈ 𝓤 α, ∀, ∃ t ∈ f, ∀ (x y) (_ : x ∈ t) (_ : y ∈ t), (x, y) ∈ s :=
  (𝓤 α).basis_sets.cauchy_iff

theorem cauchy_iff {f : Filter α} : Cauchy f ↔ NeBot f ∧ ∀, ∀ s ∈ 𝓤 α, ∀, ∃ t ∈ f, t ×ˢ t ⊆ s :=
  cauchy_iff'.trans <| by
    simp only [← subset_def, ← Prod.forall, ← mem_prod_eq, ← and_imp, ← id, ← ball_mem_comm]

theorem Cauchy.ultrafilter_of {l : Filter α} (h : Cauchy l) : Cauchy (@Ultrafilter.of _ l h.1 : Filter α) := by
  have := h.1
  have := Ultrafilter.of_le l
  exact ⟨Ultrafilter.ne_bot _, (Filter.prod_mono this this).trans h.2⟩

theorem cauchy_map_iff {l : Filter β} {f : β → α} :
    Cauchy (l.map f) ↔ NeBot l ∧ Tendsto (fun p : β × β => (f p.1, f p.2)) (l ×ᶠ l) (𝓤 α) := by
  rw [Cauchy, map_ne_bot_iff, prod_map_map_eq, tendsto]

theorem cauchy_map_iff' {l : Filter β} [hl : NeBot l] {f : β → α} :
    Cauchy (l.map f) ↔ Tendsto (fun p : β × β => (f p.1, f p.2)) (l ×ᶠ l) (𝓤 α) :=
  cauchy_map_iff.trans <| and_iff_right hl

theorem Cauchy.mono {f g : Filter α} [hg : NeBot g] (h_c : Cauchy f) (h_le : g ≤ f) : Cauchy g :=
  ⟨hg, le_transₓ (Filter.prod_mono h_le h_le) h_c.right⟩

theorem Cauchy.mono' {f g : Filter α} (h_c : Cauchy f) (hg : NeBot g) (h_le : g ≤ f) : Cauchy g :=
  h_c.mono h_le

theorem cauchy_nhds {a : α} : Cauchy (𝓝 a) :=
  ⟨nhds_ne_bot, nhds_prod_eq.symm.trans_le (nhds_le_uniformity a)⟩

theorem cauchy_pure {a : α} : Cauchy (pure a) :=
  cauchy_nhds.mono (pure_le_nhds a)

theorem Filter.Tendsto.cauchy_map {l : Filter β} [NeBot l] {f : β → α} {a : α} (h : Tendsto f l (𝓝 a)) :
    Cauchy (map f l) :=
  cauchy_nhds.mono h

theorem Cauchy.prod [UniformSpace β] {f : Filter α} {g : Filter β} (hf : Cauchy f) (hg : Cauchy g) : Cauchy (f ×ᶠ g) :=
  by
  refine' ⟨hf.1.Prod hg.1, _⟩
  simp only [← uniformity_prod, ← le_inf_iff, map_le_iff_le_comap, prod_map_map_eq]
  exact ⟨le_transₓ (prod_mono tendsto_fst tendsto_fst) hf.2, le_transₓ (prod_mono tendsto_snd tendsto_snd) hg.2⟩

/-- The common part of the proofs of `le_nhds_of_cauchy_adhp` and
`sequentially_complete.le_nhds_of_seq_tendsto_nhds`: if for any entourage `s`
one can choose a set `t ∈ f` of diameter `s` such that it contains a point `y`
with `(x, y) ∈ s`, then `f` converges to `x`. -/
theorem le_nhds_of_cauchy_adhp_aux {f : Filter α} {x : α}
    (adhs : ∀, ∀ s ∈ 𝓤 α, ∀, ∃ t ∈ f, t ×ˢ t ⊆ s ∧ ∃ y, (x, y) ∈ s ∧ y ∈ t) : f ≤ 𝓝 x := by
  -- Consider a neighborhood `s` of `x`
  intro s hs
  -- Take an entourage twice smaller than `s`
  rcases comp_mem_uniformity_sets (mem_nhds_uniformity_iff_right.1 hs) with ⟨U, U_mem, hU⟩
  -- Take a set `t ∈ f`, `t × t ⊆ U`, and a point `y ∈ t` such that `(x, y) ∈ U`
  rcases adhs U U_mem with ⟨t, t_mem, ht, y, hxy, hy⟩
  apply mem_of_superset t_mem
  -- Given a point `z ∈ t`, we have `(x, y) ∈ U` and `(y, z) ∈ t × t ⊆ U`, hence `z ∈ s`
  exact fun z hz => hU (prod_mk_mem_comp_rel hxy (ht <| mk_mem_prod hy hz)) rfl

/-- If `x` is an adherent (cluster) point for a Cauchy filter `f`, then it is a limit point
for `f`. -/
theorem le_nhds_of_cauchy_adhp {f : Filter α} {x : α} (hf : Cauchy f) (adhs : ClusterPt x f) : f ≤ 𝓝 x :=
  le_nhds_of_cauchy_adhp_aux
    (by
      intro s hs
      obtain ⟨t, t_mem, ht⟩ : ∃ t ∈ f, t ×ˢ t ⊆ s
      exact (cauchy_iff.1 hf).2 s hs
      use t, t_mem, ht
      exact forall_mem_nonempty_iff_ne_bot.2 adhs _ (inter_mem_inf (mem_nhds_left x hs) t_mem))

theorem le_nhds_iff_adhp_of_cauchy {f : Filter α} {x : α} (hf : Cauchy f) : f ≤ 𝓝 x ↔ ClusterPt x f :=
  ⟨fun h => ClusterPt.of_le_nhds' h hf.1, le_nhds_of_cauchy_adhp hf⟩

theorem Cauchy.map [UniformSpace β] {f : Filter α} {m : α → β} (hf : Cauchy f) (hm : UniformContinuous m) :
    Cauchy (map m f) :=
  ⟨hf.1.map _,
    calc
      map m f ×ᶠ map m f = map (fun p : α × α => (m p.1, m p.2)) (f ×ᶠ f) := Filter.prod_map_map_eq
      _ ≤ map (fun p : α × α => (m p.1, m p.2)) (𝓤 α) := map_mono hf.right
      _ ≤ 𝓤 β := hm
      ⟩

theorem Cauchy.comap [UniformSpace β] {f : Filter β} {m : α → β} (hf : Cauchy f)
    (hm : comap (fun p : α × α => (m p.1, m p.2)) (𝓤 β) ≤ 𝓤 α) [NeBot (comap m f)] : Cauchy (comap m f) :=
  ⟨‹_›,
    calc
      comap m f ×ᶠ comap m f = comap (fun p : α × α => (m p.1, m p.2)) (f ×ᶠ f) := Filter.prod_comap_comap_eq
      _ ≤ comap (fun p : α × α => (m p.1, m p.2)) (𝓤 β) := comap_mono hf.right
      _ ≤ 𝓤 α := hm
      ⟩

theorem Cauchy.comap' [UniformSpace β] {f : Filter β} {m : α → β} (hf : Cauchy f)
    (hm : comap (fun p : α × α => (m p.1, m p.2)) (𝓤 β) ≤ 𝓤 α) (hb : NeBot (comap m f)) : Cauchy (comap m f) :=
  hf.comap hm

/-- Cauchy sequences. Usually defined on ℕ, but often it is also useful to say that a function
defined on ℝ is Cauchy at +∞ to deduce convergence. Therefore, we define it in a type class that
is general enough to cover both ℕ and ℝ, which are the main motivating examples. -/
def CauchySeq [SemilatticeSup β] (u : β → α) :=
  Cauchy (atTop.map u)

theorem CauchySeq.tendsto_uniformity [SemilatticeSup β] {u : β → α} (h : CauchySeq u) :
    Tendsto (Prod.map u u) atTop (𝓤 α) := by
  simpa only [← tendsto, ← prod_map_map_eq', ← prod_at_top_at_top_eq] using h.right

theorem CauchySeq.nonempty [SemilatticeSup β] {u : β → α} (hu : CauchySeq u) : Nonempty β :=
  @nonempty_of_ne_bot _ _ <| (map_ne_bot_iff _).1 hu.1

theorem CauchySeq.mem_entourage {β : Type _} [SemilatticeSup β] {u : β → α} (h : CauchySeq u) {V : Set (α × α)}
    (hV : V ∈ 𝓤 α) : ∃ k₀, ∀ i j, k₀ ≤ i → k₀ ≤ j → (u i, u j) ∈ V := by
  have := h.nonempty
  have := h.tendsto_uniformity
  rw [← prod_at_top_at_top_eq] at this
  simpa [← maps_to] using at_top_basis.prod_self.tendsto_left_iff.1 this V hV

theorem Filter.Tendsto.cauchy_seq [SemilatticeSup β] [Nonempty β] {f : β → α} {x} (hx : Tendsto f atTop (𝓝 x)) :
    CauchySeq f :=
  hx.cauchy_map

theorem cauchy_seq_const [SemilatticeSup β] [Nonempty β] (x : α) : CauchySeq fun n : β => x :=
  tendsto_const_nhds.CauchySeq

theorem cauchy_seq_iff_tendsto [Nonempty β] [SemilatticeSup β] {u : β → α} :
    CauchySeq u ↔ Tendsto (Prod.map u u) atTop (𝓤 α) :=
  cauchy_map_iff'.trans <| by
    simp only [← prod_at_top_at_top_eq, ← Prod.map_def]

theorem CauchySeq.comp_tendsto {γ} [SemilatticeSup β] [SemilatticeSup γ] [Nonempty γ] {f : β → α} (hf : CauchySeq f)
    {g : γ → β} (hg : Tendsto g atTop atTop) : CauchySeq (f ∘ g) :=
  cauchy_seq_iff_tendsto.2 <| hf.tendsto_uniformity.comp (hg.prod_at_top hg)

theorem CauchySeq.comp_injective [SemilatticeSup β] [NoMaxOrder β] [Nonempty β] {u : ℕ → α} (hu : CauchySeq u)
    {f : β → ℕ} (hf : Injective f) : CauchySeq (u ∘ f) :=
  hu.comp_tendsto <| Nat.cofinite_eq_at_top ▸ hf.tendsto_cofinite.mono_left at_top_le_cofinite

theorem Function.Bijective.cauchy_seq_comp_iff {f : ℕ → ℕ} (hf : Bijective f) (u : ℕ → α) :
    CauchySeq (u ∘ f) ↔ CauchySeq u := by
  refine' ⟨fun H => _, fun H => H.comp_injective hf.injective⟩
  lift f to ℕ ≃ ℕ using hf
  simpa only [← (· ∘ ·), ← f.apply_symm_apply] using H.comp_injective f.symm.injective

theorem CauchySeq.subseq_subseq_mem {V : ℕ → Set (α × α)} (hV : ∀ n, V n ∈ 𝓤 α) {u : ℕ → α} (hu : CauchySeq u)
    {f g : ℕ → ℕ} (hf : Tendsto f atTop atTop) (hg : Tendsto g atTop atTop) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ n, ((u ∘ f ∘ φ) n, (u ∘ g ∘ φ) n) ∈ V n := by
  rw [cauchy_seq_iff_tendsto] at hu
  exact ((hu.comp <| hf.prod_at_top hg).comp tendsto_at_top_diagonal).subseq_mem hV

theorem cauchy_seq_iff' {u : ℕ → α} : CauchySeq u ↔ ∀, ∀ V ∈ 𝓤 α, ∀, ∀ᶠ k in at_top, k ∈ Prod.map u u ⁻¹' V := by
  simpa only [← cauchy_seq_iff_tendsto]

theorem cauchy_seq_iff {u : ℕ → α} : CauchySeq u ↔ ∀, ∀ V ∈ 𝓤 α, ∀, ∃ N, ∀, ∀ k ≥ N, ∀, ∀, ∀ l ≥ N, ∀, (u k, u l) ∈ V :=
  by
  simp [← cauchy_seq_iff', ← Filter.eventually_at_top_prod_self', ← prod_map]

theorem CauchySeq.prod_map {γ δ} [UniformSpace β] [SemilatticeSup γ] [SemilatticeSup δ] {u : γ → α} {v : δ → β}
    (hu : CauchySeq u) (hv : CauchySeq v) : CauchySeq (Prod.map u v) := by
  simpa only [← CauchySeq, ← prod_map_map_eq', ← prod_at_top_at_top_eq] using hu.prod hv

theorem CauchySeq.prod {γ} [UniformSpace β] [SemilatticeSup γ] {u : γ → α} {v : γ → β} (hu : CauchySeq u)
    (hv : CauchySeq v) : CauchySeq fun x => (u x, v x) := by
  have := hu.nonempty
  exact (hu.prod hv).mono (tendsto.prod_mk le_rfl le_rfl)

theorem CauchySeq.eventually_eventually [SemilatticeSup β] {u : β → α} (hu : CauchySeq u) {V : Set (α × α)}
    (hV : V ∈ 𝓤 α) : ∀ᶠ k in at_top, ∀ᶠ l in at_top, (u k, u l) ∈ V :=
  eventually_at_top_curry <| hu.tendsto_uniformity hV

theorem UniformContinuous.comp_cauchy_seq {γ} [UniformSpace β] [SemilatticeSup γ] {f : α → β} (hf : UniformContinuous f)
    {u : γ → α} (hu : CauchySeq u) : CauchySeq (f ∘ u) :=
  hu.map hf

theorem CauchySeq.subseq_mem {V : ℕ → Set (α × α)} (hV : ∀ n, V n ∈ 𝓤 α) {u : ℕ → α} (hu : CauchySeq u) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ n, (u <| φ (n + 1), u <| φ n) ∈ V n := by
  have : ∀ n, ∃ N, ∀, ∀ k ≥ N, ∀, ∀, ∀ l ≥ k, ∀, (u l, u k) ∈ V n := by
    intro n
    rw [cauchy_seq_iff] at hu
    rcases hu _ (hV n) with ⟨N, H⟩
    exact ⟨N, fun k hk l hl => H _ (le_transₓ hk hl) _ hk⟩
  obtain ⟨φ : ℕ → ℕ, φ_extr : StrictMono φ, hφ : ∀ n, ∀, ∀ l ≥ φ n, ∀, (u l, u <| φ n) ∈ V n⟩ :=
    extraction_forall_of_eventually' this
  exact ⟨φ, φ_extr, fun n => hφ _ _ (φ_extr <| lt_add_one n).le⟩

theorem Filter.Tendsto.subseq_mem_entourage {V : ℕ → Set (α × α)} (hV : ∀ n, V n ∈ 𝓤 α) {u : ℕ → α} {a : α}
    (hu : Tendsto u atTop (𝓝 a)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ (u (φ 0), a) ∈ V 0 ∧ ∀ n, (u <| φ (n + 1), u <| φ n) ∈ V (n + 1) := by
  rcases mem_at_top_sets.1 (hu (ball_mem_nhds a (symm_le_uniformity <| hV 0))) with ⟨n, hn⟩
  rcases(hu.comp (tendsto_add_at_top_nat n)).CauchySeq.subseq_mem fun n => hV (n + 1) with ⟨φ, φ_mono, hφV⟩
  exact ⟨fun k => φ k + n, φ_mono.add_const _, hn _ le_add_self, hφV⟩

/-- If a Cauchy sequence has a convergent subsequence, then it converges. -/
theorem tendsto_nhds_of_cauchy_seq_of_subseq [SemilatticeSup β] {u : β → α} (hu : CauchySeq u) {ι : Type _} {f : ι → β}
    {p : Filter ι} [NeBot p] (hf : Tendsto f p atTop) {a : α} (ha : Tendsto (u ∘ f) p (𝓝 a)) : Tendsto u atTop (𝓝 a) :=
  le_nhds_of_cauchy_adhp hu (map_cluster_pt_of_comp hf ha)

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (m n «expr ≥ » N)
-- see Note [nolint_ge]
@[nolint ge_or_gt]
theorem Filter.HasBasis.cauchy_seq_iff {γ} [Nonempty β] [SemilatticeSup β] {u : β → α} {p : γ → Prop}
    {s : γ → Set (α × α)} (h : (𝓤 α).HasBasis p s) :
    CauchySeq u ↔ ∀ i, p i → ∃ N, ∀ (m n) (_ : m ≥ N) (_ : n ≥ N), (u m, u n) ∈ s i := by
  rw [cauchy_seq_iff_tendsto, ← prod_at_top_at_top_eq]
  refine' (at_top_basis.prod_self.tendsto_iff h).trans _
  simp only [← exists_prop, ← true_andₓ, ← maps_to, ← preimage, ← subset_def, ← Prod.forall, ← mem_prod_eq, ←
    mem_set_of_eq, ← mem_Ici, ← and_imp, ← Prod.map, ← ge_iff_le, ← @forall_swap (_ ≤ _) β]

theorem Filter.HasBasis.cauchy_seq_iff' {γ} [Nonempty β] [SemilatticeSup β] {u : β → α} {p : γ → Prop}
    {s : γ → Set (α × α)} (H : (𝓤 α).HasBasis p s) : CauchySeq u ↔ ∀ i, p i → ∃ N, ∀, ∀ n ≥ N, ∀, (u n, u N) ∈ s i := by
  refine' H.cauchy_seq_iff.trans ⟨fun h i hi => _, fun h i hi => _⟩
  · exact (h i hi).imp fun N hN n hn => hN n hn N le_rfl
    
  · rcases comp_symm_of_uniformity (H.mem_of_mem hi) with ⟨t, ht, ht', hts⟩
    rcases H.mem_iff.1 ht with ⟨j, hj, hjt⟩
    refine' (h j hj).imp fun N hN m hm n hn => hts ⟨u N, hjt _, ht' <| hjt _⟩
    · exact hN m hm
      
    · exact hN n hn
      
    

theorem cauchy_seq_of_controlled [SemilatticeSup β] [Nonempty β] (U : β → Set (α × α))
    (hU : ∀, ∀ s ∈ 𝓤 α, ∀, ∃ n, U n ⊆ s) {f : β → α} (hf : ∀ {N m n : β}, N ≤ m → N ≤ n → (f m, f n) ∈ U N) :
    CauchySeq f :=
  cauchy_seq_iff_tendsto.2
    (by
      intro s hs
      rw [mem_map, mem_at_top_sets]
      cases' hU s hs with N hN
      refine' ⟨(N, N), fun mn hmn => _⟩
      cases' mn with m n
      exact hN (hf hmn.1 hmn.2))

theorem is_complete_iff_cluster_pt {s : Set α} : IsComplete s ↔ ∀ l, Cauchy l → l ≤ 𝓟 s → ∃ x ∈ s, ClusterPt x l :=
  forall₃_congrₓ fun l hl hls => exists₂_congrₓ fun x hx => le_nhds_iff_adhp_of_cauchy hl

theorem is_complete_iff_ultrafilter {s : Set α} :
    IsComplete s ↔ ∀ l : Ultrafilter α, Cauchy (l : Filter α) → ↑l ≤ 𝓟 s → ∃ x ∈ s, ↑l ≤ 𝓝 x := by
  refine' ⟨fun h l => h l, fun H => is_complete_iff_cluster_pt.2 fun l hl hls => _⟩
  have := hl.1
  rcases H (Ultrafilter.of l) hl.ultrafilter_of ((Ultrafilter.of_le l).trans hls) with ⟨x, hxs, hxl⟩
  exact ⟨x, hxs, (ClusterPt.of_le_nhds hxl).mono (Ultrafilter.of_le l)⟩

theorem is_complete_iff_ultrafilter' {s : Set α} :
    IsComplete s ↔ ∀ l : Ultrafilter α, Cauchy (l : Filter α) → s ∈ l → ∃ x ∈ s, ↑l ≤ 𝓝 x :=
  is_complete_iff_ultrafilter.trans <| by
    simp only [← le_principal_iff, ← Ultrafilter.mem_coe]

protected theorem IsComplete.union {s t : Set α} (hs : IsComplete s) (ht : IsComplete t) : IsComplete (s ∪ t) := by
  simp only [← is_complete_iff_ultrafilter', ← Ultrafilter.union_mem_iff, ← or_imp_distrib] at *
  exact fun l hl =>
    ⟨fun hsl => (hs l hl hsl).imp fun x hx => ⟨Or.inl hx.fst, hx.snd⟩, fun htl =>
      (ht l hl htl).imp fun x hx => ⟨Or.inr hx.fst, hx.snd⟩⟩

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (t «expr ⊆ » S)
theorem is_complete_Union_separated {ι : Sort _} {s : ι → Set α} (hs : ∀ i, IsComplete (s i)) {U : Set (α × α)}
    (hU : U ∈ 𝓤 α) (hd : ∀ (i j : ι), ∀ x ∈ s i, ∀, ∀ y ∈ s j, ∀, (x, y) ∈ U → i = j) : IsComplete (⋃ i, s i) := by
  set S := ⋃ i, s i
  intro l hl hls
  rw [le_principal_iff] at hls
  cases' cauchy_iff.1 hl with hl_ne hl'
  obtain ⟨t, htS, htl, htU⟩ : ∃ (t : _)(_ : t ⊆ S), t ∈ l ∧ t ×ˢ t ⊆ U := by
    rcases hl' U hU with ⟨t, htl, htU⟩
    exact
      ⟨t ∩ S, inter_subset_right _ _, inter_mem htl hls,
        (Set.prod_mono (inter_subset_left _ _) (inter_subset_left _ _)).trans htU⟩
  obtain ⟨i, hi⟩ : ∃ i, t ⊆ s i := by
    rcases Filter.nonempty_of_mem htl with ⟨x, hx⟩
    rcases mem_Union.1 (htS hx) with ⟨i, hi⟩
    refine' ⟨i, fun y hy => _⟩
    rcases mem_Union.1 (htS hy) with ⟨j, hj⟩
    convert hj
    exact hd i j x hi y hj (htU <| mk_mem_prod hx hy)
  rcases hs i l hl (le_principal_iff.2 <| mem_of_superset htl hi) with ⟨x, hxs, hlx⟩
  exact ⟨x, mem_Union.2 ⟨i, hxs⟩, hlx⟩

/-- A complete space is defined here using uniformities. A uniform space
  is complete if every Cauchy filter converges. -/
class CompleteSpace (α : Type u) [UniformSpace α] : Prop where
  complete : ∀ {f : Filter α}, Cauchy f → ∃ x, f ≤ 𝓝 x

theorem complete_univ {α : Type u} [UniformSpace α] [CompleteSpace α] : IsComplete (Univ : Set α) := by
  intro f hf _
  rcases CompleteSpace.complete hf with ⟨x, hx⟩
  exact ⟨x, mem_univ x, hx⟩

instance CompleteSpace.prod [UniformSpace β] [CompleteSpace α] [CompleteSpace β] :
    CompleteSpace
      (α × β) where complete := fun f hf =>
    let ⟨x1, hx1⟩ := CompleteSpace.complete <| hf.map uniform_continuous_fst
    let ⟨x2, hx2⟩ := CompleteSpace.complete <| hf.map uniform_continuous_snd
    ⟨(x1, x2), by
      rw [nhds_prod_eq, Filter.prod_def] <;>
        exact
          Filter.le_lift fun s hs =>
            Filter.le_lift' fun t ht =>
              have H1 : Prod.fst ⁻¹' s ∈ f.sets := hx1 hs
              have H2 : Prod.snd ⁻¹' t ∈ f.sets := hx2 ht
              Filter.inter_mem H1 H2⟩

/-- If `univ` is complete, the space is a complete space -/
theorem complete_space_of_is_complete_univ (h : IsComplete (Univ : Set α)) : CompleteSpace α :=
  ⟨fun f hf =>
    let ⟨x, _, hx⟩ := h f hf ((@principal_univ α).symm ▸ le_top)
    ⟨x, hx⟩⟩

theorem complete_space_iff_is_complete_univ : CompleteSpace α ↔ IsComplete (Univ : Set α) :=
  ⟨@complete_univ α _, complete_space_of_is_complete_univ⟩

theorem complete_space_iff_ultrafilter :
    CompleteSpace α ↔ ∀ l : Ultrafilter α, Cauchy (l : Filter α) → ∃ x : α, ↑l ≤ 𝓝 x := by
  simp [← complete_space_iff_is_complete_univ, ← is_complete_iff_ultrafilter]

theorem cauchy_iff_exists_le_nhds [CompleteSpace α] {l : Filter α} [NeBot l] : Cauchy l ↔ ∃ x, l ≤ 𝓝 x :=
  ⟨CompleteSpace.complete, fun ⟨x, hx⟩ => cauchy_nhds.mono hx⟩

theorem cauchy_map_iff_exists_tendsto [CompleteSpace α] {l : Filter β} {f : β → α} [NeBot l] :
    Cauchy (l.map f) ↔ ∃ x, Tendsto f l (𝓝 x) :=
  cauchy_iff_exists_le_nhds

/-- A Cauchy sequence in a complete space converges -/
theorem cauchy_seq_tendsto_of_complete [SemilatticeSup β] [CompleteSpace α] {u : β → α} (H : CauchySeq u) :
    ∃ x, Tendsto u atTop (𝓝 x) :=
  CompleteSpace.complete H

/-- If `K` is a complete subset, then any cauchy sequence in `K` converges to a point in `K` -/
theorem cauchy_seq_tendsto_of_is_complete [SemilatticeSup β] {K : Set α} (h₁ : IsComplete K) {u : β → α}
    (h₂ : ∀ n, u n ∈ K) (h₃ : CauchySeq u) : ∃ v ∈ K, Tendsto u atTop (𝓝 v) :=
  h₁ _ h₃ <|
    le_principal_iff.2 <|
      mem_map_iff_exists_image.2
        ⟨Univ, univ_mem, by
          simp only [← image_univ]
          rintro _ ⟨n, rfl⟩
          exact h₂ n⟩

theorem Cauchy.le_nhds_Lim [CompleteSpace α] [Nonempty α] {f : Filter α} (hf : Cauchy f) : f ≤ 𝓝 (lim f) :=
  le_nhds_Lim (CompleteSpace.complete hf)

theorem CauchySeq.tendsto_lim [SemilatticeSup β] [CompleteSpace α] [Nonempty α] {u : β → α} (h : CauchySeq u) :
    Tendsto u atTop (𝓝 <| limₓ atTop u) :=
  h.le_nhds_Lim

theorem IsClosed.is_complete [CompleteSpace α] {s : Set α} (h : IsClosed s) : IsComplete s := fun f cf fs =>
  let ⟨x, hx⟩ := CompleteSpace.complete cf
  ⟨x, is_closed_iff_cluster_pt.mp h x (cf.left.mono (le_inf hx fs)), hx⟩

/-- A set `s` is totally bounded if for every entourage `d` there is a finite
  set of points `t` such that every element of `s` is `d`-near to some element of `t`. -/
def TotallyBounded (s : Set α) : Prop :=
  ∀, ∀ d ∈ 𝓤 α, ∀, ∃ t : Set α, t.Finite ∧ s ⊆ ⋃ y ∈ t, { x | (x, y) ∈ d }

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (t «expr ⊆ » s)
theorem TotallyBounded.exists_subset {s : Set α} (hs : TotallyBounded s) {U : Set (α × α)} (hU : U ∈ 𝓤 α) :
    ∃ (t : _)(_ : t ⊆ s), Set.Finite t ∧ s ⊆ ⋃ y ∈ t, { x | (x, y) ∈ U } := by
  rcases comp_symm_of_uniformity hU with ⟨r, hr, rs, rU⟩
  rcases hs r hr with ⟨k, fk, ks⟩
  let u := k ∩ { y | ∃ x ∈ s, (x, y) ∈ r }
  choose hk f hfs hfr using fun x : u => x.coe_prop
  refine' ⟨range f, _, _, _⟩
  · exact range_subset_iff.2 hfs
    
  · have : Fintype u := (fk.inter_of_left _).Fintype
    exact finite_range f
    
  · intro x xs
    obtain ⟨y, hy, xy⟩ : ∃ y ∈ k, (x, y) ∈ r
    exact mem_Union₂.1 (ks xs)
    rw [bUnion_range, mem_Union]
    set z : ↥u := ⟨y, hy, ⟨x, xs, xy⟩⟩
    exact ⟨z, rU <| mem_comp_rel.2 ⟨y, xy, rs (hfr z)⟩⟩
    

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (t «expr ⊆ » s)
theorem totally_bounded_iff_subset {s : Set α} :
    TotallyBounded s ↔ ∀, ∀ d ∈ 𝓤 α, ∀, ∃ (t : _)(_ : t ⊆ s), Set.Finite t ∧ s ⊆ ⋃ y ∈ t, { x | (x, y) ∈ d } :=
  ⟨fun H d hd => H.exists_subset hd, fun H d hd =>
    let ⟨t, _, ht⟩ := H d hd
    ⟨t, ht⟩⟩

theorem Filter.HasBasis.totally_bounded_iff {ι} {p : ι → Prop} {U : ι → Set (α × α)} (H : (𝓤 α).HasBasis p U)
    {s : Set α} : TotallyBounded s ↔ ∀ i, p i → ∃ t : Set α, Set.Finite t ∧ s ⊆ ⋃ y ∈ t, { x | (x, y) ∈ U i } :=
  H.forall_iff fun U V hUV h => h.imp fun t ht => ⟨ht.1, ht.2.trans <| Union₂_mono fun x hx y hy => hUV hy⟩

theorem totally_bounded_of_forall_symm {s : Set α}
    (h : ∀, ∀ V ∈ 𝓤 α, ∀, SymmetricRel V → ∃ t : Set α, Set.Finite t ∧ s ⊆ ⋃ y ∈ t, Ball y V) : TotallyBounded s :=
  UniformSpace.has_basis_symmetric.totally_bounded_iff.2 fun V hV => by
    simpa only [← ball_eq_of_symmetry hV.2] using h V hV.1 hV.2

theorem totally_bounded_subset {s₁ s₂ : Set α} (hs : s₁ ⊆ s₂) (h : TotallyBounded s₂) : TotallyBounded s₁ := fun d hd =>
  let ⟨t, ht₁, ht₂⟩ := h d hd
  ⟨t, ht₁, Subset.trans hs ht₂⟩

theorem totally_bounded_empty : TotallyBounded (∅ : Set α) := fun d hd => ⟨∅, finite_empty, empty_subset _⟩

/-- The closure of a totally bounded set is totally bounded. -/
theorem TotallyBounded.closure {s : Set α} (h : TotallyBounded s) : TotallyBounded (Closure s) :=
  uniformity_has_basis_closed.totally_bounded_iff.2 fun V hV =>
    let ⟨t, htf, hst⟩ := h V hV.1
    ⟨t, htf,
      closure_minimal hst <| (is_closed_bUnion htf) fun y hy => hV.2.Preimage (continuous_id.prod_mk continuous_const)⟩

/-- The image of a totally bounded set under a uniformly continuous map is totally bounded. -/
theorem TotallyBounded.image [UniformSpace β] {f : α → β} {s : Set α} (hs : TotallyBounded s)
    (hf : UniformContinuous f) : TotallyBounded (f '' s) := fun t ht =>
  have : { p : α × α | (f p.1, f p.2) ∈ t } ∈ 𝓤 α := hf ht
  let ⟨c, hfc, hct⟩ := hs _ this
  ⟨f '' c, hfc.Image f, by
    simp [← image_subset_iff]
    simp [← subset_def] at hct
    intro x hx
    simp
    exact hct x hx⟩

theorem Ultrafilter.cauchy_of_totally_bounded {s : Set α} (f : Ultrafilter α) (hs : TotallyBounded s) (h : ↑f ≤ 𝓟 s) :
    Cauchy (f : Filter α) :=
  ⟨f.ne_bot', fun t ht =>
    let ⟨t', ht'₁, ht'_symm, ht'_t⟩ := comp_symm_of_uniformity ht
    let ⟨i, hi, hs_union⟩ := hs t' ht'₁
    have : (⋃ y ∈ i, { x | (x, y) ∈ t' }) ∈ f := mem_of_superset (le_principal_iff.mp h) hs_union
    have : ∃ y ∈ i, { x | (x, y) ∈ t' } ∈ f := (Ultrafilter.finite_bUnion_mem_iff hi).1 this
    let ⟨y, hy, hif⟩ := this
    have : { x | (x, y) ∈ t' } ×ˢ { x | (x, y) ∈ t' } ⊆ CompRel t' t' :=
      fun ⟨x₁, x₂⟩ ⟨(h₁ : (x₁, y) ∈ t'), (h₂ : (x₂, y) ∈ t')⟩ => ⟨y, h₁, ht'_symm h₂⟩
    mem_of_superset (prod_mem_prod hif hif) (Subset.trans this ht'_t)⟩

theorem totally_bounded_iff_filter {s : Set α} : TotallyBounded s ↔ ∀ f, NeBot f → f ≤ 𝓟 s → ∃ c ≤ f, Cauchy c := by
  constructor
  · intro H f hf hfs
    exact
      ⟨Ultrafilter.of f, Ultrafilter.of_le f,
        (Ultrafilter.of f).cauchy_of_totally_bounded H ((Ultrafilter.of_le f).trans hfs)⟩
    
  · intro H d hd
    contrapose! H with hd_cover
    set f := ⨅ t : Finset α, 𝓟 (s \ ⋃ y ∈ t, { x | (x, y) ∈ d })
    have : ne_bot f := by
      refine' infi_ne_bot_of_directed' (directed_of_sup _) _
      · intro t₁ t₂ h
        exact principal_mono.2 (diff_subset_diff_right <| bUnion_subset_bUnion_left h)
        
      · intro t
        simpa [← nonempty_diff] using hd_cover t t.finite_to_set
        
    have : f ≤ 𝓟 s :=
      infi_le_of_le ∅
        (by
          simp )
    refine' ⟨f, ‹_›, ‹_›, fun c hcf hc => _⟩
    rcases mem_prod_same_iff.1 (hc.2 hd) with ⟨m, hm, hmd⟩
    have : m ∩ s ∈ c := inter_mem hm (le_principal_iff.mp (hcf.trans ‹_›))
    rcases hc.1.nonempty_of_mem this with ⟨y, hym, hys⟩
    set ys := ⋃ y' ∈ ({y} : Finset α), { x | (x, y') ∈ d }
    have : m ⊆ ys := by
      simpa [← ys] using fun x hx => hmd (mk_mem_prod hx hym)
    have : c ≤ 𝓟 (s \ ys) := hcf.trans (infi_le_of_le {y} le_rfl)
    refine' hc.1.Ne (empty_mem_iff_bot.mp _)
    filter_upwards [le_principal_iff.1 this, hm]
    refine' fun x hx hxm => hx.2 _
    simpa [← ys] using hmd (mk_mem_prod hxm hym)
    

theorem totally_bounded_iff_ultrafilter {s : Set α} :
    TotallyBounded s ↔ ∀ f : Ultrafilter α, ↑f ≤ 𝓟 s → Cauchy (f : Filter α) := by
  refine' ⟨fun hs f => f.cauchy_of_totally_bounded hs, fun H => totally_bounded_iff_filter.2 _⟩
  intro f hf hfs
  exact ⟨Ultrafilter.of f, Ultrafilter.of_le f, H _ ((Ultrafilter.of_le f).trans hfs)⟩

theorem compact_iff_totally_bounded_complete {s : Set α} : IsCompact s ↔ TotallyBounded s ∧ IsComplete s :=
  ⟨fun hs =>
    ⟨totally_bounded_iff_ultrafilter.2 fun f hf =>
        let ⟨x, xs, fx⟩ := is_compact_iff_ultrafilter_le_nhds.1 hs f hf
        cauchy_nhds.mono fx,
      fun f fc fs =>
      let ⟨a, as, fa⟩ := @hs f fc.1 fs
      ⟨a, as, le_nhds_of_cauchy_adhp fc fa⟩⟩,
    fun ⟨ht, hc⟩ =>
    is_compact_iff_ultrafilter_le_nhds.2 fun f hf => hc _ (totally_bounded_iff_ultrafilter.1 ht f hf) hf⟩

protected theorem IsCompact.totally_bounded {s : Set α} (h : IsCompact s) : TotallyBounded s :=
  (compact_iff_totally_bounded_complete.1 h).1

protected theorem IsCompact.is_complete {s : Set α} (h : IsCompact s) : IsComplete s :=
  (compact_iff_totally_bounded_complete.1 h).2

-- see Note [lower instance priority]
instance (priority := 100) complete_of_compact {α : Type u} [UniformSpace α] [CompactSpace α] : CompleteSpace α :=
  ⟨fun f hf => by
    simpa using (compact_iff_totally_bounded_complete.1 compact_univ).2 f hf⟩

theorem compact_of_totally_bounded_is_closed [CompleteSpace α] {s : Set α} (ht : TotallyBounded s) (hc : IsClosed s) :
    IsCompact s :=
  (@compact_iff_totally_bounded_complete α _ s).2 ⟨ht, hc.IsComplete⟩

/-!
### Sequentially complete space

In this section we prove that a uniform space is complete provided that it is sequentially complete
(i.e., any Cauchy sequence converges) and its uniformity filter admits a countable generating set.
In particular, this applies to (e)metric spaces, see the files `topology/metric_space/emetric_space`
and `topology/metric_space/basic`.

More precisely, we assume that there is a sequence of entourages `U_n` such that any other
entourage includes one of `U_n`. Then any Cauchy filter `f` generates a decreasing sequence of
sets `s_n ∈ f` such that `s_n × s_n ⊆ U_n`. Choose a sequence `x_n∈s_n`. It is easy to show
that this is a Cauchy sequence. If this sequence converges to some `a`, then `f ≤ 𝓝 a`. -/


namespace SequentiallyComplete

variable {f : Filter α} (hf : Cauchy f) {U : ℕ → Set (α × α)} (U_mem : ∀ n, U n ∈ 𝓤 α)
  (U_le : ∀, ∀ s ∈ 𝓤 α, ∀, ∃ n, U n ⊆ s)

open Set Finset

noncomputable section

/-- An auxiliary sequence of sets approximating a Cauchy filter. -/
def setSeqAux (n : ℕ) : { s : Set α // ∃ _ : s ∈ f, s ×ˢ s ⊆ U n } :=
  indefiniteDescription _ <| (cauchy_iff.1 hf).2 (U n) (U_mem n)

/-- Given a Cauchy filter `f` and a sequence `U` of entourages, `set_seq` provides
an antitone sequence of sets `s n ∈ f` such that `s n ×ˢ s n ⊆ U`. -/
def SetSeq (n : ℕ) : Set α :=
  ⋂ m ∈ Set.Iic n, (setSeqAux hf U_mem m).val

theorem set_seq_mem (n : ℕ) : SetSeq hf U_mem n ∈ f :=
  (bInter_mem (finite_le_nat n)).2 fun m _ => (setSeqAux hf U_mem m).2.fst

theorem set_seq_mono ⦃m n : ℕ⦄ (h : m ≤ n) : SetSeq hf U_mem n ⊆ SetSeq hf U_mem m :=
  bInter_subset_bInter_left fun k hk => le_transₓ hk h

theorem set_seq_sub_aux (n : ℕ) : SetSeq hf U_mem n ⊆ setSeqAux hf U_mem n :=
  bInter_subset_of_mem right_mem_Iic

theorem set_seq_prod_subset {N m n} (hm : N ≤ m) (hn : N ≤ n) : SetSeq hf U_mem m ×ˢ SetSeq hf U_mem n ⊆ U N := by
  intro p hp
  refine' (set_seq_aux hf U_mem N).2.snd ⟨_, _⟩ <;> apply set_seq_sub_aux
  exact set_seq_mono hf U_mem hm hp.1
  exact set_seq_mono hf U_mem hn hp.2

/-- A sequence of points such that `seq n ∈ set_seq n`. Here `set_seq` is an antitone
sequence of sets `set_seq n ∈ f` with diameters controlled by a given sequence
of entourages. -/
def seq (n : ℕ) : α :=
  some <| hf.1.nonempty_of_mem (set_seq_mem hf U_mem n)

theorem seq_mem (n : ℕ) : seq hf U_mem n ∈ SetSeq hf U_mem n :=
  some_spec <| hf.1.nonempty_of_mem (set_seq_mem hf U_mem n)

theorem seq_pair_mem ⦃N m n : ℕ⦄ (hm : N ≤ m) (hn : N ≤ n) : (seq hf U_mem m, seq hf U_mem n) ∈ U N :=
  set_seq_prod_subset hf U_mem hm hn ⟨seq_mem hf U_mem m, seq_mem hf U_mem n⟩

include U_le

theorem seq_is_cauchy_seq : CauchySeq <| seq hf U_mem :=
  cauchy_seq_of_controlled U U_le <| seq_pair_mem hf U_mem

/-- If the sequence `sequentially_complete.seq` converges to `a`, then `f ≤ 𝓝 a`. -/
theorem le_nhds_of_seq_tendsto_nhds ⦃a : α⦄ (ha : Tendsto (seq hf U_mem) atTop (𝓝 a)) : f ≤ 𝓝 a :=
  le_nhds_of_cauchy_adhp_aux
    (by
      intro s hs
      rcases U_le s hs with ⟨m, hm⟩
      rcases tendsto_at_top'.1 ha _ (mem_nhds_left a (U_mem m)) with ⟨n, hn⟩
      refine' ⟨set_seq hf U_mem (max m n), set_seq_mem hf U_mem _, _, seq hf U_mem (max m n), _, seq_mem hf U_mem _⟩
      · have := le_max_leftₓ m n
        exact Set.Subset.trans (set_seq_prod_subset hf U_mem this this) hm
        
      · exact hm (hn _ <| le_max_rightₓ m n)
        )

end SequentiallyComplete

namespace UniformSpace

open SequentiallyComplete

variable [IsCountablyGenerated (𝓤 α)]

/-- A uniform space is complete provided that (a) its uniformity filter has a countable basis;
(b) any sequence satisfying a "controlled" version of the Cauchy condition converges. -/
theorem complete_of_convergent_controlled_sequences (U : ℕ → Set (α × α)) (U_mem : ∀ n, U n ∈ 𝓤 α)
    (HU : ∀ u : ℕ → α, (∀ N m n, N ≤ m → N ≤ n → (u m, u n) ∈ U N) → ∃ a, Tendsto u atTop (𝓝 a)) : CompleteSpace α := by
  obtain ⟨U', U'_mono, hU'⟩ := (𝓤 α).exists_antitone_seq
  have Hmem : ∀ n, U n ∩ U' n ∈ 𝓤 α := fun n => inter_mem (U_mem n) (hU'.2 ⟨n, subset.refl _⟩)
  refine' ⟨fun f hf => (HU (seq hf Hmem) fun N m n hm hn => _).imp <| le_nhds_of_seq_tendsto_nhds _ _ fun s hs => _⟩
  · rcases hU'.1 hs with ⟨N, hN⟩
    exact ⟨N, subset.trans (inter_subset_right _ _) hN⟩
    
  · exact inter_subset_left _ _ (seq_pair_mem hf Hmem hm hn)
    

/-- A sequentially complete uniform space with a countable basis of the uniformity filter is
complete. -/
theorem complete_of_cauchy_seq_tendsto (H' : ∀ u : ℕ → α, CauchySeq u → ∃ a, Tendsto u atTop (𝓝 a)) : CompleteSpace α :=
  let ⟨U', U'_mono, hU'⟩ := (𝓤 α).exists_antitone_seq
  complete_of_convergent_controlled_sequences U' (fun n => hU'.2 ⟨n, Subset.refl _⟩) fun u hu =>
    H' u <| cauchy_seq_of_controlled U' (fun s hs => hU'.1 hs) hu

variable (α)

instance (priority := 100) first_countable_topology : FirstCountableTopology α :=
  ⟨fun a => by
    rw [nhds_eq_comap_uniformity]
    infer_instance⟩

/-- A separable uniform space with countably generated uniformity filter is second countable:
one obtains a countable basis by taking the balls centered at points in a dense subset,
and with rational "radii" from a countable open symmetric antitone basis of `𝓤 α`. We do not
register this as an instance, as there is already an instance going in the other direction
from second countable spaces to separable spaces, and we want to avoid loops. -/
theorem second_countable_of_separable [SeparableSpace α] : SecondCountableTopology α := by
  rcases exists_countable_dense α with ⟨s, hsc, hsd⟩
  obtain
    ⟨t : ℕ → Set (α × α), hto : ∀ i : ℕ, t i ∈ (𝓤 α).Sets ∧ IsOpen (t i) ∧ SymmetricRel (t i), h_basis :
      (𝓤 α).HasAntitoneBasis t⟩ :=
    (@uniformity_has_basis_open_symmetric α _).exists_antitone_subbasis
  choose ht_mem hto hts using hto
  refine' ⟨⟨⋃ x ∈ s, range fun k => ball x (t k), hsc.bUnion fun x hx => countable_range _, _⟩⟩
  refine' (is_topological_basis_of_open_of_nhds _ _).eq_generate_from
  · simp only [← mem_Union₂, ← mem_range]
    rintro _ ⟨x, hxs, k, rfl⟩
    exact is_open_ball x (hto k)
    
  · intro x V hxV hVo
    simp only [← mem_Union₂, ← mem_range, ← exists_prop]
    rcases UniformSpace.mem_nhds_iff.1 (IsOpen.mem_nhds hVo hxV) with ⟨U, hU, hUV⟩
    rcases comp_symm_of_uniformity hU with ⟨U', hU', hsymm, hUU'⟩
    rcases h_basis.to_has_basis.mem_iff.1 hU' with ⟨k, -, hk⟩
    rcases hsd.inter_open_nonempty (ball x <| t k) (is_open_ball x (hto k))
        ⟨x, UniformSpace.mem_ball_self _ (ht_mem k)⟩ with
      ⟨y, hxy, hys⟩
    refine' ⟨_, ⟨y, hys, k, rfl⟩, (hts k).Subset hxy, fun z hz => _⟩
    exact hUV (ball_subset_of_comp_subset (hk hxy) hUU' (hk hz))
    

end UniformSpace

