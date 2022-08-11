/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import Mathbin.Topology.Constructions
import Mathbin.Topology.ContinuousOn

/-!
# Bases of topologies. Countability axioms.

A topological basis on a topological space `t` is a collection of sets,
such that all open sets can be generated as unions of these sets, without the need to take
finite intersections of them. This file introduces a framework for dealing with these collections,
and also what more we can say under certain countability conditions on bases,
which are referred to as first- and second-countable.
We also briefly cover the theory of separable spaces, which are those with a countable, dense
subset. If a space is second-countable, and also has a countably generated uniformity filter
(for example, if `t` is a metric space), it will automatically be separable (and indeed, these
conditions are equivalent in this case).

## Main definitions

* `is_topological_basis s`: The topological space `t` has basis `s`.
* `separable_space α`: The topological space `t` has a countable, dense subset.
* `is_separable s`: The set `s` is contained in the closure of a countable set.
* `first_countable_topology α`: A topology in which `𝓝 x` is countably generated for every `x`.
* `second_countable_topology α`: A topology which has a topological basis which is countable.

## Main results

* `first_countable_topology.tendsto_subseq`: In a first-countable space,
  cluster points are limits of subsequences.
* `second_countable_topology.is_open_Union_countable`: In a second-countable space, the union of
  arbitrarily-many open sets is equal to a sub-union of only countably many of these sets.
* `second_countable_topology.countable_cover_nhds`: Consider `f : α → set α` with the property that
  `f x ∈ 𝓝 x` for all `x`. Then there is some countable set `s` whose image covers the space.

## Implementation Notes
For our applications we are interested that there exists a countable basis, but we do not need the
concrete basis itself. This allows us to declare these type classes as `Prop` to use them as mixins.

### TODO:
More fine grained instances for `first_countable_topology`, `separable_space`, `t2_space`, and more
(see the comment below `subtype.second_countable_topology`.)
-/


open Set Filter Function

open TopologicalSpace Filter

noncomputable section

namespace TopologicalSpace

universe u

variable {α : Type u} [t : TopologicalSpace α]

include t

/-- A topological basis is one that satisfies the necessary conditions so that
  it suffices to take unions of the basis sets to get a topology (without taking
  finite intersections as well). -/
structure IsTopologicalBasis (s : Set (Set α)) : Prop where
  exists_subset_inter : ∀, ∀ t₁ ∈ s, ∀, ∀, ∀ t₂ ∈ s, ∀, ∀, ∀ x ∈ t₁ ∩ t₂, ∀, ∃ t₃ ∈ s, x ∈ t₃ ∧ t₃ ⊆ t₁ ∩ t₂
  sUnion_eq : ⋃₀s = univ
  eq_generate_from : t = generateFrom s

/-- If a family of sets `s` generates the topology, then nonempty intersections of finite
subcollections of `s` form a topological basis. -/
theorem is_topological_basis_of_subbasis {s : Set (Set α)} (hs : t = generateFrom s) :
    IsTopologicalBasis ((fun f => ⋂₀ f) '' { f : Set (Set α) | f.Finite ∧ f ⊆ s ∧ (⋂₀ f).Nonempty }) := by
  refine' ⟨_, _, _⟩
  · rintro _ ⟨t₁, ⟨hft₁, ht₁b, ht₁⟩, rfl⟩ _ ⟨t₂, ⟨hft₂, ht₂b, ht₂⟩, rfl⟩ x h
    have : ⋂₀ (t₁ ∪ t₂) = ⋂₀ t₁ ∩ ⋂₀ t₂ := sInter_union t₁ t₂
    exact ⟨_, ⟨t₁ ∪ t₂, ⟨hft₁.union hft₂, union_subset ht₁b ht₂b, this.symm ▸ ⟨x, h⟩⟩, this⟩, h, subset.rfl⟩
    
  · rw [sUnion_image, Union₂_eq_univ_iff]
    intro x
    have : x ∈ ⋂₀ ∅ := by
      rw [sInter_empty]
      exact mem_univ x
    exact ⟨∅, ⟨finite_empty, empty_subset _, x, this⟩, this⟩
    
  · rw [hs]
    apply le_antisymmₓ <;> apply le_generate_from
    · rintro _ ⟨t, ⟨hft, htb, ht⟩, rfl⟩
      exact @is_open_sInter _ (generate_from s) _ hft fun s hs => generate_open.basic _ <| htb hs
      
    · intro t ht
      rcases t.eq_empty_or_nonempty with (rfl | hne)
      · apply @is_open_empty _ _
        
      rw [← sInter_singleton t] at hne⊢
      exact generate_open.basic _ ⟨{t}, ⟨finite_singleton t, singleton_subset_iff.2 ht, hne⟩, rfl⟩
      
    

/-- If a family of open sets `s` is such that every open neighbourhood contains some
member of `s`, then `s` is a topological basis. -/
theorem is_topological_basis_of_open_of_nhds {s : Set (Set α)} (h_open : ∀, ∀ u ∈ s, ∀, IsOpen u)
    (h_nhds : ∀ (a : α) (u : Set α), a ∈ u → IsOpen u → ∃ v ∈ s, a ∈ v ∧ v ⊆ u) : IsTopologicalBasis s := by
  refine' ⟨fun t₁ ht₁ t₂ ht₂ x hx => h_nhds _ _ hx (IsOpen.inter (h_open _ ht₁) (h_open _ ht₂)), _, _⟩
  · refine' sUnion_eq_univ_iff.2 fun a => _
    rcases h_nhds a univ trivialₓ is_open_univ with ⟨u, h₁, h₂, -⟩
    exact ⟨u, h₁, h₂⟩
    
  · refine' (le_generate_from h_open).antisymm fun u hu => _
    refine' (@is_open_iff_nhds α (generate_from s) u).mpr fun a ha => _
    rcases h_nhds a u ha hu with ⟨v, hvs, hav, hvu⟩
    rw [nhds_generate_from]
    exact infi₂_le_of_le v ⟨hav, hvs⟩ (le_principal_iff.2 hvu)
    

/-- A set `s` is in the neighbourhood of `a` iff there is some basis set `t`, which
contains `a` and is itself contained in `s`. -/
theorem IsTopologicalBasis.mem_nhds_iff {a : α} {s : Set α} {b : Set (Set α)} (hb : IsTopologicalBasis b) :
    s ∈ 𝓝 a ↔ ∃ t ∈ b, a ∈ t ∧ t ⊆ s := by
  change s ∈ (𝓝 a).Sets ↔ ∃ t ∈ b, a ∈ t ∧ t ⊆ s
  rw [hb.eq_generate_from, nhds_generate_from, binfi_sets_eq]
  · simp [← and_assoc, ← And.left_comm]
    
  · exact fun s ⟨hs₁, hs₂⟩ t ⟨ht₁, ht₂⟩ =>
      have : a ∈ s ∩ t := ⟨hs₁, ht₁⟩
      let ⟨u, hu₁, hu₂, hu₃⟩ := hb.1 _ hs₂ _ ht₂ _ this
      ⟨u, ⟨hu₂, hu₁⟩, le_principal_iff.2 (subset.trans hu₃ (inter_subset_left _ _)),
        le_principal_iff.2 (subset.trans hu₃ (inter_subset_right _ _))⟩
    
  · rcases eq_univ_iff_forall.1 hb.sUnion_eq a with ⟨i, h1, h2⟩
    exact ⟨i, h2, h1⟩
    

theorem IsTopologicalBasis.is_open_iff {s : Set α} {b : Set (Set α)} (hb : IsTopologicalBasis b) :
    IsOpen s ↔ ∀, ∀ a ∈ s, ∀, ∃ t ∈ b, a ∈ t ∧ t ⊆ s := by
  simp [← is_open_iff_mem_nhds, ← hb.mem_nhds_iff]

theorem IsTopologicalBasis.nhds_has_basis {b : Set (Set α)} (hb : IsTopologicalBasis b) {a : α} :
    (𝓝 a).HasBasis (fun t : Set α => t ∈ b ∧ a ∈ t) fun t => t :=
  ⟨fun s =>
    hb.mem_nhds_iff.trans <| by
      simp only [← exists_prop, ← and_assoc]⟩

protected theorem IsTopologicalBasis.is_open {s : Set α} {b : Set (Set α)} (hb : IsTopologicalBasis b) (hs : s ∈ b) :
    IsOpen s := by
  rw [hb.eq_generate_from]
  exact generate_open.basic s hs

protected theorem IsTopologicalBasis.mem_nhds {a : α} {s : Set α} {b : Set (Set α)} (hb : IsTopologicalBasis b)
    (hs : s ∈ b) (ha : a ∈ s) : s ∈ 𝓝 a :=
  (hb.IsOpen hs).mem_nhds ha

theorem IsTopologicalBasis.exists_subset_of_mem_open {b : Set (Set α)} (hb : IsTopologicalBasis b) {a : α} {u : Set α}
    (au : a ∈ u) (ou : IsOpen u) : ∃ v ∈ b, a ∈ v ∧ v ⊆ u :=
  hb.mem_nhds_iff.1 <| IsOpen.mem_nhds ou au

/-- Any open set is the union of the basis sets contained in it. -/
theorem IsTopologicalBasis.open_eq_sUnion' {B : Set (Set α)} (hB : IsTopologicalBasis B) {u : Set α} (ou : IsOpen u) :
    u = ⋃₀{ s ∈ B | s ⊆ u } :=
  ext fun a =>
    ⟨fun ha =>
      let ⟨b, hb, ab, bu⟩ := hB.exists_subset_of_mem_open ha ou
      ⟨b, ⟨hb, bu⟩, ab⟩,
      fun ⟨b, ⟨hb, bu⟩, ab⟩ => bu ab⟩

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (S «expr ⊆ » B)
theorem IsTopologicalBasis.open_eq_sUnion {B : Set (Set α)} (hB : IsTopologicalBasis B) {u : Set α} (ou : IsOpen u) :
    ∃ (S : _)(_ : S ⊆ B), u = ⋃₀S :=
  ⟨{ s ∈ B | s ⊆ u }, fun s h => h.1, hB.open_eq_sUnion' ou⟩

theorem IsTopologicalBasis.open_eq_Union {B : Set (Set α)} (hB : IsTopologicalBasis B) {u : Set α} (ou : IsOpen u) :
    ∃ (β : Type u)(f : β → Set α), (u = ⋃ i, f i) ∧ ∀ i, f i ∈ B :=
  ⟨↥({ s ∈ B | s ⊆ u }), coe, by
    rw [← sUnion_eq_Union]
    apply hB.open_eq_sUnion' ou, fun s => And.left s.2⟩

/-- A point `a` is in the closure of `s` iff all basis sets containing `a` intersect `s`. -/
theorem IsTopologicalBasis.mem_closure_iff {b : Set (Set α)} (hb : IsTopologicalBasis b) {s : Set α} {a : α} :
    a ∈ Closure s ↔ ∀, ∀ o ∈ b, ∀, a ∈ o → (o ∩ s).Nonempty :=
  (mem_closure_iff_nhds_basis' hb.nhds_has_basis).trans <| by
    simp only [← and_imp]

/-- A set is dense iff it has non-trivial intersection with all basis sets. -/
theorem IsTopologicalBasis.dense_iff {b : Set (Set α)} (hb : IsTopologicalBasis b) {s : Set α} :
    Dense s ↔ ∀, ∀ o ∈ b, ∀, Set.Nonempty o → (o ∩ s).Nonempty := by
  simp only [← Dense, ← hb.mem_closure_iff]
  exact ⟨fun h o hb ⟨a, ha⟩ => h a o hb ha, fun h a o hb ha => h o hb ⟨a, ha⟩⟩

theorem IsTopologicalBasis.is_open_map_iff {β} [TopologicalSpace β] {B : Set (Set α)} (hB : IsTopologicalBasis B)
    {f : α → β} : IsOpenMap f ↔ ∀, ∀ s ∈ B, ∀, IsOpen (f '' s) := by
  refine' ⟨fun H o ho => H _ (hB.is_open ho), fun hf o ho => _⟩
  rw [hB.open_eq_sUnion' ho, sUnion_eq_Union, image_Union]
  exact is_open_Union fun s => hf s s.2.1

theorem IsTopologicalBasis.exists_nonempty_subset {B : Set (Set α)} (hb : IsTopologicalBasis B) {u : Set α}
    (hu : u.Nonempty) (ou : IsOpen u) : ∃ v ∈ B, Set.Nonempty v ∧ v ⊆ u := by
  cases' hu with x hx
  rw [hb.open_eq_sUnion' ou, mem_sUnion] at hx
  rcases hx with ⟨v, hv, hxv⟩
  exact ⟨v, hv.1, ⟨x, hxv⟩, hv.2⟩

theorem is_topological_basis_opens : IsTopologicalBasis { U : Set α | IsOpen U } :=
  is_topological_basis_of_open_of_nhds
    (by
      tauto)
    (by
      tauto)

protected theorem IsTopologicalBasis.prod {β} [TopologicalSpace β] {B₁ : Set (Set α)} {B₂ : Set (Set β)}
    (h₁ : IsTopologicalBasis B₁) (h₂ : IsTopologicalBasis B₂) : IsTopologicalBasis (Image2 (· ×ˢ ·) B₁ B₂) := by
  refine' is_topological_basis_of_open_of_nhds _ _
  · rintro _ ⟨u₁, u₂, hu₁, hu₂, rfl⟩
    exact (h₁.is_open hu₁).Prod (h₂.is_open hu₂)
    
  · rintro ⟨a, b⟩ u hu uo
    rcases(h₁.nhds_has_basis.prod_nhds h₂.nhds_has_basis).mem_iff.1 (IsOpen.mem_nhds uo hu) with
      ⟨⟨s, t⟩, ⟨⟨hs, ha⟩, ht, hb⟩, hu⟩
    exact ⟨s ×ˢ t, mem_image2_of_mem hs ht, ⟨ha, hb⟩, hu⟩
    

protected theorem IsTopologicalBasis.inducing {β} [TopologicalSpace β] {f : α → β} {T : Set (Set β)} (hf : Inducing f)
    (h : IsTopologicalBasis T) : IsTopologicalBasis (Image (Preimage f) T) := by
  refine' is_topological_basis_of_open_of_nhds _ _
  · rintro _ ⟨V, hV, rfl⟩
    rwa [hf.is_open_iff]
    refine' ⟨V, h.is_open hV, rfl⟩
    
  · intro a U ha hU
    rw [hf.is_open_iff] at hU
    obtain ⟨V, hV, rfl⟩ := hU
    obtain ⟨S, hS, rfl⟩ := h.open_eq_sUnion hV
    obtain ⟨W, hW, ha⟩ := ha
    refine' ⟨f ⁻¹' W, ⟨_, hS hW, rfl⟩, ha, Set.preimage_mono <| Set.subset_sUnion_of_mem hW⟩
    

theorem is_topological_basis_of_cover {ι} {U : ι → Set α} (Uo : ∀ i, IsOpen (U i)) (Uc : (⋃ i, U i) = univ)
    {b : ∀ i, Set (Set (U i))} (hb : ∀ i, IsTopologicalBasis (b i)) :
    IsTopologicalBasis (⋃ i : ι, Image (coe : U i → α) '' b i) := by
  refine' is_topological_basis_of_open_of_nhds (fun u hu => _) _
  · simp only [← mem_Union, ← mem_image] at hu
    rcases hu with ⟨i, s, sb, rfl⟩
    exact (Uo i).is_open_map_subtype_coe _ ((hb i).IsOpen sb)
    
  · intro a u ha uo
    rcases Union_eq_univ_iff.1 Uc a with ⟨i, hi⟩
    lift a to ↥(U i) using hi
    rcases(hb i).exists_subset_of_mem_open ha (uo.preimage continuous_subtype_coe) with ⟨v, hvb, hav, hvu⟩
    exact ⟨coe '' v, mem_Union.2 ⟨i, mem_image_of_mem _ hvb⟩, mem_image_of_mem _ hav, image_subset_iff.2 hvu⟩
    

protected theorem IsTopologicalBasis.continuous {β : Type _} [TopologicalSpace β] {B : Set (Set β)}
    (hB : IsTopologicalBasis B) (f : α → β) (hf : ∀, ∀ s ∈ B, ∀, IsOpen (f ⁻¹' s)) : Continuous f := by
  rw [hB.eq_generate_from]
  exact continuous_generated_from hf

variable (α)

/-- A separable space is one with a countable dense subset, available through
`topological_space.exists_countable_dense`. If `α` is also known to be nonempty, then
`topological_space.dense_seq` provides a sequence `ℕ → α` with dense range, see
`topological_space.dense_range_dense_seq`.

If `α` is a uniform space with countably generated uniformity filter (e.g., an `emetric_space`),
then this condition is equivalent to `topological_space.second_countable_topology α`. In this case
the latter should be used as a typeclass argument in theorems because Lean can automatically deduce
`separable_space` from `second_countable_topology` but it can't deduce `second_countable_topology`
and `emetric_space`. -/
class SeparableSpace : Prop where
  exists_countable_dense : ∃ s : Set α, s.Countable ∧ Dense s

theorem exists_countable_dense [SeparableSpace α] : ∃ s : Set α, s.Countable ∧ Dense s :=
  separable_space.exists_countable_dense

/-- A nonempty separable space admits a sequence with dense range. Instead of running `cases` on the
conclusion of this lemma, you might want to use `topological_space.dense_seq` and
`topological_space.dense_range_dense_seq`.

If `α` might be empty, then `exists_countable_dense` is the main way to use separability of `α`. -/
theorem exists_dense_seq [SeparableSpace α] [Nonempty α] : ∃ u : ℕ → α, DenseRange u := by
  obtain ⟨s : Set α, hs, s_dense⟩ := exists_countable_dense α
  cases' set.countable_iff_exists_surjective.mp hs with u hu
  exact ⟨u, s_dense.mono hu⟩

/-- A dense sequence in a non-empty separable topological space.

If `α` might be empty, then `exists_countable_dense` is the main way to use separability of `α`. -/
def denseSeq [SeparableSpace α] [Nonempty α] : ℕ → α :=
  Classical.some (exists_dense_seq α)

/-- The sequence `dense_seq α` has dense range. -/
@[simp]
theorem dense_range_dense_seq [SeparableSpace α] [Nonempty α] : DenseRange (denseSeq α) :=
  Classical.some_spec (exists_dense_seq α)

variable {α}

instance (priority := 100) Encodable.to_separable_space [Encodable α] :
    SeparableSpace α where exists_countable_dense := ⟨Set.Univ, Set.countable_encodable Set.Univ, dense_univ⟩

theorem separable_space_of_dense_range {ι : Type _} [Encodable ι] (u : ι → α) (hu : DenseRange u) : SeparableSpace α :=
  ⟨⟨Range u, countable_range u, hu⟩⟩

/-- In a separable space, a family of nonempty disjoint open sets is countable. -/
theorem _root_.set.pairwise_disjoint.countable_of_is_open [SeparableSpace α] {ι : Type _} {s : ι → Set α} {a : Set ι}
    (h : a.PairwiseDisjoint s) (ha : ∀, ∀ i ∈ a, ∀, IsOpen (s i)) (h'a : ∀, ∀ i ∈ a, ∀, (s i).Nonempty) : a.Countable :=
  by
  rcases exists_countable_dense α with ⟨u, ⟨u_encodable⟩, u_dense⟩
  have : ∀ i : a, ∃ y, y ∈ s i ∩ u := fun i => dense_iff_inter_open.1 u_dense (s i) (ha i i.2) (h'a i i.2)
  choose f hfs hfu using this
  lift f to a → u using hfu
  have f_inj : injective f := by
    refine' injective_iff_pairwise_ne.mpr ((h.subtype _ _).mono fun i j hij hfij => hij ⟨hfs i, _⟩)
    simp only [← congr_arg coe hfij, ← hfs j]
  exact ⟨@Encodable.ofInj _ _ u_encodable f f_inj⟩

/-- In a separable space, a family of disjoint sets with nonempty interiors is countable. -/
theorem _root_.set.pairwise_disjoint.countable_of_nonempty_interior [SeparableSpace α] {ι : Type _} {s : ι → Set α}
    {a : Set ι} (h : a.PairwiseDisjoint s) (ha : ∀, ∀ i ∈ a, ∀, (Interior (s i)).Nonempty) : a.Countable :=
  (h.mono fun i => interior_subset).countable_of_is_open (fun i hi => is_open_interior) ha

/-- A set `s` in a topological space is separable if it is contained in the closure of a
countable set `c`. Beware that this definition does not require that `c` is contained in `s` (to
express the latter, use `separable_space s` or `is_separable (univ : set s))`. In metric spaces,
the two definitions are equivalent, see `topological_space.is_separable.separable_space`. -/
def IsSeparable (s : Set α) :=
  ∃ c : Set α, c.Countable ∧ s ⊆ Closure c

theorem IsSeparable.mono {s u : Set α} (hs : IsSeparable s) (hu : u ⊆ s) : IsSeparable u := by
  rcases hs with ⟨c, c_count, hs⟩
  exact ⟨c, c_count, hu.trans hs⟩

theorem IsSeparable.union {s u : Set α} (hs : IsSeparable s) (hu : IsSeparable u) : IsSeparable (s ∪ u) := by
  rcases hs with ⟨cs, cs_count, hcs⟩
  rcases hu with ⟨cu, cu_count, hcu⟩
  refine' ⟨cs ∪ cu, cs_count.union cu_count, _⟩
  exact
    union_subset (hcs.trans (closure_mono (subset_union_left _ _))) (hcu.trans (closure_mono (subset_union_right _ _)))

theorem IsSeparable.closure {s : Set α} (hs : IsSeparable s) : IsSeparable (Closure s) := by
  rcases hs with ⟨c, c_count, hs⟩
  exact
    ⟨c, c_count, by
      simpa using closure_mono hs⟩

theorem is_separable_Union {ι : Type _} [Encodable ι] {s : ι → Set α} (hs : ∀ i, IsSeparable (s i)) :
    IsSeparable (⋃ i, s i) := by
  choose c hc h'c using hs
  refine' ⟨⋃ i, c i, countable_Union hc, Union_subset_iff.2 fun i => _⟩
  exact (h'c i).trans (closure_mono (subset_Union _ i))

theorem _root_.set.countable.is_separable {s : Set α} (hs : s.Countable) : IsSeparable s :=
  ⟨s, hs, subset_closure⟩

theorem _root_.set.finite.is_separable {s : Set α} (hs : s.Finite) : IsSeparable s :=
  hs.Countable.IsSeparable

theorem is_separable_univ_iff : IsSeparable (Univ : Set α) ↔ SeparableSpace α := by
  constructor
  · rintro ⟨c, c_count, hc⟩
    refine'
      ⟨⟨c, c_count, by
          rwa [dense_iff_closure_eq, ← univ_subset_iff]⟩⟩
    
  · intro h
    rcases exists_countable_dense α with ⟨c, c_count, hc⟩
    exact
      ⟨c, c_count, by
        rwa [univ_subset_iff, ← dense_iff_closure_eq]⟩
    

theorem is_separable_of_separable_space [h : SeparableSpace α] (s : Set α) : IsSeparable s :=
  IsSeparable.mono (is_separable_univ_iff.2 h) (subset_univ _)

theorem IsSeparable.image {β : Type _} [TopologicalSpace β] {s : Set α} (hs : IsSeparable s) {f : α → β}
    (hf : Continuous f) : IsSeparable (f '' s) := by
  rcases hs with ⟨c, c_count, hc⟩
  refine' ⟨f '' c, c_count.image _, _⟩
  rw [image_subset_iff]
  exact hc.trans (closure_subset_preimage_closure_image hf)

theorem is_separable_of_separable_space_subtype (s : Set α) [SeparableSpace s] : IsSeparable s := by
  have : is_separable ((coe : s → α) '' (univ : Set s)) :=
    (is_separable_of_separable_space _).Image continuous_subtype_coe
  simpa only [← image_univ, ← Subtype.range_coe_subtype]

end TopologicalSpace

open TopologicalSpace

theorem is_topological_basis_pi {ι : Type _} {X : ι → Type _} [∀ i, TopologicalSpace (X i)] {T : ∀ i, Set (Set (X i))}
    (cond : ∀ i, IsTopologicalBasis (T i)) :
    IsTopologicalBasis
      { S : Set (∀ i, X i) | ∃ (U : ∀ i, Set (X i))(F : Finset ι), (∀ i, i ∈ F → U i ∈ T i) ∧ S = (F : Set ι).pi U } :=
  by
  refine' is_topological_basis_of_open_of_nhds _ _
  · rintro _ ⟨U, F, h1, rfl⟩
    apply is_open_set_pi F.finite_to_set
    intro i hi
    exact (cond i).IsOpen (h1 i hi)
    
  · intro a U ha hU
    obtain ⟨I, t, hta, htU⟩ : ∃ (I : Finset ι)(t : ∀ i : ι, Set (X i)), (∀ i, t i ∈ 𝓝 (a i)) ∧ Set.Pi (↑I) t ⊆ U := by
      rw [← Filter.mem_pi', ← nhds_pi]
      exact hU.mem_nhds ha
    have : ∀ i, ∃ V ∈ T i, a i ∈ V ∧ V ⊆ t i := fun i => (cond i).mem_nhds_iff.1 (hta i)
    choose V hVT haV hVt
    exact ⟨_, ⟨V, I, fun i hi => hVT i, rfl⟩, fun i hi => haV i, (pi_mono fun i hi => hVt i).trans htU⟩
    

theorem is_topological_basis_infi {β : Type _} {ι : Type _} {X : ι → Type _} [t : ∀ i, TopologicalSpace (X i)]
    {T : ∀ i, Set (Set (X i))} (cond : ∀ i, IsTopologicalBasis (T i)) (f : ∀ i, β → X i) :
    @IsTopologicalBasis β (⨅ i, induced (f i) (t i))
      { S | ∃ (U : ∀ i, Set (X i))(F : Finset ι), (∀ i, i ∈ F → U i ∈ T i) ∧ S = ⋂ (i) (hi : i ∈ F), f i ⁻¹' U i } :=
  by
  convert (is_topological_basis_pi cond).Inducing (inducing_infi_to_pi _)
  ext V
  constructor
  · rintro ⟨U, F, h1, h2⟩
    have : (F : Set ι).pi U = ⋂ (i : ι) (hi : i ∈ F), (fun z : ∀ j, X j => z i) ⁻¹' U i := by
      ext
      simp
    refine' ⟨(F : Set ι).pi U, ⟨U, F, h1, rfl⟩, _⟩
    rw [this, h2, Set.preimage_Inter]
    congr 1
    ext1
    rw [Set.preimage_Inter]
    rfl
    
  · rintro ⟨U, ⟨U, F, h1, rfl⟩, h⟩
    refine' ⟨U, F, h1, _⟩
    have : (F : Set ι).pi U = ⋂ (i : ι) (hi : i ∈ F), (fun z : ∀ j, X j => z i) ⁻¹' U i := by
      ext
      simp
    rw [← h, this, Set.preimage_Inter]
    congr 1
    ext1
    rw [Set.preimage_Inter]
    rfl
    

theorem is_topological_basis_singletons (α : Type _) [TopologicalSpace α] [DiscreteTopology α] :
    IsTopologicalBasis { s | ∃ x : α, (s : Set α) = {x} } :=
  (is_topological_basis_of_open_of_nhds fun u hu => is_open_discrete _) fun x u hx u_open =>
    ⟨{x}, ⟨x, rfl⟩, mem_singleton x, singleton_subset_iff.2 hx⟩

/-- If `α` is a separable space and `f : α → β` is a continuous map with dense range, then `β` is
a separable space as well. E.g., the completion of a separable uniform space is separable. -/
protected theorem DenseRange.separable_space {α β : Type _} [TopologicalSpace α] [SeparableSpace α] [TopologicalSpace β]
    {f : α → β} (h : DenseRange f) (h' : Continuous f) : SeparableSpace β :=
  let ⟨s, s_cnt, s_dense⟩ := exists_countable_dense α
  ⟨⟨f '' s, Countable.image s_cnt f, h.dense_image h' s_dense⟩⟩

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (t «expr ⊆ » s)
theorem Dense.exists_countable_dense_subset {α : Type _} [TopologicalSpace α] {s : Set α} [SeparableSpace s]
    (hs : Dense s) : ∃ (t : _)(_ : t ⊆ s), t.Countable ∧ Dense t :=
  let ⟨t, htc, htd⟩ := exists_countable_dense s
  ⟨coe '' t, image_subset_iff.2 fun x _ => mem_preimage.2 <| Subtype.coe_prop _, htc.Image coe,
    hs.dense_range_coe.dense_image continuous_subtype_val htd⟩

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (t «expr ⊆ » s)
/-- Let `s` be a dense set in a topological space `α` with partial order structure. If `s` is a
separable space (e.g., if `α` has a second countable topology), then there exists a countable
dense subset `t ⊆ s` such that `t` contains bottom/top element of `α` when they exist and belong
to `s`. For a dense subset containing neither bot nor top elements, see
`dense.exists_countable_dense_subset_no_bot_top`. -/
theorem Dense.exists_countable_dense_subset_bot_top {α : Type _} [TopologicalSpace α] [PartialOrderₓ α] {s : Set α}
    [SeparableSpace s] (hs : Dense s) :
    ∃ (t : _)(_ : t ⊆ s), t.Countable ∧ Dense t ∧ (∀ x, IsBot x → x ∈ s → x ∈ t) ∧ ∀ x, IsTop x → x ∈ s → x ∈ t := by
  rcases hs.exists_countable_dense_subset with ⟨t, hts, htc, htd⟩
  refine' ⟨(t ∪ ({ x | IsBot x } ∪ { x | IsTop x })) ∩ s, _, _, _, _, _⟩
  exacts[inter_subset_right _ _,
    (htc.union ((countable_is_bot α).union (countable_is_top α))).mono (inter_subset_left _ _),
    htd.mono (subset_inter (subset_union_left _ _) hts), fun x hx hxs => ⟨Or.inr <| Or.inl hx, hxs⟩, fun x hx hxs =>
    ⟨Or.inr <| Or.inr hx, hxs⟩]

instance separable_space_univ {α : Type _} [TopologicalSpace α] [SeparableSpace α] : SeparableSpace (Univ : Set α) :=
  (Equivₓ.Set.univ α).symm.Surjective.DenseRange.SeparableSpace (continuous_subtype_mk _ continuous_id)

/-- If `α` is a separable topological space with a partial order, then there exists a countable
dense set `s : set α` that contains those of both bottom and top elements of `α` that actually
exist. For a dense set containing neither bot nor top elements, see
`exists_countable_dense_no_bot_top`. -/
theorem exists_countable_dense_bot_top (α : Type _) [TopologicalSpace α] [SeparableSpace α] [PartialOrderₓ α] :
    ∃ s : Set α, s.Countable ∧ Dense s ∧ (∀ x, IsBot x → x ∈ s) ∧ ∀ x, IsTop x → x ∈ s := by
  simpa using dense_univ.exists_countable_dense_subset_bot_top

namespace TopologicalSpace

universe u

variable (α : Type u) [t : TopologicalSpace α]

include t

/-- A first-countable space is one in which every point has a
  countable neighborhood basis. -/
class FirstCountableTopology : Prop where
  nhds_generated_countable : ∀ a : α, (𝓝 a).IsCountablyGenerated

attribute [instance] first_countable_topology.nhds_generated_countable

namespace FirstCountableTopology

variable {α}

/-- In a first-countable space, a cluster point `x` of a sequence
is the limit of some subsequence. -/
theorem tendsto_subseq [FirstCountableTopology α] {u : ℕ → α} {x : α} (hx : MapClusterPt x atTop u) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ Tendsto (u ∘ ψ) atTop (𝓝 x) :=
  subseq_tendsto_of_ne_bot hx

end FirstCountableTopology

variable {α}

instance is_countably_generated_nhds_within (x : α) [IsCountablyGenerated (𝓝 x)] (s : Set α) :
    IsCountablyGenerated (𝓝[s] x) :=
  Inf.is_countably_generated _ _

variable (α)

-- ./././Mathport/Syntax/Translate/Basic.lean:1440:30: infer kinds are unsupported in Lean 4: #[`is_open_generated_countable] []
/-- A second-countable space is one with a countable basis. -/
class SecondCountableTopology : Prop where
  is_open_generated_countable : ∃ b : Set (Set α), b.Countable ∧ t = TopologicalSpace.generateFrom b

variable {α}

protected theorem IsTopologicalBasis.second_countable_topology {b : Set (Set α)} (hb : IsTopologicalBasis b)
    (hc : b.Countable) : SecondCountableTopology α :=
  ⟨⟨b, hc, hb.eq_generate_from⟩⟩

variable (α)

theorem exists_countable_basis [SecondCountableTopology α] :
    ∃ b : Set (Set α), b.Countable ∧ ∅ ∉ b ∧ IsTopologicalBasis b :=
  let ⟨b, hb₁, hb₂⟩ := SecondCountableTopology.is_open_generated_countable α
  let b' := (fun s => ⋂₀ s) '' { s : Set (Set α) | s.Finite ∧ s ⊆ b ∧ (⋂₀ s).Nonempty }
  ⟨b',
    ((countable_set_of_finite_subset hb₁).mono
          (by
            simp only [and_assoc]
            apply inter_subset_left)).Image
      _,
    fun ⟨s, ⟨_, _, hn⟩, hp⟩ => absurd hn (not_nonempty_iff_eq_empty.2 hp), is_topological_basis_of_subbasis hb₂⟩

/-- A countable topological basis of `α`. -/
def CountableBasis [SecondCountableTopology α] : Set (Set α) :=
  (exists_countable_basis α).some

theorem countable_countable_basis [SecondCountableTopology α] : (CountableBasis α).Countable :=
  (exists_countable_basis α).some_spec.1

instance encodableCountableBasis [SecondCountableTopology α] : Encodable (CountableBasis α) :=
  (countable_countable_basis α).toEncodable

theorem empty_nmem_countable_basis [SecondCountableTopology α] : ∅ ∉ CountableBasis α :=
  (exists_countable_basis α).some_spec.2.1

theorem is_basis_countable_basis [SecondCountableTopology α] : IsTopologicalBasis (CountableBasis α) :=
  (exists_countable_basis α).some_spec.2.2

theorem eq_generate_from_countable_basis [SecondCountableTopology α] :
    ‹TopologicalSpace α› = generateFrom (CountableBasis α) :=
  (is_basis_countable_basis α).eq_generate_from

variable {α}

theorem is_open_of_mem_countable_basis [SecondCountableTopology α] {s : Set α} (hs : s ∈ CountableBasis α) : IsOpen s :=
  (is_basis_countable_basis α).IsOpen hs

theorem nonempty_of_mem_countable_basis [SecondCountableTopology α] {s : Set α} (hs : s ∈ CountableBasis α) :
    s.Nonempty :=
  ne_empty_iff_nonempty.1 <| ne_of_mem_of_not_mem hs <| empty_nmem_countable_basis α

variable (α)

-- see Note [lower instance priority]
instance (priority := 100) SecondCountableTopology.to_first_countable_topology [SecondCountableTopology α] :
    FirstCountableTopology α :=
  ⟨fun x =>
    has_countable_basis.is_countably_generated <|
      ⟨(is_basis_countable_basis α).nhds_has_basis, (countable_countable_basis α).mono <| inter_subset_left _ _⟩⟩

/-- If `β` is a second-countable space, then its induced topology
via `f` on `α` is also second-countable. -/
theorem second_countable_topology_induced (β) [t : TopologicalSpace β] [SecondCountableTopology β] (f : α → β) :
    @SecondCountableTopology α (t.induced f) := by
  rcases second_countable_topology.is_open_generated_countable β with ⟨b, hb, eq⟩
  refine' { is_open_generated_countable := ⟨preimage f '' b, hb.image _, _⟩ }
  rw [Eq, induced_generate_from_eq]

instance Subtype.second_countable_topology (s : Set α) [SecondCountableTopology α] : SecondCountableTopology s :=
  second_countable_topology_induced s α coe

-- TODO: more fine grained instances for first_countable_topology, separable_space, t2_space, ...
instance {β : Type _} [TopologicalSpace β] [SecondCountableTopology α] [SecondCountableTopology β] :
    SecondCountableTopology (α × β) :=
  ((is_basis_countable_basis α).Prod (is_basis_countable_basis β)).SecondCountableTopology <|
    (countable_countable_basis α).Image2 (countable_countable_basis β) _

instance second_countable_topology_encodable {ι : Type _} {π : ι → Type _} [Encodable ι]
    [t : ∀ a, TopologicalSpace (π a)] [∀ a, SecondCountableTopology (π a)] : SecondCountableTopology (∀ a, π a) := by
  have : t = fun a => generate_from (countable_basis (π a)) :=
    funext fun a => (is_basis_countable_basis (π a)).eq_generate_from
  rw [this, pi_generate_from_eq]
  constructor
  refine' ⟨_, _, rfl⟩
  have :
    Set.Countable
      { T : Set (∀ i, π i) |
        ∃ (I : Finset ι)(s : ∀ i : I, Set (π i)),
          (∀ i, s i ∈ countable_basis (π i)) ∧ T = { f | ∀ i : I, f i ∈ s i } } :=
    by
    simp only [← set_of_exists, exists_prop]
    refine' countable_Union fun I => countable.bUnion _ fun _ _ => countable_singleton _
    change Set.Countable { s : ∀ i : I, Set (π i) | ∀ i, s i ∈ countable_basis (π i) }
    exact countable_pi fun i => countable_countable_basis _
  convert this using 1
  ext1 T
  constructor
  · rintro ⟨s, I, hs, rfl⟩
    refine' ⟨I, fun i => s i, fun i => hs i i.2, _⟩
    simp only [← Set.Pi, ← SetCoe.forall']
    rfl
    
  · rintro ⟨I, s, hs, rfl⟩
    rcases@Subtype.surjective_restrict ι (fun i => Set (π i)) _ (fun i => i ∈ I) s with ⟨s, rfl⟩
    exact ⟨s, I, fun i hi => hs ⟨i, hi⟩, Set.ext fun f => Subtype.forall⟩
    

instance second_countable_topology_fintype {ι : Type _} {π : ι → Type _} [Fintype ι] [t : ∀ a, TopologicalSpace (π a)]
    [∀ a, SecondCountableTopology (π a)] : SecondCountableTopology (∀ a, π a) := by
  let this := Fintype.toEncodable ι
  exact TopologicalSpace.second_countable_topology_encodable

-- see Note [lower instance priority]
instance (priority := 100) SecondCountableTopology.to_separable_space [SecondCountableTopology α] : SeparableSpace α :=
  by
  choose p hp using fun s : countable_basis α => nonempty_of_mem_countable_basis s.2
  exact
    ⟨⟨range p, countable_range _,
        (is_basis_countable_basis α).dense_iff.2 fun o ho _ => ⟨p ⟨o, ho⟩, hp _, mem_range_self _⟩⟩⟩

variable {α}

/-- A countable open cover induces a second-countable topology if all open covers
are themselves second countable. -/
theorem second_countable_topology_of_countable_cover {ι} [Encodable ι] {U : ι → Set α}
    [∀ i, SecondCountableTopology (U i)] (Uo : ∀ i, IsOpen (U i)) (hc : (⋃ i, U i) = univ) :
    SecondCountableTopology α := by
  have : is_topological_basis (⋃ i, image (coe : U i → α) '' countable_basis (U i)) :=
    is_topological_basis_of_cover Uo hc fun i => is_basis_countable_basis (U i)
  exact this.second_countable_topology (countable_Union fun i => (countable_countable_basis _).Image _)

/-- In a second-countable space, an open set, given as a union of open sets,
is equal to the union of countably many of those sets. -/
theorem is_open_Union_countable [SecondCountableTopology α] {ι} (s : ι → Set α) (H : ∀ i, IsOpen (s i)) :
    ∃ T : Set ι, T.Countable ∧ (⋃ i ∈ T, s i) = ⋃ i, s i := by
  let B := { b ∈ countable_basis α | ∃ i, b ⊆ s i }
  choose f hf using fun b : B => b.2.2
  have : Encodable B := ((countable_countable_basis α).mono (sep_subset _ _)).toEncodable
  refine' ⟨_, countable_range f, (Union₂_subset_Union _ _).antisymm (sUnion_subset _)⟩
  rintro _ ⟨i, rfl⟩ x xs
  rcases(is_basis_countable_basis α).exists_subset_of_mem_open xs (H _) with ⟨b, hb, xb, bs⟩
  exact ⟨_, ⟨_, rfl⟩, _, ⟨⟨⟨_, hb, _, bs⟩, rfl⟩, rfl⟩, hf _ xb⟩

theorem is_open_sUnion_countable [SecondCountableTopology α] (S : Set (Set α)) (H : ∀, ∀ s ∈ S, ∀, IsOpen s) :
    ∃ T : Set (Set α), T.Countable ∧ T ⊆ S ∧ ⋃₀T = ⋃₀S :=
  let ⟨T, cT, hT⟩ := is_open_Union_countable (fun s : S => s.1) fun s => H s.1 s.2
  ⟨Subtype.val '' T, cT.Image _, image_subset_iff.2 fun ⟨x, xs⟩ xt => xs, by
    rwa [sUnion_image, sUnion_eq_Union]⟩

/-- In a topological space with second countable topology, if `f` is a function that sends each
point `x` to a neighborhood of `x`, then for some countable set `s`, the neighborhoods `f x`,
`x ∈ s`, cover the whole space. -/
theorem countable_cover_nhds [SecondCountableTopology α] {f : α → Set α} (hf : ∀ x, f x ∈ 𝓝 x) :
    ∃ s : Set α, s.Countable ∧ (⋃ x ∈ s, f x) = univ := by
  rcases is_open_Union_countable (fun x => Interior (f x)) fun x => is_open_interior with ⟨s, hsc, hsU⟩
  suffices : (⋃ x ∈ s, Interior (f x)) = univ
  exact ⟨s, hsc, flip eq_univ_of_subset this <| Union₂_mono fun _ _ => interior_subset⟩
  simp only [← hsU, ← eq_univ_iff_forall, ← mem_Union]
  exact fun x => ⟨x, mem_interior_iff_mem_nhds.2 (hf x)⟩

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (t «expr ⊆ » s)
theorem countable_cover_nhds_within [SecondCountableTopology α] {f : α → Set α} {s : Set α}
    (hf : ∀, ∀ x ∈ s, ∀, f x ∈ 𝓝[s] x) : ∃ (t : _)(_ : t ⊆ s), t.Countable ∧ s ⊆ ⋃ x ∈ t, f x := by
  have : ∀ x : s, coe ⁻¹' f x ∈ 𝓝 x := fun x => preimage_coe_mem_nhds_subtype.2 (hf x x.2)
  rcases countable_cover_nhds this with ⟨t, htc, htU⟩
  refine' ⟨coe '' t, Subtype.coe_image_subset _ _, htc.image _, fun x hx => _⟩
  simp only [← bUnion_image, ← eq_univ_iff_forall, preimage_Union, ← mem_preimage] at htU⊢
  exact htU ⟨x, hx⟩

section Sigma

variable {ι : Type _} {E : ι → Type _} [∀ i, TopologicalSpace (E i)]

omit t

/-- In a disjoint union space `Σ i, E i`, one can form a topological basis by taking the union of
topological bases on each of the parts of the space. -/
theorem IsTopologicalBasis.sigma {s : ∀ i : ι, Set (Set (E i))} (hs : ∀ i, IsTopologicalBasis (s i)) :
    IsTopologicalBasis (⋃ i : ι, (fun u => (Sigma.mk i '' u : Set (Σi, E i))) '' s i) := by
  apply is_topological_basis_of_open_of_nhds
  · intro u hu
    obtain ⟨i, t, ts, rfl⟩ : ∃ (i : ι)(t : Set (E i)), t ∈ s i ∧ Sigma.mk i '' t = u := by
      simpa only [← mem_Union, ← mem_image] using hu
    exact is_open_map_sigma_mk _ ((hs i).IsOpen ts)
    
  · rintro ⟨i, x⟩ u hxu u_open
    have hx : x ∈ Sigma.mk i ⁻¹' u := hxu
    obtain ⟨v, vs, xv, hv⟩ : ∃ (v : Set (E i))(H : v ∈ s i), x ∈ v ∧ v ⊆ Sigma.mk i ⁻¹' u :=
      (hs i).exists_subset_of_mem_open hx (is_open_sigma_iff.1 u_open i)
    exact ⟨Sigma.mk i '' v, mem_Union.2 ⟨i, mem_image_of_mem _ vs⟩, mem_image_of_mem _ xv, image_subset_iff.2 hv⟩
    

/-- A countable disjoint union of second countable spaces is second countable. -/
instance [Encodable ι] [∀ i, SecondCountableTopology (E i)] : SecondCountableTopology (Σi, E i) := by
  let b := ⋃ i : ι, (fun u => (Sigma.mk i '' u : Set (Σi, E i))) '' countable_basis (E i)
  have A : is_topological_basis b := is_topological_basis.sigma fun i => is_basis_countable_basis _
  have B : b.countable := countable_Union fun i => countable.image (countable_countable_basis _) _
  exact A.second_countable_topology B

end Sigma

section Sum

omit t

variable {β : Type _} [TopologicalSpace α] [TopologicalSpace β]

/-- In a sum space `α ⊕ β`, one can form a topological basis by taking the union of
topological bases on each of the two components. -/
theorem IsTopologicalBasis.sum {s : Set (Set α)} (hs : IsTopologicalBasis s) {t : Set (Set β)}
    (ht : IsTopologicalBasis t) : IsTopologicalBasis ((fun u => Sum.inl '' u) '' s ∪ (fun u => Sum.inr '' u) '' t) := by
  apply is_topological_basis_of_open_of_nhds
  · intro u hu
    cases hu
    · rcases hu with ⟨w, hw, rfl⟩
      exact open_embedding_inl.is_open_map w (hs.is_open hw)
      
    · rcases hu with ⟨w, hw, rfl⟩
      exact open_embedding_inr.is_open_map w (ht.is_open hw)
      
    
  · rintro x u hxu u_open
    cases x
    · have h'x : x ∈ Sum.inl ⁻¹' u := hxu
      obtain ⟨v, vs, xv, vu⟩ : ∃ (v : Set α)(H : v ∈ s), x ∈ v ∧ v ⊆ Sum.inl ⁻¹' u :=
        hs.exists_subset_of_mem_open h'x (is_open_sum_iff.1 u_open).1
      exact ⟨Sum.inl '' v, mem_union_left _ (mem_image_of_mem _ vs), mem_image_of_mem _ xv, image_subset_iff.2 vu⟩
      
    · have h'x : x ∈ Sum.inr ⁻¹' u := hxu
      obtain ⟨v, vs, xv, vu⟩ : ∃ (v : Set β)(H : v ∈ t), x ∈ v ∧ v ⊆ Sum.inr ⁻¹' u :=
        ht.exists_subset_of_mem_open h'x (is_open_sum_iff.1 u_open).2
      exact ⟨Sum.inr '' v, mem_union_right _ (mem_image_of_mem _ vs), mem_image_of_mem _ xv, image_subset_iff.2 vu⟩
      
    

/-- A sum type of two second countable spaces is second countable. -/
instance [SecondCountableTopology α] [SecondCountableTopology β] : SecondCountableTopology (Sum α β) := by
  let b := (fun u => Sum.inl '' u) '' countable_basis α ∪ (fun u => Sum.inr '' u) '' countable_basis β
  have A : is_topological_basis b := (is_basis_countable_basis α).Sum (is_basis_countable_basis β)
  have B : b.countable :=
    (countable.image (countable_countable_basis _) _).union (countable.image (countable_countable_basis _) _)
  exact A.second_countable_topology B

end Sum

end TopologicalSpace

open TopologicalSpace

variable {α β : Type _} [TopologicalSpace α] [TopologicalSpace β] {f : α → β}

protected theorem Inducing.second_countable_topology [SecondCountableTopology β] (hf : Inducing f) :
    SecondCountableTopology α := by
  rw [hf.1]
  exact second_countable_topology_induced α β f

protected theorem Embedding.second_countable_topology [SecondCountableTopology β] (hf : Embedding f) :
    SecondCountableTopology α :=
  hf.1.SecondCountableTopology

