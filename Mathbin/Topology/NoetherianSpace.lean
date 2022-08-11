/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathbin.Order.CompactlyGenerated
import Mathbin.Order.OrderIsoNat
import Mathbin.Topology.Sets.Compacts

/-!
# Noetherian space

A Noetherian space is a topological space that satisfies any of the following equivalent conditions:
- `well_founded ((>) : opens α → opens α → Prop)`
- `well_founded ((<) : closeds α → closeds α → Prop)`
- `∀ s : set α, is_compact s`
- `∀ s : opens α, is_compact s`

The first is chosen as the definition, and the equivalence is shown in
`topological_space.noetherian_space_tfae`.

Many examples of noetherian spaces come from algebraic topology. For example, the underlying space
of a noetherian scheme (e.g., the spectrum of a noetherian ring) is noetherian.

## Main Results
- `noetherian_space.set`: Every subspace of a noetherian space is noetherian.
- `noetherian_space.is_compact`: Every subspace of a noetherian space is compact.
- `noetherian_space_tfae`: Describes the equivalent definitions of noetherian spaces.
- `noetherian_space.range`: The image of a noetherian space under a continuous map is noetherian.
- `noetherian_space.Union`: The finite union of noetherian spaces is noetherian.
- `noetherian_space.discrete`: A noetherian and hausdorff space is discrete.
- `noetherian_space.exists_finset_irreducible` : Every closed subset of a noetherian space is a
  finite union of irreducible closed subsets.
- `noetherian_space.finite_irreducible_components `: The number of irreducible components of a
  noetherian space is finite.

-/


variable (α β : Type _) [TopologicalSpace α] [TopologicalSpace β]

namespace TopologicalSpace

/-- Type class for noetherian spaces. It is defined to be spaces whose open sets satisfies ACC. -/
@[mk_iff]
class NoetherianSpace : Prop where
  WellFounded : WellFounded ((· > ·) : Opens α → Opens α → Prop)

theorem noetherian_space_iff_opens : NoetherianSpace α ↔ ∀ s : Opens α, IsCompact (s : Set α) := by
  rw [noetherian_space_iff, CompleteLattice.well_founded_iff_is_Sup_finite_compact,
    CompleteLattice.is_Sup_finite_compact_iff_all_elements_compact]
  exact forall_congrₓ opens.is_compact_element_iff

instance (priority := 100) NoetherianSpace.compact_space [h : NoetherianSpace α] : CompactSpace α :=
  is_compact_univ_iff.mp ((noetherian_space_iff_opens α).mp h ⊤)

variable {α}

instance NoetherianSpace.set [h : NoetherianSpace α] (s : Set α) : NoetherianSpace s := by
  rw [noetherian_space_iff]
  apply WellFounded.well_founded_iff_has_max'.2
  intro p hp
  obtain ⟨⟨_, u, hu, rfl⟩, hu'⟩ := hp
  obtain ⟨U, hU, hU'⟩ :=
    WellFounded.well_founded_iff_has_max'.1 h.1 (opens.comap ⟨_, continuous_subtype_coe⟩ ⁻¹' p) ⟨⟨u, hu⟩, hu'⟩
  refine' ⟨opens.comap ⟨_, continuous_subtype_coe⟩ U, hU, _⟩
  rintro ⟨_, x, hx, rfl⟩ hx' hx''
  refine' le_antisymmₓ (Set.preimage_mono (_ : (⟨x, hx⟩ : opens α) ≤ U)) hx''
  refine' sup_eq_right.mp (hU' (⟨x, hx⟩⊔U) _ le_sup_right)
  dsimp' [← Set.Preimage]
  rw [map_sup]
  convert hx'
  exact sup_eq_left.mpr hx''

variable (α)

example (α : Type _) : Set α ≃o (Set α)ᵒᵈ := by
  refine' OrderIso.compl (Set α)

theorem noetherian_space_tfae :
    Tfae
      [NoetherianSpace α, WellFounded fun s t : Closeds α => s < t, ∀ s : Set α, IsCompact s,
        ∀ s : Opens α, IsCompact (s : Set α)] :=
  by
  tfae_have 1 ↔ 2
  · refine' (noetherian_space_iff _).trans (Surjective.well_founded_iff opens.compl_bijective.2 _)
    exact fun s t => (OrderIso.compl (Set α)).lt_iff_lt.symm
    
  tfae_have 1 ↔ 4
  · exact noetherian_space_iff_opens α
    
  tfae_have 1 → 3
  · intro H s
    rw [is_compact_iff_compact_space]
    skip
    infer_instance
    
  tfae_have 3 → 4
  · exact fun H s => H s
    
  tfae_finish

variable {α β}

theorem NoetherianSpace.is_compact [h : NoetherianSpace α] (s : Set α) : IsCompact s :=
  let H := (noetherian_space_tfae α).out 0 2
  H.mp h s

theorem noetherian_space_of_surjective [NoetherianSpace α] (f : α → β) (hf : Continuous f)
    (hf' : Function.Surjective f) : NoetherianSpace β := by
  rw [noetherian_space_iff_opens]
  intro s
  obtain ⟨t, e⟩ := set.image_surjective.mpr hf' s
  exact e ▸ (noetherian_space.is_compact t).Image hf

theorem noetherian_space_iff_of_homeomorph (f : α ≃ₜ β) : NoetherianSpace α ↔ NoetherianSpace β :=
  ⟨fun h => @noetherian_space_of_surjective _ _ h f f.Continuous f.Surjective, fun h =>
    @noetherian_space_of_surjective _ _ h f.symm f.symm.Continuous f.symm.Surjective⟩

theorem NoetherianSpace.range [NoetherianSpace α] (f : α → β) (hf : Continuous f) : NoetherianSpace (Set.Range f) :=
  noetherian_space_of_surjective (Set.codRestrict f _ Set.mem_range_self)
    (by
      continuity)
    fun ⟨a, b, h⟩ => ⟨b, Subtype.ext h⟩

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (t «expr ⊆ » s)
theorem noetherian_space_set_iff (s : Set α) : NoetherianSpace s ↔ ∀ (t) (_ : t ⊆ s), IsCompact t := by
  rw [(noetherian_space_tfae s).out 0 2]
  constructor
  · intro H t ht
    have := embedding_subtype_coe.is_compact_iff_is_compact_image.mp (H (coe ⁻¹' t))
    simpa [← set.inter_eq_left_iff_subset.mpr ht] using this
    
  · intro H t
    refine' embedding_subtype_coe.is_compact_iff_is_compact_image.mpr (H (coe '' t) _)
    simp
    

@[simp]
theorem noetherian_univ_iff : NoetherianSpace (Set.Univ : Set α) ↔ NoetherianSpace α :=
  noetherian_space_iff_of_homeomorph (Homeomorph.Set.univ α)

theorem NoetherianSpace.Union {ι : Type _} (f : ι → Set α) [Finite ι] [hf : ∀ i, NoetherianSpace (f i)] :
    NoetherianSpace (⋃ i, f i) := by
  cases nonempty_fintype ι
  simp_rw [noetherian_space_set_iff] at hf⊢
  intro t ht
  rw [← set.inter_eq_left_iff_subset.mpr ht, Set.inter_Union]
  exact compact_Union fun i => hf i _ (Set.inter_subset_right _ _)

-- This is not an instance since it makes a loop with `t2_space_discrete`.
theorem NoetherianSpace.discrete [NoetherianSpace α] [T2Space α] : DiscreteTopology α :=
  ⟨eq_bot_iff.mpr fun U _ => is_closed_compl_iff.mp (NoetherianSpace.is_compact _).IsClosed⟩

attribute [local instance] noetherian_space.discrete

/-- Spaces that are both Noetherian and Hausdorff is finite. -/
theorem NoetherianSpace.finite [NoetherianSpace α] [T2Space α] : Finite α := by
  let this : Fintype α := Set.fintypeOfFiniteUniv (noetherian_space.is_compact Set.Univ).finite_of_discrete
  infer_instance

instance (priority := 100) Finite.to_noetherian_space [Finite α] : NoetherianSpace α := by
  cases nonempty_fintype α
  classical
  exact ⟨@Fintype.well_founded_of_trans_of_irrefl (Subtype.fintype _) _ _ _⟩

theorem NoetherianSpace.exists_finset_irreducible [NoetherianSpace α] (s : Closeds α) :
    ∃ S : Finset (Closeds α), (∀ k : S, IsIrreducible (k : Set α)) ∧ s = S.sup id := by
  classical
  have := ((noetherian_space_tfae α).out 0 1).mp inferInstance
  apply WellFounded.induction this s
  clear s
  intro s H
  by_cases' h₁ : IsPreirreducible s.1
  cases h₂ : s.1.eq_empty_or_nonempty
  · use ∅
    refine' ⟨fun k => k.2.elim, _⟩
    rw [Finset.sup_empty]
    ext1
    exact h
    
  · use {s}
    simp only [← coe_coe, ← Finset.sup_singleton, ← id.def, ← eq_self_iff_true, ← and_trueₓ]
    rintro ⟨k, hk⟩
    cases finset.mem_singleton.mp hk
    exact ⟨h, h₁⟩
    
  · rw [is_preirreducible_iff_closed_union_closed] at h₁
    push_neg  at h₁
    obtain ⟨z₁, z₂, hz₁, hz₂, h, hz₁', hz₂'⟩ := h₁
    obtain ⟨S₁, hS₁, hS₁'⟩ := H (s⊓⟨z₁, hz₁⟩) (inf_lt_left.2 hz₁')
    obtain ⟨S₂, hS₂, hS₂'⟩ := H (s⊓⟨z₂, hz₂⟩) (inf_lt_left.2 hz₂')
    refine' ⟨S₁ ∪ S₂, fun k => _, _⟩
    · cases' finset.mem_union.mp k.2 with h' h'
      exacts[hS₁ ⟨k, h'⟩, hS₂ ⟨k, h'⟩]
      
    · rwa [Finset.sup_union, ← hS₁', ← hS₂', ← inf_sup_left, left_eq_inf]
      
    

theorem NoetherianSpace.finite_irreducible_components [NoetherianSpace α] :
    (Set.Range IrreducibleComponent : Set (Set α)).Finite := by
  classical
  obtain ⟨S, hS₁, hS₂⟩ := noetherian_space.exists_finset_irreducible (⊤ : closeds α)
  suffices ∀ x : α, ∃ s : S, IrreducibleComponent x = s by
    choose f hf
    rw [show IrreducibleComponent = coe ∘ f from funext hf, Set.range_comp]
    exact (Set.Finite.intro inferInstance).Image _
  intro x
  obtain ⟨z, hz, hz'⟩ : ∃ (z : Set α)(H : z ∈ Finset.image coe S), IrreducibleComponent x ⊆ z := by
    convert is_irreducible_iff_sUnion_closed.mp is_irreducible_irreducible_component (S.image coe) _ _
    · infer_instance
      
    · simp only [← Finset.mem_image, ← exists_prop, ← forall_exists_index, ← and_imp]
      rintro _ z hz rfl
      exact z.2
      
    · exact
        (Set.subset_univ _).trans
          ((congr_arg coe hS₂).trans <| by
              simp ).Subset
      
  obtain ⟨s, hs, e⟩ := finset.mem_image.mp hz
  rw [← e] at hz'
  use ⟨s, hs⟩
  symm
  apply eq_irreducible_component (hS₁ _).2
  simpa

end TopologicalSpace

