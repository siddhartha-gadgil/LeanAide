/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathbin.Tactic.Tfae
import Mathbin.Order.Atoms
import Mathbin.Order.OrderIsoNat
import Mathbin.Order.SupIndep
import Mathbin.Order.Zorn
import Mathbin.Data.Finset.Order
import Mathbin.Data.Finite.Default

/-!
# Compactness properties for complete lattices

For complete lattices, there are numerous equivalent ways to express the fact that the relation `>`
is well-founded. In this file we define three especially-useful characterisations and provide
proofs that they are indeed equivalent to well-foundedness.

## Main definitions
 * `complete_lattice.is_sup_closed_compact`
 * `complete_lattice.is_Sup_finite_compact`
 * `complete_lattice.is_compact_element`
 * `complete_lattice.is_compactly_generated`

## Main results
The main result is that the following four conditions are equivalent for a complete lattice:
 * `well_founded (>)`
 * `complete_lattice.is_sup_closed_compact`
 * `complete_lattice.is_Sup_finite_compact`
 * `∀ k, complete_lattice.is_compact_element k`

This is demonstrated by means of the following four lemmas:
 * `complete_lattice.well_founded.is_Sup_finite_compact`
 * `complete_lattice.is_Sup_finite_compact.is_sup_closed_compact`
 * `complete_lattice.is_sup_closed_compact.well_founded`
 * `complete_lattice.is_Sup_finite_compact_iff_all_elements_compact`

 We also show well-founded lattices are compactly generated
 (`complete_lattice.compactly_generated_of_well_founded`).

## References
- [G. Călugăreanu, *Lattice Concepts of Module Theory*][calugareanu]

## Tags

complete lattice, well-founded, compact
-/


variable {α : Type _} [CompleteLattice α]

namespace CompleteLattice

variable (α)

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (a b «expr ∈ » s)
/-- A compactness property for a complete lattice is that any `sup`-closed non-empty subset
contains its `Sup`. -/
def IsSupClosedCompact : Prop :=
  ∀ (s : Set α) (h : s.Nonempty), (∀ (a b) (_ : a ∈ s) (_ : b ∈ s), a⊔b ∈ s) → sup s ∈ s

/-- A compactness property for a complete lattice is that any subset has a finite subset with the
same `Sup`. -/
def IsSupFiniteCompact : Prop :=
  ∀ s : Set α, ∃ t : Finset α, ↑t ⊆ s ∧ sup s = t.sup id

/-- An element `k` of a complete lattice is said to be compact if any set with `Sup`
above `k` has a finite subset with `Sup` above `k`.  Such an element is also called
"finite" or "S-compact". -/
def IsCompactElement {α : Type _} [CompleteLattice α] (k : α) :=
  ∀ s : Set α, k ≤ sup s → ∃ t : Finset α, ↑t ⊆ s ∧ k ≤ t.sup id

theorem is_compact_element_iff.{u} {α : Type u} [CompleteLattice α] (k : α) :
    CompleteLattice.IsCompactElement k ↔ ∀ (ι : Type u) (s : ι → α), k ≤ supr s → ∃ t : Finset ι, k ≤ t.sup s := by
  classical
  constructor
  · intro H ι s hs
    obtain ⟨t, ht, ht'⟩ := H (Set.Range s) hs
    have : ∀ x : t, ∃ i, s i = x := fun x => ht x.Prop
    choose f hf using this
    refine' ⟨finset.univ.image f, ht'.trans _⟩
    · rw [Finset.sup_le_iff]
      intro b hb
      rw [← show s (f ⟨b, hb⟩) = id b from hf _]
      exact Finset.le_sup (Finset.mem_image_of_mem f <| Finset.mem_univ ⟨b, hb⟩)
      
    
  · intro H s hs
    obtain ⟨t, ht⟩ :=
      H s coe
        (by
          delta' supr
          rwa [Subtype.range_coe])
    refine'
      ⟨t.image coe, by
        simp , ht.trans _⟩
    rw [Finset.sup_le_iff]
    exact fun x hx => @Finset.le_sup _ _ _ _ _ id _ (Finset.mem_image_of_mem coe hx)
    

/-- An element `k` is compact if and only if any directed set with `Sup` above
`k` already got above `k` at some point in the set. -/
theorem is_compact_element_iff_le_of_directed_Sup_le (k : α) :
    IsCompactElement k ↔ ∀ s : Set α, s.Nonempty → DirectedOn (· ≤ ·) s → k ≤ sup s → ∃ x : α, x ∈ s ∧ k ≤ x := by
  classical
  constructor
  · intro hk s hne hdir hsup
    obtain ⟨t, ht⟩ := hk s hsup
    -- certainly every element of t is below something in s, since ↑t ⊆ s.
    have t_below_s : ∀, ∀ x ∈ t, ∀, ∃ y ∈ s, x ≤ y := fun x hxt => ⟨x, ht.left hxt, le_rfl⟩
    obtain ⟨x, ⟨hxs, hsupx⟩⟩ := Finset.sup_le_of_le_directed s hne hdir t t_below_s
    exact ⟨x, ⟨hxs, le_transₓ ht.right hsupx⟩⟩
    
  · intro hk s hsup
    -- Consider the set of finite joins of elements of the (plain) set s.
    let S : Set α := { x | ∃ t : Finset α, ↑t ⊆ s ∧ x = t.sup id }
    -- S is directed, nonempty, and still has sup above k.
    have dir_US : DirectedOn (· ≤ ·) S := by
      rintro x ⟨c, hc⟩ y ⟨d, hd⟩
      use x⊔y
      constructor
      · use c ∪ d
        constructor
        · simp only [← hc.left, ← hd.left, ← Set.union_subset_iff, ← Finset.coe_union, ← and_selfₓ]
          
        · simp only [← hc.right, ← hd.right, ← Finset.sup_union]
          
        
      simp only [← and_selfₓ, ← le_sup_left, ← le_sup_right]
    have sup_S : Sup s ≤ Sup S := by
      apply Sup_le_Sup
      intro x hx
      use {x}
      simpa only [← and_trueₓ, ← id.def, ← Finset.coe_singleton, ← eq_self_iff_true, ← Finset.sup_singleton, ←
        Set.singleton_subset_iff]
    have Sne : S.nonempty := by
      suffices : ⊥ ∈ S
      exact Set.nonempty_of_mem this
      use ∅
      simp only [← Set.empty_subset, ← Finset.coe_empty, ← Finset.sup_empty, ← eq_self_iff_true, ← and_selfₓ]
    -- Now apply the defn of compact and finish.
    obtain ⟨j, ⟨hjS, hjk⟩⟩ := hk S Sne dir_US (le_transₓ hsup sup_S)
    obtain ⟨t, ⟨htS, htsup⟩⟩ := hjS
    use t
    exact
      ⟨htS, by
        rwa [← htsup]⟩
    

/-- A compact element `k` has the property that any directed set lying strictly below `k` has
its Sup strictly below `k`. -/
theorem IsCompactElement.directed_Sup_lt_of_lt {α : Type _} [CompleteLattice α] {k : α} (hk : IsCompactElement k)
    {s : Set α} (hemp : s.Nonempty) (hdir : DirectedOn (· ≤ ·) s) (hbelow : ∀, ∀ x ∈ s, ∀, x < k) : sup s < k := by
  rw [is_compact_element_iff_le_of_directed_Sup_le] at hk
  by_contra
  have sSup : Sup s ≤ k := Sup_le fun s hs => (hbelow s hs).le
  replace sSup : Sup s = k := eq_iff_le_not_lt.mpr ⟨sSup, h⟩
  obtain ⟨x, hxs, hkx⟩ := hk s hemp hdir sSup.symm.le
  obtain hxk := hbelow x hxs
  exact hxk.ne (hxk.le.antisymm hkx)

theorem finset_sup_compact_of_compact {α β : Type _} [CompleteLattice α] {f : β → α} (s : Finset β)
    (h : ∀, ∀ x ∈ s, ∀, IsCompactElement (f x)) : IsCompactElement (s.sup f) := by
  classical
  rw [is_compact_element_iff_le_of_directed_Sup_le]
  intro d hemp hdir hsup
  change f with id ∘ f
  rw [← Finset.sup_finset_image]
  apply Finset.sup_le_of_le_directed d hemp hdir
  rintro x hx
  obtain ⟨p, ⟨hps, rfl⟩⟩ := finset.mem_image.mp hx
  specialize h p hps
  rw [is_compact_element_iff_le_of_directed_Sup_le] at h
  specialize h d hemp hdir (le_transₓ (Finset.le_sup hps) hsup)
  simpa only [← exists_prop]

theorem WellFounded.is_Sup_finite_compact (h : WellFounded ((· > ·) : α → α → Prop)) : IsSupFiniteCompact α := by
  intro s
  let p : Set α := { x | ∃ t : Finset α, ↑t ⊆ s ∧ t.sup id = x }
  have hp : p.nonempty := by
    use ⊥, ∅
    simp
  obtain ⟨m, ⟨t, ⟨ht₁, ht₂⟩⟩, hm⟩ := well_founded.well_founded_iff_has_max'.mp h p hp
  use t
  simp only [← ht₁, ← ht₂, ← true_andₓ]
  apply le_antisymmₓ
  · apply Sup_le
    intro y hy
    classical
    have hy' : (insert y t).sup id ∈ p := by
      use insert y t
      simp
      rw [Set.insert_subset]
      exact ⟨hy, ht₁⟩
    have hm' : m ≤ (insert y t).sup id := by
      rw [← ht₂]
      exact Finset.sup_mono (t.subset_insert y)
    rw [← hm _ hy' hm']
    simp
    
  · rw [← ht₂, Finset.sup_id_eq_Sup]
    exact Sup_le_Sup ht₁
    

theorem IsSupFiniteCompact.is_sup_closed_compact (h : IsSupFiniteCompact α) : IsSupClosedCompact α := by
  intro s hne hsc
  obtain ⟨t, ht₁, ht₂⟩ := h s
  clear h
  cases' t.eq_empty_or_nonempty with h h
  · subst h
    rw [Finset.sup_empty] at ht₂
    rw [ht₂]
    simp [← eq_singleton_bot_of_Sup_eq_bot_of_nonempty ht₂ hne]
    
  · rw [ht₂]
    exact t.sup_closed_of_sup_closed h ht₁ hsc
    

theorem IsSupClosedCompact.well_founded (h : IsSupClosedCompact α) : WellFounded ((· > ·) : α → α → Prop) := by
  refine' rel_embedding.well_founded_iff_no_descending_seq.mpr ⟨fun a => _⟩
  suffices Sup (Set.Range a) ∈ Set.Range a by
    obtain ⟨n, hn⟩ := set.mem_range.mp this
    have h' : Sup (Set.Range a) < a (n + 1) := by
      change _ > _
      simp [hn, ← a.map_rel_iff]
    apply lt_irreflₓ (a (n + 1))
    apply lt_of_le_of_ltₓ _ h'
    apply le_Sup
    apply Set.mem_range_self
  apply h (Set.Range a)
  · use a 37
    apply Set.mem_range_self
    
  · rintro x ⟨m, hm⟩ y ⟨n, hn⟩
    use m⊔n
    rw [← hm, ← hn]
    apply RelHomClass.map_sup a
    

theorem is_Sup_finite_compact_iff_all_elements_compact : IsSupFiniteCompact α ↔ ∀ k : α, IsCompactElement k := by
  refine' ⟨fun h k s hs => _, fun h s => _⟩
  · obtain ⟨t, ⟨hts, htsup⟩⟩ := h s
    use t, hts
    rwa [← htsup]
    
  · obtain ⟨t, ⟨hts, htsup⟩⟩ :=
      h (Sup s) s
        (by
          rfl)
    have : Sup s = t.sup id := by
      suffices t.sup id ≤ Sup s by
        apply le_antisymmₓ <;> assumption
      simp only [← id.def, ← Finset.sup_le_iff]
      intro x hx
      exact le_Sup (hts hx)
    use t, hts, this
    

theorem well_founded_characterisations :
    Tfae
      [WellFounded ((· > ·) : α → α → Prop), IsSupFiniteCompact α, IsSupClosedCompact α, ∀ k : α, IsCompactElement k] :=
  by
  tfae_have 1 → 2
  · exact well_founded.is_Sup_finite_compact α
    
  tfae_have 2 → 3
  · exact is_Sup_finite_compact.is_sup_closed_compact α
    
  tfae_have 3 → 1
  · exact is_sup_closed_compact.well_founded α
    
  tfae_have 2 ↔ 4
  · exact is_Sup_finite_compact_iff_all_elements_compact α
    
  tfae_finish

theorem well_founded_iff_is_Sup_finite_compact : WellFounded ((· > ·) : α → α → Prop) ↔ IsSupFiniteCompact α :=
  (well_founded_characterisations α).out 0 1

theorem is_Sup_finite_compact_iff_is_sup_closed_compact : IsSupFiniteCompact α ↔ IsSupClosedCompact α :=
  (well_founded_characterisations α).out 1 2

theorem is_sup_closed_compact_iff_well_founded : IsSupClosedCompact α ↔ WellFounded ((· > ·) : α → α → Prop) :=
  (well_founded_characterisations α).out 2 0

alias well_founded_iff_is_Sup_finite_compact ↔ _ is_Sup_finite_compact.well_founded

alias is_Sup_finite_compact_iff_is_sup_closed_compact ↔ _ is_sup_closed_compact.is_Sup_finite_compact

alias is_sup_closed_compact_iff_well_founded ↔ _ _root_.well_founded.is_sup_closed_compact

variable {α}

theorem WellFounded.finite_of_set_independent (h : WellFounded ((· > ·) : α → α → Prop)) {s : Set α}
    (hs : SetIndependent s) : s.Finite := by
  classical
  refine' set.not_infinite.mp fun contra => _
  obtain ⟨t, ht₁, ht₂⟩ := well_founded.is_Sup_finite_compact α h s
  replace contra : ∃ x : α, x ∈ s ∧ x ≠ ⊥ ∧ x ∉ t
  · have : (s \ (insert ⊥ t : Finset α)).Infinite := contra.diff (Finset.finite_to_set _)
    obtain ⟨x, hx₁, hx₂⟩ := this.nonempty
    exact
      ⟨x, hx₁, by
        simpa [← not_or_distrib] using hx₂⟩
    
  obtain ⟨x, hx₀, hx₁, hx₂⟩ := contra
  replace hs : x⊓Sup s = ⊥
  · have :=
      hs.mono
        (by
          simp [← ht₁, ← hx₀, -Set.union_singleton] : ↑t ∪ {x} ≤ s)
        (by
          simp : x ∈ _)
    simpa [← Disjoint, ← hx₂, t.sup_id_eq_Sup, ht₂] using this
    
  apply hx₁
  rw [← hs, eq_comm, inf_eq_left]
  exact le_Sup hx₀

theorem WellFounded.finite_of_independent (hwf : WellFounded ((· > ·) : α → α → Prop)) {ι : Type _} {t : ι → α}
    (ht : Independent t) (h_ne_bot : ∀ i, t i ≠ ⊥) : Finite ι := by
  have := (well_founded.finite_of_set_independent hwf ht.set_independent_range).to_subtype
  exact Finite.of_injective_finite_range (ht.injective h_ne_bot)

end CompleteLattice

/-- A complete lattice is said to be compactly generated if any
element is the `Sup` of compact elements. -/
class IsCompactlyGenerated (α : Type _) [CompleteLattice α] : Prop where
  exists_Sup_eq : ∀ x : α, ∃ s : Set α, (∀, ∀ x ∈ s, ∀, CompleteLattice.IsCompactElement x) ∧ sup s = x

section

variable {α} [IsCompactlyGenerated α] {a b : α} {s : Set α}

@[simp]
theorem Sup_compact_le_eq (b) : sup { c : α | CompleteLattice.IsCompactElement c ∧ c ≤ b } = b := by
  rcases IsCompactlyGenerated.exists_Sup_eq b with ⟨s, hs, rfl⟩
  exact le_antisymmₓ (Sup_le fun c hc => hc.2) (Sup_le_Sup fun c cs => ⟨hs c cs, le_Sup cs⟩)

@[simp]
theorem Sup_compact_eq_top : sup { a : α | CompleteLattice.IsCompactElement a } = ⊤ := by
  refine' Eq.trans (congr rfl (Set.ext fun x => _)) (Sup_compact_le_eq ⊤)
  exact (and_iff_left le_top).symm

theorem le_iff_compact_le_imp {a b : α} : a ≤ b ↔ ∀ c : α, CompleteLattice.IsCompactElement c → c ≤ a → c ≤ b :=
  ⟨fun ab c hc ca => le_transₓ ca ab, fun h => by
    rw [← Sup_compact_le_eq a, ← Sup_compact_le_eq b]
    exact Sup_le_Sup fun c hc => ⟨hc.1, h c hc.1 hc.2⟩⟩

/-- This property is sometimes referred to as `α` being upper continuous. -/
theorem inf_Sup_eq_of_directed_on (h : DirectedOn (· ≤ ·) s) : a⊓sup s = ⨆ b ∈ s, a⊓b :=
  le_antisymmₓ
    (by
      rw [le_iff_compact_le_imp]
      by_cases' hs : s.nonempty
      · intro c hc hcinf
        rw [le_inf_iff] at hcinf
        rw [CompleteLattice.is_compact_element_iff_le_of_directed_Sup_le] at hc
        rcases hc s hs h hcinf.2 with ⟨d, ds, cd⟩
        exact (le_inf hcinf.1 cd).trans (le_supr₂ d ds)
        
      · rw [Set.not_nonempty_iff_eq_empty] at hs
        simp [← hs]
        )
    supr_inf_le_inf_Sup

/-- This property is equivalent to `α` being upper continuous. -/
theorem inf_Sup_eq_supr_inf_sup_finset : a⊓sup s = ⨆ (t : Finset α) (H : ↑t ⊆ s), a⊓t.sup id :=
  le_antisymmₓ
    (by
      rw [le_iff_compact_le_imp]
      intro c hc hcinf
      rw [le_inf_iff] at hcinf
      rcases hc s hcinf.2 with ⟨t, ht1, ht2⟩
      exact (le_inf hcinf.1 ht2).trans (le_supr₂ t ht1))
    (supr_le fun t => supr_le fun h => inf_le_inf_left _ ((Finset.sup_id_eq_Sup t).symm ▸ Sup_le_Sup h))

theorem CompleteLattice.set_independent_iff_finite {s : Set α} :
    CompleteLattice.SetIndependent s ↔ ∀ t : Finset α, ↑t ⊆ s → CompleteLattice.SetIndependent (↑t : Set α) :=
  ⟨fun hs t ht => hs.mono ht, fun h a ha => by
    rw [disjoint_iff, inf_Sup_eq_supr_inf_sup_finset, supr_eq_bot]
    intro t
    rw [supr_eq_bot, Finset.sup_id_eq_Sup]
    intro ht
    classical
    have h' := (h (insert a t) _ (t.mem_insert_self a)).eq_bot
    · rwa [Finset.coe_insert, Set.insert_diff_self_of_not_mem] at h'
      exact fun con => ((Set.mem_diff a).1 (ht con)).2 (Set.mem_singleton a)
      
    · rw [Finset.coe_insert, Set.insert_subset]
      exact ⟨ha, Set.Subset.trans ht (Set.diff_subset _ _)⟩
      ⟩

theorem CompleteLattice.set_independent_Union_of_directed {η : Type _} {s : η → Set α} (hs : Directed (· ⊆ ·) s)
    (h : ∀ i, CompleteLattice.SetIndependent (s i)) : CompleteLattice.SetIndependent (⋃ i, s i) := by
  by_cases' hη : Nonempty η
  · skip
    rw [CompleteLattice.set_independent_iff_finite]
    intro t ht
    obtain ⟨I, fi, hI⟩ := Set.finite_subset_Union t.finite_to_set ht
    obtain ⟨i, hi⟩ := hs.finset_le fi.to_finset
    exact (h i).mono (Set.Subset.trans hI <| Set.Union₂_subset fun j hj => hi j (fi.mem_to_finset.2 hj))
    
  · rintro a ⟨_, ⟨i, _⟩, _⟩
    exfalso
    exact hη ⟨i⟩
    

theorem CompleteLattice.independent_sUnion_of_directed {s : Set (Set α)} (hs : DirectedOn (· ⊆ ·) s)
    (h : ∀, ∀ a ∈ s, ∀, CompleteLattice.SetIndependent a) : CompleteLattice.SetIndependent (⋃₀s) := by
  rw [Set.sUnion_eq_Union] <;>
    exact
      CompleteLattice.set_independent_Union_of_directed hs.directed_coe
        (by
          simpa using h)

end

namespace CompleteLattice

theorem compactly_generated_of_well_founded (h : WellFounded ((· > ·) : α → α → Prop)) : IsCompactlyGenerated α := by
  rw [well_founded_iff_is_Sup_finite_compact, is_Sup_finite_compact_iff_all_elements_compact] at h
  -- x is the join of the set of compact elements {x}
  exact ⟨fun x => ⟨{x}, ⟨fun x _ => h x, Sup_singleton⟩⟩⟩

/-- A compact element `k` has the property that any `b < k` lies below a "maximal element below
`k`", which is to say `[⊥, k]` is coatomic. -/
theorem Iic_coatomic_of_compact_element {k : α} (h : IsCompactElement k) : IsCoatomic (Set.Iic k) :=
  ⟨fun ⟨b, hbk⟩ => by
    by_cases' htriv : b = k
    · left
      ext
      simp only [← htriv, ← Set.Iic.coe_top, ← Subtype.coe_mk]
      
    right
    obtain ⟨a, a₀, ba, h⟩ := zorn_nonempty_partial_order₀ (Set.Iio k) _ b (lt_of_le_of_neₓ hbk htriv)
    · refine' ⟨⟨a, le_of_ltₓ a₀⟩, ⟨ne_of_ltₓ a₀, fun c hck => by_contradiction fun c₀ => _⟩, ba⟩
      cases h c.1 (lt_of_le_of_neₓ c.2 fun con => c₀ (Subtype.ext con)) hck.le
      exact lt_irreflₓ _ hck
      
    · intro S SC cC I IS
      by_cases' hS : S.nonempty
      · exact ⟨Sup S, h.directed_Sup_lt_of_lt hS cC.directed_on SC, fun _ => le_Sup⟩
        
      exact
        ⟨b, lt_of_le_of_neₓ hbk htriv, by
          simp only [← set.not_nonempty_iff_eq_empty.mp hS, ← Set.mem_empty_eq, ← forall_const, ← forall_prop_of_false,
            ← not_false_iff]⟩
      ⟩

theorem coatomic_of_top_compact (h : IsCompactElement (⊤ : α)) : IsCoatomic α :=
  (@OrderIso.iicTop α _ _).is_coatomic_iff.mp (Iic_coatomic_of_compact_element h)

end CompleteLattice

section

variable [IsModularLattice α] [IsCompactlyGenerated α]

instance (priority := 100) is_atomic_of_is_complemented [IsComplemented α] : IsAtomic α :=
  ⟨fun b => by
    by_cases' h : { c : α | CompleteLattice.IsCompactElement c ∧ c ≤ b } ⊆ {⊥}
    · left
      rw [← Sup_compact_le_eq b, Sup_eq_bot]
      exact h
      
    · rcases Set.not_subset.1 h with ⟨c, ⟨hc, hcb⟩, hcbot⟩
      right
      have hc' := CompleteLattice.Iic_coatomic_of_compact_element hc
      rw [← is_atomic_iff_is_coatomic] at hc'
      have := hc'
      obtain con | ⟨a, ha, hac⟩ := eq_bot_or_exists_atom_le (⟨c, le_reflₓ c⟩ : Set.Iic c)
      · exfalso
        apply hcbot
        simp only [← Subtype.ext_iff, ← Set.Iic.coe_bot, ← Subtype.coe_mk] at con
        exact con
        
      rw [← Subtype.coe_le_coe, Subtype.coe_mk] at hac
      exact ⟨a, ha.of_is_atom_coe_Iic, hac.trans hcb⟩
      ⟩

/-- See Lemma 5.1, Călugăreanu -/
instance (priority := 100) is_atomistic_of_is_complemented [IsComplemented α] : IsAtomistic α :=
  ⟨fun b =>
    ⟨{ a | IsAtom a ∧ a ≤ b }, by
      symm
      have hle : Sup { a : α | IsAtom a ∧ a ≤ b } ≤ b := Sup_le fun _ => And.right
      apply (lt_or_eq_of_leₓ hle).resolve_left fun con => _
      obtain ⟨c, hc⟩ := exists_is_compl (⟨Sup { a : α | IsAtom a ∧ a ≤ b }, hle⟩ : Set.Iic b)
      obtain rfl | ⟨a, ha, hac⟩ := eq_bot_or_exists_atom_le c
      · exact ne_of_ltₓ con (Subtype.ext_iff.1 (eq_top_of_is_compl_bot hc))
        
      · apply ha.1
        rw [eq_bot_iff]
        apply le_transₓ (le_inf _ hac) hc.1
        rw [← Subtype.coe_le_coe, Subtype.coe_mk]
        exact le_Sup ⟨ha.of_is_atom_coe_Iic, a.2⟩
        ,
      fun _ => And.left⟩⟩

/-- See Theorem 6.6, Călugăreanu -/
theorem is_complemented_of_Sup_atoms_eq_top (h : sup { a : α | IsAtom a } = ⊤) : IsComplemented α :=
  ⟨fun b => by
    obtain ⟨s, ⟨s_ind, b_inf_Sup_s, s_atoms⟩, s_max⟩ :=
      zorn_subset { s : Set α | CompleteLattice.SetIndependent s ∧ b⊓Sup s = ⊥ ∧ ∀, ∀ a ∈ s, ∀, IsAtom a } _
    · refine' ⟨Sup s, le_of_eqₓ b_inf_Sup_s, h.symm.trans_le <| Sup_le_iff.2 fun a ha => _⟩
      rw [← inf_eq_left]
      refine' (ha.le_iff.mp inf_le_left).resolve_left fun con => ha.1 _
      rw [eq_bot_iff, ← con]
      refine' le_inf (le_reflₓ a) ((le_Sup _).trans le_sup_right)
      rw [← disjoint_iff] at *
      have a_dis_Sup_s : Disjoint a (Sup s) := con.mono_right le_sup_right
      rw [← s_max (s ∪ {a}) ⟨fun x hx => _, ⟨_, fun x hx => _⟩⟩ (Set.subset_union_left _ _)]
      · exact Set.mem_union_right _ (Set.mem_singleton _)
        
      · rw [Set.mem_union, Set.mem_singleton_iff] at hx
        by_cases' xa : x = a
        · simp only [← xa, ← Set.mem_singleton, ← Set.insert_diff_of_mem, ← Set.union_singleton]
          exact con.mono_right (le_transₓ (Sup_le_Sup (Set.diff_subset s {a})) le_sup_right)
          
        · have h : (s ∪ {a}) \ {x} = s \ {x} ∪ {a} := by
            simp only [← Set.union_singleton]
            rw [Set.insert_diff_of_not_mem]
            rw [Set.mem_singleton_iff]
            exact Ne.symm xa
          rw [h, Sup_union, Sup_singleton]
          apply (s_ind (hx.resolve_right xa)).disjoint_sup_right_of_disjoint_sup_left (a_dis_Sup_s.mono_right _).symm
          rw [← Sup_insert, Set.insert_diff_singleton, Set.insert_eq_of_mem (hx.resolve_right xa)]
          
        
      · rw [Sup_union, Sup_singleton, ← disjoint_iff]
        exact b_inf_Sup_s.disjoint_sup_right_of_disjoint_sup_left con.symm
        
      · rw [Set.mem_union, Set.mem_singleton_iff] at hx
        cases hx
        · exact s_atoms x hx
          
        · rw [hx]
          exact ha
          
        
      
    · intro c hc1 hc2
      refine'
        ⟨⋃₀c, ⟨CompleteLattice.independent_sUnion_of_directed hc2.directed_on fun s hs => (hc1 hs).1, _, fun a ha => _⟩,
          fun _ => Set.subset_sUnion_of_mem⟩
      · rw [Sup_sUnion, ← Sup_image, inf_Sup_eq_of_directed_on, supr_eq_bot]
        · intro i
          rw [supr_eq_bot]
          intro hi
          obtain ⟨x, xc, rfl⟩ := (Set.mem_image _ _ _).1 hi
          exact (hc1 xc).2.1
          
        · rw [directed_on_image]
          refine' hc2.directed_on.mono fun s t => Sup_le_Sup
          
        
      · rcases Set.mem_sUnion.1 ha with ⟨s, sc, as⟩
        exact (hc1 sc).2.2 a as
        
      ⟩

/-- See Theorem 6.6, Călugăreanu -/
theorem is_complemented_of_is_atomistic [IsAtomistic α] : IsComplemented α :=
  is_complemented_of_Sup_atoms_eq_top Sup_atoms_eq_top

theorem is_complemented_iff_is_atomistic : IsComplemented α ↔ IsAtomistic α := by
  constructor <;> intros
  · exact is_atomistic_of_is_complemented
    
  · exact is_complemented_of_is_atomistic
    

end

