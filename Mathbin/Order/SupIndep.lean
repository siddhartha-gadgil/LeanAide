/-
Copyright (c) 2021 Aaron Anderson, Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Kevin Buzzard, Yaël Dillies, Eric Wieser
-/
import Mathbin.Data.Finset.Pairwise
import Mathbin.Data.Set.Finite

/-!
# Supremum independence

In this file, we define supremum independence of indexed sets. An indexed family `f : ι → α` is
sup-independent if, for all `a`, `f a` and the supremum of the rest are disjoint.

## Main definitions

* `finset.sup_indep s f`: a family of elements `f` are supremum independent on the finite set `s`.
* `complete_lattice.set_independent s`: a set of elements are supremum independent.
* `complete_lattice.independent f`: a family of elements are supremum independent.

## Main statements

* In a distributive lattice, supremum independence is equivalent to pairwise disjointness:
  * `finset.sup_indep_iff_pairwise_disjoint`
  * `complete_lattice.set_independent_iff_pairwise_disjoint`
  * `complete_lattice.independent_iff_pairwise_disjoint`
* Otherwise, supremum independence is stronger than pairwise disjointness:
  * `finset.sup_indep.pairwise_disjoint`
  * `complete_lattice.set_independent.pairwise_disjoint`
  * `complete_lattice.independent.pairwise_disjoint`

## Implementation notes

For the finite version, we avoid the "obvious" definition
`∀ i ∈ s, disjoint (f i) ((s.erase i).sup f)` because `erase` would require decidable equality on
`ι`.
-/


variable {α β ι ι' : Type _}

/-! ### On lattices with a bottom element, via `finset.sup` -/


namespace Finset

section Lattice

variable [Lattice α] [OrderBot α]

/-- Supremum independence of finite sets. We avoid the "obvious" definition using `s.erase i`
because `erase` would require decidable equality on `ι`. -/
def SupIndep (s : Finset ι) (f : ι → α) : Prop :=
  ∀ ⦃t⦄, t ⊆ s → ∀ ⦃i⦄, i ∈ s → i ∉ t → Disjoint (f i) (t.sup f)

variable {s t : Finset ι} {f : ι → α} {i : ι}

instance [DecidableEq ι] [DecidableEq α] : Decidable (SupIndep s f) := by
  apply @Finset.decidableForallOfDecidableSubsets _ _ _ _
  intro t ht
  apply @Finset.decidableDforallFinset _ _ _ _
  exact fun i hi => @Implies.decidable _ _ _ (decidableOfIff' (_ = ⊥) disjoint_iff)

theorem SupIndep.subset (ht : t.SupIndep f) (h : s ⊆ t) : s.SupIndep f := fun u hu i hi => ht (hu.trans h) (h hi)

theorem sup_indep_empty (f : ι → α) : (∅ : Finset ι).SupIndep f := fun _ _ a ha => ha.elim

theorem sup_indep_singleton (i : ι) (f : ι → α) : ({i} : Finset ι).SupIndep f := fun s hs j hji hj => by
  rw [eq_empty_of_ssubset_singleton ⟨hs, fun h => hj (h hji)⟩, sup_empty]
  exact disjoint_bot_right

theorem SupIndep.pairwise_disjoint (hs : s.SupIndep f) : (s : Set ι).PairwiseDisjoint f := fun a ha b hb hab =>
  sup_singleton.subst <| hs (singleton_subset_iff.2 hb) ha <| not_mem_singleton.2 hab

/-- The RHS looks like the definition of `complete_lattice.independent`. -/
theorem sup_indep_iff_disjoint_erase [DecidableEq ι] :
    s.SupIndep f ↔ ∀, ∀ i ∈ s, ∀, Disjoint (f i) ((s.erase i).sup f) :=
  ⟨fun hs i hi => hs (erase_subset _ _) hi (not_mem_erase _ _), fun hs t ht i hi hit =>
    (hs i hi).mono_right (sup_mono fun j hj => mem_erase.2 ⟨ne_of_mem_of_not_mem hj hit, ht hj⟩)⟩

@[simp]
theorem sup_indep_pair [DecidableEq ι] {i j : ι} (hij : i ≠ j) :
    ({i, j} : Finset ι).SupIndep f ↔ Disjoint (f i) (f j) :=
  ⟨fun h =>
    h.PairwiseDisjoint
      (by
        simp )
      (by
        simp )
      hij,
    fun h => by
    rw [sup_indep_iff_disjoint_erase]
    intro k hk
    rw [Finset.mem_insert, Finset.mem_singleton] at hk
    obtain rfl | rfl := hk
    · convert h using 1
      rw [Finset.erase_insert, Finset.sup_singleton]
      simpa using hij
      
    · convert h.symm using 1
      have : ({i, k} : Finset ι).erase k = {i} := by
        ext
        rw [mem_erase, mem_insert, mem_singleton, mem_singleton, and_or_distrib_left, Ne.def, not_and_selfₓ, or_falseₓ,
          and_iff_right_of_imp]
        rintro rfl
        exact hij
      rw [this, Finset.sup_singleton]
      ⟩

theorem sup_indep_univ_bool (f : Bool → α) : (Finset.univ : Finset Bool).SupIndep f ↔ Disjoint (f false) (f true) := by
  have : tt ≠ ff := by
    simp only [← Ne.def, ← not_false_iff]
  exact (sup_indep_pair this).trans Disjoint.comm

@[simp]
theorem sup_indep_univ_fin_two (f : Finₓ 2 → α) : (Finset.univ : Finset (Finₓ 2)).SupIndep f ↔ Disjoint (f 0) (f 1) :=
  by
  have : (0 : Finₓ 2) ≠ 1 := by
    simp
  exact sup_indep_pair this

theorem SupIndep.attach (hs : s.SupIndep f) : s.attach.SupIndep (f ∘ Subtype.val) := by
  intro t ht i _ hi
  classical
  rw [← Finset.sup_image]
  refine' hs (image_subset_iff.2 fun (j : { x // x ∈ s }) _ => j.2) i.2 fun hi' => hi _
  rw [mem_image] at hi'
  obtain ⟨j, hj, hji⟩ := hi'
  rwa [Subtype.ext hji] at hj

end Lattice

section DistribLattice

variable [DistribLattice α] [OrderBot α] {s : Finset ι} {f : ι → α}

theorem sup_indep_iff_pairwise_disjoint : s.SupIndep f ↔ (s : Set ι).PairwiseDisjoint f :=
  ⟨SupIndep.pairwise_disjoint, fun hs t ht i hi hit =>
    disjoint_sup_right.2 fun j hj => hs hi (ht hj) (ne_of_mem_of_not_mem hj hit).symm⟩

alias sup_indep_iff_pairwise_disjoint ↔ sup_indep.pairwise_disjoint _root_.set.pairwise_disjoint.sup_indep

/-- Bind operation for `sup_indep`. -/
theorem SupIndep.sup [DecidableEq ι] {s : Finset ι'} {g : ι' → Finset ι} {f : ι → α}
    (hs : s.SupIndep fun i => (g i).sup f) (hg : ∀, ∀ i' ∈ s, ∀, (g i').SupIndep f) : (s.sup g).SupIndep f := by
  simp_rw [sup_indep_iff_pairwise_disjoint] at hs hg⊢
  rw [sup_eq_bUnion, coe_bUnion]
  exact hs.bUnion_finset hg

/-- Bind operation for `sup_indep`. -/
theorem SupIndep.bUnion [DecidableEq ι] {s : Finset ι'} {g : ι' → Finset ι} {f : ι → α}
    (hs : s.SupIndep fun i => (g i).sup f) (hg : ∀, ∀ i' ∈ s, ∀, (g i').SupIndep f) : (s.bUnion g).SupIndep f := by
  rw [← sup_eq_bUnion]
  exact hs.sup hg

end DistribLattice

end Finset

/-! ### On complete lattices via `has_Sup.Sup` -/


namespace CompleteLattice

variable [CompleteLattice α]

open Set Function

/-- An independent set of elements in a complete lattice is one in which every element is disjoint
  from the `Sup` of the rest. -/
def SetIndependent (s : Set α) : Prop :=
  ∀ ⦃a⦄, a ∈ s → Disjoint a (sup (s \ {a}))

variable {s : Set α} (hs : SetIndependent s)

@[simp]
theorem set_independent_empty : SetIndependent (∅ : Set α) := fun x hx => (Set.not_mem_empty x hx).elim

theorem SetIndependent.mono {t : Set α} (hst : t ⊆ s) : SetIndependent t := fun a ha =>
  (hs (hst ha)).mono_right (Sup_le_Sup (diff_subset_diff_left hst))

/-- If the elements of a set are independent, then any pair within that set is disjoint. -/
theorem SetIndependent.pairwise_disjoint : s.PairwiseDisjoint id := fun x hx y hy h =>
  disjoint_Sup_right (hs hx) ((mem_diff y).mpr ⟨hy, h.symm⟩)

theorem set_independent_pair {a b : α} (hab : a ≠ b) : SetIndependent ({a, b} : Set α) ↔ Disjoint a b := by
  constructor
  · intro h
    exact h.pairwise_disjoint (mem_insert _ _) (mem_insert_of_mem _ (mem_singleton _)) hab
    
  · rintro h c ((rfl : c = a) | (rfl : c = b))
    · convert h using 1
      simp [← hab, ← Sup_singleton]
      
    · convert h.symm using 1
      simp [← hab, ← Sup_singleton]
      
    

include hs

/-- If the elements of a set are independent, then any element is disjoint from the `Sup` of some
subset of the rest. -/
theorem SetIndependent.disjoint_Sup {x : α} {y : Set α} (hx : x ∈ s) (hy : y ⊆ s) (hxy : x ∉ y) : Disjoint x (sup y) :=
  by
  have := (hs.mono <| insert_subset.mpr ⟨hx, hy⟩) (mem_insert x _)
  rw [insert_diff_of_mem _ (mem_singleton _), diff_singleton_eq_self hxy] at this
  exact this

omit hs

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (j «expr ≠ » i)
/-- An independent indexed family of elements in a complete lattice is one in which every element
  is disjoint from the `supr` of the rest.

  Example: an indexed family of non-zero elements in a
  vector space is linearly independent iff the indexed family of subspaces they generate is
  independent in this sense.

  Example: an indexed family of submodules of a module is independent in this sense if
  and only the natural map from the direct sum of the submodules to the module is injective. -/
def Independent {ι : Sort _} {α : Type _} [CompleteLattice α] (t : ι → α) : Prop :=
  ∀ i : ι, Disjoint (t i) (⨆ (j) (_ : j ≠ i), t j)

theorem set_independent_iff {α : Type _} [CompleteLattice α] (s : Set α) :
    SetIndependent s ↔ Independent (coe : s → α) := by
  simp_rw [independent, set_independent, SetCoe.forall, Sup_eq_supr]
  refine' forall₂_congrₓ fun a ha => _
  congr 2
  convert supr_subtype.symm
  simp [← supr_and]

variable {t : ι → α} (ht : Independent t)

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (j «expr ≠ » i)
theorem independent_def : Independent t ↔ ∀ i : ι, Disjoint (t i) (⨆ (j) (_ : j ≠ i), t j) :=
  Iff.rfl

theorem independent_def' : Independent t ↔ ∀ i, Disjoint (t i) (sup (t '' { j | j ≠ i })) := by
  simp_rw [Sup_image]
  rfl

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (j «expr ≠ » i)
theorem independent_def'' : Independent t ↔ ∀ i, Disjoint (t i) (sup { a | ∃ (j : _)(_ : j ≠ i), t j = a }) := by
  rw [independent_def']
  tidy

@[simp]
theorem independent_empty (t : Empty → α) : Independent t :=
  fun.

@[simp]
theorem independent_pempty (t : Pempty → α) : Independent t :=
  fun.

/-- If the elements of a set are independent, then any pair within that set is disjoint. -/
theorem Independent.pairwise_disjoint : Pairwise (Disjoint on t) := fun x y h =>
  disjoint_Sup_right (ht x) ⟨y, supr_pos h.symm⟩

theorem Independent.mono {s t : ι → α} (hs : Independent s) (hst : t ≤ s) : Independent t := fun i =>
  (hs i).mono (hst i) <| supr₂_mono fun j _ => hst j

/-- Composing an independent indexed family with an injective function on the index results in
another indepedendent indexed family. -/
theorem Independent.comp {ι ι' : Sort _} {t : ι → α} {f : ι' → ι} (ht : Independent t) (hf : Injective f) :
    Independent (t ∘ f) := fun i =>
  (ht (f i)).mono_right <| by
    refine' (supr_mono fun i => _).trans (supr_comp_le _ f)
    exact supr_const_mono hf.ne

theorem Independent.comp' {ι ι' : Sort _} {t : ι → α} {f : ι' → ι} (ht : independent <| t ∘ f) (hf : Surjective f) :
    Independent t := by
  intro i
  obtain ⟨i', rfl⟩ := hf i
  rw [← hf.supr_comp]
  exact (ht i').mono_right (bsupr_mono fun j' hij => mt (congr_arg f) hij)

theorem Independent.set_independent_range (ht : Independent t) : set_independent <| Range t := by
  rw [set_independent_iff]
  rw [← coe_comp_range_factorization t] at ht
  exact ht.comp' surjective_onto_range

theorem Independent.injective (ht : Independent t) (h_ne_bot : ∀ i, t i ≠ ⊥) : Injective t := by
  intro i j h
  by_contra' contra
  apply h_ne_bot j
  suffices t j ≤ ⨆ (k) (hk : k ≠ i), t k by
    replace ht := (ht i).mono_right this
    rwa [h, disjoint_self] at ht
  replace contra : j ≠ i
  · exact Ne.symm contra
    
  exact le_supr₂ j contra

theorem independent_pair {i j : ι} (hij : i ≠ j) (huniv : ∀ k, k = i ∨ k = j) : Independent t ↔ Disjoint (t i) (t j) :=
  by
  constructor
  · intro h
    exact h.pairwise_disjoint _ _ hij
    
  · rintro h k
    obtain rfl | rfl := huniv k
    · refine' h.mono_right (supr_le fun i => supr_le fun hi => Eq.le _)
      rw [(huniv i).resolve_left hi]
      
    · refine' h.symm.mono_right (supr_le fun j => supr_le fun hj => Eq.le _)
      rw [(huniv j).resolve_right hj]
      
    

/-- Composing an indepedent indexed family with an order isomorphism on the elements results in
another indepedendent indexed family. -/
theorem Independent.map_order_iso {ι : Sort _} {α β : Type _} [CompleteLattice α] [CompleteLattice β] (f : α ≃o β)
    {a : ι → α} (ha : Independent a) : Independent (f ∘ a) := fun i =>
  ((ha i).map_order_iso f).mono_right (f.Monotone.le_map_supr₂ _)

@[simp]
theorem independent_map_order_iso_iff {ι : Sort _} {α β : Type _} [CompleteLattice α] [CompleteLattice β] (f : α ≃o β)
    {a : ι → α} : Independent (f ∘ a) ↔ Independent a :=
  ⟨fun h =>
    have hf : f.symm ∘ f ∘ a = a := congr_arg (· ∘ a) f.left_inv.comp_eq_id
    hf ▸ h.map_order_iso f.symm,
    fun h => h.map_order_iso f⟩

/-- If the elements of a set are independent, then any element is disjoint from the `supr` of some
subset of the rest. -/
theorem Independent.disjoint_bsupr {ι : Type _} {α : Type _} [CompleteLattice α] {t : ι → α} (ht : Independent t)
    {x : ι} {y : Set ι} (hx : x ∉ y) : Disjoint (t x) (⨆ i ∈ y, t i) :=
  Disjoint.mono_right (bsupr_mono fun i hi => (ne_of_mem_of_not_mem hi hx : _)) (ht x)

end CompleteLattice

theorem CompleteLattice.independent_iff_sup_indep [CompleteLattice α] {s : Finset ι} {f : ι → α} :
    CompleteLattice.Independent (f ∘ (coe : s → ι)) ↔ s.SupIndep f := by
  classical
  rw [Finset.sup_indep_iff_disjoint_erase]
  refine' subtype.forall.trans (forall₂_congrₓ fun a b => _)
  rw [Finset.sup_eq_supr]
  congr 2
  refine' supr_subtype.trans _
  congr 1 with x
  simp [← supr_and, ← @supr_comm _ (x ∈ s)]

alias CompleteLattice.independent_iff_sup_indep ↔ CompleteLattice.Independent.sup_indep Finset.SupIndep.independent

/-- A variant of `complete_lattice.independent_iff_sup_indep` for `fintype`s. -/
theorem CompleteLattice.independent_iff_sup_indep_univ [CompleteLattice α] [Fintype ι] {f : ι → α} :
    CompleteLattice.Independent f ↔ Finset.univ.SupIndep f := by
  classical
  simp [← Finset.sup_indep_iff_disjoint_erase, ← CompleteLattice.Independent, ← Finset.sup_eq_supr]

alias CompleteLattice.independent_iff_sup_indep_univ ↔
  CompleteLattice.Independent.sup_indep_univ Finset.SupIndep.independent_of_univ

section Frame

namespace CompleteLattice

variable [Order.Frame α]

theorem set_independent_iff_pairwise_disjoint {s : Set α} : SetIndependent s ↔ s.PairwiseDisjoint id :=
  ⟨SetIndependent.pairwise_disjoint, fun hs i hi => disjoint_Sup_iff.2 fun j hj => hs hi hj.1 <| Ne.symm hj.2⟩

alias set_independent_iff_pairwise_disjoint ↔ _ _root_.set.pairwise_disjoint.set_independent

theorem independent_iff_pairwise_disjoint {f : ι → α} : Independent f ↔ Pairwise (Disjoint on f) :=
  ⟨Independent.pairwise_disjoint, fun hs i =>
    disjoint_supr_iff.2 fun j => disjoint_supr_iff.2 fun hij => hs _ _ hij.symm⟩

end CompleteLattice

end Frame

