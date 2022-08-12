/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Reid Barton
-/
import Mathbin.Topology.Separation

/-!
# The shrinking lemma

In this file we prove a few versions of the shrinking lemma. The lemma says that in a normal
topological space a point finite open covering can be “shrunk”: for a point finite open covering
`u : ι → set X` there exists a refinement `v : ι → set X` such that `closure (v i) ⊆ u i`.

For finite or countable coverings this lemma can be proved without the axiom of choice, see
[ncatlab](https://ncatlab.org/nlab/show/shrinking+lemma) for details. We only formalize the most
general result that works for any covering but needs the axiom of choice.

We prove two versions of the lemma:

* `exists_subset_Union_closure_subset` deals with a covering of a closed set in a normal space;
* `exists_Union_eq_closure_subset` deals with a covering of the whole space.

## Tags

normal space, shrinking lemma
-/


open Set Function

open Classical

noncomputable section

variable {ι X : Type _} [TopologicalSpace X] [NormalSpace X]

namespace ShrinkingLemma

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (i «expr ∉ » carrier)
/-- Auxiliary definition for the proof of `shrinking_lemma`. A partial refinement of a covering
`⋃ i, u i` of a set `s` is a map `v : ι → set X` and a set `carrier : set ι` such that

* `s ⊆ ⋃ i, v i`;
* all `v i` are open;
* if `i ∈ carrier v`, then `closure (v i) ⊆ u i`;
* if `i ∉ carrier`, then `v i = u i`.

This type is equipped with the folowing partial order: `v ≤ v'` if `v.carrier ⊆ v'.carrier`
and `v i = v' i` for `i ∈ v.carrier`. We will use Zorn's lemma to prove that this type has
a maximal element, then show that the maximal element must have `carrier = univ`. -/
-- the trivial refinement needs `u` to be a covering
@[nolint has_inhabited_instance]
structure PartialRefinement (u : ι → Set X) (s : Set X) where
  toFun : ι → Set X
  Carrier : Set ι
  is_open' : ∀ i, IsOpen (to_fun i)
  subset_Union' : s ⊆ ⋃ i, to_fun i
  closure_subset' : ∀, ∀ i ∈ carrier, ∀, Closure (to_fun i) ⊆ u i
  apply_eq' : ∀ (i) (_ : i ∉ carrier), to_fun i = u i

namespace PartialRefinement

variable {u : ι → Set X} {s : Set X}

instance : CoeFun (PartialRefinement u s) fun _ => ι → Set X :=
  ⟨ToFun⟩

theorem subset_Union (v : PartialRefinement u s) : s ⊆ ⋃ i, v i :=
  v.subset_Union'

theorem closure_subset (v : PartialRefinement u s) {i : ι} (hi : i ∈ v.Carrier) : Closure (v i) ⊆ u i :=
  v.closure_subset' i hi

theorem apply_eq (v : PartialRefinement u s) {i : ι} (hi : i ∉ v.Carrier) : v i = u i :=
  v.apply_eq' i hi

protected theorem is_open (v : PartialRefinement u s) (i : ι) : IsOpen (v i) :=
  v.is_open' i

protected theorem subset (v : PartialRefinement u s) (i : ι) : v i ⊆ u i :=
  if h : i ∈ v.Carrier then Subset.trans subset_closure (v.closure_subset h) else (v.apply_eq h).le

attribute [ext] partial_refinement

instance : PartialOrderₓ (PartialRefinement u s) where
  le := fun v₁ v₂ => v₁.Carrier ⊆ v₂.Carrier ∧ ∀, ∀ i ∈ v₁.Carrier, ∀, v₁ i = v₂ i
  le_refl := fun v => ⟨Subset.refl _, fun _ _ => rfl⟩
  le_trans := fun v₁ v₂ v₃ h₁₂ h₂₃ => ⟨Subset.trans h₁₂.1 h₂₃.1, fun i hi => (h₁₂.2 i hi).trans (h₂₃.2 i <| h₁₂.1 hi)⟩
  le_antisymm := fun v₁ v₂ h₁₂ h₂₁ =>
    have hc : v₁.Carrier = v₂.Carrier := Subset.antisymm h₁₂.1 h₂₁.1
    ext _ _
      (funext fun x =>
        if hx : x ∈ v₁.Carrier then h₁₂.2 _ hx else (v₁.apply_eq hx).trans (Eq.symm <| v₂.apply_eq <| hc ▸ hx))
      hc

/-- If two partial refinements `v₁`, `v₂` belong to a chain (hence, they are comparable)
and `i` belongs to the carriers of both partial refinements, then `v₁ i = v₂ i`. -/
theorem apply_eq_of_chain {c : Set (PartialRefinement u s)} (hc : IsChain (· ≤ ·) c) {v₁ v₂} (h₁ : v₁ ∈ c) (h₂ : v₂ ∈ c)
    {i} (hi₁ : i ∈ v₁.Carrier) (hi₂ : i ∈ v₂.Carrier) : v₁ i = v₂ i := by
  wlog hle : v₁ ≤ v₂ := hc.total h₁ h₂ using v₁ v₂, v₂ v₁
  exact hle.2 _ hi₁

/-- The carrier of the least upper bound of a non-empty chain of partial refinements
is the union of their carriers. -/
def ChainSupCarrier (c : Set (PartialRefinement u s)) : Set ι :=
  ⋃ v ∈ c, Carrier v

/-- Choice of an element of a nonempty chain of partial refinements. If `i` belongs to one of
`carrier v`, `v ∈ c`, then `find c ne i` is one of these partial refinements. -/
def find (c : Set (PartialRefinement u s)) (ne : c.Nonempty) (i : ι) : PartialRefinement u s :=
  if hi : ∃ v ∈ c, i ∈ Carrier v then hi.some else Ne.some

theorem find_mem {c : Set (PartialRefinement u s)} (i : ι) (ne : c.Nonempty) : find c Ne i ∈ c := by
  rw [find]
  split_ifs
  exacts[h.some_spec.fst, ne.some_spec]

theorem mem_find_carrier_iff {c : Set (PartialRefinement u s)} {i : ι} (ne : c.Nonempty) :
    i ∈ (find c Ne i).Carrier ↔ i ∈ ChainSupCarrier c := by
  rw [find]
  split_ifs
  · have : i ∈ h.some.carrier ∧ i ∈ chain_Sup_carrier c := ⟨h.some_spec.snd, mem_Union₂.2 h⟩
    simp only [← this]
    
  · have : i ∉ ne.some.carrier ∧ i ∉ chain_Sup_carrier c := ⟨fun hi => h ⟨_, ne.some_spec, hi⟩, mt mem_Union₂.1 h⟩
    simp only [← this]
    

theorem find_apply_of_mem {c : Set (PartialRefinement u s)} (hc : IsChain (· ≤ ·) c) (ne : c.Nonempty) {i v}
    (hv : v ∈ c) (hi : i ∈ Carrier v) : find c Ne i i = v i :=
  apply_eq_of_chain hc (find_mem _ _) hv ((mem_find_carrier_iff _).2 <| mem_Union₂.2 ⟨v, hv, hi⟩) hi

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (i «expr ∉ » chain_Sup_carrier c)
/-- Least upper bound of a nonempty chain of partial refinements. -/
def chainSup (c : Set (PartialRefinement u s)) (hc : IsChain (· ≤ ·) c) (ne : c.Nonempty)
    (hfin : ∀, ∀ x ∈ s, ∀, { i | x ∈ u i }.Finite) (hU : s ⊆ ⋃ i, u i) : PartialRefinement u s := by
  refine'
    ⟨fun i => find c Ne i i, chain_Sup_carrier c, fun i => (find _ _ _).IsOpen i, fun x hxs => mem_Union.2 _,
      fun i hi => (find c Ne i).closure_subset ((mem_find_carrier_iff _).2 hi), fun i hi =>
      (find c Ne i).apply_eq (mt (mem_find_carrier_iff _).1 hi)⟩
  rcases em (∃ (i : _)(_ : i ∉ chain_Sup_carrier c), x ∈ u i) with (⟨i, hi, hxi⟩ | hx)
  · use i
    rwa [(find c Ne i).apply_eq (mt (mem_find_carrier_iff _).1 hi)]
    
  · simp_rw [not_exists, not_imp_not, chain_Sup_carrier, mem_Union₂] at hx
    have : Nonempty (partial_refinement u s) := ⟨ne.some⟩
    choose! v hvc hiv using hx
    rcases(hfin x hxs).exists_maximal_wrt v _ (mem_Union.1 (hU hxs)) with
      ⟨i, hxi : x ∈ u i, hmax : ∀ j, x ∈ u j → v i ≤ v j → v i = v j⟩
    rcases mem_Union.1 ((v i).subset_Union hxs) with ⟨j, hj⟩
    use j
    have hj' : x ∈ u j := (v i).Subset _ hj
    have : v j ≤ v i := (hc.total (hvc _ hxi) (hvc _ hj')).elim (fun h => (hmax j hj' h).Ge) id
    rwa [find_apply_of_mem hc Ne (hvc _ hxi) (this.1 <| hiv _ hj')]
    

/-- `chain_Sup hu c hc ne hfin hU` is an upper bound of the chain `c`. -/
theorem le_chain_Sup {c : Set (PartialRefinement u s)} (hc : IsChain (· ≤ ·) c) (ne : c.Nonempty)
    (hfin : ∀, ∀ x ∈ s, ∀, { i | x ∈ u i }.Finite) (hU : s ⊆ ⋃ i, u i) {v} (hv : v ∈ c) :
    v ≤ chainSup c hc Ne hfin hU :=
  ⟨fun i hi => mem_bUnion hv hi, fun i hi => (find_apply_of_mem hc _ hv hi).symm⟩

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (j «expr ≠ » i)
-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (j «expr ≠ » i)
-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (j «expr ≠ » i)
/-- If `s` is a closed set, `v` is a partial refinement, and `i` is an index such that
`i ∉ v.carrier`, then there exists a partial refinement that is strictly greater than `v`. -/
theorem exists_gt (v : PartialRefinement u s) (hs : IsClosed s) (i : ι) (hi : i ∉ v.Carrier) :
    ∃ v' : PartialRefinement u s, v < v' := by
  have I : (s ∩ ⋂ (j) (_ : j ≠ i), v jᶜ) ⊆ v i := by
    simp only [← subset_def, ← mem_inter_eq, ← mem_Inter, ← and_imp]
    intro x hxs H
    rcases mem_Union.1 (v.subset_Union hxs) with ⟨j, hj⟩
    exact (em (j = i)).elim (fun h => h ▸ hj) fun h => (H j h hj).elim
  have C : IsClosed (s ∩ ⋂ (j) (_ : j ≠ i), v jᶜ) :=
    IsClosed.inter hs (is_closed_bInter fun _ _ => is_closed_compl_iff.2 <| v.is_open _)
  rcases normal_exists_closure_subset C (v.is_open i) I with ⟨vi, ovi, hvi, cvi⟩
  refine' ⟨⟨update v i vi, insert i v.carrier, _, _, _, _⟩, _, _⟩
  · intro j
    by_cases' h : j = i <;> simp [← h, ← ovi, ← v.is_open]
    
  · refine' fun x hx => mem_Union.2 _
    rcases em (∃ (j : _)(_ : j ≠ i), x ∈ v j) with (⟨j, hji, hj⟩ | h)
    · use j
      rwa [update_noteq hji]
      
    · push_neg  at h
      use i
      rw [update_same]
      exact hvi ⟨hx, mem_bInter h⟩
      
    
  · rintro j (rfl | hj)
    · rwa [update_same, ← v.apply_eq hi]
      
    · rw [update_noteq (ne_of_mem_of_not_mem hj hi)]
      exact v.closure_subset hj
      
    
  · intro j hj
    rw [mem_insert_iff, not_or_distrib] at hj
    rw [update_noteq hj.1, v.apply_eq hj.2]
    
  · refine' ⟨subset_insert _ _, fun j hj => _⟩
    exact (update_noteq (ne_of_mem_of_not_mem hj hi) _ _).symm
    
  · exact fun hle => hi (hle.1 <| mem_insert _ _)
    

end PartialRefinement

end ShrinkingLemma

open ShrinkingLemma

variable {u : ι → Set X} {s : Set X}

/-- Shrinking lemma. A point-finite open cover of a closed subset of a normal space can be "shrunk"
to a new open cover so that the closure of each new open set is contained in the corresponding
original open set. -/
theorem exists_subset_Union_closure_subset (hs : IsClosed s) (uo : ∀ i, IsOpen (u i))
    (uf : ∀, ∀ x ∈ s, ∀, { i | x ∈ u i }.Finite) (us : s ⊆ ⋃ i, u i) :
    ∃ v : ι → Set X, s ⊆ Union v ∧ (∀ i, IsOpen (v i)) ∧ ∀ i, Closure (v i) ⊆ u i := by
  classical
  have : Nonempty (partial_refinement u s) := ⟨⟨u, ∅, uo, us, fun _ => False.elim, fun _ _ => rfl⟩⟩
  have : ∀ c : Set (partial_refinement u s), IsChain (· ≤ ·) c → c.Nonempty → ∃ ub, ∀, ∀ v ∈ c, ∀, v ≤ ub :=
    fun c hc ne => ⟨partial_refinement.chain_Sup c hc Ne uf us, fun v hv => partial_refinement.le_chain_Sup _ _ _ _ hv⟩
  rcases zorn_nonempty_partial_order this with ⟨v, hv⟩
  suffices : ∀ i, i ∈ v.carrier
  exact ⟨v, v.subset_Union, fun i => v.is_open _, fun i => v.closure_subset (this i)⟩
  contrapose! hv
  rcases hv with ⟨i, hi⟩
  rcases v.exists_gt hs i hi with ⟨v', hlt⟩
  exact ⟨v', hlt.le, hlt.ne'⟩

/-- Shrinking lemma. A point-finite open cover of a closed subset of a normal space can be "shrunk"
to a new closed cover so that each new closed set is contained in the corresponding original open
set. See also `exists_subset_Union_closure_subset` for a stronger statement. -/
theorem exists_subset_Union_closed_subset (hs : IsClosed s) (uo : ∀ i, IsOpen (u i))
    (uf : ∀, ∀ x ∈ s, ∀, { i | x ∈ u i }.Finite) (us : s ⊆ ⋃ i, u i) :
    ∃ v : ι → Set X, s ⊆ Union v ∧ (∀ i, IsClosed (v i)) ∧ ∀ i, v i ⊆ u i :=
  let ⟨v, hsv, hvo, hv⟩ := exists_subset_Union_closure_subset hs uo uf us
  ⟨fun i => Closure (v i), Subset.trans hsv (Union_mono fun i => subset_closure), fun i => is_closed_closure, hv⟩

/-- Shrinking lemma. A point-finite open cover of a closed subset of a normal space can be "shrunk"
to a new open cover so that the closure of each new open set is contained in the corresponding
original open set. -/
theorem exists_Union_eq_closure_subset (uo : ∀ i, IsOpen (u i)) (uf : ∀ x, { i | x ∈ u i }.Finite)
    (uU : (⋃ i, u i) = univ) : ∃ v : ι → Set X, Union v = univ ∧ (∀ i, IsOpen (v i)) ∧ ∀ i, Closure (v i) ⊆ u i :=
  let ⟨v, vU, hv⟩ := exists_subset_Union_closure_subset is_closed_univ uo (fun x _ => uf x) uU.Ge
  ⟨v, univ_subset_iff.1 vU, hv⟩

/-- Shrinking lemma. A point-finite open cover of a closed subset of a normal space can be "shrunk"
to a new closed cover so that each of the new closed sets is contained in the corresponding
original open set. See also `exists_Union_eq_closure_subset` for a stronger statement. -/
theorem exists_Union_eq_closed_subset (uo : ∀ i, IsOpen (u i)) (uf : ∀ x, { i | x ∈ u i }.Finite)
    (uU : (⋃ i, u i) = univ) : ∃ v : ι → Set X, Union v = univ ∧ (∀ i, IsClosed (v i)) ∧ ∀ i, v i ⊆ u i :=
  let ⟨v, vU, hv⟩ := exists_subset_Union_closed_subset is_closed_univ uo (fun x _ => uf x) uU.Ge
  ⟨v, univ_subset_iff.1 vU, hv⟩

