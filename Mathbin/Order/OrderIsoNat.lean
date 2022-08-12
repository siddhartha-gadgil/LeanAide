/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathbin.Data.Nat.Lattice
import Mathbin.Logic.Denumerable
import Mathbin.Logic.Function.Iterate
import Mathbin.Order.Hom.Basic
import Mathbin.Tactic.Congrm

/-!
# Relation embeddings from the naturals

This file allows translation from monotone functions `ℕ → α` to order embeddings `ℕ ↪ α` and
defines the limit value of an eventually-constant sequence.

## Main declarations

* `nat_lt`/`nat_gt`: Make an order embedding `ℕ ↪ α` from an increasing/decreasing function `ℕ → α`.
* `monotonic_sequence_limit`: The limit of an eventually-constant monotone sequence `ℕ →o α`.
* `monotonic_sequence_limit_index`: The index of the first occurence of `monotonic_sequence_limit`
  in the sequence.
-/


variable {α : Type _}

namespace RelEmbedding

variable {r : α → α → Prop} [IsStrictOrder α r]

/-- If `f` is a strictly `r`-increasing sequence, then this returns `f` as an order embedding. -/
def natLt (f : ℕ → α) (H : ∀ n : ℕ, r (f n) (f (n + 1))) : ((· < ·) : ℕ → ℕ → Prop) ↪r r :=
  ofMonotone f <| Nat.rel_of_forall_rel_succ_of_lt r H

@[simp]
theorem nat_lt_apply {f : ℕ → α} {H : ∀ n : ℕ, r (f n) (f (n + 1))} {n : ℕ} : natLt f H n = f n :=
  rfl

/-- If `f` is a strictly `r`-decreasing sequence, then this returns `f` as an order embedding. -/
def natGt (f : ℕ → α) (H : ∀ n : ℕ, r (f (n + 1)) (f n)) : ((· > ·) : ℕ → ℕ → Prop) ↪r r :=
  have := IsStrictOrder.swap r
  RelEmbedding.swap (nat_lt f H)

theorem well_founded_iff_no_descending_seq : WellFounded r ↔ IsEmpty (((· > ·) : ℕ → ℕ → Prop) ↪r r) :=
  ⟨fun ⟨h⟩ =>
    ⟨fun ⟨f, o⟩ =>
      suffices ∀ a, Acc r a → ∀ n, a ≠ f n from this (f 0) (h _) 0 rfl
      fun a ac => by
      induction' ac with a _ IH
      rintro n rfl
      exact IH (f (n + 1)) (o.2 (Nat.lt_succ_selfₓ _)) _ rfl⟩,
    fun E =>
    ⟨fun a =>
      Classical.by_contradiction fun na =>
        let ⟨f, h⟩ :=
          Classical.axiom_of_choice <|
            show ∀ x : { a // ¬Acc r a }, ∃ y : { a // ¬Acc r a }, r y.1 x.1 from fun ⟨x, h⟩ =>
              Classical.by_contradiction fun hn =>
                h <| ⟨_, fun y h => Classical.by_contradiction fun na => hn ⟨⟨y, na⟩, h⟩⟩
        E.elim'
          ((natGt fun n => ((f^[n]) ⟨a, na⟩).1) fun n => by
            rw [Function.iterate_succ']
            apply h)⟩⟩

end RelEmbedding

namespace Nat

variable (s : Set ℕ) [Infinite s]

/-- An order embedding from `ℕ` to itself with a specified range -/
def orderEmbeddingOfSet [DecidablePred (· ∈ s)] : ℕ ↪o ℕ :=
  (RelEmbedding.orderEmbeddingOfLtEmbedding
        (RelEmbedding.natLt (Nat.Subtype.ofNat s) fun n => Nat.Subtype.lt_succ_self _)).trans
    (OrderEmbedding.subtype s)

/-- `nat.subtype.of_nat` as an order isomorphism between `ℕ` and an infinite subset. See also
`nat.nth` for a version where the subset may be finite. -/
noncomputable def Subtype.orderIsoOfNat : ℕ ≃o s := by
  classical
  exact
    RelIso.ofSurjective
      (RelEmbedding.orderEmbeddingOfLtEmbedding
        (RelEmbedding.natLt (Nat.Subtype.ofNat s) fun n => Nat.Subtype.lt_succ_self _))
      Nat.Subtype.of_nat_surjective

variable {s}

@[simp]
theorem coe_order_embedding_of_set : ⇑(orderEmbeddingOfSet s) = coe ∘ Subtype.ofNat s :=
  rfl

theorem order_embedding_of_set_apply {n : ℕ} : orderEmbeddingOfSet s n = Subtype.ofNat s n :=
  rfl

@[simp]
theorem Subtype.order_iso_of_nat_apply {n : ℕ} : Subtype.orderIsoOfNat s n = Subtype.ofNat s n := by
  simp [← subtype.order_iso_of_nat]

variable (s)

theorem order_embedding_of_set_range : Set.Range (Nat.orderEmbeddingOfSet s) = s :=
  subtype.coe_comp_of_nat_range

theorem exists_subseq_of_forall_mem_union {s t : Set α} (e : ℕ → α) (he : ∀ n, e n ∈ s ∪ t) :
    ∃ g : ℕ ↪o ℕ, (∀ n, e (g n) ∈ s) ∨ ∀ n, e (g n) ∈ t := by
  classical
  have : Infinite (e ⁻¹' s) ∨ Infinite (e ⁻¹' t) := by
    simp only [← Set.infinite_coe_iff, Set.infinite_union, Set.preimage_union, ←
      Set.eq_univ_of_forall fun n => Set.mem_preimage.2 (he n), ← Set.infinite_univ]
  cases this
  exacts[⟨Nat.orderEmbeddingOfSet (e ⁻¹' s), Or.inl fun n => (Nat.Subtype.ofNat (e ⁻¹' s) _).2⟩,
    ⟨Nat.orderEmbeddingOfSet (e ⁻¹' t), Or.inr fun n => (Nat.Subtype.ofNat (e ⁻¹' t) _).2⟩]

end Nat

theorem exists_increasing_or_nonincreasing_subseq' (r : α → α → Prop) (f : ℕ → α) :
    ∃ g : ℕ ↪o ℕ, (∀ n : ℕ, r (f (g n)) (f (g (n + 1)))) ∨ ∀ m n : ℕ, m < n → ¬r (f (g m)) (f (g n)) := by
  classical
  let bad : Set ℕ := { m | ∀ n, m < n → ¬r (f m) (f n) }
  by_cases' hbad : Infinite bad
  · have := hbad
    refine' ⟨Nat.orderEmbeddingOfSet bad, Or.intro_rightₓ _ fun m n mn => _⟩
    have h := Set.mem_range_self m
    rw [Nat.order_embedding_of_set_range bad] at h
    exact h _ ((OrderEmbedding.lt_iff_lt _).2 mn)
    
  · rw [Set.infinite_coe_iff, Set.Infinite, not_not] at hbad
    obtain ⟨m, hm⟩ : ∃ m, ∀ n, m ≤ n → ¬n ∈ bad := by
      by_cases' he : hbad.to_finset.nonempty
      · refine'
          ⟨(hbad.to_finset.max' he).succ, fun n hn nbad =>
            Nat.not_succ_le_selfₓ _ (hn.trans (hbad.to_finset.le_max' n (hbad.mem_to_finset.2 nbad)))⟩
        
      · exact ⟨0, fun n hn nbad => he ⟨n, hbad.mem_to_finset.2 nbad⟩⟩
        
    have h : ∀ n : ℕ, ∃ n' : ℕ, n < n' ∧ r (f (n + m)) (f (n' + m)) := by
      intro n
      have h := hm _ (le_add_of_nonneg_left n.zero_le)
      simp only [← exists_prop, ← not_not, ← Set.mem_set_of_eq, ← not_forall] at h
      obtain ⟨n', hn1, hn2⟩ := h
      obtain ⟨x, hpos, rfl⟩ := exists_pos_add_of_lt hn1
      refine' ⟨n + x, add_lt_add_left hpos n, _⟩
      rw [add_assocₓ, add_commₓ x m, ← add_assocₓ]
      exact hn2
    let g' : ℕ → ℕ := @Nat.rec (fun _ => ℕ) m fun n gn => Nat.findₓ (h gn)
    exact
      ⟨(RelEmbedding.natLt (fun n => g' n + m) fun n =>
            Nat.add_lt_add_rightₓ (Nat.find_specₓ (h (g' n))).1 m).orderEmbeddingOfLtEmbedding,
        Or.intro_left _ fun n => (Nat.find_specₓ (h (g' n))).2⟩
    

/-- This is the infinitary Erdős–Szekeres theorem, and an important lemma in the usual proof of
    Bolzano-Weierstrass for `ℝ`. -/
theorem exists_increasing_or_nonincreasing_subseq (r : α → α → Prop) [IsTrans α r] (f : ℕ → α) :
    ∃ g : ℕ ↪o ℕ, (∀ m n : ℕ, m < n → r (f (g m)) (f (g n))) ∨ ∀ m n : ℕ, m < n → ¬r (f (g m)) (f (g n)) := by
  obtain ⟨g, hr | hnr⟩ := exists_increasing_or_nonincreasing_subseq' r f
  · refine' ⟨g, Or.intro_left _ fun m n mn => _⟩
    obtain ⟨x, rfl⟩ := le_iff_exists_add.1 (Nat.succ_le_iff.2 mn)
    induction' x with x ih
    · apply hr
      
    · apply IsTrans.trans _ _ _ _ (hr _)
      exact ih (lt_of_lt_of_leₓ m.lt_succ_self (Nat.le_add_rightₓ _ _))
      
    
  · exact ⟨g, Or.intro_rightₓ _ hnr⟩
    

theorem WellFounded.monotone_chain_condition' [Preorderₓ α] :
    WellFounded ((· > ·) : α → α → Prop) ↔ ∀ a : ℕ →o α, ∃ n, ∀ m, n ≤ m → ¬a n < a m := by
  refine' ⟨fun h a => _, fun h => _⟩
  · have hne : (Set.Range a).Nonempty :=
      ⟨a 0, by
        simp ⟩
    obtain ⟨x, ⟨n, rfl⟩, H⟩ := h.has_min _ hne
    exact ⟨n, fun m hm => H _ (Set.mem_range_self _)⟩
    
  · refine' RelEmbedding.well_founded_iff_no_descending_seq.2 ⟨fun a => _⟩
    obtain ⟨n, hn⟩ := h (a.swap : ((· < ·) : ℕ → ℕ → Prop) →r ((· < ·) : α → α → Prop)).toOrderHom
    exact hn n.succ n.lt_succ_self.le ((RelEmbedding.map_rel_iff _).2 n.lt_succ_self)
    

-- ./././Mathport/Syntax/Translate/Basic.lean:647:16: unsupported tactic `congrm #[[expr ∀ a, «expr∃ , »((n), ∀ (m) (h : «expr ≤ »(n, m)), (_ : exprProp()))]]
/-- The "monotone chain condition" below is sometimes a convenient form of well foundedness. -/
theorem WellFounded.monotone_chain_condition [PartialOrderₓ α] :
    WellFounded ((· > ·) : α → α → Prop) ↔ ∀ a : ℕ →o α, ∃ n, ∀ m, n ≤ m → a n = a m :=
  WellFounded.monotone_chain_condition'.trans <| by
    trace
      "./././Mathport/Syntax/Translate/Basic.lean:647:16: unsupported tactic `congrm #[[expr ∀ a, «expr∃ , »((n), ∀ (m) (h : «expr ≤ »(n, m)), (_ : exprProp()))]]"
    rw [lt_iff_le_and_ne]
    simp [← a.mono h]

/-- Given an eventually-constant monotone sequence `a₀ ≤ a₁ ≤ a₂ ≤ ...` in a partially-ordered
type, `monotonic_sequence_limit_index a` is the least natural number `n` for which `aₙ` reaches the
constant value. For sequences that are not eventually constant, `monotonic_sequence_limit_index a`
is defined, but is a junk value. -/
noncomputable def monotonicSequenceLimitIndex [Preorderₓ α] (a : ℕ →o α) : ℕ :=
  inf { n | ∀ m, n ≤ m → a n = a m }

/-- The constant value of an eventually-constant monotone sequence `a₀ ≤ a₁ ≤ a₂ ≤ ...` in a
partially-ordered type. -/
noncomputable def monotonicSequenceLimit [Preorderₓ α] (a : ℕ →o α) :=
  a (monotonicSequenceLimitIndex a)

theorem WellFounded.supr_eq_monotonic_sequence_limit [CompleteLattice α] (h : WellFounded ((· > ·) : α → α → Prop))
    (a : ℕ →o α) : supr a = monotonicSequenceLimit a := by
  suffices (⨆ m : ℕ, a m) ≤ monotonicSequenceLimit a by
    exact le_antisymmₓ this (le_supr a _)
  apply supr_le
  intro m
  by_cases' hm : m ≤ monotonicSequenceLimitIndex a
  · exact a.monotone hm
    
  · replace hm := le_of_not_leₓ hm
    let S := { n | ∀ m, n ≤ m → a n = a m }
    have hInf : Inf S ∈ S := by
      refine' Nat.Inf_mem _
      rw [WellFounded.monotone_chain_condition] at h
      exact h a
    change Inf S ≤ m at hm
    change a m ≤ a (Inf S)
    rw [hInf m hm]
    

