/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.Data.Finset.Lattice
import Mathbin.Data.Set.Pairwise
import Mathbin.Order.Hom.Basic

/-!
# The monotone sequence of partial supremums of a sequence

We define `partial_sups : (ℕ → α) → ℕ →o α` inductively. For `f : ℕ → α`, `partial_sups f` is
the sequence `f 0 `, `f 0 ⊔ f 1`, `f 0 ⊔ f 1 ⊔ f 2`, ... The point of this definition is that
* it doesn't need a `⨆`, as opposed to `⨆ (i ≤ n), f i`.
* it doesn't need a `⊥`, as opposed to `(finset.range (n + 1)).sup f`.
* it avoids needing to prove that `finset.range (n + 1)` is nonempty to use `finset.sup'`.

Equivalence with those definitions is shown by `partial_sups_eq_bsupr`, `partial_sups_eq_sup_range`,
`partial_sups_eq_sup'_range` and respectively.

## Notes

One might dispute whether this sequence should start at `f 0` or `⊥`. We choose the former because :
* Starting at `⊥` requires... having a bottom element.
* `λ f n, (finset.range n).sup f` is already effectively the sequence starting at `⊥`.
* If we started at `⊥` we wouldn't have the Galois insertion. See `partial_sups.gi`.

## TODO

One could generalize `partial_sups` to any locally finite bot preorder domain, in place of `ℕ`.
Necessary for the TODO in the module docstring of `order.disjointed`.
-/


variable {α : Type _}

section SemilatticeSup

variable [SemilatticeSup α]

/-- The monotone sequence whose value at `n` is the supremum of the `f m` where `m ≤ n`. -/
def partialSups (f : ℕ → α) : ℕ →o α :=
  ⟨@Nat.rec (fun _ => α) (f 0) fun (n : ℕ) (a : α) => a⊔f (n + 1), monotone_nat_of_le_succ fun n => le_sup_left⟩

@[simp]
theorem partial_sups_zero (f : ℕ → α) : partialSups f 0 = f 0 :=
  rfl

@[simp]
theorem partial_sups_succ (f : ℕ → α) (n : ℕ) : partialSups f (n + 1) = partialSups f n⊔f (n + 1) :=
  rfl

theorem le_partial_sups_of_le (f : ℕ → α) {m n : ℕ} (h : m ≤ n) : f m ≤ partialSups f n := by
  induction' n with n ih
  · cases h
    exact le_rfl
    
  · cases' h with h h
    · exact le_sup_right
      
    · exact (ih h).trans le_sup_left
      
    

theorem le_partial_sups (f : ℕ → α) : f ≤ partialSups f := fun n => le_partial_sups_of_le f le_rfl

theorem partial_sups_le (f : ℕ → α) (n : ℕ) (a : α) (w : ∀ m, m ≤ n → f m ≤ a) : partialSups f n ≤ a := by
  induction' n with n ih
  · apply w 0 le_rfl
    
  · exact sup_le (ih fun m p => w m (Nat.le_succ_of_leₓ p)) (w (n + 1) le_rfl)
    

theorem Monotone.partial_sups_eq {f : ℕ → α} (hf : Monotone f) : (partialSups f : ℕ → α) = f := by
  ext n
  induction' n with n ih
  · rfl
    
  · rw [partial_sups_succ, ih, sup_eq_right.2 (hf (Nat.le_succₓ _))]
    

theorem partial_sups_mono : Monotone (partialSups : (ℕ → α) → ℕ →o α) := by
  rintro f g h n
  induction' n with n ih
  · exact h 0
    
  · exact sup_le_sup ih (h _)
    

/-- `partial_sups` forms a Galois insertion with the coercion from monotone functions to functions.
-/
def partialSups.gi : GaloisInsertion (partialSups : (ℕ → α) → ℕ →o α) coeFn where
  choice := fun f h =>
    ⟨f, by
      convert (partialSups f).Monotone
      exact (le_partial_sups f).antisymm h⟩
  gc := fun f g => by
    refine' ⟨(le_partial_sups f).trans, fun h => _⟩
    convert partial_sups_mono h
    exact OrderHom.ext _ _ g.monotone.partial_sups_eq.symm
  le_l_u := fun f => le_partial_sups f
  choice_eq := fun f h => OrderHom.ext _ _ ((le_partial_sups f).antisymm h)

theorem partial_sups_eq_sup'_range (f : ℕ → α) (n : ℕ) :
    partialSups f n = (Finset.range (n + 1)).sup' ⟨n, Finset.self_mem_range_succ n⟩ f := by
  induction' n with n ih
  · simp
    
  · dsimp' [← partialSups]  at ih⊢
    simp_rw [@Finset.range_succ n.succ]
    rw [ih, Finset.sup'_insert, sup_comm]
    

end SemilatticeSup

theorem partial_sups_eq_sup_range [SemilatticeSup α] [OrderBot α] (f : ℕ → α) (n : ℕ) :
    partialSups f n = (Finset.range (n + 1)).sup f := by
  induction' n with n ih
  · simp
    
  · dsimp' [← partialSups]  at ih⊢
    rw [Finset.range_succ, Finset.sup_insert, sup_comm, ih]
    

/- Note this lemma requires a distributive lattice, so is not useful (or true) in situations such as
submodules. -/
theorem partial_sups_disjoint_of_disjoint [DistribLattice α] [OrderBot α] (f : ℕ → α) (h : Pairwise (Disjoint on f))
    {m n : ℕ} (hmn : m < n) : Disjoint (partialSups f m) (f n) := by
  induction' m with m ih
  · exact h 0 n hmn.ne
    
  · rw [partial_sups_succ, disjoint_sup_left]
    exact ⟨ih (Nat.lt_of_succ_ltₓ hmn), h (m + 1) n hmn.ne⟩
    

section CompleteLattice

variable [CompleteLattice α]

theorem partial_sups_eq_bsupr (f : ℕ → α) (n : ℕ) : partialSups f n = ⨆ i ≤ n, f i := by
  rw [partial_sups_eq_sup_range, Finset.sup_eq_supr]
  congr
  ext a
  exact
    supr_congr_Prop
      (by
        rw [Finset.mem_range, Nat.lt_succ_iffₓ])
      fun _ => rfl

@[simp]
theorem supr_partial_sups_eq (f : ℕ → α) : (⨆ n, partialSups f n) = ⨆ n, f n := by
  refine' (supr_le fun n => _).antisymm (supr_mono <| le_partial_sups f)
  rw [partial_sups_eq_bsupr]
  exact supr₂_le_supr _ _

theorem supr_le_supr_of_partial_sups_le_partial_sups {f g : ℕ → α} (h : partialSups f ≤ partialSups g) :
    (⨆ n, f n) ≤ ⨆ n, g n := by
  rw [← supr_partial_sups_eq f, ← supr_partial_sups_eq g]
  exact supr_mono h

theorem supr_eq_supr_of_partial_sups_eq_partial_sups {f g : ℕ → α} (h : partialSups f = partialSups g) :
    (⨆ n, f n) = ⨆ n, g n := by
  simp_rw [← supr_partial_sups_eq f, ← supr_partial_sups_eq g, h]

end CompleteLattice

