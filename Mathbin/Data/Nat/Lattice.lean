/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Floris van Doorn, Gabriel Ebner, Yury Kudryashov
-/
import Mathbin.Data.Nat.PartEnat
import Mathbin.Order.ConditionallyCompleteLattice

/-!
# Conditionally complete linear order structure on `ℕ`

In this file we

* define a `conditionally_complete_linear_order_bot` structure on `ℕ`;
* define a `complete_linear_order` structure on `part_enat`;
* prove a few lemmas about `supr`/`infi`/`set.Union`/`set.Inter` and natural numbers.
-/


open Set

namespace Nat

open Classical

noncomputable instance : HasInfₓ ℕ :=
  ⟨fun s => if h : ∃ n, n ∈ s then @Nat.findₓ (fun n => n ∈ s) _ h else 0⟩

noncomputable instance : HasSupₓ ℕ :=
  ⟨fun s => if h : ∃ n, ∀, ∀ a ∈ s, ∀, a ≤ n then @Nat.findₓ (fun n => ∀, ∀ a ∈ s, ∀, a ≤ n) _ h else 0⟩

theorem Inf_def {s : Set ℕ} (h : s.Nonempty) : inf s = @Nat.findₓ (fun n => n ∈ s) _ h :=
  dif_pos _

theorem Sup_def {s : Set ℕ} (h : ∃ n, ∀, ∀ a ∈ s, ∀, a ≤ n) : sup s = @Nat.findₓ (fun n => ∀, ∀ a ∈ s, ∀, a ≤ n) _ h :=
  dif_pos _

theorem _root_.set.infinite.nat.Sup_eq_zero {s : Set ℕ} (h : s.Infinite) : sup s = 0 :=
  dif_neg fun ⟨n, hn⟩ =>
    let ⟨k, hks, hk⟩ := h.exists_nat_lt n
    (hn k hks).not_lt hk

@[simp]
theorem Inf_eq_zero {s : Set ℕ} : inf s = 0 ↔ 0 ∈ s ∨ s = ∅ := by
  cases eq_empty_or_nonempty s
  · subst h
    simp only [← or_trueₓ, ← eq_self_iff_true, ← iff_trueₓ, ← Inf, ← HasInfₓ.inf, ← mem_empty_eq, ← exists_false, ←
      dif_neg, ← not_false_iff]
    
  · have := ne_empty_iff_nonempty.mpr h
    simp only [← this, ← or_falseₓ, ← Nat.Inf_def, ← h, ← Nat.find_eq_zero]
    

@[simp]
theorem Inf_empty : inf ∅ = 0 := by
  rw [Inf_eq_zero]
  right
  rfl

@[simp]
theorem infi_of_empty {ι : Sort _} [IsEmpty ι] (f : ι → ℕ) : infi f = 0 := by
  rw [infi_of_empty', Inf_empty]

theorem Inf_mem {s : Set ℕ} (h : s.Nonempty) : inf s ∈ s := by
  rw [Nat.Inf_def h]
  exact Nat.find_specₓ h

theorem not_mem_of_lt_Inf {s : Set ℕ} {m : ℕ} (hm : m < inf s) : m ∉ s := by
  cases eq_empty_or_nonempty s
  · subst h
    apply not_mem_empty
    
  · rw [Nat.Inf_def h] at hm
    exact Nat.find_minₓ h hm
    

protected theorem Inf_le {s : Set ℕ} {m : ℕ} (hm : m ∈ s) : inf s ≤ m := by
  rw [Nat.Inf_def ⟨m, hm⟩]
  exact Nat.find_min'ₓ ⟨m, hm⟩ hm

theorem nonempty_of_pos_Inf {s : Set ℕ} (h : 0 < inf s) : s.Nonempty := by
  by_contra contra
  rw [Set.not_nonempty_iff_eq_empty] at contra
  have h' : Inf s ≠ 0 := ne_of_gtₓ h
  apply h'
  rw [Nat.Inf_eq_zero]
  right
  assumption

theorem nonempty_of_Inf_eq_succ {s : Set ℕ} {k : ℕ} (h : inf s = k + 1) : s.Nonempty :=
  nonempty_of_pos_Inf (h.symm ▸ succ_posₓ k : inf s > 0)

theorem eq_Ici_of_nonempty_of_upward_closed {s : Set ℕ} (hs : s.Nonempty)
    (hs' : ∀ k₁ k₂ : ℕ, k₁ ≤ k₂ → k₁ ∈ s → k₂ ∈ s) : s = Ici (inf s) :=
  ext fun n => ⟨fun H => Nat.Inf_le H, fun H => hs' (inf s) n H (Inf_mem hs)⟩

theorem Inf_upward_closed_eq_succ_iff {s : Set ℕ} (hs : ∀ k₁ k₂ : ℕ, k₁ ≤ k₂ → k₁ ∈ s → k₂ ∈ s) (k : ℕ) :
    inf s = k + 1 ↔ k + 1 ∈ s ∧ k ∉ s := by
  constructor
  · intro H
    rw [eq_Ici_of_nonempty_of_upward_closed (nonempty_of_Inf_eq_succ H) hs, H, mem_Ici, mem_Ici]
    exact ⟨le_rfl, k.not_succ_le_self⟩
    
  · rintro ⟨H, H'⟩
    rw [Inf_def (⟨_, H⟩ : s.nonempty), find_eq_iff]
    exact ⟨H, fun n hnk hns => H' <| hs n k (lt_succ_iff.mp hnk) hns⟩
    

/-- This instance is necessary, otherwise the lattice operations would be derived via
conditionally_complete_linear_order_bot and marked as noncomputable. -/
instance : Lattice ℕ :=
  LinearOrderₓ.toLattice

noncomputable instance : ConditionallyCompleteLinearOrderBot ℕ :=
  { (inferInstance : OrderBot ℕ), (LinearOrderₓ.toLattice : Lattice ℕ), (inferInstance : LinearOrderₓ ℕ) with
    sup := sup, inf := inf,
    le_cSup := fun s a hb ha => by
      rw [Sup_def hb] <;> revert a ha <;> exact @Nat.find_specₓ _ _ hb,
    cSup_le := fun s a hs ha => by
      rw [Sup_def ⟨a, ha⟩] <;> exact Nat.find_min'ₓ _ ha,
    le_cInf := fun s a hs hb => by
      rw [Inf_def hs] <;> exact hb (@Nat.find_specₓ (fun n => n ∈ s) _ _),
    cInf_le := fun s a hb ha => by
      rw [Inf_def ⟨a, ha⟩] <;> exact Nat.find_min'ₓ _ ha,
    cSup_empty := by
      simp only [← Sup_def, ← Set.mem_empty_eq, ← forall_const, ← forall_prop_of_false, ← not_false_iff, ← exists_const]
      apply bot_unique (Nat.find_min'ₓ _ _)
      trivial }

theorem Sup_mem {s : Set ℕ} (h₁ : s.Nonempty) (h₂ : BddAbove s) : sup s ∈ s :=
  let ⟨k, hk⟩ := h₂
  h₁.cSup_mem ((finite_le_nat k).Subset hk)

theorem Inf_add {n : ℕ} {p : ℕ → Prop} (hn : n ≤ inf { m | p m }) : inf { m | p (m + n) } + n = inf { m | p m } := by
  obtain h | ⟨m, hm⟩ := { m | p (m + n) }.eq_empty_or_nonempty
  · rw [h, Nat.Inf_empty, zero_addₓ]
    obtain hnp | hnp := hn.eq_or_lt
    · exact hnp
      
    suffices hp : p (Inf { m | p m } - n + n)
    · exact (h.subset hp).elim
      
    rw [tsub_add_cancel_of_le hn]
    exact Inf_mem (nonempty_of_pos_Inf <| n.zero_le.trans_lt hnp)
    
  · have hp : ∃ n, n ∈ { m | p m } := ⟨_, hm⟩
    rw [Nat.Inf_def ⟨m, hm⟩, Nat.Inf_def hp]
    rw [Nat.Inf_def hp] at hn
    exact find_add hn
    

theorem Inf_add' {n : ℕ} {p : ℕ → Prop} (h : 0 < inf { m | p m }) : inf { m | p m } + n = inf { m | p (m - n) } := by
  convert Inf_add _
  · simp_rw [add_tsub_cancel_right]
    
  obtain ⟨m, hm⟩ := nonempty_of_pos_Inf h
  refine'
    le_cInf ⟨m + n, _⟩ fun b hb =>
      le_of_not_ltₓ fun hbn => ne_of_mem_of_not_mem _ (not_mem_of_lt_Inf h) (tsub_eq_zero_of_le hbn.le)
  · dsimp'
    rwa [add_tsub_cancel_right]
    
  · exact hb
    

section

variable {α : Type _} [CompleteLattice α]

theorem supr_lt_succ (u : ℕ → α) (n : ℕ) : (⨆ k < n + 1, u k) = (⨆ k < n, u k)⊔u n := by
  simp [← Nat.lt_succ_iff_lt_or_eq, ← supr_or, ← supr_sup_eq]

theorem supr_lt_succ' (u : ℕ → α) (n : ℕ) : (⨆ k < n + 1, u k) = u 0⊔⨆ k < n, u (k + 1) := by
  rw [← sup_supr_nat_succ]
  simp

theorem infi_lt_succ (u : ℕ → α) (n : ℕ) : (⨅ k < n + 1, u k) = (⨅ k < n, u k)⊓u n :=
  @supr_lt_succ αᵒᵈ _ _ _

theorem infi_lt_succ' (u : ℕ → α) (n : ℕ) : (⨅ k < n + 1, u k) = u 0⊓⨅ k < n, u (k + 1) :=
  @supr_lt_succ' αᵒᵈ _ _ _

end

end Nat

namespace Set

variable {α : Type _}

theorem bUnion_lt_succ (u : ℕ → Set α) (n : ℕ) : (⋃ k < n + 1, u k) = (⋃ k < n, u k) ∪ u n :=
  Nat.supr_lt_succ u n

theorem bUnion_lt_succ' (u : ℕ → Set α) (n : ℕ) : (⋃ k < n + 1, u k) = u 0 ∪ ⋃ k < n, u (k + 1) :=
  Nat.supr_lt_succ' u n

theorem bInter_lt_succ (u : ℕ → Set α) (n : ℕ) : (⋂ k < n + 1, u k) = (⋂ k < n, u k) ∩ u n :=
  Nat.infi_lt_succ u n

theorem bInter_lt_succ' (u : ℕ → Set α) (n : ℕ) : (⋂ k < n + 1, u k) = u 0 ∩ ⋂ k < n, u (k + 1) :=
  Nat.infi_lt_succ' u n

end Set

namespace PartEnat

open Classical

noncomputable instance : CompleteLinearOrder PartEnat :=
  { PartEnat.lattice, withTopOrderIso.symm.toGaloisInsertion.liftCompleteLattice, PartEnat.linearOrder with
    inf := (·⊓·), sup := (·⊔·), top := ⊤, bot := ⊥, le := (· ≤ ·), lt := (· < ·) }

end PartEnat

