/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathbin.Data.Finset.Prod
import Mathbin.Data.Sym.Sym2

/-!
# Symmetric powers of a finset

This file defines the symmetric powers of a finset as `finset (sym α n)` and `finset (sym2 α)`.

## Main declarations

* `finset.sym`: The symmetric power of a finset. `s.sym n` is all the multisets of cardinality `n`
  whose elements are in `s`.
* `finset.sym2`: The symmetric square of a finset. `s.sym2` is all the pairs whose elements are in
  `s`.

## TODO

`finset.sym` forms a Galois connection between `finset α` and `finset (sym α n)`. Similar for
`finset.sym2`.
-/


namespace Finset

variable {α : Type _} [DecidableEq α] {s t : Finset α} {a b : α}

theorem is_diag_mk_of_mem_diag {a : α × α} (h : a ∈ s.diag) : Sym2.IsDiag ⟦a⟧ :=
  (Sym2.is_diag_iff_proj_eq _).2 ((mem_diag _ _).1 h).2

theorem not_is_diag_mk_of_mem_off_diag {a : α × α} (h : a ∈ s.offDiag) : ¬Sym2.IsDiag ⟦a⟧ := by
  rw [Sym2.is_diag_iff_proj_eq]
  exact ((mem_off_diag _ _).1 h).2.2

section Sym2

variable {m : Sym2 α}

/-- Lifts a finset to `sym2 α`. `s.sym2` is the finset of all pairs with elements in `s`. -/
protected def sym2 (s : Finset α) : Finset (Sym2 α) :=
  (s.product s).Image Quotientₓ.mk

@[simp]
theorem mem_sym2_iff : m ∈ s.Sym2 ↔ ∀, ∀ a ∈ m, ∀, a ∈ s := by
  refine' mem_image.trans ⟨_, fun h => ⟨m.out, mem_product.2 ⟨h _ m.out_fst_mem, h _ m.out_snd_mem⟩, m.out_eq⟩⟩
  rintro ⟨⟨a, b⟩, h, rfl⟩
  rw [Sym2.ball]
  rwa [mem_product] at h

theorem mk_mem_sym2_iff : ⟦(a, b)⟧ ∈ s.Sym2 ↔ a ∈ s ∧ b ∈ s := by
  rw [mem_sym2_iff, Sym2.ball]

@[simp]
theorem sym2_empty : (∅ : Finset α).Sym2 = ∅ :=
  rfl

@[simp]
theorem sym2_eq_empty : s.Sym2 = ∅ ↔ s = ∅ := by
  rw [Finset.sym2, image_eq_empty, product_eq_empty, or_selfₓ]

@[simp]
theorem sym2_nonempty : s.Sym2.Nonempty ↔ s.Nonempty := by
  rw [Finset.sym2, nonempty.image_iff, nonempty_product, and_selfₓ]

alias sym2_nonempty ↔ _ nonempty.sym2

attribute [protected] nonempty.sym2

@[simp]
theorem sym2_univ [Fintype α] : (univ : Finset α).Sym2 = univ :=
  rfl

@[simp]
theorem sym2_singleton (a : α) : ({a} : Finset α).Sym2 = {Sym2.diag a} := by
  rw [Finset.sym2, singleton_product_singleton, image_singleton, Sym2.diag]

@[simp]
theorem diag_mem_sym2_iff : Sym2.diag a ∈ s.Sym2 ↔ a ∈ s :=
  mk_mem_sym2_iff.trans <| and_selfₓ _

@[simp]
theorem sym2_mono (h : s ⊆ t) : s.Sym2 ⊆ t.Sym2 := fun m he => mem_sym2_iff.2 fun a ha => h <| mem_sym2_iff.1 he _ ha

theorem image_diag_union_image_off_diag : s.diag.Image Quotientₓ.mk ∪ s.offDiag.Image Quotientₓ.mk = s.Sym2 := by
  rw [← image_union, diag_union_off_diag]
  rfl

end Sym2

section Sym

variable {n : ℕ} {m : Sym α n}

/-- Lifts a finset to `sym α n`. `s.sym n` is the finset of all unordered tuples of cardinality `n`
with elements in `s`. -/
protected def sym (s : Finset α) : ∀ n, Finset (Sym α n)
  | 0 => {∅}
  | n + 1 => s.sup fun a => (Sym n).Image <| Sym.cons a

@[simp]
theorem sym_zero : s.Sym 0 = {∅} :=
  rfl

@[simp]
theorem sym_succ : s.Sym (n + 1) = s.sup fun a => (s.Sym n).Image <| Sym.cons a :=
  rfl

@[simp]
theorem mem_sym_iff : m ∈ s.Sym n ↔ ∀, ∀ a ∈ m, ∀, a ∈ s := by
  induction' n with n ih
  · refine' mem_singleton.trans ⟨_, fun _ => Sym.eq_nil_of_card_zero _⟩
    rintro rfl
    exact fun a ha => ha.elim
    
  refine' mem_sup.trans ⟨_, fun h => _⟩
  · rintro ⟨a, ha, he⟩ b hb
    rw [mem_image] at he
    obtain ⟨m, he, rfl⟩ := he
    rw [Sym.mem_cons] at hb
    obtain rfl | hb := hb
    · exact ha
      
    · exact ih.1 he _ hb
      
    
  · obtain ⟨a, m, rfl⟩ := m.exists_eq_cons_of_succ
    exact ⟨a, h _ <| Sym.mem_cons_self _ _, mem_image_of_mem _ <| ih.2 fun b hb => h _ <| Sym.mem_cons_of_mem hb⟩
    

@[simp]
theorem sym_empty (n : ℕ) : (∅ : Finset α).Sym (n + 1) = ∅ :=
  rfl

theorem repeat_mem_sym (ha : a ∈ s) (n : ℕ) : Sym.repeat a n ∈ s.Sym n :=
  mem_sym_iff.2 fun b hb => by
    rwa [(Sym.mem_repeat.1 hb).2]

protected theorem Nonempty.sym (h : s.Nonempty) (n : ℕ) : (s.Sym n).Nonempty :=
  let ⟨a, ha⟩ := h
  ⟨_, repeat_mem_sym ha n⟩

@[simp]
theorem sym_singleton (a : α) (n : ℕ) : ({a} : Finset α).Sym n = {Sym.repeat a n} :=
  eq_singleton_iff_nonempty_unique_mem.2
    ⟨(singleton_nonempty _).Sym n, fun s hs =>
      Sym.eq_repeat_iff.2 fun b hb => eq_of_mem_singleton <| mem_sym_iff.1 hs _ hb⟩

theorem eq_empty_of_sym_eq_empty (h : s.Sym n = ∅) : s = ∅ := by
  rw [← not_nonempty_iff_eq_empty] at h⊢
  exact fun hs => h (hs.Sym _)

@[simp]
theorem sym_eq_empty : s.Sym n = ∅ ↔ n ≠ 0 ∧ s = ∅ := by
  cases n
  · exact iff_of_false (singleton_ne_empty _) fun h => (h.1 rfl).elim
    
  · refine' ⟨fun h => ⟨n.succ_ne_zero, eq_empty_of_sym_eq_empty h⟩, _⟩
    rintro ⟨_, rfl⟩
    exact sym_empty _
    

@[simp]
theorem sym_nonempty : (s.Sym n).Nonempty ↔ n = 0 ∨ s.Nonempty := by
  simp_rw [nonempty_iff_ne_empty, Ne.def, sym_eq_empty, not_and_distrib, not_ne_iff]

alias sym2_nonempty ↔ _ nonempty.sym2

attribute [protected] nonempty.sym2

@[simp]
theorem sym_univ [Fintype α] (n : ℕ) : (univ : Finset α).Sym n = univ :=
  eq_univ_iff_forall.2 fun s => mem_sym_iff.2 fun a _ => mem_univ _

@[simp]
theorem sym_mono (h : s ⊆ t) (n : ℕ) : s.Sym n ⊆ t.Sym n := fun m hm =>
  mem_sym_iff.2 fun a ha => h <| mem_sym_iff.1 hm _ ha

@[simp]
theorem sym_inter (s t : Finset α) (n : ℕ) : (s ∩ t).Sym n = s.Sym n ∩ t.Sym n := by
  ext m
  simp only [← mem_inter, ← mem_sym_iff, ← imp_and_distrib, ← forall_and_distrib]

@[simp]
theorem sym_union (s t : Finset α) (n : ℕ) : s.Sym n ∪ t.Sym n ⊆ (s ∪ t).Sym n :=
  union_subset (sym_mono (subset_union_left s t) n) (sym_mono (subset_union_right s t) n)

end Sym

end Finset

