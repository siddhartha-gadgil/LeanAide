/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathbin.Data.Finset.LocallyFinite
import Mathbin.Data.Finset.Pointwise
import Mathbin.Data.Fintype.Card
import Mathbin.Data.Dfinsupp.Order

/-!
# Finite intervals of finitely supported functions

This file provides the `locally_finite_order` instance for `Π₀ i, α i` when `α` itself is locally
finite and calculates the cardinality of its finite intervals.
-/


open Dfinsupp Finset

open BigOperators Pointwise

variable {ι : Type _} {α : ι → Type _}

namespace Finset

variable [DecidableEq ι] [∀ i, Zero (α i)] {s : Finset ι} {f : Π₀ i, α i} {t : ∀ i, Finset (α i)}

/-- Finitely supported product of finsets. -/
def dfinsupp (s : Finset ι) (t : ∀ i, Finset (α i)) : Finset (Π₀ i, α i) :=
  (s.pi t).map
    ⟨fun f => (Dfinsupp.mk s) fun i => f i i.2, by
      refine' (mk_injective _).comp fun f g h => _
      ext i hi
      convert congr_fun h ⟨i, hi⟩⟩

@[simp]
theorem card_dfinsupp (s : Finset ι) (t : ∀ i, Finset (α i)) : (s.Dfinsupp t).card = ∏ i in s, (t i).card :=
  (card_map _).trans <| card_pi _ _

variable [∀ i, DecidableEq (α i)]

theorem mem_dfinsupp_iff : f ∈ s.Dfinsupp t ↔ f.support ⊆ s ∧ ∀, ∀ i ∈ s, ∀, f i ∈ t i := by
  refine' mem_map.trans ⟨_, _⟩
  · rintro ⟨f, hf, rfl⟩
    refine' ⟨support_mk_subset, fun i hi => _⟩
    convert mem_pi.1 hf i hi
    exact mk_of_mem hi
    
  · refine' fun h => ⟨fun i _ => f i, mem_pi.2 h.2, _⟩
    ext i
    dsimp'
    exact ite_eq_left_iff.2 fun hi => (not_mem_support_iff.1 fun H => hi <| h.1 H).symm
    

/-- When `t` is supported on `s`, `f ∈ s.dfinsupp t` precisely means that `f` is pointwise in `t`.
-/
@[simp]
theorem mem_dfinsupp_iff_of_support_subset {t : Π₀ i, Finset (α i)} (ht : t.support ⊆ s) :
    f ∈ s.Dfinsupp t ↔ ∀ i, f i ∈ t i := by
  refine'
    mem_dfinsupp_iff.trans
      (forall_and_distrib.symm.trans <|
        forall_congrₓ fun i =>
          ⟨fun h => _, fun h => ⟨fun hi => ht <| mem_support_iff.2 fun H => mem_support_iff.1 hi _, fun _ => h⟩⟩)
  · by_cases' hi : i ∈ s
    · exact h.2 hi
      
    · rw [not_mem_support_iff.1 (mt h.1 hi), not_mem_support_iff.1 (not_mem_mono ht hi)]
      exact zero_mem_zero
      
    
  · rwa [H, mem_zero] at h
    

end Finset

open Finset

namespace Dfinsupp

variable [DecidableEq ι] [∀ i, DecidableEq (α i)]

section BundledSingleton

variable [∀ i, Zero (α i)] {f : Π₀ i, α i} {i : ι} {a : α i}

/-- Pointwise `finset.singleton` bundled as a `dfinsupp`. -/
def singleton (f : Π₀ i, α i) : Π₀ i, Finset (α i) :=
  ⟦{ toFun := fun i => {f i}, preSupport := f.support.1,
      zero := fun i => (ne_or_eq (f i) 0).imp mem_support_iff.2 (congr_arg _) }⟧

theorem mem_singleton_apply_iff : a ∈ f.singleton i ↔ a = f i :=
  mem_singleton

end BundledSingleton

section BundledIcc

variable [∀ i, Zero (α i)] [∀ i, PartialOrderₓ (α i)] [∀ i, LocallyFiniteOrder (α i)] {f g : Π₀ i, α i} {i : ι}
  {a : α i}

/-- Pointwise `finset.Icc` bundled as a `dfinsupp`. -/
def rangeIcc (f g : Π₀ i, α i) : Π₀ i, Finset (α i) :=
  ⟦{ toFun := fun i => icc (f i) (g i), preSupport := f.support.1 + g.support.1,
      zero := fun i => by
        refine' or_iff_not_imp_left.2 fun h => _
        rw [not_mem_support_iff.1 (Multiset.not_mem_mono (Multiset.le_add_right _ _).Subset h),
          not_mem_support_iff.1 (Multiset.not_mem_mono (Multiset.le_add_left _ _).Subset h)]
        exact Icc_self _ }⟧

@[simp]
theorem range_Icc_apply (f g : Π₀ i, α i) (i : ι) : f.rangeIcc g i = icc (f i) (g i) :=
  rfl

theorem mem_range_Icc_apply_iff : a ∈ f.rangeIcc g i ↔ f i ≤ a ∧ a ≤ g i :=
  mem_Icc

theorem support_range_Icc_subset : (f.rangeIcc g).support ⊆ f.support ∪ g.support := by
  refine' fun x hx => _
  by_contra
  refine' not_mem_support_iff.2 _ hx
  rw [range_Icc_apply, not_mem_support_iff.1 (not_mem_mono (subset_union_left _ _) h),
    not_mem_support_iff.1 (not_mem_mono (subset_union_right _ _) h)]
  exact Icc_self _

end BundledIcc

section Pi

variable [∀ i, Zero (α i)]

/-- Given a finitely supported function `f : Π₀ i, finset (α i)`, one can define the finset
`f.pi` of all finitely supported functions whose value at `i` is in `f i` for all `i`. -/
def pi (f : Π₀ i, Finset (α i)) : Finset (Π₀ i, α i) :=
  f.support.Dfinsupp f

@[simp]
theorem mem_pi {f : Π₀ i, Finset (α i)} {g : Π₀ i, α i} : g ∈ f.pi ↔ ∀ i, g i ∈ f i :=
  mem_dfinsupp_iff_of_support_subset <| Subset.refl _

@[simp]
theorem card_pi (f : Π₀ i, Finset (α i)) : f.pi.card = f.Prod fun i => (f i).card := by
  rw [pi, card_dfinsupp]
  exact
    Finset.prod_congr rfl fun i _ => by
      simp only [← Pi.nat_apply, ← Nat.cast_id]

end Pi

section LocallyFinite

variable [∀ i, PartialOrderₓ (α i)] [∀ i, Zero (α i)] [∀ i, LocallyFiniteOrder (α i)]

instance : LocallyFiniteOrder (Π₀ i, α i) :=
  LocallyFiniteOrder.ofIcc (Π₀ i, α i) (fun f g => (f.support ∪ g.support).Dfinsupp <| f.rangeIcc g) fun f g x => by
    refine' (mem_dfinsupp_iff_of_support_subset <| support_range_Icc_subset).trans _
    simp_rw [mem_range_Icc_apply_iff, forall_and_distrib]
    rfl

variable (f g : Π₀ i, α i)

theorem card_Icc : (icc f g).card = ∏ i in f.support ∪ g.support, (icc (f i) (g i)).card :=
  card_dfinsupp _ _

theorem card_Ico : (ico f g).card = (∏ i in f.support ∪ g.support, (icc (f i) (g i)).card) - 1 := by
  rw [card_Ico_eq_card_Icc_sub_one, card_Icc]

theorem card_Ioc : (ioc f g).card = (∏ i in f.support ∪ g.support, (icc (f i) (g i)).card) - 1 := by
  rw [card_Ioc_eq_card_Icc_sub_one, card_Icc]

theorem card_Ioo : (ioo f g).card = (∏ i in f.support ∪ g.support, (icc (f i) (g i)).card) - 2 := by
  rw [card_Ioo_eq_card_Icc_sub_two, card_Icc]

end LocallyFinite

end Dfinsupp

