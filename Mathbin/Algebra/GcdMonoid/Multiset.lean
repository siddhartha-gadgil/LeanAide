/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathbin.Algebra.GcdMonoid.Basic
import Mathbin.Data.Multiset.Lattice

/-!
# GCD and LCM operations on multisets

## Main definitions

- `multiset.gcd` - the greatest common denominator of a `multiset` of elements of a `gcd_monoid`
- `multiset.lcm` - the least common multiple of a `multiset` of elements of a `gcd_monoid`

## Implementation notes

TODO: simplify with a tactic and `data.multiset.lattice`

## Tags

multiset, gcd
-/


namespace Multiset

variable {α : Type _} [CancelCommMonoidWithZero α] [NormalizedGcdMonoid α]

/-! ### lcm -/


section Lcm

/-- Least common multiple of a multiset -/
def lcm (s : Multiset α) : α :=
  s.fold GcdMonoid.lcm 1

@[simp]
theorem lcm_zero : (0 : Multiset α).lcm = 1 :=
  fold_zero _ _

@[simp]
theorem lcm_cons (a : α) (s : Multiset α) : (a ::ₘ s).lcm = GcdMonoid.lcm a s.lcm :=
  fold_cons_left _ _ _ _

@[simp]
theorem lcm_singleton {a : α} : ({a} : Multiset α).lcm = normalize a :=
  (fold_singleton _ _ _).trans <| lcm_one_right _

@[simp]
theorem lcm_add (s₁ s₂ : Multiset α) : (s₁ + s₂).lcm = GcdMonoid.lcm s₁.lcm s₂.lcm :=
  Eq.trans
    (by
      simp [← lcm])
    (fold_add _ _ _ _ _)

theorem lcm_dvd {s : Multiset α} {a : α} : s.lcm ∣ a ↔ ∀, ∀ b ∈ s, ∀, b ∣ a :=
  Multiset.induction_on s
    (by
      simp )
    (by
      simp (config := { contextual := true })[← or_imp_distrib, ← forall_and_distrib, ← lcm_dvd_iff])

theorem dvd_lcm {s : Multiset α} {a : α} (h : a ∈ s) : a ∣ s.lcm :=
  lcm_dvd.1 dvd_rfl _ h

theorem lcm_mono {s₁ s₂ : Multiset α} (h : s₁ ⊆ s₂) : s₁.lcm ∣ s₂.lcm :=
  lcm_dvd.2 fun b hb => dvd_lcm (h hb)

@[simp]
theorem normalize_lcm (s : Multiset α) : normalize s.lcm = s.lcm :=
  (Multiset.induction_on s
      (by
        simp ))
    fun a s IH => by
    simp

@[simp]
theorem lcm_eq_zero_iff [Nontrivial α] (s : Multiset α) : s.lcm = 0 ↔ (0 : α) ∈ s := by
  induction' s using Multiset.induction_on with a s ihs
  · simp only [← lcm_zero, ← one_ne_zero, ← not_mem_zero]
    
  · simp only [← mem_cons, ← lcm_cons, ← lcm_eq_zero_iff, ← ihs, ← @eq_comm _ a]
    

variable [DecidableEq α]

@[simp]
theorem lcm_dedup (s : Multiset α) : (dedup s).lcm = s.lcm :=
  (Multiset.induction_on s
      (by
        simp ))
    fun a s IH => by
    by_cases' a ∈ s <;> simp [← IH, ← h]
    unfold lcm
    rw [← cons_erase h, fold_cons_left, ← lcm_assoc, lcm_same]
    apply lcm_eq_of_associated_left (associated_normalize _)

@[simp]
theorem lcm_ndunion (s₁ s₂ : Multiset α) : (ndunion s₁ s₂).lcm = GcdMonoid.lcm s₁.lcm s₂.lcm := by
  rw [← lcm_dedup, dedup_ext.2, lcm_dedup, lcm_add]
  simp

@[simp]
theorem lcm_union (s₁ s₂ : Multiset α) : (s₁ ∪ s₂).lcm = GcdMonoid.lcm s₁.lcm s₂.lcm := by
  rw [← lcm_dedup, dedup_ext.2, lcm_dedup, lcm_add]
  simp

@[simp]
theorem lcm_ndinsert (a : α) (s : Multiset α) : (ndinsert a s).lcm = GcdMonoid.lcm a s.lcm := by
  rw [← lcm_dedup, dedup_ext.2, lcm_dedup, lcm_cons]
  simp

end Lcm

/-! ### gcd -/


section Gcd

/-- Greatest common divisor of a multiset -/
def gcd (s : Multiset α) : α :=
  s.fold GcdMonoid.gcd 0

@[simp]
theorem gcd_zero : (0 : Multiset α).gcd = 0 :=
  fold_zero _ _

@[simp]
theorem gcd_cons (a : α) (s : Multiset α) : (a ::ₘ s).gcd = GcdMonoid.gcd a s.gcd :=
  fold_cons_left _ _ _ _

@[simp]
theorem gcd_singleton {a : α} : ({a} : Multiset α).gcd = normalize a :=
  (fold_singleton _ _ _).trans <| gcd_zero_right _

@[simp]
theorem gcd_add (s₁ s₂ : Multiset α) : (s₁ + s₂).gcd = GcdMonoid.gcd s₁.gcd s₂.gcd :=
  Eq.trans
    (by
      simp [← gcd])
    (fold_add _ _ _ _ _)

theorem dvd_gcd {s : Multiset α} {a : α} : a ∣ s.gcd ↔ ∀, ∀ b ∈ s, ∀, a ∣ b :=
  Multiset.induction_on s
    (by
      simp )
    (by
      simp (config := { contextual := true })[← or_imp_distrib, ← forall_and_distrib, ← dvd_gcd_iff])

theorem gcd_dvd {s : Multiset α} {a : α} (h : a ∈ s) : s.gcd ∣ a :=
  dvd_gcd.1 dvd_rfl _ h

theorem gcd_mono {s₁ s₂ : Multiset α} (h : s₁ ⊆ s₂) : s₂.gcd ∣ s₁.gcd :=
  dvd_gcd.2 fun b hb => gcd_dvd (h hb)

@[simp]
theorem normalize_gcd (s : Multiset α) : normalize s.gcd = s.gcd :=
  (Multiset.induction_on s
      (by
        simp ))
    fun a s IH => by
    simp

theorem gcd_eq_zero_iff (s : Multiset α) : s.gcd = 0 ↔ ∀ x : α, x ∈ s → x = 0 := by
  constructor
  · intro h x hx
    apply eq_zero_of_zero_dvd
    rw [← h]
    apply gcd_dvd hx
    
  · apply s.induction_on
    · simp
      
    intro a s sgcd h
    simp [← h a (mem_cons_self a s), ← sgcd fun x hx => h x (mem_cons_of_mem hx)]
    

variable [DecidableEq α]

@[simp]
theorem gcd_dedup (s : Multiset α) : (dedup s).gcd = s.gcd :=
  (Multiset.induction_on s
      (by
        simp ))
    fun a s IH => by
    by_cases' a ∈ s <;> simp [← IH, ← h]
    unfold gcd
    rw [← cons_erase h, fold_cons_left, ← gcd_assoc, gcd_same]
    apply (associated_normalize _).gcd_eq_left

@[simp]
theorem gcd_ndunion (s₁ s₂ : Multiset α) : (ndunion s₁ s₂).gcd = GcdMonoid.gcd s₁.gcd s₂.gcd := by
  rw [← gcd_dedup, dedup_ext.2, gcd_dedup, gcd_add]
  simp

@[simp]
theorem gcd_union (s₁ s₂ : Multiset α) : (s₁ ∪ s₂).gcd = GcdMonoid.gcd s₁.gcd s₂.gcd := by
  rw [← gcd_dedup, dedup_ext.2, gcd_dedup, gcd_add]
  simp

@[simp]
theorem gcd_ndinsert (a : α) (s : Multiset α) : (ndinsert a s).gcd = GcdMonoid.gcd a s.gcd := by
  rw [← gcd_dedup, dedup_ext.2, gcd_dedup, gcd_cons]
  simp

end Gcd

end Multiset

