/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathbin.Data.Multiset.FinsetOps
import Mathbin.Data.Multiset.Fold

/-!
# Lattice operations on multisets
-/


namespace Multiset

variable {α : Type _}

/-! ### sup -/


section Sup

-- can be defined with just `[has_bot α]` where some lemmas hold without requiring `[order_bot α]`
variable [SemilatticeSup α] [OrderBot α]

/-- Supremum of a multiset: `sup {a, b, c} = a ⊔ b ⊔ c` -/
def sup (s : Multiset α) : α :=
  s.fold (·⊔·) ⊥

@[simp]
theorem sup_zero : (0 : Multiset α).sup = ⊥ :=
  fold_zero _ _

@[simp]
theorem sup_cons (a : α) (s : Multiset α) : (a ::ₘ s).sup = a⊔s.sup :=
  fold_cons_left _ _ _ _

@[simp]
theorem sup_singleton {a : α} : ({a} : Multiset α).sup = a :=
  sup_bot_eq

@[simp]
theorem sup_add (s₁ s₂ : Multiset α) : (s₁ + s₂).sup = s₁.sup⊔s₂.sup :=
  Eq.trans
    (by
      simp [← sup])
    (fold_add _ _ _ _ _)

theorem sup_le {s : Multiset α} {a : α} : s.sup ≤ a ↔ ∀, ∀ b ∈ s, ∀, b ≤ a :=
  Multiset.induction_on s
    (by
      simp )
    (by
      simp (config := { contextual := true })[← or_imp_distrib, ← forall_and_distrib])

theorem le_sup {s : Multiset α} {a : α} (h : a ∈ s) : a ≤ s.sup :=
  sup_le.1 le_rfl _ h

theorem sup_mono {s₁ s₂ : Multiset α} (h : s₁ ⊆ s₂) : s₁.sup ≤ s₂.sup :=
  sup_le.2 fun b hb => le_sup (h hb)

variable [DecidableEq α]

@[simp]
theorem sup_dedup (s : Multiset α) : (dedup s).sup = s.sup :=
  fold_dedup_idem _ _ _

@[simp]
theorem sup_ndunion (s₁ s₂ : Multiset α) : (ndunion s₁ s₂).sup = s₁.sup⊔s₂.sup := by
  rw [← sup_dedup, dedup_ext.2, sup_dedup, sup_add] <;> simp

@[simp]
theorem sup_union (s₁ s₂ : Multiset α) : (s₁ ∪ s₂).sup = s₁.sup⊔s₂.sup := by
  rw [← sup_dedup, dedup_ext.2, sup_dedup, sup_add] <;> simp

@[simp]
theorem sup_ndinsert (a : α) (s : Multiset α) : (ndinsert a s).sup = a⊔s.sup := by
  rw [← sup_dedup, dedup_ext.2, sup_dedup, sup_cons] <;> simp

theorem nodup_sup_iff {α : Type _} [DecidableEq α] {m : Multiset (Multiset α)} :
    m.sup.Nodup ↔ ∀ a : Multiset α, a ∈ m → a.Nodup := by
  apply m.induction_on
  · simp
    
  · intro a s h
    simp [← h]
    

end Sup

/-! ### inf -/


section Inf

-- can be defined with just `[has_top α]` where some lemmas hold without requiring `[order_top α]`
variable [SemilatticeInf α] [OrderTop α]

/-- Infimum of a multiset: `inf {a, b, c} = a ⊓ b ⊓ c` -/
def inf (s : Multiset α) : α :=
  s.fold (·⊓·) ⊤

@[simp]
theorem inf_zero : (0 : Multiset α).inf = ⊤ :=
  fold_zero _ _

@[simp]
theorem inf_cons (a : α) (s : Multiset α) : (a ::ₘ s).inf = a⊓s.inf :=
  fold_cons_left _ _ _ _

@[simp]
theorem inf_singleton {a : α} : ({a} : Multiset α).inf = a :=
  inf_top_eq

@[simp]
theorem inf_add (s₁ s₂ : Multiset α) : (s₁ + s₂).inf = s₁.inf⊓s₂.inf :=
  Eq.trans
    (by
      simp [← inf])
    (fold_add _ _ _ _ _)

theorem le_inf {s : Multiset α} {a : α} : a ≤ s.inf ↔ ∀, ∀ b ∈ s, ∀, a ≤ b :=
  Multiset.induction_on s
    (by
      simp )
    (by
      simp (config := { contextual := true })[← or_imp_distrib, ← forall_and_distrib])

theorem inf_le {s : Multiset α} {a : α} (h : a ∈ s) : s.inf ≤ a :=
  le_inf.1 le_rfl _ h

theorem inf_mono {s₁ s₂ : Multiset α} (h : s₁ ⊆ s₂) : s₂.inf ≤ s₁.inf :=
  le_inf.2 fun b hb => inf_le (h hb)

variable [DecidableEq α]

@[simp]
theorem inf_dedup (s : Multiset α) : (dedup s).inf = s.inf :=
  fold_dedup_idem _ _ _

@[simp]
theorem inf_ndunion (s₁ s₂ : Multiset α) : (ndunion s₁ s₂).inf = s₁.inf⊓s₂.inf := by
  rw [← inf_dedup, dedup_ext.2, inf_dedup, inf_add] <;> simp

@[simp]
theorem inf_union (s₁ s₂ : Multiset α) : (s₁ ∪ s₂).inf = s₁.inf⊓s₂.inf := by
  rw [← inf_dedup, dedup_ext.2, inf_dedup, inf_add] <;> simp

@[simp]
theorem inf_ndinsert (a : α) (s : Multiset α) : (ndinsert a s).inf = a⊓s.inf := by
  rw [← inf_dedup, dedup_ext.2, inf_dedup, inf_cons] <;> simp

end Inf

end Multiset

