/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathbin.Order.CompleteLattice
import Mathbin.Order.Cover
import Mathbin.Order.Iterate
import Mathbin.Tactic.Monotonicity.Default

/-!
# Successor and predecessor

This file defines successor and predecessor orders. `succ a`, the successor of an element `a : α` is
the least element greater than `a`. `pred a` is the greatest element less than `a`. Typical examples
include `ℕ`, `ℤ`, `ℕ+`, `fin n`, but also `enat`, the lexicographic order of a successor/predecessor
order...

## Typeclasses

* `succ_order`: Order equipped with a sensible successor function.
* `pred_order`: Order equipped with a sensible predecessor function.
* `is_succ_archimedean`: `succ_order` where `succ` iterated to an element gives all the greater
  ones.
* `is_pred_archimedean`: `pred_order` where `pred` iterated to an element gives all the smaller
  ones.

## Implementation notes

Maximal elements don't have a sensible successor. Thus the naïve typeclass
```lean
class naive_succ_order (α : Type*) [preorder α] :=
(succ : α → α)
(succ_le_iff : ∀ {a b}, succ a ≤ b ↔ a < b)
(lt_succ_iff : ∀ {a b}, a < succ b ↔ a ≤ b)
```
can't apply to an `order_top` because plugging in `a = b = ⊤` into either of `succ_le_iff` and
`lt_succ_iff` yields `⊤ < ⊤` (or more generally `m < m` for a maximal element `m`).
The solution taken here is to remove the implications `≤ → <` and instead require that `a < succ a`
for all non maximal elements (enforced by the combination of `le_succ` and the contrapositive of
`max_of_succ_le`).
The stricter condition of every element having a sensible successor can be obtained through the
combination of `succ_order α` and `no_max_order α`.

## TODO

Is `galois_connection pred succ` always true? If not, we should introduce
```lean
class succ_pred_order (α : Type*) [preorder α] extends succ_order α, pred_order α :=
(pred_succ_gc : galois_connection (pred : α → α) succ)
```
`covby` should help here.
-/


open Function OrderDual Set

variable {α : Type _}

/-- Order equipped with a sensible successor function. -/
@[ext]
class SuccOrder (α : Type _) [Preorderₓ α] where
  succ : α → α
  le_succ : ∀ a, a ≤ succ a
  max_of_succ_le {a} : succ a ≤ a → IsMax a
  succ_le_of_lt {a b} : a < b → succ a ≤ b
  le_of_lt_succ {a b} : a < succ b → a ≤ b

/-- Order equipped with a sensible predecessor function. -/
@[ext]
class PredOrder (α : Type _) [Preorderₓ α] where
  pred : α → α
  pred_le : ∀ a, pred a ≤ a
  min_of_le_pred {a} : a ≤ pred a → IsMin a
  le_pred_of_lt {a b} : a < b → a ≤ pred b
  le_of_pred_lt {a b} : pred a < b → a ≤ b

instance [Preorderₓ α] [SuccOrder α] : PredOrder αᵒᵈ where
  pred := to_dual ∘ SuccOrder.succ ∘ of_dual
  pred_le := SuccOrder.le_succ
  min_of_le_pred := fun _ => SuccOrder.max_of_succ_le
  le_pred_of_lt := fun a b h => SuccOrder.succ_le_of_lt h
  le_of_pred_lt := fun a b => SuccOrder.le_of_lt_succ

instance [Preorderₓ α] [PredOrder α] : SuccOrder αᵒᵈ where
  succ := to_dual ∘ PredOrder.pred ∘ of_dual
  le_succ := PredOrder.pred_le
  max_of_succ_le := fun _ => PredOrder.min_of_le_pred
  succ_le_of_lt := fun a b h => PredOrder.le_pred_of_lt h
  le_of_lt_succ := fun a b => PredOrder.le_of_pred_lt

section Preorderₓ

variable [Preorderₓ α]

/-- A constructor for `succ_order α` usable when `α` has no maximal element. -/
def SuccOrder.ofSuccLeIffOfLeLtSucc (succ : α → α) (hsucc_le_iff : ∀ {a b}, succ a ≤ b ↔ a < b)
    (hle_of_lt_succ : ∀ {a b}, a < succ b → a ≤ b) : SuccOrder α :=
  { succ, le_succ := fun a => (hsucc_le_iff.1 le_rfl).le,
    max_of_succ_le := fun a ha => (lt_irreflₓ a <| hsucc_le_iff.1 ha).elim, succ_le_of_lt := fun a b => hsucc_le_iff.2,
    le_of_lt_succ := fun a b => hle_of_lt_succ }

/-- A constructor for `pred_order α` usable when `α` has no minimal element. -/
def PredOrder.ofLePredIffOfPredLePred (pred : α → α) (hle_pred_iff : ∀ {a b}, a ≤ pred b ↔ a < b)
    (hle_of_pred_lt : ∀ {a b}, pred a < b → a ≤ b) : PredOrder α :=
  { pred, pred_le := fun a => (hle_pred_iff.1 le_rfl).le,
    min_of_le_pred := fun a ha => (lt_irreflₓ a <| hle_pred_iff.1 ha).elim, le_pred_of_lt := fun a b => hle_pred_iff.2,
    le_of_pred_lt := fun a b => hle_of_pred_lt }

end Preorderₓ

section LinearOrderₓ

variable [LinearOrderₓ α]

/-- A constructor for `succ_order α` for `α` a linear order. -/
@[simps]
def SuccOrder.ofCore (succ : α → α) (hn : ∀ {a}, ¬IsMax a → ∀ b, a < b ↔ succ a ≤ b) (hm : ∀ a, IsMax a → succ a = a) :
    SuccOrder α :=
  { succ, succ_le_of_lt := fun a b => Classical.by_cases (fun h hab => (hm a h).symm ▸ hab.le) fun h => (hn h b).mp,
    le_succ := fun a =>
      Classical.by_cases (fun h => (hm a h).symm.le) fun h =>
        le_of_ltₓ <| by
          simpa using (hn h a).Not,
    le_of_lt_succ := fun a b hab =>
      Classical.by_cases (fun h => hm b h ▸ hab.le) fun h => by
        simpa [← hab] using (hn h a).Not,
    max_of_succ_le := fun a =>
      not_imp_not.mp fun h => by
        simpa using (hn h a).Not }

/-- A constructor for `pred_order α` for `α` a linear order. -/
@[simps]
def PredOrder.ofCore {α} [LinearOrderₓ α] (pred : α → α) (hn : ∀ {a}, ¬IsMin a → ∀ b, b ≤ pred a ↔ b < a)
    (hm : ∀ a, IsMin a → pred a = a) : PredOrder α :=
  { pred, le_pred_of_lt := fun a b => Classical.by_cases (fun h hab => (hm b h).symm ▸ hab.le) fun h => (hn h a).mpr,
    pred_le := fun a =>
      Classical.by_cases (fun h => (hm a h).le) fun h =>
        le_of_ltₓ <| by
          simpa using (hn h a).Not,
    le_of_pred_lt := fun a b hab =>
      Classical.by_cases (fun h => hm a h ▸ hab.le) fun h => by
        simpa [← hab] using (hn h b).Not,
    min_of_le_pred := fun a =>
      not_imp_not.mp fun h => by
        simpa using (hn h a).Not }

/-- A constructor for `succ_order α` usable when `α` is a linear order with no maximal element. -/
def SuccOrder.ofSuccLeIff (succ : α → α) (hsucc_le_iff : ∀ {a b}, succ a ≤ b ↔ a < b) : SuccOrder α :=
  { succ, le_succ := fun a => (hsucc_le_iff.1 le_rfl).le,
    max_of_succ_le := fun a ha => (lt_irreflₓ a <| hsucc_le_iff.1 ha).elim, succ_le_of_lt := fun a b => hsucc_le_iff.2,
    le_of_lt_succ := fun a b h => le_of_not_ltₓ ((not_congr hsucc_le_iff).1 h.not_le) }

/-- A constructor for `pred_order α` usable when `α` is a linear order with no minimal element. -/
def PredOrder.ofLePredIff (pred : α → α) (hle_pred_iff : ∀ {a b}, a ≤ pred b ↔ a < b) : PredOrder α :=
  { pred, pred_le := fun a => (hle_pred_iff.1 le_rfl).le,
    min_of_le_pred := fun a ha => (lt_irreflₓ a <| hle_pred_iff.1 ha).elim, le_pred_of_lt := fun a b => hle_pred_iff.2,
    le_of_pred_lt := fun a b h => le_of_not_ltₓ ((not_congr hle_pred_iff).1 h.not_le) }

end LinearOrderₓ

/-! ### Successor order -/


namespace Order

section Preorderₓ

variable [Preorderₓ α] [SuccOrder α] {a b : α}

/-- The successor of an element. If `a` is not maximal, then `succ a` is the least element greater
than `a`. If `a` is maximal, then `succ a = a`. -/
def succ : α → α :=
  SuccOrder.succ

theorem le_succ : ∀ a : α, a ≤ succ a :=
  SuccOrder.le_succ

theorem max_of_succ_le {a : α} : succ a ≤ a → IsMax a :=
  SuccOrder.max_of_succ_le

theorem succ_le_of_lt {a b : α} : a < b → succ a ≤ b :=
  SuccOrder.succ_le_of_lt

theorem le_of_lt_succ {a b : α} : a < succ b → a ≤ b :=
  SuccOrder.le_of_lt_succ

@[simp]
theorem succ_le_iff_is_max : succ a ≤ a ↔ IsMax a :=
  ⟨max_of_succ_le, fun h => h <| le_succ _⟩

@[simp]
theorem lt_succ_iff_not_is_max : a < succ a ↔ ¬IsMax a :=
  ⟨not_is_max_of_lt, fun ha => (le_succ a).lt_of_not_le fun h => ha <| max_of_succ_le h⟩

alias lt_succ_iff_not_is_max ↔ _ lt_succ_of_not_is_max

theorem wcovby_succ (a : α) : a ⩿ succ a :=
  ⟨le_succ a, fun b hb => (succ_le_of_lt hb).not_lt⟩

theorem covby_succ_of_not_is_max (h : ¬IsMax a) : a ⋖ succ a :=
  (wcovby_succ a).covby_of_lt <| lt_succ_of_not_is_max h

theorem lt_succ_iff_of_not_is_max (ha : ¬IsMax a) : b < succ a ↔ b ≤ a :=
  ⟨le_of_lt_succ, fun h => h.trans_lt <| lt_succ_of_not_is_max ha⟩

theorem succ_le_iff_of_not_is_max (ha : ¬IsMax a) : succ a ≤ b ↔ a < b :=
  ⟨(lt_succ_of_not_is_max ha).trans_le, succ_le_of_lt⟩

@[simp, mono]
theorem succ_le_succ (h : a ≤ b) : succ a ≤ succ b := by
  by_cases' hb : IsMax b
  · by_cases' hba : b ≤ a
    · exact (hb <| hba.trans <| le_succ _).trans (le_succ _)
      
    · exact succ_le_of_lt ((h.lt_of_not_le hba).trans_le <| le_succ b)
      
    
  · rwa [succ_le_iff_of_not_is_max fun ha => hb <| ha.mono h, lt_succ_iff_of_not_is_max hb]
    

theorem succ_mono : Monotone (succ : α → α) := fun a b => succ_le_succ

theorem Iio_succ_of_not_is_max (ha : ¬IsMax a) : Iio (succ a) = Iic a :=
  Set.ext fun x => lt_succ_iff_of_not_is_max ha

theorem Ici_succ_of_not_is_max (ha : ¬IsMax a) : Ici (succ a) = Ioi a :=
  Set.ext fun x => succ_le_iff_of_not_is_max ha

theorem Ico_succ_right_of_not_is_max (hb : ¬IsMax b) : Ico a (succ b) = Icc a b := by
  rw [← Ici_inter_Iio, Iio_succ_of_not_is_max hb, Ici_inter_Iic]

theorem Ioo_succ_right_of_not_is_max (hb : ¬IsMax b) : Ioo a (succ b) = Ioc a b := by
  rw [← Ioi_inter_Iio, Iio_succ_of_not_is_max hb, Ioi_inter_Iic]

theorem Icc_succ_left_of_not_is_max (ha : ¬IsMax a) : Icc (succ a) b = Ioc a b := by
  rw [← Ici_inter_Iic, Ici_succ_of_not_is_max ha, Ioi_inter_Iic]

theorem Ico_succ_left_of_not_is_max (ha : ¬IsMax a) : Ico (succ a) b = Ioo a b := by
  rw [← Ici_inter_Iio, Ici_succ_of_not_is_max ha, Ioi_inter_Iio]

section NoMaxOrder

variable [NoMaxOrder α]

theorem lt_succ (a : α) : a < succ a :=
  lt_succ_of_not_is_max <| not_is_max a

@[simp]
theorem lt_succ_iff : a < succ b ↔ a ≤ b :=
  lt_succ_iff_of_not_is_max <| not_is_max b

@[simp]
theorem succ_le_iff : succ a ≤ b ↔ a < b :=
  succ_le_iff_of_not_is_max <| not_is_max a

theorem succ_le_succ_iff : succ a ≤ succ b ↔ a ≤ b := by
  simp

theorem succ_lt_succ_iff : succ a < succ b ↔ a < b := by
  simp

alias succ_le_succ_iff ↔ le_of_succ_le_succ _

alias succ_lt_succ_iff ↔ lt_of_succ_lt_succ succ_lt_succ

theorem succ_strict_mono : StrictMono (succ : α → α) := fun a b => succ_lt_succ

theorem covby_succ (a : α) : a ⋖ succ a :=
  covby_succ_of_not_is_max <| not_is_max a

@[simp]
theorem Iio_succ (a : α) : Iio (succ a) = Iic a :=
  Iio_succ_of_not_is_max <| not_is_max _

@[simp]
theorem Ici_succ (a : α) : Ici (succ a) = Ioi a :=
  Ici_succ_of_not_is_max <| not_is_max _

@[simp]
theorem Ico_succ_right (a b : α) : Ico a (succ b) = Icc a b :=
  Ico_succ_right_of_not_is_max <| not_is_max _

@[simp]
theorem Ioo_succ_right (a b : α) : Ioo a (succ b) = Ioc a b :=
  Ioo_succ_right_of_not_is_max <| not_is_max _

@[simp]
theorem Icc_succ_left (a b : α) : Icc (succ a) b = Ioc a b :=
  Icc_succ_left_of_not_is_max <| not_is_max _

@[simp]
theorem Ico_succ_left (a b : α) : Ico (succ a) b = Ioo a b :=
  Ico_succ_left_of_not_is_max <| not_is_max _

end NoMaxOrder

end Preorderₓ

section PartialOrderₓ

variable [PartialOrderₓ α] [SuccOrder α] {a b : α}

@[simp]
theorem succ_eq_iff_is_max : succ a = a ↔ IsMax a :=
  ⟨fun h => max_of_succ_le h.le, fun h => h.eq_of_ge <| le_succ _⟩

alias succ_eq_iff_is_max ↔ _ _root_.is_max.succ_eq

theorem le_le_succ_iff : a ≤ b ∧ b ≤ succ a ↔ b = a ∨ b = succ a := by
  refine'
    ⟨fun h => or_iff_not_imp_left.2 fun hba : b ≠ a => h.2.antisymm (succ_le_of_lt <| h.1.lt_of_ne <| hba.symm), _⟩
  rintro (rfl | rfl)
  · exact ⟨le_rfl, le_succ b⟩
    
  · exact ⟨le_succ a, le_rfl⟩
    

theorem _root_.covby.succ_eq (h : a ⋖ b) : succ a = b :=
  (succ_le_of_lt h.lt).eq_of_not_lt fun h' => h.2 (lt_succ_of_not_is_max h.lt.not_is_max) h'

theorem le_succ_iff_eq_or_le : a ≤ succ b ↔ a = succ b ∨ a ≤ b := by
  by_cases' hb : IsMax b
  · rw [hb.succ_eq, or_iff_right_of_imp le_of_eqₓ]
    
  · rw [← lt_succ_iff_of_not_is_max hb, le_iff_eq_or_lt]
    

theorem lt_succ_iff_eq_or_lt_of_not_is_max (hb : ¬IsMax b) : a < succ b ↔ a = b ∨ a < b :=
  (lt_succ_iff_of_not_is_max hb).trans le_iff_eq_or_lt

theorem Iic_succ (a : α) : Iic (succ a) = insert (succ a) (Iic a) :=
  ext fun _ => le_succ_iff_eq_or_le

theorem Icc_succ_right (h : a ≤ succ b) : Icc a (succ b) = insert (succ b) (Icc a b) := by
  simp_rw [← Ici_inter_Iic, Iic_succ, inter_insert_of_mem (mem_Ici.2 h)]

theorem Ioc_succ_right (h : a < succ b) : Ioc a (succ b) = insert (succ b) (Ioc a b) := by
  simp_rw [← Ioi_inter_Iic, Iic_succ, inter_insert_of_mem (mem_Ioi.2 h)]

theorem Iio_succ_eq_insert_of_not_is_max (h : ¬IsMax a) : Iio (succ a) = insert a (Iio a) :=
  ext fun _ => lt_succ_iff_eq_or_lt_of_not_is_max h

theorem Ico_succ_right_eq_insert_of_not_is_max (h₁ : a ≤ b) (h₂ : ¬IsMax b) : Ico a (succ b) = insert b (Ico a b) := by
  simp_rw [← Iio_inter_Ici, Iio_succ_eq_insert_of_not_is_max h₂, insert_inter_of_mem (mem_Ici.2 h₁)]

theorem Ioo_succ_right_eq_insert_of_not_is_max (h₁ : a < b) (h₂ : ¬IsMax b) : Ioo a (succ b) = insert b (Ioo a b) := by
  simp_rw [← Iio_inter_Ioi, Iio_succ_eq_insert_of_not_is_max h₂, insert_inter_of_mem (mem_Ioi.2 h₁)]

section NoMaxOrder

variable [NoMaxOrder α]

@[simp]
theorem succ_eq_succ_iff : succ a = succ b ↔ a = b := by
  simp_rw [eq_iff_le_not_lt, succ_le_succ_iff, succ_lt_succ_iff]

theorem succ_injective : Injective (succ : α → α) := fun a b => succ_eq_succ_iff.1

theorem succ_ne_succ_iff : succ a ≠ succ b ↔ a ≠ b :=
  succ_injective.ne_iff

alias succ_ne_succ_iff ↔ _ succ_ne_succ

theorem lt_succ_iff_eq_or_lt : a < succ b ↔ a = b ∨ a < b :=
  lt_succ_iff.trans le_iff_eq_or_lt

theorem succ_eq_iff_covby : succ a = b ↔ a ⋖ b :=
  ⟨by
    rintro rfl
    exact covby_succ _, Covby.succ_eq⟩

theorem Iio_succ_eq_insert (a : α) : Iio (succ a) = insert a (Iio a) :=
  Iio_succ_eq_insert_of_not_is_max <| not_is_max a

theorem Ico_succ_right_eq_insert (h : a ≤ b) : Ico a (succ b) = insert b (Ico a b) :=
  Ico_succ_right_eq_insert_of_not_is_max h <| not_is_max b

theorem Ioo_succ_right_eq_insert (h : a < b) : Ioo a (succ b) = insert b (Ioo a b) :=
  Ioo_succ_right_eq_insert_of_not_is_max h <| not_is_max b

end NoMaxOrder

section OrderTop

variable [OrderTop α]

@[simp]
theorem succ_top : succ (⊤ : α) = ⊤ :=
  is_max_top.succ_eq

@[simp]
theorem succ_le_iff_eq_top : succ a ≤ a ↔ a = ⊤ :=
  succ_le_iff_is_max.trans is_max_iff_eq_top

@[simp]
theorem lt_succ_iff_ne_top : a < succ a ↔ a ≠ ⊤ :=
  lt_succ_iff_not_is_max.trans not_is_max_iff_ne_top

end OrderTop

section OrderBot

variable [OrderBot α] [Nontrivial α]

theorem bot_lt_succ (a : α) : ⊥ < succ a :=
  (lt_succ_of_not_is_max not_is_max_bot).trans_le <| succ_mono bot_le

theorem succ_ne_bot (a : α) : succ a ≠ ⊥ :=
  (bot_lt_succ a).ne'

end OrderBot

end PartialOrderₓ

/-- There is at most one way to define the successors in a `partial_order`. -/
instance [PartialOrderₓ α] : Subsingleton (SuccOrder α) :=
  ⟨by
    intro h₀ h₁
    ext a
    by_cases' ha : IsMax a
    · exact (@IsMax.succ_eq _ _ h₀ _ ha).trans ha.succ_eq.symm
      
    · exact @Covby.succ_eq _ _ h₀ _ _ (covby_succ_of_not_is_max ha)
      ⟩

section CompleteLattice

variable [CompleteLattice α] [SuccOrder α]

theorem succ_eq_infi (a : α) : succ a = ⨅ (b) (h : a < b), b := by
  refine' le_antisymmₓ (le_infi fun b => le_infi succ_le_of_lt) _
  obtain rfl | ha := eq_or_ne a ⊤
  · rw [succ_top]
    exact le_top
    
  exact infi₂_le _ (lt_succ_iff_ne_top.2 ha)

end CompleteLattice

/-! ### Predecessor order -/


section Preorderₓ

variable [Preorderₓ α] [PredOrder α] {a b : α}

/-- The predecessor of an element. If `a` is not minimal, then `pred a` is the greatest element less
than `a`. If `a` is minimal, then `pred a = a`. -/
def pred : α → α :=
  PredOrder.pred

theorem pred_le : ∀ a : α, pred a ≤ a :=
  PredOrder.pred_le

theorem min_of_le_pred {a : α} : a ≤ pred a → IsMin a :=
  PredOrder.min_of_le_pred

theorem le_pred_of_lt {a b : α} : a < b → a ≤ pred b :=
  PredOrder.le_pred_of_lt

theorem le_of_pred_lt {a b : α} : pred a < b → a ≤ b :=
  PredOrder.le_of_pred_lt

@[simp]
theorem le_pred_iff_is_min : a ≤ pred a ↔ IsMin a :=
  ⟨min_of_le_pred, fun h => h <| pred_le _⟩

@[simp]
theorem pred_lt_iff_not_is_min : pred a < a ↔ ¬IsMin a :=
  ⟨not_is_min_of_lt, fun ha => (pred_le a).lt_of_not_le fun h => ha <| min_of_le_pred h⟩

alias pred_lt_iff_not_is_min ↔ _ pred_lt_of_not_is_min

theorem pred_wcovby (a : α) : pred a ⩿ a :=
  ⟨pred_le a, fun b hb => (le_of_pred_lt hb).not_lt⟩

theorem pred_covby_of_not_is_min (h : ¬IsMin a) : pred a ⋖ a :=
  (pred_wcovby a).covby_of_lt <| pred_lt_of_not_is_min h

theorem pred_lt_iff_of_not_is_min (ha : ¬IsMin a) : pred a < b ↔ a ≤ b :=
  ⟨le_of_pred_lt, (pred_lt_of_not_is_min ha).trans_le⟩

theorem le_pred_iff_of_not_is_min (ha : ¬IsMin a) : b ≤ pred a ↔ b < a :=
  ⟨fun h => h.trans_lt <| pred_lt_of_not_is_min ha, le_pred_of_lt⟩

@[simp, mono]
theorem pred_le_pred {a b : α} (h : a ≤ b) : pred a ≤ pred b :=
  succ_le_succ h.dual

theorem pred_mono : Monotone (pred : α → α) := fun a b => pred_le_pred

theorem Ioi_pred_of_not_is_min (ha : ¬IsMin a) : Ioi (pred a) = Ici a :=
  Set.ext fun x => pred_lt_iff_of_not_is_min ha

theorem Iic_pred_of_not_is_min (ha : ¬IsMin a) : Iic (pred a) = Iio a :=
  Set.ext fun x => le_pred_iff_of_not_is_min ha

theorem Ioc_pred_left_of_not_is_min (ha : ¬IsMin a) : Ioc (pred a) b = Icc a b := by
  rw [← Ioi_inter_Iic, Ioi_pred_of_not_is_min ha, Ici_inter_Iic]

theorem Ioo_pred_left_of_not_is_min (ha : ¬IsMin a) : Ioo (pred a) b = Ico a b := by
  rw [← Ioi_inter_Iio, Ioi_pred_of_not_is_min ha, Ici_inter_Iio]

theorem Icc_pred_right_of_not_is_min (ha : ¬IsMin b) : Icc a (pred b) = Ico a b := by
  rw [← Ici_inter_Iic, Iic_pred_of_not_is_min ha, Ici_inter_Iio]

theorem Ioc_pred_right_of_not_is_min (ha : ¬IsMin b) : Ioc a (pred b) = Ioo a b := by
  rw [← Ioi_inter_Iic, Iic_pred_of_not_is_min ha, Ioi_inter_Iio]

section NoMinOrder

variable [NoMinOrder α]

theorem pred_lt (a : α) : pred a < a :=
  pred_lt_of_not_is_min <| not_is_min a

@[simp]
theorem pred_lt_iff : pred a < b ↔ a ≤ b :=
  pred_lt_iff_of_not_is_min <| not_is_min a

@[simp]
theorem le_pred_iff : a ≤ pred b ↔ a < b :=
  le_pred_iff_of_not_is_min <| not_is_min b

theorem pred_le_pred_iff : pred a ≤ pred b ↔ a ≤ b := by
  simp

theorem pred_lt_pred_iff : pred a < pred b ↔ a < b := by
  simp

alias pred_le_pred_iff ↔ le_of_pred_le_pred _

alias pred_lt_pred_iff ↔ lt_of_pred_lt_pred pred_lt_pred

theorem pred_strict_mono : StrictMono (pred : α → α) := fun a b => pred_lt_pred

theorem pred_covby (a : α) : pred a ⋖ a :=
  pred_covby_of_not_is_min <| not_is_min a

@[simp]
theorem Ioi_pred (a : α) : Ioi (pred a) = Ici a :=
  Ioi_pred_of_not_is_min <| not_is_min a

@[simp]
theorem Iic_pred (a : α) : Iic (pred a) = Iio a :=
  Iic_pred_of_not_is_min <| not_is_min a

@[simp]
theorem Ioc_pred_left (a b : α) : Ioc (pred a) b = Icc a b :=
  Ioc_pred_left_of_not_is_min <| not_is_min _

@[simp]
theorem Ioo_pred_left (a b : α) : Ioo (pred a) b = Ico a b :=
  Ioo_pred_left_of_not_is_min <| not_is_min _

@[simp]
theorem Icc_pred_right (a b : α) : Icc a (pred b) = Ico a b :=
  Icc_pred_right_of_not_is_min <| not_is_min _

@[simp]
theorem Ioc_pred_right (a b : α) : Ioc a (pred b) = Ioo a b :=
  Ioc_pred_right_of_not_is_min <| not_is_min _

end NoMinOrder

end Preorderₓ

section PartialOrderₓ

variable [PartialOrderₓ α] [PredOrder α] {a b : α}

@[simp]
theorem pred_eq_iff_is_min : pred a = a ↔ IsMin a :=
  ⟨fun h => min_of_le_pred h.Ge, fun h => h.eq_of_le <| pred_le _⟩

alias pred_eq_iff_is_min ↔ _ _root_.is_min.pred_eq

theorem pred_le_le_iff {a b : α} : pred a ≤ b ∧ b ≤ a ↔ b = a ∨ b = pred a := by
  refine' ⟨fun h => or_iff_not_imp_left.2 fun hba : b ≠ a => (le_pred_of_lt <| h.2.lt_of_ne hba).antisymm h.1, _⟩
  rintro (rfl | rfl)
  · exact ⟨pred_le b, le_rfl⟩
    
  · exact ⟨le_rfl, pred_le a⟩
    

theorem _root_.covby.pred_eq {a b : α} (h : a ⋖ b) : pred b = a :=
  (le_pred_of_lt h.lt).eq_of_not_gt fun h' => h.2 h' <| pred_lt_of_not_is_min h.lt.not_is_min

theorem pred_le_iff_eq_or_le : pred a ≤ b ↔ b = pred a ∨ a ≤ b := by
  by_cases' ha : IsMin a
  · rw [ha.pred_eq, or_iff_right_of_imp ge_of_eq]
    
  · rw [← pred_lt_iff_of_not_is_min ha, le_iff_eq_or_lt, eq_comm]
    

theorem pred_lt_iff_eq_or_lt_of_not_is_min (ha : ¬IsMin a) : pred a < b ↔ a = b ∨ a < b :=
  (pred_lt_iff_of_not_is_min ha).trans le_iff_eq_or_lt

theorem Ici_pred (a : α) : Ici (pred a) = insert (pred a) (Ici a) :=
  ext fun _ => pred_le_iff_eq_or_le

theorem Ioi_pred_eq_insert_of_not_is_min (ha : ¬IsMin a) : Ioi (pred a) = insert a (Ioi a) := by
  ext x
  simp only [← insert, ← mem_set_of, ← @eq_comm _ x a]
  exact pred_lt_iff_eq_or_lt_of_not_is_min ha

theorem Icc_pred_left (h : pred a ≤ b) : Icc (pred a) b = insert (pred a) (Icc a b) := by
  simp_rw [← Ici_inter_Iic, Ici_pred, insert_inter_of_mem (mem_Iic.2 h)]

theorem Ico_pred_left (h : pred a < b) : Ico (pred a) b = insert (pred a) (Ico a b) := by
  simp_rw [← Ici_inter_Iio, Ici_pred, insert_inter_of_mem (mem_Iio.2 h)]

section NoMinOrder

variable [NoMinOrder α]

@[simp]
theorem pred_eq_pred_iff : pred a = pred b ↔ a = b := by
  simp_rw [eq_iff_le_not_lt, pred_le_pred_iff, pred_lt_pred_iff]

theorem pred_injective : Injective (pred : α → α) := fun a b => pred_eq_pred_iff.1

theorem pred_ne_pred_iff : pred a ≠ pred b ↔ a ≠ b :=
  pred_injective.ne_iff

alias pred_ne_pred_iff ↔ _ pred_ne_pred

theorem pred_lt_iff_eq_or_lt : pred a < b ↔ a = b ∨ a < b :=
  pred_lt_iff.trans le_iff_eq_or_lt

theorem pred_eq_iff_covby : pred b = a ↔ a ⋖ b :=
  ⟨by
    rintro rfl
    exact pred_covby _, Covby.pred_eq⟩

theorem Ioi_pred_eq_insert (a : α) : Ioi (pred a) = insert a (Ioi a) :=
  ext fun _ => pred_lt_iff_eq_or_lt.trans <| or_congr_left' eq_comm

theorem Ico_pred_right_eq_insert (h : a ≤ b) : Ioc (pred a) b = insert a (Ioc a b) := by
  simp_rw [← Ioi_inter_Iic, Ioi_pred_eq_insert, insert_inter_of_mem (mem_Iic.2 h)]

theorem Ioo_pred_right_eq_insert (h : a < b) : Ioo (pred a) b = insert a (Ioo a b) := by
  simp_rw [← Ioi_inter_Iio, Ioi_pred_eq_insert, insert_inter_of_mem (mem_Iio.2 h)]

end NoMinOrder

section OrderBot

variable [OrderBot α]

@[simp]
theorem pred_bot : pred (⊥ : α) = ⊥ :=
  is_min_bot.pred_eq

@[simp]
theorem le_pred_iff_eq_bot : a ≤ pred a ↔ a = ⊥ :=
  @succ_le_iff_eq_top αᵒᵈ _ _ _ _

@[simp]
theorem pred_lt_iff_ne_bot : pred a < a ↔ a ≠ ⊥ :=
  @lt_succ_iff_ne_top αᵒᵈ _ _ _ _

end OrderBot

section OrderTop

variable [OrderTop α] [Nontrivial α]

theorem pred_lt_top (a : α) : pred a < ⊤ :=
  (pred_mono le_top).trans_lt <| pred_lt_of_not_is_min not_is_min_top

theorem pred_ne_top (a : α) : pred a ≠ ⊤ :=
  (pred_lt_top a).Ne

end OrderTop

end PartialOrderₓ

/-- There is at most one way to define the predecessors in a `partial_order`. -/
instance [PartialOrderₓ α] : Subsingleton (PredOrder α) :=
  ⟨by
    intro h₀ h₁
    ext a
    by_cases' ha : IsMin a
    · exact (@IsMin.pred_eq _ _ h₀ _ ha).trans ha.pred_eq.symm
      
    · exact @Covby.pred_eq _ _ h₀ _ _ (pred_covby_of_not_is_min ha)
      ⟩

section CompleteLattice

variable [CompleteLattice α] [PredOrder α]

theorem pred_eq_supr (a : α) : pred a = ⨆ (b) (h : b < a), b := by
  refine' le_antisymmₓ _ (supr_le fun b => supr_le le_pred_of_lt)
  obtain rfl | ha := eq_or_ne a ⊥
  · rw [pred_bot]
    exact bot_le
    
  · exact @le_supr₂ _ _ (fun b => b < a) _ (fun a _ => a) (pred a) (pred_lt_iff_ne_bot.2 ha)
    

end CompleteLattice

/-! ### Successor-predecessor orders -/


section SuccPredOrder

variable [PartialOrderₓ α] [SuccOrder α] [PredOrder α] {a b : α}

@[simp]
theorem succ_pred_of_not_is_min (h : ¬IsMin a) : succ (pred a) = a :=
  (pred_covby_of_not_is_min h).succ_eq

@[simp]
theorem pred_succ_of_not_is_max (h : ¬IsMax a) : pred (succ a) = a :=
  (covby_succ_of_not_is_max h).pred_eq

@[simp]
theorem succ_pred [NoMinOrder α] (a : α) : succ (pred a) = a :=
  (pred_covby _).succ_eq

@[simp]
theorem pred_succ [NoMaxOrder α] (a : α) : pred (succ a) = a :=
  (covby_succ _).pred_eq

end SuccPredOrder

end Order

open Order

/-! ### `with_bot`, `with_top`
Adding a greatest/least element to a `succ_order` or to a `pred_order`.

As far as successors and predecessors are concerned, there are four ways to add a bottom or top
element to an order:
* Adding a `⊤` to an `order_top`: Preserves `succ` and `pred`.
* Adding a `⊤` to a `no_max_order`: Preserves `succ`. Never preserves `pred`.
* Adding a `⊥` to an `order_bot`: Preserves `succ` and `pred`.
* Adding a `⊥` to a `no_min_order`: Preserves `pred`. Never preserves `succ`.
where "preserves `(succ/pred)`" means
`(succ/pred)_order α → (succ/pred)_order ((with_top/with_bot) α)`.
-/


namespace WithTop

/-! #### Adding a `⊤` to an `order_top` -/


section Succ

variable [DecidableEq α] [PartialOrderₓ α] [OrderTop α] [SuccOrder α]

instance : SuccOrder (WithTop α) where
  succ := fun a =>
    match a with
    | ⊤ => ⊤
    | some a => ite (a = ⊤) ⊤ (some (succ a))
  le_succ := fun a => by
    cases a
    · exact le_top
      
    change _ ≤ ite _ _ _
    split_ifs
    · exact le_top
      
    · exact some_le_some.2 (le_succ a)
      
  max_of_succ_le := fun a ha => by
    cases a
    · exact is_max_top
      
    change ite _ _ _ ≤ _ at ha
    split_ifs  at ha with ha'
    · exact (not_top_le_coe _ ha).elim
      
    · rw [some_le_some, succ_le_iff_eq_top] at ha
      exact (ha' ha).elim
      
  succ_le_of_lt := fun a b h => by
    cases b
    · exact le_top
      
    cases a
    · exact (not_top_lt h).elim
      
    rw [some_lt_some] at h
    change ite _ _ _ ≤ _
    split_ifs with ha
    · rw [ha] at h
      exact (not_top_lt h).elim
      
    · exact some_le_some.2 (succ_le_of_lt h)
      
  le_of_lt_succ := fun a b h => by
    cases a
    · exact (not_top_lt h).elim
      
    cases b
    · exact le_top
      
    change _ < ite _ _ _ at h
    rw [some_le_some]
    split_ifs  at h with hb
    · rw [hb]
      exact le_top
      
    · exact le_of_lt_succ (some_lt_some.1 h)
      

@[simp]
theorem succ_coe_top : succ ↑(⊤ : α) = (⊤ : WithTop α) :=
  dif_pos rfl

theorem succ_coe_of_ne_top {a : α} (h : a ≠ ⊤) : succ (↑a : WithTop α) = ↑(succ a) :=
  dif_neg h

end Succ

section Pred

variable [Preorderₓ α] [OrderTop α] [PredOrder α]

instance : PredOrder (WithTop α) where
  pred := fun a =>
    match a with
    | ⊤ => some ⊤
    | some a => some (pred a)
  pred_le := fun a =>
    match a with
    | ⊤ => le_top
    | some a => some_le_some.2 (pred_le a)
  min_of_le_pred := fun a ha => by
    cases a
    · exact ((coe_lt_top (⊤ : α)).not_le ha).elim
      
    · exact (min_of_le_pred <| some_le_some.1 ha).WithTop
      
  le_pred_of_lt := fun a b h => by
    cases a
    · exact (le_top.not_lt h).elim
      
    cases b
    · exact some_le_some.2 le_top
      
    exact some_le_some.2 (le_pred_of_lt <| some_lt_some.1 h)
  le_of_pred_lt := fun a b h => by
    cases b
    · exact le_top
      
    cases a
    · exact (not_top_lt <| some_lt_some.1 h).elim
      
    · exact some_le_some.2 (le_of_pred_lt <| some_lt_some.1 h)
      

@[simp]
theorem pred_top : pred (⊤ : WithTop α) = ↑(⊤ : α) :=
  rfl

@[simp]
theorem pred_coe (a : α) : pred (↑a : WithTop α) = ↑(pred a) :=
  rfl

end Pred

/-! #### Adding a `⊤` to a `no_max_order` -/


section Succ

variable [Preorderₓ α] [NoMaxOrder α] [SuccOrder α]

instance succOrderOfNoMaxOrder : SuccOrder (WithTop α) where
  succ := fun a =>
    match a with
    | ⊤ => ⊤
    | some a => some (succ a)
  le_succ := fun a => by
    cases a
    · exact le_top
      
    · exact some_le_some.2 (le_succ a)
      
  max_of_succ_le := fun a ha => by
    cases a
    · exact is_max_top
      
    · exact (not_is_max _ <| max_of_succ_le <| some_le_some.1 ha).elim
      
  succ_le_of_lt := fun a b h => by
    cases a
    · exact (not_top_lt h).elim
      
    cases b
    · exact le_top
      
    · exact some_le_some.2 (succ_le_of_lt <| some_lt_some.1 h)
      
  le_of_lt_succ := fun a b h => by
    cases a
    · exact (not_top_lt h).elim
      
    cases b
    · exact le_top
      
    · exact some_le_some.2 (le_of_lt_succ <| some_lt_some.1 h)
      

@[simp]
theorem succ_coe (a : α) : succ (↑a : WithTop α) = ↑(succ a) :=
  rfl

end Succ

section Pred

variable [Preorderₓ α] [NoMaxOrder α]

instance [hα : Nonempty α] : IsEmpty (PredOrder (WithTop α)) :=
  ⟨by
    intro
    cases' h : pred (⊤ : WithTop α) with a ha
    · exact hα.elim fun a => (min_of_le_pred h.ge).not_lt <| coe_lt_top a
      
    · obtain ⟨c, hc⟩ := exists_gt a
      rw [← some_lt_some, ← h] at hc
      exact (le_of_pred_lt hc).not_lt (some_lt_none _)
      ⟩

end Pred

end WithTop

namespace WithBot

/-! #### Adding a `⊥` to an `order_bot` -/


section Succ

variable [Preorderₓ α] [OrderBot α] [SuccOrder α]

instance : SuccOrder (WithBot α) where
  succ := fun a =>
    match a with
    | ⊥ => some ⊥
    | some a => some (succ a)
  le_succ := fun a =>
    match a with
    | ⊥ => bot_le
    | some a => some_le_some.2 (le_succ a)
  max_of_succ_le := fun a ha => by
    cases a
    · exact ((none_lt_some (⊥ : α)).not_le ha).elim
      
    · exact (max_of_succ_le <| some_le_some.1 ha).WithBot
      
  succ_le_of_lt := fun a b h => by
    cases b
    · exact (not_lt_bot h).elim
      
    cases a
    · exact some_le_some.2 bot_le
      
    · exact some_le_some.2 (succ_le_of_lt <| some_lt_some.1 h)
      
  le_of_lt_succ := fun a b h => by
    cases a
    · exact bot_le
      
    cases b
    · exact (not_lt_bot <| some_lt_some.1 h).elim
      
    · exact some_le_some.2 (le_of_lt_succ <| some_lt_some.1 h)
      

@[simp]
theorem succ_bot : succ (⊥ : WithBot α) = ↑(⊥ : α) :=
  rfl

@[simp]
theorem succ_coe (a : α) : succ (↑a : WithBot α) = ↑(succ a) :=
  rfl

end Succ

section Pred

variable [DecidableEq α] [PartialOrderₓ α] [OrderBot α] [PredOrder α]

instance : PredOrder (WithBot α) where
  pred := fun a =>
    match a with
    | ⊥ => ⊥
    | some a => ite (a = ⊥) ⊥ (some (pred a))
  pred_le := fun a => by
    cases a
    · exact bot_le
      
    change ite _ _ _ ≤ _
    split_ifs
    · exact bot_le
      
    · exact some_le_some.2 (pred_le a)
      
  min_of_le_pred := fun a ha => by
    cases a
    · exact is_min_bot
      
    change _ ≤ ite _ _ _ at ha
    split_ifs  at ha with ha'
    · exact (not_coe_le_bot _ ha).elim
      
    · rw [some_le_some, le_pred_iff_eq_bot] at ha
      exact (ha' ha).elim
      
  le_pred_of_lt := fun a b h => by
    cases a
    · exact bot_le
      
    cases b
    · exact (not_lt_bot h).elim
      
    rw [some_lt_some] at h
    change _ ≤ ite _ _ _
    split_ifs with hb
    · rw [hb] at h
      exact (not_lt_bot h).elim
      
    · exact some_le_some.2 (le_pred_of_lt h)
      
  le_of_pred_lt := fun a b h => by
    cases b
    · exact (not_lt_bot h).elim
      
    cases a
    · exact bot_le
      
    change ite _ _ _ < _ at h
    rw [some_le_some]
    split_ifs  at h with ha
    · rw [ha]
      exact bot_le
      
    · exact le_of_pred_lt (some_lt_some.1 h)
      

@[simp]
theorem pred_coe_bot : pred ↑(⊥ : α) = (⊥ : WithBot α) :=
  dif_pos rfl

theorem pred_coe_of_ne_bot {a : α} (h : a ≠ ⊥) : pred (↑a : WithBot α) = ↑(pred a) :=
  dif_neg h

end Pred

/-! #### Adding a `⊥` to a `no_min_order` -/


section Succ

variable [Preorderₓ α] [NoMinOrder α]

instance [hα : Nonempty α] : IsEmpty (SuccOrder (WithBot α)) :=
  ⟨by
    intro
    cases' h : succ (⊥ : WithBot α) with a ha
    · exact hα.elim fun a => (max_of_succ_le h.le).not_lt <| bot_lt_coe a
      
    · obtain ⟨c, hc⟩ := exists_lt a
      rw [← some_lt_some, ← h] at hc
      exact (le_of_lt_succ hc).not_lt (none_lt_some _)
      ⟩

end Succ

section Pred

variable [Preorderₓ α] [NoMinOrder α] [PredOrder α]

instance predOrderOfNoMinOrder : PredOrder (WithBot α) where
  pred := fun a =>
    match a with
    | ⊥ => ⊥
    | some a => some (pred a)
  pred_le := fun a => by
    cases a
    · exact bot_le
      
    · exact some_le_some.2 (pred_le a)
      
  min_of_le_pred := fun a ha => by
    cases a
    · exact is_min_bot
      
    · exact (not_is_min _ <| min_of_le_pred <| some_le_some.1 ha).elim
      
  le_pred_of_lt := fun a b h => by
    cases b
    · exact (not_lt_bot h).elim
      
    cases a
    · exact bot_le
      
    · exact some_le_some.2 (le_pred_of_lt <| some_lt_some.1 h)
      
  le_of_pred_lt := fun a b h => by
    cases b
    · exact (not_lt_bot h).elim
      
    cases a
    · exact bot_le
      
    · exact some_le_some.2 (le_of_pred_lt <| some_lt_some.1 h)
      

@[simp]
theorem pred_coe (a : α) : pred (↑a : WithBot α) = ↑(pred a) :=
  rfl

end Pred

end WithBot

/-! ### Archimedeanness -/


/-- A `succ_order` is succ-archimedean if one can go from any two comparable elements by iterating
`succ` -/
class IsSuccArchimedean (α : Type _) [Preorderₓ α] [SuccOrder α] : Prop where
  exists_succ_iterate_of_le {a b : α} (h : a ≤ b) : ∃ n, (succ^[n]) a = b

/-- A `pred_order` is pred-archimedean if one can go from any two comparable elements by iterating
`pred` -/
class IsPredArchimedean (α : Type _) [Preorderₓ α] [PredOrder α] : Prop where
  exists_pred_iterate_of_le {a b : α} (h : a ≤ b) : ∃ n, (pred^[n]) b = a

export IsSuccArchimedean (exists_succ_iterate_of_le)

export IsPredArchimedean (exists_pred_iterate_of_le)

section Preorderₓ

variable [Preorderₓ α]

section SuccOrder

variable [SuccOrder α] [IsSuccArchimedean α] {a b : α}

instance : IsPredArchimedean αᵒᵈ :=
  ⟨fun a b h => by
    convert exists_succ_iterate_of_le h.of_dual⟩

theorem LE.le.exists_succ_iterate (h : a ≤ b) : ∃ n, (succ^[n]) a = b :=
  exists_succ_iterate_of_le h

theorem exists_succ_iterate_iff_le : (∃ n, (succ^[n]) a = b) ↔ a ≤ b := by
  refine' ⟨_, exists_succ_iterate_of_le⟩
  rintro ⟨n, rfl⟩
  exact id_le_iterate_of_id_le le_succ n a

/-- Induction principle on a type with a `succ_order` for all elements above a given element `m`. -/
@[elab_as_eliminator]
theorem Succ.rec {P : α → Prop} {m : α} (h0 : P m) (h1 : ∀ n, m ≤ n → P n → P (succ n)) ⦃n : α⦄ (hmn : m ≤ n) : P n :=
  by
  obtain ⟨n, rfl⟩ := hmn.exists_succ_iterate
  clear hmn
  induction' n with n ih
  · exact h0
    
  · rw [Function.iterate_succ_apply']
    exact h1 _ (id_le_iterate_of_id_le le_succ n m) ih
    

theorem Succ.rec_iff {p : α → Prop} (hsucc : ∀ a, p a ↔ p (succ a)) {a b : α} (h : a ≤ b) : p a ↔ p b := by
  obtain ⟨n, rfl⟩ := h.exists_succ_iterate
  exact iterate.rec (fun b => p a ↔ p b) (fun c hc => hc.trans (hsucc _)) Iff.rfl n

end SuccOrder

section PredOrder

variable [PredOrder α] [IsPredArchimedean α] {a b : α}

instance : IsSuccArchimedean αᵒᵈ :=
  ⟨fun a b h => by
    convert exists_pred_iterate_of_le h.of_dual⟩

theorem LE.le.exists_pred_iterate (h : a ≤ b) : ∃ n, (pred^[n]) b = a :=
  exists_pred_iterate_of_le h

theorem exists_pred_iterate_iff_le : (∃ n, (pred^[n]) b = a) ↔ a ≤ b :=
  @exists_succ_iterate_iff_le αᵒᵈ _ _ _ _ _

/-- Induction principle on a type with a `pred_order` for all elements below a given element `m`. -/
@[elab_as_eliminator]
theorem Pred.rec {P : α → Prop} {m : α} (h0 : P m) (h1 : ∀ n, n ≤ m → P n → P (pred n)) ⦃n : α⦄ (hmn : n ≤ m) : P n :=
  @Succ.rec αᵒᵈ _ _ _ _ _ h0 h1 _ hmn

theorem Pred.rec_iff {p : α → Prop} (hsucc : ∀ a, p a ↔ p (pred a)) {a b : α} (h : a ≤ b) : p a ↔ p b :=
  (@Succ.rec_iff αᵒᵈ _ _ _ _ hsucc _ _ h).symm

end PredOrder

end Preorderₓ

section LinearOrderₓ

variable [LinearOrderₓ α]

section SuccOrder

variable [SuccOrder α] [IsSuccArchimedean α] {a b : α}

theorem exists_succ_iterate_or : (∃ n, (succ^[n]) a = b) ∨ ∃ n, (succ^[n]) b = a :=
  (le_totalₓ a b).imp exists_succ_iterate_of_le exists_succ_iterate_of_le

theorem Succ.rec_linear {p : α → Prop} (hsucc : ∀ a, p a ↔ p (succ a)) (a b : α) : p a ↔ p b :=
  (le_totalₓ a b).elim (Succ.rec_iff hsucc) fun h => (Succ.rec_iff hsucc h).symm

end SuccOrder

section PredOrder

variable [PredOrder α] [IsPredArchimedean α] {a b : α}

theorem exists_pred_iterate_or : (∃ n, (pred^[n]) b = a) ∨ ∃ n, (pred^[n]) a = b :=
  (le_totalₓ a b).imp exists_pred_iterate_of_le exists_pred_iterate_of_le

theorem Pred.rec_linear {p : α → Prop} (hsucc : ∀ a, p a ↔ p (pred a)) (a b : α) : p a ↔ p b :=
  (le_totalₓ a b).elim (Pred.rec_iff hsucc) fun h => (Pred.rec_iff hsucc h).symm

end PredOrder

end LinearOrderₓ

section IsWellOrder

variable [LinearOrderₓ α]

instance (priority := 100) IsWellOrder.to_is_pred_archimedean [h : IsWellOrder α (· < ·)] [PredOrder α] :
    IsPredArchimedean α :=
  ⟨fun a => by
    refine' WellFounded.fix h.wf fun b ih hab => _
    replace hab := hab.eq_or_lt
    rcases hab with (rfl | hab)
    · exact ⟨0, rfl⟩
      
    cases' le_or_ltₓ b (pred b) with hb hb
    · cases (min_of_le_pred hb).not_lt hab
      
    obtain ⟨k, hk⟩ := ih (pred b) hb (le_pred_of_lt hab)
    refine' ⟨k + 1, _⟩
    rw [iterate_add_apply, iterate_one, hk]⟩

instance (priority := 100) IsWellOrder.to_is_succ_archimedean [h : IsWellOrder α (· > ·)] [SuccOrder α] :
    IsSuccArchimedean α := by
  convert @OrderDual.is_succ_archimedean αᵒᵈ _ _ _

end IsWellOrder

section OrderBot

variable [Preorderₓ α] [OrderBot α] [SuccOrder α] [IsSuccArchimedean α]

theorem Succ.rec_bot (p : α → Prop) (hbot : p ⊥) (hsucc : ∀ a, p a → p (succ a)) (a : α) : p a :=
  Succ.rec hbot (fun x _ h => hsucc x h) (bot_le : ⊥ ≤ a)

end OrderBot

section OrderTop

variable [Preorderₓ α] [OrderTop α] [PredOrder α] [IsPredArchimedean α]

theorem Pred.rec_top (p : α → Prop) (htop : p ⊤) (hpred : ∀ a, p a → p (pred a)) (a : α) : p a :=
  Pred.rec htop (fun x _ h => hpred x h) (le_top : a ≤ ⊤)

end OrderTop

