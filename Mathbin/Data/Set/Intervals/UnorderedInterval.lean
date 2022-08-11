/-
Copyright (c) 2020 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou
-/
import Mathbin.Order.Bounds
import Mathbin.Data.Set.Intervals.ImagePreimage

/-!
# Intervals without endpoints ordering

In any decidable linear order `α`, we define the set of elements lying between two elements `a` and
`b` as `Icc (min a b) (max a b)`.

`Icc a b` requires the assumption `a ≤ b` to be meaningful, which is sometimes inconvenient. The
interval as defined in this file is always the set of things lying between `a` and `b`, regardless
of the relative order of `a` and `b`.

For real numbers, `Icc (min a b) (max a b)` is the same as `segment ℝ a b`.

## Notation

We use the localized notation `[a, b]` for `interval a b`. One can open the locale `interval` to
make the notation available.

-/


universe u

open Pointwise

namespace Set

section LinearOrderₓ

variable {α : Type u} [LinearOrderₓ α] {a a₁ a₂ b b₁ b₂ c x : α}

/-- `interval a b` is the set of elements lying between `a` and `b`, with `a` and `b` included. -/
def Interval (a b : α) :=
  Icc (min a b) (max a b)

-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
@[simp]
theorem interval_of_le (h : a ≤ b) :
    "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)" = Icc a b := by
  rw [interval, min_eq_leftₓ h, max_eq_rightₓ h]

-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
@[simp]
theorem interval_of_ge (h : b ≤ a) :
    "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)" = Icc b a := by
  rw [interval, min_eq_rightₓ h, max_eq_leftₓ h]

-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
theorem interval_swap (a b : α) :
    "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)" =
      "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)" :=
  by
  rw [interval, interval, min_commₓ, max_commₓ]

-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
theorem interval_of_lt (h : a < b) :
    "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)" = Icc a b :=
  interval_of_le (le_of_ltₓ h)

-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
theorem interval_of_gt (h : b < a) :
    "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)" = Icc b a :=
  interval_of_ge (le_of_ltₓ h)

-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
theorem interval_of_not_le (h : ¬a ≤ b) :
    "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)" = Icc b a :=
  interval_of_gt (lt_of_not_geₓ h)

-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
theorem interval_of_not_ge (h : ¬b ≤ a) :
    "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)" = Icc a b :=
  interval_of_lt (lt_of_not_geₓ h)

-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
@[simp]
theorem interval_self : "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)" = {a} :=
  Set.ext <| by
    simp [← le_antisymm_iffₓ, ← and_comm]

-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
@[simp]
theorem nonempty_interval :
    Set.Nonempty "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)" := by
  simp only [← interval, ← min_le_iff, ← le_max_iff, ← nonempty_Icc]
  left
  left
  rfl

-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
@[simp]
theorem left_mem_interval : a ∈ "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)" := by
  rw [interval, mem_Icc]
  exact ⟨min_le_leftₓ _ _, le_max_leftₓ _ _⟩

-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
@[simp]
theorem right_mem_interval : b ∈ "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)" := by
  rw [interval_swap]
  exact left_mem_interval

-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
theorem Icc_subset_interval : Icc a b ⊆ "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)" :=
  by
  intro x h
  rwa [interval_of_le]
  exact le_transₓ h.1 h.2

-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
theorem Icc_subset_interval' :
    Icc b a ⊆ "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)" := by
  rw [interval_swap]
  apply Icc_subset_interval

-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
theorem mem_interval_of_le (ha : a ≤ x) (hb : x ≤ b) :
    x ∈ "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)" :=
  Icc_subset_interval ⟨ha, hb⟩

-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
theorem mem_interval_of_ge (hb : b ≤ x) (ha : x ≤ a) :
    x ∈ "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)" :=
  Icc_subset_interval' ⟨hb, ha⟩

theorem not_mem_interval_of_lt (ha : c < a) (hb : c < b) : c ∉ Interval a b :=
  not_mem_Icc_of_lt <| lt_min_iff.mpr ⟨ha, hb⟩

theorem not_mem_interval_of_gt (ha : a < c) (hb : b < c) : c ∉ Interval a b :=
  not_mem_Icc_of_gt <| max_lt_iff.mpr ⟨ha, hb⟩

-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
theorem interval_subset_interval
    (h₁ : a₁ ∈ "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)")
    (h₂ : b₁ ∈ "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)") :
    "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)" ⊆
      "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)" :=
  Icc_subset_Icc (le_minₓ h₁.1 h₂.1) (max_leₓ h₁.2 h₂.2)

-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
theorem interval_subset_Icc (ha : a₁ ∈ Icc a₂ b₂) (hb : b₁ ∈ Icc a₂ b₂) :
    "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)" ⊆ Icc a₂ b₂ :=
  Icc_subset_Icc (le_minₓ ha.1 hb.1) (max_leₓ ha.2 hb.2)

-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
theorem interval_subset_interval_iff_mem :
    "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)" ⊆
        "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)" ↔
      a₁ ∈ "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)" ∧
        b₁ ∈ "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)" :=
  Iff.intro (fun h => ⟨h left_mem_interval, h right_mem_interval⟩) fun h => interval_subset_interval h.1 h.2

-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
theorem interval_subset_interval_iff_le :
    "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)" ⊆
        "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)" ↔
      min a₂ b₂ ≤ min a₁ b₁ ∧ max a₁ b₁ ≤ max a₂ b₂ :=
  by
  rw [interval, interval, Icc_subset_Icc_iff]
  exact min_le_max

-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
theorem interval_subset_interval_right
    (h : x ∈ "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)") :
    "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)" ⊆
      "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)" :=
  interval_subset_interval h right_mem_interval

-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
theorem interval_subset_interval_left
    (h : x ∈ "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)") :
    "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)" ⊆
      "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)" :=
  interval_subset_interval left_mem_interval h

-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
/-- A sort of triangle inequality. -/
theorem interval_subset_interval_union_interval :
    "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)" ⊆
      "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)" ∪
        "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)" :=
  by
  rintro x hx
  obtain hac | hac := le_totalₓ a c
  · rw [interval_of_le hac] at hx
    obtain hb | hb := le_totalₓ x b
    · exact Or.inl (mem_interval_of_le hx.1 hb)
      
    · exact Or.inr (mem_interval_of_le hb hx.2)
      
    
  · rw [interval_of_ge hac] at hx
    obtain hb | hb := le_totalₓ x b
    · exact Or.inr (mem_interval_of_ge hx.1 hb)
      
    · exact Or.inl (mem_interval_of_ge hb hx.2)
      
    

-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
theorem bdd_below_bdd_above_iff_subset_interval (s : Set α) :
    BddBelow s ∧ BddAbove s ↔
      ∃ a b, s ⊆ "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)" :=
  by
  rw [bdd_below_bdd_above_iff_subset_Icc]
  constructor
  · rintro ⟨a, b, h⟩
    exact ⟨a, b, fun x hx => Icc_subset_interval (h hx)⟩
    
  · rintro ⟨a, b, h⟩
    exact ⟨min a b, max a b, h⟩
    

/-- The open-closed interval with unordered bounds. -/
def IntervalOc : α → α → Set α := fun a b => Ioc (min a b) (max a b)

-- mathport name: «exprΙ»
-- Below is a capital iota
localized [Interval] notation "Ι" => Set.IntervalOc

theorem interval_oc_of_le (h : a ≤ b) : Ι a b = Ioc a b := by
  simp [← interval_oc, ← h]

theorem interval_oc_of_lt (h : b < a) : Ι a b = Ioc b a := by
  simp [← interval_oc, ← le_of_ltₓ h]

theorem interval_oc_eq_union : Ι a b = Ioc a b ∪ Ioc b a := by
  cases le_totalₓ a b <;> simp [← interval_oc, *]

theorem forall_interval_oc_iff {P : α → Prop} :
    (∀, ∀ x ∈ Ι a b, ∀, P x) ↔ (∀, ∀ x ∈ Ioc a b, ∀, P x) ∧ ∀, ∀ x ∈ Ioc b a, ∀, P x := by
  simp only [← interval_oc_eq_union, ← mem_union_eq, ← or_imp_distrib, ← forall_and_distrib]

-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
theorem interval_oc_subset_interval_oc_of_interval_subset_interval {a b c d : α}
    (h :
      "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)" ⊆
        "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)") :
    Ι a b ⊆ Ι c d :=
  Ioc_subset_Ioc (interval_subset_interval_iff_le.1 h).1 (interval_subset_interval_iff_le.1 h).2

theorem interval_oc_swap (a b : α) : Ι a b = Ι b a := by
  simp only [← interval_oc, ← min_commₓ a b, ← max_commₓ a b]

end LinearOrderₓ

open Interval

section OrderedAddCommGroup

variable {α : Type u} [LinearOrderedAddCommGroup α] (a b c x y : α)

-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
@[simp]
theorem preimage_const_add_interval :
    (fun x => a + x) ⁻¹' "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)" =
      "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)" :=
  by
  simp only [← interval, ← preimage_const_add_Icc, ← min_sub_sub_right, ← max_sub_sub_right]

-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
@[simp]
theorem preimage_add_const_interval :
    (fun x => x + a) ⁻¹' "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)" =
      "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)" :=
  by
  simpa only [← add_commₓ] using preimage_const_add_interval a b c

-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
@[simp]
theorem preimage_neg_interval :
    -"./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)" =
      "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)" :=
  by
  simp only [← interval, ← preimage_neg_Icc, ← min_neg_neg, ← max_neg_neg]

-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
@[simp]
theorem preimage_sub_const_interval :
    (fun x => x - a) ⁻¹' "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)" =
      "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)" :=
  by
  simp [← sub_eq_add_neg]

-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
@[simp]
theorem preimage_const_sub_interval :
    (fun x => a - x) ⁻¹' "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)" =
      "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)" :=
  by
  rw [interval, interval, preimage_const_sub_Icc]
  simp only [← sub_eq_add_neg, ← min_add_add_left, ← max_add_add_left, ← min_neg_neg, ← max_neg_neg]

-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
@[simp]
theorem image_const_add_interval :
    (fun x => a + x) '' "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)" =
      "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)" :=
  by
  simp [← add_commₓ]

-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
@[simp]
theorem image_add_const_interval :
    (fun x => x + a) '' "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)" =
      "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)" :=
  by
  simp

-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
@[simp]
theorem image_const_sub_interval :
    (fun x => a - x) '' "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)" =
      "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)" :=
  by
  simp [← sub_eq_add_neg, ← image_comp (fun x => a + x) fun x => -x]

-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
@[simp]
theorem image_sub_const_interval :
    (fun x => x - a) '' "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)" =
      "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)" :=
  by
  simp [← sub_eq_add_neg, ← add_commₓ]

-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
theorem image_neg_interval :
    Neg.neg '' "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)" =
      "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)" :=
  by
  simp

variable {a b c x y}

-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
/-- If `[x, y]` is a subinterval of `[a, b]`, then the distance between `x` and `y`
is less than or equal to that of `a` and `b` -/
theorem abs_sub_le_of_subinterval
    (h :
      "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)" ⊆
        "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)") :
    abs (y - x) ≤ abs (b - a) := by
  rw [← max_sub_min_eq_abs, ← max_sub_min_eq_abs]
  rw [interval_subset_interval_iff_le] at h
  exact sub_le_sub h.2 h.1

-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
/-- If `x ∈ [a, b]`, then the distance between `a` and `x` is less than or equal to
that of `a` and `b`  -/
theorem abs_sub_left_of_mem_interval
    (h : x ∈ "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)") :
    abs (x - a) ≤ abs (b - a) :=
  abs_sub_le_of_subinterval (interval_subset_interval_left h)

-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
/-- If `x ∈ [a, b]`, then the distance between `x` and `b` is less than or equal to
that of `a` and `b`  -/
theorem abs_sub_right_of_mem_interval
    (h : x ∈ "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)") :
    abs (b - x) ≤ abs (b - a) :=
  abs_sub_le_of_subinterval (interval_subset_interval_right h)

end OrderedAddCommGroup

section LinearOrderedField

variable {k : Type u} [LinearOrderedField k] {a : k}

-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
@[simp]
theorem preimage_mul_const_interval (ha : a ≠ 0) (b c : k) :
    (fun x => x * a) ⁻¹' "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)" =
      "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)" :=
  (lt_or_gt_of_neₓ ha).elim
    (fun ha => by
      simp [← interval, ← ha, ← ha.le, ← min_div_div_right_of_nonpos, ← max_div_div_right_of_nonpos])
    fun ha : 0 < a => by
    simp [← interval, ← ha, ← ha.le, ← min_div_div_right, ← max_div_div_right]

-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
@[simp]
theorem preimage_const_mul_interval (ha : a ≠ 0) (b c : k) :
    (fun x => a * x) ⁻¹' "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)" =
      "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)" :=
  by
  simp only [preimage_mul_const_interval ha, ← mul_comm]

-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
@[simp]
theorem preimage_div_const_interval (ha : a ≠ 0) (b c : k) :
    (fun x => x / a) ⁻¹' "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)" =
      "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)" :=
  by
  simp only [← div_eq_mul_inv, ← preimage_mul_const_interval (inv_ne_zero ha), ← inv_invₓ]

-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
@[simp]
theorem image_mul_const_interval (a b c : k) :
    (fun x => x * a) '' "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)" =
      "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)" :=
  if ha : a = 0 then by
    simp [← ha]
  else
    calc
      (fun x => x * a) '' "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)" =
          (fun x => x * a⁻¹) ⁻¹' "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)" :=
        (Units.mk0 a ha).mul_right.image_eq_preimage _
      _ = (fun x => x / a) ⁻¹' "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)" := by
        simp only [← div_eq_mul_inv]
      _ = "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)" :=
        preimage_div_const_interval ha _ _
      

-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
@[simp]
theorem image_const_mul_interval (a b c : k) :
    (fun x => a * x) '' "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)" =
      "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)" :=
  by
  simpa only [← mul_comm] using image_mul_const_interval a b c

-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
@[simp]
theorem image_div_const_interval (a b c : k) :
    (fun x => x / a) '' "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)" =
      "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)" :=
  by
  simp only [← div_eq_mul_inv, ← image_mul_const_interval]

end LinearOrderedField

end Set

