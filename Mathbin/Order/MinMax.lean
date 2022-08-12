/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathbin.Order.Lattice

/-!
# `max` and `min`

This file proves basic properties about maxima and minima on a `linear_order`.

## Tags

min, max
-/


universe u v

variable {α : Type u} {β : Type v}

attribute [simp] max_eq_leftₓ max_eq_rightₓ min_eq_leftₓ min_eq_rightₓ

section

variable [LinearOrderₓ α] [LinearOrderₓ β] {f : α → β} {s : Set α} {a b c d : α}

-- translate from lattices to linear orders (sup → max, inf → min)
@[simp]
theorem le_min_iff : c ≤ min a b ↔ c ≤ a ∧ c ≤ b :=
  le_inf_iff

@[simp]
theorem le_max_iff : a ≤ max b c ↔ a ≤ b ∨ a ≤ c :=
  le_sup_iff

@[simp]
theorem min_le_iff : min a b ≤ c ↔ a ≤ c ∨ b ≤ c :=
  inf_le_iff

@[simp]
theorem max_le_iff : max a b ≤ c ↔ a ≤ c ∧ b ≤ c :=
  sup_le_iff

@[simp]
theorem lt_min_iff : a < min b c ↔ a < b ∧ a < c :=
  lt_inf_iff

@[simp]
theorem lt_max_iff : a < max b c ↔ a < b ∨ a < c :=
  lt_sup_iff

@[simp]
theorem min_lt_iff : min a b < c ↔ a < c ∨ b < c :=
  inf_lt_iff

@[simp]
theorem max_lt_iff : max a b < c ↔ a < c ∧ b < c :=
  sup_lt_iff

theorem max_le_max : a ≤ c → b ≤ d → max a b ≤ max c d :=
  sup_le_sup

theorem min_le_min : a ≤ c → b ≤ d → min a b ≤ min c d :=
  inf_le_inf

theorem le_max_of_le_left : a ≤ b → a ≤ max b c :=
  le_sup_of_le_left

theorem le_max_of_le_right : a ≤ c → a ≤ max b c :=
  le_sup_of_le_right

theorem lt_max_of_lt_left (h : a < b) : a < max b c :=
  h.trans_le (le_max_leftₓ b c)

theorem lt_max_of_lt_right (h : a < c) : a < max b c :=
  h.trans_le (le_max_rightₓ b c)

theorem min_le_of_left_le : a ≤ c → min a b ≤ c :=
  inf_le_of_left_le

theorem min_le_of_right_le : b ≤ c → min a b ≤ c :=
  inf_le_of_right_le

theorem min_lt_of_left_lt (h : a < c) : min a b < c :=
  (min_le_leftₓ a b).trans_lt h

theorem min_lt_of_right_lt (h : b < c) : min a b < c :=
  (min_le_rightₓ a b).trans_lt h

theorem max_min_distrib_left : max a (min b c) = min (max a b) (max a c) :=
  sup_inf_left

theorem max_min_distrib_right : max (min a b) c = min (max a c) (max b c) :=
  sup_inf_right

theorem min_max_distrib_left : min a (max b c) = max (min a b) (min a c) :=
  inf_sup_left

theorem min_max_distrib_right : min (max a b) c = max (min a c) (min b c) :=
  inf_sup_right

theorem min_le_max : min a b ≤ max a b :=
  le_transₓ (min_le_leftₓ a b) (le_max_leftₓ a b)

@[simp]
theorem min_eq_left_iff : min a b = a ↔ a ≤ b :=
  inf_eq_left

@[simp]
theorem min_eq_right_iff : min a b = b ↔ b ≤ a :=
  inf_eq_right

@[simp]
theorem max_eq_left_iff : max a b = a ↔ b ≤ a :=
  sup_eq_left

@[simp]
theorem max_eq_right_iff : max a b = b ↔ a ≤ b :=
  sup_eq_right

/-- For elements `a` and `b` of a linear order, either `min a b = a` and `a ≤ b`,
    or `min a b = b` and `b < a`.
    Use cases on this lemma to automate linarith in inequalities -/
theorem min_cases (a b : α) : min a b = a ∧ a ≤ b ∨ min a b = b ∧ b < a := by
  by_cases' a ≤ b
  · left
    exact ⟨min_eq_leftₓ h, h⟩
    
  · right
    exact ⟨min_eq_rightₓ (le_of_ltₓ (not_le.mp h)), not_le.mp h⟩
    

/-- For elements `a` and `b` of a linear order, either `max a b = a` and `b ≤ a`,
    or `max a b = b` and `a < b`.
    Use cases on this lemma to automate linarith in inequalities -/
theorem max_cases (a b : α) : max a b = a ∧ b ≤ a ∨ max a b = b ∧ a < b :=
  @min_cases αᵒᵈ _ a b

theorem min_eq_iff : min a b = c ↔ a = c ∧ a ≤ b ∨ b = c ∧ b ≤ a := by
  constructor
  · intro h
    refine' Or.imp (fun h' => _) (fun h' => _) (le_totalₓ a b) <;>
      exact
        ⟨by
          simpa [← h'] using h, h'⟩
    
  · rintro (⟨rfl, h⟩ | ⟨rfl, h⟩) <;> simp [← h]
    

theorem max_eq_iff : max a b = c ↔ a = c ∧ b ≤ a ∨ b = c ∧ a ≤ b :=
  @min_eq_iff αᵒᵈ _ a b c

theorem min_lt_min_left_iff : min a c < min b c ↔ a < b ∧ a < c := by
  simp_rw [lt_min_iff, min_lt_iff, or_iff_left (lt_irreflₓ _)]
  exact and_congr_left fun h => or_iff_left_of_imp h.trans

theorem min_lt_min_right_iff : min a b < min a c ↔ b < c ∧ b < a := by
  simp_rw [min_commₓ a, min_lt_min_left_iff]

theorem max_lt_max_left_iff : max a c < max b c ↔ a < b ∧ c < b :=
  @min_lt_min_left_iff αᵒᵈ _ _ _ _

theorem max_lt_max_right_iff : max a b < max a c ↔ b < c ∧ a < c :=
  @min_lt_min_right_iff αᵒᵈ _ _ _ _

/-- An instance asserting that `max a a = a` -/
instance max_idem : IsIdempotent α max := by
  infer_instance

/-- An instance asserting that `min a a = a` -/
-- short-circuit type class inference
instance min_idem : IsIdempotent α min := by
  infer_instance

-- short-circuit type class inference
theorem min_lt_max : min a b < max a b ↔ a ≠ b :=
  inf_lt_sup

theorem max_lt_max (h₁ : a < c) (h₂ : b < d) : max a b < max c d := by
  simp [← lt_max_iff, ← max_lt_iff, *]

theorem min_lt_min (h₁ : a < c) (h₂ : b < d) : min a b < min c d :=
  @max_lt_max αᵒᵈ _ _ _ _ _ h₁ h₂

theorem min_right_comm (a b c : α) : min (min a b) c = min (min a c) b :=
  right_comm min min_commₓ min_assocₓ a b c

theorem Max.left_comm (a b c : α) : max a (max b c) = max b (max a c) :=
  left_comm max max_commₓ max_assocₓ a b c

theorem Max.right_comm (a b c : α) : max (max a b) c = max (max a c) b :=
  right_comm max max_commₓ max_assocₓ a b c

theorem MonotoneOn.map_max (hf : MonotoneOn f s) (ha : a ∈ s) (hb : b ∈ s) : f (max a b) = max (f a) (f b) := by
  cases le_totalₓ a b <;> simp only [← max_eq_rightₓ, ← max_eq_leftₓ, ← hf ha hb, ← hf hb ha, ← h]

theorem MonotoneOn.map_min (hf : MonotoneOn f s) (ha : a ∈ s) (hb : b ∈ s) : f (min a b) = min (f a) (f b) :=
  hf.dual.map_max ha hb

theorem AntitoneOn.map_max (hf : AntitoneOn f s) (ha : a ∈ s) (hb : b ∈ s) : f (max a b) = min (f a) (f b) :=
  hf.dual_right.map_max ha hb

theorem AntitoneOn.map_min (hf : AntitoneOn f s) (ha : a ∈ s) (hb : b ∈ s) : f (min a b) = max (f a) (f b) :=
  hf.dual.map_max ha hb

theorem Monotone.map_max (hf : Monotone f) : f (max a b) = max (f a) (f b) := by
  cases le_totalₓ a b <;> simp [← h, ← hf h]

theorem Monotone.map_min (hf : Monotone f) : f (min a b) = min (f a) (f b) :=
  hf.dual.map_max

theorem Antitone.map_max (hf : Antitone f) : f (max a b) = min (f a) (f b) := by
  cases le_totalₓ a b <;> simp [← h, ← hf h]

theorem Antitone.map_min (hf : Antitone f) : f (min a b) = max (f a) (f b) :=
  hf.dual.map_max

theorem min_choice (a b : α) : min a b = a ∨ min a b = b := by
  cases le_totalₓ a b <;> simp [*]

theorem max_choice (a b : α) : max a b = a ∨ max a b = b :=
  @min_choice αᵒᵈ _ a b

theorem le_of_max_le_left {a b c : α} (h : max a b ≤ c) : a ≤ c :=
  le_transₓ (le_max_leftₓ _ _) h

theorem le_of_max_le_right {a b c : α} (h : max a b ≤ c) : b ≤ c :=
  le_transₓ (le_max_rightₓ _ _) h

theorem max_commutative : Commutative (max : α → α → α) :=
  max_commₓ

theorem max_associative : Associative (max : α → α → α) :=
  max_assocₓ

theorem max_left_commutative : LeftCommutative (max : α → α → α) :=
  max_left_commₓ

theorem min_commutative : Commutative (min : α → α → α) :=
  min_commₓ

theorem min_associative : Associative (min : α → α → α) :=
  min_assocₓ

theorem min_left_commutative : LeftCommutative (min : α → α → α) :=
  min_left_commₓ

end

