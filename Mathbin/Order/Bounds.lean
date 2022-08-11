/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov
-/
import Mathbin.Data.Set.Intervals.Basic

/-!

# Upper / lower bounds

In this file we define:

* `upper_bounds`, `lower_bounds` : the set of upper bounds (resp., lower bounds) of a set;
* `bdd_above s`, `bdd_below s` : the set `s` is bounded above (resp., below), i.e., the set of upper
  (resp., lower) bounds of `s` is nonempty;
* `is_least s a`, `is_greatest s a` : `a` is a least (resp., greatest) element of `s`;
  for a partial order, it is unique if exists;
* `is_lub s a`, `is_glb s a` : `a` is a least upper bound (resp., a greatest lower bound)
  of `s`; for a partial order, it is unique if exists.

We also prove various lemmas about monotonicity, behaviour under `∪`, `∩`, `insert`, and provide
formulas for `∅`, `univ`, and intervals.
-/


open Function Set

open OrderDual (toDual ofDual)

universe u v w x

variable {α : Type u} {β : Type v} {γ : Type w} {ι : Sort x}

section

variable [Preorderₓ α] [Preorderₓ β] {s t : Set α} {a b : α}

/-!
### Definitions
-/


/-- The set of upper bounds of a set. -/
def UpperBounds (s : Set α) : Set α :=
  { x | ∀ ⦃a⦄, a ∈ s → a ≤ x }

/-- The set of lower bounds of a set. -/
def LowerBounds (s : Set α) : Set α :=
  { x | ∀ ⦃a⦄, a ∈ s → x ≤ a }

/-- A set is bounded above if there exists an upper bound. -/
def BddAbove (s : Set α) :=
  (UpperBounds s).Nonempty

/-- A set is bounded below if there exists a lower bound. -/
def BddBelow (s : Set α) :=
  (LowerBounds s).Nonempty

/-- `a` is a least element of a set `s`; for a partial order, it is unique if exists. -/
def IsLeast (s : Set α) (a : α) : Prop :=
  a ∈ s ∧ a ∈ LowerBounds s

/-- `a` is a greatest element of a set `s`; for a partial order, it is unique if exists -/
def IsGreatest (s : Set α) (a : α) : Prop :=
  a ∈ s ∧ a ∈ UpperBounds s

/-- `a` is a least upper bound of a set `s`; for a partial order, it is unique if exists. -/
def IsLub (s : Set α) : α → Prop :=
  IsLeast (UpperBounds s)

/-- `a` is a greatest lower bound of a set `s`; for a partial order, it is unique if exists. -/
def IsGlb (s : Set α) : α → Prop :=
  IsGreatest (LowerBounds s)

theorem mem_upper_bounds : a ∈ UpperBounds s ↔ ∀, ∀ x ∈ s, ∀, x ≤ a :=
  Iff.rfl

theorem mem_lower_bounds : a ∈ LowerBounds s ↔ ∀, ∀ x ∈ s, ∀, a ≤ x :=
  Iff.rfl

theorem bdd_above_def : BddAbove s ↔ ∃ x, ∀, ∀ y ∈ s, ∀, y ≤ x :=
  Iff.rfl

theorem bdd_below_def : BddBelow s ↔ ∃ x, ∀, ∀ y ∈ s, ∀, x ≤ y :=
  Iff.rfl

theorem bot_mem_lower_bounds [OrderBot α] (s : Set α) : ⊥ ∈ LowerBounds s := fun _ _ => bot_le

theorem top_mem_upper_bounds [OrderTop α] (s : Set α) : ⊤ ∈ UpperBounds s := fun _ _ => le_top

@[simp]
theorem is_least_bot_iff [OrderBot α] : IsLeast s ⊥ ↔ ⊥ ∈ s :=
  and_iff_left <| bot_mem_lower_bounds _

@[simp]
theorem is_greatest_top_iff [OrderTop α] : IsGreatest s ⊤ ↔ ⊤ ∈ s :=
  and_iff_left <| top_mem_upper_bounds _

/-- A set `s` is not bounded above if and only if for each `x` there exists `y ∈ s` such that `x`
is not greater than or equal to `y`. This version only assumes `preorder` structure and uses
`¬(y ≤ x)`. A version for linear orders is called `not_bdd_above_iff`. -/
theorem not_bdd_above_iff' : ¬BddAbove s ↔ ∀ x, ∃ y ∈ s, ¬y ≤ x := by
  simp [← BddAbove, ← UpperBounds, ← Set.Nonempty]

/-- A set `s` is not bounded below if and only if for each `x` there exists `y ∈ s` such that `x`
is not less than or equal to `y`. This version only assumes `preorder` structure and uses
`¬(x ≤ y)`. A version for linear orders is called `not_bdd_below_iff`. -/
theorem not_bdd_below_iff' : ¬BddBelow s ↔ ∀ x, ∃ y ∈ s, ¬x ≤ y :=
  @not_bdd_above_iff' αᵒᵈ _ _

/-- A set `s` is not bounded above if and only if for each `x` there exists `y ∈ s` that is greater
than `x`. A version for preorders is called `not_bdd_above_iff'`. -/
theorem not_bdd_above_iff {α : Type _} [LinearOrderₓ α] {s : Set α} : ¬BddAbove s ↔ ∀ x, ∃ y ∈ s, x < y := by
  simp only [← not_bdd_above_iff', ← not_leₓ]

/-- A set `s` is not bounded below if and only if for each `x` there exists `y ∈ s` that is less
than `x`. A version for preorders is called `not_bdd_below_iff'`. -/
theorem not_bdd_below_iff {α : Type _} [LinearOrderₓ α] {s : Set α} : ¬BddBelow s ↔ ∀ x, ∃ y ∈ s, y < x :=
  @not_bdd_above_iff αᵒᵈ _ _

theorem BddAbove.dual (h : BddAbove s) : BddBelow (of_dual ⁻¹' s) :=
  h

theorem BddBelow.dual (h : BddBelow s) : BddAbove (of_dual ⁻¹' s) :=
  h

theorem IsLeast.dual (h : IsLeast s a) : IsGreatest (of_dual ⁻¹' s) (toDual a) :=
  h

theorem IsGreatest.dual (h : IsGreatest s a) : IsLeast (of_dual ⁻¹' s) (toDual a) :=
  h

theorem IsLub.dual (h : IsLub s a) : IsGlb (of_dual ⁻¹' s) (toDual a) :=
  h

theorem IsGlb.dual (h : IsGlb s a) : IsLub (of_dual ⁻¹' s) (toDual a) :=
  h

/-- If `a` is the least element of a set `s`, then subtype `s` is an order with bottom element. -/
@[reducible]
def IsLeast.orderBot (h : IsLeast s a) : OrderBot s where
  bot := ⟨a, h.1⟩
  bot_le := Subtype.forall.2 h.2

/-- If `a` is the greatest element of a set `s`, then subtype `s` is an order with top element. -/
@[reducible]
def IsGreatest.orderTop (h : IsGreatest s a) : OrderTop s where
  top := ⟨a, h.1⟩
  le_top := Subtype.forall.2 h.2

/-!
### Monotonicity
-/


theorem upper_bounds_mono_set ⦃s t : Set α⦄ (hst : s ⊆ t) : UpperBounds t ⊆ UpperBounds s := fun b hb x h => hb <| hst h

theorem lower_bounds_mono_set ⦃s t : Set α⦄ (hst : s ⊆ t) : LowerBounds t ⊆ LowerBounds s := fun b hb x h => hb <| hst h

theorem upper_bounds_mono_mem ⦃a b⦄ (hab : a ≤ b) : a ∈ UpperBounds s → b ∈ UpperBounds s := fun ha x h =>
  le_transₓ (ha h) hab

theorem lower_bounds_mono_mem ⦃a b⦄ (hab : a ≤ b) : b ∈ LowerBounds s → a ∈ LowerBounds s := fun hb x h =>
  le_transₓ hab (hb h)

theorem upper_bounds_mono ⦃s t : Set α⦄ (hst : s ⊆ t) ⦃a b⦄ (hab : a ≤ b) : a ∈ UpperBounds t → b ∈ UpperBounds s :=
  fun ha => upper_bounds_mono_set hst <| upper_bounds_mono_mem hab ha

theorem lower_bounds_mono ⦃s t : Set α⦄ (hst : s ⊆ t) ⦃a b⦄ (hab : a ≤ b) : b ∈ LowerBounds t → a ∈ LowerBounds s :=
  fun hb => lower_bounds_mono_set hst <| lower_bounds_mono_mem hab hb

/-- If `s ⊆ t` and `t` is bounded above, then so is `s`. -/
theorem BddAbove.mono ⦃s t : Set α⦄ (h : s ⊆ t) : BddAbove t → BddAbove s :=
  nonempty.mono <| upper_bounds_mono_set h

/-- If `s ⊆ t` and `t` is bounded below, then so is `s`. -/
theorem BddBelow.mono ⦃s t : Set α⦄ (h : s ⊆ t) : BddBelow t → BddBelow s :=
  nonempty.mono <| lower_bounds_mono_set h

/-- If `a` is a least upper bound for sets `s` and `p`, then it is a least upper bound for any
set `t`, `s ⊆ t ⊆ p`. -/
theorem IsLub.of_subset_of_superset {s t p : Set α} (hs : IsLub s a) (hp : IsLub p a) (hst : s ⊆ t) (htp : t ⊆ p) :
    IsLub t a :=
  ⟨upper_bounds_mono_set htp hp.1, lower_bounds_mono_set (upper_bounds_mono_set hst) hs.2⟩

/-- If `a` is a greatest lower bound for sets `s` and `p`, then it is a greater lower bound for any
set `t`, `s ⊆ t ⊆ p`. -/
theorem IsGlb.of_subset_of_superset {s t p : Set α} (hs : IsGlb s a) (hp : IsGlb p a) (hst : s ⊆ t) (htp : t ⊆ p) :
    IsGlb t a :=
  hs.dual.of_subset_of_superset hp hst htp

theorem IsLeast.mono (ha : IsLeast s a) (hb : IsLeast t b) (hst : s ⊆ t) : b ≤ a :=
  hb.2 (hst ha.1)

theorem IsGreatest.mono (ha : IsGreatest s a) (hb : IsGreatest t b) (hst : s ⊆ t) : a ≤ b :=
  hb.2 (hst ha.1)

theorem IsLub.mono (ha : IsLub s a) (hb : IsLub t b) (hst : s ⊆ t) : a ≤ b :=
  hb.mono ha <| upper_bounds_mono_set hst

theorem IsGlb.mono (ha : IsGlb s a) (hb : IsGlb t b) (hst : s ⊆ t) : b ≤ a :=
  hb.mono ha <| lower_bounds_mono_set hst

theorem subset_lower_bounds_upper_bounds (s : Set α) : s ⊆ LowerBounds (UpperBounds s) := fun x hx y hy => hy hx

theorem subset_upper_bounds_lower_bounds (s : Set α) : s ⊆ UpperBounds (LowerBounds s) := fun x hx y hy => hy hx

theorem Set.Nonempty.bdd_above_lower_bounds (hs : s.Nonempty) : BddAbove (LowerBounds s) :=
  hs.mono (subset_upper_bounds_lower_bounds s)

theorem Set.Nonempty.bdd_below_upper_bounds (hs : s.Nonempty) : BddBelow (UpperBounds s) :=
  hs.mono (subset_lower_bounds_upper_bounds s)

/-!
### Conversions
-/


theorem IsLeast.is_glb (h : IsLeast s a) : IsGlb s a :=
  ⟨h.2, fun b hb => hb h.1⟩

theorem IsGreatest.is_lub (h : IsGreatest s a) : IsLub s a :=
  ⟨h.2, fun b hb => hb h.1⟩

theorem IsLub.upper_bounds_eq (h : IsLub s a) : UpperBounds s = Ici a :=
  Set.ext fun b => ⟨fun hb => h.2 hb, fun hb => upper_bounds_mono_mem hb h.1⟩

theorem IsGlb.lower_bounds_eq (h : IsGlb s a) : LowerBounds s = Iic a :=
  h.dual.upper_bounds_eq

theorem IsLeast.lower_bounds_eq (h : IsLeast s a) : LowerBounds s = Iic a :=
  h.IsGlb.lower_bounds_eq

theorem IsGreatest.upper_bounds_eq (h : IsGreatest s a) : UpperBounds s = Ici a :=
  h.IsLub.upper_bounds_eq

theorem is_lub_le_iff (h : IsLub s a) : a ≤ b ↔ b ∈ UpperBounds s := by
  rw [h.upper_bounds_eq]
  rfl

theorem le_is_glb_iff (h : IsGlb s a) : b ≤ a ↔ b ∈ LowerBounds s := by
  rw [h.lower_bounds_eq]
  rfl

theorem is_lub_iff_le_iff : IsLub s a ↔ ∀ b, a ≤ b ↔ b ∈ UpperBounds s :=
  ⟨fun h b => is_lub_le_iff h, fun H => ⟨(H _).1 le_rfl, fun b hb => (H b).2 hb⟩⟩

theorem is_glb_iff_le_iff : IsGlb s a ↔ ∀ b, b ≤ a ↔ b ∈ LowerBounds s :=
  @is_lub_iff_le_iff αᵒᵈ _ _ _

/-- If `s` has a least upper bound, then it is bounded above. -/
theorem IsLub.bdd_above (h : IsLub s a) : BddAbove s :=
  ⟨a, h.1⟩

/-- If `s` has a greatest lower bound, then it is bounded below. -/
theorem IsGlb.bdd_below (h : IsGlb s a) : BddBelow s :=
  ⟨a, h.1⟩

/-- If `s` has a greatest element, then it is bounded above. -/
theorem IsGreatest.bdd_above (h : IsGreatest s a) : BddAbove s :=
  ⟨a, h.2⟩

/-- If `s` has a least element, then it is bounded below. -/
theorem IsLeast.bdd_below (h : IsLeast s a) : BddBelow s :=
  ⟨a, h.2⟩

theorem IsLeast.nonempty (h : IsLeast s a) : s.Nonempty :=
  ⟨a, h.1⟩

theorem IsGreatest.nonempty (h : IsGreatest s a) : s.Nonempty :=
  ⟨a, h.1⟩

/-!
### Union and intersection
-/


@[simp]
theorem upper_bounds_union : UpperBounds (s ∪ t) = UpperBounds s ∩ UpperBounds t :=
  Subset.antisymm (fun b hb => ⟨fun x hx => hb (Or.inl hx), fun x hx => hb (Or.inr hx)⟩) fun b hb x hx =>
    hx.elim (fun hs => hb.1 hs) fun ht => hb.2 ht

@[simp]
theorem lower_bounds_union : LowerBounds (s ∪ t) = LowerBounds s ∩ LowerBounds t :=
  @upper_bounds_union αᵒᵈ _ s t

theorem union_upper_bounds_subset_upper_bounds_inter : UpperBounds s ∪ UpperBounds t ⊆ UpperBounds (s ∩ t) :=
  union_subset (upper_bounds_mono_set <| inter_subset_left _ _) (upper_bounds_mono_set <| inter_subset_right _ _)

theorem union_lower_bounds_subset_lower_bounds_inter : LowerBounds s ∪ LowerBounds t ⊆ LowerBounds (s ∩ t) :=
  @union_upper_bounds_subset_upper_bounds_inter αᵒᵈ _ s t

theorem is_least_union_iff {a : α} {s t : Set α} :
    IsLeast (s ∪ t) a ↔ IsLeast s a ∧ a ∈ LowerBounds t ∨ a ∈ LowerBounds s ∧ IsLeast t a := by
  simp [← IsLeast, ← lower_bounds_union, ← or_and_distrib_right, ← and_comm (a ∈ t), ← and_assoc]

theorem is_greatest_union_iff :
    IsGreatest (s ∪ t) a ↔ IsGreatest s a ∧ a ∈ UpperBounds t ∨ a ∈ UpperBounds s ∧ IsGreatest t a :=
  @is_least_union_iff αᵒᵈ _ a s t

/-- If `s` is bounded, then so is `s ∩ t` -/
theorem BddAbove.inter_of_left (h : BddAbove s) : BddAbove (s ∩ t) :=
  h.mono <| inter_subset_left s t

/-- If `t` is bounded, then so is `s ∩ t` -/
theorem BddAbove.inter_of_right (h : BddAbove t) : BddAbove (s ∩ t) :=
  h.mono <| inter_subset_right s t

/-- If `s` is bounded, then so is `s ∩ t` -/
theorem BddBelow.inter_of_left (h : BddBelow s) : BddBelow (s ∩ t) :=
  h.mono <| inter_subset_left s t

/-- If `t` is bounded, then so is `s ∩ t` -/
theorem BddBelow.inter_of_right (h : BddBelow t) : BddBelow (s ∩ t) :=
  h.mono <| inter_subset_right s t

/-- If `s` and `t` are bounded above sets in a `semilattice_sup`, then so is `s ∪ t`. -/
theorem BddAbove.union [SemilatticeSup γ] {s t : Set γ} : BddAbove s → BddAbove t → BddAbove (s ∪ t) := by
  rintro ⟨bs, hs⟩ ⟨bt, ht⟩
  use bs⊔bt
  rw [upper_bounds_union]
  exact ⟨upper_bounds_mono_mem le_sup_left hs, upper_bounds_mono_mem le_sup_right ht⟩

/-- The union of two sets is bounded above if and only if each of the sets is. -/
theorem bdd_above_union [SemilatticeSup γ] {s t : Set γ} : BddAbove (s ∪ t) ↔ BddAbove s ∧ BddAbove t :=
  ⟨fun h => ⟨h.mono <| subset_union_left s t, h.mono <| subset_union_right s t⟩, fun h => h.1.union h.2⟩

theorem BddBelow.union [SemilatticeInf γ] {s t : Set γ} : BddBelow s → BddBelow t → BddBelow (s ∪ t) :=
  @BddAbove.union γᵒᵈ _ s t

/-- The union of two sets is bounded above if and only if each of the sets is.-/
theorem bdd_below_union [SemilatticeInf γ] {s t : Set γ} : BddBelow (s ∪ t) ↔ BddBelow s ∧ BddBelow t :=
  @bdd_above_union γᵒᵈ _ s t

/-- If `a` is the least upper bound of `s` and `b` is the least upper bound of `t`,
then `a ⊔ b` is the least upper bound of `s ∪ t`. -/
theorem IsLub.union [SemilatticeSup γ] {a b : γ} {s t : Set γ} (hs : IsLub s a) (ht : IsLub t b) :
    IsLub (s ∪ t) (a⊔b) :=
  ⟨fun c h => h.casesOn (fun h => le_sup_of_le_left <| hs.left h) fun h => le_sup_of_le_right <| ht.left h, fun c hc =>
    sup_le (hs.right fun d hd => hc <| Or.inl hd) (ht.right fun d hd => hc <| Or.inr hd)⟩

/-- If `a` is the greatest lower bound of `s` and `b` is the greatest lower bound of `t`,
then `a ⊓ b` is the greatest lower bound of `s ∪ t`. -/
theorem IsGlb.union [SemilatticeInf γ] {a₁ a₂ : γ} {s t : Set γ} (hs : IsGlb s a₁) (ht : IsGlb t a₂) :
    IsGlb (s ∪ t) (a₁⊓a₂) :=
  hs.dual.union ht

/-- If `a` is the least element of `s` and `b` is the least element of `t`,
then `min a b` is the least element of `s ∪ t`. -/
theorem IsLeast.union [LinearOrderₓ γ] {a b : γ} {s t : Set γ} (ha : IsLeast s a) (hb : IsLeast t b) :
    IsLeast (s ∪ t) (min a b) :=
  ⟨by
    cases' le_totalₓ a b with h h <;> simp [← h, ← ha.1, ← hb.1], (ha.IsGlb.union hb.IsGlb).1⟩

/-- If `a` is the greatest element of `s` and `b` is the greatest element of `t`,
then `max a b` is the greatest element of `s ∪ t`. -/
theorem IsGreatest.union [LinearOrderₓ γ] {a b : γ} {s t : Set γ} (ha : IsGreatest s a) (hb : IsGreatest t b) :
    IsGreatest (s ∪ t) (max a b) :=
  ⟨by
    cases' le_totalₓ a b with h h <;> simp [← h, ← ha.1, ← hb.1], (ha.IsLub.union hb.IsLub).1⟩

theorem IsLub.inter_Ici_of_mem [LinearOrderₓ γ] {s : Set γ} {a b : γ} (ha : IsLub s a) (hb : b ∈ s) :
    IsLub (s ∩ Ici b) a :=
  ⟨fun x hx => ha.1 hx.1, fun c hc =>
    have hbc : b ≤ c := hc ⟨hb, le_rfl⟩
    ha.2 fun x hx => ((le_totalₓ x b).elim fun hxb => hxb.trans hbc) fun hbx => hc ⟨hx, hbx⟩⟩

theorem IsGlb.inter_Iic_of_mem [LinearOrderₓ γ] {s : Set γ} {a b : γ} (ha : IsGlb s a) (hb : b ∈ s) :
    IsGlb (s ∩ Iic b) a :=
  ha.dual.inter_Ici_of_mem hb

theorem bdd_above_iff_exists_ge [SemilatticeSup γ] {s : Set γ} (x₀ : γ) :
    BddAbove s ↔ ∃ x, x₀ ≤ x ∧ ∀, ∀ y ∈ s, ∀, y ≤ x := by
  rw [bdd_above_def, exists_ge_and_iff_exists]
  exact Monotone.ball fun x hx => monotone_le

theorem bdd_below_iff_exists_le [SemilatticeInf γ] {s : Set γ} (x₀ : γ) :
    BddBelow s ↔ ∃ x, x ≤ x₀ ∧ ∀, ∀ y ∈ s, ∀, x ≤ y :=
  bdd_above_iff_exists_ge (toDual x₀)

theorem BddAbove.exists_ge [SemilatticeSup γ] {s : Set γ} (hs : BddAbove s) (x₀ : γ) :
    ∃ x, x₀ ≤ x ∧ ∀, ∀ y ∈ s, ∀, y ≤ x :=
  (bdd_above_iff_exists_ge x₀).mp hs

theorem BddBelow.exists_le [SemilatticeInf γ] {s : Set γ} (hs : BddBelow s) (x₀ : γ) :
    ∃ x, x ≤ x₀ ∧ ∀, ∀ y ∈ s, ∀, x ≤ y :=
  (bdd_below_iff_exists_le x₀).mp hs

/-!
### Specific sets

#### Unbounded intervals
-/


theorem is_least_Ici : IsLeast (Ici a) a :=
  ⟨left_mem_Ici, fun x => id⟩

theorem is_greatest_Iic : IsGreatest (Iic a) a :=
  ⟨right_mem_Iic, fun x => id⟩

theorem is_lub_Iic : IsLub (Iic a) a :=
  is_greatest_Iic.IsLub

theorem is_glb_Ici : IsGlb (Ici a) a :=
  is_least_Ici.IsGlb

theorem upper_bounds_Iic : UpperBounds (Iic a) = Ici a :=
  is_lub_Iic.upper_bounds_eq

theorem lower_bounds_Ici : LowerBounds (Ici a) = Iic a :=
  is_glb_Ici.lower_bounds_eq

theorem bdd_above_Iic : BddAbove (Iic a) :=
  is_lub_Iic.BddAbove

theorem bdd_below_Ici : BddBelow (Ici a) :=
  is_glb_Ici.BddBelow

theorem bdd_above_Iio : BddAbove (Iio a) :=
  ⟨a, fun x hx => le_of_ltₓ hx⟩

theorem bdd_below_Ioi : BddBelow (Ioi a) :=
  ⟨a, fun x hx => le_of_ltₓ hx⟩

theorem lub_Iio_le (a : α) (hb : IsLub (Set.Iio a) b) : b ≤ a :=
  (is_lub_le_iff hb).mpr fun k hk => le_of_ltₓ hk

theorem le_glb_Ioi (a : α) (hb : IsGlb (Set.Ioi a) b) : a ≤ b :=
  @lub_Iio_le αᵒᵈ _ _ a hb

theorem lub_Iio_eq_self_or_Iio_eq_Iic [PartialOrderₓ γ] {j : γ} (i : γ) (hj : IsLub (Set.Iio i) j) :
    j = i ∨ Set.Iio i = Set.Iic j := by
  cases' eq_or_lt_of_le (lub_Iio_le i hj) with hj_eq_i hj_lt_i
  · exact Or.inl hj_eq_i
    
  · right
    exact Set.ext fun k => ⟨fun hk_lt => hj.1 hk_lt, fun hk_le_j => lt_of_le_of_ltₓ hk_le_j hj_lt_i⟩
    

theorem glb_Ioi_eq_self_or_Ioi_eq_Ici [PartialOrderₓ γ] {j : γ} (i : γ) (hj : IsGlb (Set.Ioi i) j) :
    j = i ∨ Set.Ioi i = Set.Ici j :=
  @lub_Iio_eq_self_or_Iio_eq_Iic γᵒᵈ _ j i hj

section

variable [LinearOrderₓ γ]

theorem exists_lub_Iio (i : γ) : ∃ j, IsLub (Set.Iio i) j := by
  by_cases' h_exists_lt : ∃ j, j ∈ UpperBounds (Set.Iio i) ∧ j < i
  · obtain ⟨j, hj_ub, hj_lt_i⟩ := h_exists_lt
    exact ⟨j, hj_ub, fun k hk_ub => hk_ub hj_lt_i⟩
    
  · refine' ⟨i, fun j hj => le_of_ltₓ hj, _⟩
    rw [mem_lower_bounds]
    by_contra
    refine' h_exists_lt _
    push_neg  at h
    exact h
    

theorem exists_glb_Ioi (i : γ) : ∃ j, IsGlb (Set.Ioi i) j :=
  @exists_lub_Iio γᵒᵈ _ i

variable [DenselyOrdered γ]

theorem is_lub_Iio {a : γ} : IsLub (Iio a) a :=
  ⟨fun x hx => le_of_ltₓ hx, fun y hy => le_of_forall_ge_of_dense hy⟩

theorem is_glb_Ioi {a : γ} : IsGlb (Ioi a) a :=
  @is_lub_Iio γᵒᵈ _ _ a

theorem upper_bounds_Iio {a : γ} : UpperBounds (Iio a) = Ici a :=
  is_lub_Iio.upper_bounds_eq

theorem lower_bounds_Ioi {a : γ} : LowerBounds (Ioi a) = Iic a :=
  is_glb_Ioi.lower_bounds_eq

end

/-!
#### Singleton
-/


theorem is_greatest_singleton : IsGreatest {a} a :=
  ⟨mem_singleton a, fun x hx => le_of_eqₓ <| eq_of_mem_singleton hx⟩

theorem is_least_singleton : IsLeast {a} a :=
  @is_greatest_singleton αᵒᵈ _ a

theorem is_lub_singleton : IsLub {a} a :=
  is_greatest_singleton.IsLub

theorem is_glb_singleton : IsGlb {a} a :=
  is_least_singleton.IsGlb

theorem bdd_above_singleton : BddAbove ({a} : Set α) :=
  is_lub_singleton.BddAbove

theorem bdd_below_singleton : BddBelow ({a} : Set α) :=
  is_glb_singleton.BddBelow

@[simp]
theorem upper_bounds_singleton : UpperBounds {a} = Ici a :=
  is_lub_singleton.upper_bounds_eq

@[simp]
theorem lower_bounds_singleton : LowerBounds {a} = Iic a :=
  is_glb_singleton.lower_bounds_eq

/-!
#### Bounded intervals
-/


theorem bdd_above_Icc : BddAbove (Icc a b) :=
  ⟨b, fun _ => And.right⟩

theorem bdd_below_Icc : BddBelow (Icc a b) :=
  ⟨a, fun _ => And.left⟩

theorem bdd_above_Ico : BddAbove (Ico a b) :=
  bdd_above_Icc.mono Ico_subset_Icc_self

theorem bdd_below_Ico : BddBelow (Ico a b) :=
  bdd_below_Icc.mono Ico_subset_Icc_self

theorem bdd_above_Ioc : BddAbove (Ioc a b) :=
  bdd_above_Icc.mono Ioc_subset_Icc_self

theorem bdd_below_Ioc : BddBelow (Ioc a b) :=
  bdd_below_Icc.mono Ioc_subset_Icc_self

theorem bdd_above_Ioo : BddAbove (Ioo a b) :=
  bdd_above_Icc.mono Ioo_subset_Icc_self

theorem bdd_below_Ioo : BddBelow (Ioo a b) :=
  bdd_below_Icc.mono Ioo_subset_Icc_self

theorem is_greatest_Icc (h : a ≤ b) : IsGreatest (Icc a b) b :=
  ⟨right_mem_Icc.2 h, fun x => And.right⟩

theorem is_lub_Icc (h : a ≤ b) : IsLub (Icc a b) b :=
  (is_greatest_Icc h).IsLub

theorem upper_bounds_Icc (h : a ≤ b) : UpperBounds (Icc a b) = Ici b :=
  (is_lub_Icc h).upper_bounds_eq

theorem is_least_Icc (h : a ≤ b) : IsLeast (Icc a b) a :=
  ⟨left_mem_Icc.2 h, fun x => And.left⟩

theorem is_glb_Icc (h : a ≤ b) : IsGlb (Icc a b) a :=
  (is_least_Icc h).IsGlb

theorem lower_bounds_Icc (h : a ≤ b) : LowerBounds (Icc a b) = Iic a :=
  (is_glb_Icc h).lower_bounds_eq

theorem is_greatest_Ioc (h : a < b) : IsGreatest (Ioc a b) b :=
  ⟨right_mem_Ioc.2 h, fun x => And.right⟩

theorem is_lub_Ioc (h : a < b) : IsLub (Ioc a b) b :=
  (is_greatest_Ioc h).IsLub

theorem upper_bounds_Ioc (h : a < b) : UpperBounds (Ioc a b) = Ici b :=
  (is_lub_Ioc h).upper_bounds_eq

theorem is_least_Ico (h : a < b) : IsLeast (Ico a b) a :=
  ⟨left_mem_Ico.2 h, fun x => And.left⟩

theorem is_glb_Ico (h : a < b) : IsGlb (Ico a b) a :=
  (is_least_Ico h).IsGlb

theorem lower_bounds_Ico (h : a < b) : LowerBounds (Ico a b) = Iic a :=
  (is_glb_Ico h).lower_bounds_eq

section

variable [SemilatticeSup γ] [DenselyOrdered γ]

theorem is_glb_Ioo {a b : γ} (h : a < b) : IsGlb (Ioo a b) a :=
  ⟨fun x hx => hx.1.le, fun x hx => by
    cases' eq_or_lt_of_le (le_sup_right : a ≤ x⊔a) with h₁ h₂
    · exact h₁.symm ▸ le_sup_left
      
    obtain ⟨y, lty, ylt⟩ := exists_between h₂
    apply (not_lt_of_le (sup_le (hx ⟨lty, ylt.trans_le (sup_le _ h.le)⟩) lty.le) ylt).elim
    obtain ⟨u, au, ub⟩ := exists_between h
    apply (hx ⟨au, ub⟩).trans ub.le⟩

theorem lower_bounds_Ioo {a b : γ} (hab : a < b) : LowerBounds (Ioo a b) = Iic a :=
  (is_glb_Ioo hab).lower_bounds_eq

theorem is_glb_Ioc {a b : γ} (hab : a < b) : IsGlb (Ioc a b) a :=
  (is_glb_Ioo hab).of_subset_of_superset (is_glb_Icc hab.le) Ioo_subset_Ioc_self Ioc_subset_Icc_self

theorem lower_bound_Ioc {a b : γ} (hab : a < b) : LowerBounds (Ioc a b) = Iic a :=
  (is_glb_Ioc hab).lower_bounds_eq

end

section

variable [SemilatticeInf γ] [DenselyOrdered γ]

theorem is_lub_Ioo {a b : γ} (hab : a < b) : IsLub (Ioo a b) b := by
  simpa only [← dual_Ioo] using is_glb_Ioo hab.dual

theorem upper_bounds_Ioo {a b : γ} (hab : a < b) : UpperBounds (Ioo a b) = Ici b :=
  (is_lub_Ioo hab).upper_bounds_eq

theorem is_lub_Ico {a b : γ} (hab : a < b) : IsLub (Ico a b) b := by
  simpa only [← dual_Ioc] using is_glb_Ioc hab.dual

theorem upper_bounds_Ico {a b : γ} (hab : a < b) : UpperBounds (Ico a b) = Ici b :=
  (is_lub_Ico hab).upper_bounds_eq

end

theorem bdd_below_iff_subset_Ici : BddBelow s ↔ ∃ a, s ⊆ Ici a :=
  Iff.rfl

theorem bdd_above_iff_subset_Iic : BddAbove s ↔ ∃ a, s ⊆ Iic a :=
  Iff.rfl

theorem bdd_below_bdd_above_iff_subset_Icc : BddBelow s ∧ BddAbove s ↔ ∃ a b, s ⊆ Icc a b := by
  simp only [← Ici_inter_Iic.symm, ← subset_inter_iff, ← bdd_below_iff_subset_Ici, ← bdd_above_iff_subset_Iic, ←
    exists_and_distrib_left, ← exists_and_distrib_right]

/-!
#### Univ
-/


theorem is_greatest_univ [Preorderₓ γ] [OrderTop γ] : IsGreatest (Univ : Set γ) ⊤ :=
  ⟨mem_univ _, fun x hx => le_top⟩

@[simp]
theorem OrderTop.upper_bounds_univ [PartialOrderₓ γ] [OrderTop γ] : UpperBounds (Univ : Set γ) = {⊤} := by
  rw [is_greatest_univ.upper_bounds_eq, Ici_top]

theorem is_lub_univ [Preorderₓ γ] [OrderTop γ] : IsLub (Univ : Set γ) ⊤ :=
  is_greatest_univ.IsLub

@[simp]
theorem OrderBot.lower_bounds_univ [PartialOrderₓ γ] [OrderBot γ] : LowerBounds (Univ : Set γ) = {⊥} :=
  @OrderTop.upper_bounds_univ γᵒᵈ _ _

theorem is_least_univ [Preorderₓ γ] [OrderBot γ] : IsLeast (Univ : Set γ) ⊥ :=
  @is_greatest_univ γᵒᵈ _ _

theorem is_glb_univ [Preorderₓ γ] [OrderBot γ] : IsGlb (Univ : Set γ) ⊥ :=
  is_least_univ.IsGlb

@[simp]
theorem NoMaxOrder.upper_bounds_univ [NoMaxOrder α] : UpperBounds (Univ : Set α) = ∅ :=
  eq_empty_of_subset_empty fun b hb =>
    let ⟨x, hx⟩ := exists_gt b
    not_le_of_lt hx (hb trivialₓ)

@[simp]
theorem NoMinOrder.lower_bounds_univ [NoMinOrder α] : LowerBounds (Univ : Set α) = ∅ :=
  @NoMaxOrder.upper_bounds_univ αᵒᵈ _ _

@[simp]
theorem not_bdd_above_univ [NoMaxOrder α] : ¬BddAbove (Univ : Set α) := by
  simp [← BddAbove]

@[simp]
theorem not_bdd_below_univ [NoMinOrder α] : ¬BddBelow (Univ : Set α) :=
  @not_bdd_above_univ αᵒᵈ _ _

/-!
#### Empty set
-/


@[simp]
theorem upper_bounds_empty : UpperBounds (∅ : Set α) = univ := by
  simp only [← UpperBounds, ← eq_univ_iff_forall, ← mem_set_of_eq, ← ball_empty_iff, ← forall_true_iff]

@[simp]
theorem lower_bounds_empty : LowerBounds (∅ : Set α) = univ :=
  @upper_bounds_empty αᵒᵈ _

@[simp]
theorem bdd_above_empty [Nonempty α] : BddAbove (∅ : Set α) := by
  simp only [← BddAbove, ← upper_bounds_empty, ← univ_nonempty]

@[simp]
theorem bdd_below_empty [Nonempty α] : BddBelow (∅ : Set α) := by
  simp only [← BddBelow, ← lower_bounds_empty, ← univ_nonempty]

theorem is_glb_empty [Preorderₓ γ] [OrderTop γ] : IsGlb ∅ (⊤ : γ) := by
  simp only [← IsGlb, ← lower_bounds_empty, ← is_greatest_univ]

theorem is_lub_empty [Preorderₓ γ] [OrderBot γ] : IsLub ∅ (⊥ : γ) :=
  @is_glb_empty γᵒᵈ _ _

theorem IsLub.nonempty [NoMinOrder α] (hs : IsLub s a) : s.Nonempty :=
  let ⟨a', ha'⟩ := exists_lt a
  ne_empty_iff_nonempty.1 fun h =>
    not_le_of_lt ha' <|
      hs.right <| by
        simp only [← h, ← upper_bounds_empty]

theorem IsGlb.nonempty [NoMaxOrder α] (hs : IsGlb s a) : s.Nonempty :=
  hs.dual.Nonempty

theorem nonempty_of_not_bdd_above [ha : Nonempty α] (h : ¬BddAbove s) : s.Nonempty :=
  (Nonempty.elimₓ ha) fun x => (not_bdd_above_iff'.1 h x).imp fun a ha => ha.fst

theorem nonempty_of_not_bdd_below [ha : Nonempty α] (h : ¬BddBelow s) : s.Nonempty :=
  @nonempty_of_not_bdd_above αᵒᵈ _ _ _ h

/-!
#### insert
-/


/-- Adding a point to a set preserves its boundedness above. -/
@[simp]
theorem bdd_above_insert [SemilatticeSup γ] (a : γ) {s : Set γ} : BddAbove (insert a s) ↔ BddAbove s := by
  simp only [← insert_eq, ← bdd_above_union, ← bdd_above_singleton, ← true_andₓ]

theorem BddAbove.insert [SemilatticeSup γ] (a : γ) {s : Set γ} (hs : BddAbove s) : BddAbove (insert a s) :=
  (bdd_above_insert a).2 hs

/-- Adding a point to a set preserves its boundedness below.-/
@[simp]
theorem bdd_below_insert [SemilatticeInf γ] (a : γ) {s : Set γ} : BddBelow (insert a s) ↔ BddBelow s := by
  simp only [← insert_eq, ← bdd_below_union, ← bdd_below_singleton, ← true_andₓ]

theorem BddBelow.insert [SemilatticeInf γ] (a : γ) {s : Set γ} (hs : BddBelow s) : BddBelow (insert a s) :=
  (bdd_below_insert a).2 hs

theorem IsLub.insert [SemilatticeSup γ] (a) {b} {s : Set γ} (hs : IsLub s b) : IsLub (insert a s) (a⊔b) := by
  rw [insert_eq]
  exact is_lub_singleton.union hs

theorem IsGlb.insert [SemilatticeInf γ] (a) {b} {s : Set γ} (hs : IsGlb s b) : IsGlb (insert a s) (a⊓b) := by
  rw [insert_eq]
  exact is_glb_singleton.union hs

theorem IsGreatest.insert [LinearOrderₓ γ] (a) {b} {s : Set γ} (hs : IsGreatest s b) :
    IsGreatest (insert a s) (max a b) := by
  rw [insert_eq]
  exact is_greatest_singleton.union hs

theorem IsLeast.insert [LinearOrderₓ γ] (a) {b} {s : Set γ} (hs : IsLeast s b) : IsLeast (insert a s) (min a b) := by
  rw [insert_eq]
  exact is_least_singleton.union hs

@[simp]
theorem upper_bounds_insert (a : α) (s : Set α) : UpperBounds (insert a s) = Ici a ∩ UpperBounds s := by
  rw [insert_eq, upper_bounds_union, upper_bounds_singleton]

@[simp]
theorem lower_bounds_insert (a : α) (s : Set α) : LowerBounds (insert a s) = Iic a ∩ LowerBounds s := by
  rw [insert_eq, lower_bounds_union, lower_bounds_singleton]

/-- When there is a global maximum, every set is bounded above. -/
@[simp]
protected theorem OrderTop.bdd_above [Preorderₓ γ] [OrderTop γ] (s : Set γ) : BddAbove s :=
  ⟨⊤, fun a ha => OrderTop.le_top a⟩

/-- When there is a global minimum, every set is bounded below. -/
@[simp]
protected theorem OrderBot.bdd_below [Preorderₓ γ] [OrderBot γ] (s : Set γ) : BddBelow s :=
  ⟨⊥, fun a ha => OrderBot.bot_le a⟩

/-!
#### Pair
-/


theorem is_lub_pair [SemilatticeSup γ] {a b : γ} : IsLub {a, b} (a⊔b) :=
  is_lub_singleton.insert _

theorem is_glb_pair [SemilatticeInf γ] {a b : γ} : IsGlb {a, b} (a⊓b) :=
  is_glb_singleton.insert _

theorem is_least_pair [LinearOrderₓ γ] {a b : γ} : IsLeast {a, b} (min a b) :=
  is_least_singleton.insert _

theorem is_greatest_pair [LinearOrderₓ γ] {a b : γ} : IsGreatest {a, b} (max a b) :=
  is_greatest_singleton.insert _

/-!
#### Lower/upper bounds
-/


@[simp]
theorem is_lub_lower_bounds : IsLub (LowerBounds s) a ↔ IsGlb s a :=
  ⟨fun H => ⟨fun x hx => H.2 <| subset_upper_bounds_lower_bounds s hx, H.1⟩, IsGreatest.is_lub⟩

@[simp]
theorem is_glb_upper_bounds : IsGlb (UpperBounds s) a ↔ IsLub s a :=
  @is_lub_lower_bounds αᵒᵈ _ _ _

end

/-!
### (In)equalities with the least upper bound and the greatest lower bound
-/


section Preorderₓ

variable [Preorderₓ α] {s : Set α} {a b : α}

theorem lower_bounds_le_upper_bounds (ha : a ∈ LowerBounds s) (hb : b ∈ UpperBounds s) : s.Nonempty → a ≤ b
  | ⟨c, hc⟩ => le_transₓ (ha hc) (hb hc)

theorem is_glb_le_is_lub (ha : IsGlb s a) (hb : IsLub s b) (hs : s.Nonempty) : a ≤ b :=
  lower_bounds_le_upper_bounds ha.1 hb.1 hs

theorem is_lub_lt_iff (ha : IsLub s a) : a < b ↔ ∃ c ∈ UpperBounds s, c < b :=
  ⟨fun hb => ⟨a, ha.1, hb⟩, fun ⟨c, hcs, hcb⟩ => lt_of_le_of_ltₓ (ha.2 hcs) hcb⟩

theorem lt_is_glb_iff (ha : IsGlb s a) : b < a ↔ ∃ c ∈ LowerBounds s, b < c :=
  is_lub_lt_iff ha.dual

theorem le_of_is_lub_le_is_glb {x y} (ha : IsGlb s a) (hb : IsLub s b) (hab : b ≤ a) (hx : x ∈ s) (hy : y ∈ s) :
    x ≤ y :=
  calc
    x ≤ b := hb.1 hx
    _ ≤ a := hab
    _ ≤ y := ha.1 hy
    

end Preorderₓ

section PartialOrderₓ

variable [PartialOrderₓ α] {s : Set α} {a b : α}

theorem IsLeast.unique (Ha : IsLeast s a) (Hb : IsLeast s b) : a = b :=
  le_antisymmₓ (Ha.right Hb.left) (Hb.right Ha.left)

theorem IsLeast.is_least_iff_eq (Ha : IsLeast s a) : IsLeast s b ↔ a = b :=
  Iff.intro Ha.unique fun h => h ▸ Ha

theorem IsGreatest.unique (Ha : IsGreatest s a) (Hb : IsGreatest s b) : a = b :=
  le_antisymmₓ (Hb.right Ha.left) (Ha.right Hb.left)

theorem IsGreatest.is_greatest_iff_eq (Ha : IsGreatest s a) : IsGreatest s b ↔ a = b :=
  Iff.intro Ha.unique fun h => h ▸ Ha

theorem IsLub.unique (Ha : IsLub s a) (Hb : IsLub s b) : a = b :=
  Ha.unique Hb

theorem IsGlb.unique (Ha : IsGlb s a) (Hb : IsGlb s b) : a = b :=
  Ha.unique Hb

theorem Set.subsingleton_of_is_lub_le_is_glb (Ha : IsGlb s a) (Hb : IsLub s b) (hab : b ≤ a) : s.Subsingleton :=
  fun x hx y hy => le_antisymmₓ (le_of_is_lub_le_is_glb Ha Hb hab hx hy) (le_of_is_lub_le_is_glb Ha Hb hab hy hx)

theorem is_glb_lt_is_lub_of_ne (Ha : IsGlb s a) (Hb : IsLub s b) {x y} (Hx : x ∈ s) (Hy : y ∈ s) (Hxy : x ≠ y) :
    a < b :=
  lt_iff_le_not_leₓ.2
    ⟨lower_bounds_le_upper_bounds Ha.1 Hb.1 ⟨x, Hx⟩, fun hab =>
      Hxy <| Set.subsingleton_of_is_lub_le_is_glb Ha Hb hab Hx Hy⟩

end PartialOrderₓ

section LinearOrderₓ

variable [LinearOrderₓ α] {s : Set α} {a b : α}

theorem lt_is_lub_iff (h : IsLub s a) : b < a ↔ ∃ c ∈ s, b < c := by
  simp only [not_leₓ, ← is_lub_le_iff h, ← mem_upper_bounds, ← not_forall]

theorem is_glb_lt_iff (h : IsGlb s a) : a < b ↔ ∃ c ∈ s, c < b :=
  lt_is_lub_iff h.dual

theorem IsLub.exists_between (h : IsLub s a) (hb : b < a) : ∃ c ∈ s, b < c ∧ c ≤ a :=
  let ⟨c, hcs, hbc⟩ := (lt_is_lub_iff h).1 hb
  ⟨c, hcs, hbc, h.1 hcs⟩

theorem IsLub.exists_between' (h : IsLub s a) (h' : a ∉ s) (hb : b < a) : ∃ c ∈ s, b < c ∧ c < a :=
  let ⟨c, hcs, hbc, hca⟩ := h.exists_between hb
  ⟨c, hcs, hbc, hca.lt_of_ne fun hac => h' <| hac ▸ hcs⟩

theorem IsGlb.exists_between (h : IsGlb s a) (hb : a < b) : ∃ c ∈ s, a ≤ c ∧ c < b :=
  let ⟨c, hcs, hbc⟩ := (is_glb_lt_iff h).1 hb
  ⟨c, hcs, h.1 hcs, hbc⟩

theorem IsGlb.exists_between' (h : IsGlb s a) (h' : a ∉ s) (hb : a < b) : ∃ c ∈ s, a < c ∧ c < b :=
  let ⟨c, hcs, hac, hcb⟩ := h.exists_between hb
  ⟨c, hcs, hac.lt_of_ne fun hac => h' <| hac.symm ▸ hcs, hcb⟩

end LinearOrderₓ

/-!
### Least upper bound and the greatest lower bound in linear ordered additive commutative groups
-/


section LinearOrderedAddCommGroup

variable [LinearOrderedAddCommGroup α] {s : Set α} {a ε : α}

theorem IsGlb.exists_between_self_add (h : IsGlb s a) (hε : 0 < ε) : ∃ b ∈ s, a ≤ b ∧ b < a + ε :=
  h.exists_between <| lt_add_of_pos_right _ hε

theorem IsGlb.exists_between_self_add' (h : IsGlb s a) (h₂ : a ∉ s) (hε : 0 < ε) : ∃ b ∈ s, a < b ∧ b < a + ε :=
  h.exists_between' h₂ <| lt_add_of_pos_right _ hε

theorem IsLub.exists_between_sub_self (h : IsLub s a) (hε : 0 < ε) : ∃ b ∈ s, a - ε < b ∧ b ≤ a :=
  h.exists_between <| sub_lt_self _ hε

theorem IsLub.exists_between_sub_self' (h : IsLub s a) (h₂ : a ∉ s) (hε : 0 < ε) : ∃ b ∈ s, a - ε < b ∧ b < a :=
  h.exists_between' h₂ <| sub_lt_self _ hε

end LinearOrderedAddCommGroup

/-!
### Images of upper/lower bounds under monotone functions
-/


namespace MonotoneOn

variable [Preorderₓ α] [Preorderₓ β] {f : α → β} {s t : Set α} (Hf : MonotoneOn f t) {a : α} (Hst : s ⊆ t)

include Hf

theorem mem_upper_bounds_image (Has : a ∈ UpperBounds s) (Hat : a ∈ t) : f a ∈ UpperBounds (f '' s) :=
  ball_image_of_ball fun x H => Hf (Hst H) Hat (Has H)

theorem mem_upper_bounds_image_self : a ∈ UpperBounds t → a ∈ t → f a ∈ UpperBounds (f '' t) :=
  Hf.mem_upper_bounds_image subset_rfl

theorem mem_lower_bounds_image (Has : a ∈ LowerBounds s) (Hat : a ∈ t) : f a ∈ LowerBounds (f '' s) :=
  ball_image_of_ball fun x H => Hf Hat (Hst H) (Has H)

theorem mem_lower_bounds_image_self : a ∈ LowerBounds t → a ∈ t → f a ∈ LowerBounds (f '' t) :=
  Hf.mem_lower_bounds_image subset_rfl

theorem image_upper_bounds_subset_upper_bounds_image (Hst : s ⊆ t) : f '' (UpperBounds s ∩ t) ⊆ UpperBounds (f '' s) :=
  by
  rintro _ ⟨a, ha, rfl⟩
  exact Hf.mem_upper_bounds_image Hst ha.1 ha.2

theorem image_lower_bounds_subset_lower_bounds_image : f '' (LowerBounds s ∩ t) ⊆ LowerBounds (f '' s) :=
  Hf.dual.image_upper_bounds_subset_upper_bounds_image Hst

/-- The image under a monotone function on a set `t` of a subset which has an upper bound in `t`
  is bounded above. -/
theorem map_bdd_above : (UpperBounds s ∩ t).Nonempty → BddAbove (f '' s) := fun ⟨C, hs, ht⟩ =>
  ⟨f C, Hf.mem_upper_bounds_image Hst hs ht⟩

/-- The image under a monotone function on a set `t` of a subset which has a lower bound in `t`
  is bounded below. -/
theorem map_bdd_below : (LowerBounds s ∩ t).Nonempty → BddBelow (f '' s) := fun ⟨C, hs, ht⟩ =>
  ⟨f C, Hf.mem_lower_bounds_image Hst hs ht⟩

/-- A monotone map sends a least element of a set to a least element of its image. -/
theorem map_is_least (Ha : IsLeast t a) : IsLeast (f '' t) (f a) :=
  ⟨mem_image_of_mem _ Ha.1, Hf.mem_lower_bounds_image_self Ha.2 Ha.1⟩

/-- A monotone map sends a greatest element of a set to a greatest element of its image. -/
theorem map_is_greatest (Ha : IsGreatest t a) : IsGreatest (f '' t) (f a) :=
  ⟨mem_image_of_mem _ Ha.1, Hf.mem_upper_bounds_image_self Ha.2 Ha.1⟩

end MonotoneOn

namespace AntitoneOn

variable [Preorderₓ α] [Preorderₓ β] {f : α → β} {s t : Set α} (Hf : AntitoneOn f t) {a : α} (Hst : s ⊆ t)

include Hf

theorem mem_upper_bounds_image (Has : a ∈ LowerBounds s) : a ∈ t → f a ∈ UpperBounds (f '' s) :=
  Hf.dual_right.mem_lower_bounds_image Hst Has

theorem mem_upper_bounds_image_self : a ∈ LowerBounds t → a ∈ t → f a ∈ UpperBounds (f '' t) :=
  Hf.dual_right.mem_lower_bounds_image_self

theorem mem_lower_bounds_image : a ∈ UpperBounds s → a ∈ t → f a ∈ LowerBounds (f '' s) :=
  Hf.dual_right.mem_upper_bounds_image Hst

theorem mem_lower_bounds_image_self : a ∈ UpperBounds t → a ∈ t → f a ∈ LowerBounds (f '' t) :=
  Hf.dual_right.mem_upper_bounds_image_self

theorem image_lower_bounds_subset_upper_bounds_image : f '' (LowerBounds s ∩ t) ⊆ UpperBounds (f '' s) :=
  Hf.dual_right.image_lower_bounds_subset_lower_bounds_image Hst

theorem image_upper_bounds_subset_lower_bounds_image : f '' (UpperBounds s ∩ t) ⊆ LowerBounds (f '' s) :=
  Hf.dual_right.image_upper_bounds_subset_upper_bounds_image Hst

/-- The image under an antitone function of a set which is bounded above is bounded below. -/
theorem map_bdd_above : (UpperBounds s ∩ t).Nonempty → BddBelow (f '' s) :=
  Hf.dual_right.map_bdd_above Hst

/-- The image under an antitone function of a set which is bounded below is bounded above. -/
theorem map_bdd_below : (LowerBounds s ∩ t).Nonempty → BddAbove (f '' s) :=
  Hf.dual_right.map_bdd_below Hst

/-- An antitone map sends a greatest element of a set to a least element of its image. -/
theorem map_is_greatest : IsGreatest t a → IsLeast (f '' t) (f a) :=
  Hf.dual_right.map_is_greatest

/-- An antitone map sends a least element of a set to a greatest element of its image. -/
theorem map_is_least : IsLeast t a → IsGreatest (f '' t) (f a) :=
  Hf.dual_right.map_is_least

end AntitoneOn

namespace Monotone

variable [Preorderₓ α] [Preorderₓ β] {f : α → β} (Hf : Monotone f) {a : α} {s : Set α}

include Hf

theorem mem_upper_bounds_image (Ha : a ∈ UpperBounds s) : f a ∈ UpperBounds (f '' s) :=
  ball_image_of_ball fun x H => Hf (Ha H)

theorem mem_lower_bounds_image (Ha : a ∈ LowerBounds s) : f a ∈ LowerBounds (f '' s) :=
  ball_image_of_ball fun x H => Hf (Ha H)

theorem image_upper_bounds_subset_upper_bounds_image : f '' UpperBounds s ⊆ UpperBounds (f '' s) := by
  rintro _ ⟨a, ha, rfl⟩
  exact Hf.mem_upper_bounds_image ha

theorem image_lower_bounds_subset_lower_bounds_image : f '' LowerBounds s ⊆ LowerBounds (f '' s) :=
  Hf.dual.image_upper_bounds_subset_upper_bounds_image

/-- The image under a monotone function of a set which is bounded above is bounded above. See also
`bdd_above.image2`. -/
theorem map_bdd_above : BddAbove s → BddAbove (f '' s)
  | ⟨C, hC⟩ => ⟨f C, Hf.mem_upper_bounds_image hC⟩

/-- The image under a monotone function of a set which is bounded below is bounded below. See also
`bdd_below.image2`. -/
theorem map_bdd_below : BddBelow s → BddBelow (f '' s)
  | ⟨C, hC⟩ => ⟨f C, Hf.mem_lower_bounds_image hC⟩

/-- A monotone map sends a least element of a set to a least element of its image. -/
theorem map_is_least (Ha : IsLeast s a) : IsLeast (f '' s) (f a) :=
  ⟨mem_image_of_mem _ Ha.1, Hf.mem_lower_bounds_image Ha.2⟩

/-- A monotone map sends a greatest element of a set to a greatest element of its image. -/
theorem map_is_greatest (Ha : IsGreatest s a) : IsGreatest (f '' s) (f a) :=
  ⟨mem_image_of_mem _ Ha.1, Hf.mem_upper_bounds_image Ha.2⟩

end Monotone

namespace Antitone

variable [Preorderₓ α] [Preorderₓ β] {f : α → β} (hf : Antitone f) {a : α} {s : Set α}

theorem mem_upper_bounds_image : a ∈ LowerBounds s → f a ∈ UpperBounds (f '' s) :=
  hf.dual_right.mem_lower_bounds_image

theorem mem_lower_bounds_image : a ∈ UpperBounds s → f a ∈ LowerBounds (f '' s) :=
  hf.dual_right.mem_upper_bounds_image

theorem image_lower_bounds_subset_upper_bounds_image : f '' LowerBounds s ⊆ UpperBounds (f '' s) :=
  hf.dual_right.image_lower_bounds_subset_lower_bounds_image

theorem image_upper_bounds_subset_lower_bounds_image : f '' UpperBounds s ⊆ LowerBounds (f '' s) :=
  hf.dual_right.image_upper_bounds_subset_upper_bounds_image

/-- The image under an antitone function of a set which is bounded above is bounded below. -/
theorem map_bdd_above : BddAbove s → BddBelow (f '' s) :=
  hf.dual_right.map_bdd_above

/-- The image under an antitone function of a set which is bounded below is bounded above. -/
theorem map_bdd_below : BddBelow s → BddAbove (f '' s) :=
  hf.dual_right.map_bdd_below

/-- An antitone map sends a greatest element of a set to a least element of its image. -/
theorem map_is_greatest : IsGreatest s a → IsLeast (f '' s) (f a) :=
  hf.dual_right.map_is_greatest

/-- An antitone map sends a least element of a set to a greatest element of its image. -/
theorem map_is_least : IsLeast s a → IsGreatest (f '' s) (f a) :=
  hf.dual_right.map_is_least

end Antitone

section Image2

variable [Preorderₓ α] [Preorderₓ β] [Preorderₓ γ] {f : α → β → γ} {s : Set α} {t : Set β} {a : α} {b : β}

section MonotoneMonotone

variable (h₀ : ∀ b, Monotone (swap f b)) (h₁ : ∀ a, Monotone (f a))

include h₀ h₁

theorem mem_upper_bounds_image2 (ha : a ∈ UpperBounds s) (hb : b ∈ UpperBounds t) :
    f a b ∈ UpperBounds (Image2 f s t) :=
  forall_image2_iff.2 fun x hx y hy => (h₀ _ <| ha hx).trans <| h₁ _ <| hb hy

theorem mem_lower_bounds_image2 (ha : a ∈ LowerBounds s) (hb : b ∈ LowerBounds t) :
    f a b ∈ LowerBounds (Image2 f s t) :=
  forall_image2_iff.2 fun x hx y hy => (h₀ _ <| ha hx).trans <| h₁ _ <| hb hy

theorem image2_upper_bounds_upper_bounds_subset :
    Image2 f (UpperBounds s) (UpperBounds t) ⊆ UpperBounds (Image2 f s t) := by
  rintro _ ⟨a, b, ha, hb, rfl⟩
  exact mem_upper_bounds_image2 h₀ h₁ ha hb

theorem image2_lower_bounds_lower_bounds_subset :
    Image2 f (LowerBounds s) (LowerBounds t) ⊆ LowerBounds (Image2 f s t) := by
  rintro _ ⟨a, b, ha, hb, rfl⟩
  exact mem_lower_bounds_image2 h₀ h₁ ha hb

/-- See also `monotone.map_bdd_above`. -/
theorem BddAbove.image2 : BddAbove s → BddAbove t → BddAbove (Image2 f s t) := by
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  exact ⟨f a b, mem_upper_bounds_image2 h₀ h₁ ha hb⟩

/-- See also `monotone.map_bdd_below`. -/
theorem BddBelow.image2 : BddBelow s → BddBelow t → BddBelow (Image2 f s t) := by
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  exact ⟨f a b, mem_lower_bounds_image2 h₀ h₁ ha hb⟩

theorem IsGreatest.image2 (ha : IsGreatest s a) (hb : IsGreatest t b) : IsGreatest (Image2 f s t) (f a b) :=
  ⟨mem_image2_of_mem ha.1 hb.1, mem_upper_bounds_image2 h₀ h₁ ha.2 hb.2⟩

theorem IsLeast.image2 (ha : IsLeast s a) (hb : IsLeast t b) : IsLeast (Image2 f s t) (f a b) :=
  ⟨mem_image2_of_mem ha.1 hb.1, mem_lower_bounds_image2 h₀ h₁ ha.2 hb.2⟩

end MonotoneMonotone

section MonotoneAntitone

variable (h₀ : ∀ b, Monotone (swap f b)) (h₁ : ∀ a, Antitone (f a))

include h₀ h₁

theorem mem_upper_bounds_image2_of_mem_upper_bounds_of_mem_lower_bounds (ha : a ∈ UpperBounds s)
    (hb : b ∈ LowerBounds t) : f a b ∈ UpperBounds (Image2 f s t) :=
  forall_image2_iff.2 fun x hx y hy => (h₀ _ <| ha hx).trans <| h₁ _ <| hb hy

theorem mem_lower_bounds_image2_of_mem_lower_bounds_of_mem_upper_bounds (ha : a ∈ LowerBounds s)
    (hb : b ∈ UpperBounds t) : f a b ∈ LowerBounds (Image2 f s t) :=
  forall_image2_iff.2 fun x hx y hy => (h₀ _ <| ha hx).trans <| h₁ _ <| hb hy

theorem image2_upper_bounds_lower_bounds_subset_upper_bounds_image2 :
    Image2 f (UpperBounds s) (LowerBounds t) ⊆ UpperBounds (Image2 f s t) := by
  rintro _ ⟨a, b, ha, hb, rfl⟩
  exact mem_upper_bounds_image2_of_mem_upper_bounds_of_mem_lower_bounds h₀ h₁ ha hb

theorem image2_lower_bounds_upper_bounds_subset_lower_bounds_image2 :
    Image2 f (LowerBounds s) (UpperBounds t) ⊆ LowerBounds (Image2 f s t) := by
  rintro _ ⟨a, b, ha, hb, rfl⟩
  exact mem_lower_bounds_image2_of_mem_lower_bounds_of_mem_upper_bounds h₀ h₁ ha hb

theorem BddAbove.bdd_above_image2_of_bdd_below : BddAbove s → BddBelow t → BddAbove (Image2 f s t) := by
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  exact ⟨f a b, mem_upper_bounds_image2_of_mem_upper_bounds_of_mem_lower_bounds h₀ h₁ ha hb⟩

theorem BddBelow.bdd_below_image2_of_bdd_above : BddBelow s → BddAbove t → BddBelow (Image2 f s t) := by
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  exact ⟨f a b, mem_lower_bounds_image2_of_mem_lower_bounds_of_mem_upper_bounds h₀ h₁ ha hb⟩

theorem IsGreatest.is_greatest_image2_of_is_least (ha : IsGreatest s a) (hb : IsLeast t b) :
    IsGreatest (Image2 f s t) (f a b) :=
  ⟨mem_image2_of_mem ha.1 hb.1, mem_upper_bounds_image2_of_mem_upper_bounds_of_mem_lower_bounds h₀ h₁ ha.2 hb.2⟩

theorem IsLeast.is_least_image2_of_is_greatest (ha : IsLeast s a) (hb : IsGreatest t b) :
    IsLeast (Image2 f s t) (f a b) :=
  ⟨mem_image2_of_mem ha.1 hb.1, mem_lower_bounds_image2_of_mem_lower_bounds_of_mem_upper_bounds h₀ h₁ ha.2 hb.2⟩

end MonotoneAntitone

section AntitoneAntitone

variable (h₀ : ∀ b, Antitone (swap f b)) (h₁ : ∀ a, Antitone (f a))

include h₀ h₁

theorem mem_upper_bounds_image2_of_mem_lower_bounds (ha : a ∈ LowerBounds s) (hb : b ∈ LowerBounds t) :
    f a b ∈ UpperBounds (Image2 f s t) :=
  forall_image2_iff.2 fun x hx y hy => (h₀ _ <| ha hx).trans <| h₁ _ <| hb hy

theorem mem_lower_bounds_image2_of_mem_upper_bounds (ha : a ∈ UpperBounds s) (hb : b ∈ UpperBounds t) :
    f a b ∈ LowerBounds (Image2 f s t) :=
  forall_image2_iff.2 fun x hx y hy => (h₀ _ <| ha hx).trans <| h₁ _ <| hb hy

theorem image2_upper_bounds_upper_bounds_subset_upper_bounds_image2 :
    Image2 f (LowerBounds s) (LowerBounds t) ⊆ UpperBounds (Image2 f s t) := by
  rintro _ ⟨a, b, ha, hb, rfl⟩
  exact mem_upper_bounds_image2_of_mem_lower_bounds h₀ h₁ ha hb

theorem image2_lower_bounds_lower_bounds_subset_lower_bounds_image2 :
    Image2 f (UpperBounds s) (UpperBounds t) ⊆ LowerBounds (Image2 f s t) := by
  rintro _ ⟨a, b, ha, hb, rfl⟩
  exact mem_lower_bounds_image2_of_mem_upper_bounds h₀ h₁ ha hb

theorem BddBelow.image2_bdd_above : BddBelow s → BddBelow t → BddAbove (Image2 f s t) := by
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  exact ⟨f a b, mem_upper_bounds_image2_of_mem_lower_bounds h₀ h₁ ha hb⟩

theorem BddAbove.image2_bdd_below : BddAbove s → BddAbove t → BddBelow (Image2 f s t) := by
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  exact ⟨f a b, mem_lower_bounds_image2_of_mem_upper_bounds h₀ h₁ ha hb⟩

theorem IsLeast.is_greatest_image2 (ha : IsLeast s a) (hb : IsLeast t b) : IsGreatest (Image2 f s t) (f a b) :=
  ⟨mem_image2_of_mem ha.1 hb.1, mem_upper_bounds_image2_of_mem_lower_bounds h₀ h₁ ha.2 hb.2⟩

theorem IsGreatest.is_least_image2 (ha : IsGreatest s a) (hb : IsGreatest t b) : IsLeast (Image2 f s t) (f a b) :=
  ⟨mem_image2_of_mem ha.1 hb.1, mem_lower_bounds_image2_of_mem_upper_bounds h₀ h₁ ha.2 hb.2⟩

end AntitoneAntitone

section AntitoneMonotone

variable (h₀ : ∀ b, Antitone (swap f b)) (h₁ : ∀ a, Monotone (f a))

include h₀ h₁

theorem mem_upper_bounds_image2_of_mem_upper_bounds_of_mem_upper_bounds (ha : a ∈ LowerBounds s)
    (hb : b ∈ UpperBounds t) : f a b ∈ UpperBounds (Image2 f s t) :=
  forall_image2_iff.2 fun x hx y hy => (h₀ _ <| ha hx).trans <| h₁ _ <| hb hy

theorem mem_lower_bounds_image2_of_mem_lower_bounds_of_mem_lower_bounds (ha : a ∈ UpperBounds s)
    (hb : b ∈ LowerBounds t) : f a b ∈ LowerBounds (Image2 f s t) :=
  forall_image2_iff.2 fun x hx y hy => (h₀ _ <| ha hx).trans <| h₁ _ <| hb hy

theorem image2_lower_bounds_upper_bounds_subset_upper_bounds_image2 :
    Image2 f (LowerBounds s) (UpperBounds t) ⊆ UpperBounds (Image2 f s t) := by
  rintro _ ⟨a, b, ha, hb, rfl⟩
  exact mem_upper_bounds_image2_of_mem_upper_bounds_of_mem_upper_bounds h₀ h₁ ha hb

theorem image2_upper_bounds_lower_bounds_subset_lower_bounds_image2 :
    Image2 f (UpperBounds s) (LowerBounds t) ⊆ LowerBounds (Image2 f s t) := by
  rintro _ ⟨a, b, ha, hb, rfl⟩
  exact mem_lower_bounds_image2_of_mem_lower_bounds_of_mem_lower_bounds h₀ h₁ ha hb

theorem BddBelow.bdd_above_image2_of_bdd_above : BddBelow s → BddAbove t → BddAbove (Image2 f s t) := by
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  exact ⟨f a b, mem_upper_bounds_image2_of_mem_upper_bounds_of_mem_upper_bounds h₀ h₁ ha hb⟩

theorem BddAbove.bdd_below_image2_of_bdd_above : BddAbove s → BddBelow t → BddBelow (Image2 f s t) := by
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  exact ⟨f a b, mem_lower_bounds_image2_of_mem_lower_bounds_of_mem_lower_bounds h₀ h₁ ha hb⟩

theorem IsLeast.is_greatest_image2_of_is_greatest (ha : IsLeast s a) (hb : IsGreatest t b) :
    IsGreatest (Image2 f s t) (f a b) :=
  ⟨mem_image2_of_mem ha.1 hb.1, mem_upper_bounds_image2_of_mem_upper_bounds_of_mem_upper_bounds h₀ h₁ ha.2 hb.2⟩

theorem IsGreatest.is_least_image2_of_is_least (ha : IsGreatest s a) (hb : IsLeast t b) :
    IsLeast (Image2 f s t) (f a b) :=
  ⟨mem_image2_of_mem ha.1 hb.1, mem_lower_bounds_image2_of_mem_lower_bounds_of_mem_lower_bounds h₀ h₁ ha.2 hb.2⟩

end AntitoneMonotone

end Image2

theorem IsGlb.of_image [Preorderₓ α] [Preorderₓ β] {f : α → β} (hf : ∀ {x y}, f x ≤ f y ↔ x ≤ y) {s : Set α} {x : α}
    (hx : IsGlb (f '' s) (f x)) : IsGlb s x :=
  ⟨fun y hy => hf.1 <| hx.1 <| mem_image_of_mem _ hy, fun y hy =>
    hf.1 <| hx.2 <| Monotone.mem_lower_bounds_image (fun x y => hf.2) hy⟩

theorem IsLub.of_image [Preorderₓ α] [Preorderₓ β] {f : α → β} (hf : ∀ {x y}, f x ≤ f y ↔ x ≤ y) {s : Set α} {x : α}
    (hx : IsLub (f '' s) (f x)) : IsLub s x :=
  @IsGlb.of_image αᵒᵈ βᵒᵈ _ _ f (fun x y => hf) _ _ hx

theorem is_lub_pi {π : α → Type _} [∀ a, Preorderₓ (π a)] {s : Set (∀ a, π a)} {f : ∀ a, π a} :
    IsLub s f ↔ ∀ a, IsLub (Function.eval a '' s) (f a) := by
  classical
  refine' ⟨fun H a => ⟨(Function.monotone_eval a).mem_upper_bounds_image H.1, fun b hb => _⟩, fun H => ⟨_, _⟩⟩
  · suffices : Function.update f a b ∈ UpperBounds s
    exact Function.update_same a b f ▸ H.2 this a
    refine' fun g hg => le_update_iff.2 ⟨hb <| mem_image_of_mem _ hg, fun i hi => H.1 hg i⟩
    
  · exact fun g hg a => (H a).1 (mem_image_of_mem _ hg)
    
  · exact fun g hg a => (H a).2 ((Function.monotone_eval a).mem_upper_bounds_image hg)
    

theorem is_glb_pi {π : α → Type _} [∀ a, Preorderₓ (π a)] {s : Set (∀ a, π a)} {f : ∀ a, π a} :
    IsGlb s f ↔ ∀ a, IsGlb (Function.eval a '' s) (f a) :=
  @is_lub_pi α (fun a => (π a)ᵒᵈ) _ s f

theorem is_lub_prod [Preorderₓ α] [Preorderₓ β] {s : Set (α × β)} (p : α × β) :
    IsLub s p ↔ IsLub (Prod.fst '' s) p.1 ∧ IsLub (Prod.snd '' s) p.2 := by
  refine'
    ⟨fun H =>
      ⟨⟨monotone_fst.mem_upper_bounds_image H.1, fun a ha => _⟩,
        ⟨monotone_snd.mem_upper_bounds_image H.1, fun a ha => _⟩⟩,
      fun H => ⟨_, _⟩⟩
  · suffices : (a, p.2) ∈ UpperBounds s
    exact (H.2 this).1
    exact fun q hq => ⟨ha <| mem_image_of_mem _ hq, (H.1 hq).2⟩
    
  · suffices : (p.1, a) ∈ UpperBounds s
    exact (H.2 this).2
    exact fun q hq => ⟨(H.1 hq).1, ha <| mem_image_of_mem _ hq⟩
    
  · exact fun q hq => ⟨H.1.1 <| mem_image_of_mem _ hq, H.2.1 <| mem_image_of_mem _ hq⟩
    
  · exact fun q hq => ⟨H.1.2 <| monotone_fst.mem_upper_bounds_image hq, H.2.2 <| monotone_snd.mem_upper_bounds_image hq⟩
    

theorem is_glb_prod [Preorderₓ α] [Preorderₓ β] {s : Set (α × β)} (p : α × β) :
    IsGlb s p ↔ IsGlb (Prod.fst '' s) p.1 ∧ IsGlb (Prod.snd '' s) p.2 :=
  @is_lub_prod αᵒᵈ βᵒᵈ _ _ _ _

namespace OrderIso

variable [Preorderₓ α] [Preorderₓ β] (f : α ≃o β)

theorem upper_bounds_image {s : Set α} : UpperBounds (f '' s) = f '' UpperBounds s :=
  Subset.antisymm
    (fun x hx => ⟨f.symm x, fun y hy => f.le_symm_apply.2 (hx <| mem_image_of_mem _ hy), f.apply_symm_apply x⟩)
    f.Monotone.image_upper_bounds_subset_upper_bounds_image

theorem lower_bounds_image {s : Set α} : LowerBounds (f '' s) = f '' LowerBounds s :=
  @upper_bounds_image αᵒᵈ βᵒᵈ _ _ f.dual _

@[simp]
theorem is_lub_image {s : Set α} {x : β} : IsLub (f '' s) x ↔ IsLub s (f.symm x) :=
  ⟨fun h => IsLub.of_image (fun _ _ => f.le_iff_le) ((f.apply_symm_apply x).symm ▸ h), fun h =>
    (IsLub.of_image fun _ _ => f.symm.le_iff_le) <| (f.symm_image_image s).symm ▸ h⟩

theorem is_lub_image' {s : Set α} {x : α} : IsLub (f '' s) (f x) ↔ IsLub s x := by
  rw [is_lub_image, f.symm_apply_apply]

@[simp]
theorem is_glb_image {s : Set α} {x : β} : IsGlb (f '' s) x ↔ IsGlb s (f.symm x) :=
  f.dual.is_lub_image

theorem is_glb_image' {s : Set α} {x : α} : IsGlb (f '' s) (f x) ↔ IsGlb s x :=
  f.dual.is_lub_image'

@[simp]
theorem is_lub_preimage {s : Set β} {x : α} : IsLub (f ⁻¹' s) x ↔ IsLub s (f x) := by
  rw [← f.symm_symm, ← image_eq_preimage, is_lub_image]

theorem is_lub_preimage' {s : Set β} {x : β} : IsLub (f ⁻¹' s) (f.symm x) ↔ IsLub s x := by
  rw [is_lub_preimage, f.apply_symm_apply]

@[simp]
theorem is_glb_preimage {s : Set β} {x : α} : IsGlb (f ⁻¹' s) x ↔ IsGlb s (f x) :=
  f.dual.is_lub_preimage

theorem is_glb_preimage' {s : Set β} {x : β} : IsGlb (f ⁻¹' s) (f.symm x) ↔ IsGlb s x :=
  f.dual.is_lub_preimage'

end OrderIso

