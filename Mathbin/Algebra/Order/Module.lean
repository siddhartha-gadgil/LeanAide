/-
Copyright (c) 2020 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis, Yaël Dillies
-/
import Mathbin.Algebra.Module.Pi
import Mathbin.Algebra.Module.Prod
import Mathbin.Algebra.Order.Pi
import Mathbin.Algebra.Order.Smul
import Mathbin.Data.Set.Pointwise

/-!
# Ordered module

In this file we provide lemmas about `ordered_smul` that hold once a module structure is present.

## References

* https://en.wikipedia.org/wiki/Ordered_module

## Tags

ordered module, ordered scalar, ordered smul, ordered action, ordered vector space
-/


open Pointwise

variable {k M N : Type _}

namespace OrderDual

instance [Semiringₓ k] [OrderedAddCommMonoid M] [Module k M] : Module k Mᵒᵈ where
  add_smul := fun r s x => OrderDual.rec (add_smul _ _) x
  zero_smul := fun m => OrderDual.rec (zero_smul _) m

end OrderDual

section Semiringₓ

variable [OrderedSemiring k] [OrderedAddCommGroup M] [Module k M] [OrderedSmul k M] {a b : M} {c : k}

/- can be generalized from `module k M` to `distrib_mul_action_with_zero k M` once it exists.
where `distrib_mul_action_with_zero k M`is the conjunction of `distrib_mul_action k M` and
`smul_with_zero k M`.-/
theorem smul_neg_iff_of_pos (hc : 0 < c) : c • a < 0 ↔ a < 0 := by
  rw [← neg_negₓ a, smul_neg, neg_neg_iff_pos, neg_neg_iff_pos]
  exact smul_pos_iff_of_pos hc

end Semiringₓ

section Ringₓ

variable [OrderedRing k] [OrderedAddCommGroup M] [Module k M] [OrderedSmul k M] {a b : M} {c : k}

theorem smul_lt_smul_of_neg (h : a < b) (hc : c < 0) : c • b < c • a := by
  rw [← neg_negₓ c, neg_smul, neg_smul (-c), neg_lt_neg_iff]
  exact smul_lt_smul_of_pos h (neg_pos_of_neg hc)

theorem smul_le_smul_of_nonpos (h : a ≤ b) (hc : c ≤ 0) : c • b ≤ c • a := by
  rw [← neg_negₓ c, neg_smul, neg_smul (-c), neg_le_neg_iff]
  exact smul_le_smul_of_nonneg h (neg_nonneg_of_nonpos hc)

theorem eq_of_smul_eq_smul_of_neg_of_le (hab : c • a = c • b) (hc : c < 0) (h : a ≤ b) : a = b := by
  rw [← neg_negₓ c, neg_smul, neg_smul (-c), neg_inj] at hab
  exact eq_of_smul_eq_smul_of_pos_of_le hab (neg_pos_of_neg hc) h

theorem lt_of_smul_lt_smul_of_nonpos (h : c • a < c • b) (hc : c ≤ 0) : b < a := by
  rw [← neg_negₓ c, neg_smul, neg_smul (-c), neg_lt_neg_iff] at h
  exact lt_of_smul_lt_smul_of_nonneg h (neg_nonneg_of_nonpos hc)

theorem smul_lt_smul_iff_of_neg (hc : c < 0) : c • a < c • b ↔ b < a := by
  rw [← neg_negₓ c, neg_smul, neg_smul (-c), neg_lt_neg_iff]
  exact smul_lt_smul_iff_of_pos (neg_pos_of_neg hc)

theorem smul_neg_iff_of_neg (hc : c < 0) : c • a < 0 ↔ 0 < a := by
  rw [← neg_negₓ c, neg_smul, neg_neg_iff_pos]
  exact smul_pos_iff_of_pos (neg_pos_of_neg hc)

theorem smul_pos_iff_of_neg (hc : c < 0) : 0 < c • a ↔ a < 0 := by
  rw [← neg_negₓ c, neg_smul, neg_pos]
  exact smul_neg_iff_of_pos (neg_pos_of_neg hc)

theorem smul_nonpos_of_nonpos_of_nonneg (hc : c ≤ 0) (ha : 0 ≤ a) : c • a ≤ 0 :=
  calc
    c • a ≤ c • 0 := smul_le_smul_of_nonpos ha hc
    _ = 0 := smul_zero' M c
    

theorem smul_nonneg_of_nonpos_of_nonpos (hc : c ≤ 0) (ha : a ≤ 0) : 0 ≤ c • a :=
  @smul_nonpos_of_nonpos_of_nonneg k Mᵒᵈ _ _ _ _ _ _ hc ha

alias smul_pos_iff_of_neg ↔ _ smul_pos_of_neg_of_neg

alias smul_neg_iff_of_pos ↔ _ smul_neg_of_pos_of_neg

alias smul_neg_iff_of_neg ↔ _ smul_neg_of_neg_of_pos

theorem antitone_smul_left (hc : c ≤ 0) : Antitone (HasSmul.smul c : M → M) := fun a b h => smul_le_smul_of_nonpos h hc

theorem strict_anti_smul_left (hc : c < 0) : StrictAnti (HasSmul.smul c : M → M) := fun a b h =>
  smul_lt_smul_of_neg h hc

/-- Binary **rearrangement inequality**. -/
theorem smul_add_smul_le_smul_add_smul [ContravariantClass M M (· + ·) (· ≤ ·)] {a b : k} {c d : M} (hab : a ≤ b)
    (hcd : c ≤ d) : a • d + b • c ≤ a • c + b • d := by
  obtain ⟨b, rfl⟩ := exists_add_of_le hab
  obtain ⟨d, rfl⟩ := exists_add_of_le hcd
  rw [smul_add, add_right_commₓ, smul_add, ← add_assocₓ, add_smul _ _ d]
  rw [le_add_iff_nonneg_right] at hab hcd
  exact add_le_add_left (le_add_of_nonneg_right <| smul_nonneg hab hcd) _

/-- Binary **rearrangement inequality**. -/
theorem smul_add_smul_le_smul_add_smul' [ContravariantClass M M (· + ·) (· ≤ ·)] {a b : k} {c d : M} (hba : b ≤ a)
    (hdc : d ≤ c) : a • d + b • c ≤ a • c + b • d := by
  rw [add_commₓ (a • d), add_commₓ (a • c)]
  exact smul_add_smul_le_smul_add_smul hba hdc

/-- Binary strict **rearrangement inequality**. -/
theorem smul_add_smul_lt_smul_add_smul [CovariantClass M M (· + ·) (· < ·)] [ContravariantClass M M (· + ·) (· < ·)]
    {a b : k} {c d : M} (hab : a < b) (hcd : c < d) : a • d + b • c < a • c + b • d := by
  obtain ⟨b, rfl⟩ := exists_add_of_le hab.le
  obtain ⟨d, rfl⟩ := exists_add_of_le hcd.le
  rw [smul_add, add_right_commₓ, smul_add, ← add_assocₓ, add_smul _ _ d]
  rw [lt_add_iff_pos_right] at hab hcd
  exact add_lt_add_left (lt_add_of_pos_right _ <| smul_pos hab hcd) _

/-- Binary strict **rearrangement inequality**. -/
theorem smul_add_smul_lt_smul_add_smul' [CovariantClass M M (· + ·) (· < ·)] [ContravariantClass M M (· + ·) (· < ·)]
    {a b : k} {c d : M} (hba : b < a) (hdc : d < c) : a • d + b • c < a • c + b • d := by
  rw [add_commₓ (a • d), add_commₓ (a • c)]
  exact smul_add_smul_lt_smul_add_smul hba hdc

end Ringₓ

section Field

variable [LinearOrderedField k] [OrderedAddCommGroup M] [Module k M] [OrderedSmul k M] {a b : M} {c : k}

theorem smul_le_smul_iff_of_neg (hc : c < 0) : c • a ≤ c • b ↔ b ≤ a := by
  rw [← neg_negₓ c, neg_smul, neg_smul (-c), neg_le_neg_iff]
  exact smul_le_smul_iff_of_pos (neg_pos_of_neg hc)

theorem smul_lt_iff_of_neg (hc : c < 0) : c • a < b ↔ c⁻¹ • b < a := by
  rw [← neg_negₓ c, ← neg_negₓ a, neg_smul_neg, inv_neg, neg_smul _ b, neg_lt_neg_iff]
  exact smul_lt_iff_of_pos (neg_pos_of_neg hc)

theorem lt_smul_iff_of_neg (hc : c < 0) : a < c • b ↔ b < c⁻¹ • a := by
  rw [← neg_negₓ c, ← neg_negₓ b, neg_smul_neg, inv_neg, neg_smul _ a, neg_lt_neg_iff]
  exact lt_smul_iff_of_pos (neg_pos_of_neg hc)

variable (M)

/-- Left scalar multiplication as an order isomorphism. -/
@[simps]
def OrderIso.smulLeftDual {c : k} (hc : c < 0) : M ≃o Mᵒᵈ where
  toFun := fun b => OrderDual.toDual (c • b)
  invFun := fun b => c⁻¹ • OrderDual.ofDual b
  left_inv := inv_smul_smul₀ hc.Ne
  right_inv := smul_inv_smul₀ hc.Ne
  map_rel_iff' := fun b₁ b₂ => smul_le_smul_iff_of_neg hc

variable {M} [OrderedAddCommGroup N] [Module k N] [OrderedSmul k N]

-- TODO: solve `prod.has_lt` and `prod.has_le` misalignment issue
instance Prod.ordered_smul : OrderedSmul k (M × N) :=
  OrderedSmul.mk' fun (v u : M × N) (c : k) h hc =>
    ⟨smul_le_smul_of_nonneg h.1.1 hc.le, smul_le_smul_of_nonneg h.1.2 hc.le⟩

instance Pi.smulWithZero'' {ι : Type _} {M : ι → Type _} [∀ i, OrderedAddCommGroup (M i)]
    [∀ i, MulActionWithZero k (M i)] : SmulWithZero k (∀ i : ι, M i) := by
  infer_instance

instance Pi.ordered_smul {ι : Type _} {M : ι → Type _} [∀ i, OrderedAddCommGroup (M i)] [∀ i, MulActionWithZero k (M i)]
    [∀ i, OrderedSmul k (M i)] : OrderedSmul k (∀ i : ι, M i) := by
  refine' OrderedSmul.mk' fun v u c h hc i => _
  change c • v i ≤ c • u i
  exact smul_le_smul_of_nonneg (h.le i) hc.le

-- Sometimes Lean fails to apply the dependent version to non-dependent functions,
-- so we define another instance
instance Pi.ordered_smul' {ι : Type _} {M : Type _} [OrderedAddCommGroup M] [MulActionWithZero k M] [OrderedSmul k M] :
    OrderedSmul k (ι → M) :=
  Pi.ordered_smul

end Field

/-! ### Upper/lower bounds -/


section OrderedSemiring

variable [OrderedSemiring k] [OrderedAddCommMonoid M] [SmulWithZero k M] [OrderedSmul k M] {s : Set M} {c : k}

theorem smul_lower_bounds_subset_lower_bounds_smul (hc : 0 ≤ c) : c • LowerBounds s ⊆ LowerBounds (c • s) :=
  (monotone_smul_left hc).image_lower_bounds_subset_lower_bounds_image

theorem smul_upper_bounds_subset_upper_bounds_smul (hc : 0 ≤ c) : c • UpperBounds s ⊆ UpperBounds (c • s) :=
  (monotone_smul_left hc).image_upper_bounds_subset_upper_bounds_image

theorem BddBelow.smul_of_nonneg (hs : BddBelow s) (hc : 0 ≤ c) : BddBelow (c • s) :=
  (monotone_smul_left hc).map_bdd_below hs

theorem BddAbove.smul_of_nonneg (hs : BddAbove s) (hc : 0 ≤ c) : BddAbove (c • s) :=
  (monotone_smul_left hc).map_bdd_above hs

end OrderedSemiring

section OrderedRing

variable [OrderedRing k] [OrderedAddCommGroup M] [Module k M] [OrderedSmul k M] {s : Set M} {c : k}

theorem smul_lower_bounds_subset_upper_bounds_smul (hc : c ≤ 0) : c • LowerBounds s ⊆ UpperBounds (c • s) :=
  (antitone_smul_left hc).image_lower_bounds_subset_upper_bounds_image

theorem smul_upper_bounds_subset_lower_bounds_smul (hc : c ≤ 0) : c • UpperBounds s ⊆ LowerBounds (c • s) :=
  (antitone_smul_left hc).image_upper_bounds_subset_lower_bounds_image

theorem BddBelow.smul_of_nonpos (hc : c ≤ 0) (hs : BddBelow s) : BddAbove (c • s) :=
  (antitone_smul_left hc).map_bdd_below hs

theorem BddAbove.smul_of_nonpos (hc : c ≤ 0) (hs : BddAbove s) : BddBelow (c • s) :=
  (antitone_smul_left hc).map_bdd_above hs

end OrderedRing

section LinearOrderedField

variable [LinearOrderedField k] [OrderedAddCommGroup M]

section MulActionWithZero

variable [MulActionWithZero k M] [OrderedSmul k M] {s t : Set M} {c : k}

@[simp]
theorem lower_bounds_smul_of_pos (hc : 0 < c) : LowerBounds (c • s) = c • LowerBounds s :=
  (OrderIso.smulLeft _ hc).lower_bounds_image

@[simp]
theorem upper_bounds_smul_of_pos (hc : 0 < c) : UpperBounds (c • s) = c • UpperBounds s :=
  (OrderIso.smulLeft _ hc).upper_bounds_image

@[simp]
theorem bdd_below_smul_iff_of_pos (hc : 0 < c) : BddBelow (c • s) ↔ BddBelow s :=
  (OrderIso.smulLeft _ hc).bdd_below_image

@[simp]
theorem bdd_above_smul_iff_of_pos (hc : 0 < c) : BddAbove (c • s) ↔ BddAbove s :=
  (OrderIso.smulLeft _ hc).bdd_above_image

end MulActionWithZero

section Module

variable [Module k M] [OrderedSmul k M] {s t : Set M} {c : k}

@[simp]
theorem lower_bounds_smul_of_neg (hc : c < 0) : LowerBounds (c • s) = c • UpperBounds s :=
  (OrderIso.smulLeftDual M hc).upper_bounds_image

@[simp]
theorem upper_bounds_smul_of_neg (hc : c < 0) : UpperBounds (c • s) = c • LowerBounds s :=
  (OrderIso.smulLeftDual M hc).lower_bounds_image

@[simp]
theorem bdd_below_smul_iff_of_neg (hc : c < 0) : BddBelow (c • s) ↔ BddAbove s :=
  (OrderIso.smulLeftDual M hc).bdd_above_image

@[simp]
theorem bdd_above_smul_iff_of_neg (hc : c < 0) : BddAbove (c • s) ↔ BddBelow s :=
  (OrderIso.smulLeftDual M hc).bdd_below_image

end Module

end LinearOrderedField

