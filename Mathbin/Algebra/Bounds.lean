/-
Copyright (c) 2021 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import Mathbin.Data.Set.Pointwise
import Mathbin.Order.ConditionallyCompleteLattice

/-!
# Upper/lower bounds in ordered monoids and groups

In this file we prove a few facts like “`-s` is bounded above iff `s` is bounded below”
(`bdd_above_neg`).
-/


open Function Set

open Pointwise

section inv_neg

variable {G : Type _} [Groupₓ G] [Preorderₓ G] [CovariantClass G G (· * ·) (· ≤ ·)]
  [CovariantClass G G (swap (· * ·)) (· ≤ ·)] {s : Set G} {a : G}

@[simp, to_additive]
theorem bdd_above_inv : BddAbove s⁻¹ ↔ BddBelow s :=
  (OrderIso.inv G).bdd_above_preimage

@[simp, to_additive]
theorem bdd_below_inv : BddBelow s⁻¹ ↔ BddAbove s :=
  (OrderIso.inv G).bdd_below_preimage

@[to_additive]
theorem BddAbove.inv (h : BddAbove s) : BddBelow s⁻¹ :=
  bdd_below_inv.2 h

@[to_additive]
theorem BddBelow.inv (h : BddBelow s) : BddAbove s⁻¹ :=
  bdd_above_inv.2 h

@[simp, to_additive]
theorem is_lub_inv : IsLub s⁻¹ a ↔ IsGlb s a⁻¹ :=
  (OrderIso.inv G).is_lub_preimage

@[to_additive]
theorem is_lub_inv' : IsLub s⁻¹ a⁻¹ ↔ IsGlb s a :=
  (OrderIso.inv G).is_lub_preimage'

@[to_additive]
theorem IsGlb.inv (h : IsGlb s a) : IsLub s⁻¹ a⁻¹ :=
  is_lub_inv'.2 h

@[simp, to_additive]
theorem is_glb_inv : IsGlb s⁻¹ a ↔ IsLub s a⁻¹ :=
  (OrderIso.inv G).is_glb_preimage

@[to_additive]
theorem is_glb_inv' : IsGlb s⁻¹ a⁻¹ ↔ IsLub s a :=
  (OrderIso.inv G).is_glb_preimage'

@[to_additive]
theorem IsLub.inv (h : IsLub s a) : IsGlb s⁻¹ a⁻¹ :=
  is_glb_inv'.2 h

end inv_neg

section mul_addₓ

variable {M : Type _} [Mul M] [Preorderₓ M] [CovariantClass M M (· * ·) (· ≤ ·)]
  [CovariantClass M M (swap (· * ·)) (· ≤ ·)]

@[to_additive]
theorem mul_mem_upper_bounds_mul {s t : Set M} {a b : M} (ha : a ∈ UpperBounds s) (hb : b ∈ UpperBounds t) :
    a * b ∈ UpperBounds (s * t) :=
  forall_image2_iff.2 fun x hx y hy => mul_le_mul' (ha hx) (hb hy)

@[to_additive]
theorem subset_upper_bounds_mul (s t : Set M) : UpperBounds s * UpperBounds t ⊆ UpperBounds (s * t) :=
  image2_subset_iff.2 fun x hx y hy => mul_mem_upper_bounds_mul hx hy

@[to_additive]
theorem mul_mem_lower_bounds_mul {s t : Set M} {a b : M} (ha : a ∈ LowerBounds s) (hb : b ∈ LowerBounds t) :
    a * b ∈ LowerBounds (s * t) :=
  @mul_mem_upper_bounds_mul Mᵒᵈ _ _ _ _ _ _ _ _ ha hb

@[to_additive]
theorem subset_lower_bounds_mul (s t : Set M) : LowerBounds s * LowerBounds t ⊆ LowerBounds (s * t) :=
  @subset_upper_bounds_mul Mᵒᵈ _ _ _ _ _ _

@[to_additive]
theorem BddAbove.mul {s t : Set M} (hs : BddAbove s) (ht : BddAbove t) : BddAbove (s * t) :=
  (hs.mul ht).mono (subset_upper_bounds_mul s t)

@[to_additive]
theorem BddBelow.mul {s t : Set M} (hs : BddBelow s) (ht : BddBelow t) : BddBelow (s * t) :=
  (hs.mul ht).mono (subset_lower_bounds_mul s t)

end mul_addₓ

section ConditionallyCompleteLattice

section Right

variable {ι G : Type _} [Groupₓ G] [ConditionallyCompleteLattice G] [CovariantClass G G (Function.swap (· * ·)) (· ≤ ·)]
  [Nonempty ι] {f : ι → G}

@[to_additive]
theorem csupr_mul (hf : BddAbove (Set.Range f)) (a : G) : (⨆ i, f i) * a = ⨆ i, f i * a :=
  (OrderIso.mulRight a).map_csupr hf

@[to_additive]
theorem csupr_div (hf : BddAbove (Set.Range f)) (a : G) : (⨆ i, f i) / a = ⨆ i, f i / a := by
  simp only [← div_eq_mul_inv, ← csupr_mul hf]

end Right

section Left

variable {ι G : Type _} [Groupₓ G] [ConditionallyCompleteLattice G] [CovariantClass G G (· * ·) (· ≤ ·)] [Nonempty ι]
  {f : ι → G}

@[to_additive]
theorem mul_csupr (hf : BddAbove (Set.Range f)) (a : G) : (a * ⨆ i, f i) = ⨆ i, a * f i :=
  (OrderIso.mulLeft a).map_csupr hf

end Left

end ConditionallyCompleteLattice

