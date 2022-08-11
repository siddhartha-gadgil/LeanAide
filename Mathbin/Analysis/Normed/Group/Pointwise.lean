/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathbin.Analysis.Normed.Group.AddTorsor
import Mathbin.Topology.MetricSpace.HausdorffDistance

/-!
# Properties of pointwise addition of sets in normed groups

We explore the relationships between pointwise addition of sets in normed groups, and the norm.
Notably, we show that the sum of bounded sets remain bounded.
-/


open Metric Set

open Pointwise TopologicalSpace

section SemiNormedGroup

variable {E : Type _} [SemiNormedGroup E] {ε δ : ℝ} {s t : Set E} {x y : E}

theorem bounded_iff_exists_norm_le : Bounded s ↔ ∃ R, ∀, ∀ x ∈ s, ∀, ∥x∥ ≤ R := by
  simp [← subset_def, ← bounded_iff_subset_ball (0 : E)]

alias bounded_iff_exists_norm_le ↔ Metric.Bounded.exists_norm_le _

theorem Metric.Bounded.exists_pos_norm_le (hs : Metric.Bounded s) : ∃ R > 0, ∀, ∀ x ∈ s, ∀, ∥x∥ ≤ R := by
  obtain ⟨R₀, hR₀⟩ := hs.exists_norm_le
  refine' ⟨max R₀ 1, _, _⟩
  · exact
      (by
            norm_num : (0 : ℝ) < 1).trans_le
        (le_max_rightₓ R₀ 1)
    
  intro x hx
  exact (hR₀ x hx).trans (le_max_leftₓ _ _)

theorem Metric.Bounded.add (hs : Bounded s) (ht : Bounded t) : Bounded (s + t) := by
  obtain ⟨Rs, hRs⟩ : ∃ R : ℝ, ∀, ∀ x ∈ s, ∀, ∥x∥ ≤ R := hs.exists_norm_le
  obtain ⟨Rt, hRt⟩ : ∃ R : ℝ, ∀, ∀ x ∈ t, ∀, ∥x∥ ≤ R := ht.exists_norm_le
  refine' bounded_iff_exists_norm_le.2 ⟨Rs + Rt, _⟩
  rintro z ⟨x, y, hx, hy, rfl⟩
  calc ∥x + y∥ ≤ ∥x∥ + ∥y∥ := norm_add_le _ _ _ ≤ Rs + Rt := add_le_add (hRs x hx) (hRt y hy)

theorem Metric.Bounded.neg : Bounded s → Bounded (-s) := by
  simp_rw [bounded_iff_exists_norm_le, ← image_neg, ball_image_iff, norm_neg]
  exact id

theorem Metric.Bounded.sub (hs : Bounded s) (ht : Bounded t) : Bounded (s - t) :=
  (sub_eq_add_neg _ _).symm.subst <| hs.add ht.neg

section Emetric

open Emetric

theorem inf_edist_neg (x : E) (s : Set E) : infEdist (-x) s = infEdist x (-s) :=
  eq_of_forall_le_iff fun r => by
    simp_rw [le_inf_edist, ← image_neg, ball_image_iff, edist_neg]

@[simp]
theorem inf_edist_neg_neg (x : E) (s : Set E) : infEdist (-x) (-s) = infEdist x s := by
  rw [inf_edist_neg, neg_negₓ]

end Emetric

variable (ε δ s t x y)

@[simp]
theorem neg_thickening : -Thickening δ s = Thickening δ (-s) := by
  unfold thickening
  simp_rw [← inf_edist_neg]
  rfl

@[simp]
theorem neg_cthickening : -Cthickening δ s = Cthickening δ (-s) := by
  unfold cthickening
  simp_rw [← inf_edist_neg]
  rfl

@[simp]
theorem neg_ball : -Ball x δ = Ball (-x) δ := by
  unfold Metric.Ball
  simp_rw [← dist_neg]
  rfl

@[simp]
theorem neg_closed_ball : -ClosedBall x δ = ClosedBall (-x) δ := by
  unfold Metric.ClosedBall
  simp_rw [← dist_neg]
  rfl

theorem singleton_add_ball : {x} + Ball y δ = Ball (x + y) δ := by
  simp only [← preimage_add_ball, ← image_add_left, ← singleton_add, ← sub_neg_eq_add, ← add_commₓ y x]

theorem singleton_sub_ball : {x} - Ball y δ = Ball (x - y) δ := by
  simp_rw [sub_eq_add_neg, neg_ball, singleton_add_ball]

theorem ball_add_singleton : Ball x δ + {y} = Ball (x + y) δ := by
  rw [add_commₓ, singleton_add_ball, add_commₓ y]

theorem ball_sub_singleton : Ball x δ - {y} = Ball (x - y) δ := by
  simp_rw [sub_eq_add_neg, neg_singleton, ball_add_singleton]

theorem singleton_add_ball_zero : {x} + Ball 0 δ = Ball x δ := by
  simp

theorem singleton_sub_ball_zero : {x} - Ball 0 δ = Ball x δ := by
  simp [← singleton_sub_ball]

theorem ball_zero_add_singleton : Ball 0 δ + {x} = Ball x δ := by
  simp [← ball_add_singleton]

theorem ball_zero_sub_singleton : Ball 0 δ - {x} = Ball (-x) δ := by
  simp [← ball_sub_singleton]

theorem vadd_ball_zero : x +ᵥ Ball 0 δ = Ball x δ := by
  simp

@[simp]
theorem singleton_add_closed_ball : {x} + ClosedBall y δ = ClosedBall (x + y) δ := by
  simp only [← add_commₓ y x, ← preimage_add_closed_ball, ← image_add_left, ← singleton_add, ← sub_neg_eq_add]

@[simp]
theorem singleton_sub_closed_ball : {x} - ClosedBall y δ = ClosedBall (x - y) δ := by
  simp_rw [sub_eq_add_neg, neg_closed_ball, singleton_add_closed_ball]

@[simp]
theorem closed_ball_add_singleton : ClosedBall x δ + {y} = ClosedBall (x + y) δ := by
  simp [← add_commₓ _ {y}, ← add_commₓ y]

@[simp]
theorem closed_ball_sub_singleton : ClosedBall x δ - {y} = ClosedBall (x - y) δ := by
  simp [← sub_eq_add_neg]

theorem singleton_add_closed_ball_zero : {x} + ClosedBall 0 δ = ClosedBall x δ := by
  simp

theorem singleton_sub_closed_ball_zero : {x} - ClosedBall 0 δ = ClosedBall x δ := by
  simp

theorem closed_ball_zero_add_singleton : ClosedBall 0 δ + {x} = ClosedBall x δ := by
  simp

theorem closed_ball_zero_sub_singleton : ClosedBall 0 δ - {x} = ClosedBall (-x) δ := by
  simp

@[simp]
theorem vadd_closed_ball_zero : x +ᵥ ClosedBall 0 δ = ClosedBall x δ := by
  simp

theorem add_ball_zero : s + Ball 0 δ = Thickening δ s := by
  rw [thickening_eq_bUnion_ball]
  convert Union₂_add (fun x (_ : x ∈ s) => {x}) (ball (0 : E) δ)
  exact s.bUnion_of_singleton.symm
  ext x y
  simp_rw [singleton_add_ball, add_zeroₓ]

theorem sub_ball_zero : s - Ball 0 δ = Thickening δ s := by
  simp [← sub_eq_add_neg, ← add_ball_zero]

theorem ball_add_zero : Ball 0 δ + s = Thickening δ s := by
  rw [add_commₓ, add_ball_zero]

theorem ball_sub_zero : Ball 0 δ - s = Thickening δ (-s) := by
  simp [← sub_eq_add_neg, ← ball_add_zero]

@[simp]
theorem add_ball : s + Ball x δ = x +ᵥ Thickening δ s := by
  rw [← vadd_ball_zero, add_vadd_comm, add_ball_zero]

@[simp]
theorem sub_ball : s - Ball x δ = -x +ᵥ Thickening δ s := by
  simp [← sub_eq_add_neg]

@[simp]
theorem ball_add : Ball x δ + s = x +ᵥ Thickening δ s := by
  rw [add_commₓ, add_ball]

@[simp]
theorem ball_sub : Ball x δ - s = x +ᵥ Thickening δ (-s) := by
  simp [← sub_eq_add_neg]

variable {ε δ s t x y}

theorem IsCompact.add_closed_ball_zero (hs : IsCompact s) (hδ : 0 ≤ δ) : s + ClosedBall 0 δ = Cthickening δ s := by
  rw [hs.cthickening_eq_bUnion_closed_ball hδ]
  ext x
  simp only [← mem_add, ← dist_eq_norm, ← exists_prop, ← mem_Union, ← mem_closed_ball, ← exists_and_distrib_left, ←
    mem_closed_ball_zero_iff, eq_sub_iff_add_eq', ← exists_eq_right]

theorem IsCompact.sub_closed_ball_zero (hs : IsCompact s) (hδ : 0 ≤ δ) : s - ClosedBall 0 δ = Cthickening δ s := by
  simp [← sub_eq_add_neg, ← hs.add_closed_ball_zero hδ]

theorem IsCompact.closed_ball_zero_add (hs : IsCompact s) (hδ : 0 ≤ δ) : ClosedBall 0 δ + s = Cthickening δ s := by
  rw [add_commₓ, hs.add_closed_ball_zero hδ]

theorem IsCompact.closed_ball_zero_sub (hs : IsCompact s) (hδ : 0 ≤ δ) : ClosedBall 0 δ - s = Cthickening δ (-s) := by
  simp [← sub_eq_add_neg, ← add_commₓ, ← hs.neg.add_closed_ball_zero hδ]

theorem IsCompact.add_closed_ball (hs : IsCompact s) (hδ : 0 ≤ δ) (x : E) : s + ClosedBall x δ = x +ᵥ Cthickening δ s :=
  by
  rw [← vadd_closed_ball_zero, add_vadd_comm, hs.add_closed_ball_zero hδ]

theorem IsCompact.sub_closed_ball (hs : IsCompact s) (hδ : 0 ≤ δ) (x : E) :
    s - ClosedBall x δ = -x +ᵥ Cthickening δ s := by
  simp [← sub_eq_add_neg, ← add_commₓ, ← hs.add_closed_ball hδ]

theorem IsCompact.closed_ball_add (hs : IsCompact s) (hδ : 0 ≤ δ) (x : E) : ClosedBall x δ + s = x +ᵥ Cthickening δ s :=
  by
  rw [add_commₓ, hs.add_closed_ball hδ]

theorem IsCompact.closed_ball_sub (hs : IsCompact s) (hδ : 0 ≤ δ) (x : E) : ClosedBall x δ + s = x +ᵥ Cthickening δ s :=
  by
  simp [← sub_eq_add_neg, ← add_commₓ, ← hs.closed_ball_add hδ]

end SemiNormedGroup

