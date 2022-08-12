/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathbin.Analysis.SpecificLimits.Basic
import Mathbin.Topology.MetricSpace.Isometry
import Mathbin.Topology.Instances.Ennreal

/-!
# Hausdorff distance

The Hausdorff distance on subsets of a metric (or emetric) space.

Given two subsets `s` and `t` of a metric space, their Hausdorff distance is the smallest `d`
such that any point `s` is within `d` of a point in `t`, and conversely. This quantity
is often infinite (think of `s` bounded and `t` unbounded), and therefore better
expressed in the setting of emetric spaces.

## Main definitions

This files introduces:
* `inf_edist x s`, the infimum edistance of a point `x` to a set `s` in an emetric space
* `Hausdorff_edist s t`, the Hausdorff edistance of two sets in an emetric space
* Versions of these notions on metric spaces, called respectively `inf_dist` and `Hausdorff_dist`
* `thickening δ s`, the open thickening by radius `δ` of a set `s` in a pseudo emetric space.
* `cthickening δ s`, the closed thickening by radius `δ` of a set `s` in a pseudo emetric space.
-/


noncomputable section

open Classical Nnreal Ennreal TopologicalSpace

universe u v w

open Classical Set Function TopologicalSpace Filter

variable {ι : Sort _} {α : Type u} {β : Type v}

namespace Emetric

section InfEdist

variable [PseudoEmetricSpace α] [PseudoEmetricSpace β] {x y : α} {s t : Set α} {Φ : α → β}

/-! ### Distance of a point to a set as a function into `ℝ≥0∞`. -/


/-- The minimal edistance of a point to a set -/
def infEdist (x : α) (s : Set α) : ℝ≥0∞ :=
  ⨅ y ∈ s, edist x y

@[simp]
theorem inf_edist_empty : infEdist x ∅ = ∞ :=
  infi_emptyset

theorem le_inf_edist {d} : d ≤ infEdist x s ↔ ∀, ∀ y ∈ s, ∀, d ≤ edist x y := by
  simp only [← inf_edist, ← le_infi_iff]

/-- The edist to a union is the minimum of the edists -/
@[simp]
theorem inf_edist_union : infEdist x (s ∪ t) = infEdist x s⊓infEdist x t :=
  infi_union

@[simp]
theorem inf_edist_Union (f : ι → Set α) (x : α) : infEdist x (⋃ i, f i) = ⨅ i, infEdist x (f i) :=
  infi_Union f _

/-- The edist to a singleton is the edistance to the single point of this singleton -/
@[simp]
theorem inf_edist_singleton : infEdist x {y} = edist x y :=
  infi_singleton

/-- The edist to a set is bounded above by the edist to any of its points -/
theorem inf_edist_le_edist_of_mem (h : y ∈ s) : infEdist x s ≤ edist x y :=
  infi₂_le _ h

/-- If a point `x` belongs to `s`, then its edist to `s` vanishes -/
theorem inf_edist_zero_of_mem (h : x ∈ s) : infEdist x s = 0 :=
  nonpos_iff_eq_zero.1 <| @edist_self _ _ x ▸ inf_edist_le_edist_of_mem h

/-- The edist is antitone with respect to inclusion. -/
theorem inf_edist_anti (h : s ⊆ t) : infEdist x t ≤ infEdist x s :=
  infi_le_infi_of_subset h

/-- The edist to a set is `< r` iff there exists a point in the set at edistance `< r` -/
theorem inf_edist_lt_iff {r : ℝ≥0∞} : infEdist x s < r ↔ ∃ y ∈ s, edist x y < r := by
  simp_rw [inf_edist, infi_lt_iff]

/-- The edist of `x` to `s` is bounded by the sum of the edist of `y` to `s` and
the edist from `x` to `y` -/
theorem inf_edist_le_inf_edist_add_edist : infEdist x s ≤ infEdist y s + edist x y :=
  calc
    (⨅ z ∈ s, edist x z) ≤ ⨅ z ∈ s, edist y z + edist x y :=
      infi₂_mono fun z hz => (edist_triangle _ _ _).trans_eq (add_commₓ _ _)
    _ = (⨅ z ∈ s, edist y z) + edist x y := by
      simp only [← Ennreal.infi_add]
    

theorem inf_edist_le_edist_add_inf_edist : infEdist x s ≤ edist x y + infEdist y s := by
  rw [add_commₓ]
  exact inf_edist_le_inf_edist_add_edist

/-- The edist to a set depends continuously on the point -/
@[continuity]
theorem continuous_inf_edist : Continuous fun x => infEdist x s :=
  continuous_of_le_add_edist 1
      (by
        simp ) <|
    by
    simp only [← one_mulₓ, ← inf_edist_le_inf_edist_add_edist, ← forall_2_true_iff]

/-- The edist to a set and to its closure coincide -/
theorem inf_edist_closure : infEdist x (Closure s) = infEdist x s := by
  refine' le_antisymmₓ (inf_edist_anti subset_closure) _
  refine' Ennreal.le_of_forall_pos_le_add fun ε εpos h => _
  have ε0 : 0 < (ε / 2 : ℝ≥0∞) := by
    simpa [← pos_iff_ne_zero] using εpos
  have : inf_edist x (Closure s) < inf_edist x (Closure s) + ε / 2 := Ennreal.lt_add_right h.ne ε0.ne'
  rcases inf_edist_lt_iff.mp this with ⟨y, ycs, hy⟩
  -- y : α,  ycs : y ∈ closure s,  hy : edist x y < inf_edist x (closure s) + ↑ε / 2
  rcases Emetric.mem_closure_iff.1 ycs (ε / 2) ε0 with ⟨z, zs, dyz⟩
  -- z : α,  zs : z ∈ s,  dyz : edist y z < ↑ε / 2
  calc inf_edist x s ≤ edist x z := inf_edist_le_edist_of_mem zs _ ≤ edist x y + edist y z :=
      edist_triangle _ _ _ _ ≤ inf_edist x (Closure s) + ε / 2 + ε / 2 :=
      add_le_add (le_of_ltₓ hy) (le_of_ltₓ dyz)_ = inf_edist x (Closure s) + ↑ε := by
      rw [add_assocₓ, Ennreal.add_halves]

/-- A point belongs to the closure of `s` iff its infimum edistance to this set vanishes -/
theorem mem_closure_iff_inf_edist_zero : x ∈ Closure s ↔ infEdist x s = 0 :=
  ⟨fun h => by
    rw [← inf_edist_closure]
    exact inf_edist_zero_of_mem h, fun h =>
    Emetric.mem_closure_iff.2 fun ε εpos =>
      inf_edist_lt_iff.mp <| by
        rwa [h]⟩

/-- Given a closed set `s`, a point belongs to `s` iff its infimum edistance to this set vanishes -/
theorem mem_iff_inf_edist_zero_of_closed (h : IsClosed s) : x ∈ s ↔ infEdist x s = 0 := by
  convert ← mem_closure_iff_inf_edist_zero
  exact h.closure_eq

theorem disjoint_closed_ball_of_lt_inf_edist {r : ℝ≥0∞} (h : r < infEdist x s) : Disjoint (ClosedBall x r) s := by
  rw [disjoint_left]
  intro y hy h'y
  apply lt_irreflₓ (inf_edist x s)
  calc inf_edist x s ≤ edist x y := inf_edist_le_edist_of_mem h'y _ ≤ r := by
      rwa [mem_closed_ball, edist_comm] at hy _ < inf_edist x s := h

/-- The infimum edistance is invariant under isometries -/
theorem inf_edist_image (hΦ : Isometry Φ) : infEdist (Φ x) (Φ '' t) = infEdist x t := by
  simp only [← inf_edist, ← infi_image, ← hΦ.edist_eq]

theorem _root_.is_open.exists_Union_is_closed {U : Set α} (hU : IsOpen U) :
    ∃ F : ℕ → Set α, (∀ n, IsClosed (F n)) ∧ (∀ n, F n ⊆ U) ∧ (⋃ n, F n) = U ∧ Monotone F := by
  obtain ⟨a, a_pos, a_lt_one⟩ : ∃ a : ℝ≥0∞, 0 < a ∧ a < 1 := exists_between Ennreal.zero_lt_one
  let F := fun n : ℕ => (fun x => inf_edist x (Uᶜ)) ⁻¹' Ici (a ^ n)
  have F_subset : ∀ n, F n ⊆ U := by
    intro n x hx
    have : inf_edist x (Uᶜ) ≠ 0 := ((Ennreal.pow_pos a_pos _).trans_le hx).ne'
    contrapose! this
    exact inf_edist_zero_of_mem this
  refine' ⟨F, fun n => IsClosed.preimage continuous_inf_edist is_closed_Ici, F_subset, _, _⟩
  show Monotone F
  · intro m n hmn x hx
    simp only [← mem_Ici, ← mem_preimage] at hx⊢
    apply le_transₓ (Ennreal.pow_le_pow_of_le_one a_lt_one.le hmn) hx
    
  show (⋃ n, F n) = U
  · refine'
      subset.antisymm
        (by
          simp only [← Union_subset_iff, ← F_subset, ← forall_const])
        fun x hx => _
    have : ¬x ∈ Uᶜ := by
      simpa using hx
    rw [mem_iff_inf_edist_zero_of_closed hU.is_closed_compl] at this
    have B : 0 < inf_edist x (Uᶜ) := by
      simpa [← pos_iff_ne_zero] using this
    have : Filter.Tendsto (fun n => a ^ n) at_top (𝓝 0) := Ennreal.tendsto_pow_at_top_nhds_0_of_lt_1 a_lt_one
    rcases((tendsto_order.1 this).2 _ B).exists with ⟨n, hn⟩
    simp only [← mem_Union, ← mem_Ici, ← mem_preimage]
    exact ⟨n, hn.le⟩
    

theorem _root_.is_compact.exists_inf_edist_eq_edist (hs : IsCompact s) (hne : s.Nonempty) (x : α) :
    ∃ y ∈ s, infEdist x s = edist x y := by
  have A : Continuous fun y => edist x y := continuous_const.edist continuous_id
  obtain ⟨y, ys, hy⟩ : ∃ y ∈ s, ∀ z, z ∈ s → edist x y ≤ edist x z := hs.exists_forall_le hne A.continuous_on
  exact
    ⟨y, ys,
      le_antisymmₓ (inf_edist_le_edist_of_mem ys)
        (by
          rwa [le_inf_edist])⟩

theorem exists_pos_forall_le_edist (hs : IsCompact s) (hs' : s.Nonempty) (ht : IsClosed t) (hst : Disjoint s t) :
    ∃ r, 0 < r ∧ ∀, ∀ x ∈ s, ∀, ∀ y ∈ t, ∀, r ≤ edist x y := by
  obtain ⟨x, hx, h⟩ : ∃ x ∈ s, ∀, ∀ y ∈ s, ∀, inf_edist x t ≤ inf_edist y t :=
    hs.exists_forall_le hs' continuous_inf_edist.continuous_on
  refine' ⟨inf_edist x t, pos_iff_ne_zero.2 fun H => hst ⟨hx, _⟩, fun y hy => le_inf_edist.1 <| h y hy⟩
  rw [← ht.closure_eq]
  exact mem_closure_iff_inf_edist_zero.2 H

end InfEdist

/-! ### The Hausdorff distance as a function into `ℝ≥0∞`. -/


/-- The Hausdorff edistance between two sets is the smallest `r` such that each set
is contained in the `r`-neighborhood of the other one -/
--section
irreducible_def hausdorffEdist {α : Type u} [PseudoEmetricSpace α] (s t : Set α) : ℝ≥0∞ :=
  (⨆ x ∈ s, infEdist x t)⊔⨆ y ∈ t, infEdist y s

theorem Hausdorff_edist_def {α : Type u} [PseudoEmetricSpace α] (s t : Set α) :
    hausdorffEdist s t = (⨆ x ∈ s, infEdist x t)⊔⨆ y ∈ t, infEdist y s := by
  rw [Hausdorff_edist]

section HausdorffEdist

variable [PseudoEmetricSpace α] [PseudoEmetricSpace β] {x y : α} {s t u : Set α} {Φ : α → β}

/-- The Hausdorff edistance of a set to itself vanishes -/
@[simp]
theorem Hausdorff_edist_self : hausdorffEdist s s = 0 := by
  simp only [← Hausdorff_edist_def, ← sup_idem, ← Ennreal.supr_eq_zero]
  exact fun x hx => inf_edist_zero_of_mem hx

/-- The Haudorff edistances of `s` to `t` and of `t` to `s` coincide -/
theorem Hausdorff_edist_comm : hausdorffEdist s t = hausdorffEdist t s := by
  unfold Hausdorff_edist <;> apply sup_comm

/-- Bounding the Hausdorff edistance by bounding the edistance of any point
in each set to the other set -/
theorem Hausdorff_edist_le_of_inf_edist {r : ℝ≥0∞} (H1 : ∀, ∀ x ∈ s, ∀, infEdist x t ≤ r)
    (H2 : ∀, ∀ x ∈ t, ∀, infEdist x s ≤ r) : hausdorffEdist s t ≤ r := by
  simp only [← Hausdorff_edist, ← sup_le_iff, ← supr_le_iff]
  exact ⟨H1, H2⟩

/-- Bounding the Hausdorff edistance by exhibiting, for any point in each set,
another point in the other set at controlled distance -/
theorem Hausdorff_edist_le_of_mem_edist {r : ℝ≥0∞} (H1 : ∀, ∀ x ∈ s, ∀, ∃ y ∈ t, edist x y ≤ r)
    (H2 : ∀, ∀ x ∈ t, ∀, ∃ y ∈ s, edist x y ≤ r) : hausdorffEdist s t ≤ r := by
  refine' Hausdorff_edist_le_of_inf_edist _ _
  · intro x xs
    rcases H1 x xs with ⟨y, yt, hy⟩
    exact le_transₓ (inf_edist_le_edist_of_mem yt) hy
    
  · intro x xt
    rcases H2 x xt with ⟨y, ys, hy⟩
    exact le_transₓ (inf_edist_le_edist_of_mem ys) hy
    

/-- The distance to a set is controlled by the Hausdorff distance -/
theorem inf_edist_le_Hausdorff_edist_of_mem (h : x ∈ s) : infEdist x t ≤ hausdorffEdist s t := by
  rw [Hausdorff_edist_def]
  refine' le_transₓ _ le_sup_left
  exact le_supr₂ x h

/-- If the Hausdorff distance is `<r`, then any point in one of the sets has
a corresponding point at distance `<r` in the other set -/
theorem exists_edist_lt_of_Hausdorff_edist_lt {r : ℝ≥0∞} (h : x ∈ s) (H : hausdorffEdist s t < r) :
    ∃ y ∈ t, edist x y < r :=
  inf_edist_lt_iff.mp <|
    calc
      infEdist x t ≤ hausdorffEdist s t := inf_edist_le_Hausdorff_edist_of_mem h
      _ < r := H
      

/-- The distance from `x` to `s` or `t` is controlled in terms of the Hausdorff distance
between `s` and `t` -/
theorem inf_edist_le_inf_edist_add_Hausdorff_edist : infEdist x t ≤ infEdist x s + hausdorffEdist s t :=
  Ennreal.le_of_forall_pos_le_add fun ε εpos h => by
    have ε0 : (ε / 2 : ℝ≥0∞) ≠ 0 := by
      simpa [← pos_iff_ne_zero] using εpos
    have : inf_edist x s < inf_edist x s + ε / 2 := Ennreal.lt_add_right (Ennreal.add_lt_top.1 h).1.Ne ε0
    rcases inf_edist_lt_iff.mp this with ⟨y, ys, dxy⟩
    -- y : α,  ys : y ∈ s,  dxy : edist x y < inf_edist x s + ↑ε / 2
    have : Hausdorff_edist s t < Hausdorff_edist s t + ε / 2 := Ennreal.lt_add_right (Ennreal.add_lt_top.1 h).2.Ne ε0
    rcases exists_edist_lt_of_Hausdorff_edist_lt ys this with ⟨z, zt, dyz⟩
    -- z : α,  zt : z ∈ t,  dyz : edist y z < Hausdorff_edist s t + ↑ε / 2
    calc inf_edist x t ≤ edist x z := inf_edist_le_edist_of_mem zt _ ≤ edist x y + edist y z :=
        edist_triangle _ _ _ _ ≤ inf_edist x s + ε / 2 + (Hausdorff_edist s t + ε / 2) :=
        add_le_add dxy.le dyz.le _ = inf_edist x s + Hausdorff_edist s t + ε := by
        simp [← Ennreal.add_halves, ← add_commₓ, ← add_left_commₓ]

/-- The Hausdorff edistance is invariant under eisometries -/
theorem Hausdorff_edist_image (h : Isometry Φ) : hausdorffEdist (Φ '' s) (Φ '' t) = hausdorffEdist s t := by
  simp only [← Hausdorff_edist_def, ← supr_image, ← inf_edist_image h]

/-- The Hausdorff distance is controlled by the diameter of the union -/
theorem Hausdorff_edist_le_ediam (hs : s.Nonempty) (ht : t.Nonempty) : hausdorffEdist s t ≤ diam (s ∪ t) := by
  rcases hs with ⟨x, xs⟩
  rcases ht with ⟨y, yt⟩
  refine' Hausdorff_edist_le_of_mem_edist _ _
  · intro z hz
    exact ⟨y, yt, edist_le_diam_of_mem (subset_union_left _ _ hz) (subset_union_right _ _ yt)⟩
    
  · intro z hz
    exact ⟨x, xs, edist_le_diam_of_mem (subset_union_right _ _ hz) (subset_union_left _ _ xs)⟩
    

/-- The Hausdorff distance satisfies the triangular inequality -/
theorem Hausdorff_edist_triangle : hausdorffEdist s u ≤ hausdorffEdist s t + hausdorffEdist t u := by
  rw [Hausdorff_edist_def]
  simp only [← sup_le_iff, ← supr_le_iff]
  constructor
  show ∀, ∀ x ∈ s, ∀, inf_edist x u ≤ Hausdorff_edist s t + Hausdorff_edist t u
  exact fun x xs =>
    calc
      inf_edist x u ≤ inf_edist x t + Hausdorff_edist t u := inf_edist_le_inf_edist_add_Hausdorff_edist
      _ ≤ Hausdorff_edist s t + Hausdorff_edist t u := add_le_add_right (inf_edist_le_Hausdorff_edist_of_mem xs) _
      
  show ∀, ∀ x ∈ u, ∀, inf_edist x s ≤ Hausdorff_edist s t + Hausdorff_edist t u
  exact fun x xu =>
    calc
      inf_edist x s ≤ inf_edist x t + Hausdorff_edist t s := inf_edist_le_inf_edist_add_Hausdorff_edist
      _ ≤ Hausdorff_edist u t + Hausdorff_edist t s := add_le_add_right (inf_edist_le_Hausdorff_edist_of_mem xu) _
      _ = Hausdorff_edist s t + Hausdorff_edist t u := by
        simp [← Hausdorff_edist_comm, ← add_commₓ]
      

/-- Two sets are at zero Hausdorff edistance if and only if they have the same closure -/
theorem Hausdorff_edist_zero_iff_closure_eq_closure : hausdorffEdist s t = 0 ↔ Closure s = Closure t :=
  calc
    hausdorffEdist s t = 0 ↔ s ⊆ Closure t ∧ t ⊆ Closure s := by
      simp only [← Hausdorff_edist_def, ← Ennreal.sup_eq_zero, ← Ennreal.supr_eq_zero, mem_closure_iff_inf_edist_zero, ←
        subset_def]
    _ ↔ Closure s = Closure t :=
      ⟨fun h => Subset.antisymm (closure_minimal h.1 is_closed_closure) (closure_minimal h.2 is_closed_closure),
        fun h => ⟨h ▸ subset_closure, h.symm ▸ subset_closure⟩⟩
    

/-- The Hausdorff edistance between a set and its closure vanishes -/
@[simp]
theorem Hausdorff_edist_self_closure : hausdorffEdist s (Closure s) = 0 := by
  rw [Hausdorff_edist_zero_iff_closure_eq_closure, closure_closure]

/-- Replacing a set by its closure does not change the Hausdorff edistance. -/
@[simp]
theorem Hausdorff_edist_closure₁ : hausdorffEdist (Closure s) t = hausdorffEdist s t := by
  refine' le_antisymmₓ _ _
  · calc _ ≤ Hausdorff_edist (Closure s) s + Hausdorff_edist s t := Hausdorff_edist_triangle _ = Hausdorff_edist s t :=
        by
        simp [← Hausdorff_edist_comm]
    
  · calc _ ≤ Hausdorff_edist s (Closure s) + Hausdorff_edist (Closure s) t :=
        Hausdorff_edist_triangle _ = Hausdorff_edist (Closure s) t := by
        simp
    

/-- Replacing a set by its closure does not change the Hausdorff edistance. -/
@[simp]
theorem Hausdorff_edist_closure₂ : hausdorffEdist s (Closure t) = hausdorffEdist s t := by
  simp [← @Hausdorff_edist_comm _ _ s _]

/-- The Hausdorff edistance between sets or their closures is the same -/
@[simp]
theorem Hausdorff_edist_closure : hausdorffEdist (Closure s) (Closure t) = hausdorffEdist s t := by
  simp

/-- Two closed sets are at zero Hausdorff edistance if and only if they coincide -/
theorem Hausdorff_edist_zero_iff_eq_of_closed (hs : IsClosed s) (ht : IsClosed t) : hausdorffEdist s t = 0 ↔ s = t := by
  rw [Hausdorff_edist_zero_iff_closure_eq_closure, hs.closure_eq, ht.closure_eq]

/-- The Haudorff edistance to the empty set is infinite -/
theorem Hausdorff_edist_empty (ne : s.Nonempty) : hausdorffEdist s ∅ = ∞ := by
  rcases Ne with ⟨x, xs⟩
  have : inf_edist x ∅ ≤ Hausdorff_edist s ∅ := inf_edist_le_Hausdorff_edist_of_mem xs
  simpa using this

/-- If a set is at finite Hausdorff edistance of a nonempty set, it is nonempty -/
theorem nonempty_of_Hausdorff_edist_ne_top (hs : s.Nonempty) (fin : hausdorffEdist s t ≠ ⊤) : t.Nonempty :=
  t.eq_empty_or_nonempty.elim (fun ht => (Finₓ <| ht.symm ▸ Hausdorff_edist_empty hs).elim) id

theorem empty_or_nonempty_of_Hausdorff_edist_ne_top (fin : hausdorffEdist s t ≠ ⊤) :
    s = ∅ ∧ t = ∅ ∨ s.Nonempty ∧ t.Nonempty := by
  cases' s.eq_empty_or_nonempty with hs hs
  · cases' t.eq_empty_or_nonempty with ht ht
    · exact Or.inl ⟨hs, ht⟩
      
    · rw [Hausdorff_edist_comm] at fin
      exact Or.inr ⟨nonempty_of_Hausdorff_edist_ne_top ht Finₓ, ht⟩
      
    
  · exact Or.inr ⟨hs, nonempty_of_Hausdorff_edist_ne_top hs Finₓ⟩
    

end HausdorffEdist

-- section
end Emetric

/-! Now, we turn to the same notions in metric spaces. To avoid the difficulties related to
`Inf` and `Sup` on `ℝ` (which is only conditionally complete), we use the notions in `ℝ≥0∞`
formulated in terms of the edistance, and coerce them to `ℝ`.
Then their properties follow readily from the corresponding properties in `ℝ≥0∞`,
modulo some tedious rewriting of inequalities from one to the other. -/


--namespace
namespace Metric

section

variable [PseudoMetricSpace α] [PseudoMetricSpace β] {s t u : Set α} {x y : α} {Φ : α → β}

open Emetric

/-! ### Distance of a point to a set as a function into `ℝ`. -/


/-- The minimal distance of a point to a set -/
def infDist (x : α) (s : Set α) : ℝ :=
  Ennreal.toReal (infEdist x s)

/-- the minimal distance is always nonnegative -/
theorem inf_dist_nonneg : 0 ≤ infDist x s := by
  simp [← inf_dist]

/-- the minimal distance to the empty set is 0 (if you want to have the more reasonable
value ∞ instead, use `inf_edist`, which takes values in ℝ≥0∞) -/
@[simp]
theorem inf_dist_empty : infDist x ∅ = 0 := by
  simp [← inf_dist]

/-- In a metric space, the minimal edistance to a nonempty set is finite -/
theorem inf_edist_ne_top (h : s.Nonempty) : infEdist x s ≠ ⊤ := by
  rcases h with ⟨y, hy⟩
  apply lt_top_iff_ne_top.1
  calc inf_edist x s ≤ edist x y := inf_edist_le_edist_of_mem hy _ < ⊤ := lt_top_iff_ne_top.2 (edist_ne_top _ _)

/-- The minimal distance of a point to a set containing it vanishes -/
theorem inf_dist_zero_of_mem (h : x ∈ s) : infDist x s = 0 := by
  simp [← inf_edist_zero_of_mem h, ← inf_dist]

/-- The minimal distance to a singleton is the distance to the unique point in this singleton -/
@[simp]
theorem inf_dist_singleton : infDist x {y} = dist x y := by
  simp [← inf_dist, ← inf_edist, ← dist_edist]

/-- The minimal distance to a set is bounded by the distance to any point in this set -/
theorem inf_dist_le_dist_of_mem (h : y ∈ s) : infDist x s ≤ dist x y := by
  rw [dist_edist, inf_dist, Ennreal.to_real_le_to_real (inf_edist_ne_top ⟨_, h⟩) (edist_ne_top _ _)]
  exact inf_edist_le_edist_of_mem h

/-- The minimal distance is monotonous with respect to inclusion -/
theorem inf_dist_le_inf_dist_of_subset (h : s ⊆ t) (hs : s.Nonempty) : infDist x t ≤ infDist x s := by
  have ht : t.nonempty := hs.mono h
  rw [inf_dist, inf_dist, Ennreal.to_real_le_to_real (inf_edist_ne_top ht) (inf_edist_ne_top hs)]
  exact inf_edist_anti h

/-- The minimal distance to a set is `< r` iff there exists a point in this set at distance `< r` -/
theorem inf_dist_lt_iff {r : ℝ} (hs : s.Nonempty) : infDist x s < r ↔ ∃ y ∈ s, dist x y < r := by
  simp_rw [inf_dist, ← Ennreal.lt_of_real_iff_to_real_lt (inf_edist_ne_top hs), inf_edist_lt_iff,
    Ennreal.lt_of_real_iff_to_real_lt (edist_ne_top _ _), ← dist_edist]

/-- The minimal distance from `x` to `s` is bounded by the distance from `y` to `s`, modulo
the distance between `x` and `y` -/
theorem inf_dist_le_inf_dist_add_dist : infDist x s ≤ infDist y s + dist x y := by
  cases' s.eq_empty_or_nonempty with hs hs
  · simp [← hs, ← dist_nonneg]
    
  · rw [inf_dist, inf_dist, dist_edist, ← Ennreal.to_real_add (inf_edist_ne_top hs) (edist_ne_top _ _),
      Ennreal.to_real_le_to_real (inf_edist_ne_top hs)]
    · exact inf_edist_le_inf_edist_add_edist
      
    · simp [← Ennreal.add_eq_top, ← inf_edist_ne_top hs, ← edist_ne_top]
      
    

theorem not_mem_of_dist_lt_inf_dist (h : dist x y < infDist x s) : y ∉ s := fun hy =>
  h.not_le <| inf_dist_le_dist_of_mem hy

theorem disjoint_ball_inf_dist : Disjoint (Ball x (infDist x s)) s :=
  disjoint_left.2 fun y hy =>
    not_mem_of_dist_lt_inf_dist <|
      calc
        dist x y = dist y x := dist_comm _ _
        _ < infDist x s := hy
        

theorem ball_inf_dist_subset_compl : Ball x (infDist x s) ⊆ sᶜ :=
  disjoint_ball_inf_dist.subset_compl_right

theorem ball_inf_dist_compl_subset : Ball x (infDist x (sᶜ)) ⊆ s :=
  ball_inf_dist_subset_compl.trans (compl_compl s).Subset

theorem disjoint_closed_ball_of_lt_inf_dist {r : ℝ} (h : r < infDist x s) : Disjoint (ClosedBall x r) s :=
  disjoint_ball_inf_dist.mono_left <| closed_ball_subset_ball h

variable (s)

/-- The minimal distance to a set is Lipschitz in point with constant 1 -/
theorem lipschitz_inf_dist_pt : LipschitzWith 1 fun x => infDist x s :=
  LipschitzWith.of_le_add fun x y => inf_dist_le_inf_dist_add_dist

/-- The minimal distance to a set is uniformly continuous in point -/
theorem uniform_continuous_inf_dist_pt : UniformContinuous fun x => infDist x s :=
  (lipschitz_inf_dist_pt s).UniformContinuous

/-- The minimal distance to a set is continuous in point -/
@[continuity]
theorem continuous_inf_dist_pt : Continuous fun x => infDist x s :=
  (uniform_continuous_inf_dist_pt s).Continuous

variable {s}

/-- The minimal distance to a set and its closure coincide -/
theorem inf_dist_eq_closure : infDist x (Closure s) = infDist x s := by
  simp [← inf_dist, ← inf_edist_closure]

/-- If a point belongs to the closure of `s`, then its infimum distance to `s` equals zero.
The converse is true provided that `s` is nonempty, see `mem_closure_iff_inf_dist_zero`. -/
theorem inf_dist_zero_of_mem_closure (hx : x ∈ Closure s) : infDist x s = 0 := by
  rw [← inf_dist_eq_closure]
  exact inf_dist_zero_of_mem hx

/-- A point belongs to the closure of `s` iff its infimum distance to this set vanishes -/
theorem mem_closure_iff_inf_dist_zero (h : s.Nonempty) : x ∈ Closure s ↔ infDist x s = 0 := by
  simp [← mem_closure_iff_inf_edist_zero, ← inf_dist, ← Ennreal.to_real_eq_zero_iff, ← inf_edist_ne_top h]

/-- Given a closed set `s`, a point belongs to `s` iff its infimum distance to this set vanishes -/
theorem _root_.is_closed.mem_iff_inf_dist_zero (h : IsClosed s) (hs : s.Nonempty) : x ∈ s ↔ infDist x s = 0 := by
  rw [← mem_closure_iff_inf_dist_zero hs, h.closure_eq]

/-- Given a closed set `s`, a point belongs to `s` iff its infimum distance to this set vanishes -/
theorem _root_.is_closed.not_mem_iff_inf_dist_pos (h : IsClosed s) (hs : s.Nonempty) : x ∉ s ↔ 0 < infDist x s := by
  rw [← not_iff_not]
  push_neg
  simp [← h.mem_iff_inf_dist_zero hs, ← le_antisymm_iffₓ, ← inf_dist_nonneg]

/-- The infimum distance is invariant under isometries -/
theorem inf_dist_image (hΦ : Isometry Φ) : infDist (Φ x) (Φ '' t) = infDist x t := by
  simp [← inf_dist, ← inf_edist_image hΦ]

theorem inf_dist_inter_closed_ball_of_mem (h : y ∈ s) : infDist x (s ∩ ClosedBall x (dist y x)) = infDist x s := by
  replace h : y ∈ s ∩ closed_ball x (dist y x) := ⟨h, mem_closed_ball.2 le_rfl⟩
  refine' le_antisymmₓ _ (inf_dist_le_inf_dist_of_subset (inter_subset_left _ _) ⟨y, h⟩)
  refine' not_ltₓ.1 fun hlt => _
  rcases(inf_dist_lt_iff ⟨y, h.1⟩).mp hlt with ⟨z, hzs, hz⟩
  cases' le_or_ltₓ (dist z x) (dist y x) with hle hlt
  · exact hz.not_le (inf_dist_le_dist_of_mem ⟨hzs, hle⟩)
    
  · rw [dist_comm z, dist_comm y] at hlt
    exact (hlt.trans hz).not_le (inf_dist_le_dist_of_mem h)
    

theorem _root_.is_compact.exists_inf_dist_eq_dist (h : IsCompact s) (hne : s.Nonempty) (x : α) :
    ∃ y ∈ s, infDist x s = dist x y :=
  let ⟨y, hys, hy⟩ := h.exists_inf_edist_eq_edist hne x
  ⟨y, hys, by
    rw [inf_dist, dist_edist, hy]⟩

theorem _root_.is_closed.exists_inf_dist_eq_dist [ProperSpace α] (h : IsClosed s) (hne : s.Nonempty) (x : α) :
    ∃ y ∈ s, infDist x s = dist x y := by
  rcases hne with ⟨z, hz⟩
  rw [← inf_dist_inter_closed_ball_of_mem hz]
  set t := s ∩ closed_ball x (dist z x)
  have htc : IsCompact t := (is_compact_closed_ball x (dist z x)).inter_left h
  have htne : t.nonempty := ⟨z, hz, mem_closed_ball.2 le_rfl⟩
  obtain ⟨y, ⟨hys, hyx⟩, hyd⟩ : ∃ y ∈ t, inf_dist x t = dist x y := htc.exists_inf_dist_eq_dist htne x
  exact ⟨y, hys, hyd⟩

theorem exists_mem_closure_inf_dist_eq_dist [ProperSpace α] (hne : s.Nonempty) (x : α) :
    ∃ y ∈ Closure s, infDist x s = dist x y := by
  simpa only [← inf_dist_eq_closure] using is_closed_closure.exists_inf_dist_eq_dist hne.closure x

/-! ### Distance of a point to a set as a function into `ℝ≥0`. -/


/-- The minimal distance of a point to a set as a `ℝ≥0` -/
def infNndist (x : α) (s : Set α) : ℝ≥0 :=
  Ennreal.toNnreal (infEdist x s)

@[simp]
theorem coe_inf_nndist : (infNndist x s : ℝ) = infDist x s :=
  rfl

/-- The minimal distance to a set (as `ℝ≥0`) is Lipschitz in point with constant 1 -/
theorem lipschitz_inf_nndist_pt (s : Set α) : LipschitzWith 1 fun x => infNndist x s :=
  LipschitzWith.of_le_add fun x y => inf_dist_le_inf_dist_add_dist

/-- The minimal distance to a set (as `ℝ≥0`) is uniformly continuous in point -/
theorem uniform_continuous_inf_nndist_pt (s : Set α) : UniformContinuous fun x => infNndist x s :=
  (lipschitz_inf_nndist_pt s).UniformContinuous

/-- The minimal distance to a set (as `ℝ≥0`) is continuous in point -/
theorem continuous_inf_nndist_pt (s : Set α) : Continuous fun x => infNndist x s :=
  (uniform_continuous_inf_nndist_pt s).Continuous

/-! ### The Hausdorff distance as a function into `ℝ`. -/


/-- The Hausdorff distance between two sets is the smallest nonnegative `r` such that each set is
included in the `r`-neighborhood of the other. If there is no such `r`, it is defined to
be `0`, arbitrarily -/
def hausdorffDist (s t : Set α) : ℝ :=
  Ennreal.toReal (hausdorffEdist s t)

/-- The Hausdorff distance is nonnegative -/
theorem Hausdorff_dist_nonneg : 0 ≤ hausdorffDist s t := by
  simp [← Hausdorff_dist]

/-- If two sets are nonempty and bounded in a metric space, they are at finite Hausdorff
edistance. -/
theorem Hausdorff_edist_ne_top_of_nonempty_of_bounded (hs : s.Nonempty) (ht : t.Nonempty) (bs : Bounded s)
    (bt : Bounded t) : hausdorffEdist s t ≠ ⊤ := by
  rcases hs with ⟨cs, hcs⟩
  rcases ht with ⟨ct, hct⟩
  rcases(bounded_iff_subset_ball ct).1 bs with ⟨rs, hrs⟩
  rcases(bounded_iff_subset_ball cs).1 bt with ⟨rt, hrt⟩
  have : Hausdorff_edist s t ≤ Ennreal.ofReal (max rs rt) := by
    apply Hausdorff_edist_le_of_mem_edist
    · intro x xs
      exists ct, hct
      have : dist x ct ≤ max rs rt := le_transₓ (hrs xs) (le_max_leftₓ _ _)
      rwa [edist_dist, Ennreal.of_real_le_of_real_iff]
      exact le_transₓ dist_nonneg this
      
    · intro x xt
      exists cs, hcs
      have : dist x cs ≤ max rs rt := le_transₓ (hrt xt) (le_max_rightₓ _ _)
      rwa [edist_dist, Ennreal.of_real_le_of_real_iff]
      exact le_transₓ dist_nonneg this
      
  exact ne_top_of_le_ne_top Ennreal.of_real_ne_top this

/-- The Hausdorff distance between a set and itself is zero -/
@[simp]
theorem Hausdorff_dist_self_zero : hausdorffDist s s = 0 := by
  simp [← Hausdorff_dist]

/-- The Hausdorff distance from `s` to `t` and from `t` to `s` coincide -/
theorem Hausdorff_dist_comm : hausdorffDist s t = hausdorffDist t s := by
  simp [← Hausdorff_dist, ← Hausdorff_edist_comm]

/-- The Hausdorff distance to the empty set vanishes (if you want to have the more reasonable
value ∞ instead, use `Hausdorff_edist`, which takes values in ℝ≥0∞) -/
@[simp]
theorem Hausdorff_dist_empty : hausdorffDist s ∅ = 0 := by
  cases' s.eq_empty_or_nonempty with h h
  · simp [← h]
    
  · simp [← Hausdorff_dist, ← Hausdorff_edist_empty h]
    

/-- The Hausdorff distance to the empty set vanishes (if you want to have the more reasonable
value ∞ instead, use `Hausdorff_edist`, which takes values in ℝ≥0∞) -/
@[simp]
theorem Hausdorff_dist_empty' : hausdorffDist ∅ s = 0 := by
  simp [← Hausdorff_dist_comm]

/-- Bounding the Hausdorff distance by bounding the distance of any point
in each set to the other set -/
theorem Hausdorff_dist_le_of_inf_dist {r : ℝ} (hr : 0 ≤ r) (H1 : ∀, ∀ x ∈ s, ∀, infDist x t ≤ r)
    (H2 : ∀, ∀ x ∈ t, ∀, infDist x s ≤ r) : hausdorffDist s t ≤ r := by
  by_cases' h1 : Hausdorff_edist s t = ⊤
  · rwa [Hausdorff_dist, h1, Ennreal.top_to_real]
    
  cases' s.eq_empty_or_nonempty with hs hs
  · rwa [hs, Hausdorff_dist_empty']
    
  cases' t.eq_empty_or_nonempty with ht ht
  · rwa [ht, Hausdorff_dist_empty]
    
  have : Hausdorff_edist s t ≤ Ennreal.ofReal r := by
    apply Hausdorff_edist_le_of_inf_edist _ _
    · intro x hx
      have I := H1 x hx
      rwa [inf_dist, ← Ennreal.to_real_of_real hr,
        Ennreal.to_real_le_to_real (inf_edist_ne_top ht) Ennreal.of_real_ne_top] at I
      
    · intro x hx
      have I := H2 x hx
      rwa [inf_dist, ← Ennreal.to_real_of_real hr,
        Ennreal.to_real_le_to_real (inf_edist_ne_top hs) Ennreal.of_real_ne_top] at I
      
  rwa [Hausdorff_dist, ← Ennreal.to_real_of_real hr, Ennreal.to_real_le_to_real h1 Ennreal.of_real_ne_top]

/-- Bounding the Hausdorff distance by exhibiting, for any point in each set,
another point in the other set at controlled distance -/
theorem Hausdorff_dist_le_of_mem_dist {r : ℝ} (hr : 0 ≤ r) (H1 : ∀, ∀ x ∈ s, ∀, ∃ y ∈ t, dist x y ≤ r)
    (H2 : ∀, ∀ x ∈ t, ∀, ∃ y ∈ s, dist x y ≤ r) : hausdorffDist s t ≤ r := by
  apply Hausdorff_dist_le_of_inf_dist hr
  · intro x xs
    rcases H1 x xs with ⟨y, yt, hy⟩
    exact le_transₓ (inf_dist_le_dist_of_mem yt) hy
    
  · intro x xt
    rcases H2 x xt with ⟨y, ys, hy⟩
    exact le_transₓ (inf_dist_le_dist_of_mem ys) hy
    

/-- The Hausdorff distance is controlled by the diameter of the union -/
theorem Hausdorff_dist_le_diam (hs : s.Nonempty) (bs : Bounded s) (ht : t.Nonempty) (bt : Bounded t) :
    hausdorffDist s t ≤ diam (s ∪ t) := by
  rcases hs with ⟨x, xs⟩
  rcases ht with ⟨y, yt⟩
  refine' Hausdorff_dist_le_of_mem_dist diam_nonneg _ _
  · exact fun z hz =>
      ⟨y, yt, dist_le_diam_of_mem (bounded_union.2 ⟨bs, bt⟩) (subset_union_left _ _ hz) (subset_union_right _ _ yt)⟩
    
  · exact fun z hz =>
      ⟨x, xs, dist_le_diam_of_mem (bounded_union.2 ⟨bs, bt⟩) (subset_union_right _ _ hz) (subset_union_left _ _ xs)⟩
    

/-- The distance to a set is controlled by the Hausdorff distance -/
theorem inf_dist_le_Hausdorff_dist_of_mem (hx : x ∈ s) (fin : hausdorffEdist s t ≠ ⊤) :
    infDist x t ≤ hausdorffDist s t := by
  have ht : t.nonempty := nonempty_of_Hausdorff_edist_ne_top ⟨x, hx⟩ Finₓ
  rw [Hausdorff_dist, inf_dist, Ennreal.to_real_le_to_real (inf_edist_ne_top ht) Finₓ]
  exact inf_edist_le_Hausdorff_edist_of_mem hx

/-- If the Hausdorff distance is `<r`, then any point in one of the sets is at distance
`<r` of a point in the other set -/
theorem exists_dist_lt_of_Hausdorff_dist_lt {r : ℝ} (h : x ∈ s) (H : hausdorffDist s t < r)
    (fin : hausdorffEdist s t ≠ ⊤) : ∃ y ∈ t, dist x y < r := by
  have r0 : 0 < r := lt_of_le_of_ltₓ Hausdorff_dist_nonneg H
  have : Hausdorff_edist s t < Ennreal.ofReal r := by
    rwa [Hausdorff_dist, ← Ennreal.to_real_of_real (le_of_ltₓ r0),
      Ennreal.to_real_lt_to_real Finₓ Ennreal.of_real_ne_top] at H
  rcases exists_edist_lt_of_Hausdorff_edist_lt h this with ⟨y, hy, yr⟩
  rw [edist_dist, Ennreal.of_real_lt_of_real_iff r0] at yr
  exact ⟨y, hy, yr⟩

/-- If the Hausdorff distance is `<r`, then any point in one of the sets is at distance
`<r` of a point in the other set -/
theorem exists_dist_lt_of_Hausdorff_dist_lt' {r : ℝ} (h : y ∈ t) (H : hausdorffDist s t < r)
    (fin : hausdorffEdist s t ≠ ⊤) : ∃ x ∈ s, dist x y < r := by
  rw [Hausdorff_dist_comm] at H
  rw [Hausdorff_edist_comm] at fin
  simpa [← dist_comm] using exists_dist_lt_of_Hausdorff_dist_lt h H Finₓ

/-- The infimum distance to `s` and `t` are the same, up to the Hausdorff distance
between `s` and `t` -/
theorem inf_dist_le_inf_dist_add_Hausdorff_dist (fin : hausdorffEdist s t ≠ ⊤) :
    infDist x t ≤ infDist x s + hausdorffDist s t := by
  rcases empty_or_nonempty_of_Hausdorff_edist_ne_top Finₓ with (⟨hs, ht⟩ | ⟨hs, ht⟩)
  · simp only [← hs, ← ht, ← Hausdorff_dist_empty, ← inf_dist_empty, ← zero_addₓ]
    
  rw [inf_dist, inf_dist, Hausdorff_dist, ← Ennreal.to_real_add (inf_edist_ne_top hs) Finₓ,
    Ennreal.to_real_le_to_real (inf_edist_ne_top ht)]
  · exact inf_edist_le_inf_edist_add_Hausdorff_edist
    
  · exact Ennreal.add_ne_top.2 ⟨inf_edist_ne_top hs, Finₓ⟩
    

/-- The Hausdorff distance is invariant under isometries -/
theorem Hausdorff_dist_image (h : Isometry Φ) : hausdorffDist (Φ '' s) (Φ '' t) = hausdorffDist s t := by
  simp [← Hausdorff_dist, ← Hausdorff_edist_image h]

/-- The Hausdorff distance satisfies the triangular inequality -/
theorem Hausdorff_dist_triangle (fin : hausdorffEdist s t ≠ ⊤) :
    hausdorffDist s u ≤ hausdorffDist s t + hausdorffDist t u := by
  by_cases' Hausdorff_edist s u = ⊤
  · calc Hausdorff_dist s u = 0 + 0 := by
        simp [← Hausdorff_dist, ← h]_ ≤ Hausdorff_dist s t + Hausdorff_dist t u :=
        add_le_add Hausdorff_dist_nonneg Hausdorff_dist_nonneg
    
  · have Dtu : Hausdorff_edist t u < ⊤ :=
      calc
        Hausdorff_edist t u ≤ Hausdorff_edist t s + Hausdorff_edist s u := Hausdorff_edist_triangle
        _ = Hausdorff_edist s t + Hausdorff_edist s u := by
          simp [← Hausdorff_edist_comm]
        _ < ⊤ := lt_top_iff_ne_top.mpr <| ennreal.add_ne_top.mpr ⟨Finₓ, h⟩
        
    rw [Hausdorff_dist, Hausdorff_dist, Hausdorff_dist, ← Ennreal.to_real_add Finₓ Dtu.ne, Ennreal.to_real_le_to_real h]
    · exact Hausdorff_edist_triangle
      
    · simp [← Ennreal.add_eq_top, ← lt_top_iff_ne_top.1 Dtu, ← Finₓ]
      
    

/-- The Hausdorff distance satisfies the triangular inequality -/
theorem Hausdorff_dist_triangle' (fin : hausdorffEdist t u ≠ ⊤) :
    hausdorffDist s u ≤ hausdorffDist s t + hausdorffDist t u := by
  rw [Hausdorff_edist_comm] at fin
  have I : Hausdorff_dist u s ≤ Hausdorff_dist u t + Hausdorff_dist t s := Hausdorff_dist_triangle Finₓ
  simpa [← add_commₓ, ← Hausdorff_dist_comm] using I

/-- The Hausdorff distance between a set and its closure vanish -/
@[simp]
theorem Hausdorff_dist_self_closure : hausdorffDist s (Closure s) = 0 := by
  simp [← Hausdorff_dist]

/-- Replacing a set by its closure does not change the Hausdorff distance. -/
@[simp]
theorem Hausdorff_dist_closure₁ : hausdorffDist (Closure s) t = hausdorffDist s t := by
  simp [← Hausdorff_dist]

/-- Replacing a set by its closure does not change the Hausdorff distance. -/
@[simp]
theorem Hausdorff_dist_closure₂ : hausdorffDist s (Closure t) = hausdorffDist s t := by
  simp [← Hausdorff_dist]

/-- The Hausdorff distance between two sets and their closures coincide -/
@[simp]
theorem Hausdorff_dist_closure : hausdorffDist (Closure s) (Closure t) = hausdorffDist s t := by
  simp [← Hausdorff_dist]

/-- Two sets are at zero Hausdorff distance if and only if they have the same closures -/
theorem Hausdorff_dist_zero_iff_closure_eq_closure (fin : hausdorffEdist s t ≠ ⊤) :
    hausdorffDist s t = 0 ↔ Closure s = Closure t := by
  simp [← Hausdorff_edist_zero_iff_closure_eq_closure.symm, ← Hausdorff_dist, ← Ennreal.to_real_eq_zero_iff, ← Finₓ]

/-- Two closed sets are at zero Hausdorff distance if and only if they coincide -/
theorem _root_.is_closed.Hausdorff_dist_zero_iff_eq (hs : IsClosed s) (ht : IsClosed t) (fin : hausdorffEdist s t ≠ ⊤) :
    hausdorffDist s t = 0 ↔ s = t := by
  simp [Hausdorff_edist_zero_iff_eq_of_closed hs ht, ← Hausdorff_dist, ← Ennreal.to_real_eq_zero_iff, ← Finₓ]

end

--section
section Thickening

variable [PseudoEmetricSpace α] {δ : ℝ} {s : Set α} {x : α}

open Emetric

/-- The (open) `δ`-thickening `thickening δ E` of a subset `E` in a pseudo emetric space consists
of those points that are at distance less than `δ` from some point of `E`. -/
def Thickening (δ : ℝ) (E : Set α) : Set α :=
  { x : α | infEdist x E < Ennreal.ofReal δ }

theorem mem_thickening_iff_inf_edist_lt : x ∈ Thickening δ s ↔ infEdist x s < Ennreal.ofReal δ :=
  Iff.rfl

/-- The (open) thickening equals the preimage of an open interval under `inf_edist`. -/
theorem thickening_eq_preimage_inf_edist (δ : ℝ) (E : Set α) :
    Thickening δ E = (fun x => infEdist x E) ⁻¹' Iio (Ennreal.ofReal δ) :=
  rfl

/-- The (open) thickening is an open set. -/
theorem is_open_thickening {δ : ℝ} {E : Set α} : IsOpen (Thickening δ E) :=
  Continuous.is_open_preimage continuous_inf_edist _ is_open_Iio

/-- The (open) thickening of the empty set is empty. -/
@[simp]
theorem thickening_empty (δ : ℝ) : Thickening δ (∅ : Set α) = ∅ := by
  simp only [← thickening, ← set_of_false, ← inf_edist_empty, ← not_top_lt]

theorem thickening_of_nonpos (hδ : δ ≤ 0) (s : Set α) : Thickening δ s = ∅ :=
  eq_empty_of_forall_not_mem fun x => ((Ennreal.of_real_of_nonpos hδ).trans_le bot_le).not_lt

/-- The (open) thickening `thickening δ E` of a fixed subset `E` is an increasing function of the
thickening radius `δ`. -/
theorem thickening_mono {δ₁ δ₂ : ℝ} (hle : δ₁ ≤ δ₂) (E : Set α) : Thickening δ₁ E ⊆ Thickening δ₂ E :=
  preimage_mono (Iio_subset_Iio (Ennreal.of_real_le_of_real hle))

/-- The (open) thickening `thickening δ E` with a fixed thickening radius `δ` is
an increasing function of the subset `E`. -/
theorem thickening_subset_of_subset (δ : ℝ) {E₁ E₂ : Set α} (h : E₁ ⊆ E₂) : Thickening δ E₁ ⊆ Thickening δ E₂ :=
  fun _ hx => lt_of_le_of_ltₓ (inf_edist_anti h) hx

theorem mem_thickening_iff_exists_edist_lt {δ : ℝ} (E : Set α) (x : α) :
    x ∈ Thickening δ E ↔ ∃ z ∈ E, edist x z < Ennreal.ofReal δ :=
  inf_edist_lt_iff

variable {X : Type u} [PseudoMetricSpace X]

/-- A point in a metric space belongs to the (open) `δ`-thickening of a subset `E` if and only if
it is at distance less than `δ` from some point of `E`. -/
theorem mem_thickening_iff {E : Set X} {x : X} : x ∈ Thickening δ E ↔ ∃ z ∈ E, dist x z < δ := by
  have key_iff : ∀ z : X, edist x z < Ennreal.ofReal δ ↔ dist x z < δ := by
    intro z
    rw [dist_edist]
    have d_lt_top : edist x z < ∞ := by
      simp only [← edist_dist, ← Ennreal.of_real_lt_top]
    have key := @Ennreal.of_real_lt_of_real_iff_of_nonneg (edist x z).toReal δ Ennreal.to_real_nonneg
    rwa [Ennreal.of_real_to_real d_lt_top.ne] at key
  simp_rw [mem_thickening_iff_exists_edist_lt, key_iff]

@[simp]
theorem thickening_singleton (δ : ℝ) (x : X) : Thickening δ ({x} : Set X) = Ball x δ := by
  ext
  simp [← mem_thickening_iff]

/-- The (open) `δ`-thickening `thickening δ E` of a subset `E` in a metric space equals the
union of balls of radius `δ` centered at points of `E`. -/
theorem thickening_eq_bUnion_ball {δ : ℝ} {E : Set X} : Thickening δ E = ⋃ x ∈ E, Ball x δ := by
  ext x
  rw [mem_Union₂]
  exact mem_thickening_iff

theorem Bounded.thickening {δ : ℝ} {E : Set X} (h : Bounded E) : Bounded (Thickening δ E) := by
  refine' bounded_iff_mem_bounded.2 fun x hx => _
  rcases h.subset_ball x with ⟨R, hR⟩
  refine' (bounded_iff_subset_ball x).2 ⟨R + δ, _⟩
  intro y hy
  rcases mem_thickening_iff.1 hy with ⟨z, zE, hz⟩
  calc dist y x ≤ dist z x + dist y z := by
      rw [add_commₓ]
      exact dist_triangle _ _ _ _ ≤ R + δ := add_le_add (hR zE) hz.le

end Thickening

--section
section Cthickening

variable [PseudoEmetricSpace α] {δ ε : ℝ} {s t : Set α} {x : α}

open Emetric

/-- The closed `δ`-thickening `cthickening δ E` of a subset `E` in a pseudo emetric space consists
of those points that are at infimum distance at most `δ` from `E`. -/
def Cthickening (δ : ℝ) (E : Set α) : Set α :=
  { x : α | infEdist x E ≤ Ennreal.ofReal δ }

@[simp]
theorem mem_cthickening_iff : x ∈ Cthickening δ s ↔ infEdist x s ≤ Ennreal.ofReal δ :=
  Iff.rfl

theorem mem_cthickening_of_edist_le (x y : α) (δ : ℝ) (E : Set α) (h : y ∈ E) (h' : edist x y ≤ Ennreal.ofReal δ) :
    x ∈ Cthickening δ E :=
  (inf_edist_le_edist_of_mem h).trans h'

theorem mem_cthickening_of_dist_le {α : Type _} [PseudoMetricSpace α] (x y : α) (δ : ℝ) (E : Set α) (h : y ∈ E)
    (h' : dist x y ≤ δ) : x ∈ Cthickening δ E := by
  apply mem_cthickening_of_edist_le x y δ E h
  rw [edist_dist]
  exact Ennreal.of_real_le_of_real h'

theorem cthickening_eq_preimage_inf_edist (δ : ℝ) (E : Set α) :
    Cthickening δ E = (fun x => infEdist x E) ⁻¹' Iic (Ennreal.ofReal δ) :=
  rfl

/-- The closed thickening is a closed set. -/
theorem is_closed_cthickening {δ : ℝ} {E : Set α} : IsClosed (Cthickening δ E) :=
  IsClosed.preimage continuous_inf_edist is_closed_Iic

/-- The closed thickening of the empty set is empty. -/
@[simp]
theorem cthickening_empty (δ : ℝ) : Cthickening δ (∅ : Set α) = ∅ := by
  simp only [← cthickening, ← Ennreal.of_real_ne_top, ← set_of_false, ← inf_edist_empty, ← top_le_iff]

theorem cthickening_of_nonpos {δ : ℝ} (hδ : δ ≤ 0) (E : Set α) : Cthickening δ E = Closure E := by
  ext x
  simp [← mem_closure_iff_inf_edist_zero, ← cthickening, ← Ennreal.of_real_eq_zero.2 hδ]

/-- The closed thickening with radius zero is the closure of the set. -/
@[simp]
theorem cthickening_zero (E : Set α) : Cthickening 0 E = Closure E :=
  cthickening_of_nonpos le_rfl E

/-- The closed thickening `cthickening δ E` of a fixed subset `E` is an increasing function of
the thickening radius `δ`. -/
theorem cthickening_mono {δ₁ δ₂ : ℝ} (hle : δ₁ ≤ δ₂) (E : Set α) : Cthickening δ₁ E ⊆ Cthickening δ₂ E :=
  preimage_mono (Iic_subset_Iic.mpr (Ennreal.of_real_le_of_real hle))

@[simp]
theorem cthickening_singleton {α : Type _} [PseudoMetricSpace α] (x : α) {δ : ℝ} (hδ : 0 ≤ δ) :
    Cthickening δ ({x} : Set α) = ClosedBall x δ := by
  ext y
  simp [← cthickening, ← edist_dist, ← Ennreal.of_real_le_of_real_iff hδ]

theorem closed_ball_subset_cthickening_singleton {α : Type _} [PseudoMetricSpace α] (x : α) (δ : ℝ) :
    ClosedBall x δ ⊆ Cthickening δ ({x} : Set α) := by
  rcases lt_or_leₓ δ 0 with (hδ | hδ)
  · simp only [← closed_ball_eq_empty.mpr hδ, ← empty_subset]
    
  · simp only [← cthickening_singleton x hδ]
    

/-- The closed thickening `cthickening δ E` with a fixed thickening radius `δ` is
an increasing function of the subset `E`. -/
theorem cthickening_subset_of_subset (δ : ℝ) {E₁ E₂ : Set α} (h : E₁ ⊆ E₂) : Cthickening δ E₁ ⊆ Cthickening δ E₂ :=
  fun _ hx => le_transₓ (inf_edist_anti h) hx

theorem cthickening_subset_thickening {δ₁ : ℝ≥0 } {δ₂ : ℝ} (hlt : (δ₁ : ℝ) < δ₂) (E : Set α) :
    Cthickening δ₁ E ⊆ Thickening δ₂ E := fun _ hx =>
  lt_of_le_of_ltₓ hx ((Ennreal.of_real_lt_of_real_iff (lt_of_le_of_ltₓ δ₁.Prop hlt)).mpr hlt)

/-- The closed thickening `cthickening δ₁ E` is contained in the open thickening `thickening δ₂ E`
if the radius of the latter is positive and larger. -/
theorem cthickening_subset_thickening' {δ₁ δ₂ : ℝ} (δ₂_pos : 0 < δ₂) (hlt : δ₁ < δ₂) (E : Set α) :
    Cthickening δ₁ E ⊆ Thickening δ₂ E := fun _ hx =>
  lt_of_le_of_ltₓ hx ((Ennreal.of_real_lt_of_real_iff δ₂_pos).mpr hlt)

/-- The open thickening `thickening δ E` is contained in the closed thickening `cthickening δ E`
with the same radius. -/
theorem thickening_subset_cthickening (δ : ℝ) (E : Set α) : Thickening δ E ⊆ Cthickening δ E := by
  intro x hx
  rw [thickening, mem_set_of_eq] at hx
  exact hx.le

theorem thickening_subset_cthickening_of_le {δ₁ δ₂ : ℝ} (hle : δ₁ ≤ δ₂) (E : Set α) :
    Thickening δ₁ E ⊆ Cthickening δ₂ E :=
  (thickening_subset_cthickening δ₁ E).trans (cthickening_mono hle E)

theorem Bounded.cthickening {α : Type _} [PseudoMetricSpace α] {δ : ℝ} {E : Set α} (h : Bounded E) :
    Bounded (Cthickening δ E) := by
  have : bounded (thickening (max (δ + 1) 1) E) := h.thickening
  apply bounded.mono _ this
  exact
    cthickening_subset_thickening' (zero_lt_one.trans_le (le_max_rightₓ _ _))
      ((lt_add_one _).trans_le (le_max_leftₓ _ _)) _

theorem thickening_subset_interior_cthickening (δ : ℝ) (E : Set α) : Thickening δ E ⊆ Interior (Cthickening δ E) :=
  (subset_interior_iff_open.mpr is_open_thickening).trans (interior_mono (thickening_subset_cthickening δ E))

theorem closure_thickening_subset_cthickening (δ : ℝ) (E : Set α) : Closure (Thickening δ E) ⊆ Cthickening δ E :=
  (closure_mono (thickening_subset_cthickening δ E)).trans is_closed_cthickening.closure_subset

/-- The closed thickening of a set contains the closure of the set. -/
theorem closure_subset_cthickening (δ : ℝ) (E : Set α) : Closure E ⊆ Cthickening δ E := by
  rw [← cthickening_of_nonpos (min_le_rightₓ δ 0)]
  exact cthickening_mono (min_le_leftₓ δ 0) E

/-- The (open) thickening of a set contains the closure of the set. -/
theorem closure_subset_thickening {δ : ℝ} (δ_pos : 0 < δ) (E : Set α) : Closure E ⊆ Thickening δ E := by
  rw [← cthickening_zero]
  exact cthickening_subset_thickening' δ_pos δ_pos E

/-- A set is contained in its own (open) thickening. -/
theorem self_subset_thickening {δ : ℝ} (δ_pos : 0 < δ) (E : Set α) : E ⊆ Thickening δ E :=
  (@subset_closure _ _ E).trans (closure_subset_thickening δ_pos E)

/-- A set is contained in its own closed thickening. -/
theorem self_subset_cthickening {δ : ℝ} (E : Set α) : E ⊆ Cthickening δ E :=
  subset_closure.trans (closure_subset_cthickening δ E)

@[simp]
theorem thickening_union (δ : ℝ) (s t : Set α) : Thickening δ (s ∪ t) = Thickening δ s ∪ Thickening δ t := by
  simp_rw [thickening, inf_edist_union, inf_eq_min, min_lt_iff, set_of_or]

@[simp]
theorem cthickening_union (δ : ℝ) (s t : Set α) : Cthickening δ (s ∪ t) = Cthickening δ s ∪ Cthickening δ t := by
  simp_rw [cthickening, inf_edist_union, inf_eq_min, min_le_iff, set_of_or]

@[simp]
theorem thickening_Union (δ : ℝ) (f : ι → Set α) : Thickening δ (⋃ i, f i) = ⋃ i, Thickening δ (f i) := by
  simp_rw [thickening, inf_edist_Union, infi_lt_iff, set_of_exists]

@[simp]
theorem thickening_closure : Thickening δ (Closure s) = Thickening δ s := by
  simp_rw [thickening, inf_edist_closure]

@[simp]
theorem cthickening_closure : Cthickening δ (Closure s) = Cthickening δ s := by
  simp_rw [cthickening, inf_edist_closure]

open Ennreal

theorem _root_.disjoint.exists_thickenings (hst : Disjoint s t) (hs : IsCompact s) (ht : IsClosed t) :
    ∃ δ, 0 < δ ∧ Disjoint (Thickening δ s) (Thickening δ t) := by
  obtain rfl | hs' := s.eq_empty_or_nonempty
  · simp_rw [thickening_empty]
    exact ⟨1, zero_lt_one, empty_disjoint _⟩
    
  obtain ⟨r, hr, h⟩ := exists_pos_forall_le_edist hs hs' ht hst
  refine'
    ⟨(min 1 (r / 2)).toReal,
      to_real_pos (lt_minₓ Ennreal.zero_lt_one <| half_pos hr.ne').ne' (min_lt_of_left_lt one_lt_top).Ne, _⟩
  rintro z ⟨hzs, hzt⟩
  rw [mem_thickening_iff_exists_edist_lt] at hzs hzt
  obtain ⟨x, hx, hzx⟩ := hzs
  obtain ⟨y, hy, hzy⟩ := hzt
  refine' (((h _ hx _ hy).trans <| edist_triangle_left _ _ _).trans_lt <| Ennreal.add_lt_add hzx hzy).not_le _
  rw [← two_mul]
  exact Ennreal.mul_le_of_le_div' (of_real_to_real_le.trans <| min_le_rightₓ _ _)

theorem _root_.disjoint.exists_cthickenings (hst : Disjoint s t) (hs : IsCompact s) (ht : IsClosed t) :
    ∃ δ, 0 < δ ∧ Disjoint (Cthickening δ s) (Cthickening δ t) := by
  obtain ⟨δ, hδ, h⟩ := hst.exists_thickenings hs ht
  refine' ⟨δ / 2, half_pos hδ, h.mono _ _⟩ <;> exact cthickening_subset_thickening' hδ (half_lt_self hδ) _

theorem _root_.is_compact.exists_thickening_subset_open (hs : IsCompact s) (ht : IsOpen t) (hst : s ⊆ t) :
    ∃ δ, 0 < δ ∧ Thickening δ s ⊆ t :=
  (hst.disjoint_compl_right.exists_thickenings hs ht.is_closed_compl).imp fun δ h =>
    ⟨h.1, disjoint_compl_right_iff_subset.1 <| h.2.mono_right <| self_subset_thickening h.1 _⟩

theorem _root_.is_compact.exists_cthickening_subset_open (hs : IsCompact s) (ht : IsOpen t) (hst : s ⊆ t) :
    ∃ δ, 0 < δ ∧ Cthickening δ s ⊆ t :=
  (hst.disjoint_compl_right.exists_cthickenings hs ht.is_closed_compl).imp fun δ h =>
    ⟨h.1, disjoint_compl_right_iff_subset.1 <| h.2.mono_right <| self_subset_cthickening _⟩

theorem cthickening_eq_Inter_cthickening' {δ : ℝ} (s : Set ℝ) (hsδ : s ⊆ Ioi δ)
    (hs : ∀ ε, δ < ε → (s ∩ Ioc δ ε).Nonempty) (E : Set α) : Cthickening δ E = ⋂ ε ∈ s, Cthickening ε E := by
  apply subset.antisymm
  · exact subset_Inter₂ fun _ hε => cthickening_mono (le_of_ltₓ (hsδ hε)) E
    
  · unfold thickening cthickening
    intro x hx
    simp only [← mem_Inter, ← mem_set_of_eq] at *
    apply Ennreal.le_of_forall_pos_le_add
    intro η η_pos _
    rcases hs (δ + η) (lt_add_of_pos_right _ (nnreal.coe_pos.mpr η_pos)) with ⟨ε, ⟨hsε, hε⟩⟩
    apply ((hx ε hsε).trans (Ennreal.of_real_le_of_real hε.2)).trans
    rw [Ennreal.coe_nnreal_eq η]
    exact Ennreal.of_real_add_le
    

theorem cthickening_eq_Inter_cthickening {δ : ℝ} (E : Set α) :
    Cthickening δ E = ⋂ (ε : ℝ) (h : δ < ε), Cthickening ε E := by
  apply cthickening_eq_Inter_cthickening' (Ioi δ) rfl.subset
  simp_rw [inter_eq_right_iff_subset.mpr Ioc_subset_Ioi_self]
  exact fun _ hε => nonempty_Ioc.mpr hε

theorem cthickening_eq_Inter_thickening' {δ : ℝ} (δ_nn : 0 ≤ δ) (s : Set ℝ) (hsδ : s ⊆ Ioi δ)
    (hs : ∀ ε, δ < ε → (s ∩ Ioc δ ε).Nonempty) (E : Set α) : Cthickening δ E = ⋂ ε ∈ s, Thickening ε E := by
  refine' (subset_Inter₂ fun ε hε => _).antisymm _
  · obtain ⟨ε', hsε', hε'⟩ := hs ε (hsδ hε)
    have ss := cthickening_subset_thickening' (lt_of_le_of_ltₓ δ_nn hε'.1) hε'.1 E
    exact ss.trans (thickening_mono hε'.2 E)
    
  · rw [cthickening_eq_Inter_cthickening' s hsδ hs E]
    exact Inter₂_mono fun ε hε => thickening_subset_cthickening ε E
    

theorem cthickening_eq_Inter_thickening {δ : ℝ} (δ_nn : 0 ≤ δ) (E : Set α) :
    Cthickening δ E = ⋂ (ε : ℝ) (h : δ < ε), Thickening ε E := by
  apply cthickening_eq_Inter_thickening' δ_nn (Ioi δ) rfl.subset
  simp_rw [inter_eq_right_iff_subset.mpr Ioc_subset_Ioi_self]
  exact fun _ hε => nonempty_Ioc.mpr hε

/-- The closure of a set equals the intersection of its closed thickenings of positive radii
accumulating at zero. -/
theorem closure_eq_Inter_cthickening' (E : Set α) (s : Set ℝ) (hs : ∀ ε, 0 < ε → (s ∩ Ioc 0 ε).Nonempty) :
    Closure E = ⋂ δ ∈ s, Cthickening δ E := by
  by_cases' hs₀ : s ⊆ Ioi 0
  · rw [← cthickening_zero]
    apply cthickening_eq_Inter_cthickening' _ hs₀ hs
    
  obtain ⟨δ, hδs, δ_nonpos⟩ := not_subset.mp hs₀
  rw [Set.mem_Ioi, not_ltₓ] at δ_nonpos
  apply subset.antisymm
  · exact subset_Inter₂ fun ε _ => closure_subset_cthickening ε E
    
  · rw [← cthickening_of_nonpos δ_nonpos E]
    exact bInter_subset_of_mem hδs
    

/-- The closure of a set equals the intersection of its closed thickenings of positive radii. -/
theorem closure_eq_Inter_cthickening (E : Set α) : Closure E = ⋂ (δ : ℝ) (h : 0 < δ), Cthickening δ E := by
  rw [← cthickening_zero]
  exact cthickening_eq_Inter_cthickening E

/-- The closure of a set equals the intersection of its open thickenings of positive radii
accumulating at zero. -/
theorem closure_eq_Inter_thickening' (E : Set α) (s : Set ℝ) (hs₀ : s ⊆ Ioi 0)
    (hs : ∀ ε, 0 < ε → (s ∩ Ioc 0 ε).Nonempty) : Closure E = ⋂ δ ∈ s, Thickening δ E := by
  rw [← cthickening_zero]
  apply cthickening_eq_Inter_thickening' le_rfl _ hs₀ hs

/-- The closure of a set equals the intersection of its (open) thickenings of positive radii. -/
theorem closure_eq_Inter_thickening (E : Set α) : Closure E = ⋂ (δ : ℝ) (h : 0 < δ), Thickening δ E := by
  rw [← cthickening_zero]
  exact cthickening_eq_Inter_thickening rfl.ge E

/-- The frontier of the (open) thickening of a set is contained in an `inf_edist` level set. -/
theorem frontier_thickening_subset (E : Set α) {δ : ℝ} (δ_pos : 0 < δ) :
    Frontier (Thickening δ E) ⊆ { x : α | infEdist x E = Ennreal.ofReal δ } := by
  have singleton_preim :
    { x : α | inf_edist x E = Ennreal.ofReal δ } = (fun x => inf_edist x E) ⁻¹' {Ennreal.ofReal δ} := by
    simp only [← preimage, ← mem_singleton_iff]
  rw [thickening_eq_preimage_inf_edist, singleton_preim, ← frontier_Iio' ⟨(0 : ℝ≥0∞), ennreal.of_real_pos.mpr δ_pos⟩]
  exact continuous_inf_edist.frontier_preimage_subset (Iio (Ennreal.ofReal δ))

/-- The frontier of the closed thickening of a set is contained in an `inf_edist` level set. -/
theorem frontier_cthickening_subset (E : Set α) {δ : ℝ} :
    Frontier (Cthickening δ E) ⊆ { x : α | infEdist x E = Ennreal.ofReal δ } := by
  have singleton_preim :
    { x : α | inf_edist x E = Ennreal.ofReal δ } = (fun x => inf_edist x E) ⁻¹' {Ennreal.ofReal δ} := by
    simp only [← preimage, ← mem_singleton_iff]
  rw [cthickening_eq_preimage_inf_edist, singleton_preim, ← frontier_Iic' ⟨∞, Ennreal.of_real_lt_top⟩]
  exact continuous_inf_edist.frontier_preimage_subset (Iic (Ennreal.ofReal δ))

/-- The closed ball of radius `δ` centered at a point of `E` is included in the closed
thickening of `E`. -/
theorem closed_ball_subset_cthickening {α : Type _} [PseudoMetricSpace α] {x : α} {E : Set α} (hx : x ∈ E) (δ : ℝ) :
    ClosedBall x δ ⊆ Cthickening δ E := by
  refine' (closed_ball_subset_cthickening_singleton _ _).trans (cthickening_subset_of_subset _ _)
  simpa using hx

/-- The closed thickening of a compact set `E` is the union of the balls `closed_ball x δ` over
`x ∈ E`. -/
theorem _root_.is_compact.cthickening_eq_bUnion_closed_ball {α : Type _} [PseudoMetricSpace α] {δ : ℝ} {E : Set α}
    (hE : IsCompact E) (hδ : 0 ≤ δ) : Cthickening δ E = ⋃ x ∈ E, ClosedBall x δ := by
  rcases eq_empty_or_nonempty E with (rfl | hne)
  · simp only [← cthickening_empty, ← Union_false, ← Union_empty]
    
  refine' subset.antisymm (fun x hx => _) (Union₂_subset fun x hx => closed_ball_subset_cthickening hx _)
  obtain ⟨y, yE, hy⟩ : ∃ y ∈ E, Emetric.infEdist x E = edist x y := hE.exists_inf_edist_eq_edist hne _
  have D1 : edist x y ≤ Ennreal.ofReal δ := (le_of_eqₓ hy.symm).trans hx
  have D2 : dist x y ≤ δ := by
    rw [edist_dist] at D1
    exact (Ennreal.of_real_le_of_real_iff hδ).1 D1
  exact mem_bUnion yE D2

/-- For the equality, see `inf_edist_cthickening`. -/
theorem inf_edist_le_inf_edist_cthickening_add : infEdist x s ≤ infEdist x (Cthickening δ s) + Ennreal.ofReal δ := by
  refine' le_of_forall_lt' fun r h => _
  simp_rw [← lt_tsub_iff_right, inf_edist_lt_iff, mem_cthickening_iff] at h
  obtain ⟨y, hy, hxy⟩ := h
  exact
    inf_edist_le_edist_add_inf_edist.trans_lt
      ((Ennreal.add_lt_add_of_lt_of_le (hy.trans_lt Ennreal.of_real_lt_top).Ne hxy hy).trans_le
        (tsub_add_cancel_of_le <| le_self_add.trans (lt_tsub_iff_left.1 hxy).le).le)

/-- For the equality, see `inf_edist_thickening`. -/
theorem inf_edist_le_inf_edist_thickening_add : infEdist x s ≤ infEdist x (Thickening δ s) + Ennreal.ofReal δ :=
  inf_edist_le_inf_edist_cthickening_add.trans <|
    add_le_add_right (inf_edist_anti <| thickening_subset_cthickening _ _) _

/-- For the equality, see `thickening_thickening`. -/
@[simp]
theorem thickening_thickening_subset (ε δ : ℝ) (s : Set α) : Thickening ε (Thickening δ s) ⊆ Thickening (ε + δ) s := by
  obtain hε | hε := le_totalₓ ε 0
  · simp only [← thickening_of_nonpos hε, ← empty_subset]
    
  obtain hδ | hδ := le_totalₓ δ 0
  · simp only [← thickening_of_nonpos hδ, ← thickening_empty, ← empty_subset]
    
  intro x
  simp_rw [mem_thickening_iff_exists_edist_lt, Ennreal.of_real_add hε hδ]
  exact fun ⟨y, ⟨z, hz, hy⟩, hx⟩ => ⟨z, hz, (edist_triangle _ _ _).trans_lt <| Ennreal.add_lt_add hx hy⟩

/-- For the equality, see `thickening_cthickening`. -/
@[simp]
theorem thickening_cthickening_subset (ε : ℝ) (hδ : 0 ≤ δ) (s : Set α) :
    Thickening ε (Cthickening δ s) ⊆ Thickening (ε + δ) s := by
  obtain hε | hε := le_totalₓ ε 0
  · simp only [← thickening_of_nonpos hε, ← empty_subset]
    
  intro x
  simp_rw [mem_thickening_iff_exists_edist_lt, mem_cthickening_iff, ← inf_edist_lt_iff, Ennreal.of_real_add hε hδ]
  rintro ⟨y, hy, hxy⟩
  exact
    inf_edist_le_edist_add_inf_edist.trans_lt
      (Ennreal.add_lt_add_of_lt_of_le (hy.trans_lt Ennreal.of_real_lt_top).Ne hxy hy)

/-- For the equality, see `cthickening_thickening`. -/
@[simp]
theorem cthickening_thickening_subset (hε : 0 ≤ ε) (δ : ℝ) (s : Set α) :
    Cthickening ε (Thickening δ s) ⊆ Cthickening (ε + δ) s := by
  obtain hδ | hδ := le_totalₓ δ 0
  · simp only [← thickening_of_nonpos hδ, ← cthickening_empty, ← empty_subset]
    
  intro x
  simp_rw [mem_cthickening_iff, Ennreal.of_real_add hε hδ]
  exact fun hx => inf_edist_le_inf_edist_thickening_add.trans (add_le_add_right hx _)

/-- For the equality, see `cthickening_cthickening`. -/
@[simp]
theorem cthickening_cthickening_subset (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (s : Set α) :
    Cthickening ε (Cthickening δ s) ⊆ Cthickening (ε + δ) s := by
  intro x
  simp_rw [mem_cthickening_iff, Ennreal.of_real_add hε hδ]
  exact fun hx => inf_edist_le_inf_edist_cthickening_add.trans (add_le_add_right hx _)

end Cthickening

--section
end Metric

--namespace
