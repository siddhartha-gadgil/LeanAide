/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathbin.Topology.MetricSpace.EmetricSpace

/-!
# Metric separated pairs of sets

In this file we define the predicate `is_metric_separated`. We say that two sets in an (extended)
metric space are *metric separated* if the (extended) distance between `x ∈ s` and `y ∈ t` is
bounded from below by a positive constant.

This notion is useful, e.g., to define metric outer measures.
-/


open Emetric Set

noncomputable section

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (r «expr ≠ » 0)
/-- Two sets in an (extended) metric space are called *metric separated* if the (extended) distance
between `x ∈ s` and `y ∈ t` is bounded from below by a positive constant. -/
def IsMetricSeparated {X : Type _} [EmetricSpace X] (s t : Set X) :=
  ∃ (r : _)(_ : r ≠ 0), ∀, ∀ x ∈ s, ∀, ∀ y ∈ t, ∀, r ≤ edist x y

namespace IsMetricSeparated

variable {X : Type _} [EmetricSpace X] {s t : Set X} {x y : X}

@[symm]
theorem symm (h : IsMetricSeparated s t) : IsMetricSeparated t s :=
  let ⟨r, r0, hr⟩ := h
  ⟨r, r0, fun y hy x hx => edist_comm x y ▸ hr x hx y hy⟩

theorem comm : IsMetricSeparated s t ↔ IsMetricSeparated t s :=
  ⟨symm, symm⟩

@[simp]
theorem empty_left (s : Set X) : IsMetricSeparated ∅ s :=
  ⟨1, Ennreal.zero_lt_one.ne', fun x => False.elim⟩

@[simp]
theorem empty_right (s : Set X) : IsMetricSeparated s ∅ :=
  (empty_left s).symm

protected theorem disjoint (h : IsMetricSeparated s t) : Disjoint s t :=
  let ⟨r, r0, hr⟩ := h
  fun x hx =>
  r0 <| by
    simpa using hr x hx.1 x hx.2

theorem subset_compl_right (h : IsMetricSeparated s t) : s ⊆ tᶜ := fun x hs ht => h.Disjoint ⟨hs, ht⟩

@[mono]
theorem mono {s' t'} (hs : s ⊆ s') (ht : t ⊆ t') : IsMetricSeparated s' t' → IsMetricSeparated s t := fun ⟨r, r0, hr⟩ =>
  ⟨r, r0, fun x hx y hy => hr x (hs hx) y (ht hy)⟩

theorem mono_left {s'} (h' : IsMetricSeparated s' t) (hs : s ⊆ s') : IsMetricSeparated s t :=
  h'.mono hs Subset.rfl

theorem mono_right {t'} (h' : IsMetricSeparated s t') (ht : t ⊆ t') : IsMetricSeparated s t :=
  h'.mono Subset.rfl ht

theorem union_left {s'} (h : IsMetricSeparated s t) (h' : IsMetricSeparated s' t) : IsMetricSeparated (s ∪ s') t := by
  rcases h, h' with ⟨⟨r, r0, hr⟩, ⟨r', r0', hr'⟩⟩
  refine' ⟨min r r', _, fun x hx y hy => hx.elim _ _⟩
  · rw [← pos_iff_ne_zero] at r0 r0'⊢
    exact lt_minₓ r0 r0'
    
  · exact fun hx => (min_le_leftₓ _ _).trans (hr _ hx _ hy)
    
  · exact fun hx => (min_le_rightₓ _ _).trans (hr' _ hx _ hy)
    

@[simp]
theorem union_left_iff {s'} : IsMetricSeparated (s ∪ s') t ↔ IsMetricSeparated s t ∧ IsMetricSeparated s' t :=
  ⟨fun h => ⟨h.mono_left (subset_union_left _ _), h.mono_left (subset_union_right _ _)⟩, fun h => h.1.union_left h.2⟩

theorem union_right {t'} (h : IsMetricSeparated s t) (h' : IsMetricSeparated s t') : IsMetricSeparated s (t ∪ t') :=
  (h.symm.union_left h'.symm).symm

@[simp]
theorem union_right_iff {t'} : IsMetricSeparated s (t ∪ t') ↔ IsMetricSeparated s t ∧ IsMetricSeparated s t' :=
  comm.trans <| union_left_iff.trans <| and_congr comm comm

theorem finite_Union_left_iff {ι : Type _} {I : Set ι} (hI : I.Finite) {s : ι → Set X} {t : Set X} :
    IsMetricSeparated (⋃ i ∈ I, s i) t ↔ ∀, ∀ i ∈ I, ∀, IsMetricSeparated (s i) t := by
  refine'
    finite.induction_on hI
      (by
        simp )
      fun i I hi _ hI => _
  rw [bUnion_insert, ball_insert_iff, union_left_iff, hI]

alias finite_Union_left_iff ↔ _ finite_Union_left

theorem finite_Union_right_iff {ι : Type _} {I : Set ι} (hI : I.Finite) {s : Set X} {t : ι → Set X} :
    IsMetricSeparated s (⋃ i ∈ I, t i) ↔ ∀, ∀ i ∈ I, ∀, IsMetricSeparated s (t i) := by
  simpa only [← @comm _ _ s] using finite_Union_left_iff hI

@[simp]
theorem finset_Union_left_iff {ι : Type _} {I : Finset ι} {s : ι → Set X} {t : Set X} :
    IsMetricSeparated (⋃ i ∈ I, s i) t ↔ ∀, ∀ i ∈ I, ∀, IsMetricSeparated (s i) t :=
  finite_Union_left_iff I.finite_to_set

alias finset_Union_left_iff ↔ _ finset_Union_left

@[simp]
theorem finset_Union_right_iff {ι : Type _} {I : Finset ι} {s : Set X} {t : ι → Set X} :
    IsMetricSeparated s (⋃ i ∈ I, t i) ↔ ∀, ∀ i ∈ I, ∀, IsMetricSeparated s (t i) :=
  finite_Union_right_iff I.finite_to_set

alias finset_Union_right_iff ↔ _ finset_Union_right

end IsMetricSeparated

