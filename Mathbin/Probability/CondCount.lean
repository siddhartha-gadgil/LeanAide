/-
Copyright (c) 2022 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying, Bhavik Mehta
-/
import Mathbin.Probability.ConditionalProbability

/-!
# Classical probability

The classical formulation of probability states that the probability of an event occurring in a
finite probability space is the ratio of that event to all possible events.
This notion can be expressed with measure theory using
the counting measure. In particular, given the sets `s` and `t`, we define the probability of `t`
occuring in `s` to be `|s|⁻¹ * |s ∩ t|`. With this definition, we recover the the probability over
the entire sample space when `s = set.univ`.

Classical probability is often used in combinatorics and we prove some useful lemmas in this file
for that purpose.

## Main definition

* `probability_theory.cond_count`: given a set `s`, `cond_count s` is the counting measure
  conditioned on `s`. This is a probability measure when `s` is finite and nonempty.

## Notes

The original aim of this file is to provide a measure theoretic method of describing the
probability an element of a set `s` satisfies some predicate `P`. Our current formulation still
allow us to describe this by abusing the definitional equality of sets and predicates by simply
writing `cond_count s P`. We should avoid this however as none of the lemmas are written for
predicates.
-/


noncomputable section

open ProbabilityTheory

open MeasureTheory MeasurableSpace

namespace ProbabilityTheory

variable {α : Type _} [MeasurableSpace α]

/-- Given a set `s`, `cond_count s` is the counting measure conditioned on `s`. In particular,
`cond_count s t` is the proportion of `s` that is contained in `t`.

This is a probability measure when `s` is finite and nonempty and is given by
`probability_theory.cond_count_is_probability_measure`. -/
def condCount (s : Set α) : Measureₓ α :=
  measure.count[|s]

@[simp]
theorem cond_count_empty_meas : (condCount ∅ : Measureₓ α) = 0 := by
  simp [← cond_count]

theorem cond_count_empty {s : Set α} : condCount s ∅ = 0 := by
  simp

theorem finite_of_cond_count_ne_zero {s t : Set α} (h : condCount s t ≠ 0) : s.Finite := by
  by_contra hs'
  simpa [← cond_count, ← cond, ← measure.count_apply_infinite hs'] using h

variable [MeasurableSingletonClass α]

theorem cond_count_is_probability_measure {s : Set α} (hs : s.Finite) (hs' : s.Nonempty) :
    IsProbabilityMeasure (condCount s) :=
  { measure_univ := by
      rw [cond_count, cond_apply _ hs.measurable_set, Set.inter_univ, Ennreal.inv_mul_cancel]
      · exact fun h => hs'.ne_empty <| measure.empty_of_count_eq_zero h
        
      · exact (measure.count_apply_lt_top.2 hs).Ne
         }

theorem cond_count_singleton (a : α) (t : Set α) [Decidable (a ∈ t)] : condCount {a} t = if a ∈ t then 1 else 0 := by
  rw [cond_count, cond_apply _ (measurable_set_singleton a), measure.count_singleton, Ennreal.inv_one, one_mulₓ]
  split_ifs
  · rw
      [(by
        simpa : ({a} : Set α) ∩ t = {a}),
      measure.count_singleton]
    
  · rw
      [(by
        simpa : ({a} : Set α) ∩ t = ∅),
      measure.count_empty]
    

variable {s t u : Set α}

theorem cond_count_inter_self (hs : s.Finite) : condCount s (s ∩ t) = condCount s t := by
  rw [cond_count, cond_inter_self _ hs.measurable_set]

theorem cond_count_self (hs : s.Finite) (hs' : s.Nonempty) : condCount s s = 1 := by
  rw [cond_count, cond_apply _ hs.measurable_set, Set.inter_self, Ennreal.inv_mul_cancel]
  · exact fun h => hs'.ne_empty <| measure.empty_of_count_eq_zero h
    
  · exact (measure.count_apply_lt_top.2 hs).Ne
    

theorem cond_count_eq_one_of (hs : s.Finite) (hs' : s.Nonempty) (ht : s ⊆ t) : condCount s t = 1 := by
  have := cond_count_is_probability_measure hs hs'
  refine' eq_of_le_of_not_lt prob_le_one _
  rw [not_ltₓ, ← cond_count_self hs hs']
  exact measure_mono ht

theorem pred_true_of_cond_count_eq_one (h : condCount s t = 1) : s ⊆ t := by
  have hsf :=
    finite_of_cond_count_ne_zero
      (by
        rw [h]
        exact one_ne_zero)
  rw [cond_count, cond_apply _ hsf.measurable_set, mul_comm] at h
  replace h := Ennreal.eq_inv_of_mul_eq_one_left h
  rw [inv_invₓ, measure.count_apply_finite _ hsf, measure.count_apply_finite _ (hsf.inter_of_left _), Nat.cast_inj] at h
  suffices s ∩ t = s by
    exact this ▸ fun x hx => hx.2
  rw [← @Set.Finite.to_finset_inj _ _ _ (hsf.inter_of_left _) hsf]
  exact Finset.eq_of_subset_of_card_le (Set.Finite.to_finset_mono.2 (s.inter_subset_left t)) h.symm.le

theorem cond_count_eq_zero_iff (hs : s.Finite) : condCount s t = 0 ↔ s ∩ t = ∅ := by
  simp [← cond_count, ← cond_apply _ hs.measurable_set, ← measure.count_apply_eq_top, ← Set.not_infinite.2 hs, ←
    measure.count_apply_finite _ (hs.inter_of_left _)]

theorem cond_count_univ (hs : s.Finite) (hs' : s.Nonempty) : condCount s Set.Univ = 1 :=
  cond_count_eq_one_of hs hs' s.subset_univ

theorem cond_count_inter (hs : s.Finite) : condCount s (t ∩ u) = condCount (s ∩ t) u * condCount s t := by
  by_cases' hst : s ∩ t = ∅
  · rw [hst, cond_count_empty_meas, measure.coe_zero, Pi.zero_apply, zero_mul, cond_count_eq_zero_iff hs, ←
      Set.inter_assoc, hst, Set.empty_inter]
    
  rw [cond_count, cond_count, cond_apply _ hs.measurable_set, cond_apply _ hs.measurable_set,
    cond_apply _ (hs.inter_of_left _).MeasurableSet, mul_comm _ (measure.count (s ∩ t)), ← mul_assoc,
    mul_comm _ (measure.count (s ∩ t)), ← mul_assoc, Ennreal.mul_inv_cancel, one_mulₓ, mul_comm, Set.inter_assoc]
  · rwa [← measure.count_eq_zero_iff] at hst
    
  · exact (measure.count_apply_lt_top.2 <| hs.inter_of_left _).Ne
    

theorem cond_count_inter' (hs : s.Finite) : condCount s (t ∩ u) = condCount (s ∩ u) t * condCount s u := by
  rw [← Set.inter_comm]
  exact cond_count_inter hs

theorem cond_count_union (hs : s.Finite) (htu : Disjoint t u) : condCount s (t ∪ u) = condCount s t + condCount s u :=
  by
  rw [cond_count, cond_apply _ hs.measurable_set, cond_apply _ hs.measurable_set, cond_apply _ hs.measurable_set,
    Set.inter_union_distrib_left, measure_union, mul_addₓ]
  exacts[htu.mono inf_le_right inf_le_right, (hs.inter_of_left _).MeasurableSet]

theorem cond_count_compl (t : Set α) (hs : s.Finite) (hs' : s.Nonempty) : condCount s t + condCount s (tᶜ) = 1 := by
  rw [← cond_count_union hs disjoint_compl_right, Set.union_compl_self,
    (cond_count_is_probability_measure hs hs').measure_univ]

theorem cond_count_disjoint_union (hs : s.Finite) (ht : t.Finite) (hst : Disjoint s t) :
    condCount s u * condCount (s ∪ t) s + condCount t u * condCount (s ∪ t) t = condCount (s ∪ t) u := by
  rcases s.eq_empty_or_nonempty with (rfl | hs') <;> rcases t.eq_empty_or_nonempty with (rfl | ht')
  · simp
    
  · simp [← cond_count_self ht ht']
    
  · simp [← cond_count_self hs hs']
    
  rw [cond_count, cond_count, cond_count, cond_apply _ hs.measurable_set, cond_apply _ ht.measurable_set,
    cond_apply _ (hs.union ht).MeasurableSet, cond_apply _ (hs.union ht).MeasurableSet,
    cond_apply _ (hs.union ht).MeasurableSet]
  conv_lhs =>
    rw [Set.union_inter_cancel_left, Set.union_inter_cancel_right, mul_comm (measure.count (s ∪ t))⁻¹,
      mul_comm (measure.count (s ∪ t))⁻¹, ← mul_assoc, ← mul_assoc, mul_comm _ (measure.count s),
      mul_comm _ (measure.count t), ← mul_assoc, ← mul_assoc]
  rw [Ennreal.mul_inv_cancel, Ennreal.mul_inv_cancel, one_mulₓ, one_mulₓ, ← add_mulₓ, ← measure_union,
    Set.union_inter_distrib_right, mul_comm]
  exacts[hst.mono inf_le_left inf_le_left, (ht.inter_of_left _).MeasurableSet, measure.count_ne_zero ht',
    (measure.count_apply_lt_top.2 ht).Ne, measure.count_ne_zero hs', (measure.count_apply_lt_top.2 hs).Ne]

/-- A version of the law of total probability for counting probabilites. -/
theorem cond_count_add_compl_eq (u t : Set α) (hs : s.Finite) :
    condCount (s ∩ u) t * condCount s u + condCount (s ∩ uᶜ) t * condCount s (uᶜ) = condCount s t := by
  conv_rhs =>
    rw
      [(by
        simp : s = s ∩ u ∪ s ∩ uᶜ),
      ←
      cond_count_disjoint_union (hs.inter_of_left _) (hs.inter_of_left _)
        (disjoint_compl_right.mono inf_le_right inf_le_right)]
  simp [← cond_count_inter_self hs]

end ProbabilityTheory

