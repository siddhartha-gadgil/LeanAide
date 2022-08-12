/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Devon Tuma
-/
import Mathbin.Topology.Instances.Ennreal
import Mathbin.MeasureTheory.Measure.MeasureSpace

/-!
# Probability mass functions

This file is about probability mass functions or discrete probability measures:
a function `α → ℝ≥0` such that the values have (infinite) sum `1`.

Construction of monadic `pure` and `bind` is found in `probability_mass_function/monad.lean`,
other constructions of `pmf`s are found in `probability_mass_function/constructions.lean`.

Given `p : pmf α`, `pmf.to_outer_measure` constructs an `outer_measure` on `α`,
by assigning each set the sum of the probabilities of each of its elements.
Under this outer measure, every set is Carathéodory-measurable,
so we can further extend this to a `measure` on `α`, see `pmf.to_measure`.
`pmf.to_measure.is_probability_measure` shows this associated measure is a probability measure.

## Tags

probability mass function, discrete probability measure
-/


noncomputable section

variable {α β γ : Type _}

open Classical BigOperators Nnreal Ennreal

/-- A probability mass function, or discrete probability measures is a function `α → ℝ≥0` such that
  the values have (infinite) sum `1`. -/
def Pmf.{u} (α : Type u) : Type u :=
  { f : α → ℝ≥0 // HasSum f 1 }

namespace Pmf

instance : CoeFun (Pmf α) fun p => α → ℝ≥0 :=
  ⟨fun p a => p.1 a⟩

@[ext]
protected theorem ext : ∀ {p q : Pmf α}, (∀ a, p a = q a) → p = q
  | ⟨f, hf⟩, ⟨g, hg⟩, Eq => Subtype.eq <| funext Eq

theorem has_sum_coe_one (p : Pmf α) : HasSum p 1 :=
  p.2

theorem summable_coe (p : Pmf α) : Summable p :=
  p.has_sum_coe_one.Summable

@[simp]
theorem tsum_coe (p : Pmf α) : (∑' a, p a) = 1 :=
  p.has_sum_coe_one.tsum_eq

/-- The support of a `pmf` is the set where it is nonzero. -/
def Support (p : Pmf α) : Set α :=
  Function.Support p

@[simp]
theorem mem_support_iff (p : Pmf α) (a : α) : a ∈ p.Support ↔ p a ≠ 0 :=
  Iff.rfl

theorem apply_eq_zero_iff (p : Pmf α) (a : α) : p a = 0 ↔ a ∉ p.Support := by
  rw [mem_support_iff, not_not]

theorem coe_le_one (p : Pmf α) (a : α) : p a ≤ 1 :=
  has_sum_le
    (by
      intro b
      split_ifs <;> simp only [← h, ← zero_le'])
    (has_sum_ite_eq a (p a)) (has_sum_coe_one p)

section OuterMeasure

open MeasureTheory MeasureTheory.OuterMeasure

/-- Construct an `outer_measure` from a `pmf`, by assigning measure to each set `s : set α` equal
  to the sum of `p x` for for each `x ∈ α` -/
def toOuterMeasure (p : Pmf α) : OuterMeasure α :=
  OuterMeasure.sum fun x : α => p x • dirac x

variable (p : Pmf α) (s t : Set α)

theorem to_outer_measure_apply : p.toOuterMeasure s = ∑' x, s.indicator (coe ∘ p) x :=
  tsum_congr fun x => smul_dirac_apply (p x) x s

theorem to_outer_measure_apply' : p.toOuterMeasure s = ↑(∑' x : α, s.indicator p x) := by
  simp only [← Ennreal.coe_tsum (Nnreal.indicator_summable (summable_coe p) s), ← Ennreal.coe_indicator, ←
    to_outer_measure_apply]

@[simp]
theorem to_outer_measure_apply_finset (s : Finset α) : p.toOuterMeasure s = ∑ x in s, ↑(p x) := by
  refine' (to_outer_measure_apply p s).trans ((@tsum_eq_sum _ _ _ _ _ _ s _).trans _)
  · exact fun x hx => Set.indicator_of_not_mem hx _
    
  · exact Finset.sum_congr rfl fun x hx => Set.indicator_of_mem hx _
    

theorem to_outer_measure_apply_eq_zero_iff : p.toOuterMeasure s = 0 ↔ Disjoint p.Support s := by
  rw [to_outer_measure_apply', Ennreal.coe_eq_zero, tsum_eq_zero_iff (Nnreal.indicator_summable (summable_coe p) s)]
  exact function.funext_iff.symm.trans Set.indicator_eq_zero'

theorem to_outer_measure_apply_eq_one_iff : p.toOuterMeasure s = 1 ↔ p.Support ⊆ s := by
  rw [to_outer_measure_apply', Ennreal.coe_eq_one]
  refine' ⟨fun h a ha => _, fun h => _⟩
  · have hsp : ∀ x, s.indicator p x ≤ p x := fun _ => Set.indicator_apply_le fun _ => le_rfl
    have := fun hpa => ne_of_ltₓ (Nnreal.tsum_lt_tsum hsp hpa p.summable_coe) (h.trans p.tsum_coe.symm)
    exact
      not_not.1 fun has =>
        ha <|
          Set.indicator_apply_eq_self.1 (le_antisymmₓ (Set.indicator_apply_le fun _ => le_rfl) <| le_of_not_ltₓ <| this)
            has
    
  · suffices : ∀ x, x ∉ s → p x = 0
    exact trans (tsum_congr fun a => (Set.indicator_apply s p a).trans (ite_eq_left_iff.2 <| symm ∘ this a)) p.tsum_coe
    exact fun a ha => (p.apply_eq_zero_iff a).2 <| Set.not_mem_subset h ha
    

@[simp]
theorem to_outer_measure_apply_inter_support : p.toOuterMeasure (s ∩ p.Support) = p.toOuterMeasure s := by
  simp only [← to_outer_measure_apply', ← Ennreal.coe_eq_coe, ← Pmf.Support, ← Set.indicator_inter_support]

/-- Slightly stronger than `outer_measure.mono` having an intersection with `p.support` -/
theorem to_outer_measure_mono {s t : Set α} (h : s ∩ p.Support ⊆ t) : p.toOuterMeasure s ≤ p.toOuterMeasure t :=
  le_transₓ (le_of_eqₓ (to_outer_measure_apply_inter_support p s).symm) (p.toOuterMeasure.mono h)

theorem to_outer_measure_apply_eq_of_inter_support_eq {s t : Set α} (h : s ∩ p.Support = t ∩ p.Support) :
    p.toOuterMeasure s = p.toOuterMeasure t :=
  le_antisymmₓ (p.to_outer_measure_mono (h.symm ▸ Set.inter_subset_left t p.Support))
    (p.to_outer_measure_mono (h ▸ Set.inter_subset_left s p.Support))

@[simp]
theorem to_outer_measure_apply_fintype [Fintype α] : p.toOuterMeasure s = ↑(∑ x, s.indicator p x) :=
  (p.to_outer_measure_apply' s).trans (Ennreal.coe_eq_coe.2 <| tsum_eq_sum fun x h => absurd (Finset.mem_univ x) h)

@[simp]
theorem to_outer_measure_caratheodory (p : Pmf α) : (toOuterMeasure p).caratheodory = ⊤ := by
  refine' eq_top_iff.2 <| le_transₓ (le_Inf fun x hx => _) (le_sum_caratheodory _)
  obtain ⟨y, hy⟩ := hx
  exact ((le_of_eqₓ (dirac_caratheodory y).symm).trans (le_smul_caratheodory _ _)).trans (le_of_eqₓ hy)

end OuterMeasure

section Measureₓ

open MeasureTheory

/-- Since every set is Carathéodory-measurable under `pmf.to_outer_measure`,
  we can further extend this `outer_measure` to a `measure` on `α` -/
def toMeasure [MeasurableSpace α] (p : Pmf α) : Measureₓ α :=
  p.toOuterMeasure.toMeasure ((to_outer_measure_caratheodory p).symm ▸ le_top)

variable [MeasurableSpace α] (p : Pmf α) (s t : Set α)

theorem to_outer_measure_apply_le_to_measure_apply : p.toOuterMeasure s ≤ p.toMeasure s :=
  le_to_measure_apply p.toOuterMeasure _ s

theorem to_measure_apply_eq_to_outer_measure_apply (hs : MeasurableSet s) : p.toMeasure s = p.toOuterMeasure s :=
  to_measure_apply p.toOuterMeasure _ hs

theorem to_measure_apply (hs : MeasurableSet s) : p.toMeasure s = ∑' x, s.indicator (coe ∘ p) x :=
  (p.to_measure_apply_eq_to_outer_measure_apply s hs).trans (p.to_outer_measure_apply s)

theorem to_measure_apply' (hs : MeasurableSet s) : p.toMeasure s = ↑(∑' x, s.indicator p x) :=
  (p.to_measure_apply_eq_to_outer_measure_apply s hs).trans (p.to_outer_measure_apply' s)

theorem to_measure_apply_eq_one_iff (hs : MeasurableSet s) : p.toMeasure s = 1 ↔ p.Support ⊆ s :=
  (p.to_measure_apply_eq_to_outer_measure_apply s hs : p.toMeasure s = p.toOuterMeasure s).symm ▸
    p.to_outer_measure_apply_eq_one_iff s

@[simp]
theorem to_measure_apply_inter_support (hs : MeasurableSet s) (hp : MeasurableSet p.Support) :
    p.toMeasure (s ∩ p.Support) = p.toMeasure s := by
  simp [← p.to_measure_apply_eq_to_outer_measure_apply s hs, ←
    p.to_measure_apply_eq_to_outer_measure_apply _ (hs.inter hp)]

theorem to_measure_mono {s t : Set α} (hs : MeasurableSet s) (ht : MeasurableSet t) (h : s ∩ p.Support ⊆ t) :
    p.toMeasure s ≤ p.toMeasure t := by
  simpa only [← p.to_measure_apply_eq_to_outer_measure_apply, ← hs, ← ht] using to_outer_measure_mono p h

theorem to_measure_apply_eq_of_inter_support_eq {s t : Set α} (hs : MeasurableSet s) (ht : MeasurableSet t)
    (h : s ∩ p.Support = t ∩ p.Support) : p.toMeasure s = p.toMeasure t := by
  simpa only [← p.to_measure_apply_eq_to_outer_measure_apply, ← hs, ← ht] using
    to_outer_measure_apply_eq_of_inter_support_eq p h

section MeasurableSingletonClass

variable [MeasurableSingletonClass α]

@[simp]
theorem to_measure_apply_finset (s : Finset α) : p.toMeasure s = ∑ x in s, (p x : ℝ≥0∞) :=
  (p.to_measure_apply_eq_to_outer_measure_apply s s.MeasurableSet).trans (p.to_outer_measure_apply_finset s)

theorem to_measure_apply_of_finite (hs : s.Finite) : p.toMeasure s = ↑(∑' x, s.indicator p x) :=
  (p.to_measure_apply_eq_to_outer_measure_apply s hs.MeasurableSet).trans (p.to_outer_measure_apply' s)

@[simp]
theorem to_measure_apply_fintype [Fintype α] : p.toMeasure s = ↑(∑ x, s.indicator p x) :=
  (p.to_measure_apply_eq_to_outer_measure_apply s s.to_finite.MeasurableSet).trans (p.to_outer_measure_apply_fintype s)

end MeasurableSingletonClass

/-- The measure associated to a `pmf` by `to_measure` is a probability measure -/
instance toMeasure.is_probability_measure (p : Pmf α) : IsProbabilityMeasure p.toMeasure :=
  ⟨by
    simpa only [← MeasurableSet.univ, ← to_measure_apply_eq_to_outer_measure_apply, ← Set.indicator_univ, ←
      to_outer_measure_apply', ← Ennreal.coe_eq_one] using tsum_coe p⟩

end Measureₓ

end Pmf

