/-
Copyright (c) 2021 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
import Mathbin.MeasureTheory.Measure.VectorMeasure

/-!
# Complex measure

This file proves some elementary results about complex measures. In particular, we prove that
a complex measure is always in the form `s + it` where `s` and `t` are signed measures.

The complex measure is defined to be vector measure over `ℂ`, this definition can be found
in `measure_theory.measure.vector_measure` and is known as `measure_theory.complex_measure`.

## Main definitions

* `measure_theory.complex_measure.re`: obtains a signed measure `s` from a complex measure `c`
  such that `s i = (c i).re` for all measurable sets `i`.
* `measure_theory.complex_measure.im`: obtains a signed measure `s` from a complex measure `c`
  such that `s i = (c i).im` for all measurable sets `i`.
* `measure_theory.signed_measure.to_complex_measure`: given two signed measures `s` and `t`,
  `s.to_complex_measure t` provides a complex measure of the form `s + it`.
* `measure_theory.complex_measure.equiv_signed_measure`: is the equivalence between the complex
  measures and the type of the product of the signed measures with itself.

# Tags

Complex measure
-/


noncomputable section

open Classical MeasureTheory Ennreal Nnreal

variable {α β : Type _} {m : MeasurableSpace α}

namespace MeasureTheory

open VectorMeasure

namespace ComplexMeasure

include m

/-- The real part of a complex measure is a signed measure. -/
@[simps apply]
def re : ComplexMeasure α →ₗ[ℝ] SignedMeasure α :=
  mapRangeₗ Complex.reClm Complex.continuous_re

/-- The imaginary part of a complex measure is a signed measure. -/
@[simps apply]
def im : ComplexMeasure α →ₗ[ℝ] SignedMeasure α :=
  mapRangeₗ Complex.imClm Complex.continuous_im

/-- Given `s` and `t` signed measures, `s + it` is a complex measure-/
@[simps]
def _root_.measure_theory.signed_measure.to_complex_measure (s t : SignedMeasure α) : ComplexMeasure α where
  measureOf' := fun i => ⟨s i, t i⟩
  empty' := by
    rw [s.empty, t.empty] <;> rfl
  not_measurable' := fun i hi => by
    rw [s.not_measurable hi, t.not_measurable hi] <;> rfl
  m_Union' := fun f hf hfdisj => (Complex.has_sum_iff _ _).2 ⟨s.m_Union hf hfdisj, t.m_Union hf hfdisj⟩

theorem _root_.measure_theory.signed_measure.to_complex_measure_apply {s t : SignedMeasure α} {i : Set α} :
    s.toComplexMeasure t i = ⟨s i, t i⟩ :=
  rfl

theorem to_complex_measure_to_signed_measure (c : ComplexMeasure α) : c.re.toComplexMeasure c.im = c := by
  ext i hi <;> rfl

theorem _root_.measure_theory.signed_measure.re_to_complex_measure (s t : SignedMeasure α) :
    (s.toComplexMeasure t).re = s := by
  ext i hi
  rfl

theorem _root_.measure_theory.signed_measure.im_to_complex_measure (s t : SignedMeasure α) :
    (s.toComplexMeasure t).im = t := by
  ext i hi
  rfl

/-- The complex measures form an equivalence to the type of pairs of signed measures. -/
@[simps]
def equivSignedMeasure : ComplexMeasure α ≃ SignedMeasure α × SignedMeasure α where
  toFun := fun c => ⟨c.re, c.im⟩
  invFun := fun ⟨s, t⟩ => s.toComplexMeasure t
  left_inv := fun c => c.to_complex_measure_to_signed_measure
  right_inv := fun ⟨s, t⟩ => Prod.mk.inj_iff.2 ⟨s.re_to_complex_measure t, s.im_to_complex_measure t⟩

section

variable {R : Type _} [Semiringₓ R] [Module R ℝ]

variable [HasContinuousConstSmul R ℝ] [HasContinuousConstSmul R ℂ]

/-- The complex measures form an linear isomorphism to the type of pairs of signed measures. -/
@[simps]
def equivSignedMeasureₗ : ComplexMeasure α ≃ₗ[R] SignedMeasure α × SignedMeasure α :=
  { equivSignedMeasure with
    map_add' := fun c d => by
      ext i hi <;> rfl,
    map_smul' := by
      intro r c
      ext i hi
      · change (r • c i).re = r • (c i).re
        simp [← Complex.smul_re]
        
      · ext i hi
        change (r • c i).im = r • (c i).im
        simp [← Complex.smul_im]
         }

end

theorem absolutely_continuous_ennreal_iff (c : ComplexMeasure α) (μ : VectorMeasure α ℝ≥0∞) :
    c ≪ᵥ μ ↔ c.re ≪ᵥ μ ∧ c.im ≪ᵥ μ := by
  constructor <;> intro h
  · constructor <;>
      · intro i hi
        simp [← h hi]
        
    
  · intro i hi
    rw [← Complex.re_add_im (c i), (_ : (c i).re = 0), (_ : (c i).im = 0)]
    exacts[by
      simp , h.2 hi, h.1 hi]
    

end ComplexMeasure

end MeasureTheory

