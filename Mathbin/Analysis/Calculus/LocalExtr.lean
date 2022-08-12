/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathbin.Analysis.Calculus.Deriv
import Mathbin.Data.Polynomial.FieldDivision
import Mathbin.Topology.Algebra.Order.ExtendFrom
import Mathbin.Topology.Algebra.Polynomial
import Mathbin.Topology.LocalExtr

/-!
# Local extrema of smooth functions

## Main definitions

In a real normed space `E` we define `pos_tangent_cone_at (s : set E) (x : E)`.
This would be the same as `tangent_cone_at ℝ≥0 s x` if we had a theory of normed semifields.
This set is used in the proof of Fermat's Theorem (see below), and can be used to formalize
[Lagrange multipliers](https://en.wikipedia.org/wiki/Lagrange_multiplier) and/or
[Karush–Kuhn–Tucker conditions](https://en.wikipedia.org/wiki/Karush–Kuhn–Tucker_conditions).

## Main statements

For each theorem name listed below,
we also prove similar theorems for `min`, `extr` (if applicable)`,
and `(f)deriv` instead of `has_fderiv`.

* `is_local_max_on.has_fderiv_within_at_nonpos` : `f' y ≤ 0` whenever `a` is a local maximum
  of `f` on `s`, `f` has derivative `f'` at `a` within `s`, and `y` belongs to the positive tangent
  cone of `s` at `a`.

* `is_local_max_on.has_fderiv_within_at_eq_zero` : In the settings of the previous theorem, if both
  `y` and `-y` belong to the positive tangent cone, then `f' y = 0`.

* `is_local_max.has_fderiv_at_eq_zero` :
  [Fermat's Theorem](https://en.wikipedia.org/wiki/Fermat's_theorem_(stationary_points)),
  the derivative of a differentiable function at a local extremum point equals zero.

* `exists_has_deriv_at_eq_zero` :
  [Rolle's Theorem](https://en.wikipedia.org/wiki/Rolle's_theorem): given a function `f` continuous
  on `[a, b]` and differentiable on `(a, b)`, there exists `c ∈ (a, b)` such that `f' c = 0`.

## Implementation notes

For each mathematical fact we prove several versions of its formalization:

* for maxima and minima;
* using `has_fderiv*`/`has_deriv*` or `fderiv*`/`deriv*`.

For the `fderiv*`/`deriv*` versions we omit the differentiability condition whenever it is possible
due to the fact that `fderiv` and `deriv` are defined to be zero for non-differentiable functions.

## References

* [Fermat's Theorem](https://en.wikipedia.org/wiki/Fermat's_theorem_(stationary_points));
* [Rolle's Theorem](https://en.wikipedia.org/wiki/Rolle's_theorem);
* [Tangent cone](https://en.wikipedia.org/wiki/Tangent_cone);

## Tags

local extremum, Fermat's Theorem, Rolle's Theorem
-/


universe u v

open Filter Set

open TopologicalSpace Classical Polynomial

section Module

variable {E : Type u} [NormedGroup E] [NormedSpace ℝ E] {f : E → ℝ} {a : E} {f' : E →L[ℝ] ℝ}

/-- "Positive" tangent cone to `s` at `x`; the only difference from `tangent_cone_at`
is that we require `c n → ∞` instead of `∥c n∥ → ∞`. One can think about `pos_tangent_cone_at`
as `tangent_cone_at nnreal` but we have no theory of normed semifields yet. -/
def PosTangentConeAt (s : Set E) (x : E) : Set E :=
  { y : E |
    ∃ (c : ℕ → ℝ)(d : ℕ → E),
      (∀ᶠ n in at_top, x + d n ∈ s) ∧ Tendsto c atTop atTop ∧ Tendsto (fun n => c n • d n) atTop (𝓝 y) }

theorem pos_tangent_cone_at_mono : Monotone fun s => PosTangentConeAt s a := by
  rintro s t hst y ⟨c, d, hd, hc, hcd⟩
  exact ⟨c, d, (mem_of_superset hd) fun h hn => hst hn, hc, hcd⟩

theorem mem_pos_tangent_cone_at_of_segment_subset {s : Set E} {x y : E} (h : Segment ℝ x y ⊆ s) :
    y - x ∈ PosTangentConeAt s x := by
  let c := fun n : ℕ => (2 : ℝ) ^ n
  let d := fun n : ℕ => (c n)⁻¹ • (y - x)
  refine' ⟨c, d, Filter.univ_mem' fun n => h _, tendsto_pow_at_top_at_top_of_one_lt one_lt_two, _⟩
  show x + d n ∈ Segment ℝ x y
  · rw [segment_eq_image']
    refine' ⟨(c n)⁻¹, ⟨_, _⟩, rfl⟩
    exacts[inv_nonneg.2 (pow_nonneg zero_le_two _), inv_le_one (one_le_pow_of_one_le one_le_two _)]
    
  show tendsto (fun n => c n • d n) at_top (𝓝 (y - x))
  · convert tendsto_const_nhds
    ext n
    simp only [← d, ← smul_smul]
    rw [mul_inv_cancel, one_smul]
    exact pow_ne_zero _ two_ne_zero
    

theorem mem_pos_tangent_cone_at_of_segment_subset' {s : Set E} {x y : E} (h : Segment ℝ x (x + y) ⊆ s) :
    y ∈ PosTangentConeAt s x := by
  simpa only [← add_sub_cancel'] using mem_pos_tangent_cone_at_of_segment_subset h

theorem pos_tangent_cone_at_univ : PosTangentConeAt Univ a = univ :=
  eq_univ_of_forall fun x => mem_pos_tangent_cone_at_of_segment_subset' (subset_univ _)

/-- If `f` has a local max on `s` at `a`, `f'` is the derivative of `f` at `a` within `s`, and
`y` belongs to the positive tangent cone of `s` at `a`, then `f' y ≤ 0`. -/
theorem IsLocalMaxOn.has_fderiv_within_at_nonpos {s : Set E} (h : IsLocalMaxOn f s a) (hf : HasFderivWithinAt f f' s a)
    {y} (hy : y ∈ PosTangentConeAt s a) : f' y ≤ 0 := by
  rcases hy with ⟨c, d, hd, hc, hcd⟩
  have hc' : tendsto (fun n => ∥c n∥) at_top at_top := tendsto_at_top_mono (fun n => le_abs_self _) hc
  refine' le_of_tendsto (hf.lim at_top hd hc' hcd) _
  replace hd : tendsto (fun n => a + d n) at_top (𝓝[s] (a + 0))
  exact
    tendsto_inf.2
      ⟨tendsto_const_nhds.add (TangentConeAt.lim_zero _ hc' hcd), by
        rwa [tendsto_principal]⟩
  rw [add_zeroₓ] at hd
  replace h : ∀ᶠ n in at_top, f (a + d n) ≤ f a
  exact mem_map.1 (hd h)
  replace hc : ∀ᶠ n in at_top, 0 ≤ c n
  exact mem_map.1 (hc (mem_at_top (0 : ℝ)))
  filter_upwards [h, hc]
  simp only [← smul_eq_mul, ← mem_preimage, ← subset_def]
  intro n hnf hn
  exact mul_nonpos_of_nonneg_of_nonpos hn (sub_nonpos.2 hnf)

/-- If `f` has a local max on `s` at `a` and `y` belongs to the positive tangent cone
of `s` at `a`, then `f' y ≤ 0`. -/
theorem IsLocalMaxOn.fderiv_within_nonpos {s : Set E} (h : IsLocalMaxOn f s a) {y} (hy : y ∈ PosTangentConeAt s a) :
    (fderivWithin ℝ f s a : E → ℝ) y ≤ 0 :=
  if hf : DifferentiableWithinAt ℝ f s a then h.has_fderiv_within_at_nonpos hf.HasFderivWithinAt hy
  else by
    rw [fderiv_within_zero_of_not_differentiable_within_at hf]
    rfl

/-- If `f` has a local max on `s` at `a`, `f'` is a derivative of `f` at `a` within `s`, and
both `y` and `-y` belong to the positive tangent cone of `s` at `a`, then `f' y ≤ 0`. -/
theorem IsLocalMaxOn.has_fderiv_within_at_eq_zero {s : Set E} (h : IsLocalMaxOn f s a) (hf : HasFderivWithinAt f f' s a)
    {y} (hy : y ∈ PosTangentConeAt s a) (hy' : -y ∈ PosTangentConeAt s a) : f' y = 0 :=
  le_antisymmₓ (h.has_fderiv_within_at_nonpos hf hy) <| by
    simpa using h.has_fderiv_within_at_nonpos hf hy'

/-- If `f` has a local max on `s` at `a` and both `y` and `-y` belong to the positive tangent cone
of `s` at `a`, then `f' y = 0`. -/
theorem IsLocalMaxOn.fderiv_within_eq_zero {s : Set E} (h : IsLocalMaxOn f s a) {y} (hy : y ∈ PosTangentConeAt s a)
    (hy' : -y ∈ PosTangentConeAt s a) : (fderivWithin ℝ f s a : E → ℝ) y = 0 :=
  if hf : DifferentiableWithinAt ℝ f s a then h.has_fderiv_within_at_eq_zero hf.HasFderivWithinAt hy hy'
  else by
    rw [fderiv_within_zero_of_not_differentiable_within_at hf]
    rfl

/-- If `f` has a local min on `s` at `a`, `f'` is the derivative of `f` at `a` within `s`, and
`y` belongs to the positive tangent cone of `s` at `a`, then `0 ≤ f' y`. -/
theorem IsLocalMinOn.has_fderiv_within_at_nonneg {s : Set E} (h : IsLocalMinOn f s a) (hf : HasFderivWithinAt f f' s a)
    {y} (hy : y ∈ PosTangentConeAt s a) : 0 ≤ f' y := by
  simpa using h.neg.has_fderiv_within_at_nonpos hf.neg hy

/-- If `f` has a local min on `s` at `a` and `y` belongs to the positive tangent cone
of `s` at `a`, then `0 ≤ f' y`. -/
theorem IsLocalMinOn.fderiv_within_nonneg {s : Set E} (h : IsLocalMinOn f s a) {y} (hy : y ∈ PosTangentConeAt s a) :
    (0 : ℝ) ≤ (fderivWithin ℝ f s a : E → ℝ) y :=
  if hf : DifferentiableWithinAt ℝ f s a then h.has_fderiv_within_at_nonneg hf.HasFderivWithinAt hy
  else by
    rw [fderiv_within_zero_of_not_differentiable_within_at hf]
    rfl

/-- If `f` has a local max on `s` at `a`, `f'` is a derivative of `f` at `a` within `s`, and
both `y` and `-y` belong to the positive tangent cone of `s` at `a`, then `f' y ≤ 0`. -/
theorem IsLocalMinOn.has_fderiv_within_at_eq_zero {s : Set E} (h : IsLocalMinOn f s a) (hf : HasFderivWithinAt f f' s a)
    {y} (hy : y ∈ PosTangentConeAt s a) (hy' : -y ∈ PosTangentConeAt s a) : f' y = 0 := by
  simpa using h.neg.has_fderiv_within_at_eq_zero hf.neg hy hy'

/-- If `f` has a local min on `s` at `a` and both `y` and `-y` belong to the positive tangent cone
of `s` at `a`, then `f' y = 0`. -/
theorem IsLocalMinOn.fderiv_within_eq_zero {s : Set E} (h : IsLocalMinOn f s a) {y} (hy : y ∈ PosTangentConeAt s a)
    (hy' : -y ∈ PosTangentConeAt s a) : (fderivWithin ℝ f s a : E → ℝ) y = 0 :=
  if hf : DifferentiableWithinAt ℝ f s a then h.has_fderiv_within_at_eq_zero hf.HasFderivWithinAt hy hy'
  else by
    rw [fderiv_within_zero_of_not_differentiable_within_at hf]
    rfl

/-- **Fermat's Theorem**: the derivative of a function at a local minimum equals zero. -/
theorem IsLocalMin.has_fderiv_at_eq_zero (h : IsLocalMin f a) (hf : HasFderivAt f f' a) : f' = 0 := by
  ext y
  apply (h.on univ).has_fderiv_within_at_eq_zero hf.has_fderiv_within_at <;>
    rw [pos_tangent_cone_at_univ] <;> apply mem_univ

/-- **Fermat's Theorem**: the derivative of a function at a local minimum equals zero. -/
theorem IsLocalMin.fderiv_eq_zero (h : IsLocalMin f a) : fderiv ℝ f a = 0 :=
  if hf : DifferentiableAt ℝ f a then h.has_fderiv_at_eq_zero hf.HasFderivAt
  else fderiv_zero_of_not_differentiable_at hf

/-- **Fermat's Theorem**: the derivative of a function at a local maximum equals zero. -/
theorem IsLocalMax.has_fderiv_at_eq_zero (h : IsLocalMax f a) (hf : HasFderivAt f f' a) : f' = 0 :=
  neg_eq_zero.1 <| h.neg.has_fderiv_at_eq_zero hf.neg

/-- **Fermat's Theorem**: the derivative of a function at a local maximum equals zero. -/
theorem IsLocalMax.fderiv_eq_zero (h : IsLocalMax f a) : fderiv ℝ f a = 0 :=
  if hf : DifferentiableAt ℝ f a then h.has_fderiv_at_eq_zero hf.HasFderivAt
  else fderiv_zero_of_not_differentiable_at hf

/-- **Fermat's Theorem**: the derivative of a function at a local extremum equals zero. -/
theorem IsLocalExtr.has_fderiv_at_eq_zero (h : IsLocalExtr f a) : HasFderivAt f f' a → f' = 0 :=
  h.elim IsLocalMin.has_fderiv_at_eq_zero IsLocalMax.has_fderiv_at_eq_zero

/-- **Fermat's Theorem**: the derivative of a function at a local extremum equals zero. -/
theorem IsLocalExtr.fderiv_eq_zero (h : IsLocalExtr f a) : fderiv ℝ f a = 0 :=
  h.elim IsLocalMin.fderiv_eq_zero IsLocalMax.fderiv_eq_zero

end Module

section Real

variable {f : ℝ → ℝ} {f' : ℝ} {a b : ℝ}

/-- **Fermat's Theorem**: the derivative of a function at a local minimum equals zero. -/
theorem IsLocalMin.has_deriv_at_eq_zero (h : IsLocalMin f a) (hf : HasDerivAt f f' a) : f' = 0 := by
  simpa using ContinuousLinearMap.ext_iff.1 (h.has_fderiv_at_eq_zero (has_deriv_at_iff_has_fderiv_at.1 hf)) 1

/-- **Fermat's Theorem**: the derivative of a function at a local minimum equals zero. -/
theorem IsLocalMin.deriv_eq_zero (h : IsLocalMin f a) : deriv f a = 0 :=
  if hf : DifferentiableAt ℝ f a then h.has_deriv_at_eq_zero hf.HasDerivAt else deriv_zero_of_not_differentiable_at hf

/-- **Fermat's Theorem**: the derivative of a function at a local maximum equals zero. -/
theorem IsLocalMax.has_deriv_at_eq_zero (h : IsLocalMax f a) (hf : HasDerivAt f f' a) : f' = 0 :=
  neg_eq_zero.1 <| h.neg.has_deriv_at_eq_zero hf.neg

/-- **Fermat's Theorem**: the derivative of a function at a local maximum equals zero. -/
theorem IsLocalMax.deriv_eq_zero (h : IsLocalMax f a) : deriv f a = 0 :=
  if hf : DifferentiableAt ℝ f a then h.has_deriv_at_eq_zero hf.HasDerivAt else deriv_zero_of_not_differentiable_at hf

/-- **Fermat's Theorem**: the derivative of a function at a local extremum equals zero. -/
theorem IsLocalExtr.has_deriv_at_eq_zero (h : IsLocalExtr f a) : HasDerivAt f f' a → f' = 0 :=
  h.elim IsLocalMin.has_deriv_at_eq_zero IsLocalMax.has_deriv_at_eq_zero

/-- **Fermat's Theorem**: the derivative of a function at a local extremum equals zero. -/
theorem IsLocalExtr.deriv_eq_zero (h : IsLocalExtr f a) : deriv f a = 0 :=
  h.elim IsLocalMin.deriv_eq_zero IsLocalMax.deriv_eq_zero

end Real

section Rolle

variable (f f' : ℝ → ℝ) {a b : ℝ}

/-- A continuous function on a closed interval with `f a = f b` takes either its maximum
or its minimum value at a point in the interior of the interval. -/
theorem exists_Ioo_extr_on_Icc (hab : a < b) (hfc : ContinuousOn f (Icc a b)) (hfI : f a = f b) :
    ∃ c ∈ Ioo a b, IsExtrOn f (Icc a b) c := by
  have ne : (Icc a b).Nonempty := nonempty_Icc.2 (le_of_ltₓ hab)
  -- Consider absolute min and max points
  obtain ⟨c, cmem, cle⟩ : ∃ c ∈ Icc a b, ∀, ∀ x ∈ Icc a b, ∀, f c ≤ f x
  exact is_compact_Icc.exists_forall_le Ne hfc
  obtain ⟨C, Cmem, Cge⟩ : ∃ C ∈ Icc a b, ∀, ∀ x ∈ Icc a b, ∀, f x ≤ f C
  exact is_compact_Icc.exists_forall_ge Ne hfc
  by_cases' hc : f c = f a
  · by_cases' hC : f C = f a
    · have : ∀, ∀ x ∈ Icc a b, ∀, f x = f a := fun x hx => le_antisymmₓ (hC ▸ Cge x hx) (hc ▸ cle x hx)
      -- `f` is a constant, so we can take any point in `Ioo a b`
      rcases exists_between hab with ⟨c', hc'⟩
      refine' ⟨c', hc', Or.inl _⟩
      intro x hx
      rw [mem_set_of_eq, this x hx, ← hC]
      exact Cge c' ⟨le_of_ltₓ hc'.1, le_of_ltₓ hc'.2⟩
      
    · refine' ⟨C, ⟨lt_of_le_of_neₓ Cmem.1 <| mt _ hC, lt_of_le_of_neₓ Cmem.2 <| mt _ hC⟩, Or.inr Cge⟩
      exacts[fun h => by
        rw [h], fun h => by
        rw [h, hfI]]
      
    
  · refine' ⟨c, ⟨lt_of_le_of_neₓ cmem.1 <| mt _ hc, lt_of_le_of_neₓ cmem.2 <| mt _ hc⟩, Or.inl cle⟩
    exacts[fun h => by
      rw [h], fun h => by
      rw [h, hfI]]
    

/-- A continuous function on a closed interval with `f a = f b` has a local extremum at some
point of the corresponding open interval. -/
theorem exists_local_extr_Ioo (hab : a < b) (hfc : ContinuousOn f (Icc a b)) (hfI : f a = f b) :
    ∃ c ∈ Ioo a b, IsLocalExtr f c :=
  let ⟨c, cmem, hc⟩ := exists_Ioo_extr_on_Icc f hab hfc hfI
  ⟨c, cmem, hc.IsLocalExtr <| Icc_mem_nhds cmem.1 cmem.2⟩

/-- **Rolle's Theorem** `has_deriv_at` version -/
theorem exists_has_deriv_at_eq_zero (hab : a < b) (hfc : ContinuousOn f (Icc a b)) (hfI : f a = f b)
    (hff' : ∀, ∀ x ∈ Ioo a b, ∀, HasDerivAt f (f' x) x) : ∃ c ∈ Ioo a b, f' c = 0 :=
  let ⟨c, cmem, hc⟩ := exists_local_extr_Ioo f hab hfc hfI
  ⟨c, cmem, hc.has_deriv_at_eq_zero <| hff' c cmem⟩

/-- **Rolle's Theorem** `deriv` version -/
theorem exists_deriv_eq_zero (hab : a < b) (hfc : ContinuousOn f (Icc a b)) (hfI : f a = f b) :
    ∃ c ∈ Ioo a b, deriv f c = 0 :=
  let ⟨c, cmem, hc⟩ := exists_local_extr_Ioo f hab hfc hfI
  ⟨c, cmem, hc.deriv_eq_zero⟩

variable {f f'} {l : ℝ}

/-- **Rolle's Theorem**, a version for a function on an open interval: if `f` has derivative `f'`
on `(a, b)` and has the same limit `l` at `𝓝[>] a` and `𝓝[<] b`, then `f' c = 0`
for some `c ∈ (a, b)`.  -/
theorem exists_has_deriv_at_eq_zero' (hab : a < b) (hfa : Tendsto f (𝓝[>] a) (𝓝 l)) (hfb : Tendsto f (𝓝[<] b) (𝓝 l))
    (hff' : ∀, ∀ x ∈ Ioo a b, ∀, HasDerivAt f (f' x) x) : ∃ c ∈ Ioo a b, f' c = 0 := by
  have : ContinuousOn f (Ioo a b) := fun x hx => (hff' x hx).ContinuousAt.ContinuousWithinAt
  have hcont := continuous_on_Icc_extend_from_Ioo hab.ne this hfa hfb
  obtain ⟨c, hc, hcextr⟩ : ∃ c ∈ Ioo a b, IsLocalExtr (extendFrom (Ioo a b) f) c := by
    apply exists_local_extr_Ioo _ hab hcont
    rw [eq_lim_at_right_extend_from_Ioo hab hfb]
    exact eq_lim_at_left_extend_from_Ioo hab hfa
  use c, hc
  apply (hcextr.congr _).has_deriv_at_eq_zero (hff' c hc)
  rw [eventually_eq_iff_exists_mem]
  exact ⟨Ioo a b, Ioo_mem_nhds hc.1 hc.2, extend_from_extends this⟩

/-- **Rolle's Theorem**, a version for a function on an open interval: if `f` has the same limit
`l` at `𝓝[>] a` and `𝓝[<] b`, then `deriv f c = 0` for some `c ∈ (a, b)`. This version
does not require differentiability of `f` because we define `deriv f c = 0` whenever `f` is not
differentiable at `c`. -/
theorem exists_deriv_eq_zero' (hab : a < b) (hfa : Tendsto f (𝓝[>] a) (𝓝 l)) (hfb : Tendsto f (𝓝[<] b) (𝓝 l)) :
    ∃ c ∈ Ioo a b, deriv f c = 0 :=
  Classical.by_cases
    (fun h : ∀, ∀ x ∈ Ioo a b, ∀, DifferentiableAt ℝ f x =>
      show ∃ c ∈ Ioo a b, deriv f c = 0 from exists_has_deriv_at_eq_zero' hab hfa hfb fun x hx => (h x hx).HasDerivAt)
    fun h : ¬∀, ∀ x ∈ Ioo a b, ∀, DifferentiableAt ℝ f x =>
    have h : ∃ x, x ∈ Ioo a b ∧ ¬DifferentiableAt ℝ f x := by
      push_neg  at h
      exact h
    let ⟨c, hc, hcdiff⟩ := h
    ⟨c, hc, deriv_zero_of_not_differentiable_at hcdiff⟩

end Rolle

namespace Polynomial

theorem card_root_set_le_derivative {F : Type _} [Field F] [Algebra F ℝ] (p : F[X]) :
    Fintype.card (p.RootSet ℝ) ≤ Fintype.card (p.derivative.RootSet ℝ) + 1 := by
  have : CharZero F :=
    (RingHom.char_zero_iff (algebraMap F ℝ).Injective).mpr
      (by
        infer_instance)
  by_cases' hp : p = 0
  · simp_rw [hp, derivative_zero, root_set_zero, Set.empty_card', zero_le_one]
    
  by_cases' hp' : p.derivative = 0
  · rw [eq_C_of_nat_degree_eq_zero (nat_degree_eq_zero_of_derivative_eq_zero hp')]
    simp_rw [root_set_C, Set.empty_card', zero_le]
    
  simp_rw [root_set_def, Finset.coe_sort_coe, Fintype.card_coe]
  refine' Finset.card_le_of_interleaved fun x hx y hy hxy => _
  rw [← Finset.mem_coe, ← root_set_def, mem_root_set hp] at hx hy
  obtain ⟨z, hz1, hz2⟩ :=
    exists_deriv_eq_zero (fun x : ℝ => aeval x p) hxy p.continuous_aeval.continuous_on (hx.trans hy.symm)
  refine' ⟨z, _, hz1⟩
  rw [← Finset.mem_coe, ← root_set_def, mem_root_set hp', ← hz2]
  simp_rw [aeval_def, ← eval_map, Polynomial.deriv, derivative_map]

end Polynomial

