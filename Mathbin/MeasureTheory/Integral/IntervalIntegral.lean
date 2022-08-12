/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov, Patrick Massot, Sébastien Gouëzel
-/
import Mathbin.Analysis.NormedSpace.Dual
import Mathbin.Data.Set.Intervals.Disjoint
import Mathbin.MeasureTheory.Measure.HaarLebesgue
import Mathbin.Analysis.Calculus.ExtendDeriv
import Mathbin.MeasureTheory.Function.LocallyIntegrable
import Mathbin.MeasureTheory.Integral.SetIntegral
import Mathbin.MeasureTheory.Integral.VitaliCaratheodory
import Mathbin.Analysis.Calculus.FderivMeasurable

/-!
# Integral over an interval

In this file we define `∫ x in a..b, f x ∂μ` to be `∫ x in Ioc a b, f x ∂μ` if `a ≤ b` and
`-∫ x in Ioc b a, f x ∂μ` if `b ≤ a`. We prove a few simple properties and several versions of the
[fundamental theorem of calculus](https://en.wikipedia.org/wiki/Fundamental_theorem_of_calculus).

Recall that its first version states that the function `(u, v) ↦ ∫ x in u..v, f x` has derivative
`(δu, δv) ↦ δv • f b - δu • f a` at `(a, b)` provided that `f` is continuous at `a` and `b`,
and its second version states that, if `f` has an integrable derivative on `[a, b]`, then
`∫ x in a..b, f' x = f b - f a`.

## Main statements

### FTC-1 for Lebesgue measure

We prove several versions of FTC-1, all in the `interval_integral` namespace. Many of them follow
the naming scheme `integral_has(_strict?)_(f?)deriv(_within?)_at(_of_tendsto_ae?)(_right|_left?)`.
They formulate FTC in terms of `has(_strict?)_(f?)deriv(_within?)_at`.
Let us explain the meaning of each part of the name:

* `_strict` means that the theorem is about strict differentiability;
* `f` means that the theorem is about differentiability in both endpoints; incompatible with
  `_right|_left`;
* `_within` means that the theorem is about one-sided derivatives, see below for details;
* `_of_tendsto_ae` means that instead of continuity the theorem assumes that `f` has a finite limit
  almost surely as `x` tends to `a` and/or `b`;
* `_right` or `_left` mean that the theorem is about differentiability in the right (resp., left)
  endpoint.

We also reformulate these theorems in terms of `(f?)deriv(_within?)`. These theorems are named
`(f?)deriv(_within?)_integral(_of_tendsto_ae?)(_right|_left?)` with the same meaning of parts of the
name.

### One-sided derivatives

Theorem `integral_has_fderiv_within_at_of_tendsto_ae` states that `(u, v) ↦ ∫ x in u..v, f x` has a
derivative `(δu, δv) ↦ δv • cb - δu • ca` within the set `s × t` at `(a, b)` provided that `f` tends
to `ca` (resp., `cb`) almost surely at `la` (resp., `lb`), where possible values of `s`, `t`, and
corresponding filters `la`, `lb` are given in the following table.

| `s`     | `la`     | `t`     | `lb`     |
| ------- | ----     | ---     | ----     |
| `Iic a` | `𝓝[≤] a` | `Iic b` | `𝓝[≤] b` |
| `Ici a` | `𝓝[>] a` | `Ici b` | `𝓝[>] b` |
| `{a}`   | `⊥`      | `{b}`   | `⊥`      |
| `univ`  | `𝓝 a`    | `univ`  | `𝓝 b`    |

We use a typeclass `FTC_filter` to make Lean automatically find `la`/`lb` based on `s`/`t`. This way
we can formulate one theorem instead of `16` (or `8` if we leave only non-trivial ones not covered
by `integral_has_deriv_within_at_of_tendsto_ae_(left|right)` and
`integral_has_fderiv_at_of_tendsto_ae`). Similarly,
`integral_has_deriv_within_at_of_tendsto_ae_right` works for both one-sided derivatives using the
same typeclass to find an appropriate filter.

### FTC for a locally finite measure

Before proving FTC for the Lebesgue measure, we prove a few statements that can be seen as FTC for
any measure. The most general of them,
`measure_integral_sub_integral_sub_linear_is_o_of_tendsto_ae`, states the following. Let `(la, la')`
be an `FTC_filter` pair of filters around `a` (i.e., `FTC_filter a la la'`) and let `(lb, lb')` be
an `FTC_filter` pair of filters around `b`. If `f` has finite limits `ca` and `cb` almost surely at
`la'` and `lb'`, respectively, then
`∫ x in va..vb, f x ∂μ - ∫ x in ua..ub, f x ∂μ = ∫ x in ub..vb, cb ∂μ - ∫ x in ua..va, ca ∂μ +
  o(∥∫ x in ua..va, (1:ℝ) ∂μ∥ + ∥∫ x in ub..vb, (1:ℝ) ∂μ∥)` as `ua` and `va` tend to `la` while
`ub` and `vb` tend to `lb`.

### FTC-2 and corollaries

We use FTC-1 to prove several versions of FTC-2 for the Lebesgue measure, using a similar naming
scheme as for the versions of FTC-1. They include:
* `interval_integral.integral_eq_sub_of_has_deriv_right_of_le` - most general version, for functions
  with a right derivative
* `interval_integral.integral_eq_sub_of_has_deriv_at'` - version for functions with a derivative on
  an open set
* `interval_integral.integral_deriv_eq_sub'` - version that is easiest to use when computing the
  integral of a specific function

We then derive additional integration techniques from FTC-2:
* `interval_integral.integral_mul_deriv_eq_deriv_mul` - integration by parts
* `interval_integral.integral_comp_mul_deriv''` - integration by substitution

Many applications of these theorems can be found in the file `analysis.special_functions.integrals`.

Note that the assumptions of FTC-2 are formulated in the form that `f'` is integrable. To use it in
a context with the stronger assumption that `f'` is continuous, one can use
`continuous_on.interval_integrable` or `continuous_on.integrable_on_Icc` or
`continuous_on.integrable_on_interval`.

## Implementation notes

### Avoiding `if`, `min`, and `max`

In order to avoid `if`s in the definition, we define `interval_integrable f μ a b` as
`integrable_on f (Ioc a b) μ ∧ integrable_on f (Ioc b a) μ`. For any `a`, `b` one of these
intervals is empty and the other coincides with `set.interval_oc a b = set.Ioc (min a b) (max a b)`.

Similarly, we define `∫ x in a..b, f x ∂μ` to be `∫ x in Ioc a b, f x ∂μ - ∫ x in Ioc b a, f x ∂μ`.
Again, for any `a`, `b` one of these integrals is zero, and the other gives the expected result.

This way some properties can be translated from integrals over sets without dealing with
the cases `a ≤ b` and `b ≤ a` separately.

### Choice of the interval

We use integral over `set.interval_oc a b = set.Ioc (min a b) (max a b)` instead of one of the other
three possible intervals with the same endpoints for two reasons:

* this way `∫ x in a..b, f x ∂μ + ∫ x in b..c, f x ∂μ = ∫ x in a..c, f x ∂μ` holds whenever
  `f` is integrable on each interval; in particular, it works even if the measure `μ` has an atom
  at `b`; this rules out `set.Ioo` and `set.Icc` intervals;
* with this definition for a probability measure `μ`, the integral `∫ x in a..b, 1 ∂μ` equals
  the difference $F_μ(b)-F_μ(a)$, where $F_μ(a)=μ(-∞, a]$ is the
  [cumulative distribution function](https://en.wikipedia.org/wiki/Cumulative_distribution_function)
  of `μ`.

### `FTC_filter` class

As explained above, many theorems in this file rely on the typeclass
`FTC_filter (a : ℝ) (l l' : filter ℝ)` to avoid code duplication. This typeclass combines four
assumptions:

- `pure a ≤ l`;
- `l' ≤ 𝓝 a`;
- `l'` has a basis of measurable sets;
- if `u n` and `v n` tend to `l`, then for any `s ∈ l'`, `Ioc (u n) (v n)` is eventually included
  in `s`.

This typeclass has the following “real” instances: `(a, pure a, ⊥)`, `(a, 𝓝[≥] a, 𝓝[>] a)`,
`(a, 𝓝[≤] a, 𝓝[≤] a)`, `(a, 𝓝 a, 𝓝 a)`.
Furthermore, we have the following instances that are equal to the previously mentioned instances:
`(a, 𝓝[{a}] a, ⊥)` and `(a, 𝓝[univ] a, 𝓝[univ] a)`.
While the difference between `Ici a` and `Ioi a` doesn't matter for theorems about Lebesgue measure,
it becomes important in the versions of FTC about any locally finite measure if this measure has an
atom at one of the endpoints.

### Combining one-sided and two-sided derivatives

There are some `FTC_filter` instances where the fact that it is one-sided or
two-sided depends on the point, namely `(x, 𝓝[Icc a b] x, 𝓝[Icc a b] x)`
(resp. `(x, 𝓝[[a, b]] x, 𝓝[[a, b]] x)`, where `[a, b] = set.interval a b`),
with `x ∈ Icc a b` (resp. `x ∈ [a, b]`).
This results in a two-sided derivatives for `x ∈ Ioo a b` and one-sided derivatives for
`x ∈ {a, b}`. Other instances could be added when needed (in that case, one also needs to add
instances for `filter.is_measurably_generated` and `filter.tendsto_Ixx_class`).

## Tags

integral, fundamental theorem of calculus, FTC-1, FTC-2, change of variables in integrals
-/


noncomputable section

open TopologicalSpace (SecondCountableTopology)

open MeasureTheory Set Classical Filter Function

open Classical TopologicalSpace Filter Ennreal BigOperators Interval Nnreal

variable {ι 𝕜 E F : Type _} [NormedGroup E]

/-!
### Integrability at an interval
-/


/-- A function `f` is called *interval integrable* with respect to a measure `μ` on an unordered
interval `a..b` if it is integrable on both intervals `(a, b]` and `(b, a]`. One of these
intervals is always empty, so this property is equivalent to `f` being integrable on
`(min a b, max a b]`. -/
def IntervalIntegrable (f : ℝ → E) (μ : Measureₓ ℝ) (a b : ℝ) :=
  IntegrableOn f (Ioc a b) μ ∧ IntegrableOn f (Ioc b a) μ

section

variable {f : ℝ → E} {a b : ℝ} {μ : Measureₓ ℝ}

/-- A function is interval integrable with respect to a given measure `μ` on `a..b` if and
  only if it is integrable on `interval_oc a b` with respect to `μ`. This is an equivalent
  definition of `interval_integrable`. -/
theorem interval_integrable_iff : IntervalIntegrable f μ a b ↔ IntegrableOn f (Ι a b) μ := by
  rw [interval_oc_eq_union, integrable_on_union, IntervalIntegrable]

/-- If a function is interval integrable with respect to a given measure `μ` on `a..b` then
  it is integrable on `interval_oc a b` with respect to `μ`. -/
theorem IntervalIntegrable.def (h : IntervalIntegrable f μ a b) : IntegrableOn f (Ι a b) μ :=
  interval_integrable_iff.mp h

theorem interval_integrable_iff_integrable_Ioc_of_le (hab : a ≤ b) :
    IntervalIntegrable f μ a b ↔ IntegrableOn f (Ioc a b) μ := by
  rw [interval_integrable_iff, interval_oc_of_le hab]

theorem integrable_on_Icc_iff_integrable_on_Ioc' {E : Type _} [NormedGroup E] {f : ℝ → E} (ha : μ {a} ≠ ∞) :
    IntegrableOn f (Icc a b) μ ↔ IntegrableOn f (Ioc a b) μ := by
  cases' le_or_ltₓ a b with hab hab
  · have : Icc a b = Icc a a ∪ Ioc a b := (Icc_union_Ioc_eq_Icc le_rfl hab).symm
    rw [this, integrable_on_union]
    simp [← ha.lt_top]
    
  · simp [← hab, ← hab.le]
    

theorem integrable_on_Icc_iff_integrable_on_Ioc {E : Type _} [NormedGroup E] [HasNoAtoms μ] {f : ℝ → E} {a b : ℝ} :
    IntegrableOn f (Icc a b) μ ↔ IntegrableOn f (Ioc a b) μ :=
  integrable_on_Icc_iff_integrable_on_Ioc'
    (by
      simp )

theorem integrable_on_Ioc_iff_integrable_on_Ioo' {E : Type _} [NormedGroup E] {f : ℝ → E} {a b : ℝ} (hb : μ {b} ≠ ∞) :
    IntegrableOn f (Ioc a b) μ ↔ IntegrableOn f (Ioo a b) μ := by
  cases' lt_or_leₓ a b with hab hab
  · have : Ioc a b = Ioo a b ∪ Icc b b := (Ioo_union_Icc_eq_Ioc hab le_rfl).symm
    rw [this, integrable_on_union]
    simp [← hb.lt_top]
    
  · simp [← hab]
    

theorem integrable_on_Ioc_iff_integrable_on_Ioo {E : Type _} [NormedGroup E] [HasNoAtoms μ] {f : ℝ → E} {a b : ℝ} :
    IntegrableOn f (Ioc a b) μ ↔ IntegrableOn f (Ioo a b) μ :=
  integrable_on_Ioc_iff_integrable_on_Ioo'
    (by
      simp )

theorem integrable_on_Icc_iff_integrable_on_Ioo {E : Type _} [NormedGroup E] [HasNoAtoms μ] {f : ℝ → E} {a b : ℝ} :
    IntegrableOn f (Icc a b) μ ↔ IntegrableOn f (Ioo a b) μ := by
  rw [integrable_on_Icc_iff_integrable_on_Ioc, integrable_on_Ioc_iff_integrable_on_Ioo]

theorem interval_integrable_iff' [HasNoAtoms μ] : IntervalIntegrable f μ a b ↔ IntegrableOn f (Interval a b) μ := by
  rw [interval_integrable_iff, interval, interval_oc, integrable_on_Icc_iff_integrable_on_Ioc]

theorem interval_integrable_iff_integrable_Icc_of_le {E : Type _} [NormedGroup E] {f : ℝ → E} {a b : ℝ} (hab : a ≤ b)
    {μ : Measureₓ ℝ} [HasNoAtoms μ] : IntervalIntegrable f μ a b ↔ IntegrableOn f (Icc a b) μ := by
  rw [interval_integrable_iff_integrable_Ioc_of_le hab, integrable_on_Icc_iff_integrable_on_Ioc]

theorem integrable_on_Ici_iff_integrable_on_Ioi' {E : Type _} [NormedGroup E] {f : ℝ → E} (ha : μ {a} ≠ ∞) :
    IntegrableOn f (Ici a) μ ↔ IntegrableOn f (Ioi a) μ := by
  have : Ici a = Icc a a ∪ Ioi a := (Icc_union_Ioi_eq_Ici le_rfl).symm
  rw [this, integrable_on_union]
  simp [← ha.lt_top]

theorem integrable_on_Ici_iff_integrable_on_Ioi {E : Type _} [NormedGroup E] [HasNoAtoms μ] {f : ℝ → E} :
    IntegrableOn f (Ici a) μ ↔ IntegrableOn f (Ioi a) μ :=
  integrable_on_Ici_iff_integrable_on_Ioi'
    (by
      simp )

/-- If a function is integrable with respect to a given measure `μ` then it is interval integrable
  with respect to `μ` on `interval a b`. -/
theorem MeasureTheory.Integrable.interval_integrable (hf : Integrable f μ) : IntervalIntegrable f μ a b :=
  ⟨hf.IntegrableOn, hf.IntegrableOn⟩

-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
theorem MeasureTheory.IntegrableOn.interval_integrable
    (hf : IntegrableOn f "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)" μ) :
    IntervalIntegrable f μ a b :=
  ⟨MeasureTheory.IntegrableOn.mono_set hf (Ioc_subset_Icc_self.trans Icc_subset_interval),
    MeasureTheory.IntegrableOn.mono_set hf (Ioc_subset_Icc_self.trans Icc_subset_interval')⟩

theorem interval_integrable_const_iff {c : E} : IntervalIntegrable (fun _ => c) μ a b ↔ c = 0 ∨ μ (Ι a b) < ∞ := by
  simp only [← interval_integrable_iff, ← integrable_on_const]

@[simp]
theorem interval_integrable_const [IsLocallyFiniteMeasure μ] {c : E} : IntervalIntegrable (fun _ => c) μ a b :=
  interval_integrable_const_iff.2 <| Or.inr measure_Ioc_lt_top

end

namespace IntervalIntegrable

section

variable {f : ℝ → E} {a b c d : ℝ} {μ ν : Measureₓ ℝ}

@[symm]
theorem symm (h : IntervalIntegrable f μ a b) : IntervalIntegrable f μ b a :=
  h.symm

@[refl]
theorem refl : IntervalIntegrable f μ a a := by
  constructor <;> simp

@[trans]
theorem trans {a b c : ℝ} (hab : IntervalIntegrable f μ a b) (hbc : IntervalIntegrable f μ b c) :
    IntervalIntegrable f μ a c :=
  ⟨(hab.1.union hbc.1).mono_set Ioc_subset_Ioc_union_Ioc, (hbc.2.union hab.2).mono_set Ioc_subset_Ioc_union_Ioc⟩

theorem trans_iterate_Ico {a : ℕ → ℝ} {m n : ℕ} (hmn : m ≤ n)
    (hint : ∀, ∀ k ∈ Ico m n, ∀, IntervalIntegrable f μ (a k) (a <| k + 1)) : IntervalIntegrable f μ (a m) (a n) := by
  revert hint
  refine' Nat.le_induction _ _ n hmn
  · simp
    
  · intro p hp IH h
    exact
      (IH fun k hk => h k (Ico_subset_Ico_right p.le_succ hk)).trans
        (h p
          (by
            simp [← hp]))
    

theorem trans_iterate {a : ℕ → ℝ} {n : ℕ} (hint : ∀, ∀ k < n, ∀, IntervalIntegrable f μ (a k) (a <| k + 1)) :
    IntervalIntegrable f μ (a 0) (a n) :=
  trans_iterate_Ico bot_le fun k hk => hint k hk.2

theorem neg (h : IntervalIntegrable f μ a b) : IntervalIntegrable (-f) μ a b :=
  ⟨h.1.neg, h.2.neg⟩

theorem norm (h : IntervalIntegrable f μ a b) : IntervalIntegrable (fun x => ∥f x∥) μ a b :=
  ⟨h.1.norm, h.2.norm⟩

theorem abs {f : ℝ → ℝ} (h : IntervalIntegrable f μ a b) : IntervalIntegrable (fun x => abs (f x)) μ a b :=
  h.norm

-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
theorem mono (hf : IntervalIntegrable f ν a b)
    (h1 :
      "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)" ⊆
        "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)")
    (h2 : μ ≤ ν) : IntervalIntegrable f μ c d :=
  interval_integrable_iff.mpr <| hf.def.mono (interval_oc_subset_interval_oc_of_interval_subset_interval h1) h2

-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
theorem mono_set (hf : IntervalIntegrable f μ a b)
    (h :
      "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)" ⊆
        "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)") :
    IntervalIntegrable f μ c d :=
  hf.mono h rfl.le

theorem mono_measure (hf : IntervalIntegrable f ν a b) (h : μ ≤ ν) : IntervalIntegrable f μ a b :=
  hf.mono rfl.Subset h

theorem mono_set_ae (hf : IntervalIntegrable f μ a b) (h : Ι c d ≤ᵐ[μ] Ι a b) : IntervalIntegrable f μ c d :=
  interval_integrable_iff.mpr <| hf.def.mono_set_ae h

theorem mono_fun [NormedGroup F] {g : ℝ → F} (hf : IntervalIntegrable f μ a b)
    (hgm : AeStronglyMeasurable g (μ.restrict (Ι a b))) (hle : (fun x => ∥g x∥) ≤ᵐ[μ.restrict (Ι a b)] fun x => ∥f x∥) :
    IntervalIntegrable g μ a b :=
  interval_integrable_iff.2 <| hf.def.Integrable.mono hgm hle

theorem mono_fun' {g : ℝ → ℝ} (hg : IntervalIntegrable g μ a b) (hfm : AeStronglyMeasurable f (μ.restrict (Ι a b)))
    (hle : (fun x => ∥f x∥) ≤ᵐ[μ.restrict (Ι a b)] g) : IntervalIntegrable f μ a b :=
  interval_integrable_iff.2 <| hg.def.Integrable.mono' hfm hle

protected theorem ae_strongly_measurable (h : IntervalIntegrable f μ a b) :
    AeStronglyMeasurable f (μ.restrict (Ioc a b)) :=
  h.1.AeStronglyMeasurable

protected theorem ae_strongly_measurable' (h : IntervalIntegrable f μ a b) :
    AeStronglyMeasurable f (μ.restrict (Ioc b a)) :=
  h.2.AeStronglyMeasurable

end

variable {f g : ℝ → E} {a b : ℝ} {μ : Measureₓ ℝ}

theorem smul [NormedField 𝕜] [NormedSpace 𝕜 E] {f : ℝ → E} {a b : ℝ} {μ : Measureₓ ℝ} (h : IntervalIntegrable f μ a b)
    (r : 𝕜) : IntervalIntegrable (r • f) μ a b :=
  ⟨h.1.smul r, h.2.smul r⟩

@[simp]
theorem add (hf : IntervalIntegrable f μ a b) (hg : IntervalIntegrable g μ a b) :
    IntervalIntegrable (fun x => f x + g x) μ a b :=
  ⟨hf.1.add hg.1, hf.2.add hg.2⟩

@[simp]
theorem sub (hf : IntervalIntegrable f μ a b) (hg : IntervalIntegrable g μ a b) :
    IntervalIntegrable (fun x => f x - g x) μ a b :=
  ⟨hf.1.sub hg.1, hf.2.sub hg.2⟩

theorem sum (s : Finset ι) {f : ι → ℝ → E} (h : ∀, ∀ i ∈ s, ∀, IntervalIntegrable (f i) μ a b) :
    IntervalIntegrable (∑ i in s, f i) μ a b :=
  ⟨integrable_finset_sum' s fun i hi => (h i hi).1, integrable_finset_sum' s fun i hi => (h i hi).2⟩

-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
theorem mul_continuous_on {f g : ℝ → ℝ} (hf : IntervalIntegrable f μ a b)
    (hg : ContinuousOn g "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)") :
    IntervalIntegrable (fun x => f x * g x) μ a b := by
  rw [interval_integrable_iff] at hf⊢
  exact hf.mul_continuous_on_of_subset hg measurable_set_Ioc is_compact_interval Ioc_subset_Icc_self

-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
theorem continuous_on_mul {f g : ℝ → ℝ} (hf : IntervalIntegrable f μ a b)
    (hg : ContinuousOn g "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)") :
    IntervalIntegrable (fun x => g x * f x) μ a b := by
  simpa [← mul_comm] using hf.mul_continuous_on hg

theorem comp_mul_left (hf : IntervalIntegrable f volume a b) (c : ℝ) :
    IntervalIntegrable (fun x => f (c * x)) volume (a / c) (b / c) := by
  rcases eq_or_ne c 0 with (hc | hc)
  · rw [hc]
    simp
    
  rw [interval_integrable_iff'] at hf⊢
  have A : MeasurableEmbedding fun x => x * c⁻¹ :=
    (Homeomorph.mulRight₀ _ (inv_ne_zero hc)).ClosedEmbedding.MeasurableEmbedding
  rw [← Real.smul_map_volume_mul_right (inv_ne_zero hc), integrable_on, measure.restrict_smul,
    integrable_smul_measure
      (by
        simpa : Ennreal.ofReal (abs c⁻¹) ≠ 0)
      Ennreal.of_real_ne_top,
    ← integrable_on, MeasurableEmbedding.integrable_on_map_iff A]
  convert hf using 1
  · ext
    simp only [← comp_app]
    congr 1
    field_simp
    ring
    
  · rw [preimage_mul_const_interval (inv_ne_zero hc)]
    field_simp [← hc]
    

theorem iff_comp_neg : IntervalIntegrable f volume a b ↔ IntervalIntegrable (fun x => f (-x)) volume (-a) (-b) := by
  constructor
  all_goals
    intro hf
    convert comp_mul_left hf (-1)
    simp
    field_simp
    field_simp

end IntervalIntegrable

section

variable {μ : Measureₓ ℝ} [IsLocallyFiniteMeasure μ]

theorem ContinuousOn.interval_integrable {u : ℝ → E} {a b : ℝ} (hu : ContinuousOn u (Interval a b)) :
    IntervalIntegrable u μ a b :=
  (ContinuousOn.integrable_on_Icc hu).IntervalIntegrable

theorem ContinuousOn.interval_integrable_of_Icc {u : ℝ → E} {a b : ℝ} (h : a ≤ b) (hu : ContinuousOn u (Icc a b)) :
    IntervalIntegrable u μ a b :=
  ContinuousOn.interval_integrable ((interval_of_le h).symm ▸ hu)

/-- A continuous function on `ℝ` is `interval_integrable` with respect to any locally finite measure
`ν` on ℝ. -/
theorem Continuous.interval_integrable {u : ℝ → E} (hu : Continuous u) (a b : ℝ) : IntervalIntegrable u μ a b :=
  hu.ContinuousOn.IntervalIntegrable

end

section

variable {μ : Measureₓ ℝ} [IsLocallyFiniteMeasure μ] [ConditionallyCompleteLinearOrder E] [OrderTopology E]
  [SecondCountableTopology E]

theorem MonotoneOn.interval_integrable {u : ℝ → E} {a b : ℝ} (hu : MonotoneOn u (Interval a b)) :
    IntervalIntegrable u μ a b := by
  rw [interval_integrable_iff]
  exact (hu.integrable_on_compact is_compact_interval).mono_set Ioc_subset_Icc_self

theorem AntitoneOn.interval_integrable {u : ℝ → E} {a b : ℝ} (hu : AntitoneOn u (Interval a b)) :
    IntervalIntegrable u μ a b :=
  hu.dual_right.IntervalIntegrable

theorem Monotone.interval_integrable {u : ℝ → E} {a b : ℝ} (hu : Monotone u) : IntervalIntegrable u μ a b :=
  (hu.MonotoneOn _).IntervalIntegrable

theorem Antitone.interval_integrable {u : ℝ → E} {a b : ℝ} (hu : Antitone u) : IntervalIntegrable u μ a b :=
  (hu.AntitoneOn _).IntervalIntegrable

end

/-- Let `l'` be a measurably generated filter; let `l` be a of filter such that each `s ∈ l'`
eventually includes `Ioc u v` as both `u` and `v` tend to `l`. Let `μ` be a measure finite at `l'`.

Suppose that `f : ℝ → E` has a finite limit at `l' ⊓ μ.ae`. Then `f` is interval integrable on
`u..v` provided that both `u` and `v` tend to `l`.

Typeclass instances allow Lean to find `l'` based on `l` but not vice versa, so
`apply tendsto.eventually_interval_integrable_ae` will generate goals `filter ℝ` and
`tendsto_Ixx_class Ioc ?m_1 l'`. -/
theorem Filter.Tendsto.eventually_interval_integrable_ae {f : ℝ → E} {μ : Measureₓ ℝ} {l l' : Filter ℝ}
    (hfm : StronglyMeasurableAtFilter f l' μ) [TendstoIxxClass Ioc l l'] [IsMeasurablyGenerated l']
    (hμ : μ.FiniteAtFilter l') {c : E} (hf : Tendsto f (l'⊓μ.ae) (𝓝 c)) {u v : ι → ℝ} {lt : Filter ι}
    (hu : Tendsto u lt l) (hv : Tendsto v lt l) : ∀ᶠ t in lt, IntervalIntegrable f μ (u t) (v t) :=
  have := (hf.integrable_at_filter_ae hfm hμ).Eventually
  ((hu.Ioc hv).Eventually this).And <| (hv.Ioc hu).Eventually this

/-- Let `l'` be a measurably generated filter; let `l` be a of filter such that each `s ∈ l'`
eventually includes `Ioc u v` as both `u` and `v` tend to `l`. Let `μ` be a measure finite at `l'`.

Suppose that `f : ℝ → E` has a finite limit at `l`. Then `f` is interval integrable on `u..v`
provided that both `u` and `v` tend to `l`.

Typeclass instances allow Lean to find `l'` based on `l` but not vice versa, so
`apply tendsto.eventually_interval_integrable_ae` will generate goals `filter ℝ` and
`tendsto_Ixx_class Ioc ?m_1 l'`. -/
theorem Filter.Tendsto.eventually_interval_integrable {f : ℝ → E} {μ : Measureₓ ℝ} {l l' : Filter ℝ}
    (hfm : StronglyMeasurableAtFilter f l' μ) [TendstoIxxClass Ioc l l'] [IsMeasurablyGenerated l']
    (hμ : μ.FiniteAtFilter l') {c : E} (hf : Tendsto f l' (𝓝 c)) {u v : ι → ℝ} {lt : Filter ι} (hu : Tendsto u lt l)
    (hv : Tendsto v lt l) : ∀ᶠ t in lt, IntervalIntegrable f μ (u t) (v t) :=
  (hf.mono_left inf_le_left).eventually_interval_integrable_ae hfm hμ hu hv

/-!
### Interval integral: definition and basic properties

In this section we define `∫ x in a..b, f x ∂μ` as `∫ x in Ioc a b, f x ∂μ - ∫ x in Ioc b a, f x ∂μ`
and prove some basic properties.
-/


variable [CompleteSpace E] [NormedSpace ℝ E]

/-- The interval integral `∫ x in a..b, f x ∂μ` is defined
as `∫ x in Ioc a b, f x ∂μ - ∫ x in Ioc b a, f x ∂μ`. If `a ≤ b`, then it equals
`∫ x in Ioc a b, f x ∂μ`, otherwise it equals `-∫ x in Ioc b a, f x ∂μ`. -/
def intervalIntegral (f : ℝ → E) (a b : ℝ) (μ : Measureₓ ℝ) :=
  (∫ x in Ioc a b, f x ∂μ) - ∫ x in Ioc b a, f x ∂μ

-- mathport name: «expr∫ in .. , ∂ »
notation3"∫ "(...)" in "a".."b", "r:(scoped f => f)" ∂"μ => intervalIntegral r a b μ

-- mathport name: «expr∫ in .. , »
notation3"∫ "(...)" in "a".."b", "r:(scoped f => intervalIntegral f a b volume) => r

namespace intervalIntegral

section Basic

variable {a b : ℝ} {f g : ℝ → E} {μ : Measureₓ ℝ}

@[simp]
theorem integral_zero : (∫ x in a..b, (0 : E) ∂μ) = 0 := by
  simp [← intervalIntegral]

theorem integral_of_le (h : a ≤ b) : (∫ x in a..b, f x ∂μ) = ∫ x in Ioc a b, f x ∂μ := by
  simp [← intervalIntegral, ← h]

@[simp]
theorem integral_same : (∫ x in a..a, f x ∂μ) = 0 :=
  sub_self _

theorem integral_symm (a b) : (∫ x in b..a, f x ∂μ) = -∫ x in a..b, f x ∂μ := by
  simp only [← intervalIntegral, ← neg_sub]

theorem integral_of_ge (h : b ≤ a) : (∫ x in a..b, f x ∂μ) = -∫ x in Ioc b a, f x ∂μ := by
  simp only [← integral_symm b, ← integral_of_le h]

theorem interval_integral_eq_integral_interval_oc (f : ℝ → E) (a b : ℝ) (μ : Measureₓ ℝ) :
    (∫ x in a..b, f x ∂μ) = (if a ≤ b then 1 else -1 : ℝ) • ∫ x in Ι a b, f x ∂μ := by
  split_ifs with h
  · simp only [← integral_of_le h, ← interval_oc_of_le h, ← one_smul]
    
  · simp only [← integral_of_ge (not_leₓ.1 h).le, ← interval_oc_of_lt (not_leₓ.1 h), ← neg_one_smul]
    

theorem integral_cases (f : ℝ → E) (a b) :
    (∫ x in a..b, f x ∂μ) ∈ ({∫ x in Ι a b, f x ∂μ, -∫ x in Ι a b, f x ∂μ} : Set E) := by
  rw [interval_integral_eq_integral_interval_oc]
  split_ifs <;> simp

theorem integral_undef (h : ¬IntervalIntegrable f μ a b) : (∫ x in a..b, f x ∂μ) = 0 := by
  cases' le_totalₓ a b with hab hab <;>
    simp only [← integral_of_le, ← integral_of_ge, ← hab, ← neg_eq_zero] <;>
      refine' integral_undef (not_imp_not.mpr integrable.integrable_on' _) <;> simpa [← hab] using not_and_distrib.mp h

theorem integral_non_ae_strongly_measurable (hf : ¬AeStronglyMeasurable f (μ.restrict (Ι a b))) :
    (∫ x in a..b, f x ∂μ) = 0 := by
  rw [interval_integral_eq_integral_interval_oc, integral_non_ae_strongly_measurable hf, smul_zero]

theorem integral_non_ae_strongly_measurable_of_le (h : a ≤ b) (hf : ¬AeStronglyMeasurable f (μ.restrict (Ioc a b))) :
    (∫ x in a..b, f x ∂μ) = 0 :=
  integral_non_ae_strongly_measurable <| by
    rwa [interval_oc_of_le h]

theorem norm_integral_min_max (f : ℝ → E) : ∥∫ x in min a b..max a b, f x ∂μ∥ = ∥∫ x in a..b, f x ∂μ∥ := by
  cases le_totalₓ a b <;> simp [*, ← integral_symm a b]

theorem norm_integral_eq_norm_integral_Ioc (f : ℝ → E) : ∥∫ x in a..b, f x ∂μ∥ = ∥∫ x in Ι a b, f x ∂μ∥ := by
  rw [← norm_integral_min_max, integral_of_le min_le_max, interval_oc]

theorem abs_integral_eq_abs_integral_interval_oc (f : ℝ → ℝ) : abs (∫ x in a..b, f x ∂μ) = abs (∫ x in Ι a b, f x ∂μ) :=
  norm_integral_eq_norm_integral_Ioc f

theorem norm_integral_le_integral_norm_Ioc : ∥∫ x in a..b, f x ∂μ∥ ≤ ∫ x in Ι a b, ∥f x∥ ∂μ :=
  calc
    ∥∫ x in a..b, f x ∂μ∥ = ∥∫ x in Ι a b, f x ∂μ∥ := norm_integral_eq_norm_integral_Ioc f
    _ ≤ ∫ x in Ι a b, ∥f x∥ ∂μ := norm_integral_le_integral_norm f
    

theorem norm_integral_le_abs_integral_norm : ∥∫ x in a..b, f x ∂μ∥ ≤ abs (∫ x in a..b, ∥f x∥ ∂μ) := by
  simp only [Real.norm_eq_abs, ← norm_integral_eq_norm_integral_Ioc]
  exact le_transₓ (norm_integral_le_integral_norm _) (le_abs_self _)

theorem norm_integral_le_integral_norm (h : a ≤ b) : ∥∫ x in a..b, f x ∂μ∥ ≤ ∫ x in a..b, ∥f x∥ ∂μ :=
  norm_integral_le_integral_norm_Ioc.trans_eq <| by
    rw [interval_oc_of_le h, integral_of_le h]

theorem norm_integral_le_of_norm_le_const_ae {a b C : ℝ} {f : ℝ → E} (h : ∀ᵐ x, x ∈ Ι a b → ∥f x∥ ≤ C) :
    ∥∫ x in a..b, f x∥ ≤ C * abs (b - a) := by
  rw [norm_integral_eq_norm_integral_Ioc]
  convert norm_set_integral_le_of_norm_le_const_ae'' _ measurable_set_Ioc h
  · rw [Real.volume_Ioc, max_sub_min_eq_abs, Ennreal.to_real_of_real (abs_nonneg _)]
    
  · simp only [← Real.volume_Ioc, ← Ennreal.of_real_lt_top]
    

theorem norm_integral_le_of_norm_le_const {a b C : ℝ} {f : ℝ → E} (h : ∀, ∀ x ∈ Ι a b, ∀, ∥f x∥ ≤ C) :
    ∥∫ x in a..b, f x∥ ≤ C * abs (b - a) :=
  norm_integral_le_of_norm_le_const_ae <| eventually_of_forall h

@[simp]
theorem integral_add (hf : IntervalIntegrable f μ a b) (hg : IntervalIntegrable g μ a b) :
    (∫ x in a..b, f x + g x ∂μ) = (∫ x in a..b, f x ∂μ) + ∫ x in a..b, g x ∂μ := by
  simp only [← interval_integral_eq_integral_interval_oc, ← integral_add hf.def hg.def, ← smul_add]

theorem integral_finset_sum {ι} {s : Finset ι} {f : ι → ℝ → E} (h : ∀, ∀ i ∈ s, ∀, IntervalIntegrable (f i) μ a b) :
    (∫ x in a..b, ∑ i in s, f i x ∂μ) = ∑ i in s, ∫ x in a..b, f i x ∂μ := by
  simp only [← interval_integral_eq_integral_interval_oc, ← integral_finset_sum s fun i hi => (h i hi).def, ←
    Finset.smul_sum]

@[simp]
theorem integral_neg : (∫ x in a..b, -f x ∂μ) = -∫ x in a..b, f x ∂μ := by
  simp only [← intervalIntegral, ← integral_neg]
  abel

@[simp]
theorem integral_sub (hf : IntervalIntegrable f μ a b) (hg : IntervalIntegrable g μ a b) :
    (∫ x in a..b, f x - g x ∂μ) = (∫ x in a..b, f x ∂μ) - ∫ x in a..b, g x ∂μ := by
  simpa only [← sub_eq_add_neg] using (integral_add hf hg.neg).trans (congr_arg _ integral_neg)

@[simp]
theorem integral_smul {𝕜 : Type _} [NondiscreteNormedField 𝕜] [NormedSpace 𝕜 E] [SmulCommClass ℝ 𝕜 E] (r : 𝕜)
    (f : ℝ → E) : (∫ x in a..b, r • f x ∂μ) = r • ∫ x in a..b, f x ∂μ := by
  simp only [← intervalIntegral, ← integral_smul, ← smul_sub]

@[simp]
theorem integral_smul_const {𝕜 : Type _} [IsROrC 𝕜] [NormedSpace 𝕜 E] (f : ℝ → 𝕜) (c : E) :
    (∫ x in a..b, f x • c ∂μ) = (∫ x in a..b, f x ∂μ) • c := by
  simp only [← interval_integral_eq_integral_interval_oc, ← integral_smul_const, ← smul_assoc]

@[simp]
theorem integral_const_mul {𝕜 : Type _} [IsROrC 𝕜] (r : 𝕜) (f : ℝ → 𝕜) :
    (∫ x in a..b, r * f x ∂μ) = r * ∫ x in a..b, f x ∂μ :=
  integral_smul r f

@[simp]
theorem integral_mul_const {𝕜 : Type _} [IsROrC 𝕜] (r : 𝕜) (f : ℝ → 𝕜) :
    (∫ x in a..b, f x * r ∂μ) = (∫ x in a..b, f x ∂μ) * r := by
  simpa only [← mul_comm r] using integral_const_mul r f

@[simp]
theorem integral_div {𝕜 : Type _} [IsROrC 𝕜] (r : 𝕜) (f : ℝ → 𝕜) :
    (∫ x in a..b, f x / r ∂μ) = (∫ x in a..b, f x ∂μ) / r := by
  simpa only [← div_eq_mul_inv] using integral_mul_const r⁻¹ f

theorem integral_const' (c : E) : (∫ x in a..b, c ∂μ) = ((μ <| Ioc a b).toReal - (μ <| Ioc b a).toReal) • c := by
  simp only [← intervalIntegral, ← set_integral_const, ← sub_smul]

@[simp]
theorem integral_const (c : E) : (∫ x in a..b, c) = (b - a) • c := by
  simp only [← integral_const', ← Real.volume_Ioc, ← Ennreal.to_real_of_real', neg_sub b, ← max_zero_sub_eq_self]

theorem integral_smul_measure (c : ℝ≥0∞) : (∫ x in a..b, f x ∂c • μ) = c.toReal • ∫ x in a..b, f x ∂μ := by
  simp only [← intervalIntegral, ← measure.restrict_smul, ← integral_smul_measure, ← smul_sub]

variable [NormedGroup F] [CompleteSpace F] [NormedSpace ℝ F]

theorem _root_.continuous_linear_map.interval_integral_comp_comm (L : E →L[ℝ] F) (hf : IntervalIntegrable f μ a b) :
    (∫ x in a..b, L (f x) ∂μ) = L (∫ x in a..b, f x ∂μ) := by
  rw [intervalIntegral, intervalIntegral, L.integral_comp_comm, L.integral_comp_comm, L.map_sub]
  exacts[hf.2, hf.1]

end Basic

section Comp

variable {a b c d : ℝ} (f : ℝ → E)

@[simp]
theorem integral_comp_mul_right (hc : c ≠ 0) : (∫ x in a..b, f (x * c)) = c⁻¹ • ∫ x in a * c..b * c, f x := by
  have A : MeasurableEmbedding fun x => x * c := (Homeomorph.mulRight₀ c hc).ClosedEmbedding.MeasurableEmbedding
  conv_rhs => rw [← Real.smul_map_volume_mul_right hc]
  simp_rw [integral_smul_measure, intervalIntegral, A.set_integral_map, Ennreal.to_real_of_real (abs_nonneg c)]
  cases hc.lt_or_lt
  · simp [← h, ← mul_div_cancel, ← hc, ← abs_of_neg, ← measure.restrict_congr_set Ico_ae_eq_Ioc]
    
  · simp [← h, ← mul_div_cancel, ← hc, ← abs_of_pos]
    

@[simp]
theorem smul_integral_comp_mul_right (c) : (c • ∫ x in a..b, f (x * c)) = ∫ x in a * c..b * c, f x := by
  by_cases' hc : c = 0 <;> simp [← hc]

@[simp]
theorem integral_comp_mul_left (hc : c ≠ 0) : (∫ x in a..b, f (c * x)) = c⁻¹ • ∫ x in c * a..c * b, f x := by
  simpa only [← mul_comm c] using integral_comp_mul_right f hc

@[simp]
theorem smul_integral_comp_mul_left (c) : (c • ∫ x in a..b, f (c * x)) = ∫ x in c * a..c * b, f x := by
  by_cases' hc : c = 0 <;> simp [← hc]

@[simp]
theorem integral_comp_div (hc : c ≠ 0) : (∫ x in a..b, f (x / c)) = c • ∫ x in a / c..b / c, f x := by
  simpa only [← inv_invₓ] using integral_comp_mul_right f (inv_ne_zero hc)

@[simp]
theorem inv_smul_integral_comp_div (c) : (c⁻¹ • ∫ x in a..b, f (x / c)) = ∫ x in a / c..b / c, f x := by
  by_cases' hc : c = 0 <;> simp [← hc]

@[simp]
theorem integral_comp_add_right (d) : (∫ x in a..b, f (x + d)) = ∫ x in a + d..b + d, f x :=
  have A : MeasurableEmbedding fun x => x + d := (Homeomorph.addRight d).ClosedEmbedding.MeasurableEmbedding
  calc
    (∫ x in a..b, f (x + d)) = ∫ x in a + d..b + d, f x ∂Measure.map (fun x => x + d) volume := by
      simp [← intervalIntegral, ← A.set_integral_map]
    _ = ∫ x in a + d..b + d, f x := by
      rw [map_add_right_eq_self]
    

@[simp]
theorem integral_comp_add_left (d) : (∫ x in a..b, f (d + x)) = ∫ x in d + a..d + b, f x := by
  simpa only [← add_commₓ] using integral_comp_add_right f d

@[simp]
theorem integral_comp_mul_add (hc : c ≠ 0) (d) :
    (∫ x in a..b, f (c * x + d)) = c⁻¹ • ∫ x in c * a + d..c * b + d, f x := by
  rw [← integral_comp_add_right, ← integral_comp_mul_left _ hc]

@[simp]
theorem smul_integral_comp_mul_add (c d) : (c • ∫ x in a..b, f (c * x + d)) = ∫ x in c * a + d..c * b + d, f x := by
  by_cases' hc : c = 0 <;> simp [← hc]

@[simp]
theorem integral_comp_add_mul (hc : c ≠ 0) (d) :
    (∫ x in a..b, f (d + c * x)) = c⁻¹ • ∫ x in d + c * a..d + c * b, f x := by
  rw [← integral_comp_add_left, ← integral_comp_mul_left _ hc]

@[simp]
theorem smul_integral_comp_add_mul (c d) : (c • ∫ x in a..b, f (d + c * x)) = ∫ x in d + c * a..d + c * b, f x := by
  by_cases' hc : c = 0 <;> simp [← hc]

@[simp]
theorem integral_comp_div_add (hc : c ≠ 0) (d) : (∫ x in a..b, f (x / c + d)) = c • ∫ x in a / c + d..b / c + d, f x :=
  by
  simpa only [← div_eq_inv_mul, ← inv_invₓ] using integral_comp_mul_add f (inv_ne_zero hc) d

@[simp]
theorem inv_smul_integral_comp_div_add (c d) : (c⁻¹ • ∫ x in a..b, f (x / c + d)) = ∫ x in a / c + d..b / c + d, f x :=
  by
  by_cases' hc : c = 0 <;> simp [← hc]

@[simp]
theorem integral_comp_add_div (hc : c ≠ 0) (d) : (∫ x in a..b, f (d + x / c)) = c • ∫ x in d + a / c..d + b / c, f x :=
  by
  simpa only [← div_eq_inv_mul, ← inv_invₓ] using integral_comp_add_mul f (inv_ne_zero hc) d

@[simp]
theorem inv_smul_integral_comp_add_div (c d) : (c⁻¹ • ∫ x in a..b, f (d + x / c)) = ∫ x in d + a / c..d + b / c, f x :=
  by
  by_cases' hc : c = 0 <;> simp [← hc]

@[simp]
theorem integral_comp_mul_sub (hc : c ≠ 0) (d) :
    (∫ x in a..b, f (c * x - d)) = c⁻¹ • ∫ x in c * a - d..c * b - d, f x := by
  simpa only [← sub_eq_add_neg] using integral_comp_mul_add f hc (-d)

@[simp]
theorem smul_integral_comp_mul_sub (c d) : (c • ∫ x in a..b, f (c * x - d)) = ∫ x in c * a - d..c * b - d, f x := by
  by_cases' hc : c = 0 <;> simp [← hc]

@[simp]
theorem integral_comp_sub_mul (hc : c ≠ 0) (d) :
    (∫ x in a..b, f (d - c * x)) = c⁻¹ • ∫ x in d - c * b..d - c * a, f x := by
  simp only [← sub_eq_add_neg, ← neg_mul_eq_neg_mulₓ]
  rw [integral_comp_add_mul f (neg_ne_zero.mpr hc) d, integral_symm]
  simp only [← inv_neg, ← smul_neg, ← neg_negₓ, ← neg_smul]

@[simp]
theorem smul_integral_comp_sub_mul (c d) : (c • ∫ x in a..b, f (d - c * x)) = ∫ x in d - c * b..d - c * a, f x := by
  by_cases' hc : c = 0 <;> simp [← hc]

@[simp]
theorem integral_comp_div_sub (hc : c ≠ 0) (d) : (∫ x in a..b, f (x / c - d)) = c • ∫ x in a / c - d..b / c - d, f x :=
  by
  simpa only [← div_eq_inv_mul, ← inv_invₓ] using integral_comp_mul_sub f (inv_ne_zero hc) d

@[simp]
theorem inv_smul_integral_comp_div_sub (c d) : (c⁻¹ • ∫ x in a..b, f (x / c - d)) = ∫ x in a / c - d..b / c - d, f x :=
  by
  by_cases' hc : c = 0 <;> simp [← hc]

@[simp]
theorem integral_comp_sub_div (hc : c ≠ 0) (d) : (∫ x in a..b, f (d - x / c)) = c • ∫ x in d - b / c..d - a / c, f x :=
  by
  simpa only [← div_eq_inv_mul, ← inv_invₓ] using integral_comp_sub_mul f (inv_ne_zero hc) d

@[simp]
theorem inv_smul_integral_comp_sub_div (c d) : (c⁻¹ • ∫ x in a..b, f (d - x / c)) = ∫ x in d - b / c..d - a / c, f x :=
  by
  by_cases' hc : c = 0 <;> simp [← hc]

@[simp]
theorem integral_comp_sub_right (d) : (∫ x in a..b, f (x - d)) = ∫ x in a - d..b - d, f x := by
  simpa only [← sub_eq_add_neg] using integral_comp_add_right f (-d)

@[simp]
theorem integral_comp_sub_left (d) : (∫ x in a..b, f (d - x)) = ∫ x in d - b..d - a, f x := by
  simpa only [← one_mulₓ, ← one_smul, ← inv_one] using integral_comp_sub_mul f one_ne_zero d

@[simp]
theorem integral_comp_neg : (∫ x in a..b, f (-x)) = ∫ x in -b..-a, f x := by
  simpa only [← zero_sub] using integral_comp_sub_left f 0

end Comp

/-!
### Integral is an additive function of the interval

In this section we prove that `∫ x in a..b, f x ∂μ + ∫ x in b..c, f x ∂μ = ∫ x in a..c, f x ∂μ`
as well as a few other identities trivially equivalent to this one. We also prove that
`∫ x in a..b, f x ∂μ = ∫ x, f x ∂μ` provided that `support f ⊆ Ioc a b`.
-/


section OrderClosedTopology

variable {a b c d : ℝ} {f g : ℝ → E} {μ : Measureₓ ℝ}

-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
/-- If two functions are equal in the relevant interval, their interval integrals are also equal. -/
theorem integral_congr {a b : ℝ}
    (h : EqOn f g "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)") :
    (∫ x in a..b, f x ∂μ) = ∫ x in a..b, g x ∂μ := by
  cases' le_totalₓ a b with hab hab <;>
    simpa [← hab, ← integral_of_le, ← integral_of_ge] using
      set_integral_congr measurable_set_Ioc (h.mono Ioc_subset_Icc_self)

theorem integral_add_adjacent_intervals_cancel (hab : IntervalIntegrable f μ a b) (hbc : IntervalIntegrable f μ b c) :
    (((∫ x in a..b, f x ∂μ) + ∫ x in b..c, f x ∂μ) + ∫ x in c..a, f x ∂μ) = 0 := by
  have hac := hab.trans hbc
  simp only [← intervalIntegral, ← sub_add_sub_comm, ← sub_eq_zero]
  iterate 4 
    rw [← integral_union]
  · suffices Ioc a b ∪ Ioc b c ∪ Ioc c a = Ioc b a ∪ Ioc c b ∪ Ioc a c by
      rw [this]
    rw [Ioc_union_Ioc_union_Ioc_cycle, union_right_comm, Ioc_union_Ioc_union_Ioc_cycle, min_left_commₓ, max_left_commₓ]
    
  all_goals
    simp [*, ← MeasurableSet.union, ← measurable_set_Ioc, ← Ioc_disjoint_Ioc_same, ← Ioc_disjoint_Ioc_same.symm, ←
      hab.1, ← hab.2, ← hbc.1, ← hbc.2, ← hac.1, ← hac.2]

theorem integral_add_adjacent_intervals (hab : IntervalIntegrable f μ a b) (hbc : IntervalIntegrable f μ b c) :
    ((∫ x in a..b, f x ∂μ) + ∫ x in b..c, f x ∂μ) = ∫ x in a..c, f x ∂μ := by
  rw [← add_neg_eq_zero, ← integral_symm, integral_add_adjacent_intervals_cancel hab hbc]

theorem sum_integral_adjacent_intervals_Ico {a : ℕ → ℝ} {m n : ℕ} (hmn : m ≤ n)
    (hint : ∀, ∀ k ∈ Ico m n, ∀, IntervalIntegrable f μ (a k) (a <| k + 1)) :
    (∑ k : ℕ in Finset.ico m n, ∫ x in a k..a <| k + 1, f x ∂μ) = ∫ x in a m..a n, f x ∂μ := by
  revert hint
  refine' Nat.le_induction _ _ n hmn
  · simp
    
  · intro p hmp IH h
    rw [Finset.sum_Ico_succ_top hmp, IH, integral_add_adjacent_intervals]
    · apply IntervalIntegrable.trans_iterate_Ico hmp fun k hk => h k _
      exact (Ico_subset_Ico le_rfl (Nat.le_succₓ _)) hk
      
    · apply h
      simp [← hmp]
      
    · intro k hk
      exact h _ (Ico_subset_Ico_right p.le_succ hk)
      
    

theorem sum_integral_adjacent_intervals {a : ℕ → ℝ} {n : ℕ}
    (hint : ∀, ∀ k < n, ∀, IntervalIntegrable f μ (a k) (a <| k + 1)) :
    (∑ k : ℕ in Finset.range n, ∫ x in a k..a <| k + 1, f x ∂μ) = ∫ x in a 0 ..a n, f x ∂μ := by
  rw [← Nat.Ico_zero_eq_range]
  exact sum_integral_adjacent_intervals_Ico (zero_le n) fun k hk => hint k hk.2

theorem integral_interval_sub_left (hab : IntervalIntegrable f μ a b) (hac : IntervalIntegrable f μ a c) :
    ((∫ x in a..b, f x ∂μ) - ∫ x in a..c, f x ∂μ) = ∫ x in c..b, f x ∂μ :=
  sub_eq_of_eq_add' <| Eq.symm <| integral_add_adjacent_intervals hac (hac.symm.trans hab)

theorem integral_interval_add_interval_comm (hab : IntervalIntegrable f μ a b) (hcd : IntervalIntegrable f μ c d)
    (hac : IntervalIntegrable f μ a c) :
    ((∫ x in a..b, f x ∂μ) + ∫ x in c..d, f x ∂μ) = (∫ x in a..d, f x ∂μ) + ∫ x in c..b, f x ∂μ := by
  rw [← integral_add_adjacent_intervals hac hcd, add_assocₓ, add_left_commₓ,
    integral_add_adjacent_intervals hac (hac.symm.trans hab), add_commₓ]

theorem integral_interval_sub_interval_comm (hab : IntervalIntegrable f μ a b) (hcd : IntervalIntegrable f μ c d)
    (hac : IntervalIntegrable f μ a c) :
    ((∫ x in a..b, f x ∂μ) - ∫ x in c..d, f x ∂μ) = (∫ x in a..c, f x ∂μ) - ∫ x in b..d, f x ∂μ := by
  simp only [← sub_eq_add_neg, integral_symm, ← integral_interval_add_interval_comm hab hcd.symm (hac.trans hcd)]

theorem integral_interval_sub_interval_comm' (hab : IntervalIntegrable f μ a b) (hcd : IntervalIntegrable f μ c d)
    (hac : IntervalIntegrable f μ a c) :
    ((∫ x in a..b, f x ∂μ) - ∫ x in c..d, f x ∂μ) = (∫ x in d..b, f x ∂μ) - ∫ x in c..a, f x ∂μ := by
  rw [integral_interval_sub_interval_comm hab hcd hac, integral_symm b d, integral_symm a c, sub_neg_eq_add,
    sub_eq_neg_add]

theorem integral_Iic_sub_Iic (ha : IntegrableOn f (Iic a) μ) (hb : IntegrableOn f (Iic b) μ) :
    ((∫ x in Iic b, f x ∂μ) - ∫ x in Iic a, f x ∂μ) = ∫ x in a..b, f x ∂μ := by
  wlog (discharger := tactic.skip) hab : a ≤ b using a b
  · rw [sub_eq_iff_eq_add', integral_of_le hab, ← integral_union (Iic_disjoint_Ioc le_rfl), Iic_union_Ioc_eq_Iic hab]
    exacts[measurable_set_Ioc, ha, hb.mono_set fun _ => And.right]
    
  · intro ha hb
    rw [integral_symm, ← this hb ha, neg_sub]
    

/-- If `μ` is a finite measure then `∫ x in a..b, c ∂μ = (μ (Iic b) - μ (Iic a)) • c`. -/
theorem integral_const_of_cdf [IsFiniteMeasure μ] (c : E) :
    (∫ x in a..b, c ∂μ) = ((μ (Iic b)).toReal - (μ (Iic a)).toReal) • c := by
  simp only [← sub_smul, set_integral_const]
  refine' (integral_Iic_sub_Iic _ _).symm <;> simp only [← integrable_on_const, ← measure_lt_top, ← or_trueₓ]

theorem integral_eq_integral_of_support_subset {a b} (h : Support f ⊆ Ioc a b) : (∫ x in a..b, f x ∂μ) = ∫ x, f x ∂μ :=
  by
  cases' le_totalₓ a b with hab hab
  · rw [integral_of_le hab, ← integral_indicator measurable_set_Ioc, indicator_eq_self.2 h] <;> infer_instance
    
  · rw [Ioc_eq_empty hab.not_lt, subset_empty_iff, support_eq_empty_iff] at h
    simp [← h]
    

theorem integral_congr_ae' (h : ∀ᵐ x ∂μ, x ∈ Ioc a b → f x = g x) (h' : ∀ᵐ x ∂μ, x ∈ Ioc b a → f x = g x) :
    (∫ x in a..b, f x ∂μ) = ∫ x in a..b, g x ∂μ := by
  simp only [← intervalIntegral, ← set_integral_congr_ae measurable_set_Ioc h, ←
    set_integral_congr_ae measurable_set_Ioc h']

theorem integral_congr_ae (h : ∀ᵐ x ∂μ, x ∈ Ι a b → f x = g x) : (∫ x in a..b, f x ∂μ) = ∫ x in a..b, g x ∂μ :=
  integral_congr_ae' (ae_interval_oc_iff.mp h).1 (ae_interval_oc_iff.mp h).2

theorem integral_zero_ae (h : ∀ᵐ x ∂μ, x ∈ Ι a b → f x = 0) : (∫ x in a..b, f x ∂μ) = 0 :=
  calc
    (∫ x in a..b, f x ∂μ) = ∫ x in a..b, 0 ∂μ := integral_congr_ae h
    _ = 0 := integral_zero
    

theorem integral_indicator {a₁ a₂ a₃ : ℝ} (h : a₂ ∈ Icc a₁ a₃) :
    (∫ x in a₁..a₃, indicatorₓ { x | x ≤ a₂ } f x ∂μ) = ∫ x in a₁..a₂, f x ∂μ := by
  have : { x | x ≤ a₂ } ∩ Ioc a₁ a₃ = Ioc a₁ a₂ := Iic_inter_Ioc_of_le h.2
  rw [integral_of_le h.1, integral_of_le (h.1.trans h.2), integral_indicator, measure.restrict_restrict, this]
  exact measurable_set_Iic
  all_goals
    apply measurable_set_Iic

/-- Lebesgue dominated convergence theorem for filters with a countable basis -/
theorem tendsto_integral_filter_of_dominated_convergence {ι} {l : Filter ι} [l.IsCountablyGenerated] {F : ι → ℝ → E}
    (bound : ℝ → ℝ) (hF_meas : ∀ᶠ n in l, AeStronglyMeasurable (F n) (μ.restrict (Ι a b)))
    (h_bound : ∀ᶠ n in l, ∀ᵐ x ∂μ, x ∈ Ι a b → ∥F n x∥ ≤ bound x) (bound_integrable : IntervalIntegrable bound μ a b)
    (h_lim : ∀ᵐ x ∂μ, x ∈ Ι a b → Tendsto (fun n => F n x) l (𝓝 (f x))) :
    Tendsto (fun n => ∫ x in a..b, F n x ∂μ) l (𝓝 <| ∫ x in a..b, f x ∂μ) := by
  simp only [← interval_integrable_iff, ← interval_integral_eq_integral_interval_oc,
    ae_restrict_iff' measurable_set_interval_oc] at *
  exact
    tendsto_const_nhds.smul
      (tendsto_integral_filter_of_dominated_convergence bound hF_meas h_bound bound_integrable h_lim)

/-- Lebesgue dominated convergence theorem for series. -/
theorem has_sum_integral_of_dominated_convergence {ι} [Encodable ι] {F : ι → ℝ → E} (bound : ι → ℝ → ℝ)
    (hF_meas : ∀ n, AeStronglyMeasurable (F n) (μ.restrict (Ι a b)))
    (h_bound : ∀ n, ∀ᵐ t ∂μ, t ∈ Ι a b → ∥F n t∥ ≤ bound n t)
    (bound_summable : ∀ᵐ t ∂μ, t ∈ Ι a b → Summable fun n => bound n t)
    (bound_integrable : IntervalIntegrable (fun t => ∑' n, bound n t) μ a b)
    (h_lim : ∀ᵐ t ∂μ, t ∈ Ι a b → HasSum (fun n => F n t) (f t)) :
    HasSum (fun n => ∫ t in a..b, F n t ∂μ) (∫ t in a..b, f t ∂μ) := by
  simp only [← interval_integrable_iff, ← interval_integral_eq_integral_interval_oc,
    ae_restrict_iff' measurable_set_interval_oc] at *
  exact
    (has_sum_integral_of_dominated_convergence bound hF_meas h_bound bound_summable bound_integrable h_lim).const_smul

open TopologicalSpace

variable {X : Type _} [TopologicalSpace X] [FirstCountableTopology X]

/-- Continuity of interval integral with respect to a parameter, at a point within a set.
  Given `F : X → ℝ → E`, assume `F x` is ae-measurable on `[a, b]` for `x` in a
  neighborhood of `x₀` within `s` and at `x₀`, and assume it is bounded by a function integrable
  on `[a, b]` independent of `x` in a neighborhood of `x₀` within `s`. If `(λ x, F x t)`
  is continuous at `x₀` within `s` for almost every `t` in `[a, b]`
  then the same holds for `(λ x, ∫ t in a..b, F x t ∂μ) s x₀`. -/
theorem continuous_within_at_of_dominated_interval {F : X → ℝ → E} {x₀ : X} {bound : ℝ → ℝ} {a b : ℝ} {s : Set X}
    (hF_meas : ∀ᶠ x in 𝓝[s] x₀, AeStronglyMeasurable (F x) (μ.restrict <| Ι a b))
    (h_bound : ∀ᶠ x in 𝓝[s] x₀, ∀ᵐ t ∂μ, t ∈ Ι a b → ∥F x t∥ ≤ bound t)
    (bound_integrable : IntervalIntegrable bound μ a b)
    (h_cont : ∀ᵐ t ∂μ, t ∈ Ι a b → ContinuousWithinAt (fun x => F x t) s x₀) :
    ContinuousWithinAt (fun x => ∫ t in a..b, F x t ∂μ) s x₀ :=
  tendsto_integral_filter_of_dominated_convergence bound hF_meas h_bound bound_integrable h_cont

/-- Continuity of interval integral with respect to a parameter at a point.
  Given `F : X → ℝ → E`, assume `F x` is ae-measurable on `[a, b]` for `x` in a
  neighborhood of `x₀`, and assume it is bounded by a function integrable on
  `[a, b]` independent of `x` in a neighborhood of `x₀`. If `(λ x, F x t)`
  is continuous at `x₀` for almost every `t` in `[a, b]`
  then the same holds for `(λ x, ∫ t in a..b, F x t ∂μ) s x₀`. -/
theorem continuous_at_of_dominated_interval {F : X → ℝ → E} {x₀ : X} {bound : ℝ → ℝ} {a b : ℝ}
    (hF_meas : ∀ᶠ x in 𝓝 x₀, AeStronglyMeasurable (F x) (μ.restrict <| Ι a b))
    (h_bound : ∀ᶠ x in 𝓝 x₀, ∀ᵐ t ∂μ, t ∈ Ι a b → ∥F x t∥ ≤ bound t) (bound_integrable : IntervalIntegrable bound μ a b)
    (h_cont : ∀ᵐ t ∂μ, t ∈ Ι a b → ContinuousAt (fun x => F x t) x₀) :
    ContinuousAt (fun x => ∫ t in a..b, F x t ∂μ) x₀ :=
  tendsto_integral_filter_of_dominated_convergence bound hF_meas h_bound bound_integrable h_cont

/-- Continuity of interval integral with respect to a parameter.
  Given `F : X → ℝ → E`, assume each `F x` is ae-measurable on `[a, b]`,
  and assume it is bounded by a function integrable on `[a, b]` independent of `x`.
  If `(λ x, F x t)` is continuous for almost every `t` in `[a, b]`
  then the same holds for `(λ x, ∫ t in a..b, F x t ∂μ) s x₀`. -/
theorem continuous_of_dominated_interval {F : X → ℝ → E} {bound : ℝ → ℝ} {a b : ℝ}
    (hF_meas : ∀ x, AeStronglyMeasurable (F x) <| μ.restrict <| Ι a b)
    (h_bound : ∀ x, ∀ᵐ t ∂μ, t ∈ Ι a b → ∥F x t∥ ≤ bound t) (bound_integrable : IntervalIntegrable bound μ a b)
    (h_cont : ∀ᵐ t ∂μ, t ∈ Ι a b → Continuous fun x => F x t) : Continuous fun x => ∫ t in a..b, F x t ∂μ :=
  continuous_iff_continuous_at.mpr fun x₀ =>
    continuous_at_of_dominated_interval (eventually_of_forall hF_meas) (eventually_of_forall h_bound)
        bound_integrable <|
      h_cont.mono fun x himp hx => (himp hx).ContinuousAt

end OrderClosedTopology

section ContinuousPrimitive

open TopologicalSpace

variable {a b b₀ b₁ b₂ : ℝ} {μ : Measureₓ ℝ} {f g : ℝ → E}

theorem continuous_within_at_primitive (hb₀ : μ {b₀} = 0) (h_int : IntervalIntegrable f μ (min a b₁) (max a b₂)) :
    ContinuousWithinAt (fun b => ∫ x in a..b, f x ∂μ) (Icc b₁ b₂) b₀ := by
  by_cases' h₀ : b₀ ∈ Icc b₁ b₂
  · have h₁₂ : b₁ ≤ b₂ := h₀.1.trans h₀.2
    have min₁₂ : min b₁ b₂ = b₁ := min_eq_leftₓ h₁₂
    have h_int' : ∀ {x}, x ∈ Icc b₁ b₂ → IntervalIntegrable f μ b₁ x := by
      rintro x ⟨h₁, h₂⟩
      apply h_int.mono_set
      apply interval_subset_interval
      · exact ⟨min_le_of_left_le (min_le_rightₓ a b₁), h₁.trans (h₂.trans <| le_max_of_le_right <| le_max_rightₓ _ _)⟩
        
      · exact ⟨min_le_of_left_le <| (min_le_rightₓ _ _).trans h₁, le_max_of_le_right <| h₂.trans <| le_max_rightₓ _ _⟩
        
    have : ∀, ∀ b ∈ Icc b₁ b₂, ∀, (∫ x in a..b, f x ∂μ) = (∫ x in a..b₁, f x ∂μ) + ∫ x in b₁..b, f x ∂μ := by
      rintro b ⟨h₁, h₂⟩
      rw [← integral_add_adjacent_intervals _ (h_int' ⟨h₁, h₂⟩)]
      apply h_int.mono_set
      apply interval_subset_interval
      · exact ⟨min_le_of_left_le (min_le_leftₓ a b₁), le_max_of_le_right (le_max_leftₓ _ _)⟩
        
      · exact ⟨min_le_of_left_le (min_le_rightₓ _ _), le_max_of_le_right (h₁.trans <| h₂.trans (le_max_rightₓ a b₂))⟩
        
    apply ContinuousWithinAt.congr _ this (this _ h₀)
    clear this
    refine' continuous_within_at_const.add _
    have : (fun b => ∫ x in b₁..b, f x ∂μ) =ᶠ[𝓝[Icc b₁ b₂] b₀] fun b => ∫ x in b₁..b₂, indicator { x | x ≤ b } f x ∂μ :=
      by
      apply eventually_eq_of_mem self_mem_nhds_within
      exact fun b b_in => (integral_indicator b_in).symm
    apply ContinuousWithinAt.congr_of_eventually_eq _ this (integral_indicator h₀).symm
    have : IntervalIntegrable (fun x => ∥f x∥) μ b₁ b₂ := IntervalIntegrable.norm (h_int' <| right_mem_Icc.mpr h₁₂)
    refine' continuous_within_at_of_dominated_interval _ _ this _ <;> clear this
    · apply eventually.mono self_mem_nhds_within
      intro x hx
      erw [ae_strongly_measurable_indicator_iff, measure.restrict_restrict, Iic_inter_Ioc_of_le]
      · rw [min₁₂]
        exact (h_int' hx).1.AeStronglyMeasurable
        
      · exact le_max_of_le_right hx.2
        
      exacts[measurable_set_Iic, measurable_set_Iic]
      
    · refine' eventually_of_forall fun x => eventually_of_forall fun t => _
      dsimp' [← indicator]
      split_ifs <;> simp
      
    · have : ∀ᵐ t ∂μ, t < b₀ ∨ b₀ < t := by
        apply eventually.mono (compl_mem_ae_iff.mpr hb₀)
        intro x hx
        exact Ne.lt_or_lt hx
      apply this.mono
      rintro x₀ (hx₀ | hx₀) -
      · have : ∀ᶠ x in 𝓝[Icc b₁ b₂] b₀, { t : ℝ | t ≤ x }.indicator f x₀ = f x₀ := by
          apply mem_nhds_within_of_mem_nhds
          apply eventually.mono (Ioi_mem_nhds hx₀)
          intro x hx
          simp [← hx.le]
        apply continuous_within_at_const.congr_of_eventually_eq this
        simp [← hx₀.le]
        
      · have : ∀ᶠ x in 𝓝[Icc b₁ b₂] b₀, { t : ℝ | t ≤ x }.indicator f x₀ = 0 := by
          apply mem_nhds_within_of_mem_nhds
          apply eventually.mono (Iio_mem_nhds hx₀)
          intro x hx
          simp [← hx]
        apply continuous_within_at_const.congr_of_eventually_eq this
        simp [← hx₀]
        
      
    
  · apply continuous_within_at_of_not_mem_closure
    rwa [closure_Icc]
    

theorem continuous_on_primitive [HasNoAtoms μ] (h_int : IntegrableOn f (Icc a b) μ) :
    ContinuousOn (fun x => ∫ t in Ioc a x, f t ∂μ) (Icc a b) := by
  by_cases' h : a ≤ b
  · have : ∀, ∀ x ∈ Icc a b, ∀, (∫ t in Ioc a x, f t ∂μ) = ∫ t in a..x, f t ∂μ := by
      intro x x_in
      simp_rw [← interval_oc_of_le h, integral_of_le x_in.1]
    rw [continuous_on_congr this]
    intro x₀ hx₀
    refine' continuous_within_at_primitive (measure_singleton x₀) _
    simp only [← interval_integrable_iff_integrable_Ioc_of_le, ← min_eq_leftₓ, ← max_eq_rightₓ, ← h]
    exact h_int.mono Ioc_subset_Icc_self le_rfl
    
  · rw [Icc_eq_empty h]
    exact continuous_on_empty _
    

theorem continuous_on_primitive_Icc [HasNoAtoms μ] (h_int : IntegrableOn f (Icc a b) μ) :
    ContinuousOn (fun x => ∫ t in Icc a x, f t ∂μ) (Icc a b) := by
  rw
    [show (fun x => ∫ t in Icc a x, f t ∂μ) = fun x => ∫ t in Ioc a x, f t ∂μ by
      ext x
      exact integral_Icc_eq_integral_Ioc]
  exact continuous_on_primitive h_int

-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
/-- Note: this assumes that `f` is `interval_integrable`, in contrast to some other lemmas here. -/
theorem continuous_on_primitive_interval' [HasNoAtoms μ] (h_int : IntervalIntegrable f μ b₁ b₂)
    (ha : a ∈ "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)") :
    ContinuousOn (fun b => ∫ x in a..b, f x ∂μ)
      "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)" :=
  by
  intro b₀ hb₀
  refine' continuous_within_at_primitive (measure_singleton _) _
  rw [min_eq_rightₓ ha.1, max_eq_rightₓ ha.2]
  simpa [← interval_integrable_iff, ← interval_oc] using h_int

theorem continuous_on_primitive_interval [HasNoAtoms μ] (h_int : IntegrableOn f (Interval a b) μ) :
    ContinuousOn (fun x => ∫ t in a..x, f t ∂μ) (Interval a b) :=
  continuous_on_primitive_interval' h_int.IntervalIntegrable left_mem_interval

theorem continuous_on_primitive_interval_left [HasNoAtoms μ] (h_int : IntegrableOn f (Interval a b) μ) :
    ContinuousOn (fun x => ∫ t in x..b, f t ∂μ) (Interval a b) := by
  rw [interval_swap a b] at h_int⊢
  simp only [← integral_symm b]
  exact (continuous_on_primitive_interval h_int).neg

variable [HasNoAtoms μ]

theorem continuous_primitive (h_int : ∀ a b, IntervalIntegrable f μ a b) (a : ℝ) :
    Continuous fun b => ∫ x in a..b, f x ∂μ := by
  rw [continuous_iff_continuous_at]
  intro b₀
  cases' exists_lt b₀ with b₁ hb₁
  cases' exists_gt b₀ with b₂ hb₂
  apply ContinuousWithinAt.continuous_at _ (Icc_mem_nhds hb₁ hb₂)
  exact continuous_within_at_primitive (measure_singleton b₀) (h_int _ _)

theorem _root_.measure_theory.integrable.continuous_primitive (h_int : Integrable f μ) (a : ℝ) :
    Continuous fun b => ∫ x in a..b, f x ∂μ :=
  continuous_primitive (fun _ _ => h_int.IntervalIntegrable) a

end ContinuousPrimitive

section

variable {f g : ℝ → ℝ} {a b : ℝ} {μ : Measureₓ ℝ}

theorem integral_eq_zero_iff_of_le_of_nonneg_ae (hab : a ≤ b) (hf : 0 ≤ᵐ[μ.restrict (Ioc a b)] f)
    (hfi : IntervalIntegrable f μ a b) : (∫ x in a..b, f x ∂μ) = 0 ↔ f =ᵐ[μ.restrict (Ioc a b)] 0 := by
  rw [integral_of_le hab, integral_eq_zero_iff_of_nonneg_ae hf hfi.1]

theorem integral_eq_zero_iff_of_nonneg_ae (hf : 0 ≤ᵐ[μ.restrict (Ioc a b ∪ Ioc b a)] f)
    (hfi : IntervalIntegrable f μ a b) : (∫ x in a..b, f x ∂μ) = 0 ↔ f =ᵐ[μ.restrict (Ioc a b ∪ Ioc b a)] 0 := by
  cases' le_totalₓ a b with hab hab <;> simp only [← Ioc_eq_empty hab.not_lt, ← empty_union, ← union_empty] at hf⊢
  · exact integral_eq_zero_iff_of_le_of_nonneg_ae hab hf hfi
    
  · rw [integral_symm, neg_eq_zero, integral_eq_zero_iff_of_le_of_nonneg_ae hab hf hfi.symm]
    

/-- If `f` is nonnegative and integrable on the unordered interval `set.interval_oc a b`, then its
integral over `a..b` is positive if and only if `a < b` and the measure of
`function.support f ∩ set.Ioc a b` is positive. -/
theorem integral_pos_iff_support_of_nonneg_ae' (hf : 0 ≤ᵐ[μ.restrict (Ι a b)] f) (hfi : IntervalIntegrable f μ a b) :
    (0 < ∫ x in a..b, f x ∂μ) ↔ a < b ∧ 0 < μ (Support f ∩ Ioc a b) := by
  cases' lt_or_leₓ a b with hab hba
  · rw [interval_oc_of_le hab.le] at hf
    simp only [← hab, ← true_andₓ, ← integral_of_le hab.le, ← set_integral_pos_iff_support_of_nonneg_ae hf hfi.1]
    
  · suffices (∫ x in a..b, f x ∂μ) ≤ 0 by
      simp only [← this.not_lt, ← hba.not_lt, ← false_andₓ]
    rw [integral_of_ge hba, neg_nonpos]
    rw [interval_oc_swap, interval_oc_of_le hba] at hf
    exact integral_nonneg_of_ae hf
    

/-- If `f` is nonnegative a.e.-everywhere and it is integrable on the unordered interval
`set.interval_oc a b`, then its integral over `a..b` is positive if and only if `a < b` and the
measure of `function.support f ∩ set.Ioc a b` is positive. -/
theorem integral_pos_iff_support_of_nonneg_ae (hf : 0 ≤ᵐ[μ] f) (hfi : IntervalIntegrable f μ a b) :
    (0 < ∫ x in a..b, f x ∂μ) ↔ a < b ∧ 0 < μ (Support f ∩ Ioc a b) :=
  integral_pos_iff_support_of_nonneg_ae' (ae_mono Measure.restrict_le_self hf) hfi

/-- If `f : ℝ → ℝ` is strictly positive and integrable on `(a, b]` for real numbers `a < b`, then
its integral over `a..b` is strictly positive. -/
theorem interval_integral_pos_of_pos {f : ℝ → ℝ} {a b : ℝ} (hfi : IntervalIntegrable f MeasureSpace.volume a b)
    (h : ∀ x, 0 < f x) (hab : a < b) : 0 < ∫ x in a..b, f x := by
  have hsupp : support f = univ := eq_univ_iff_forall.mpr fun t => (h t).Ne.symm
  replace h₀ : 0 ≤ᵐ[volume] f := eventually_of_forall fun x => (h x).le
  rw [integral_pos_iff_support_of_nonneg_ae h₀ hfi]
  exact
    ⟨hab, by
      simp [← hsupp, ← hab]⟩

/-- If `f` and `g` are two functions that are interval integrable on `a..b`, `a ≤ b`,
`f x ≤ g x` for a.e. `x ∈ set.Ioc a b`, and `f x < g x` on a subset of `set.Ioc a b`
of nonzero measure, then `∫ x in a..b, f x ∂μ < ∫ x in a..b, g x ∂μ`. -/
theorem integral_lt_integral_of_ae_le_of_measure_set_of_lt_ne_zero (hab : a ≤ b) (hfi : IntervalIntegrable f μ a b)
    (hgi : IntervalIntegrable g μ a b) (hle : f ≤ᵐ[μ.restrict (Ioc a b)] g)
    (hlt : μ.restrict (Ioc a b) { x | f x < g x } ≠ 0) : (∫ x in a..b, f x ∂μ) < ∫ x in a..b, g x ∂μ := by
  rw [← sub_pos, ← integral_sub hgi hfi, integral_of_le hab, MeasureTheory.integral_pos_iff_support_of_nonneg_ae]
  · refine' pos_iff_ne_zero.2 (mt (measure_mono_null _) hlt)
    exact fun x hx => (sub_pos.2 hx).ne'
    
  exacts[hle.mono fun x => sub_nonneg.2, hgi.1.sub hfi.1]

/-- If `f` and `g` are continuous on `[a, b]`, `a < b`, `f x ≤ g x` on this interval, and
`f c < g c` at some point `c ∈ [a, b]`, then `∫ x in a..b, f x < ∫ x in a..b, g x`. -/
theorem integral_lt_integral_of_continuous_on_of_le_of_exists_lt {f g : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hfc : ContinuousOn f (Icc a b)) (hgc : ContinuousOn g (Icc a b)) (hle : ∀, ∀ x ∈ Ioc a b, ∀, f x ≤ g x)
    (hlt : ∃ c ∈ Icc a b, f c < g c) : (∫ x in a..b, f x) < ∫ x in a..b, g x := by
  refine'
    integral_lt_integral_of_ae_le_of_measure_set_of_lt_ne_zero hab.le (hfc.interval_integrable_of_Icc hab.le)
      (hgc.interval_integrable_of_Icc hab.le) ((ae_restrict_mem measurable_set_Ioc).mono hle) _
  contrapose! hlt
  have h_eq : f =ᵐ[volume.restrict (Ioc a b)] g := by
    simp only [not_leₓ, ae_iff] at hlt
    exact eventually_le.antisymm ((ae_restrict_iff' measurable_set_Ioc).2 <| eventually_of_forall hle) hlt
  simp only [← measure.restrict_congr_set Ioc_ae_eq_Icc] at h_eq
  exact fun c hc => (measure.eq_on_Icc_of_ae_eq volume hab.ne h_eq hfc hgc hc).Ge

theorem integral_nonneg_of_ae_restrict (hab : a ≤ b) (hf : 0 ≤ᵐ[μ.restrict (Icc a b)] f) : 0 ≤ ∫ u in a..b, f u ∂μ := by
  let H := ae_restrict_of_ae_restrict_of_subset Ioc_subset_Icc_self hf
  simpa only [← integral_of_le hab] using set_integral_nonneg_of_ae_restrict H

theorem integral_nonneg_of_ae (hab : a ≤ b) (hf : 0 ≤ᵐ[μ] f) : 0 ≤ ∫ u in a..b, f u ∂μ :=
  integral_nonneg_of_ae_restrict hab <| ae_restrict_of_ae hf

theorem integral_nonneg_of_forall (hab : a ≤ b) (hf : ∀ u, 0 ≤ f u) : 0 ≤ ∫ u in a..b, f u ∂μ :=
  integral_nonneg_of_ae hab <| eventually_of_forall hf

theorem integral_nonneg (hab : a ≤ b) (hf : ∀ u, u ∈ Icc a b → 0 ≤ f u) : 0 ≤ ∫ u in a..b, f u ∂μ :=
  integral_nonneg_of_ae_restrict hab <| (ae_restrict_iff' measurable_set_Icc).mpr <| ae_of_all μ hf

theorem abs_integral_le_integral_abs (hab : a ≤ b) : abs (∫ x in a..b, f x ∂μ) ≤ ∫ x in a..b, abs (f x) ∂μ := by
  simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm hab

section Mono

variable (hab : a ≤ b) (hf : IntervalIntegrable f μ a b) (hg : IntervalIntegrable g μ a b)

include hab hf hg

theorem integral_mono_ae_restrict (h : f ≤ᵐ[μ.restrict (Icc a b)] g) : (∫ u in a..b, f u ∂μ) ≤ ∫ u in a..b, g u ∂μ := by
  let H := h.filter_mono <| ae_mono <| Measure.restrict_mono Ioc_subset_Icc_self <| le_reflₓ μ
  simpa only [← integral_of_le hab] using set_integral_mono_ae_restrict hf.1 hg.1 H

theorem integral_mono_ae (h : f ≤ᵐ[μ] g) : (∫ u in a..b, f u ∂μ) ≤ ∫ u in a..b, g u ∂μ := by
  simpa only [← integral_of_le hab] using set_integral_mono_ae hf.1 hg.1 h

theorem integral_mono_on (h : ∀, ∀ x ∈ Icc a b, ∀, f x ≤ g x) : (∫ u in a..b, f u ∂μ) ≤ ∫ u in a..b, g u ∂μ := by
  let H := fun x hx => h x <| Ioc_subset_Icc_self hx
  simpa only [← integral_of_le hab] using set_integral_mono_on hf.1 hg.1 measurable_set_Ioc H

theorem integral_mono (h : f ≤ g) : (∫ u in a..b, f u ∂μ) ≤ ∫ u in a..b, g u ∂μ :=
  integral_mono_ae hab hf hg <| ae_of_all _ h

omit hg hab

theorem integral_mono_interval {c d} (hca : c ≤ a) (hab : a ≤ b) (hbd : b ≤ d) (hf : 0 ≤ᵐ[μ.restrict (Ioc c d)] f)
    (hfi : IntervalIntegrable f μ c d) : (∫ x in a..b, f x ∂μ) ≤ ∫ x in c..d, f x ∂μ := by
  rw [integral_of_le hab, integral_of_le (hca.trans (hab.trans hbd))]
  exact set_integral_mono_set hfi.1 hf (Ioc_subset_Ioc hca hbd).EventuallyLe

theorem abs_integral_mono_interval {c d} (h : Ι a b ⊆ Ι c d) (hf : 0 ≤ᵐ[μ.restrict (Ι c d)] f)
    (hfi : IntervalIntegrable f μ c d) : abs (∫ x in a..b, f x ∂μ) ≤ abs (∫ x in c..d, f x ∂μ) :=
  have hf' : 0 ≤ᵐ[μ.restrict (Ι a b)] f := ae_mono (Measure.restrict_mono h le_rfl) hf
  calc
    abs (∫ x in a..b, f x ∂μ) = abs (∫ x in Ι a b, f x ∂μ) := abs_integral_eq_abs_integral_interval_oc f
    _ = ∫ x in Ι a b, f x ∂μ := abs_of_nonneg (MeasureTheory.integral_nonneg_of_ae hf')
    _ ≤ ∫ x in Ι c d, f x ∂μ := set_integral_mono_set hfi.def hf h.EventuallyLe
    _ ≤ abs (∫ x in Ι c d, f x ∂μ) := le_abs_self _
    _ = abs (∫ x in c..d, f x ∂μ) := (abs_integral_eq_abs_integral_interval_oc f).symm
    

end Mono

end

/-!
### Fundamental theorem of calculus, part 1, for any measure

In this section we prove a few lemmas that can be seen as versions of FTC-1 for interval integrals
w.r.t. any measure. Many theorems are formulated for one or two pairs of filters related by
`FTC_filter a l l'`. This typeclass has exactly four “real” instances: `(a, pure a, ⊥)`,
`(a, 𝓝[≥] a, 𝓝[>] a)`, `(a, 𝓝[≤] a, 𝓝[≤] a)`, `(a, 𝓝 a, 𝓝 a)`, and two instances
that are equal to the first and last “real” instances: `(a, 𝓝[{a}] a, ⊥)` and
`(a, 𝓝[univ] a, 𝓝[univ] a)`.  We use this approach to avoid repeating arguments in many very similar
cases.  Lean can automatically find both `a` and `l'` based on `l`.

The most general theorem `measure_integral_sub_integral_sub_linear_is_o_of_tendsto_ae` can be seen
as a generalization of lemma `integral_has_strict_fderiv_at` below which states strict
differentiability of `∫ x in u..v, f x` in `(u, v)` at `(a, b)` for a measurable function `f` that
is integrable on `a..b` and is continuous at `a` and `b`. The lemma is generalized in three
directions: first, `measure_integral_sub_integral_sub_linear_is_o_of_tendsto_ae` deals with any
locally finite measure `μ`; second, it works for one-sided limits/derivatives; third, it assumes
only that `f` has finite limits almost surely at `a` and `b`.

Namely, let `f` be a measurable function integrable on `a..b`. Let `(la, la')` be a pair of
`FTC_filter`s around `a`; let `(lb, lb')` be a pair of `FTC_filter`s around `b`. Suppose that `f`
has finite limits `ca` and `cb` at `la' ⊓ μ.ae` and `lb' ⊓ μ.ae`, respectively.  Then
`∫ x in va..vb, f x ∂μ - ∫ x in ua..ub, f x ∂μ = ∫ x in ub..vb, cb ∂μ - ∫ x in ua..va, ca ∂μ +
  o(∥∫ x in ua..va, (1:ℝ) ∂μ∥ + ∥∫ x in ub..vb, (1:ℝ) ∂μ∥)`
as `ua` and `va` tend to `la` while `ub` and `vb` tend to `lb`.

This theorem is formulated with integral of constants instead of measures in the right hand sides
for two reasons: first, this way we avoid `min`/`max` in the statements; second, often it is
possible to write better `simp` lemmas for these integrals, see `integral_const` and
`integral_const_of_cdf`.

In the next subsection we apply this theorem to prove various theorems about differentiability
of the integral w.r.t. Lebesgue measure. -/


/-- An auxiliary typeclass for the Fundamental theorem of calculus, part 1. It is used to formulate
theorems that work simultaneously for left and right one-sided derivatives of `∫ x in u..v, f x`. -/
class FTCFilter (a : outParam ℝ) (outer : Filter ℝ) (inner : outParam <| Filter ℝ) extends
  TendstoIxxClass Ioc outer inner : Prop where
  pure_le : pure a ≤ outer
  le_nhds : inner ≤ 𝓝 a
  [meas_gen : IsMeasurablyGenerated inner]

/- The `dangerous_instance` linter doesn't take `out_param`s into account, so it thinks that
`FTC_filter.to_tendsto_Ixx_class` is dangerous. Disable this linter using `nolint`.
-/
attribute [nolint dangerous_instance] FTC_filter.to_tendsto_Ixx_class

namespace FTCFilter

instance pure (a : ℝ) : FTCFilter a (pure a) ⊥ where
  pure_le := le_rfl
  le_nhds := bot_le

instance nhds_within_singleton (a : ℝ) : FTCFilter a (𝓝[{a}] a) ⊥ := by
  rw [nhdsWithin, principal_singleton, inf_eq_right.2 (pure_le_nhds a)]
  infer_instance

theorem finite_at_inner {a : ℝ} (l : Filter ℝ) {l'} [h : FTCFilter a l l'] {μ : Measureₓ ℝ} [IsLocallyFiniteMeasure μ] :
    μ.FiniteAtFilter l' :=
  (μ.finite_at_nhds a).filter_mono h.le_nhds

instance nhds (a : ℝ) : FTCFilter a (𝓝 a) (𝓝 a) where
  pure_le := pure_le_nhds a
  le_nhds := le_rfl

instance nhds_univ (a : ℝ) : FTCFilter a (𝓝[univ] a) (𝓝 a) := by
  rw [nhds_within_univ]
  infer_instance

instance nhds_left (a : ℝ) : FTCFilter a (𝓝[≤] a) (𝓝[≤] a) where
  pure_le := pure_le_nhds_within right_mem_Iic
  le_nhds := inf_le_left

instance nhds_right (a : ℝ) : FTCFilter a (𝓝[≥] a) (𝓝[>] a) where
  pure_le := pure_le_nhds_within left_mem_Ici
  le_nhds := inf_le_left

instance nhds_Icc {x a b : ℝ} [h : Fact (x ∈ Icc a b)] : FTCFilter x (𝓝[Icc a b] x) (𝓝[Icc a b] x) where
  pure_le := pure_le_nhds_within h.out
  le_nhds := inf_le_left

-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
instance nhds_interval {x a b : ℝ}
    [h : Fact (x ∈ "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)")] :
    FTCFilter x (𝓝["./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)"] x)
      (𝓝["./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)"] x) :=
  by
  have : Fact (x ∈ Set.Icc (min a b) (max a b)) := h
  exact FTC_filter.nhds_Icc

end FTCFilter

open Asymptotics

section

variable {f : ℝ → E} {a b : ℝ} {c ca cb : E} {l l' la la' lb lb' : Filter ℝ} {lt : Filter ι} {μ : Measureₓ ℝ}
  {u v ua va ub vb : ι → ℝ}

/-- Fundamental theorem of calculus-1, local version for any measure.
Let filters `l` and `l'` be related by `tendsto_Ixx_class Ioc`.
If `f` has a finite limit `c` at `l' ⊓ μ.ae`, where `μ` is a measure
finite at `l'`, then `∫ x in u..v, f x ∂μ = ∫ x in u..v, c ∂μ + o(∫ x in u..v, 1 ∂μ)` as both
`u` and `v` tend to `l`.

See also `measure_integral_sub_linear_is_o_of_tendsto_ae` for a version assuming
`[FTC_filter a l l']` and `[is_locally_finite_measure μ]`. If `l` is one of `𝓝[≥] a`,
`𝓝[≤] a`, `𝓝 a`, then it's easier to apply the non-primed version.
The primed version also works, e.g., for `l = l' = at_top`.

We use integrals of constants instead of measures because this way it is easier to formulate
a statement that works in both cases `u ≤ v` and `v ≤ u`. -/
theorem measure_integral_sub_linear_is_o_of_tendsto_ae' [IsMeasurablyGenerated l'] [TendstoIxxClass Ioc l l']
    (hfm : StronglyMeasurableAtFilter f l' μ) (hf : Tendsto f (l'⊓μ.ae) (𝓝 c)) (hl : μ.FiniteAtFilter l')
    (hu : Tendsto u lt l) (hv : Tendsto v lt l) :
    (fun t => (∫ x in u t..v t, f x ∂μ) - ∫ x in u t..v t, c ∂μ) =o[lt] fun t => ∫ x in u t..v t, (1 : ℝ) ∂μ := by
  have A := hf.integral_sub_linear_is_o_ae hfm hl (hu.Ioc hv)
  have B := hf.integral_sub_linear_is_o_ae hfm hl (hv.Ioc hu)
  simp only [← integral_const']
  convert (A.trans_le _).sub (B.trans_le _)
  · ext t
    simp_rw [intervalIntegral, sub_smul]
    abel
    
  all_goals
    intro t
    cases' le_totalₓ (u t) (v t) with huv huv <;> simp [← huv]

/-- Fundamental theorem of calculus-1, local version for any measure.
Let filters `l` and `l'` be related by `tendsto_Ixx_class Ioc`.
If `f` has a finite limit `c` at `l ⊓ μ.ae`, where `μ` is a measure
finite at `l`, then `∫ x in u..v, f x ∂μ = μ (Ioc u v) • c + o(μ(Ioc u v))` as both
`u` and `v` tend to `l` so that `u ≤ v`.

See also `measure_integral_sub_linear_is_o_of_tendsto_ae_of_le` for a version assuming
`[FTC_filter a l l']` and `[is_locally_finite_measure μ]`. If `l` is one of `𝓝[≥] a`,
`𝓝[≤] a`, `𝓝 a`, then it's easier to apply the non-primed version.
The primed version also works, e.g., for `l = l' = at_top`. -/
theorem measure_integral_sub_linear_is_o_of_tendsto_ae_of_le' [IsMeasurablyGenerated l'] [TendstoIxxClass Ioc l l']
    (hfm : StronglyMeasurableAtFilter f l' μ) (hf : Tendsto f (l'⊓μ.ae) (𝓝 c)) (hl : μ.FiniteAtFilter l')
    (hu : Tendsto u lt l) (hv : Tendsto v lt l) (huv : u ≤ᶠ[lt] v) :
    (fun t => (∫ x in u t..v t, f x ∂μ) - (μ (Ioc (u t) (v t))).toReal • c) =o[lt] fun t =>
      (μ <| Ioc (u t) (v t)).toReal :=
  (measure_integral_sub_linear_is_o_of_tendsto_ae' hfm hf hl hu hv).congr'
    (huv.mono fun x hx => by
      simp [← integral_const', ← hx])
    (huv.mono fun x hx => by
      simp [← integral_const', ← hx])

/-- Fundamental theorem of calculus-1, local version for any measure.
Let filters `l` and `l'` be related by `tendsto_Ixx_class Ioc`.
If `f` has a finite limit `c` at `l ⊓ μ.ae`, where `μ` is a measure
finite at `l`, then `∫ x in u..v, f x ∂μ = -μ (Ioc v u) • c + o(μ(Ioc v u))` as both
`u` and `v` tend to `l` so that `v ≤ u`.

See also `measure_integral_sub_linear_is_o_of_tendsto_ae_of_ge` for a version assuming
`[FTC_filter a l l']` and `[is_locally_finite_measure μ]`. If `l` is one of `𝓝[≥] a`,
`𝓝[≤] a`, `𝓝 a`, then it's easier to apply the non-primed version.
The primed version also works, e.g., for `l = l' = at_top`. -/
theorem measure_integral_sub_linear_is_o_of_tendsto_ae_of_ge' [IsMeasurablyGenerated l'] [TendstoIxxClass Ioc l l']
    (hfm : StronglyMeasurableAtFilter f l' μ) (hf : Tendsto f (l'⊓μ.ae) (𝓝 c)) (hl : μ.FiniteAtFilter l')
    (hu : Tendsto u lt l) (hv : Tendsto v lt l) (huv : v ≤ᶠ[lt] u) :
    (fun t => (∫ x in u t..v t, f x ∂μ) + (μ (Ioc (v t) (u t))).toReal • c) =o[lt] fun t =>
      (μ <| Ioc (v t) (u t)).toReal :=
  (measure_integral_sub_linear_is_o_of_tendsto_ae_of_le' hfm hf hl hv hu huv).neg_left.congr_left fun t => by
    simp [← integral_symm (u t), ← add_commₓ]

section

variable [IsLocallyFiniteMeasure μ] [FTCFilter a l l']

include a

attribute [local instance] FTC_filter.meas_gen

/-- Fundamental theorem of calculus-1, local version for any measure.
Let filters `l` and `l'` be related by `[FTC_filter a l l']`; let `μ` be a locally finite measure.
If `f` has a finite limit `c` at `l' ⊓ μ.ae`, then
`∫ x in u..v, f x ∂μ = ∫ x in u..v, c ∂μ + o(∫ x in u..v, 1 ∂μ)` as both `u` and `v` tend to `l`.

See also `measure_integral_sub_linear_is_o_of_tendsto_ae'` for a version that also works, e.g., for
`l = l' = at_top`.

We use integrals of constants instead of measures because this way it is easier to formulate
a statement that works in both cases `u ≤ v` and `v ≤ u`. -/
theorem measure_integral_sub_linear_is_o_of_tendsto_ae (hfm : StronglyMeasurableAtFilter f l' μ)
    (hf : Tendsto f (l'⊓μ.ae) (𝓝 c)) (hu : Tendsto u lt l) (hv : Tendsto v lt l) :
    (fun t => (∫ x in u t..v t, f x ∂μ) - ∫ x in u t..v t, c ∂μ) =o[lt] fun t => ∫ x in u t..v t, (1 : ℝ) ∂μ :=
  measure_integral_sub_linear_is_o_of_tendsto_ae' hfm hf (FTCFilter.finite_at_inner l) hu hv

/-- Fundamental theorem of calculus-1, local version for any measure.
Let filters `l` and `l'` be related by `[FTC_filter a l l']`; let `μ` be a locally finite measure.
If `f` has a finite limit `c` at `l' ⊓ μ.ae`, then
`∫ x in u..v, f x ∂μ = μ (Ioc u v) • c + o(μ(Ioc u v))` as both `u` and `v` tend to `l`.

See also `measure_integral_sub_linear_is_o_of_tendsto_ae_of_le'` for a version that also works,
e.g., for `l = l' = at_top`. -/
theorem measure_integral_sub_linear_is_o_of_tendsto_ae_of_le (hfm : StronglyMeasurableAtFilter f l' μ)
    (hf : Tendsto f (l'⊓μ.ae) (𝓝 c)) (hu : Tendsto u lt l) (hv : Tendsto v lt l) (huv : u ≤ᶠ[lt] v) :
    (fun t => (∫ x in u t..v t, f x ∂μ) - (μ (Ioc (u t) (v t))).toReal • c) =o[lt] fun t =>
      (μ <| Ioc (u t) (v t)).toReal :=
  measure_integral_sub_linear_is_o_of_tendsto_ae_of_le' hfm hf (FTCFilter.finite_at_inner l) hu hv huv

/-- Fundamental theorem of calculus-1, local version for any measure.
Let filters `l` and `l'` be related by `[FTC_filter a l l']`; let `μ` be a locally finite measure.
If `f` has a finite limit `c` at `l' ⊓ μ.ae`, then
`∫ x in u..v, f x ∂μ = -μ (Ioc v u) • c + o(μ(Ioc v u))` as both `u` and `v` tend to `l`.

See also `measure_integral_sub_linear_is_o_of_tendsto_ae_of_ge'` for a version that also works,
e.g., for `l = l' = at_top`. -/
theorem measure_integral_sub_linear_is_o_of_tendsto_ae_of_ge (hfm : StronglyMeasurableAtFilter f l' μ)
    (hf : Tendsto f (l'⊓μ.ae) (𝓝 c)) (hu : Tendsto u lt l) (hv : Tendsto v lt l) (huv : v ≤ᶠ[lt] u) :
    (fun t => (∫ x in u t..v t, f x ∂μ) + (μ (Ioc (v t) (u t))).toReal • c) =o[lt] fun t =>
      (μ <| Ioc (v t) (u t)).toReal :=
  measure_integral_sub_linear_is_o_of_tendsto_ae_of_ge' hfm hf (FTCFilter.finite_at_inner l) hu hv huv

end

attribute [local instance] FTC_filter.meas_gen

variable [FTCFilter a la la'] [FTCFilter b lb lb'] [IsLocallyFiniteMeasure μ]

/-- Fundamental theorem of calculus-1, strict derivative in both limits for a locally finite
measure.

Let `f` be a measurable function integrable on `a..b`. Let `(la, la')` be a pair of `FTC_filter`s
around `a`; let `(lb, lb')` be a pair of `FTC_filter`s around `b`. Suppose that `f` has finite
limits `ca` and `cb` at `la' ⊓ μ.ae` and `lb' ⊓ μ.ae`, respectively.
Then `∫ x in va..vb, f x ∂μ - ∫ x in ua..ub, f x ∂μ =
  ∫ x in ub..vb, cb ∂μ - ∫ x in ua..va, ca ∂μ +
    o(∥∫ x in ua..va, (1:ℝ) ∂μ∥ + ∥∫ x in ub..vb, (1:ℝ) ∂μ∥)`
as `ua` and `va` tend to `la` while `ub` and `vb` tend to `lb`.
-/
theorem measure_integral_sub_integral_sub_linear_is_o_of_tendsto_ae (hab : IntervalIntegrable f μ a b)
    (hmeas_a : StronglyMeasurableAtFilter f la' μ) (hmeas_b : StronglyMeasurableAtFilter f lb' μ)
    (ha_lim : Tendsto f (la'⊓μ.ae) (𝓝 ca)) (hb_lim : Tendsto f (lb'⊓μ.ae) (𝓝 cb)) (hua : Tendsto ua lt la)
    (hva : Tendsto va lt la) (hub : Tendsto ub lt lb) (hvb : Tendsto vb lt lb) :
    (fun t =>
        ((∫ x in va t..vb t, f x ∂μ) - ∫ x in ua t..ub t, f x ∂μ) -
          ((∫ x in ub t..vb t, cb ∂μ) - ∫ x in ua t..va t, ca ∂μ)) =o[lt]
      fun t => ∥∫ x in ua t..va t, (1 : ℝ) ∂μ∥ + ∥∫ x in ub t..vb t, (1 : ℝ) ∂μ∥ :=
  by
  refine'
    ((measure_integral_sub_linear_is_o_of_tendsto_ae hmeas_a ha_lim hua hva).neg_left.add_add
          (measure_integral_sub_linear_is_o_of_tendsto_ae hmeas_b hb_lim hub hvb)).congr'
      _ eventually_eq.rfl
  have A : ∀ᶠ t in lt, IntervalIntegrable f μ (ua t) (va t) :=
    ha_lim.eventually_interval_integrable_ae hmeas_a (FTC_filter.finite_at_inner la) hua hva
  have A' : ∀ᶠ t in lt, IntervalIntegrable f μ a (ua t) :=
    ha_lim.eventually_interval_integrable_ae hmeas_a (FTC_filter.finite_at_inner la)
      (tendsto_const_pure.mono_right FTC_filter.pure_le) hua
  have B : ∀ᶠ t in lt, IntervalIntegrable f μ (ub t) (vb t) :=
    hb_lim.eventually_interval_integrable_ae hmeas_b (FTC_filter.finite_at_inner lb) hub hvb
  have B' : ∀ᶠ t in lt, IntervalIntegrable f μ b (ub t) :=
    hb_lim.eventually_interval_integrable_ae hmeas_b (FTC_filter.finite_at_inner lb)
      (tendsto_const_pure.mono_right FTC_filter.pure_le) hub
  filter_upwards [A, A', B, B'] with _ ua_va a_ua ub_vb b_ub
  rw [← integral_interval_sub_interval_comm']
  · dsimp' only
    abel
    
  exacts[ub_vb, ua_va, b_ub.symm.trans <| hab.symm.trans a_ua]

/-- Fundamental theorem of calculus-1, strict derivative in right endpoint for a locally finite
measure.

Let `f` be a measurable function integrable on `a..b`. Let `(lb, lb')` be a pair of `FTC_filter`s
around `b`. Suppose that `f` has a finite limit `c` at `lb' ⊓ μ.ae`.

Then `∫ x in a..v, f x ∂μ - ∫ x in a..u, f x ∂μ = ∫ x in u..v, c ∂μ + o(∫ x in u..v, (1:ℝ) ∂μ)`
as `u` and `v` tend to `lb`.
-/
theorem measure_integral_sub_integral_sub_linear_is_o_of_tendsto_ae_right (hab : IntervalIntegrable f μ a b)
    (hmeas : StronglyMeasurableAtFilter f lb' μ) (hf : Tendsto f (lb'⊓μ.ae) (𝓝 c)) (hu : Tendsto u lt lb)
    (hv : Tendsto v lt lb) :
    (fun t => ((∫ x in a..v t, f x ∂μ) - ∫ x in a..u t, f x ∂μ) - ∫ x in u t..v t, c ∂μ) =o[lt] fun t =>
      ∫ x in u t..v t, (1 : ℝ) ∂μ :=
  by
  simpa using
    measure_integral_sub_integral_sub_linear_is_o_of_tendsto_ae hab strongly_measurable_at_bot hmeas
      ((tendsto_bot : tendsto _ ⊥ (𝓝 0)).mono_left inf_le_left) hf (tendsto_const_pure : tendsto _ _ (pure a))
      tendsto_const_pure hu hv

/-- Fundamental theorem of calculus-1, strict derivative in left endpoint for a locally finite
measure.

Let `f` be a measurable function integrable on `a..b`. Let `(la, la')` be a pair of `FTC_filter`s
around `a`. Suppose that `f` has a finite limit `c` at `la' ⊓ μ.ae`.

Then `∫ x in v..b, f x ∂μ - ∫ x in u..b, f x ∂μ = -∫ x in u..v, c ∂μ + o(∫ x in u..v, (1:ℝ) ∂μ)`
as `u` and `v` tend to `la`.
-/
theorem measure_integral_sub_integral_sub_linear_is_o_of_tendsto_ae_left (hab : IntervalIntegrable f μ a b)
    (hmeas : StronglyMeasurableAtFilter f la' μ) (hf : Tendsto f (la'⊓μ.ae) (𝓝 c)) (hu : Tendsto u lt la)
    (hv : Tendsto v lt la) :
    (fun t => ((∫ x in v t..b, f x ∂μ) - ∫ x in u t..b, f x ∂μ) + ∫ x in u t..v t, c ∂μ) =o[lt] fun t =>
      ∫ x in u t..v t, (1 : ℝ) ∂μ :=
  by
  simpa using
    measure_integral_sub_integral_sub_linear_is_o_of_tendsto_ae hab hmeas strongly_measurable_at_bot hf
      ((tendsto_bot : tendsto _ ⊥ (𝓝 0)).mono_left inf_le_left) hu hv (tendsto_const_pure : tendsto _ _ (pure b))
      tendsto_const_pure

end

/-!
### Fundamental theorem of calculus-1 for Lebesgue measure

In this section we restate theorems from the previous section for Lebesgue measure.
In particular, we prove that `∫ x in u..v, f x` is strictly differentiable in `(u, v)`
at `(a, b)` provided that `f` is integrable on `a..b` and is continuous at `a` and `b`.
-/


variable {f : ℝ → E} {c ca cb : E} {l l' la la' lb lb' : Filter ℝ} {lt : Filter ι} {a b z : ℝ} {u v ua ub va vb : ι → ℝ}
  [FTCFilter a la la'] [FTCFilter b lb lb']

/-!
#### Auxiliary `is_o` statements

In this section we prove several lemmas that can be interpreted as strict differentiability of
`(u, v) ↦ ∫ x in u..v, f x ∂μ` in `u` and/or `v` at a filter. The statements use `is_o` because
we have no definition of `has_strict_(f)deriv_at_filter` in the library.
-/


/-- Fundamental theorem of calculus-1, local version. If `f` has a finite limit `c` almost surely at
`l'`, where `(l, l')` is an `FTC_filter` pair around `a`, then
`∫ x in u..v, f x ∂μ = (v - u) • c + o (v - u)` as both `u` and `v` tend to `l`. -/
theorem integral_sub_linear_is_o_of_tendsto_ae [FTCFilter a l l'] (hfm : StronglyMeasurableAtFilter f l')
    (hf : Tendsto f (l'⊓volume.ae) (𝓝 c)) {u v : ι → ℝ} (hu : Tendsto u lt l) (hv : Tendsto v lt l) :
    (fun t => (∫ x in u t..v t, f x) - (v t - u t) • c) =o[lt] (v - u) := by
  simpa [← integral_const] using measure_integral_sub_linear_is_o_of_tendsto_ae hfm hf hu hv

/-- Fundamental theorem of calculus-1, strict differentiability at filter in both endpoints.
If `f` is a measurable function integrable on `a..b`, `(la, la')` is an `FTC_filter` pair around
`a`, and `(lb, lb')` is an `FTC_filter` pair around `b`, and `f` has finite limits `ca` and `cb`
almost surely at `la'` and `lb'`, respectively, then
`(∫ x in va..vb, f x) - ∫ x in ua..ub, f x = (vb - ub) • cb - (va - ua) • ca +
  o(∥va - ua∥ + ∥vb - ub∥)` as `ua` and `va` tend to `la` while `ub` and `vb` tend to `lb`.

This lemma could've been formulated using `has_strict_fderiv_at_filter` if we had this
definition. -/
theorem integral_sub_integral_sub_linear_is_o_of_tendsto_ae (hab : IntervalIntegrable f volume a b)
    (hmeas_a : StronglyMeasurableAtFilter f la') (hmeas_b : StronglyMeasurableAtFilter f lb')
    (ha_lim : Tendsto f (la'⊓volume.ae) (𝓝 ca)) (hb_lim : Tendsto f (lb'⊓volume.ae) (𝓝 cb)) (hua : Tendsto ua lt la)
    (hva : Tendsto va lt la) (hub : Tendsto ub lt lb) (hvb : Tendsto vb lt lb) :
    (fun t => ((∫ x in va t..vb t, f x) - ∫ x in ua t..ub t, f x) - ((vb t - ub t) • cb - (va t - ua t) • ca)) =o[lt]
      fun t => ∥va t - ua t∥ + ∥vb t - ub t∥ :=
  by
  simpa [← integral_const] using
    measure_integral_sub_integral_sub_linear_is_o_of_tendsto_ae hab hmeas_a hmeas_b ha_lim hb_lim hua hva hub hvb

/-- Fundamental theorem of calculus-1, strict differentiability at filter in both endpoints.
If `f` is a measurable function integrable on `a..b`, `(lb, lb')` is an `FTC_filter` pair
around `b`, and `f` has a finite limit `c` almost surely at `lb'`, then
`(∫ x in a..v, f x) - ∫ x in a..u, f x = (v - u) • c + o(∥v - u∥)` as `u` and `v` tend to `lb`.

This lemma could've been formulated using `has_strict_deriv_at_filter` if we had this definition. -/
theorem integral_sub_integral_sub_linear_is_o_of_tendsto_ae_right (hab : IntervalIntegrable f volume a b)
    (hmeas : StronglyMeasurableAtFilter f lb') (hf : Tendsto f (lb'⊓volume.ae) (𝓝 c)) (hu : Tendsto u lt lb)
    (hv : Tendsto v lt lb) : (fun t => ((∫ x in a..v t, f x) - ∫ x in a..u t, f x) - (v t - u t) • c) =o[lt] (v - u) :=
  by
  simpa only [← integral_const, ← smul_eq_mul, ← mul_oneₓ] using
    measure_integral_sub_integral_sub_linear_is_o_of_tendsto_ae_right hab hmeas hf hu hv

/-- Fundamental theorem of calculus-1, strict differentiability at filter in both endpoints.
If `f` is a measurable function integrable on `a..b`, `(la, la')` is an `FTC_filter` pair
around `a`, and `f` has a finite limit `c` almost surely at `la'`, then
`(∫ x in v..b, f x) - ∫ x in u..b, f x = -(v - u) • c + o(∥v - u∥)` as `u` and `v` tend to `la`.

This lemma could've been formulated using `has_strict_deriv_at_filter` if we had this definition. -/
theorem integral_sub_integral_sub_linear_is_o_of_tendsto_ae_left (hab : IntervalIntegrable f volume a b)
    (hmeas : StronglyMeasurableAtFilter f la') (hf : Tendsto f (la'⊓volume.ae) (𝓝 c)) (hu : Tendsto u lt la)
    (hv : Tendsto v lt la) : (fun t => ((∫ x in v t..b, f x) - ∫ x in u t..b, f x) + (v t - u t) • c) =o[lt] (v - u) :=
  by
  simpa only [← integral_const, ← smul_eq_mul, ← mul_oneₓ] using
    measure_integral_sub_integral_sub_linear_is_o_of_tendsto_ae_left hab hmeas hf hu hv

open ContinuousLinearMap (fst snd smul_right sub_apply smul_right_apply coe_fst' coe_snd' map_sub)

/-!
#### Strict differentiability

In this section we prove that for a measurable function `f` integrable on `a..b`,

* `integral_has_strict_fderiv_at_of_tendsto_ae`: the function `(u, v) ↦ ∫ x in u..v, f x` has
  derivative `(u, v) ↦ v • cb - u • ca` at `(a, b)` in the sense of strict differentiability
  provided that `f` tends to `ca` and `cb` almost surely as `x` tendsto to `a` and `b`,
  respectively;

* `integral_has_strict_fderiv_at`: the function `(u, v) ↦ ∫ x in u..v, f x` has
  derivative `(u, v) ↦ v • f b - u • f a` at `(a, b)` in the sense of strict differentiability
  provided that `f` is continuous at `a` and `b`;

* `integral_has_strict_deriv_at_of_tendsto_ae_right`: the function `u ↦ ∫ x in a..u, f x` has
  derivative `c` at `b` in the sense of strict differentiability provided that `f` tends to `c`
  almost surely as `x` tends to `b`;

* `integral_has_strict_deriv_at_right`: the function `u ↦ ∫ x in a..u, f x` has derivative `f b` at
  `b` in the sense of strict differentiability provided that `f` is continuous at `b`;

* `integral_has_strict_deriv_at_of_tendsto_ae_left`: the function `u ↦ ∫ x in u..b, f x` has
  derivative `-c` at `a` in the sense of strict differentiability provided that `f` tends to `c`
  almost surely as `x` tends to `a`;

* `integral_has_strict_deriv_at_left`: the function `u ↦ ∫ x in u..b, f x` has derivative `-f a` at
  `a` in the sense of strict differentiability provided that `f` is continuous at `a`.
-/


/-- Fundamental theorem of calculus-1: if `f : ℝ → E` is integrable on `a..b` and `f x` has finite
limits `ca` and `cb` almost surely as `x` tends to `a` and `b`, respectively, then
`(u, v) ↦ ∫ x in u..v, f x` has derivative `(u, v) ↦ v • cb - u • ca` at `(a, b)`
in the sense of strict differentiability. -/
theorem integral_has_strict_fderiv_at_of_tendsto_ae (hf : IntervalIntegrable f volume a b)
    (hmeas_a : StronglyMeasurableAtFilter f (𝓝 a)) (hmeas_b : StronglyMeasurableAtFilter f (𝓝 b))
    (ha : Tendsto f (𝓝 a⊓volume.ae) (𝓝 ca)) (hb : Tendsto f (𝓝 b⊓volume.ae) (𝓝 cb)) :
    HasStrictFderivAt (fun p : ℝ × ℝ => ∫ x in p.1 ..p.2, f x) ((snd ℝ ℝ ℝ).smul_right cb - (fst ℝ ℝ ℝ).smul_right ca)
      (a, b) :=
  by
  have :=
    integral_sub_integral_sub_linear_is_o_of_tendsto_ae hf hmeas_a hmeas_b ha hb
      ((continuous_fst.comp continuous_snd).Tendsto ((a, b), (a, b)))
      ((continuous_fst.comp continuous_fst).Tendsto ((a, b), (a, b)))
      ((continuous_snd.comp continuous_snd).Tendsto ((a, b), (a, b)))
      ((continuous_snd.comp continuous_fst).Tendsto ((a, b), (a, b)))
  refine' (this.congr_left _).trans_is_O _
  · intro x
    simp [← sub_smul]
    
  · exact is_O_fst_prod.norm_left.add is_O_snd_prod.norm_left
    

/-- Fundamental theorem of calculus-1: if `f : ℝ → E` is integrable on `a..b` and `f` is continuous
at `a` and `b`, then `(u, v) ↦ ∫ x in u..v, f x` has derivative `(u, v) ↦ v • cb - u • ca`
at `(a, b)` in the sense of strict differentiability. -/
theorem integral_has_strict_fderiv_at (hf : IntervalIntegrable f volume a b)
    (hmeas_a : StronglyMeasurableAtFilter f (𝓝 a)) (hmeas_b : StronglyMeasurableAtFilter f (𝓝 b))
    (ha : ContinuousAt f a) (hb : ContinuousAt f b) :
    HasStrictFderivAt (fun p : ℝ × ℝ => ∫ x in p.1 ..p.2, f x)
      ((snd ℝ ℝ ℝ).smul_right (f b) - (fst ℝ ℝ ℝ).smul_right (f a)) (a, b) :=
  integral_has_strict_fderiv_at_of_tendsto_ae hf hmeas_a hmeas_b (ha.mono_left inf_le_left) (hb.mono_left inf_le_left)

/-- **First Fundamental Theorem of Calculus**: if `f : ℝ → E` is integrable on `a..b` and `f x` has
a finite limit `c` almost surely at `b`, then `u ↦ ∫ x in a..u, f x` has derivative `c` at `b` in
the sense of strict differentiability. -/
theorem integral_has_strict_deriv_at_of_tendsto_ae_right (hf : IntervalIntegrable f volume a b)
    (hmeas : StronglyMeasurableAtFilter f (𝓝 b)) (hb : Tendsto f (𝓝 b⊓volume.ae) (𝓝 c)) :
    HasStrictDerivAt (fun u => ∫ x in a..u, f x) c b :=
  integral_sub_integral_sub_linear_is_o_of_tendsto_ae_right hf hmeas hb continuous_at_snd continuous_at_fst

/-- Fundamental theorem of calculus-1: if `f : ℝ → E` is integrable on `a..b` and `f` is continuous
at `b`, then `u ↦ ∫ x in a..u, f x` has derivative `f b` at `b` in the sense of strict
differentiability. -/
theorem integral_has_strict_deriv_at_right (hf : IntervalIntegrable f volume a b)
    (hmeas : StronglyMeasurableAtFilter f (𝓝 b)) (hb : ContinuousAt f b) :
    HasStrictDerivAt (fun u => ∫ x in a..u, f x) (f b) b :=
  integral_has_strict_deriv_at_of_tendsto_ae_right hf hmeas (hb.mono_left inf_le_left)

/-- Fundamental theorem of calculus-1: if `f : ℝ → E` is integrable on `a..b` and `f x` has a finite
limit `c` almost surely at `a`, then `u ↦ ∫ x in u..b, f x` has derivative `-c` at `a` in the sense
of strict differentiability. -/
theorem integral_has_strict_deriv_at_of_tendsto_ae_left (hf : IntervalIntegrable f volume a b)
    (hmeas : StronglyMeasurableAtFilter f (𝓝 a)) (ha : Tendsto f (𝓝 a⊓volume.ae) (𝓝 c)) :
    HasStrictDerivAt (fun u => ∫ x in u..b, f x) (-c) a := by
  simpa only [integral_symm] using (integral_has_strict_deriv_at_of_tendsto_ae_right hf.symm hmeas ha).neg

/-- Fundamental theorem of calculus-1: if `f : ℝ → E` is integrable on `a..b` and `f` is continuous
at `a`, then `u ↦ ∫ x in u..b, f x` has derivative `-f a` at `a` in the sense of strict
differentiability. -/
theorem integral_has_strict_deriv_at_left (hf : IntervalIntegrable f volume a b)
    (hmeas : StronglyMeasurableAtFilter f (𝓝 a)) (ha : ContinuousAt f a) :
    HasStrictDerivAt (fun u => ∫ x in u..b, f x) (-f a) a := by
  simpa only [integral_symm] using (integral_has_strict_deriv_at_right hf.symm hmeas ha).neg

/-!
#### Fréchet differentiability

In this subsection we restate results from the previous subsection in terms of `has_fderiv_at`,
`has_deriv_at`, `fderiv`, and `deriv`.
-/


/-- Fundamental theorem of calculus-1: if `f : ℝ → E` is integrable on `a..b` and `f x` has finite
limits `ca` and `cb` almost surely as `x` tends to `a` and `b`, respectively, then
`(u, v) ↦ ∫ x in u..v, f x` has derivative `(u, v) ↦ v • cb - u • ca` at `(a, b)`. -/
theorem integral_has_fderiv_at_of_tendsto_ae (hf : IntervalIntegrable f volume a b)
    (hmeas_a : StronglyMeasurableAtFilter f (𝓝 a)) (hmeas_b : StronglyMeasurableAtFilter f (𝓝 b))
    (ha : Tendsto f (𝓝 a⊓volume.ae) (𝓝 ca)) (hb : Tendsto f (𝓝 b⊓volume.ae) (𝓝 cb)) :
    HasFderivAt (fun p : ℝ × ℝ => ∫ x in p.1 ..p.2, f x) ((snd ℝ ℝ ℝ).smul_right cb - (fst ℝ ℝ ℝ).smul_right ca)
      (a, b) :=
  (integral_has_strict_fderiv_at_of_tendsto_ae hf hmeas_a hmeas_b ha hb).HasFderivAt

/-- Fundamental theorem of calculus-1: if `f : ℝ → E` is integrable on `a..b` and `f` is continuous
at `a` and `b`, then `(u, v) ↦ ∫ x in u..v, f x` has derivative `(u, v) ↦ v • cb - u • ca`
at `(a, b)`. -/
theorem integral_has_fderiv_at (hf : IntervalIntegrable f volume a b) (hmeas_a : StronglyMeasurableAtFilter f (𝓝 a))
    (hmeas_b : StronglyMeasurableAtFilter f (𝓝 b)) (ha : ContinuousAt f a) (hb : ContinuousAt f b) :
    HasFderivAt (fun p : ℝ × ℝ => ∫ x in p.1 ..p.2, f x) ((snd ℝ ℝ ℝ).smul_right (f b) - (fst ℝ ℝ ℝ).smul_right (f a))
      (a, b) :=
  (integral_has_strict_fderiv_at hf hmeas_a hmeas_b ha hb).HasFderivAt

/-- Fundamental theorem of calculus-1: if `f : ℝ → E` is integrable on `a..b` and `f x` has finite
limits `ca` and `cb` almost surely as `x` tends to `a` and `b`, respectively, then `fderiv`
derivative of `(u, v) ↦ ∫ x in u..v, f x` at `(a, b)` equals `(u, v) ↦ v • cb - u • ca`. -/
theorem fderiv_integral_of_tendsto_ae (hf : IntervalIntegrable f volume a b)
    (hmeas_a : StronglyMeasurableAtFilter f (𝓝 a)) (hmeas_b : StronglyMeasurableAtFilter f (𝓝 b))
    (ha : Tendsto f (𝓝 a⊓volume.ae) (𝓝 ca)) (hb : Tendsto f (𝓝 b⊓volume.ae) (𝓝 cb)) :
    fderiv ℝ (fun p : ℝ × ℝ => ∫ x in p.1 ..p.2, f x) (a, b) = (snd ℝ ℝ ℝ).smul_right cb - (fst ℝ ℝ ℝ).smul_right ca :=
  (integral_has_fderiv_at_of_tendsto_ae hf hmeas_a hmeas_b ha hb).fderiv

/-- Fundamental theorem of calculus-1: if `f : ℝ → E` is integrable on `a..b` and `f` is continuous
at `a` and `b`, then `fderiv` derivative of `(u, v) ↦ ∫ x in u..v, f x` at `(a, b)` equals `(u, v) ↦
v • cb - u • ca`. -/
theorem fderiv_integral (hf : IntervalIntegrable f volume a b) (hmeas_a : StronglyMeasurableAtFilter f (𝓝 a))
    (hmeas_b : StronglyMeasurableAtFilter f (𝓝 b)) (ha : ContinuousAt f a) (hb : ContinuousAt f b) :
    fderiv ℝ (fun p : ℝ × ℝ => ∫ x in p.1 ..p.2, f x) (a, b) =
      (snd ℝ ℝ ℝ).smul_right (f b) - (fst ℝ ℝ ℝ).smul_right (f a) :=
  (integral_has_fderiv_at hf hmeas_a hmeas_b ha hb).fderiv

/-- Fundamental theorem of calculus-1: if `f : ℝ → E` is integrable on `a..b` and `f x` has a finite
limit `c` almost surely at `b`, then `u ↦ ∫ x in a..u, f x` has derivative `c` at `b`. -/
theorem integral_has_deriv_at_of_tendsto_ae_right (hf : IntervalIntegrable f volume a b)
    (hmeas : StronglyMeasurableAtFilter f (𝓝 b)) (hb : Tendsto f (𝓝 b⊓volume.ae) (𝓝 c)) :
    HasDerivAt (fun u => ∫ x in a..u, f x) c b :=
  (integral_has_strict_deriv_at_of_tendsto_ae_right hf hmeas hb).HasDerivAt

/-- Fundamental theorem of calculus-1: if `f : ℝ → E` is integrable on `a..b` and `f` is continuous
at `b`, then `u ↦ ∫ x in a..u, f x` has derivative `f b` at `b`. -/
theorem integral_has_deriv_at_right (hf : IntervalIntegrable f volume a b) (hmeas : StronglyMeasurableAtFilter f (𝓝 b))
    (hb : ContinuousAt f b) : HasDerivAt (fun u => ∫ x in a..u, f x) (f b) b :=
  (integral_has_strict_deriv_at_right hf hmeas hb).HasDerivAt

/-- Fundamental theorem of calculus: if `f : ℝ → E` is integrable on `a..b` and `f` has a finite
limit `c` almost surely at `b`, then the derivative of `u ↦ ∫ x in a..u, f x` at `b` equals `c`. -/
theorem deriv_integral_of_tendsto_ae_right (hf : IntervalIntegrable f volume a b)
    (hmeas : StronglyMeasurableAtFilter f (𝓝 b)) (hb : Tendsto f (𝓝 b⊓volume.ae) (𝓝 c)) :
    deriv (fun u => ∫ x in a..u, f x) b = c :=
  (integral_has_deriv_at_of_tendsto_ae_right hf hmeas hb).deriv

/-- Fundamental theorem of calculus: if `f : ℝ → E` is integrable on `a..b` and `f` is continuous
at `b`, then the derivative of `u ↦ ∫ x in a..u, f x` at `b` equals `f b`. -/
theorem deriv_integral_right (hf : IntervalIntegrable f volume a b) (hmeas : StronglyMeasurableAtFilter f (𝓝 b))
    (hb : ContinuousAt f b) : deriv (fun u => ∫ x in a..u, f x) b = f b :=
  (integral_has_deriv_at_right hf hmeas hb).deriv

/-- Fundamental theorem of calculus-1: if `f : ℝ → E` is integrable on `a..b` and `f x` has a finite
limit `c` almost surely at `a`, then `u ↦ ∫ x in u..b, f x` has derivative `-c` at `a`. -/
theorem integral_has_deriv_at_of_tendsto_ae_left (hf : IntervalIntegrable f volume a b)
    (hmeas : StronglyMeasurableAtFilter f (𝓝 a)) (ha : Tendsto f (𝓝 a⊓volume.ae) (𝓝 c)) :
    HasDerivAt (fun u => ∫ x in u..b, f x) (-c) a :=
  (integral_has_strict_deriv_at_of_tendsto_ae_left hf hmeas ha).HasDerivAt

/-- Fundamental theorem of calculus-1: if `f : ℝ → E` is integrable on `a..b` and `f` is continuous
at `a`, then `u ↦ ∫ x in u..b, f x` has derivative `-f a` at `a`. -/
theorem integral_has_deriv_at_left (hf : IntervalIntegrable f volume a b) (hmeas : StronglyMeasurableAtFilter f (𝓝 a))
    (ha : ContinuousAt f a) : HasDerivAt (fun u => ∫ x in u..b, f x) (-f a) a :=
  (integral_has_strict_deriv_at_left hf hmeas ha).HasDerivAt

/-- Fundamental theorem of calculus: if `f : ℝ → E` is integrable on `a..b` and `f` has a finite
limit `c` almost surely at `a`, then the derivative of `u ↦ ∫ x in u..b, f x` at `a` equals `-c`. -/
theorem deriv_integral_of_tendsto_ae_left (hf : IntervalIntegrable f volume a b)
    (hmeas : StronglyMeasurableAtFilter f (𝓝 a)) (hb : Tendsto f (𝓝 a⊓volume.ae) (𝓝 c)) :
    deriv (fun u => ∫ x in u..b, f x) a = -c :=
  (integral_has_deriv_at_of_tendsto_ae_left hf hmeas hb).deriv

/-- Fundamental theorem of calculus: if `f : ℝ → E` is integrable on `a..b` and `f` is continuous
at `a`, then the derivative of `u ↦ ∫ x in u..b, f x` at `a` equals `-f a`. -/
theorem deriv_integral_left (hf : IntervalIntegrable f volume a b) (hmeas : StronglyMeasurableAtFilter f (𝓝 a))
    (hb : ContinuousAt f a) : deriv (fun u => ∫ x in u..b, f x) a = -f a :=
  (integral_has_deriv_at_left hf hmeas hb).deriv

/-!
#### One-sided derivatives
-/


/-- Let `f` be a measurable function integrable on `a..b`. The function `(u, v) ↦ ∫ x in u..v, f x`
has derivative `(u, v) ↦ v • cb - u • ca` within `s × t` at `(a, b)`, where
`s ∈ {Iic a, {a}, Ici a, univ}` and `t ∈ {Iic b, {b}, Ici b, univ}` provided that `f` tends to `ca`
and `cb` almost surely at the filters `la` and `lb` from the following table.

| `s`     | `la`     | `t`     | `lb`     |
| ------- | ----     | ---     | ----     |
| `Iic a` | `𝓝[≤] a` | `Iic b` | `𝓝[≤] b` |
| `Ici a` | `𝓝[>] a` | `Ici b` | `𝓝[>] b` |
| `{a}`   | `⊥`      | `{b}`   | `⊥`      |
| `univ`  | `𝓝 a`    | `univ`  | `𝓝 b`    |
-/
theorem integral_has_fderiv_within_at_of_tendsto_ae (hf : IntervalIntegrable f volume a b) {s t : Set ℝ}
    [FTCFilter a (𝓝[s] a) la] [FTCFilter b (𝓝[t] b) lb] (hmeas_a : StronglyMeasurableAtFilter f la)
    (hmeas_b : StronglyMeasurableAtFilter f lb) (ha : Tendsto f (la⊓volume.ae) (𝓝 ca))
    (hb : Tendsto f (lb⊓volume.ae) (𝓝 cb)) :
    HasFderivWithinAt (fun p : ℝ × ℝ => ∫ x in p.1 ..p.2, f x) ((snd ℝ ℝ ℝ).smul_right cb - (fst ℝ ℝ ℝ).smul_right ca)
      (s ×ˢ t) (a, b) :=
  by
  rw [HasFderivWithinAt, nhds_within_prod_eq]
  have :=
    integral_sub_integral_sub_linear_is_o_of_tendsto_ae hf hmeas_a hmeas_b ha hb
      (tendsto_const_pure.mono_right FTC_filter.pure_le : tendsto _ _ (𝓝[s] a)) tendsto_fst
      (tendsto_const_pure.mono_right FTC_filter.pure_le : tendsto _ _ (𝓝[t] b)) tendsto_snd
  refine' (this.congr_left _).trans_is_O _
  · intro x
    simp [← sub_smul]
    
  · exact is_O_fst_prod.norm_left.add is_O_snd_prod.norm_left
    

/-- Let `f` be a measurable function integrable on `a..b`. The function `(u, v) ↦ ∫ x in u..v, f x`
has derivative `(u, v) ↦ v • f b - u • f a` within `s × t` at `(a, b)`, where
`s ∈ {Iic a, {a}, Ici a, univ}` and `t ∈ {Iic b, {b}, Ici b, univ}` provided that `f` tends to
`f a` and `f b` at the filters `la` and `lb` from the following table. In most cases this assumption
is definitionally equal `continuous_at f _` or `continuous_within_at f _ _`.

| `s`     | `la`     | `t`     | `lb`     |
| ------- | ----     | ---     | ----     |
| `Iic a` | `𝓝[≤] a` | `Iic b` | `𝓝[≤] b` |
| `Ici a` | `𝓝[>] a` | `Ici b` | `𝓝[>] b` |
| `{a}`   | `⊥`      | `{b}`   | `⊥`      |
| `univ`  | `𝓝 a`    | `univ`  | `𝓝 b`    |
-/
theorem integral_has_fderiv_within_at (hf : IntervalIntegrable f volume a b) (hmeas_a : StronglyMeasurableAtFilter f la)
    (hmeas_b : StronglyMeasurableAtFilter f lb) {s t : Set ℝ} [FTCFilter a (𝓝[s] a) la] [FTCFilter b (𝓝[t] b) lb]
    (ha : Tendsto f la (𝓝 <| f a)) (hb : Tendsto f lb (𝓝 <| f b)) :
    HasFderivWithinAt (fun p : ℝ × ℝ => ∫ x in p.1 ..p.2, f x)
      ((snd ℝ ℝ ℝ).smul_right (f b) - (fst ℝ ℝ ℝ).smul_right (f a)) (s ×ˢ t) (a, b) :=
  integral_has_fderiv_within_at_of_tendsto_ae hf hmeas_a hmeas_b (ha.mono_left inf_le_left) (hb.mono_left inf_le_left)

-- ./././Mathport/Syntax/Translate/Basic.lean:1087:4: warning: unsupported (TODO): `[tacs]
/-- An auxiliary tactic closing goals `unique_diff_within_at ℝ s a` where
`s ∈ {Iic a, Ici a, univ}`. -/
unsafe def unique_diff_within_at_Ici_Iic_univ : tactic Unit :=
  sorry

/-- Let `f` be a measurable function integrable on `a..b`. Choose `s ∈ {Iic a, Ici a, univ}`
and `t ∈ {Iic b, Ici b, univ}`. Suppose that `f` tends to `ca` and `cb` almost surely at the filters
`la` and `lb` from the table below. Then `fderiv_within ℝ (λ p, ∫ x in p.1..p.2, f x) (s ×ˢ t)`
is equal to `(u, v) ↦ u • cb - v • ca`.

| `s`     | `la`     | `t`     | `lb`     |
| ------- | ----     | ---     | ----     |
| `Iic a` | `𝓝[≤] a` | `Iic b` | `𝓝[≤] b` |
| `Ici a` | `𝓝[>] a` | `Ici b` | `𝓝[>] b` |
| `{a}`   | `⊥`      | `{b}`   | `⊥`      |
| `univ`  | `𝓝 a`    | `univ`  | `𝓝 b`    |
-/
theorem fderiv_within_integral_of_tendsto_ae (hf : IntervalIntegrable f volume a b)
    (hmeas_a : StronglyMeasurableAtFilter f la) (hmeas_b : StronglyMeasurableAtFilter f lb) {s t : Set ℝ}
    [FTCFilter a (𝓝[s] a) la] [FTCFilter b (𝓝[t] b) lb] (ha : Tendsto f (la⊓volume.ae) (𝓝 ca))
    (hb : Tendsto f (lb⊓volume.ae) (𝓝 cb))
    (hs : UniqueDiffWithinAt ℝ s a := by
      run_tac
        unique_diff_within_at_Ici_Iic_univ)
    (ht : UniqueDiffWithinAt ℝ t b := by
      run_tac
        unique_diff_within_at_Ici_Iic_univ) :
    fderivWithin ℝ (fun p : ℝ × ℝ => ∫ x in p.1 ..p.2, f x) (s ×ˢ t) (a, b) =
      (snd ℝ ℝ ℝ).smul_right cb - (fst ℝ ℝ ℝ).smul_right ca :=
  (integral_has_fderiv_within_at_of_tendsto_ae hf hmeas_a hmeas_b ha hb).fderivWithin <| hs.Prod ht

/-- Fundamental theorem of calculus: if `f : ℝ → E` is integrable on `a..b` and `f x` has a finite
limit `c` almost surely as `x` tends to `b` from the right or from the left,
then `u ↦ ∫ x in a..u, f x` has right (resp., left) derivative `c` at `b`. -/
theorem integral_has_deriv_within_at_of_tendsto_ae_right (hf : IntervalIntegrable f volume a b) {s t : Set ℝ}
    [FTCFilter b (𝓝[s] b) (𝓝[t] b)] (hmeas : StronglyMeasurableAtFilter f (𝓝[t] b))
    (hb : Tendsto f (𝓝[t] b⊓volume.ae) (𝓝 c)) : HasDerivWithinAt (fun u => ∫ x in a..u, f x) c s b :=
  integral_sub_integral_sub_linear_is_o_of_tendsto_ae_right hf hmeas hb
    (tendsto_const_pure.mono_right FTCFilter.pure_le) tendsto_id

/-- Fundamental theorem of calculus: if `f : ℝ → E` is integrable on `a..b` and `f x` is continuous
from the left or from the right at `b`, then `u ↦ ∫ x in a..u, f x` has left (resp., right)
derivative `f b` at `b`. -/
theorem integral_has_deriv_within_at_right (hf : IntervalIntegrable f volume a b) {s t : Set ℝ}
    [FTCFilter b (𝓝[s] b) (𝓝[t] b)] (hmeas : StronglyMeasurableAtFilter f (𝓝[t] b)) (hb : ContinuousWithinAt f t b) :
    HasDerivWithinAt (fun u => ∫ x in a..u, f x) (f b) s b :=
  integral_has_deriv_within_at_of_tendsto_ae_right hf hmeas (hb.mono_left inf_le_left)

/-- Fundamental theorem of calculus: if `f : ℝ → E` is integrable on `a..b` and `f x` has a finite
limit `c` almost surely as `x` tends to `b` from the right or from the left, then the right
(resp., left) derivative of `u ↦ ∫ x in a..u, f x` at `b` equals `c`. -/
theorem deriv_within_integral_of_tendsto_ae_right (hf : IntervalIntegrable f volume a b) {s t : Set ℝ}
    [FTCFilter b (𝓝[s] b) (𝓝[t] b)] (hmeas : StronglyMeasurableAtFilter f (𝓝[t] b))
    (hb : Tendsto f (𝓝[t] b⊓volume.ae) (𝓝 c))
    (hs : UniqueDiffWithinAt ℝ s b := by
      run_tac
        unique_diff_within_at_Ici_Iic_univ) :
    derivWithin (fun u => ∫ x in a..u, f x) s b = c :=
  (integral_has_deriv_within_at_of_tendsto_ae_right hf hmeas hb).derivWithin hs

/-- Fundamental theorem of calculus: if `f : ℝ → E` is integrable on `a..b` and `f x` is continuous
on the right or on the left at `b`, then the right (resp., left) derivative of
`u ↦ ∫ x in a..u, f x` at `b` equals `f b`. -/
theorem deriv_within_integral_right (hf : IntervalIntegrable f volume a b) {s t : Set ℝ} [FTCFilter b (𝓝[s] b) (𝓝[t] b)]
    (hmeas : StronglyMeasurableAtFilter f (𝓝[t] b)) (hb : ContinuousWithinAt f t b)
    (hs : UniqueDiffWithinAt ℝ s b := by
      run_tac
        unique_diff_within_at_Ici_Iic_univ) :
    derivWithin (fun u => ∫ x in a..u, f x) s b = f b :=
  (integral_has_deriv_within_at_right hf hmeas hb).derivWithin hs

/-- Fundamental theorem of calculus: if `f : ℝ → E` is integrable on `a..b` and `f x` has a finite
limit `c` almost surely as `x` tends to `a` from the right or from the left,
then `u ↦ ∫ x in u..b, f x` has right (resp., left) derivative `-c` at `a`. -/
theorem integral_has_deriv_within_at_of_tendsto_ae_left (hf : IntervalIntegrable f volume a b) {s t : Set ℝ}
    [FTCFilter a (𝓝[s] a) (𝓝[t] a)] (hmeas : StronglyMeasurableAtFilter f (𝓝[t] a))
    (ha : Tendsto f (𝓝[t] a⊓volume.ae) (𝓝 c)) : HasDerivWithinAt (fun u => ∫ x in u..b, f x) (-c) s a := by
  simp only [← integral_symm b]
  exact (integral_has_deriv_within_at_of_tendsto_ae_right hf.symm hmeas ha).neg

/-- Fundamental theorem of calculus: if `f : ℝ → E` is integrable on `a..b` and `f x` is continuous
from the left or from the right at `a`, then `u ↦ ∫ x in u..b, f x` has left (resp., right)
derivative `-f a` at `a`. -/
theorem integral_has_deriv_within_at_left (hf : IntervalIntegrable f volume a b) {s t : Set ℝ}
    [FTCFilter a (𝓝[s] a) (𝓝[t] a)] (hmeas : StronglyMeasurableAtFilter f (𝓝[t] a)) (ha : ContinuousWithinAt f t a) :
    HasDerivWithinAt (fun u => ∫ x in u..b, f x) (-f a) s a :=
  integral_has_deriv_within_at_of_tendsto_ae_left hf hmeas (ha.mono_left inf_le_left)

/-- Fundamental theorem of calculus: if `f : ℝ → E` is integrable on `a..b` and `f x` has a finite
limit `c` almost surely as `x` tends to `a` from the right or from the left, then the right
(resp., left) derivative of `u ↦ ∫ x in u..b, f x` at `a` equals `-c`. -/
theorem deriv_within_integral_of_tendsto_ae_left (hf : IntervalIntegrable f volume a b) {s t : Set ℝ}
    [FTCFilter a (𝓝[s] a) (𝓝[t] a)] (hmeas : StronglyMeasurableAtFilter f (𝓝[t] a))
    (ha : Tendsto f (𝓝[t] a⊓volume.ae) (𝓝 c))
    (hs : UniqueDiffWithinAt ℝ s a := by
      run_tac
        unique_diff_within_at_Ici_Iic_univ) :
    derivWithin (fun u => ∫ x in u..b, f x) s a = -c :=
  (integral_has_deriv_within_at_of_tendsto_ae_left hf hmeas ha).derivWithin hs

/-- Fundamental theorem of calculus: if `f : ℝ → E` is integrable on `a..b` and `f x` is continuous
on the right or on the left at `a`, then the right (resp., left) derivative of
`u ↦ ∫ x in u..b, f x` at `a` equals `-f a`. -/
theorem deriv_within_integral_left (hf : IntervalIntegrable f volume a b) {s t : Set ℝ} [FTCFilter a (𝓝[s] a) (𝓝[t] a)]
    (hmeas : StronglyMeasurableAtFilter f (𝓝[t] a)) (ha : ContinuousWithinAt f t a)
    (hs : UniqueDiffWithinAt ℝ s a := by
      run_tac
        unique_diff_within_at_Ici_Iic_univ) :
    derivWithin (fun u => ∫ x in u..b, f x) s a = -f a :=
  (integral_has_deriv_within_at_left hf hmeas ha).derivWithin hs

/-- The integral of a continuous function is differentiable on a real set `s`. -/
theorem differentiable_on_integral_of_continuous {s : Set ℝ} (hintg : ∀, ∀ x ∈ s, ∀, IntervalIntegrable f volume a x)
    (hcont : Continuous f) : DifferentiableOn ℝ (fun u => ∫ x in a..u, f x) s := fun y hy =>
  (integral_has_deriv_at_right (hintg y hy) hcont.AeStronglyMeasurable.StronglyMeasurableAtFilter
        hcont.ContinuousAt).DifferentiableAt.DifferentiableWithinAt

/-!
### Fundamental theorem of calculus, part 2

This section contains theorems pertaining to FTC-2 for interval integrals, i.e., the assertion
that `∫ x in a..b, f' x = f b - f a` under suitable assumptions.

The most classical version of this theorem assumes that `f'` is continuous. However, this is
unnecessarily strong: the result holds if `f'` is just integrable. We prove the strong version,
following [Rudin, *Real and Complex Analysis* (Theorem 7.21)][rudin2006real]. The proof is first
given for real-valued functions, and then deduced for functions with a general target space. For
a real-valued function `g`, it suffices to show that `g b - g a ≤ (∫ x in a..b, g' x) + ε` for all
positive `ε`. To prove this, choose a lower-semicontinuous function `G'` with `g' < G'` and with
integral close to that of `g'` (its existence is guaranteed by the Vitali-Carathéodory theorem).
It satisfies `g t - g a ≤ ∫ x in a..t, G' x` for all `t ∈ [a, b]`: this inequality holds at `a`,
and if it holds at `t` then it holds for `u` close to `t` on its right, as the left hand side
increases by `g u - g t ∼ (u -t) g' t`, while the right hand side increases by
`∫ x in t..u, G' x` which is roughly at least `∫ x in t..u, G' t = (u - t) G' t`, by lower
semicontinuity. As  `g' t < G' t`, this gives the conclusion. One can therefore push progressively
this inequality to the right until the point `b`, where it gives the desired conclusion.
-/


variable {g' g φ : ℝ → ℝ}

/-- Hard part of FTC-2 for integrable derivatives, real-valued functions: one has
`g b - g a ≤ ∫ y in a..b, g' y` when `g'` is integrable.
Auxiliary lemma in the proof of `integral_eq_sub_of_has_deriv_right_of_le`.
We give the slightly more general version that `g b - g a ≤ ∫ y in a..b, φ y` when `g' ≤ φ` and
`φ` is integrable (even if `g'` is not known to be integrable).
Version assuming that `g` is differentiable on `[a, b)`. -/
theorem sub_le_integral_of_has_deriv_right_of_le_Ico (hab : a ≤ b) (hcont : ContinuousOn g (Icc a b))
    (hderiv : ∀, ∀ x ∈ Ico a b, ∀, HasDerivWithinAt g (g' x) (Ioi x) x) (φint : IntegrableOn φ (Icc a b))
    (hφg : ∀, ∀ x ∈ Ico a b, ∀, g' x ≤ φ x) : g b - g a ≤ ∫ y in a..b, φ y := by
  refine' le_of_forall_pos_le_add fun ε εpos => _
  -- Bound from above `g'` by a lower-semicontinuous function `G'`.
  rcases exists_lt_lower_semicontinuous_integral_lt φ φint εpos with ⟨G', f_lt_G', G'cont, G'int, G'lt_top, hG'⟩
  -- we will show by "induction" that `g t - g a ≤ ∫ u in a..t, G' u` for all `t ∈ [a, b]`.
  set s := { t | g t - g a ≤ ∫ u in a..t, (G' u).toReal } ∩ Icc a b
  -- the set `s` of points where this property holds is closed.
  have s_closed : IsClosed s := by
    have : ContinuousOn (fun t => (g t - g a, ∫ u in a..t, (G' u).toReal)) (Icc a b) := by
      rw [← interval_of_le hab] at G'int hcont⊢
      exact (hcont.sub continuous_on_const).Prod (continuous_on_primitive_interval G'int)
    simp only [← s, ← inter_comm]
    exact this.preimage_closed_of_closed is_closed_Icc OrderClosedTopology.is_closed_le'
  have main : Icc a b ⊆ { t | g t - g a ≤ ∫ u in a..t, (G' u).toReal } := by
    -- to show that the set `s` is all `[a, b]`, it suffices to show that any point `t` in `s`
    -- with `t < b` admits another point in `s` slightly to its right
    -- (this is a sort of real induction).
    apply
      s_closed.Icc_subset_of_forall_exists_gt
        (by
          simp only [← integral_same, ← mem_set_of_eq, ← sub_self])
        fun t ht v t_lt_v => _
    obtain ⟨y, g'_lt_y', y_lt_G'⟩ : ∃ y : ℝ, (g' t : Ereal) < y ∧ (y : Ereal) < G' t :=
      Ereal.lt_iff_exists_real_btwn.1 ((Ereal.coe_le_coe_iff.2 (hφg t ht.2)).trans_lt (f_lt_G' t))
    -- bound from below the increase of `∫ x in a..u, G' x` on the right of `t`, using the lower
    -- semicontinuity of `G'`.
    have I1 : ∀ᶠ u in 𝓝[>] t, (u - t) * y ≤ ∫ w in t..u, (G' w).toReal := by
      have B : ∀ᶠ u in 𝓝 t, (y : Ereal) < G' u := G'cont.lower_semicontinuous_at _ _ y_lt_G'
      rcases mem_nhds_iff_exists_Ioo_subset.1 B with ⟨m, M, ⟨hm, hM⟩, H⟩
      have : Ioo t (min M b) ∈ 𝓝[>] t :=
        mem_nhds_within_Ioi_iff_exists_Ioo_subset.2
          ⟨min M b, by
            simp only [← hM, ← ht.right.right, ← lt_min_iff, ← mem_Ioi, ← and_selfₓ], subset.refl _⟩
      filter_upwards [this] with u hu
      have I : Icc t u ⊆ Icc a b := Icc_subset_Icc ht.2.1 (hu.2.le.trans (min_le_rightₓ _ _))
      calc (u - t) * y = ∫ v in Icc t u, y := by
          simp only [← hu.left.le, ← MeasureTheory.integral_const, ← Algebra.id.smul_eq_mul, ← sub_nonneg, ←
            MeasurableSet.univ, ← Real.volume_Icc, ← measure.restrict_apply, ← univ_inter, ←
            Ennreal.to_real_of_real]_ ≤ ∫ w in t..u, (G' w).toReal :=
          by
          rw [intervalIntegral.integral_of_le hu.1.le, ← integral_Icc_eq_integral_Ioc]
          apply set_integral_mono_ae_restrict
          · simp only [← integrable_on_const, ← Real.volume_Icc, ← Ennreal.of_real_lt_top, ← or_trueₓ]
            
          · exact integrable_on.mono_set G'int I
            
          · have C1 : ∀ᵐ x : ℝ ∂volume.restrict (Icc t u), G' x < ∞ := ae_mono (measure.restrict_mono I le_rfl) G'lt_top
            have C2 : ∀ᵐ x : ℝ ∂volume.restrict (Icc t u), x ∈ Icc t u := ae_restrict_mem measurable_set_Icc
            filter_upwards [C1, C2] with x G'x hx
            apply Ereal.coe_le_coe_iff.1
            have : x ∈ Ioo m M := by
              simp only [← hm.trans_le hx.left, ← (hx.right.trans_lt hu.right).trans_le (min_le_leftₓ M b), ← mem_Ioo, ←
                and_selfₓ]
            convert le_of_ltₓ (H this)
            exact Ereal.coe_to_real G'x.ne (ne_bot_of_gt (f_lt_G' x))
            
    -- bound from above the increase of `g u - g a` on the right of `t`, using the derivative at `t`
    have I2 : ∀ᶠ u in 𝓝[>] t, g u - g t ≤ (u - t) * y := by
      have g'_lt_y : g' t < y := Ereal.coe_lt_coe_iff.1 g'_lt_y'
      filter_upwards [(hderiv t ⟨ht.2.1, ht.2.2⟩).limsup_slope_le' (not_mem_Ioi.2 le_rfl) g'_lt_y,
        self_mem_nhds_within] with u hu t_lt_u
      have := mul_le_mul_of_nonneg_left hu.le (sub_pos.2 t_lt_u).le
      rwa [← smul_eq_mul, sub_smul_slope] at this
    -- combine the previous two bounds to show that `g u - g a` increases less quickly than
    -- `∫ x in a..u, G' x`.
    have I3 : ∀ᶠ u in 𝓝[>] t, g u - g t ≤ ∫ w in t..u, (G' w).toReal := by
      filter_upwards [I1, I2] with u hu1 hu2 using hu2.trans hu1
    have I4 : ∀ᶠ u in 𝓝[>] t, u ∈ Ioc t (min v b) := by
      refine' mem_nhds_within_Ioi_iff_exists_Ioc_subset.2 ⟨min v b, _, subset.refl _⟩
      simp only [← lt_min_iff, ← mem_Ioi]
      exact ⟨t_lt_v, ht.2.2⟩
    -- choose a point `x` slightly to the right of `t` which satisfies the above bound
    rcases(I3.and I4).exists with ⟨x, hx, h'x⟩
    -- we check that it belongs to `s`, essentially by construction
    refine' ⟨x, _, Ioc_subset_Ioc le_rfl (min_le_leftₓ _ _) h'x⟩
    calc g x - g a = g t - g a + (g x - g t) := by
        abel _ ≤ (∫ w in a..t, (G' w).toReal) + ∫ w in t..x, (G' w).toReal :=
        add_le_add ht.1 hx _ = ∫ w in a..x, (G' w).toReal := by
        apply integral_add_adjacent_intervals
        · rw [interval_integrable_iff_integrable_Ioc_of_le ht.2.1]
          exact integrable_on.mono_set G'int (Ioc_subset_Icc_self.trans (Icc_subset_Icc le_rfl ht.2.2.le))
          
        · rw [interval_integrable_iff_integrable_Ioc_of_le h'x.1.le]
          apply integrable_on.mono_set G'int
          refine' Ioc_subset_Icc_self.trans (Icc_subset_Icc ht.2.1 (h'x.2.trans (min_le_rightₓ _ _)))
          
  -- now that we know that `s` contains `[a, b]`, we get the desired result by applying this to `b`.
  calc g b - g a ≤ ∫ y in a..b, (G' y).toReal := main (right_mem_Icc.2 hab)_ ≤ (∫ y in a..b, φ y) + ε := by
      convert hG'.le <;>
        · rw [intervalIntegral.integral_of_le hab]
          simp only [← integral_Icc_eq_integral_Ioc', ← Real.volume_singleton]
          

/-- Hard part of FTC-2 for integrable derivatives, real-valued functions: one has
`g b - g a ≤ ∫ y in a..b, g' y` when `g'` is integrable.
Auxiliary lemma in the proof of `integral_eq_sub_of_has_deriv_right_of_le`.
We give the slightly more general version that `g b - g a ≤ ∫ y in a..b, φ y` when `g' ≤ φ` and
`φ` is integrable (even if `g'` is not known to be integrable).
Version assuming that `g` is differentiable on `(a, b)`. -/
theorem sub_le_integral_of_has_deriv_right_of_le (hab : a ≤ b) (hcont : ContinuousOn g (Icc a b))
    (hderiv : ∀, ∀ x ∈ Ioo a b, ∀, HasDerivWithinAt g (g' x) (Ioi x) x) (φint : IntegrableOn φ (Icc a b))
    (hφg : ∀, ∀ x ∈ Ioo a b, ∀, g' x ≤ φ x) : g b - g a ≤ ∫ y in a..b, φ y := by
  -- This follows from the version on a closed-open interval (applied to `[t, b)` for `t` close to
  -- `a`) and a continuity argument.
  obtain rfl | a_lt_b := hab.eq_or_lt
  · simp
    
  set s := { t | g b - g t ≤ ∫ u in t..b, φ u } ∩ Icc a b
  have s_closed : IsClosed s := by
    have : ContinuousOn (fun t => (g b - g t, ∫ u in t..b, φ u)) (Icc a b) := by
      rw [← interval_of_le hab] at hcont φint⊢
      exact (continuous_on_const.sub hcont).Prod (continuous_on_primitive_interval_left φint)
    simp only [← s, ← inter_comm]
    exact this.preimage_closed_of_closed is_closed_Icc is_closed_le_prod
  have A : Closure (Ioc a b) ⊆ s := by
    apply s_closed.closure_subset_iff.2
    intro t ht
    refine' ⟨_, ⟨ht.1.le, ht.2⟩⟩
    exact
      sub_le_integral_of_has_deriv_right_of_le_Ico ht.2 (hcont.mono (Icc_subset_Icc ht.1.le le_rfl))
        (fun x hx => hderiv x ⟨ht.1.trans_le hx.1, hx.2⟩) (φint.mono_set (Icc_subset_Icc ht.1.le le_rfl)) fun x hx =>
        hφg x ⟨ht.1.trans_le hx.1, hx.2⟩
  rw [closure_Ioc a_lt_b.ne] at A
  exact (A (left_mem_Icc.2 hab)).1

/-- Auxiliary lemma in the proof of `integral_eq_sub_of_has_deriv_right_of_le`. -/
theorem integral_le_sub_of_has_deriv_right_of_le (hab : a ≤ b) (hcont : ContinuousOn g (Icc a b))
    (hderiv : ∀, ∀ x ∈ Ioo a b, ∀, HasDerivWithinAt g (g' x) (Ioi x) x) (φint : IntegrableOn φ (Icc a b))
    (hφg : ∀, ∀ x ∈ Ioo a b, ∀, φ x ≤ g' x) : (∫ y in a..b, φ y) ≤ g b - g a := by
  rw [← neg_le_neg_iff]
  convert
    sub_le_integral_of_has_deriv_right_of_le hab hcont.neg (fun x hx => (hderiv x hx).neg) φint.neg fun x hx =>
      neg_le_neg (hφg x hx)
  · abel
    
  · simp only [integral_neg]
    rfl
    

/-- Auxiliary lemma in the proof of `integral_eq_sub_of_has_deriv_right_of_le`: real version -/
theorem integral_eq_sub_of_has_deriv_right_of_le_real (hab : a ≤ b) (hcont : ContinuousOn g (Icc a b))
    (hderiv : ∀, ∀ x ∈ Ioo a b, ∀, HasDerivWithinAt g (g' x) (Ioi x) x) (g'int : IntegrableOn g' (Icc a b)) :
    (∫ y in a..b, g' y) = g b - g a :=
  le_antisymmₓ (integral_le_sub_of_has_deriv_right_of_le hab hcont hderiv g'int fun x hx => le_rfl)
    (sub_le_integral_of_has_deriv_right_of_le hab hcont hderiv g'int fun x hx => le_rfl)

variable {f' : ℝ → E}

/-- **Fundamental theorem of calculus-2**: If `f : ℝ → E` is continuous on `[a, b]` (where `a ≤ b`)
  and has a right derivative at `f' x` for all `x` in `(a, b)`, and `f'` is integrable on `[a, b]`,
  then `∫ y in a..b, f' y` equals `f b - f a`. -/
theorem integral_eq_sub_of_has_deriv_right_of_le (hab : a ≤ b) (hcont : ContinuousOn f (Icc a b))
    (hderiv : ∀, ∀ x ∈ Ioo a b, ∀, HasDerivWithinAt f (f' x) (Ioi x) x) (f'int : IntervalIntegrable f' volume a b) :
    (∫ y in a..b, f' y) = f b - f a := by
  refine' (NormedSpace.eq_iff_forall_dual_eq ℝ).2 fun g => _
  rw [← g.interval_integral_comp_comm f'int, g.map_sub]
  exact
    integral_eq_sub_of_has_deriv_right_of_le_real hab (g.continuous.comp_continuous_on hcont)
      (fun x hx => g.has_fderiv_at.comp_has_deriv_within_at x (hderiv x hx))
      (g.integrable_comp ((interval_integrable_iff_integrable_Icc_of_le hab).1 f'int))

/-- Fundamental theorem of calculus-2: If `f : ℝ → E` is continuous on `[a, b]` and
  has a right derivative at `f' x` for all `x` in `[a, b)`, and `f'` is integrable on `[a, b]` then
  `∫ y in a..b, f' y` equals `f b - f a`. -/
theorem integral_eq_sub_of_has_deriv_right (hcont : ContinuousOn f (Interval a b))
    (hderiv : ∀, ∀ x ∈ Ioo (min a b) (max a b), ∀, HasDerivWithinAt f (f' x) (Ioi x) x)
    (hint : IntervalIntegrable f' volume a b) : (∫ y in a..b, f' y) = f b - f a := by
  cases' le_totalₓ a b with hab hab
  · simp only [← interval_of_le, ← min_eq_leftₓ, ← max_eq_rightₓ, ← hab] at hcont hderiv hint
    apply integral_eq_sub_of_has_deriv_right_of_le hab hcont hderiv hint
    
  · simp only [← interval_of_ge, ← min_eq_rightₓ, ← max_eq_leftₓ, ← hab] at hcont hderiv
    rw [integral_symm, integral_eq_sub_of_has_deriv_right_of_le hab hcont hderiv hint.symm, neg_sub]
    

/-- Fundamental theorem of calculus-2: If `f : ℝ → E` is continuous on `[a, b]` (where `a ≤ b`) and
  has a derivative at `f' x` for all `x` in `(a, b)`, and `f'` is integrable on `[a, b]`, then
  `∫ y in a..b, f' y` equals `f b - f a`. -/
theorem integral_eq_sub_of_has_deriv_at_of_le (hab : a ≤ b) (hcont : ContinuousOn f (Icc a b))
    (hderiv : ∀, ∀ x ∈ Ioo a b, ∀, HasDerivAt f (f' x) x) (hint : IntervalIntegrable f' volume a b) :
    (∫ y in a..b, f' y) = f b - f a :=
  integral_eq_sub_of_has_deriv_right_of_le hab hcont (fun x hx => (hderiv x hx).HasDerivWithinAt) hint

/-- Fundamental theorem of calculus-2: If `f : ℝ → E` has a derivative at `f' x` for all `x` in
  `[a, b]` and `f'` is integrable on `[a, b]`, then `∫ y in a..b, f' y` equals `f b - f a`. -/
theorem integral_eq_sub_of_has_deriv_at (hderiv : ∀, ∀ x ∈ Interval a b, ∀, HasDerivAt f (f' x) x)
    (hint : IntervalIntegrable f' volume a b) : (∫ y in a..b, f' y) = f b - f a :=
  integral_eq_sub_of_has_deriv_right (HasDerivAt.continuous_on hderiv)
    (fun x hx => (hderiv _ (mem_Icc_of_Ioo hx)).HasDerivWithinAt) hint

theorem integral_eq_sub_of_has_deriv_at_of_tendsto (hab : a < b) {fa fb}
    (hderiv : ∀, ∀ x ∈ Ioo a b, ∀, HasDerivAt f (f' x) x) (hint : IntervalIntegrable f' volume a b)
    (ha : Tendsto f (𝓝[>] a) (𝓝 fa)) (hb : Tendsto f (𝓝[<] b) (𝓝 fb)) : (∫ y in a..b, f' y) = fb - fa := by
  set F : ℝ → E := update (update f a fa) b fb
  have Fderiv : ∀, ∀ x ∈ Ioo a b, ∀, HasDerivAt F (f' x) x := by
    refine' fun x hx => (hderiv x hx).congr_of_eventually_eq _
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with _ hy
    simp only [← F]
    rw [update_noteq hy.2.Ne, update_noteq hy.1.ne']
  have hcont : ContinuousOn F (Icc a b) := by
    rw [continuous_on_update_iff, continuous_on_update_iff, Icc_diff_right, Ico_diff_left]
    refine' ⟨⟨fun z hz => (hderiv z hz).ContinuousAt.ContinuousWithinAt, _⟩, _⟩
    · exact fun _ => ha.mono_left (nhds_within_mono _ Ioo_subset_Ioi_self)
      
    · rintro -
      refine' (hb.congr' _).mono_left (nhds_within_mono _ Ico_subset_Iio_self)
      filter_upwards [Ioo_mem_nhds_within_Iio (right_mem_Ioc.2 hab)] with _ hz using(update_noteq hz.1.ne' _ _).symm
      
  simpa [← F, ← hab.ne, ← hab.ne'] using integral_eq_sub_of_has_deriv_at_of_le hab.le hcont Fderiv hint

/-- Fundamental theorem of calculus-2: If `f : ℝ → E` is differentiable at every `x` in `[a, b]` and
  its derivative is integrable on `[a, b]`, then `∫ y in a..b, deriv f y` equals `f b - f a`. -/
theorem integral_deriv_eq_sub (hderiv : ∀, ∀ x ∈ Interval a b, ∀, DifferentiableAt ℝ f x)
    (hint : IntervalIntegrable (deriv f) volume a b) : (∫ y in a..b, deriv f y) = f b - f a :=
  integral_eq_sub_of_has_deriv_at (fun x hx => (hderiv x hx).HasDerivAt) hint

theorem integral_deriv_eq_sub' (f) (hderiv : deriv f = f') (hdiff : ∀, ∀ x ∈ Interval a b, ∀, DifferentiableAt ℝ f x)
    (hcont : ContinuousOn f' (Interval a b)) : (∫ y in a..b, f' y) = f b - f a := by
  rw [← hderiv, integral_deriv_eq_sub hdiff]
  rw [hderiv]
  exact hcont.interval_integrable

/-!
### Automatic integrability for nonnegative derivatives
-/


/-- When the right derivative of a function is nonnegative, then it is automatically integrable. -/
theorem integrable_on_deriv_right_of_nonneg (hab : a ≤ b) (hcont : ContinuousOn g (Icc a b))
    (hderiv : ∀, ∀ x ∈ Ioo a b, ∀, HasDerivWithinAt g (g' x) (Ioi x) x) (g'pos : ∀, ∀ x ∈ Ioo a b, ∀, 0 ≤ g' x) :
    IntegrableOn g' (Ioc a b) := by
  rw [integrable_on_Ioc_iff_integrable_on_Ioo]
  have meas_g' : AeMeasurable g' (volume.restrict (Ioo a b)) := by
    apply (ae_measurable_deriv_within_Ioi g _).congr
    refine' (ae_restrict_mem measurable_set_Ioo).mono fun x hx => _
    exact (hderiv x hx).derivWithin (unique_diff_within_at_Ioi _)
  suffices H : (∫⁻ x in Ioo a b, ∥g' x∥₊) ≤ Ennreal.ofReal (g b - g a)
  exact ⟨meas_g'.ae_strongly_measurable, H.trans_lt Ennreal.of_real_lt_top⟩
  by_contra' H
  obtain ⟨f, fle, fint, hf⟩ :
    ∃ f : simple_func ℝ ℝ≥0 ,
      (∀ x, f x ≤ ∥g' x∥₊) ∧ (∫⁻ x : ℝ in Ioo a b, f x) < ∞ ∧ Ennreal.ofReal (g b - g a) < ∫⁻ x : ℝ in Ioo a b, f x :=
    exists_lt_lintegral_simple_func_of_lt_lintegral H
  let F : ℝ → ℝ := coe ∘ f
  have intF : integrable_on F (Ioo a b) := by
    refine' ⟨f.measurable.coe_nnreal_real.ae_strongly_measurable, _⟩
    simpa only [← has_finite_integral, ← Nnreal.nnnorm_eq] using fint
  have A : (∫⁻ x : ℝ in Ioo a b, f x) = Ennreal.ofReal (∫ x in Ioo a b, F x) := lintegral_coe_eq_integral _ intF
  rw [A] at hf
  have B : (∫ x : ℝ in Ioo a b, F x) ≤ g b - g a := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hab]
    apply integral_le_sub_of_has_deriv_right_of_le hab hcont hderiv _ fun x hx => _
    · rwa [integrable_on_Icc_iff_integrable_on_Ioo]
      
    · convert Nnreal.coe_le_coe.2 (fle x)
      simp only [← Real.norm_of_nonneg (g'pos x hx), ← coe_nnnorm]
      
  exact lt_irreflₓ _ (hf.trans_le (Ennreal.of_real_le_of_real B))

/-- When the derivative of a function is nonnegative, then it is automatically integrable,
Ioc version. -/
theorem integrable_on_deriv_of_nonneg (hab : a ≤ b) (hcont : ContinuousOn g (Icc a b))
    (hderiv : ∀, ∀ x ∈ Ioo a b, ∀, HasDerivAt g (g' x) x) (g'pos : ∀, ∀ x ∈ Ioo a b, ∀, 0 ≤ g' x) :
    IntegrableOn g' (Ioc a b) :=
  integrable_on_deriv_right_of_nonneg hab hcont (fun x hx => (hderiv x hx).HasDerivWithinAt) g'pos

/-- When the derivative of a function is nonnegative, then it is automatically integrable,
interval version. -/
theorem interval_integrable_deriv_of_nonneg (hcont : ContinuousOn g (Interval a b))
    (hderiv : ∀, ∀ x ∈ Ioo (min a b) (max a b), ∀, HasDerivAt g (g' x) x)
    (hpos : ∀, ∀ x ∈ Ioo (min a b) (max a b), ∀, 0 ≤ g' x) : IntervalIntegrable g' volume a b := by
  cases' le_totalₓ a b with hab hab
  · simp only [← interval_of_le, ← min_eq_leftₓ, ← max_eq_rightₓ, ← hab, ← IntervalIntegrable, ← hab, ←
      Ioc_eq_empty_of_le, ← integrable_on_empty, ← and_trueₓ] at hcont hderiv hpos⊢
    exact integrable_on_deriv_of_nonneg hab hcont hderiv hpos
    
  · simp only [← interval_of_ge, ← min_eq_rightₓ, ← max_eq_leftₓ, ← hab, ← IntervalIntegrable, ← Ioc_eq_empty_of_le, ←
      integrable_on_empty, ← true_andₓ] at hcont hderiv hpos⊢
    exact integrable_on_deriv_of_nonneg hab hcont hderiv hpos
    

/-!
### Integration by parts
-/


theorem integral_deriv_mul_eq_sub {u v u' v' : ℝ → ℝ} (hu : ∀, ∀ x ∈ Interval a b, ∀, HasDerivAt u (u' x) x)
    (hv : ∀, ∀ x ∈ Interval a b, ∀, HasDerivAt v (v' x) x) (hu' : IntervalIntegrable u' volume a b)
    (hv' : IntervalIntegrable v' volume a b) : (∫ x in a..b, u' x * v x + u x * v' x) = u b * v b - u a * v a :=
  (integral_eq_sub_of_has_deriv_at fun x hx => (hu x hx).mul (hv x hx)) <|
    (hu'.mul_continuous_on (HasDerivAt.continuous_on hv)).add (hv'.continuous_on_mul (HasDerivAt.continuous_on hu))

theorem integral_mul_deriv_eq_deriv_mul {u v u' v' : ℝ → ℝ} (hu : ∀, ∀ x ∈ Interval a b, ∀, HasDerivAt u (u' x) x)
    (hv : ∀, ∀ x ∈ Interval a b, ∀, HasDerivAt v (v' x) x) (hu' : IntervalIntegrable u' volume a b)
    (hv' : IntervalIntegrable v' volume a b) :
    (∫ x in a..b, u x * v' x) = u b * v b - u a * v a - ∫ x in a..b, v x * u' x := by
  rw [← integral_deriv_mul_eq_sub hu hv hu' hv', ← integral_sub]
  · exact
      integral_congr fun x hx => by
        simp only [← mul_comm, ← add_sub_cancel']
    
  · exact
      (hu'.mul_continuous_on (HasDerivAt.continuous_on hv)).add (hv'.continuous_on_mul (HasDerivAt.continuous_on hu))
    
  · exact hu'.continuous_on_mul (HasDerivAt.continuous_on hv)
    

/-!
### Integration by substitution / Change of variables
-/


section Smul

-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
/-- Change of variables, general form. If `f` is continuous on `[a, b]` and has
continuous right-derivative `f'` in `(a, b)`, and `g` is continuous on `f '' [a, b]` then we can
substitute `u = f x` to get `∫ x in a..b, f' x • (g ∘ f) x = ∫ u in f a..f b, g u`.

We could potentially slightly weaken the conditions, by not requiring that `f'` and `g` are
continuous on the endpoints of these intervals, but in that case we need to additionally assume that
the functions are integrable on that interval.
-/
theorem integral_comp_smul_deriv'' {f f' : ℝ → ℝ} {g : ℝ → E}
    (hf : ContinuousOn f "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)")
    (hff' : ∀, ∀ x ∈ Ioo (min a b) (max a b), ∀, HasDerivWithinAt f (f' x) (Ioi x) x)
    (hf' : ContinuousOn f' "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)")
    (hg : ContinuousOn g (f '' "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)")) :
    (∫ x in a..b, f' x • (g ∘ f) x) = ∫ u in f a..f b, g u := by
  have h_cont :
    ContinuousOn (fun u => ∫ t in f a..f u, g t)
      "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)" :=
    by
    rw [hf.image_interval] at hg
    refine' (continuous_on_primitive_interval' hg.interval_integrable _).comp hf _
    · rw [← hf.image_interval]
      exact mem_image_of_mem f left_mem_interval
      
    · rw [← hf.image_interval]
      exact maps_to_image _ _
      
  have h_der :
    ∀,
      ∀ x ∈ Ioo (min a b) (max a b), ∀, HasDerivWithinAt (fun u => ∫ t in f a..f u, g t) (f' x • (g ∘ f) x) (Ioi x) x :=
    by
    intro x hx
    let I := "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)"
    have hI : f '' "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)" = I :=
      hf.image_interval
    have h2x : f x ∈ I := by
      rw [← hI]
      exact mem_image_of_mem f (Ioo_subset_Icc_self hx)
    have h2g : IntervalIntegrable g volume (f a) (f x) := by
      refine' (hg.mono <| _).IntervalIntegrable
      exact hf.surj_on_interval left_mem_interval (Ioo_subset_Icc_self hx)
    rw [hI] at hg
    have h3g : StronglyMeasurableAtFilter g (𝓝[I] f x) volume :=
      hg.strongly_measurable_at_filter_nhds_within measurable_set_Icc (f x)
    have : Fact (f x ∈ I) := ⟨h2x⟩
    have : HasDerivWithinAt (fun u => ∫ x in f a..u, g x) (g (f x)) I (f x) :=
      integral_has_deriv_within_at_right h2g h3g (hg (f x) h2x)
    refine' (this.scomp x ((hff' x hx).Ioo_of_Ioi hx.2) _).Ioi_of_Ioo hx.2
    rw [← hI]
    exact (maps_to_image _ _).mono (Ioo_subset_Icc_self.trans <| Icc_subset_Icc_left hx.1.le) subset.rfl
  have h_int : IntervalIntegrable (fun x : ℝ => f' x • (g ∘ f) x) volume a b :=
    (hf'.smul (hg.comp hf <| subset_preimage_image f _)).IntervalIntegrable
  simp_rw [integral_eq_sub_of_has_deriv_right h_cont h_der h_int, integral_same, sub_zero]

-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
/-- Change of variables. If `f` is has continuous derivative `f'` on `[a, b]`,
and `g` is continuous on `f '' [a, b]`, then we can substitute `u = f x` to get
`∫ x in a..b, f' x • (g ∘ f) x = ∫ u in f a..f b, g u`.
Compared to `interval_integral.integral_comp_smul_deriv` we only require that `g` is continuous on
`f '' [a, b]`.
-/
theorem integral_comp_smul_deriv' {f f' : ℝ → ℝ} {g : ℝ → E} (h : ∀, ∀ x ∈ Interval a b, ∀, HasDerivAt f (f' x) x)
    (h' : ContinuousOn f' (Interval a b))
    (hg : ContinuousOn g (f '' "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)")) :
    (∫ x in a..b, f' x • (g ∘ f) x) = ∫ x in f a..f b, g x :=
  integral_comp_smul_deriv'' (fun x hx => (h x hx).ContinuousAt.ContinuousWithinAt)
    (fun x hx => (h x <| Ioo_subset_Icc_self hx).HasDerivWithinAt) h' hg

/-- Change of variables, most common version. If `f` is has continuous derivative `f'` on `[a, b]`,
and `g` is continuous, then we can substitute `u = f x` to get
`∫ x in a..b, f' x • (g ∘ f) x = ∫ u in f a..f b, g u`.
-/
theorem integral_comp_smul_deriv {f f' : ℝ → ℝ} {g : ℝ → E} (h : ∀, ∀ x ∈ Interval a b, ∀, HasDerivAt f (f' x) x)
    (h' : ContinuousOn f' (Interval a b)) (hg : Continuous g) :
    (∫ x in a..b, f' x • (g ∘ f) x) = ∫ x in f a..f b, g x :=
  integral_comp_smul_deriv' h h' hg.ContinuousOn

-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
theorem integral_deriv_comp_smul_deriv' {f f' : ℝ → ℝ} {g g' : ℝ → E}
    (hf : ContinuousOn f "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)")
    (hff' : ∀, ∀ x ∈ Ioo (min a b) (max a b), ∀, HasDerivWithinAt f (f' x) (Ioi x) x)
    (hf' : ContinuousOn f' "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)")
    (hg : ContinuousOn g "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)")
    (hgg' : ∀, ∀ x ∈ Ioo (min (f a) (f b)) (max (f a) (f b)), ∀, HasDerivWithinAt g (g' x) (Ioi x) x)
    (hg' : ContinuousOn g' (f '' "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)")) :
    (∫ x in a..b, f' x • (g' ∘ f) x) = (g ∘ f) b - (g ∘ f) a := by
  rw [integral_comp_smul_deriv'' hf hff' hf' hg',
    integral_eq_sub_of_has_deriv_right hg hgg' (hg'.mono _).IntervalIntegrable]
  exact intermediate_value_interval hf

theorem integral_deriv_comp_smul_deriv {f f' : ℝ → ℝ} {g g' : ℝ → E}
    (hf : ∀, ∀ x ∈ Interval a b, ∀, HasDerivAt f (f' x) x)
    (hg : ∀, ∀ x ∈ Interval a b, ∀, HasDerivAt g (g' (f x)) (f x)) (hf' : ContinuousOn f' (Interval a b))
    (hg' : Continuous g') : (∫ x in a..b, f' x • (g' ∘ f) x) = (g ∘ f) b - (g ∘ f) a :=
  integral_eq_sub_of_has_deriv_at (fun x hx => (hg x hx).scomp x <| hf x hx)
    (hf'.smul (hg'.comp_continuous_on <| HasDerivAt.continuous_on hf)).IntervalIntegrable

end Smul

section Mul

-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
/-- Change of variables, general form for scalar functions. If `f` is continuous on `[a, b]` and has
continuous right-derivative `f'` in `(a, b)`, and `g` is continuous on `f '' [a, b]` then we can
substitute `u = f x` to get `∫ x in a..b, (g ∘ f) x * f' x = ∫ u in f a..f b, g u`.
-/
theorem integral_comp_mul_deriv'' {f f' g : ℝ → ℝ}
    (hf : ContinuousOn f "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)")
    (hff' : ∀, ∀ x ∈ Ioo (min a b) (max a b), ∀, HasDerivWithinAt f (f' x) (Ioi x) x)
    (hf' : ContinuousOn f' "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)")
    (hg : ContinuousOn g (f '' "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)")) :
    (∫ x in a..b, (g ∘ f) x * f' x) = ∫ u in f a..f b, g u := by
  simpa [← mul_comm] using integral_comp_smul_deriv'' hf hff' hf' hg

-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
/-- Change of variables. If `f` is has continuous derivative `f'` on `[a, b]`,
and `g` is continuous on `f '' [a, b]`, then we can substitute `u = f x` to get
`∫ x in a..b, (g ∘ f) x * f' x = ∫ u in f a..f b, g u`.
Compared to `interval_integral.integral_comp_mul_deriv` we only require that `g` is continuous on
`f '' [a, b]`.
-/
theorem integral_comp_mul_deriv' {f f' g : ℝ → ℝ} (h : ∀, ∀ x ∈ Interval a b, ∀, HasDerivAt f (f' x) x)
    (h' : ContinuousOn f' (Interval a b))
    (hg : ContinuousOn g (f '' "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)")) :
    (∫ x in a..b, (g ∘ f) x * f' x) = ∫ x in f a..f b, g x := by
  simpa [← mul_comm] using integral_comp_smul_deriv' h h' hg

/-- Change of variables, most common version. If `f` is has continuous derivative `f'` on `[a, b]`,
and `g` is continuous, then we can substitute `u = f x` to get
`∫ x in a..b, (g ∘ f) x * f' x = ∫ u in f a..f b, g u`.
-/
theorem integral_comp_mul_deriv {f f' g : ℝ → ℝ} (h : ∀, ∀ x ∈ Interval a b, ∀, HasDerivAt f (f' x) x)
    (h' : ContinuousOn f' (Interval a b)) (hg : Continuous g) :
    (∫ x in a..b, (g ∘ f) x * f' x) = ∫ x in f a..f b, g x :=
  integral_comp_mul_deriv' h h' hg.ContinuousOn

-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
-- ./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)
theorem integral_deriv_comp_mul_deriv' {f f' g g' : ℝ → ℝ}
    (hf : ContinuousOn f "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)")
    (hff' : ∀, ∀ x ∈ Ioo (min a b) (max a b), ∀, HasDerivWithinAt f (f' x) (Ioi x) x)
    (hf' : ContinuousOn f' "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)")
    (hg : ContinuousOn g "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)")
    (hgg' : ∀, ∀ x ∈ Ioo (min (f a) (f b)) (max (f a) (f b)), ∀, HasDerivWithinAt g (g' x) (Ioi x) x)
    (hg' : ContinuousOn g' (f '' "./././Mathport/Syntax/Translate/Basic.lean:958:47: unsupported (impossible)")) :
    (∫ x in a..b, (g' ∘ f) x * f' x) = (g ∘ f) b - (g ∘ f) a := by
  simpa [← mul_comm] using integral_deriv_comp_smul_deriv' hf hff' hf' hg hgg' hg'

theorem integral_deriv_comp_mul_deriv {f f' g g' : ℝ → ℝ} (hf : ∀, ∀ x ∈ Interval a b, ∀, HasDerivAt f (f' x) x)
    (hg : ∀, ∀ x ∈ Interval a b, ∀, HasDerivAt g (g' (f x)) (f x)) (hf' : ContinuousOn f' (Interval a b))
    (hg' : Continuous g') : (∫ x in a..b, (g' ∘ f) x * f' x) = (g ∘ f) b - (g ∘ f) a := by
  simpa [← mul_comm] using integral_deriv_comp_smul_deriv hf hg hf' hg'

end Mul

end intervalIntegral

