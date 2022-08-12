/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathbin.Analysis.Calculus.MeanValue
import Mathbin.Analysis.NormedSpace.Multilinear
import Mathbin.Analysis.Calculus.FormalMultilinearSeries
import Mathbin.Tactic.Congrm

/-!
# Higher differentiability

A function is `C^1` on a domain if it is differentiable there, and its derivative is continuous.
By induction, it is `C^n` if it is `C^{n-1}` and its (n-1)-th derivative is `C^1` there or,
equivalently, if it is `C^1` and its derivative is `C^{n-1}`.
Finally, it is `C^∞` if it is `C^n` for all n.

We formalize these notions by defining iteratively the `n+1`-th derivative of a function as the
derivative of the `n`-th derivative. It is called `iterated_fderiv 𝕜 n f x` where `𝕜` is the
field, `n` is the number of iterations, `f` is the function and `x` is the point, and it is given
as an `n`-multilinear map. We also define a version `iterated_fderiv_within` relative to a domain,
as well as predicates `cont_diff_within_at`, `cont_diff_at`, `cont_diff_on` and
`cont_diff` saying that the function is `C^n` within a set at a point, at a point, on a set
and on the whole space respectively.

To avoid the issue of choice when choosing a derivative in sets where the derivative is not
necessarily unique, `cont_diff_on` is not defined directly in terms of the
regularity of the specific choice `iterated_fderiv_within 𝕜 n f s` inside `s`, but in terms of the
existence of a nice sequence of derivatives, expressed with a predicate
`has_ftaylor_series_up_to_on`.

We prove basic properties of these notions.

## Main definitions and results
Let `f : E → F` be a map between normed vector spaces over a nondiscrete normed field `𝕜`.

* `has_ftaylor_series_up_to n f p`: expresses that the formal multilinear series `p` is a sequence
  of iterated derivatives of `f`, up to the `n`-th term (where `n` is a natural number or `∞`).
* `has_ftaylor_series_up_to_on n f p s`: same thing, but inside a set `s`. The notion of derivative
  is now taken inside `s`. In particular, derivatives don't have to be unique.
* `cont_diff 𝕜 n f`: expresses that `f` is `C^n`, i.e., it admits a Taylor series up to
  rank `n`.
* `cont_diff_on 𝕜 n f s`: expresses that `f` is `C^n` in `s`.
* `cont_diff_at 𝕜 n f x`: expresses that `f` is `C^n` around `x`.
* `cont_diff_within_at 𝕜 n f s x`: expresses that `f` is `C^n` around `x` within the set `s`.
* `iterated_fderiv_within 𝕜 n f s x` is an `n`-th derivative of `f` over the field `𝕜` on the
  set `s` at the point `x`. It is a continuous multilinear map from `E^n` to `F`, defined as a
  derivative within `s` of `iterated_fderiv_within 𝕜 (n-1) f s` if one exists, and `0` otherwise.
* `iterated_fderiv 𝕜 n f x` is the `n`-th derivative of `f` over the field `𝕜` at the point `x`.
  It is a continuous multilinear map from `E^n` to `F`, defined as a derivative of
  `iterated_fderiv 𝕜 (n-1) f` if one exists, and `0` otherwise.

In sets of unique differentiability, `cont_diff_on 𝕜 n f s` can be expressed in terms of the
properties of `iterated_fderiv_within 𝕜 m f s` for `m ≤ n`. In the whole space,
`cont_diff 𝕜 n f` can be expressed in terms of the properties of `iterated_fderiv 𝕜 m f`
for `m ≤ n`.

We also prove that the usual operations (addition, multiplication, difference, composition, and
so on) preserve `C^n` functions.

## Implementation notes

The definitions in this file are designed to work on any field `𝕜`. They are sometimes slightly more
complicated than the naive definitions one would guess from the intuition over the real or complex
numbers, but they are designed to circumvent the lack of gluing properties and partitions of unity
in general. In the usual situations, they coincide with the usual definitions.

### Definition of `C^n` functions in domains

One could define `C^n` functions in a domain `s` by fixing an arbitrary choice of derivatives (this
is what we do with `iterated_fderiv_within`) and requiring that all these derivatives up to `n` are
continuous. If the derivative is not unique, this could lead to strange behavior like two `C^n`
functions `f` and `g` on `s` whose sum is not `C^n`. A better definition is thus to say that a
function is `C^n` inside `s` if it admits a sequence of derivatives up to `n` inside `s`.

This definition still has the problem that a function which is locally `C^n` would not need to
be `C^n`, as different choices of sequences of derivatives around different points might possibly
not be glued together to give a globally defined sequence of derivatives. (Note that this issue
can not happen over reals, thanks to partition of unity, but the behavior over a general field is
not so clear, and we want a definition for general fields). Also, there are locality
problems for the order parameter: one could image a function which, for each `n`, has a nice
sequence of derivatives up to order `n`, but they do not coincide for varying `n` and can therefore
not be glued to give rise to an infinite sequence of derivatives. This would give a function
which is `C^n` for all `n`, but not `C^∞`. We solve this issue by putting locality conditions
in space and order in our definition of `cont_diff_within_at` and `cont_diff_on`.
The resulting definition is slightly more complicated to work with (in fact not so much), but it
gives rise to completely satisfactory theorems.

For instance, with this definition, a real function which is `C^m` (but not better) on `(-1/m, 1/m)`
for each natural `m` is by definition `C^∞` at `0`.

There is another issue with the definition of `cont_diff_within_at 𝕜 n f s x`. We can
require the existence and good behavior of derivatives up to order `n` on a neighborhood of `x`
within `s`. However, this does not imply continuity or differentiability within `s` of the function
at `x` when `x` does not belong to `s`. Therefore, we require such existence and good behavior on
a neighborhood of `x` within `s ∪ {x}` (which appears as `insert x s` in this file).

### Side of the composition, and universe issues

With a naïve direct definition, the `n`-th derivative of a function belongs to the space
`E →L[𝕜] (E →L[𝕜] (E ... F)...)))` where there are n iterations of `E →L[𝕜]`. This space
may also be seen as the space of continuous multilinear functions on `n` copies of `E` with
values in `F`, by uncurrying. This is the point of view that is usually adopted in textbooks,
and that we also use. This means that the definition and the first proofs are slightly involved,
as one has to keep track of the uncurrying operation. The uncurrying can be done from the
left or from the right, amounting to defining the `n+1`-th derivative either as the derivative of
the `n`-th derivative, or as the `n`-th derivative of the derivative.
For proofs, it would be more convenient to use the latter approach (from the right),
as it means to prove things at the `n+1`-th step we only need to understand well enough the
derivative in `E →L[𝕜] F` (contrary to the approach from the left, where one would need to know
enough on the `n`-th derivative to deduce things on the `n+1`-th derivative).

However, the definition from the right leads to a universe polymorphism problem: if we define
`iterated_fderiv 𝕜 (n + 1) f x = iterated_fderiv 𝕜 n (fderiv 𝕜 f) x` by induction, we need to
generalize over all spaces (as `f` and `fderiv 𝕜 f` don't take values in the same space). It is
only possible to generalize over all spaces in some fixed universe in an inductive definition.
For `f : E → F`, then `fderiv 𝕜 f` is a map `E → (E →L[𝕜] F)`. Therefore, the definition will only
work if `F` and `E →L[𝕜] F` are in the same universe.

This issue does not appear with the definition from the left, where one does not need to generalize
over all spaces. Therefore, we use the definition from the left. This means some proofs later on
become a little bit more complicated: to prove that a function is `C^n`, the most efficient approach
is to exhibit a formula for its `n`-th derivative and prove it is continuous (contrary to the
inductive approach where one would prove smoothness statements without giving a formula for the
derivative). In the end, this approach is still satisfactory as it is good to have formulas for the
iterated derivatives in various constructions.

One point where we depart from this explicit approach is in the proof of smoothness of a
composition: there is a formula for the `n`-th derivative of a composition (Faà di Bruno's formula),
but it is very complicated and barely usable, while the inductive proof is very simple. Thus, we
give the inductive proof. As explained above, it works by generalizing over the target space, hence
it only works well if all spaces belong to the same universe. To get the general version, we lift
things to a common universe using a trick.

### Variables management

The textbook definitions and proofs use various identifications and abuse of notations, for instance
when saying that the natural space in which the derivative lives, i.e.,
`E →L[𝕜] (E →L[𝕜] ( ... →L[𝕜] F))`, is the same as a space of multilinear maps. When doing things
formally, we need to provide explicit maps for these identifications, and chase some diagrams to see
everything is compatible with the identifications. In particular, one needs to check that taking the
derivative and then doing the identification, or first doing the identification and then taking the
derivative, gives the same result. The key point for this is that taking the derivative commutes
with continuous linear equivalences. Therefore, we need to implement all our identifications with
continuous linear equivs.

## Notations

We use the notation `E [×n]→L[𝕜] F` for the space of continuous multilinear maps on `E^n` with
values in `F`. This is the space in which the `n`-th derivative of a function from `E` to `F` lives.

In this file, we denote `⊤ : with_top ℕ` with `∞`.

## Tags

derivative, differentiability, higher derivative, `C^n`, multilinear, Taylor series, formal series
-/


noncomputable section

open Classical BigOperators Nnreal

-- mathport name: «expr∞»
local notation "∞" => (⊤ : WithTop ℕ)

universe u v w

attribute [local instance] NormedGroup.toAddCommGroup NormedSpace.toModule' AddCommGroupₓ.toAddCommMonoid

open Set Finₓ Filter

open TopologicalSpace

variable {𝕜 : Type _} [NondiscreteNormedField 𝕜] {E : Type _} [NormedGroup E] [NormedSpace 𝕜 E] {F : Type _}
  [NormedGroup F] [NormedSpace 𝕜 F] {G : Type _} [NormedGroup G] [NormedSpace 𝕜 G] {X : Type _} [NormedGroup X]
  [NormedSpace 𝕜 X] {s s₁ t u : Set E} {f f₁ : E → F} {g : F → G} {x : E} {c : F} {b : E × F → G} {m n : WithTop ℕ}

/-! ### Functions with a Taylor series on a domain -/


variable {p : E → FormalMultilinearSeries 𝕜 E F}

/-- `has_ftaylor_series_up_to_on n f p s` registers the fact that `p 0 = f` and `p (m+1)` is a
derivative of `p m` for `m < n`, and is continuous for `m ≤ n`. This is a predicate analogous to
`has_fderiv_within_at` but for higher order derivatives. -/
structure HasFtaylorSeriesUpToOn (n : WithTop ℕ) (f : E → F) (p : E → FormalMultilinearSeries 𝕜 E F) (s : Set E) :
  Prop where
  zero_eq : ∀, ∀ x ∈ s, ∀, (p x 0).uncurry0 = f x
  fderivWithin :
    ∀ (m : ℕ) (hm : (m : WithTop ℕ) < n), ∀, ∀ x ∈ s, ∀, HasFderivWithinAt (fun y => p y m) (p x m.succ).curryLeft s x
  cont : ∀ (m : ℕ) (hm : (m : WithTop ℕ) ≤ n), ContinuousOn (fun x => p x m) s

theorem HasFtaylorSeriesUpToOn.zero_eq' (h : HasFtaylorSeriesUpToOn n f p s) {x : E} (hx : x ∈ s) :
    p x 0 = (continuousMultilinearCurryFin0 𝕜 E F).symm (f x) := by
  rw [← h.zero_eq x hx]
  symm
  exact ContinuousMultilinearMap.uncurry0_curry0 _

/-- If two functions coincide on a set `s`, then a Taylor series for the first one is as well a
Taylor series for the second one. -/
theorem HasFtaylorSeriesUpToOn.congr (h : HasFtaylorSeriesUpToOn n f p s) (h₁ : ∀, ∀ x ∈ s, ∀, f₁ x = f x) :
    HasFtaylorSeriesUpToOn n f₁ p s := by
  refine' ⟨fun x hx => _, h.fderiv_within, h.cont⟩
  rw [h₁ x hx]
  exact h.zero_eq x hx

theorem HasFtaylorSeriesUpToOn.mono (h : HasFtaylorSeriesUpToOn n f p s) {t : Set E} (hst : t ⊆ s) :
    HasFtaylorSeriesUpToOn n f p t :=
  ⟨fun x hx => h.zero_eq x (hst hx), fun m hm x hx => (h.fderivWithin m hm x (hst hx)).mono hst, fun m hm =>
    (h.cont m hm).mono hst⟩

theorem HasFtaylorSeriesUpToOn.of_le (h : HasFtaylorSeriesUpToOn n f p s) (hmn : m ≤ n) :
    HasFtaylorSeriesUpToOn m f p s :=
  ⟨h.zero_eq, fun k hk x hx => h.fderivWithin k (lt_of_lt_of_leₓ hk hmn) x hx, fun k hk => h.cont k (le_transₓ hk hmn)⟩

theorem HasFtaylorSeriesUpToOn.continuous_on (h : HasFtaylorSeriesUpToOn n f p s) : ContinuousOn f s := by
  have := (h.cont 0 bot_le).congr fun x hx => (h.zero_eq' hx).symm
  rwa [LinearIsometryEquiv.comp_continuous_on_iff] at this

theorem has_ftaylor_series_up_to_on_zero_iff :
    HasFtaylorSeriesUpToOn 0 f p s ↔ ContinuousOn f s ∧ ∀, ∀ x ∈ s, ∀, (p x 0).uncurry0 = f x := by
  refine' ⟨fun H => ⟨H.ContinuousOn, H.zero_eq⟩, fun H => ⟨H.2, fun m hm => False.elim (not_leₓ.2 hm bot_le), _⟩⟩
  intro m hm
  obtain rfl : m = 0 := by
    exact_mod_cast hm.antisymm (zero_le _)
  have : ∀, ∀ x ∈ s, ∀, p x 0 = (continuousMultilinearCurryFin0 𝕜 E F).symm (f x) := by
    intro x hx
    rw [← H.2 x hx]
    symm
    exact ContinuousMultilinearMap.uncurry0_curry0 _
  rw [continuous_on_congr this, LinearIsometryEquiv.comp_continuous_on_iff]
  exact H.1

theorem has_ftaylor_series_up_to_on_top_iff :
    HasFtaylorSeriesUpToOn ∞ f p s ↔ ∀ n : ℕ, HasFtaylorSeriesUpToOn n f p s := by
  constructor
  · intro H n
    exact H.of_le le_top
    
  · intro H
    constructor
    · exact (H 0).zero_eq
      
    · intro m hm
      apply (H m.succ).fderivWithin m (WithTop.coe_lt_coe.2 (lt_add_one m))
      
    · intro m hm
      apply (H m).cont m le_rfl
      
    

/-- If a function has a Taylor series at order at least `1`, then the term of order `1` of this
series is a derivative of `f`. -/
theorem HasFtaylorSeriesUpToOn.has_fderiv_within_at (h : HasFtaylorSeriesUpToOn n f p s) (hn : 1 ≤ n) (hx : x ∈ s) :
    HasFderivWithinAt f (continuousMultilinearCurryFin1 𝕜 E F (p x 1)) s x := by
  have A : ∀, ∀ y ∈ s, ∀, f y = (continuousMultilinearCurryFin0 𝕜 E F) (p y 0) := by
    intro y hy
    rw [← h.zero_eq y hy]
    rfl
  suffices H :
    HasFderivWithinAt (fun y => continuousMultilinearCurryFin0 𝕜 E F (p y 0))
      (continuousMultilinearCurryFin1 𝕜 E F (p x 1)) s x
  · exact H.congr A (A x hx)
    
  rw [LinearIsometryEquiv.comp_has_fderiv_within_at_iff']
  have : ((0 : ℕ) : WithTop ℕ) < n := lt_of_lt_of_leₓ (WithTop.coe_lt_coe.2 Nat.zero_lt_oneₓ) hn
  convert h.fderiv_within _ this x hx
  ext y v
  change (p x 1) (snoc 0 y) = (p x 1) (cons y v)
  unfold_coes
  congr with i
  rw [Unique.eq_default i]
  rfl

theorem HasFtaylorSeriesUpToOn.differentiable_on (h : HasFtaylorSeriesUpToOn n f p s) (hn : 1 ≤ n) :
    DifferentiableOn 𝕜 f s := fun x hx => (h.HasFderivWithinAt hn hx).DifferentiableWithinAt

/-- If a function has a Taylor series at order at least `1` on a neighborhood of `x`, then the term
of order `1` of this series is a derivative of `f` at `x`. -/
theorem HasFtaylorSeriesUpToOn.has_fderiv_at (h : HasFtaylorSeriesUpToOn n f p s) (hn : 1 ≤ n) (hx : s ∈ 𝓝 x) :
    HasFderivAt f (continuousMultilinearCurryFin1 𝕜 E F (p x 1)) x :=
  (h.HasFderivWithinAt hn (mem_of_mem_nhds hx)).HasFderivAt hx

/-- If a function has a Taylor series at order at least `1` on a neighborhood of `x`, then
in a neighborhood of `x`, the term of order `1` of this series is a derivative of `f`. -/
theorem HasFtaylorSeriesUpToOn.eventually_has_fderiv_at (h : HasFtaylorSeriesUpToOn n f p s) (hn : 1 ≤ n)
    (hx : s ∈ 𝓝 x) : ∀ᶠ y in 𝓝 x, HasFderivAt f (continuousMultilinearCurryFin1 𝕜 E F (p y 1)) y :=
  (eventually_eventually_nhds.2 hx).mono fun y hy => h.HasFderivAt hn hy

/-- If a function has a Taylor series at order at least `1` on a neighborhood of `x`, then
it is differentiable at `x`. -/
theorem HasFtaylorSeriesUpToOn.differentiable_at (h : HasFtaylorSeriesUpToOn n f p s) (hn : 1 ≤ n) (hx : s ∈ 𝓝 x) :
    DifferentiableAt 𝕜 f x :=
  (h.HasFderivAt hn hx).DifferentiableAt

/-- `p` is a Taylor series of `f` up to `n+1` if and only if `p` is a Taylor series up to `n`, and
`p (n + 1)` is a derivative of `p n`. -/
theorem has_ftaylor_series_up_to_on_succ_iff_left {n : ℕ} :
    HasFtaylorSeriesUpToOn (n + 1) f p s ↔
      HasFtaylorSeriesUpToOn n f p s ∧
        (∀, ∀ x ∈ s, ∀, HasFderivWithinAt (fun y => p y n) (p x n.succ).curryLeft s x) ∧
          ContinuousOn (fun x => p x (n + 1)) s :=
  by
  constructor
  · intro h
    exact
      ⟨h.of_le (WithTop.coe_le_coe.2 (Nat.le_succₓ n)), h.fderiv_within _ (WithTop.coe_lt_coe.2 (lt_add_one n)),
        h.cont (n + 1) le_rfl⟩
    
  · intro h
    constructor
    · exact h.1.zero_eq
      
    · intro m hm
      by_cases' h' : m < n
      · exact h.1.fderivWithin m (WithTop.coe_lt_coe.2 h')
        
      · have : m = n := Nat.eq_of_lt_succ_of_not_lt (WithTop.coe_lt_coe.1 hm) h'
        rw [this]
        exact h.2.1
        
      
    · intro m hm
      by_cases' h' : m ≤ n
      · apply h.1.cont m (WithTop.coe_le_coe.2 h')
        
      · have : m = n + 1 := le_antisymmₓ (WithTop.coe_le_coe.1 hm) (not_leₓ.1 h')
        rw [this]
        exact h.2.2
        
      
    

/-- `p` is a Taylor series of `f` up to `n+1` if and only if `p.shift` is a Taylor series up to `n`
for `p 1`, which is a derivative of `f`. -/
theorem has_ftaylor_series_up_to_on_succ_iff_right {n : ℕ} :
    HasFtaylorSeriesUpToOn (n + 1 : ℕ) f p s ↔
      (∀, ∀ x ∈ s, ∀, (p x 0).uncurry0 = f x) ∧
        (∀, ∀ x ∈ s, ∀, HasFderivWithinAt (fun y => p y 0) (p x 1).curryLeft s x) ∧
          HasFtaylorSeriesUpToOn n (fun x => continuousMultilinearCurryFin1 𝕜 E F (p x 1)) (fun x => (p x).shift) s :=
  by
  constructor
  · intro H
    refine' ⟨H.zero_eq, H.fderiv_within 0 (WithTop.coe_lt_coe.2 (Nat.succ_posₓ n)), _⟩
    constructor
    · intro x hx
      rfl
      
    · intro m(hm : (m : WithTop ℕ) < n)x(hx : x ∈ s)
      have A : (m.succ : WithTop ℕ) < n.succ := by
        rw [WithTop.coe_lt_coe] at hm⊢
        exact nat.lt_succ_iff.mpr hm
      change
        HasFderivWithinAt ((continuousMultilinearCurryRightEquiv' 𝕜 m E F).symm ∘ fun y : E => p y m.succ)
          (p x m.succ.succ).curryRight.curryLeft s x
      rw [LinearIsometryEquiv.comp_has_fderiv_within_at_iff']
      convert H.fderiv_within _ A x hx
      ext y v
      change (p x m.succ.succ) (snoc (cons y (init v)) (v (last _))) = (p x (Nat.succ (Nat.succ m))) (cons y v)
      rw [← cons_snoc_eq_snoc_cons, snoc_init_self]
      
    · intro m(hm : (m : WithTop ℕ) ≤ n)
      have A : (m.succ : WithTop ℕ) ≤ n.succ := by
        rw [WithTop.coe_le_coe] at hm⊢
        exact nat.pred_le_iff.mp hm
      change ContinuousOn ((continuousMultilinearCurryRightEquiv' 𝕜 m E F).symm ∘ fun y : E => p y m.succ) s
      rw [LinearIsometryEquiv.comp_continuous_on_iff]
      exact H.cont _ A
      
    
  · rintro ⟨Hzero_eq, Hfderiv_zero, Htaylor⟩
    constructor
    · exact Hzero_eq
      
    · intro m(hm : (m : WithTop ℕ) < n.succ)x(hx : x ∈ s)
      cases m
      · exact Hfderiv_zero x hx
        
      · have A : (m : WithTop ℕ) < n := by
          rw [WithTop.coe_lt_coe] at hm⊢
          exact Nat.lt_of_succ_lt_succₓ hm
        have :
          HasFderivWithinAt ((continuousMultilinearCurryRightEquiv' 𝕜 m E F).symm ∘ fun y : E => p y m.succ)
            ((p x).shift m.succ).curryLeft s x :=
          Htaylor.fderiv_within _ A x hx
        rw [LinearIsometryEquiv.comp_has_fderiv_within_at_iff'] at this
        convert this
        ext y v
        change (p x (Nat.succ (Nat.succ m))) (cons y v) = (p x m.succ.succ) (snoc (cons y (init v)) (v (last _)))
        rw [← cons_snoc_eq_snoc_cons, snoc_init_self]
        
      
    · intro m(hm : (m : WithTop ℕ) ≤ n.succ)
      cases m
      · have : DifferentiableOn 𝕜 (fun x => p x 0) s := fun x hx => (Hfderiv_zero x hx).DifferentiableWithinAt
        exact this.continuous_on
        
      · have A : (m : WithTop ℕ) ≤ n := by
          rw [WithTop.coe_le_coe] at hm⊢
          exact nat.lt_succ_iff.mp hm
        have : ContinuousOn ((continuousMultilinearCurryRightEquiv' 𝕜 m E F).symm ∘ fun y : E => p y m.succ) s :=
          Htaylor.cont _ A
        rwa [LinearIsometryEquiv.comp_continuous_on_iff] at this
        
      
    

/-! ### Smooth functions within a set around a point -/


variable (𝕜)

/-- A function is continuously differentiable up to order `n` within a set `s` at a point `x` if
it admits continuous derivatives up to order `n` in a neighborhood of `x` in `s ∪ {x}`.
For `n = ∞`, we only require that this holds up to any finite order (where the neighborhood may
depend on the finite order we consider).

For instance, a real function which is `C^m` on `(-1/m, 1/m)` for each natural `m`, but not
better, is `C^∞` at `0` within `univ`.
-/
def ContDiffWithinAt (n : WithTop ℕ) (f : E → F) (s : Set E) (x : E) :=
  ∀ m : ℕ,
    (m : WithTop ℕ) ≤ n → ∃ u ∈ 𝓝[insert x s] x, ∃ p : E → FormalMultilinearSeries 𝕜 E F, HasFtaylorSeriesUpToOn m f p u

variable {𝕜}

theorem cont_diff_within_at_nat {n : ℕ} :
    ContDiffWithinAt 𝕜 n f s x ↔
      ∃ u ∈ 𝓝[insert x s] x, ∃ p : E → FormalMultilinearSeries 𝕜 E F, HasFtaylorSeriesUpToOn n f p u :=
  ⟨fun H => H n le_rfl, fun ⟨u, hu, p, hp⟩ m hm => ⟨u, hu, p, hp.of_le hm⟩⟩

theorem ContDiffWithinAt.of_le (h : ContDiffWithinAt 𝕜 n f s x) (hmn : m ≤ n) : ContDiffWithinAt 𝕜 m f s x :=
  fun k hk => h k (le_transₓ hk hmn)

theorem cont_diff_within_at_iff_forall_nat_le :
    ContDiffWithinAt 𝕜 n f s x ↔ ∀ m : ℕ, ↑m ≤ n → ContDiffWithinAt 𝕜 m f s x :=
  ⟨fun H m hm => H.of_le hm, fun H m hm => H m hm _ le_rfl⟩

theorem cont_diff_within_at_top : ContDiffWithinAt 𝕜 ∞ f s x ↔ ∀ n : ℕ, ContDiffWithinAt 𝕜 n f s x :=
  cont_diff_within_at_iff_forall_nat_le.trans <| by
    simp only [← forall_prop_of_true, ← le_top]

theorem ContDiffWithinAt.continuous_within_at (h : ContDiffWithinAt 𝕜 n f s x) : ContinuousWithinAt f s x := by
  rcases h 0 bot_le with ⟨u, hu, p, H⟩
  rw [mem_nhds_within_insert] at hu
  exact (H.continuous_on.continuous_within_at hu.1).mono_of_mem hu.2

theorem ContDiffWithinAt.congr_of_eventually_eq (h : ContDiffWithinAt 𝕜 n f s x) (h₁ : f₁ =ᶠ[𝓝[s] x] f)
    (hx : f₁ x = f x) : ContDiffWithinAt 𝕜 n f₁ s x := fun m hm =>
  let ⟨u, hu, p, H⟩ := h m hm
  ⟨{ x ∈ u | f₁ x = f x }, Filter.inter_mem hu (mem_nhds_within_insert.2 ⟨hx, h₁⟩), p,
    (H.mono (sep_subset _ _)).congr fun _ => And.right⟩

theorem ContDiffWithinAt.congr_of_eventually_eq_insert (h : ContDiffWithinAt 𝕜 n f s x)
    (h₁ : f₁ =ᶠ[𝓝[insert x s] x] f) : ContDiffWithinAt 𝕜 n f₁ s x :=
  h.congr_of_eventually_eq (nhds_within_mono x (subset_insert x s) h₁) (mem_of_mem_nhds_within (mem_insert x s) h₁ : _)

theorem ContDiffWithinAt.congr_of_eventually_eq' (h : ContDiffWithinAt 𝕜 n f s x) (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : x ∈ s) :
    ContDiffWithinAt 𝕜 n f₁ s x :=
  h.congr_of_eventually_eq h₁ <| h₁.self_of_nhds_within hx

theorem Filter.EventuallyEq.cont_diff_within_at_iff (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) :
    ContDiffWithinAt 𝕜 n f₁ s x ↔ ContDiffWithinAt 𝕜 n f s x :=
  ⟨fun H => ContDiffWithinAt.congr_of_eventually_eq H h₁.symm hx.symm, fun H => H.congr_of_eventually_eq h₁ hx⟩

theorem ContDiffWithinAt.congr (h : ContDiffWithinAt 𝕜 n f s x) (h₁ : ∀, ∀ y ∈ s, ∀, f₁ y = f y) (hx : f₁ x = f x) :
    ContDiffWithinAt 𝕜 n f₁ s x :=
  h.congr_of_eventually_eq (Filter.eventually_eq_of_mem self_mem_nhds_within h₁) hx

theorem ContDiffWithinAt.congr' (h : ContDiffWithinAt 𝕜 n f s x) (h₁ : ∀, ∀ y ∈ s, ∀, f₁ y = f y) (hx : x ∈ s) :
    ContDiffWithinAt 𝕜 n f₁ s x :=
  h.congr h₁ (h₁ _ hx)

theorem ContDiffWithinAt.mono_of_mem (h : ContDiffWithinAt 𝕜 n f s x) {t : Set E} (hst : s ∈ 𝓝[t] x) :
    ContDiffWithinAt 𝕜 n f t x := by
  intro m hm
  rcases h m hm with ⟨u, hu, p, H⟩
  exact ⟨u, nhds_within_le_of_mem (insert_mem_nhds_within_insert hst) hu, p, H⟩

theorem ContDiffWithinAt.mono (h : ContDiffWithinAt 𝕜 n f s x) {t : Set E} (hst : t ⊆ s) : ContDiffWithinAt 𝕜 n f t x :=
  h.mono_of_mem <| Filter.mem_of_superset self_mem_nhds_within hst

theorem ContDiffWithinAt.congr_nhds (h : ContDiffWithinAt 𝕜 n f s x) {t : Set E} (hst : 𝓝[s] x = 𝓝[t] x) :
    ContDiffWithinAt 𝕜 n f t x :=
  h.mono_of_mem <| hst ▸ self_mem_nhds_within

theorem cont_diff_within_at_congr_nhds {t : Set E} (hst : 𝓝[s] x = 𝓝[t] x) :
    ContDiffWithinAt 𝕜 n f s x ↔ ContDiffWithinAt 𝕜 n f t x :=
  ⟨fun h => h.congr_nhds hst, fun h => h.congr_nhds hst.symm⟩

theorem cont_diff_within_at_inter' (h : t ∈ 𝓝[s] x) : ContDiffWithinAt 𝕜 n f (s ∩ t) x ↔ ContDiffWithinAt 𝕜 n f s x :=
  cont_diff_within_at_congr_nhds <| Eq.symm <| nhds_within_restrict'' _ h

theorem cont_diff_within_at_inter (h : t ∈ 𝓝 x) : ContDiffWithinAt 𝕜 n f (s ∩ t) x ↔ ContDiffWithinAt 𝕜 n f s x :=
  cont_diff_within_at_inter' (mem_nhds_within_of_mem_nhds h)

/-- If a function is `C^n` within a set at a point, with `n ≥ 1`, then it is differentiable
within this set at this point. -/
theorem ContDiffWithinAt.differentiable_within_at' (h : ContDiffWithinAt 𝕜 n f s x) (hn : 1 ≤ n) :
    DifferentiableWithinAt 𝕜 f (insert x s) x := by
  rcases h 1 hn with ⟨u, hu, p, H⟩
  rcases mem_nhds_within.1 hu with ⟨t, t_open, xt, tu⟩
  rw [inter_comm] at tu
  have := ((H.mono tu).DifferentiableOn le_rfl) x ⟨mem_insert x s, xt⟩
  exact (differentiable_within_at_inter (IsOpen.mem_nhds t_open xt)).1 this

theorem ContDiffWithinAt.differentiable_within_at (h : ContDiffWithinAt 𝕜 n f s x) (hn : 1 ≤ n) :
    DifferentiableWithinAt 𝕜 f s x :=
  (h.differentiable_within_at' hn).mono (subset_insert x s)

/-- A function is `C^(n + 1)` on a domain iff locally, it has a derivative which is `C^n`. -/
theorem cont_diff_within_at_succ_iff_has_fderiv_within_at {n : ℕ} :
    ContDiffWithinAt 𝕜 (n + 1 : ℕ) f s x ↔
      ∃ u ∈ 𝓝[insert x s] x,
        ∃ f' : E → E →L[𝕜] F, (∀, ∀ x ∈ u, ∀, HasFderivWithinAt f (f' x) u x) ∧ ContDiffWithinAt 𝕜 n f' u x :=
  by
  constructor
  · intro h
    rcases h n.succ le_rfl with ⟨u, hu, p, Hp⟩
    refine'
      ⟨u, hu, fun y => (continuousMultilinearCurryFin1 𝕜 E F) (p y 1), fun y hy =>
        Hp.has_fderiv_within_at (WithTop.coe_le_coe.2 (Nat.le_add_leftₓ 1 n)) hy, _⟩
    intro m hm
    refine' ⟨u, _, fun y : E => (p y).shift, _⟩
    · convert self_mem_nhds_within
      have : x ∈ insert x s := by
        simp
      exact insert_eq_of_mem (mem_of_mem_nhds_within this hu)
      
    · rw [has_ftaylor_series_up_to_on_succ_iff_right] at Hp
      exact Hp.2.2.of_le hm
      
    
  · rintro ⟨u, hu, f', f'_eq_deriv, Hf'⟩
    rw [cont_diff_within_at_nat]
    rcases Hf' n le_rfl with ⟨v, hv, p', Hp'⟩
    refine' ⟨v ∩ u, _, fun x => (p' x).unshift (f x), _⟩
    · apply Filter.inter_mem _ hu
      apply nhds_within_le_of_mem hu
      exact nhds_within_mono _ (subset_insert x u) hv
      
    · rw [has_ftaylor_series_up_to_on_succ_iff_right]
      refine' ⟨fun y hy => rfl, fun y hy => _, _⟩
      · change
          HasFderivWithinAt (fun z => (continuousMultilinearCurryFin0 𝕜 E F).symm (f z))
            (FormalMultilinearSeries.unshift (p' y) (f y) 1).curryLeft (v ∩ u) y
        rw [LinearIsometryEquiv.comp_has_fderiv_within_at_iff']
        convert (f'_eq_deriv y hy.2).mono (inter_subset_right v u)
        rw [← Hp'.zero_eq y hy.1]
        ext z
        change ((p' y 0) (init (@cons 0 (fun i => E) z 0))) (@cons 0 (fun i => E) z 0 (last 0)) = ((p' y 0) 0) z
        unfold_coes
        congr
        
      · convert (Hp'.mono (inter_subset_left v u)).congr fun x hx => Hp'.zero_eq x hx.1
        · ext x y
          change p' x 0 (init (@snoc 0 (fun i : Finₓ 1 => E) 0 y)) y = p' x 0 0 y
          rw [init_snoc]
          
        · ext x k v y
          change
            p' x k (init (@snoc k (fun i : Finₓ k.succ => E) v y)) (@snoc k (fun i : Finₓ k.succ => E) v y (last k)) =
              p' x k v y
          rw [snoc_last, init_snoc]
          
        
      
    

/-- One direction of `cont_diff_within_at_succ_iff_has_fderiv_within_at`, but where all derivatives
  are taken within the same set. -/
theorem ContDiffWithinAt.has_fderiv_within_at_nhds {n : ℕ} (hf : ContDiffWithinAt 𝕜 (n + 1 : ℕ) f s x) :
    ∃ u ∈ 𝓝[insert x s] x,
      u ⊆ insert x s ∧
        ∃ f' : E → E →L[𝕜] F, (∀, ∀ x ∈ u, ∀, HasFderivWithinAt f (f' x) s x) ∧ ContDiffWithinAt 𝕜 n f' s x :=
  by
  obtain ⟨u, hu, f', huf', hf'⟩ := cont_diff_within_at_succ_iff_has_fderiv_within_at.mp hf
  obtain ⟨w, hw, hxw, hwu⟩ := mem_nhds_within.mp hu
  rw [inter_comm] at hwu
  refine' ⟨insert x s ∩ w, inter_mem_nhds_within _ (hw.mem_nhds hxw), inter_subset_left _ _, f', fun y hy => _, _⟩
  · refine' ((huf' y <| hwu hy).mono hwu).mono_of_mem _
    refine' mem_of_superset _ (inter_subset_inter_left _ (subset_insert _ _))
    refine' inter_mem_nhds_within _ (hw.mem_nhds hy.2)
    
  · exact hf'.mono_of_mem (nhds_within_mono _ (subset_insert _ _) hu)
    

/-- A version of `cont_diff_within_at_succ_iff_has_fderiv_within_at` where all derivatives
  are taken within the same set. This lemma assumes `x ∈ s`. -/
theorem cont_diff_within_at_succ_iff_has_fderiv_within_at_of_mem {n : ℕ} (hx : x ∈ s) :
    ContDiffWithinAt 𝕜 (n + 1 : ℕ) f s x ↔
      ∃ u ∈ 𝓝[s] x,
        u ⊆ s ∧ ∃ f' : E → E →L[𝕜] F, (∀, ∀ x ∈ u, ∀, HasFderivWithinAt f (f' x) s x) ∧ ContDiffWithinAt 𝕜 n f' s x :=
  by
  constructor
  · intro hf
    simpa only [← insert_eq_of_mem hx] using hf.has_fderiv_within_at_nhds
    
  rw [cont_diff_within_at_succ_iff_has_fderiv_within_at, insert_eq_of_mem hx]
  rintro ⟨u, hu, hus, f', huf', hf'⟩
  exact ⟨u, hu, f', fun y hy => (huf' y hy).mono hus, hf'.mono hus⟩

/-! ### Smooth functions within a set -/


variable (𝕜)

/-- A function is continuously differentiable up to `n` on `s` if, for any point `x` in `s`, it
admits continuous derivatives up to order `n` on a neighborhood of `x` in `s`.

For `n = ∞`, we only require that this holds up to any finite order (where the neighborhood may
depend on the finite order we consider).
-/
def ContDiffOn (n : WithTop ℕ) (f : E → F) (s : Set E) :=
  ∀, ∀ x ∈ s, ∀, ContDiffWithinAt 𝕜 n f s x

variable {𝕜}

theorem ContDiffOn.cont_diff_within_at (h : ContDiffOn 𝕜 n f s) (hx : x ∈ s) : ContDiffWithinAt 𝕜 n f s x :=
  h x hx

theorem ContDiffWithinAt.cont_diff_on {m : ℕ} (hm : (m : WithTop ℕ) ≤ n) (h : ContDiffWithinAt 𝕜 n f s x) :
    ∃ u ∈ 𝓝[insert x s] x, u ⊆ insert x s ∧ ContDiffOn 𝕜 m f u := by
  rcases h m hm with ⟨u, u_nhd, p, hp⟩
  refine' ⟨u ∩ insert x s, Filter.inter_mem u_nhd self_mem_nhds_within, inter_subset_right _ _, _⟩
  intro y hy m' hm'
  refine' ⟨u ∩ insert x s, _, p, (hp.mono (inter_subset_left _ _)).of_le hm'⟩
  convert self_mem_nhds_within
  exact insert_eq_of_mem hy

protected theorem ContDiffWithinAt.eventually {n : ℕ} (h : ContDiffWithinAt 𝕜 n f s x) :
    ∀ᶠ y in 𝓝[insert x s] x, ContDiffWithinAt 𝕜 n f s y := by
  rcases h.cont_diff_on le_rfl with ⟨u, hu, hu_sub, hd⟩
  have : ∀ᶠ y : E in 𝓝[insert x s] x, u ∈ 𝓝[insert x s] y ∧ y ∈ u := (eventually_nhds_within_nhds_within.2 hu).And hu
  refine' this.mono fun y hy => (hd y hy.2).mono_of_mem _
  exact nhds_within_mono y (subset_insert _ _) hy.1

theorem ContDiffOn.of_le (h : ContDiffOn 𝕜 n f s) (hmn : m ≤ n) : ContDiffOn 𝕜 m f s := fun x hx => (h x hx).of_le hmn

theorem cont_diff_on_iff_forall_nat_le : ContDiffOn 𝕜 n f s ↔ ∀ m : ℕ, ↑m ≤ n → ContDiffOn 𝕜 m f s :=
  ⟨fun H m hm => H.of_le hm, fun H x hx m hm => H m hm x hx m le_rfl⟩

theorem cont_diff_on_top : ContDiffOn 𝕜 ∞ f s ↔ ∀ n : ℕ, ContDiffOn 𝕜 n f s :=
  cont_diff_on_iff_forall_nat_le.trans <| by
    simp only [← le_top, ← forall_prop_of_true]

theorem cont_diff_on_all_iff_nat : (∀ n, ContDiffOn 𝕜 n f s) ↔ ∀ n : ℕ, ContDiffOn 𝕜 n f s := by
  refine' ⟨fun H n => H n, _⟩
  rintro H (_ | n)
  exacts[cont_diff_on_top.2 H, H n]

theorem ContDiffOn.continuous_on (h : ContDiffOn 𝕜 n f s) : ContinuousOn f s := fun x hx => (h x hx).ContinuousWithinAt

theorem ContDiffOn.congr (h : ContDiffOn 𝕜 n f s) (h₁ : ∀, ∀ x ∈ s, ∀, f₁ x = f x) : ContDiffOn 𝕜 n f₁ s := fun x hx =>
  (h x hx).congr h₁ (h₁ x hx)

theorem cont_diff_on_congr (h₁ : ∀, ∀ x ∈ s, ∀, f₁ x = f x) : ContDiffOn 𝕜 n f₁ s ↔ ContDiffOn 𝕜 n f s :=
  ⟨fun H => H.congr fun x hx => (h₁ x hx).symm, fun H => H.congr h₁⟩

theorem ContDiffOn.mono (h : ContDiffOn 𝕜 n f s) {t : Set E} (hst : t ⊆ s) : ContDiffOn 𝕜 n f t := fun x hx =>
  (h x (hst hx)).mono hst

theorem ContDiffOn.congr_mono (hf : ContDiffOn 𝕜 n f s) (h₁ : ∀, ∀ x ∈ s₁, ∀, f₁ x = f x) (hs : s₁ ⊆ s) :
    ContDiffOn 𝕜 n f₁ s₁ :=
  (hf.mono hs).congr h₁

/-- If a function is `C^n` on a set with `n ≥ 1`, then it is differentiable there. -/
theorem ContDiffOn.differentiable_on (h : ContDiffOn 𝕜 n f s) (hn : 1 ≤ n) : DifferentiableOn 𝕜 f s := fun x hx =>
  (h x hx).DifferentiableWithinAt hn

/-- If a function is `C^n` around each point in a set, then it is `C^n` on the set. -/
theorem cont_diff_on_of_locally_cont_diff_on (h : ∀, ∀ x ∈ s, ∀, ∃ u, IsOpen u ∧ x ∈ u ∧ ContDiffOn 𝕜 n f (s ∩ u)) :
    ContDiffOn 𝕜 n f s := by
  intro x xs
  rcases h x xs with ⟨u, u_open, xu, hu⟩
  apply (cont_diff_within_at_inter _).1 (hu x ⟨xs, xu⟩)
  exact IsOpen.mem_nhds u_open xu

/-- A function is `C^(n + 1)` on a domain iff locally, it has a derivative which is `C^n`. -/
theorem cont_diff_on_succ_iff_has_fderiv_within_at {n : ℕ} :
    ContDiffOn 𝕜 (n + 1 : ℕ) f s ↔
      ∀,
        ∀ x ∈ s,
          ∀,
            ∃ u ∈ 𝓝[insert x s] x,
              ∃ f' : E → E →L[𝕜] F, (∀, ∀ x ∈ u, ∀, HasFderivWithinAt f (f' x) u x) ∧ ContDiffOn 𝕜 n f' u :=
  by
  constructor
  · intro h x hx
    rcases(h x hx) n.succ le_rfl with ⟨u, hu, p, Hp⟩
    refine'
      ⟨u, hu, fun y => (continuousMultilinearCurryFin1 𝕜 E F) (p y 1), fun y hy =>
        Hp.has_fderiv_within_at (WithTop.coe_le_coe.2 (Nat.le_add_leftₓ 1 n)) hy, _⟩
    rw [has_ftaylor_series_up_to_on_succ_iff_right] at Hp
    intro z hz m hm
    refine' ⟨u, _, fun x : E => (p x).shift, Hp.2.2.of_le hm⟩
    convert self_mem_nhds_within
    exact insert_eq_of_mem hz
    
  · intro h x hx
    rw [cont_diff_within_at_succ_iff_has_fderiv_within_at]
    rcases h x hx with ⟨u, u_nhbd, f', hu, hf'⟩
    have : x ∈ u := mem_of_mem_nhds_within (mem_insert _ _) u_nhbd
    exact ⟨u, u_nhbd, f', hu, hf' x this⟩
    

/-! ### Iterated derivative within a set -/


variable (𝕜)

/-- The `n`-th derivative of a function along a set, defined inductively by saying that the `n+1`-th
derivative of `f` is the derivative of the `n`-th derivative of `f` along this set, together with
an uncurrying step to see it as a multilinear map in `n+1` variables..
-/
noncomputable def iteratedFderivWithin (n : ℕ) (f : E → F) (s : Set E) : E → E[×n]→L[𝕜] F :=
  Nat.recOn n (fun x => ContinuousMultilinearMap.curry0 𝕜 E (f x)) fun n rec x =>
    ContinuousLinearMap.uncurryLeft (fderivWithin 𝕜 rec s x)

/-- Formal Taylor series associated to a function within a set. -/
def ftaylorSeriesWithin (f : E → F) (s : Set E) (x : E) : FormalMultilinearSeries 𝕜 E F := fun n =>
  iteratedFderivWithin 𝕜 n f s x

variable {𝕜}

@[simp]
theorem iterated_fderiv_within_zero_apply (m : Finₓ 0 → E) :
    (iteratedFderivWithin 𝕜 0 f s x : (Finₓ 0 → E) → F) m = f x :=
  rfl

theorem iterated_fderiv_within_zero_eq_comp :
    iteratedFderivWithin 𝕜 0 f s = (continuousMultilinearCurryFin0 𝕜 E F).symm ∘ f :=
  rfl

theorem iterated_fderiv_within_succ_apply_left {n : ℕ} (m : Finₓ (n + 1) → E) :
    (iteratedFderivWithin 𝕜 (n + 1) f s x : (Finₓ (n + 1) → E) → F) m =
      (fderivWithin 𝕜 (iteratedFderivWithin 𝕜 n f s) s x : E → E[×n]→L[𝕜] F) (m 0) (tail m) :=
  rfl

/-- Writing explicitly the `n+1`-th derivative as the composition of a currying linear equiv,
and the derivative of the `n`-th derivative. -/
theorem iterated_fderiv_within_succ_eq_comp_left {n : ℕ} :
    iteratedFderivWithin 𝕜 (n + 1) f s =
      continuousMultilinearCurryLeftEquiv 𝕜 (fun i : Finₓ (n + 1) => E) F ∘
        fderivWithin 𝕜 (iteratedFderivWithin 𝕜 n f s) s :=
  rfl

theorem iterated_fderiv_within_succ_apply_right {n : ℕ} (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ s) (m : Finₓ (n + 1) → E) :
    (iteratedFderivWithin 𝕜 (n + 1) f s x : (Finₓ (n + 1) → E) → F) m =
      iteratedFderivWithin 𝕜 n (fun y => fderivWithin 𝕜 f s y) s x (init m) (m (last n)) :=
  by
  induction' n with n IH generalizing x
  · rw [iterated_fderiv_within_succ_eq_comp_left, iterated_fderiv_within_zero_eq_comp,
      iterated_fderiv_within_zero_apply, Function.comp_applyₓ, LinearIsometryEquiv.comp_fderiv_within _ (hs x hx)]
    rfl
    
  · let I := continuousMultilinearCurryRightEquiv' 𝕜 n E F
    have A :
      ∀,
        ∀ y ∈ s,
          ∀, iteratedFderivWithin 𝕜 n.succ f s y = (I ∘ iteratedFderivWithin 𝕜 n (fun y => fderivWithin 𝕜 f s y) s) y :=
      by
      intro y hy
      ext m
      rw [@IH m y hy]
      rfl
    calc
      (iteratedFderivWithin 𝕜 (n + 2) f s x : (Finₓ (n + 2) → E) → F) m =
          (fderivWithin 𝕜 (iteratedFderivWithin 𝕜 n.succ f s) s x : E → E[×n + 1]→L[𝕜] F) (m 0) (tail m) :=
        rfl _ =
          (fderivWithin 𝕜 (I ∘ iteratedFderivWithin 𝕜 n (fderivWithin 𝕜 f s) s) s x : E → E[×n + 1]→L[𝕜] F) (m 0)
            (tail m) :=
        by
        rw
          [fderiv_within_congr (hs x hx) A
            (A x
              hx)]_ =
          (I ∘ fderivWithin 𝕜 (iteratedFderivWithin 𝕜 n (fderivWithin 𝕜 f s) s) s x : E → E[×n + 1]→L[𝕜] F) (m 0)
            (tail m) :=
        by
        rw [LinearIsometryEquiv.comp_fderiv_within _ (hs x hx)]
        rfl _ =
          (fderivWithin 𝕜 (iteratedFderivWithin 𝕜 n (fun y => fderivWithin 𝕜 f s y) s) s x : E → E[×n]→L[𝕜] E →L[𝕜] F)
            (m 0) (init (tail m)) ((tail m) (last n)) :=
        rfl _ = iteratedFderivWithin 𝕜 (Nat.succ n) (fun y => fderivWithin 𝕜 f s y) s x (init m) (m (last (n + 1))) :=
        by
        rw [iterated_fderiv_within_succ_apply_left, tail_init_eq_init_tail]
        rfl
    

/-- Writing explicitly the `n+1`-th derivative as the composition of a currying linear equiv,
and the `n`-th derivative of the derivative. -/
theorem iterated_fderiv_within_succ_eq_comp_right {n : ℕ} (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ s) :
    iteratedFderivWithin 𝕜 (n + 1) f s x =
      (continuousMultilinearCurryRightEquiv' 𝕜 n E F ∘ iteratedFderivWithin 𝕜 n (fun y => fderivWithin 𝕜 f s y) s) x :=
  by
  ext m
  rw [iterated_fderiv_within_succ_apply_right hs hx]
  rfl

@[simp]
theorem iterated_fderiv_within_one_apply (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ s) (m : Finₓ 1 → E) :
    (iteratedFderivWithin 𝕜 1 f s x : (Finₓ 1 → E) → F) m = (fderivWithin 𝕜 f s x : E → F) (m 0) := by
  rw [iterated_fderiv_within_succ_apply_right hs hx, iterated_fderiv_within_zero_apply]
  rfl

/-- If two functions coincide on a set `s` of unique differentiability, then their iterated
differentials within this set coincide. -/
theorem iterated_fderiv_within_congr {n : ℕ} (hs : UniqueDiffOn 𝕜 s) (hL : ∀, ∀ y ∈ s, ∀, f₁ y = f y) (hx : x ∈ s) :
    iteratedFderivWithin 𝕜 n f₁ s x = iteratedFderivWithin 𝕜 n f s x := by
  induction' n with n IH generalizing x
  · ext m
    simp [← hL x hx]
    
  · have :
      fderivWithin 𝕜 (fun y => iteratedFderivWithin 𝕜 n f₁ s y) s x =
        fderivWithin 𝕜 (fun y => iteratedFderivWithin 𝕜 n f s y) s x :=
      fderiv_within_congr (hs x hx) (fun y hy => IH hy) (IH hx)
    ext m
    rw [iterated_fderiv_within_succ_apply_left, iterated_fderiv_within_succ_apply_left, this]
    

/-- The iterated differential within a set `s` at a point `x` is not modified if one intersects
`s` with an open set containing `x`. -/
theorem iterated_fderiv_within_inter_open {n : ℕ} (hu : IsOpen u) (hs : UniqueDiffOn 𝕜 (s ∩ u)) (hx : x ∈ s ∩ u) :
    iteratedFderivWithin 𝕜 n f (s ∩ u) x = iteratedFderivWithin 𝕜 n f s x := by
  induction' n with n IH generalizing x
  · ext m
    simp
    
  · have A :
      fderivWithin 𝕜 (fun y => iteratedFderivWithin 𝕜 n f (s ∩ u) y) (s ∩ u) x =
        fderivWithin 𝕜 (fun y => iteratedFderivWithin 𝕜 n f s y) (s ∩ u) x :=
      fderiv_within_congr (hs x hx) (fun y hy => IH hy) (IH hx)
    have B :
      fderivWithin 𝕜 (fun y => iteratedFderivWithin 𝕜 n f s y) (s ∩ u) x =
        fderivWithin 𝕜 (fun y => iteratedFderivWithin 𝕜 n f s y) s x :=
      fderiv_within_inter (IsOpen.mem_nhds hu hx.2)
        ((unique_diff_within_at_inter (IsOpen.mem_nhds hu hx.2)).1 (hs x hx))
    ext m
    rw [iterated_fderiv_within_succ_apply_left, iterated_fderiv_within_succ_apply_left, A, B]
    

/-- The iterated differential within a set `s` at a point `x` is not modified if one intersects
`s` with a neighborhood of `x` within `s`. -/
theorem iterated_fderiv_within_inter' {n : ℕ} (hu : u ∈ 𝓝[s] x) (hs : UniqueDiffOn 𝕜 s) (xs : x ∈ s) :
    iteratedFderivWithin 𝕜 n f (s ∩ u) x = iteratedFderivWithin 𝕜 n f s x := by
  obtain ⟨v, v_open, xv, vu⟩ : ∃ v, IsOpen v ∧ x ∈ v ∧ v ∩ s ⊆ u := mem_nhds_within.1 hu
  have A : s ∩ u ∩ v = s ∩ v := by
    apply subset.antisymm (inter_subset_inter (inter_subset_left _ _) (subset.refl _))
    exact fun y ⟨ys, yv⟩ => ⟨⟨ys, vu ⟨yv, ys⟩⟩, yv⟩
  have : iteratedFderivWithin 𝕜 n f (s ∩ v) x = iteratedFderivWithin 𝕜 n f s x :=
    iterated_fderiv_within_inter_open v_open (hs.inter v_open) ⟨xs, xv⟩
  rw [← this]
  have : iteratedFderivWithin 𝕜 n f (s ∩ u ∩ v) x = iteratedFderivWithin 𝕜 n f (s ∩ u) x := by
    refine' iterated_fderiv_within_inter_open v_open _ ⟨⟨xs, vu ⟨xv, xs⟩⟩, xv⟩
    rw [A]
    exact hs.inter v_open
  rw [A] at this
  rw [← this]

/-- The iterated differential within a set `s` at a point `x` is not modified if one intersects
`s` with a neighborhood of `x`. -/
theorem iterated_fderiv_within_inter {n : ℕ} (hu : u ∈ 𝓝 x) (hs : UniqueDiffOn 𝕜 s) (xs : x ∈ s) :
    iteratedFderivWithin 𝕜 n f (s ∩ u) x = iteratedFderivWithin 𝕜 n f s x :=
  iterated_fderiv_within_inter' (mem_nhds_within_of_mem_nhds hu) hs xs

@[simp]
theorem cont_diff_on_zero : ContDiffOn 𝕜 0 f s ↔ ContinuousOn f s := by
  refine' ⟨fun H => H.ContinuousOn, fun H => _⟩
  intro x hx m hm
  have : (m : WithTop ℕ) = 0 := le_antisymmₓ hm bot_le
  rw [this]
  refine' ⟨insert x s, self_mem_nhds_within, ftaylorSeriesWithin 𝕜 f s, _⟩
  rw [has_ftaylor_series_up_to_on_zero_iff]
  exact
    ⟨by
      rwa [insert_eq_of_mem hx], fun x hx => by
      simp [← ftaylorSeriesWithin]⟩

theorem cont_diff_within_at_zero (hx : x ∈ s) : ContDiffWithinAt 𝕜 0 f s x ↔ ∃ u ∈ 𝓝[s] x, ContinuousOn f (s ∩ u) := by
  constructor
  · intro h
    obtain ⟨u, H, p, hp⟩ :=
      h 0
        (by
          norm_num)
    refine' ⟨u, _, _⟩
    · simpa [← hx] using H
      
    · simp only [← WithTop.coe_zero, ← has_ftaylor_series_up_to_on_zero_iff] at hp
      exact hp.1.mono (inter_subset_right s u)
      
    
  · rintro ⟨u, H, hu⟩
    rw [← cont_diff_within_at_inter' H]
    have h' : x ∈ s ∩ u := ⟨hx, mem_of_mem_nhds_within hx H⟩
    exact (cont_diff_on_zero.mpr hu).ContDiffWithinAt h'
    

/-- On a set with unique differentiability, any choice of iterated differential has to coincide
with the one we have chosen in `iterated_fderiv_within 𝕜 m f s`. -/
theorem HasFtaylorSeriesUpToOn.eq_ftaylor_series_of_unique_diff_on (h : HasFtaylorSeriesUpToOn n f p s) {m : ℕ}
    (hmn : (m : WithTop ℕ) ≤ n) (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ s) : p x m = iteratedFderivWithin 𝕜 m f s x := by
  induction' m with m IH generalizing x
  · rw [h.zero_eq' hx, iterated_fderiv_within_zero_eq_comp]
    
  · have A : (m : WithTop ℕ) < n := lt_of_lt_of_leₓ (WithTop.coe_lt_coe.2 (lt_add_one m)) hmn
    have :
      HasFderivWithinAt (fun y : E => iteratedFderivWithin 𝕜 m f s y)
        (ContinuousMultilinearMap.curryLeft (p x (Nat.succ m))) s x :=
      (h.fderiv_within m A x hx).congr (fun y hy => (IH (le_of_ltₓ A) hy).symm) (IH (le_of_ltₓ A) hx).symm
    rw [iterated_fderiv_within_succ_eq_comp_left, Function.comp_applyₓ, this.fderiv_within (hs x hx)]
    exact (ContinuousMultilinearMap.uncurry_curry_left _).symm
    

/-- When a function is `C^n` in a set `s` of unique differentiability, it admits
`ftaylor_series_within 𝕜 f s` as a Taylor series up to order `n` in `s`. -/
theorem ContDiffOn.ftaylor_series_within (h : ContDiffOn 𝕜 n f s) (hs : UniqueDiffOn 𝕜 s) :
    HasFtaylorSeriesUpToOn n f (ftaylorSeriesWithin 𝕜 f s) s := by
  constructor
  · intro x hx
    simp only [← ftaylorSeriesWithin, ← ContinuousMultilinearMap.uncurry0_apply, ← iterated_fderiv_within_zero_apply]
    
  · intro m hm x hx
    rcases(h x hx) m.succ (WithTop.add_one_le_of_lt hm) with ⟨u, hu, p, Hp⟩
    rw [insert_eq_of_mem hx] at hu
    rcases mem_nhds_within.1 hu with ⟨o, o_open, xo, ho⟩
    rw [inter_comm] at ho
    have : p x m.succ = ftaylorSeriesWithin 𝕜 f s x m.succ := by
      change p x m.succ = iteratedFderivWithin 𝕜 m.succ f s x
      rw [← iterated_fderiv_within_inter (IsOpen.mem_nhds o_open xo) hs hx]
      exact (Hp.mono ho).eq_ftaylor_series_of_unique_diff_on le_rfl (hs.inter o_open) ⟨hx, xo⟩
    rw [← this, ← has_fderiv_within_at_inter (IsOpen.mem_nhds o_open xo)]
    have A : ∀, ∀ y ∈ s ∩ o, ∀, p y m = ftaylorSeriesWithin 𝕜 f s y m := by
      rintro y ⟨hy, yo⟩
      change p y m = iteratedFderivWithin 𝕜 m f s y
      rw [← iterated_fderiv_within_inter (IsOpen.mem_nhds o_open yo) hs hy]
      exact
        (Hp.mono ho).eq_ftaylor_series_of_unique_diff_on (WithTop.coe_le_coe.2 (Nat.le_succₓ m)) (hs.inter o_open)
          ⟨hy, yo⟩
    exact
      ((Hp.mono ho).fderivWithin m (WithTop.coe_lt_coe.2 (lt_add_one m)) x ⟨hx, xo⟩).congr (fun y hy => (A y hy).symm)
        (A x ⟨hx, xo⟩).symm
    
  · intro m hm
    apply continuous_on_of_locally_continuous_on
    intro x hx
    rcases h x hx m hm with ⟨u, hu, p, Hp⟩
    rcases mem_nhds_within.1 hu with ⟨o, o_open, xo, ho⟩
    rw [insert_eq_of_mem hx] at ho
    rw [inter_comm] at ho
    refine' ⟨o, o_open, xo, _⟩
    have A : ∀, ∀ y ∈ s ∩ o, ∀, p y m = ftaylorSeriesWithin 𝕜 f s y m := by
      rintro y ⟨hy, yo⟩
      change p y m = iteratedFderivWithin 𝕜 m f s y
      rw [← iterated_fderiv_within_inter (IsOpen.mem_nhds o_open yo) hs hy]
      exact (Hp.mono ho).eq_ftaylor_series_of_unique_diff_on le_rfl (hs.inter o_open) ⟨hy, yo⟩
    exact ((Hp.mono ho).cont m le_rfl).congr fun y hy => (A y hy).symm
    

theorem cont_diff_on_of_continuous_on_differentiable_on
    (Hcont : ∀ m : ℕ, (m : WithTop ℕ) ≤ n → ContinuousOn (fun x => iteratedFderivWithin 𝕜 m f s x) s)
    (Hdiff : ∀ m : ℕ, (m : WithTop ℕ) < n → DifferentiableOn 𝕜 (fun x => iteratedFderivWithin 𝕜 m f s x) s) :
    ContDiffOn 𝕜 n f s := by
  intro x hx m hm
  rw [insert_eq_of_mem hx]
  refine' ⟨s, self_mem_nhds_within, ftaylorSeriesWithin 𝕜 f s, _⟩
  constructor
  · intro y hy
    simp only [← ftaylorSeriesWithin, ← ContinuousMultilinearMap.uncurry0_apply, ← iterated_fderiv_within_zero_apply]
    
  · intro k hk y hy
    convert (Hdiff k (lt_of_lt_of_leₓ hk hm) y hy).HasFderivWithinAt
    simp only [← ftaylorSeriesWithin, ← iterated_fderiv_within_succ_eq_comp_left, ← ContinuousLinearEquiv.coe_apply, ←
      Function.comp_app, ← coe_fn_coe_base]
    exact ContinuousLinearMap.curry_uncurry_left _
    
  · intro k hk
    exact Hcont k (le_transₓ hk hm)
    

theorem cont_diff_on_of_differentiable_on
    (h : ∀ m : ℕ, (m : WithTop ℕ) ≤ n → DifferentiableOn 𝕜 (iteratedFderivWithin 𝕜 m f s) s) : ContDiffOn 𝕜 n f s :=
  cont_diff_on_of_continuous_on_differentiable_on (fun m hm => (h m hm).ContinuousOn) fun m hm => h m (le_of_ltₓ hm)

theorem ContDiffOn.continuous_on_iterated_fderiv_within {m : ℕ} (h : ContDiffOn 𝕜 n f s) (hmn : (m : WithTop ℕ) ≤ n)
    (hs : UniqueDiffOn 𝕜 s) : ContinuousOn (iteratedFderivWithin 𝕜 m f s) s :=
  (h.ftaylorSeriesWithin hs).cont m hmn

theorem ContDiffOn.differentiable_on_iterated_fderiv_within {m : ℕ} (h : ContDiffOn 𝕜 n f s) (hmn : (m : WithTop ℕ) < n)
    (hs : UniqueDiffOn 𝕜 s) : DifferentiableOn 𝕜 (iteratedFderivWithin 𝕜 m f s) s := fun x hx =>
  ((h.ftaylorSeriesWithin hs).fderivWithin m hmn x hx).DifferentiableWithinAt

theorem cont_diff_on_iff_continuous_on_differentiable_on (hs : UniqueDiffOn 𝕜 s) :
    ContDiffOn 𝕜 n f s ↔
      (∀ m : ℕ, (m : WithTop ℕ) ≤ n → ContinuousOn (fun x => iteratedFderivWithin 𝕜 m f s x) s) ∧
        ∀ m : ℕ, (m : WithTop ℕ) < n → DifferentiableOn 𝕜 (fun x => iteratedFderivWithin 𝕜 m f s x) s :=
  by
  constructor
  · intro h
    constructor
    · intro m hm
      exact h.continuous_on_iterated_fderiv_within hm hs
      
    · intro m hm
      exact h.differentiable_on_iterated_fderiv_within hm hs
      
    
  · intro h
    exact cont_diff_on_of_continuous_on_differentiable_on h.1 h.2
    

theorem cont_diff_on_succ_of_fderiv_within {n : ℕ} (hf : DifferentiableOn 𝕜 f s)
    (h : ContDiffOn 𝕜 n (fun y => fderivWithin 𝕜 f s y) s) : ContDiffOn 𝕜 (n + 1 : ℕ) f s := by
  intro x hx
  rw [cont_diff_within_at_succ_iff_has_fderiv_within_at, insert_eq_of_mem hx]
  exact ⟨s, self_mem_nhds_within, fderivWithin 𝕜 f s, fun y hy => (hf y hy).HasFderivWithinAt, h x hx⟩

/-- A function is `C^(n + 1)` on a domain with unique derivatives if and only if it is
differentiable there, and its derivative (expressed with `fderiv_within`) is `C^n`. -/
theorem cont_diff_on_succ_iff_fderiv_within {n : ℕ} (hs : UniqueDiffOn 𝕜 s) :
    ContDiffOn 𝕜 (n + 1 : ℕ) f s ↔ DifferentiableOn 𝕜 f s ∧ ContDiffOn 𝕜 n (fun y => fderivWithin 𝕜 f s y) s := by
  refine' ⟨fun H => _, fun h => cont_diff_on_succ_of_fderiv_within h.1 h.2⟩
  refine' ⟨H.differentiable_on (WithTop.coe_le_coe.2 (Nat.le_add_leftₓ 1 n)), fun x hx => _⟩
  rcases cont_diff_within_at_succ_iff_has_fderiv_within_at.1 (H x hx) with ⟨u, hu, f', hff', hf'⟩
  rcases mem_nhds_within.1 hu with ⟨o, o_open, xo, ho⟩
  rw [inter_comm, insert_eq_of_mem hx] at ho
  have := hf'.mono ho
  rw [cont_diff_within_at_inter' (mem_nhds_within_of_mem_nhds (IsOpen.mem_nhds o_open xo))] at this
  apply this.congr_of_eventually_eq' _ hx
  have : o ∩ s ∈ 𝓝[s] x := mem_nhds_within.2 ⟨o, o_open, xo, subset.refl _⟩
  rw [inter_comm] at this
  apply Filter.eventually_eq_of_mem this fun y hy => _
  have A : fderivWithin 𝕜 f (s ∩ o) y = f' y := ((hff' y (ho hy)).mono ho).fderivWithin (hs.inter o_open y hy)
  rwa [fderiv_within_inter (IsOpen.mem_nhds o_open hy.2) (hs y hy.1)] at A

-- ./././Mathport/Syntax/Translate/Basic.lean:647:16: unsupported tactic `congrm #[[expr «expr ∧ »(_, _)]]
/-- A function is `C^(n + 1)` on an open domain if and only if it is
differentiable there, and its derivative (expressed with `fderiv`) is `C^n`. -/
theorem cont_diff_on_succ_iff_fderiv_of_open {n : ℕ} (hs : IsOpen s) :
    ContDiffOn 𝕜 (n + 1 : ℕ) f s ↔ DifferentiableOn 𝕜 f s ∧ ContDiffOn 𝕜 n (fun y => fderiv 𝕜 f y) s := by
  rw [cont_diff_on_succ_iff_fderiv_within hs.unique_diff_on]
  trace "./././Mathport/Syntax/Translate/Basic.lean:647:16: unsupported tactic `congrm #[[expr «expr ∧ »(_, _)]]"
  apply cont_diff_on_congr
  intro x hx
  exact fderiv_within_of_open hs hx

/-- A function is `C^∞` on a domain with unique derivatives if and only if it is differentiable
there, and its derivative (expressed with `fderiv_within`) is `C^∞`. -/
theorem cont_diff_on_top_iff_fderiv_within (hs : UniqueDiffOn 𝕜 s) :
    ContDiffOn 𝕜 ∞ f s ↔ DifferentiableOn 𝕜 f s ∧ ContDiffOn 𝕜 ∞ (fun y => fderivWithin 𝕜 f s y) s := by
  constructor
  · intro h
    refine' ⟨h.differentiable_on le_top, _⟩
    apply cont_diff_on_top.2 fun n => ((cont_diff_on_succ_iff_fderiv_within hs).1 _).2
    exact h.of_le le_top
    
  · intro h
    refine' cont_diff_on_top.2 fun n => _
    have A : (n : WithTop ℕ) ≤ ∞ := le_top
    apply ((cont_diff_on_succ_iff_fderiv_within hs).2 ⟨h.1, h.2.of_le A⟩).of_le
    exact WithTop.coe_le_coe.2 (Nat.le_succₓ n)
    

-- ./././Mathport/Syntax/Translate/Basic.lean:647:16: unsupported tactic `congrm #[[expr «expr ∧ »(_, _)]]
/-- A function is `C^∞` on an open domain if and only if it is differentiable there, and its
derivative (expressed with `fderiv`) is `C^∞`. -/
theorem cont_diff_on_top_iff_fderiv_of_open (hs : IsOpen s) :
    ContDiffOn 𝕜 ∞ f s ↔ DifferentiableOn 𝕜 f s ∧ ContDiffOn 𝕜 ∞ (fun y => fderiv 𝕜 f y) s := by
  rw [cont_diff_on_top_iff_fderiv_within hs.unique_diff_on]
  trace "./././Mathport/Syntax/Translate/Basic.lean:647:16: unsupported tactic `congrm #[[expr «expr ∧ »(_, _)]]"
  apply cont_diff_on_congr
  intro x hx
  exact fderiv_within_of_open hs hx

theorem ContDiffOn.fderiv_within (hf : ContDiffOn 𝕜 n f s) (hs : UniqueDiffOn 𝕜 s) (hmn : m + 1 ≤ n) :
    ContDiffOn 𝕜 m (fun y => fderivWithin 𝕜 f s y) s := by
  cases m
  · change ∞ + 1 ≤ n at hmn
    have : n = ∞ := by
      simpa using hmn
    rw [this] at hf
    exact ((cont_diff_on_top_iff_fderiv_within hs).1 hf).2
    
  · change (m.succ : WithTop ℕ) ≤ n at hmn
    exact ((cont_diff_on_succ_iff_fderiv_within hs).1 (hf.of_le hmn)).2
    

theorem ContDiffOn.fderiv_of_open (hf : ContDiffOn 𝕜 n f s) (hs : IsOpen s) (hmn : m + 1 ≤ n) :
    ContDiffOn 𝕜 m (fun y => fderiv 𝕜 f y) s :=
  (hf.fderivWithin hs.UniqueDiffOn hmn).congr fun x hx => (fderiv_within_of_open hs hx).symm

theorem ContDiffOn.continuous_on_fderiv_within (h : ContDiffOn 𝕜 n f s) (hs : UniqueDiffOn 𝕜 s) (hn : 1 ≤ n) :
    ContinuousOn (fun x => fderivWithin 𝕜 f s x) s :=
  ((cont_diff_on_succ_iff_fderiv_within hs).1 (h.of_le hn)).2.ContinuousOn

theorem ContDiffOn.continuous_on_fderiv_of_open (h : ContDiffOn 𝕜 n f s) (hs : IsOpen s) (hn : 1 ≤ n) :
    ContinuousOn (fun x => fderiv 𝕜 f x) s :=
  ((cont_diff_on_succ_iff_fderiv_of_open hs).1 (h.of_le hn)).2.ContinuousOn

theorem ContDiffWithinAt.fderiv_within' (hf : ContDiffWithinAt 𝕜 n f s x)
    (hs : ∀ᶠ y in 𝓝[insert x s] x, UniqueDiffWithinAt 𝕜 s y) (hmn : m + 1 ≤ n) :
    ContDiffWithinAt 𝕜 m (fderivWithin 𝕜 f s) s x := by
  have : ∀ k : ℕ, (k + 1 : WithTop ℕ) ≤ n → ContDiffWithinAt 𝕜 k (fderivWithin 𝕜 f s) s x := by
    intro k hkn
    obtain ⟨v, hv, -, f', hvf', hf'⟩ := (hf.of_le hkn).has_fderiv_within_at_nhds
    apply hf'.congr_of_eventually_eq_insert
    filter_upwards [hv, hs]
    exact fun y hy h2y => (hvf' y hy).fderivWithin h2y
  induction m using WithTop.recTopCoe
  · obtain rfl := eq_top_iff.mpr hmn
    rw [cont_diff_within_at_top]
    exact fun m => this m le_top
    
  exact this m hmn

theorem ContDiffWithinAt.fderiv_within (hf : ContDiffWithinAt 𝕜 n f s x) (hs : UniqueDiffOn 𝕜 s)
    (hmn : (m + 1 : WithTop ℕ) ≤ n) (hxs : x ∈ s) : ContDiffWithinAt 𝕜 m (fderivWithin 𝕜 f s) s x :=
  hf.fderiv_within'
    (by
      rw [insert_eq_of_mem hxs]
      exact eventually_of_mem self_mem_nhds_within hs)
    hmn

/-- If a function is at least `C^1`, its bundled derivative (mapping `(x, v)` to `Df(x) v`) is
continuous. -/
theorem ContDiffOn.continuous_on_fderiv_within_apply (h : ContDiffOn 𝕜 n f s) (hs : UniqueDiffOn 𝕜 s) (hn : 1 ≤ n) :
    ContinuousOn (fun p : E × E => (fderivWithin 𝕜 f s p.1 : E → F) p.2) (s ×ˢ (Univ : Set E)) := by
  have A : Continuous fun q : (E →L[𝕜] F) × E => q.1 q.2 := is_bounded_bilinear_map_apply.continuous
  have B : ContinuousOn (fun p : E × E => (fderivWithin 𝕜 f s p.1, p.2)) (s ×ˢ (univ : Set E)) := by
    apply ContinuousOn.prod _ continuous_snd.continuous_on
    exact
      ContinuousOn.comp (h.continuous_on_fderiv_within hs hn) continuous_fst.continuous_on
        (prod_subset_preimage_fst _ _)
  exact A.comp_continuous_on B

/-! ### Functions with a Taylor series on the whole space -/


/-- `has_ftaylor_series_up_to n f p` registers the fact that `p 0 = f` and `p (m+1)` is a
derivative of `p m` for `m < n`, and is continuous for `m ≤ n`. This is a predicate analogous to
`has_fderiv_at` but for higher order derivatives. -/
structure HasFtaylorSeriesUpTo (n : WithTop ℕ) (f : E → F) (p : E → FormalMultilinearSeries 𝕜 E F) : Prop where
  zero_eq : ∀ x, (p x 0).uncurry0 = f x
  fderiv : ∀ (m : ℕ) (hm : (m : WithTop ℕ) < n), ∀ x, HasFderivAt (fun y => p y m) (p x m.succ).curryLeft x
  cont : ∀ (m : ℕ) (hm : (m : WithTop ℕ) ≤ n), Continuous fun x => p x m

theorem HasFtaylorSeriesUpTo.zero_eq' (h : HasFtaylorSeriesUpTo n f p) (x : E) :
    p x 0 = (continuousMultilinearCurryFin0 𝕜 E F).symm (f x) := by
  rw [← h.zero_eq x]
  symm
  exact ContinuousMultilinearMap.uncurry0_curry0 _

theorem has_ftaylor_series_up_to_on_univ_iff : HasFtaylorSeriesUpToOn n f p Univ ↔ HasFtaylorSeriesUpTo n f p := by
  constructor
  · intro H
    constructor
    · exact fun x => H.zero_eq x (mem_univ x)
      
    · intro m hm x
      rw [← has_fderiv_within_at_univ]
      exact H.fderiv_within m hm x (mem_univ x)
      
    · intro m hm
      rw [continuous_iff_continuous_on_univ]
      exact H.cont m hm
      
    
  · intro H
    constructor
    · exact fun x hx => H.zero_eq x
      
    · intro m hm x hx
      rw [has_fderiv_within_at_univ]
      exact H.fderiv m hm x
      
    · intro m hm
      rw [← continuous_iff_continuous_on_univ]
      exact H.cont m hm
      
    

theorem HasFtaylorSeriesUpTo.has_ftaylor_series_up_to_on (h : HasFtaylorSeriesUpTo n f p) (s : Set E) :
    HasFtaylorSeriesUpToOn n f p s :=
  (has_ftaylor_series_up_to_on_univ_iff.2 h).mono (subset_univ _)

theorem HasFtaylorSeriesUpTo.of_le (h : HasFtaylorSeriesUpTo n f p) (hmn : m ≤ n) : HasFtaylorSeriesUpTo m f p := by
  rw [← has_ftaylor_series_up_to_on_univ_iff] at h⊢
  exact h.of_le hmn

theorem HasFtaylorSeriesUpTo.continuous (h : HasFtaylorSeriesUpTo n f p) : Continuous f := by
  rw [← has_ftaylor_series_up_to_on_univ_iff] at h
  rw [continuous_iff_continuous_on_univ]
  exact h.continuous_on

theorem has_ftaylor_series_up_to_zero_iff : HasFtaylorSeriesUpTo 0 f p ↔ Continuous f ∧ ∀ x, (p x 0).uncurry0 = f x :=
  by
  simp [← has_ftaylor_series_up_to_on_univ_iff.symm, ← continuous_iff_continuous_on_univ, ←
    has_ftaylor_series_up_to_on_zero_iff]

/-- If a function has a Taylor series at order at least `1`, then the term of order `1` of this
series is a derivative of `f`. -/
theorem HasFtaylorSeriesUpTo.has_fderiv_at (h : HasFtaylorSeriesUpTo n f p) (hn : 1 ≤ n) (x : E) :
    HasFderivAt f (continuousMultilinearCurryFin1 𝕜 E F (p x 1)) x := by
  rw [← has_fderiv_within_at_univ]
  exact (has_ftaylor_series_up_to_on_univ_iff.2 h).HasFderivWithinAt hn (mem_univ _)

theorem HasFtaylorSeriesUpTo.differentiable (h : HasFtaylorSeriesUpTo n f p) (hn : 1 ≤ n) : Differentiable 𝕜 f :=
  fun x => (h.HasFderivAt hn x).DifferentiableAt

/-- `p` is a Taylor series of `f` up to `n+1` if and only if `p.shift` is a Taylor series up to `n`
for `p 1`, which is a derivative of `f`. -/
theorem has_ftaylor_series_up_to_succ_iff_right {n : ℕ} :
    HasFtaylorSeriesUpTo (n + 1 : ℕ) f p ↔
      (∀ x, (p x 0).uncurry0 = f x) ∧
        (∀ x, HasFderivAt (fun y => p y 0) (p x 1).curryLeft x) ∧
          HasFtaylorSeriesUpTo n (fun x => continuousMultilinearCurryFin1 𝕜 E F (p x 1)) fun x => (p x).shift :=
  by
  simp only [← has_ftaylor_series_up_to_on_succ_iff_right, has_ftaylor_series_up_to_on_univ_iff, ← mem_univ, ←
    forall_true_left, ← has_fderiv_within_at_univ]

/-! ### Smooth functions at a point -/


variable (𝕜)

/-- A function is continuously differentiable up to `n` at a point `x` if, for any integer `k ≤ n`,
there is a neighborhood of `x` where `f` admits derivatives up to order `n`, which are continuous.
-/
def ContDiffAt (n : WithTop ℕ) (f : E → F) (x : E) :=
  ContDiffWithinAt 𝕜 n f Univ x

variable {𝕜}

theorem cont_diff_within_at_univ : ContDiffWithinAt 𝕜 n f Univ x ↔ ContDiffAt 𝕜 n f x :=
  Iff.rfl

theorem cont_diff_at_top : ContDiffAt 𝕜 ∞ f x ↔ ∀ n : ℕ, ContDiffAt 𝕜 n f x := by
  simp [cont_diff_within_at_univ, ← cont_diff_within_at_top]

theorem ContDiffAt.cont_diff_within_at (h : ContDiffAt 𝕜 n f x) : ContDiffWithinAt 𝕜 n f s x :=
  h.mono (subset_univ _)

theorem ContDiffWithinAt.cont_diff_at (h : ContDiffWithinAt 𝕜 n f s x) (hx : s ∈ 𝓝 x) : ContDiffAt 𝕜 n f x := by
  rwa [ContDiffAt, ← cont_diff_within_at_inter hx, univ_inter]

theorem ContDiffAt.congr_of_eventually_eq (h : ContDiffAt 𝕜 n f x) (hg : f₁ =ᶠ[𝓝 x] f) : ContDiffAt 𝕜 n f₁ x :=
  h.congr_of_eventually_eq'
    (by
      rwa [nhds_within_univ])
    (mem_univ x)

theorem ContDiffAt.of_le (h : ContDiffAt 𝕜 n f x) (hmn : m ≤ n) : ContDiffAt 𝕜 m f x :=
  h.of_le hmn

theorem ContDiffAt.continuous_at (h : ContDiffAt 𝕜 n f x) : ContinuousAt f x := by
  simpa [← continuous_within_at_univ] using h.continuous_within_at

/-- If a function is `C^n` with `n ≥ 1` at a point, then it is differentiable there. -/
theorem ContDiffAt.differentiable_at (h : ContDiffAt 𝕜 n f x) (hn : 1 ≤ n) : DifferentiableAt 𝕜 f x := by
  simpa [← hn, ← differentiable_within_at_univ] using h.differentiable_within_at

/-- A function is `C^(n + 1)` at a point iff locally, it has a derivative which is `C^n`. -/
theorem cont_diff_at_succ_iff_has_fderiv_at {n : ℕ} :
    ContDiffAt 𝕜 (n + 1 : ℕ) f x ↔
      ∃ f' : E → E →L[𝕜] F, (∃ u ∈ 𝓝 x, ∀, ∀ x ∈ u, ∀, HasFderivAt f (f' x) x) ∧ ContDiffAt 𝕜 n f' x :=
  by
  rw [← cont_diff_within_at_univ, cont_diff_within_at_succ_iff_has_fderiv_within_at]
  simp only [← nhds_within_univ, ← exists_prop, ← mem_univ, ← insert_eq_of_mem]
  constructor
  · rintro ⟨u, H, f', h_fderiv, h_cont_diff⟩
    rcases mem_nhds_iff.mp H with ⟨t, htu, ht, hxt⟩
    refine' ⟨f', ⟨t, _⟩, h_cont_diff.cont_diff_at H⟩
    refine' ⟨mem_nhds_iff.mpr ⟨t, subset.rfl, ht, hxt⟩, _⟩
    intro y hyt
    refine' (h_fderiv y (htu hyt)).HasFderivAt _
    exact mem_nhds_iff.mpr ⟨t, htu, ht, hyt⟩
    
  · rintro ⟨f', ⟨u, H, h_fderiv⟩, h_cont_diff⟩
    refine' ⟨u, H, f', _, h_cont_diff.cont_diff_within_at⟩
    intro x hxu
    exact (h_fderiv x hxu).HasFderivWithinAt
    

protected theorem ContDiffAt.eventually {n : ℕ} (h : ContDiffAt 𝕜 n f x) : ∀ᶠ y in 𝓝 x, ContDiffAt 𝕜 n f y := by
  simpa [← nhds_within_univ] using h.eventually

/-! ### Smooth functions -/


variable (𝕜)

/-- A function is continuously differentiable up to `n` if it admits derivatives up to
order `n`, which are continuous. Contrary to the case of definitions in domains (where derivatives
might not be unique) we do not need to localize the definition in space or time.
-/
def ContDiff (n : WithTop ℕ) (f : E → F) :=
  ∃ p : E → FormalMultilinearSeries 𝕜 E F, HasFtaylorSeriesUpTo n f p

variable {𝕜}

theorem cont_diff_on_univ : ContDiffOn 𝕜 n f Univ ↔ ContDiff 𝕜 n f := by
  constructor
  · intro H
    use ftaylorSeriesWithin 𝕜 f univ
    rw [← has_ftaylor_series_up_to_on_univ_iff]
    exact H.ftaylor_series_within unique_diff_on_univ
    
  · rintro ⟨p, hp⟩ x hx m hm
    exact ⟨univ, Filter.univ_sets _, p, (hp.has_ftaylor_series_up_to_on univ).of_le hm⟩
    

theorem cont_diff_iff_cont_diff_at : ContDiff 𝕜 n f ↔ ∀ x, ContDiffAt 𝕜 n f x := by
  simp [cont_diff_on_univ, ← ContDiffOn, ← ContDiffAt]

theorem ContDiff.cont_diff_at (h : ContDiff 𝕜 n f) : ContDiffAt 𝕜 n f x :=
  cont_diff_iff_cont_diff_at.1 h x

theorem ContDiff.cont_diff_within_at (h : ContDiff 𝕜 n f) : ContDiffWithinAt 𝕜 n f s x :=
  h.ContDiffAt.ContDiffWithinAt

theorem cont_diff_top : ContDiff 𝕜 ∞ f ↔ ∀ n : ℕ, ContDiff 𝕜 n f := by
  simp [← cont_diff_on_univ.symm, ← cont_diff_on_top]

theorem cont_diff_all_iff_nat : (∀ n, ContDiff 𝕜 n f) ↔ ∀ n : ℕ, ContDiff 𝕜 n f := by
  simp only [cont_diff_on_univ, ← cont_diff_on_all_iff_nat]

theorem ContDiff.cont_diff_on (h : ContDiff 𝕜 n f) : ContDiffOn 𝕜 n f s :=
  (cont_diff_on_univ.2 h).mono (subset_univ _)

@[simp]
theorem cont_diff_zero : ContDiff 𝕜 0 f ↔ Continuous f := by
  rw [← cont_diff_on_univ, continuous_iff_continuous_on_univ]
  exact cont_diff_on_zero

theorem cont_diff_at_zero : ContDiffAt 𝕜 0 f x ↔ ∃ u ∈ 𝓝 x, ContinuousOn f u := by
  rw [← cont_diff_within_at_univ]
  simp [← cont_diff_within_at_zero, ← nhds_within_univ]

theorem cont_diff_at_one_iff :
    ContDiffAt 𝕜 1 f x ↔ ∃ f' : E → E →L[𝕜] F, ∃ u ∈ 𝓝 x, ContinuousOn f' u ∧ ∀, ∀ x ∈ u, ∀, HasFderivAt f (f' x) x :=
  by
  simp_rw [show (1 : WithTop ℕ) = (0 + 1 : ℕ) from (zero_addₓ 1).symm, cont_diff_at_succ_iff_has_fderiv_at,
    show ((0 : ℕ) : WithTop ℕ) = 0 from rfl, cont_diff_at_zero,
    exists_mem_and_iff antitone_bforall antitone_continuous_on, and_comm]

theorem ContDiff.of_le (h : ContDiff 𝕜 n f) (hmn : m ≤ n) : ContDiff 𝕜 m f :=
  cont_diff_on_univ.1 <| (cont_diff_on_univ.2 h).of_le hmn

theorem ContDiff.of_succ {n : ℕ} (h : ContDiff 𝕜 (n + 1) f) : ContDiff 𝕜 n f :=
  h.of_le <| WithTop.coe_le_coe.mpr le_self_add

theorem ContDiff.one_of_succ {n : ℕ} (h : ContDiff 𝕜 (n + 1) f) : ContDiff 𝕜 1 f :=
  h.of_le <| WithTop.coe_le_coe.mpr le_add_self

theorem ContDiff.continuous (h : ContDiff 𝕜 n f) : Continuous f :=
  cont_diff_zero.1 (h.of_le bot_le)

/-- If a function is `C^n` with `n ≥ 1`, then it is differentiable. -/
theorem ContDiff.differentiable (h : ContDiff 𝕜 n f) (hn : 1 ≤ n) : Differentiable 𝕜 f :=
  differentiable_on_univ.1 <| (cont_diff_on_univ.2 h).DifferentiableOn hn

/-! ### Iterated derivative -/


variable (𝕜)

/-- The `n`-th derivative of a function, as a multilinear map, defined inductively. -/
noncomputable def iteratedFderiv (n : ℕ) (f : E → F) : E → E[×n]→L[𝕜] F :=
  Nat.recOn n (fun x => ContinuousMultilinearMap.curry0 𝕜 E (f x)) fun n rec x =>
    ContinuousLinearMap.uncurryLeft (fderiv 𝕜 rec x)

/-- Formal Taylor series associated to a function within a set. -/
def ftaylorSeries (f : E → F) (x : E) : FormalMultilinearSeries 𝕜 E F := fun n => iteratedFderiv 𝕜 n f x

variable {𝕜}

@[simp]
theorem iterated_fderiv_zero_apply (m : Finₓ 0 → E) : (iteratedFderiv 𝕜 0 f x : (Finₓ 0 → E) → F) m = f x :=
  rfl

theorem iterated_fderiv_zero_eq_comp : iteratedFderiv 𝕜 0 f = (continuousMultilinearCurryFin0 𝕜 E F).symm ∘ f :=
  rfl

theorem iterated_fderiv_succ_apply_left {n : ℕ} (m : Finₓ (n + 1) → E) :
    (iteratedFderiv 𝕜 (n + 1) f x : (Finₓ (n + 1) → E) → F) m =
      (fderiv 𝕜 (iteratedFderiv 𝕜 n f) x : E → E[×n]→L[𝕜] F) (m 0) (tail m) :=
  rfl

/-- Writing explicitly the `n+1`-th derivative as the composition of a currying linear equiv,
and the derivative of the `n`-th derivative. -/
theorem iterated_fderiv_succ_eq_comp_left {n : ℕ} :
    iteratedFderiv 𝕜 (n + 1) f =
      continuousMultilinearCurryLeftEquiv 𝕜 (fun i : Finₓ (n + 1) => E) F ∘ fderiv 𝕜 (iteratedFderiv 𝕜 n f) :=
  rfl

theorem iterated_fderiv_within_univ {n : ℕ} : iteratedFderivWithin 𝕜 n f Univ = iteratedFderiv 𝕜 n f := by
  induction' n with n IH
  · ext x
    simp
    
  · ext x m
    rw [iterated_fderiv_succ_apply_left, iterated_fderiv_within_succ_apply_left, IH, fderiv_within_univ]
    

/-- In an open set, the iterated derivative within this set coincides with the global iterated
derivative. -/
theorem iterated_fderiv_within_of_is_open (n : ℕ) (hs : IsOpen s) :
    EqOn (iteratedFderivWithin 𝕜 n f s) (iteratedFderiv 𝕜 n f) s := by
  induction' n with n IH
  · intro x hx
    ext1 m
    simp only [← iterated_fderiv_within_zero_apply, ← iterated_fderiv_zero_apply]
    
  · intro x hx
    rw [iterated_fderiv_succ_eq_comp_left, iterated_fderiv_within_succ_eq_comp_left]
    dsimp'
    congr 1
    rw [fderiv_within_of_open hs hx]
    apply Filter.EventuallyEq.fderiv_eq
    filter_upwards [hs.mem_nhds hx]
    exact IH
    

theorem ftaylor_series_within_univ : ftaylorSeriesWithin 𝕜 f Univ = ftaylorSeries 𝕜 f := by
  ext1 x
  ext1 n
  change iteratedFderivWithin 𝕜 n f univ x = iteratedFderiv 𝕜 n f x
  rw [iterated_fderiv_within_univ]

theorem iterated_fderiv_succ_apply_right {n : ℕ} (m : Finₓ (n + 1) → E) :
    (iteratedFderiv 𝕜 (n + 1) f x : (Finₓ (n + 1) → E) → F) m =
      iteratedFderiv 𝕜 n (fun y => fderiv 𝕜 f y) x (init m) (m (last n)) :=
  by
  rw [← iterated_fderiv_within_univ, ← iterated_fderiv_within_univ, ← fderiv_within_univ]
  exact iterated_fderiv_within_succ_apply_right unique_diff_on_univ (mem_univ _) _

/-- Writing explicitly the `n+1`-th derivative as the composition of a currying linear equiv,
and the `n`-th derivative of the derivative. -/
theorem iterated_fderiv_succ_eq_comp_right {n : ℕ} :
    iteratedFderiv 𝕜 (n + 1) f x =
      (continuousMultilinearCurryRightEquiv' 𝕜 n E F ∘ iteratedFderiv 𝕜 n fun y => fderiv 𝕜 f y) x :=
  by
  ext m
  rw [iterated_fderiv_succ_apply_right]
  rfl

@[simp]
theorem iterated_fderiv_one_apply (m : Finₓ 1 → E) :
    (iteratedFderiv 𝕜 1 f x : (Finₓ 1 → E) → F) m = (fderiv 𝕜 f x : E → F) (m 0) := by
  rw [iterated_fderiv_succ_apply_right, iterated_fderiv_zero_apply]
  rfl

/-- When a function is `C^n` in a set `s` of unique differentiability, it admits
`ftaylor_series_within 𝕜 f s` as a Taylor series up to order `n` in `s`. -/
theorem cont_diff_on_iff_ftaylor_series : ContDiff 𝕜 n f ↔ HasFtaylorSeriesUpTo n f (ftaylorSeries 𝕜 f) := by
  constructor
  · rw [← cont_diff_on_univ, ← has_ftaylor_series_up_to_on_univ_iff, ← ftaylor_series_within_univ]
    exact fun h => ContDiffOn.ftaylor_series_within h unique_diff_on_univ
    
  · intro h
    exact ⟨ftaylorSeries 𝕜 f, h⟩
    

theorem cont_diff_iff_continuous_differentiable :
    ContDiff 𝕜 n f ↔
      (∀ m : ℕ, (m : WithTop ℕ) ≤ n → Continuous fun x => iteratedFderiv 𝕜 m f x) ∧
        ∀ m : ℕ, (m : WithTop ℕ) < n → Differentiable 𝕜 fun x => iteratedFderiv 𝕜 m f x :=
  by
  simp [← cont_diff_on_univ.symm, ← continuous_iff_continuous_on_univ, ← differentiable_on_univ.symm, ←
    iterated_fderiv_within_univ, ← cont_diff_on_iff_continuous_on_differentiable_on unique_diff_on_univ]

theorem cont_diff_of_differentiable_iterated_fderiv
    (h : ∀ m : ℕ, (m : WithTop ℕ) ≤ n → Differentiable 𝕜 (iteratedFderiv 𝕜 m f)) : ContDiff 𝕜 n f :=
  cont_diff_iff_continuous_differentiable.2 ⟨fun m hm => (h m hm).Continuous, fun m hm => h m (le_of_ltₓ hm)⟩

/-- A function is `C^(n + 1)` if and only if it is differentiable,
and its derivative (formulated in terms of `fderiv`) is `C^n`. -/
theorem cont_diff_succ_iff_fderiv {n : ℕ} :
    ContDiff 𝕜 (n + 1 : ℕ) f ↔ Differentiable 𝕜 f ∧ ContDiff 𝕜 n fun y => fderiv 𝕜 f y := by
  simp only [cont_diff_on_univ, differentiable_on_univ, fderiv_within_univ, ←
    cont_diff_on_succ_iff_fderiv_within unique_diff_on_univ]

theorem cont_diff_one_iff_fderiv : ContDiff 𝕜 1 f ↔ Differentiable 𝕜 f ∧ Continuous (fderiv 𝕜 f) :=
  cont_diff_succ_iff_fderiv.trans <| Iff.rfl.And cont_diff_zero

/-- A function is `C^∞` if and only if it is differentiable,
and its derivative (formulated in terms of `fderiv`) is `C^∞`. -/
theorem cont_diff_top_iff_fderiv : ContDiff 𝕜 ∞ f ↔ Differentiable 𝕜 f ∧ ContDiff 𝕜 ∞ fun y => fderiv 𝕜 f y := by
  simp [← cont_diff_on_univ.symm, ← differentiable_on_univ.symm, ← fderiv_within_univ.symm, -fderiv_within_univ]
  rw [cont_diff_on_top_iff_fderiv_within unique_diff_on_univ]

theorem ContDiff.continuous_fderiv (h : ContDiff 𝕜 n f) (hn : 1 ≤ n) : Continuous fun x => fderiv 𝕜 f x :=
  (cont_diff_succ_iff_fderiv.1 (h.of_le hn)).2.Continuous

/-- If a function is at least `C^1`, its bundled derivative (mapping `(x, v)` to `Df(x) v`) is
continuous. -/
theorem ContDiff.continuous_fderiv_apply (h : ContDiff 𝕜 n f) (hn : 1 ≤ n) :
    Continuous fun p : E × E => (fderiv 𝕜 f p.1 : E → F) p.2 := by
  have A : Continuous fun q : (E →L[𝕜] F) × E => q.1 q.2 := is_bounded_bilinear_map_apply.continuous
  have B : Continuous fun p : E × E => (fderiv 𝕜 f p.1, p.2) := by
    apply Continuous.prod_mk _ continuous_snd
    exact Continuous.comp (h.continuous_fderiv hn) continuous_fst
  exact A.comp B

/-! ### Constants -/


theorem iterated_fderiv_within_zero_fun {n : ℕ} : (iteratedFderiv 𝕜 n fun x : E => (0 : F)) = 0 := by
  induction' n with n IH
  · ext m
    simp
    
  · ext x m
    rw [iterated_fderiv_succ_apply_left, IH]
    change (fderiv 𝕜 (fun x : E => (0 : E[×n]→L[𝕜] F)) x : E → E[×n]→L[𝕜] F) (m 0) (tail m) = _
    rw [fderiv_const]
    rfl
    

theorem cont_diff_zero_fun : ContDiff 𝕜 n fun x : E => (0 : F) := by
  apply cont_diff_of_differentiable_iterated_fderiv fun m hm => _
  rw [iterated_fderiv_within_zero_fun]
  apply differentiable_const (0 : E[×m]→L[𝕜] F)

/-- Constants are `C^∞`.
-/
theorem cont_diff_const {c : F} : ContDiff 𝕜 n fun x : E => c := by
  suffices h : ContDiff 𝕜 ∞ fun x : E => c
  · exact h.of_le le_top
    
  rw [cont_diff_top_iff_fderiv]
  refine' ⟨differentiable_const c, _⟩
  rw [fderiv_const]
  exact cont_diff_zero_fun

theorem cont_diff_on_const {c : F} {s : Set E} : ContDiffOn 𝕜 n (fun x : E => c) s :=
  cont_diff_const.ContDiffOn

theorem cont_diff_at_const {c : F} : ContDiffAt 𝕜 n (fun x : E => c) x :=
  cont_diff_const.ContDiffAt

theorem cont_diff_within_at_const {c : F} : ContDiffWithinAt 𝕜 n (fun x : E => c) s x :=
  cont_diff_at_const.ContDiffWithinAt

@[nontriviality]
theorem cont_diff_of_subsingleton [Subsingleton F] : ContDiff 𝕜 n f := by
  rw [Subsingleton.elimₓ f fun _ => 0]
  exact cont_diff_const

@[nontriviality]
theorem cont_diff_at_of_subsingleton [Subsingleton F] : ContDiffAt 𝕜 n f x := by
  rw [Subsingleton.elimₓ f fun _ => 0]
  exact cont_diff_at_const

@[nontriviality]
theorem cont_diff_within_at_of_subsingleton [Subsingleton F] : ContDiffWithinAt 𝕜 n f s x := by
  rw [Subsingleton.elimₓ f fun _ => 0]
  exact cont_diff_within_at_const

@[nontriviality]
theorem cont_diff_on_of_subsingleton [Subsingleton F] : ContDiffOn 𝕜 n f s := by
  rw [Subsingleton.elimₓ f fun _ => 0]
  exact cont_diff_on_const

/-! ### Smoothness of linear functions -/


/-- Unbundled bounded linear functions are `C^∞`.
-/
theorem IsBoundedLinearMap.cont_diff (hf : IsBoundedLinearMap 𝕜 f) : ContDiff 𝕜 n f := by
  suffices h : ContDiff 𝕜 ∞ f
  · exact h.of_le le_top
    
  rw [cont_diff_top_iff_fderiv]
  refine' ⟨hf.differentiable, _⟩
  simp_rw [hf.fderiv]
  exact cont_diff_const

theorem ContinuousLinearMap.cont_diff (f : E →L[𝕜] F) : ContDiff 𝕜 n f :=
  f.IsBoundedLinearMap.ContDiff

theorem ContinuousLinearEquiv.cont_diff (f : E ≃L[𝕜] F) : ContDiff 𝕜 n f :=
  (f : E →L[𝕜] F).ContDiff

theorem LinearIsometry.cont_diff (f : E →ₗᵢ[𝕜] F) : ContDiff 𝕜 n f :=
  f.toContinuousLinearMap.ContDiff

theorem LinearIsometryEquiv.cont_diff (f : E ≃ₗᵢ[𝕜] F) : ContDiff 𝕜 n f :=
  (f : E →L[𝕜] F).ContDiff

/-- The identity is `C^∞`.
-/
theorem cont_diff_id : ContDiff 𝕜 n (id : E → E) :=
  IsBoundedLinearMap.id.ContDiff

theorem cont_diff_within_at_id {s x} : ContDiffWithinAt 𝕜 n (id : E → E) s x :=
  cont_diff_id.ContDiffWithinAt

theorem cont_diff_at_id {x} : ContDiffAt 𝕜 n (id : E → E) x :=
  cont_diff_id.ContDiffAt

theorem cont_diff_on_id {s} : ContDiffOn 𝕜 n (id : E → E) s :=
  cont_diff_id.ContDiffOn

/-- Bilinear functions are `C^∞`.
-/
theorem IsBoundedBilinearMap.cont_diff (hb : IsBoundedBilinearMap 𝕜 b) : ContDiff 𝕜 n b := by
  suffices h : ContDiff 𝕜 ∞ b
  · exact h.of_le le_top
    
  rw [cont_diff_top_iff_fderiv]
  refine' ⟨hb.differentiable, _⟩
  simp [← hb.fderiv]
  exact hb.is_bounded_linear_map_deriv.cont_diff

/-- If `f` admits a Taylor series `p` in a set `s`, and `g` is linear, then `g ∘ f` admits a Taylor
series whose `k`-th term is given by `g ∘ (p k)`. -/
theorem HasFtaylorSeriesUpToOn.continuous_linear_map_comp (g : F →L[𝕜] G) (hf : HasFtaylorSeriesUpToOn n f p s) :
    HasFtaylorSeriesUpToOn n (g ∘ f) (fun x k => g.compContinuousMultilinearMap (p x k)) s := by
  set L : ∀ m : ℕ, (E[×m]→L[𝕜] F) →L[𝕜] E[×m]→L[𝕜] G := fun m =>
    ContinuousLinearMap.compContinuousMultilinearMapL 𝕜 (fun _ => E) F G g
  constructor
  · exact fun x hx => congr_arg g (hf.zero_eq x hx)
    
  · intro m hm x hx
    convert (L m).HasFderivAt.comp_has_fderiv_within_at x (hf.fderiv_within m hm x hx)
    
  · intro m hm
    convert (L m).Continuous.comp_continuous_on (hf.cont m hm)
    

/-- Composition by continuous linear maps on the left preserves `C^n` functions in a domain
at a point. -/
theorem ContDiffWithinAt.continuous_linear_map_comp (g : F →L[𝕜] G) (hf : ContDiffWithinAt 𝕜 n f s x) :
    ContDiffWithinAt 𝕜 n (g ∘ f) s x := by
  intro m hm
  rcases hf m hm with ⟨u, hu, p, hp⟩
  exact ⟨u, hu, _, hp.continuous_linear_map_comp g⟩

/-- Composition by continuous linear maps on the left preserves `C^n` functions in a domain
at a point. -/
theorem ContDiffAt.continuous_linear_map_comp (g : F →L[𝕜] G) (hf : ContDiffAt 𝕜 n f x) : ContDiffAt 𝕜 n (g ∘ f) x :=
  ContDiffWithinAt.continuous_linear_map_comp g hf

/-- Composition by continuous linear maps on the left preserves `C^n` functions on domains. -/
theorem ContDiffOn.continuous_linear_map_comp (g : F →L[𝕜] G) (hf : ContDiffOn 𝕜 n f s) : ContDiffOn 𝕜 n (g ∘ f) s :=
  fun x hx => (hf x hx).continuous_linear_map_comp g

/-- Composition by continuous linear maps on the left preserves `C^n` functions. -/
theorem ContDiff.continuous_linear_map_comp {f : E → F} (g : F →L[𝕜] G) (hf : ContDiff 𝕜 n f) :
    ContDiff 𝕜 n fun x => g (f x) :=
  cont_diff_on_univ.1 <| ContDiffOn.continuous_linear_map_comp _ (cont_diff_on_univ.2 hf)

/-- Composition by continuous linear equivs on the left respects higher differentiability on
domains. -/
theorem ContinuousLinearEquiv.comp_cont_diff_within_at_iff (e : F ≃L[𝕜] G) :
    ContDiffWithinAt 𝕜 n (e ∘ f) s x ↔ ContDiffWithinAt 𝕜 n f s x :=
  ⟨fun H => by
    simpa only [← (· ∘ ·), ← e.symm.coe_coe, ← e.symm_apply_apply] using
      H.continuous_linear_map_comp (e.symm : G →L[𝕜] F),
    fun H => H.continuous_linear_map_comp (e : F →L[𝕜] G)⟩

/-- Composition by continuous linear equivs on the left respects higher differentiability on
domains. -/
theorem ContinuousLinearEquiv.comp_cont_diff_on_iff (e : F ≃L[𝕜] G) : ContDiffOn 𝕜 n (e ∘ f) s ↔ ContDiffOn 𝕜 n f s :=
  by
  simp [← ContDiffOn, ← e.comp_cont_diff_within_at_iff]

/-- If `f` admits a Taylor series `p` in a set `s`, and `g` is linear, then `f ∘ g` admits a Taylor
series in `g ⁻¹' s`, whose `k`-th term is given by `p k (g v₁, ..., g vₖ)` . -/
theorem HasFtaylorSeriesUpToOn.comp_continuous_linear_map (hf : HasFtaylorSeriesUpToOn n f p s) (g : G →L[𝕜] E) :
    HasFtaylorSeriesUpToOn n (f ∘ g) (fun x k => (p (g x) k).compContinuousLinearMap fun _ => g) (g ⁻¹' s) := by
  let A : ∀ m : ℕ, (E[×m]→L[𝕜] F) → G[×m]→L[𝕜] F := fun m h => h.compContinuousLinearMap fun _ => g
  have hA : ∀ m, IsBoundedLinearMap 𝕜 (A m) := fun m => is_bounded_linear_map_continuous_multilinear_map_comp_linear g
  constructor
  · intro x hx
    simp only [← (hf.zero_eq (g x) hx).symm, ← Function.comp_app]
    change (p (g x) 0 fun i : Finₓ 0 => g 0) = p (g x) 0 0
    rw [ContinuousLinearMap.map_zero]
    rfl
    
  · intro m hm x hx
    convert
      (hA m).HasFderivAt.comp_has_fderiv_within_at x
        ((hf.fderiv_within m hm (g x) hx).comp x g.has_fderiv_within_at (subset.refl _))
    ext y v
    change p (g x) (Nat.succ m) (g ∘ cons y v) = p (g x) m.succ (cons (g y) (g ∘ v))
    rw [comp_cons]
    
  · intro m hm
    exact (hA m).Continuous.comp_continuous_on ((hf.cont m hm).comp g.continuous.continuous_on (subset.refl _))
    

/-- Composition by continuous linear maps on the right preserves `C^n` functions at a point on
a domain. -/
theorem ContDiffWithinAt.comp_continuous_linear_map {x : G} (g : G →L[𝕜] E) (hf : ContDiffWithinAt 𝕜 n f s (g x)) :
    ContDiffWithinAt 𝕜 n (f ∘ g) (g ⁻¹' s) x := by
  intro m hm
  rcases hf m hm with ⟨u, hu, p, hp⟩
  refine' ⟨g ⁻¹' u, _, _, hp.comp_continuous_linear_map g⟩
  apply ContinuousWithinAt.preimage_mem_nhds_within'
  · exact g.continuous.continuous_within_at
    
  · apply nhds_within_mono (g x) _ hu
    rw [image_insert_eq]
    exact insert_subset_insert (image_preimage_subset g s)
    

/-- Composition by continuous linear maps on the right preserves `C^n` functions on domains. -/
theorem ContDiffOn.comp_continuous_linear_map (hf : ContDiffOn 𝕜 n f s) (g : G →L[𝕜] E) :
    ContDiffOn 𝕜 n (f ∘ g) (g ⁻¹' s) := fun x hx => (hf (g x) hx).compContinuousLinearMap g

/-- Composition by continuous linear maps on the right preserves `C^n` functions. -/
theorem ContDiff.comp_continuous_linear_map {f : E → F} {g : G →L[𝕜] E} (hf : ContDiff 𝕜 n f) : ContDiff 𝕜 n (f ∘ g) :=
  cont_diff_on_univ.1 <| ContDiffOn.comp_continuous_linear_map (cont_diff_on_univ.2 hf) _

/-- Composition by continuous linear equivs on the right respects higher differentiability at a
point in a domain. -/
theorem ContinuousLinearEquiv.cont_diff_within_at_comp_iff (e : G ≃L[𝕜] E) :
    ContDiffWithinAt 𝕜 n (f ∘ e) (e ⁻¹' s) (e.symm x) ↔ ContDiffWithinAt 𝕜 n f s x := by
  constructor
  · intro H
    simpa [preimage_comp, ← (· ∘ ·)] using H.comp_continuous_linear_map (e.symm : E →L[𝕜] G)
    
  · intro H
    rw [← e.apply_symm_apply x, ← e.coe_coe] at H
    exact H.comp_continuous_linear_map _
    

/-- Composition by continuous linear equivs on the right respects higher differentiability on
domains. -/
theorem ContinuousLinearEquiv.cont_diff_on_comp_iff (e : G ≃L[𝕜] E) :
    ContDiffOn 𝕜 n (f ∘ e) (e ⁻¹' s) ↔ ContDiffOn 𝕜 n f s := by
  refine' ⟨fun H => _, fun H => H.compContinuousLinearMap (e : G →L[𝕜] E)⟩
  have A : f = (f ∘ e) ∘ e.symm := by
    ext y
    simp only [← Function.comp_app]
    rw [e.apply_symm_apply y]
  have B : e.symm ⁻¹' (e ⁻¹' s) = s := by
    rw [← preimage_comp, e.self_comp_symm]
    rfl
  rw [A, ← B]
  exact H.comp_continuous_linear_map (e.symm : E →L[𝕜] G)

/-- If two functions `f` and `g` admit Taylor series `p` and `q` in a set `s`, then the cartesian
product of `f` and `g` admits the cartesian product of `p` and `q` as a Taylor series. -/
theorem HasFtaylorSeriesUpToOn.prod (hf : HasFtaylorSeriesUpToOn n f p s) {g : E → G}
    {q : E → FormalMultilinearSeries 𝕜 E G} (hg : HasFtaylorSeriesUpToOn n g q s) :
    HasFtaylorSeriesUpToOn n (fun y => (f y, g y)) (fun y k => (p y k).Prod (q y k)) s := by
  set L := fun m => ContinuousMultilinearMap.prodL 𝕜 (fun i : Finₓ m => E) F G
  constructor
  · intro x hx
    rw [← hf.zero_eq x hx, ← hg.zero_eq x hx]
    rfl
    
  · intro m hm x hx
    convert
      (L m).HasFderivAt.comp_has_fderiv_within_at x ((hf.fderiv_within m hm x hx).Prod (hg.fderiv_within m hm x hx))
    
  · intro m hm
    exact (L m).Continuous.comp_continuous_on ((hf.cont m hm).Prod (hg.cont m hm))
    

/-- The cartesian product of `C^n` functions at a point in a domain is `C^n`. -/
theorem ContDiffWithinAt.prod {s : Set E} {f : E → F} {g : E → G} (hf : ContDiffWithinAt 𝕜 n f s x)
    (hg : ContDiffWithinAt 𝕜 n g s x) : ContDiffWithinAt 𝕜 n (fun x : E => (f x, g x)) s x := by
  intro m hm
  rcases hf m hm with ⟨u, hu, p, hp⟩
  rcases hg m hm with ⟨v, hv, q, hq⟩
  exact ⟨u ∩ v, Filter.inter_mem hu hv, _, (hp.mono (inter_subset_left u v)).Prod (hq.mono (inter_subset_right u v))⟩

/-- The cartesian product of `C^n` functions on domains is `C^n`. -/
theorem ContDiffOn.prod {s : Set E} {f : E → F} {g : E → G} (hf : ContDiffOn 𝕜 n f s) (hg : ContDiffOn 𝕜 n g s) :
    ContDiffOn 𝕜 n (fun x : E => (f x, g x)) s := fun x hx => (hf x hx).Prod (hg x hx)

/-- The cartesian product of `C^n` functions at a point is `C^n`. -/
theorem ContDiffAt.prod {f : E → F} {g : E → G} (hf : ContDiffAt 𝕜 n f x) (hg : ContDiffAt 𝕜 n g x) :
    ContDiffAt 𝕜 n (fun x : E => (f x, g x)) x :=
  cont_diff_within_at_univ.1 <| ContDiffWithinAt.prod (cont_diff_within_at_univ.2 hf) (cont_diff_within_at_univ.2 hg)

/-- The cartesian product of `C^n` functions is `C^n`.-/
theorem ContDiff.prod {f : E → F} {g : E → G} (hf : ContDiff 𝕜 n f) (hg : ContDiff 𝕜 n g) :
    ContDiff 𝕜 n fun x : E => (f x, g x) :=
  cont_diff_on_univ.1 <| ContDiffOn.prod (cont_diff_on_univ.2 hf) (cont_diff_on_univ.2 hg)

/-!
### Composition of `C^n` functions

We show that the composition of `C^n` functions is `C^n`. One way to prove it would be to write
the `n`-th derivative of the composition (this is Faà di Bruno's formula) and check its continuity,
but this is very painful. Instead, we go for a simple inductive proof. Assume it is done for `n`.
Then, to check it for `n+1`, one needs to check that the derivative of `g ∘ f` is `C^n`, i.e.,
that `Dg(f x) ⬝ Df(x)` is `C^n`. The term `Dg (f x)` is the composition of two `C^n` functions, so
it is `C^n` by the inductive assumption. The term `Df(x)` is also `C^n`. Then, the matrix
multiplication is the application of a bilinear map (which is `C^∞`, and therefore `C^n`) to
`x ↦ (Dg(f x), Df x)`. As the composition of two `C^n` maps, it is again `C^n`, and we are done.

There is a subtlety in this argument: we apply the inductive assumption to functions on other Banach
spaces. In maths, one would say: prove by induction over `n` that, for all `C^n` maps between all
pairs of Banach spaces, their composition is `C^n`. In Lean, this is fine as long as the spaces
stay in the same universe. This is not the case in the above argument: if `E` lives in universe `u`
and `F` lives in universe `v`, then linear maps from `E` to `F` (to which the derivative of `f`
belongs) is in universe `max u v`. If one could quantify over finitely many universes, the above
proof would work fine, but this is not the case. One could still write the proof considering spaces
in any universe in `u, v, w, max u v, max v w, max u v w`, but it would be extremely tedious and
lead to a lot of duplication. Instead, we formulate the above proof when all spaces live in the same
universe (where everything is fine), and then we deduce the general result by lifting all our spaces
to a common universe. We use the trick that any space `H` is isomorphic through a continuous linear
equiv to `continuous_multilinear_map (λ (i : fin 0), E × F × G) H` to change the universe level,
and then argue that composing with such a linear equiv does not change the fact of being `C^n`,
which we have already proved previously.
-/


/-- Auxiliary lemma proving that the composition of `C^n` functions on domains is `C^n` when all
spaces live in the same universe. Use instead `cont_diff_on.comp` which removes the universe
assumption (but is deduced from this one). -/
private theorem cont_diff_on.comp_same_univ {Eu : Type u} [NormedGroup Eu] [NormedSpace 𝕜 Eu] {Fu : Type u}
    [NormedGroup Fu] [NormedSpace 𝕜 Fu] {Gu : Type u} [NormedGroup Gu] [NormedSpace 𝕜 Gu] {s : Set Eu} {t : Set Fu}
    {g : Fu → Gu} {f : Eu → Fu} (hg : ContDiffOn 𝕜 n g t) (hf : ContDiffOn 𝕜 n f s) (st : s ⊆ f ⁻¹' t) :
    ContDiffOn 𝕜 n (g ∘ f) s := by
  induction' n using WithTop.nat_induction with n IH Itop generalizing Eu Fu Gu
  · rw [cont_diff_on_zero] at hf hg⊢
    exact ContinuousOn.comp hg hf st
    
  · rw [cont_diff_on_succ_iff_has_fderiv_within_at] at hg⊢
    intro x hx
    rcases(cont_diff_on_succ_iff_has_fderiv_within_at.1 hf) x hx with ⟨u, hu, f', hf', f'_diff⟩
    rcases hg (f x) (st hx) with ⟨v, hv, g', hg', g'_diff⟩
    rw [insert_eq_of_mem hx] at hu⊢
    have xu : x ∈ u := mem_of_mem_nhds_within hx hu
    let w := s ∩ (u ∩ f ⁻¹' v)
    have wv : w ⊆ f ⁻¹' v := fun y hy => hy.2.2
    have wu : w ⊆ u := fun y hy => hy.2.1
    have ws : w ⊆ s := fun y hy => hy.1
    refine' ⟨w, _, fun y => (g' (f y)).comp (f' y), _, _⟩
    show w ∈ 𝓝[s] x
    · apply Filter.inter_mem self_mem_nhds_within
      apply Filter.inter_mem hu
      apply ContinuousWithinAt.preimage_mem_nhds_within'
      · rw [← continuous_within_at_inter' hu]
        exact (hf' x xu).DifferentiableWithinAt.ContinuousWithinAt.mono (inter_subset_right _ _)
        
      · apply nhds_within_mono _ _ hv
        exact subset.trans (image_subset_iff.mpr st) (subset_insert (f x) t)
        
      
    show ∀, ∀ y ∈ w, ∀, HasFderivWithinAt (g ∘ f) ((g' (f y)).comp (f' y)) w y
    · rintro y ⟨ys, yu, yv⟩
      exact (hg' (f y) yv).comp y ((hf' y yu).mono wu) wv
      
    show ContDiffOn 𝕜 n (fun y => (g' (f y)).comp (f' y)) w
    · have A : ContDiffOn 𝕜 n (fun y => g' (f y)) w :=
        IH g'_diff ((hf.of_le (WithTop.coe_le_coe.2 (Nat.le_succₓ n))).mono ws) wv
      have B : ContDiffOn 𝕜 n f' w := f'_diff.mono wu
      have C : ContDiffOn 𝕜 n (fun y => (g' (f y), f' y)) w := A.prod B
      have D : ContDiffOn 𝕜 n (fun p : (Fu →L[𝕜] Gu) × (Eu →L[𝕜] Fu) => p.1.comp p.2) univ :=
        is_bounded_bilinear_map_comp.cont_diff.cont_diff_on
      exact IH D C (subset_univ _)
      
    
  · rw [cont_diff_on_top] at hf hg⊢
    exact fun n => Itop n (hg n) (hf n) st
    

/-- The composition of `C^n` functions on domains is `C^n`. -/
theorem ContDiffOn.comp {s : Set E} {t : Set F} {g : F → G} {f : E → F} (hg : ContDiffOn 𝕜 n g t)
    (hf : ContDiffOn 𝕜 n f s) (st : s ⊆ f ⁻¹' t) : ContDiffOn 𝕜 n (g ∘ f) s := by
  /- we lift all the spaces to a common universe, as we have already proved the result in this
    situation. For the lift, we use the trick that `H` is isomorphic through a
    continuous linear equiv to `continuous_multilinear_map 𝕜 (λ (i : fin 0), (E × F × G)) H`, and
    continuous linear equivs respect smoothness classes. -/
  let Eu := ContinuousMultilinearMap 𝕜 (fun i : Finₓ 0 => E × F × G) E
  let this : NormedGroup Eu := by
    infer_instance
  let this : NormedSpace 𝕜 Eu := by
    infer_instance
  let Fu := ContinuousMultilinearMap 𝕜 (fun i : Finₓ 0 => E × F × G) F
  let this : NormedGroup Fu := by
    infer_instance
  let this : NormedSpace 𝕜 Fu := by
    infer_instance
  let Gu := ContinuousMultilinearMap 𝕜 (fun i : Finₓ 0 => E × F × G) G
  let this : NormedGroup Gu := by
    infer_instance
  let this : NormedSpace 𝕜 Gu := by
    infer_instance
  -- declare the isomorphisms
  let isoE : Eu ≃L[𝕜] E := continuousMultilinearCurryFin0 𝕜 (E × F × G) E
  let isoF : Fu ≃L[𝕜] F := continuousMultilinearCurryFin0 𝕜 (E × F × G) F
  let isoG : Gu ≃L[𝕜] G := continuousMultilinearCurryFin0 𝕜 (E × F × G) G
  -- lift the functions to the new spaces, check smoothness there, and then go back.
  let fu : Eu → Fu := (isoF.symm ∘ f) ∘ isoE
  have fu_diff : ContDiffOn 𝕜 n fu (isoE ⁻¹' s) := by
    rwa [isoE.cont_diff_on_comp_iff, isoF.symm.comp_cont_diff_on_iff]
  let gu : Fu → Gu := (isoG.symm ∘ g) ∘ isoF
  have gu_diff : ContDiffOn 𝕜 n gu (isoF ⁻¹' t) := by
    rwa [isoF.cont_diff_on_comp_iff, isoG.symm.comp_cont_diff_on_iff]
  have main : ContDiffOn 𝕜 n (gu ∘ fu) (isoE ⁻¹' s) := by
    apply cont_diff_on.comp_same_univ gu_diff fu_diff
    intro y hy
    simp only [← fu, ← ContinuousLinearEquiv.coe_apply, ← Function.comp_app, ← mem_preimage]
    rw [isoF.apply_symm_apply (f (isoE y))]
    exact st hy
  have : gu ∘ fu = (isoG.symm ∘ g ∘ f) ∘ isoE := by
    ext y
    simp only [← Function.comp_applyₓ, ← gu, ← fu]
    rw [isoF.apply_symm_apply (f (isoE y))]
  rwa [this, isoE.cont_diff_on_comp_iff, isoG.symm.comp_cont_diff_on_iff] at main

/-- The composition of `C^n` functions on domains is `C^n`. -/
theorem ContDiffOn.comp' {s : Set E} {t : Set F} {g : F → G} {f : E → F} (hg : ContDiffOn 𝕜 n g t)
    (hf : ContDiffOn 𝕜 n f s) : ContDiffOn 𝕜 n (g ∘ f) (s ∩ f ⁻¹' t) :=
  hg.comp (hf.mono (inter_subset_left _ _)) (inter_subset_right _ _)

/-- The composition of a `C^n` function on a domain with a `C^n` function is `C^n`. -/
theorem ContDiff.comp_cont_diff_on {s : Set E} {g : F → G} {f : E → F} (hg : ContDiff 𝕜 n g) (hf : ContDiffOn 𝕜 n f s) :
    ContDiffOn 𝕜 n (g ∘ f) s :=
  (cont_diff_on_univ.2 hg).comp hf subset_preimage_univ

/-- The composition of `C^n` functions is `C^n`. -/
theorem ContDiff.comp {g : F → G} {f : E → F} (hg : ContDiff 𝕜 n g) (hf : ContDiff 𝕜 n f) : ContDiff 𝕜 n (g ∘ f) :=
  cont_diff_on_univ.1 <| ContDiffOn.comp (cont_diff_on_univ.2 hg) (cont_diff_on_univ.2 hf) (subset_univ _)

/-- The composition of `C^n` functions at points in domains is `C^n`. -/
theorem ContDiffWithinAt.comp {s : Set E} {t : Set F} {g : F → G} {f : E → F} (x : E)
    (hg : ContDiffWithinAt 𝕜 n g t (f x)) (hf : ContDiffWithinAt 𝕜 n f s x) (st : s ⊆ f ⁻¹' t) :
    ContDiffWithinAt 𝕜 n (g ∘ f) s x := by
  intro m hm
  rcases hg.cont_diff_on hm with ⟨u, u_nhd, ut, hu⟩
  rcases hf.cont_diff_on hm with ⟨v, v_nhd, vs, hv⟩
  have xmem : x ∈ f ⁻¹' u ∩ v :=
    ⟨(mem_of_mem_nhds_within (mem_insert (f x) _) u_nhd : _), mem_of_mem_nhds_within (mem_insert x s) v_nhd⟩
  have : f ⁻¹' u ∈ 𝓝[insert x s] x := by
    apply hf.continuous_within_at.insert_self.preimage_mem_nhds_within'
    apply nhds_within_mono _ _ u_nhd
    rw [image_insert_eq]
    exact insert_subset_insert (image_subset_iff.mpr st)
  have Z := (hu.comp (hv.mono (inter_subset_right (f ⁻¹' u) v)) (inter_subset_left _ _)).ContDiffWithinAt xmem m le_rfl
  have : 𝓝[f ⁻¹' u ∩ v] x = 𝓝[insert x s] x := by
    have A : f ⁻¹' u ∩ v = insert x s ∩ (f ⁻¹' u ∩ v) := by
      apply subset.antisymm _ (inter_subset_right _ _)
      rintro y ⟨hy1, hy2⟩
      simp [← hy1, ← hy2, ← vs hy2]
    rw [A, ← nhds_within_restrict'']
    exact Filter.inter_mem this v_nhd
  rwa [insert_eq_of_mem xmem, this] at Z

/-- The composition of `C^n` functions at points in domains is `C^n`. -/
theorem ContDiffWithinAt.comp' {s : Set E} {t : Set F} {g : F → G} {f : E → F} (x : E)
    (hg : ContDiffWithinAt 𝕜 n g t (f x)) (hf : ContDiffWithinAt 𝕜 n f s x) :
    ContDiffWithinAt 𝕜 n (g ∘ f) (s ∩ f ⁻¹' t) x :=
  hg.comp x (hf.mono (inter_subset_left _ _)) (inter_subset_right _ _)

theorem ContDiffAt.comp_cont_diff_within_at {n} (x : E) (hg : ContDiffAt 𝕜 n g (f x))
    (hf : ContDiffWithinAt 𝕜 n f s x) : ContDiffWithinAt 𝕜 n (g ∘ f) s x :=
  hg.comp x hf (maps_to_univ _ _)

/-- The composition of `C^n` functions at points is `C^n`. -/
theorem ContDiffAt.comp (x : E) (hg : ContDiffAt 𝕜 n g (f x)) (hf : ContDiffAt 𝕜 n f x) : ContDiffAt 𝕜 n (g ∘ f) x :=
  hg.comp x hf subset_preimage_univ

theorem ContDiff.comp_cont_diff_within_at {g : F → G} {f : E → F} (h : ContDiff 𝕜 n g)
    (hf : ContDiffWithinAt 𝕜 n f t x) : ContDiffWithinAt 𝕜 n (g ∘ f) t x := by
  have : ContDiffWithinAt 𝕜 n g univ (f x) := h.cont_diff_at.cont_diff_within_at
  exact this.comp x hf (subset_univ _)

theorem ContDiff.comp_cont_diff_at {g : F → G} {f : E → F} (x : E) (hg : ContDiff 𝕜 n g) (hf : ContDiffAt 𝕜 n f x) :
    ContDiffAt 𝕜 n (g ∘ f) x :=
  hg.comp_cont_diff_within_at hf

/-!
### Smoothness of projections
-/


/-- The first projection in a product is `C^∞`. -/
theorem cont_diff_fst : ContDiff 𝕜 n (Prod.fst : E × F → E) :=
  IsBoundedLinearMap.cont_diff IsBoundedLinearMap.fst

/-- Postcomposing `f` with `prod.fst` is `C^n` -/
theorem ContDiff.fst {f : E → F × G} (hf : ContDiff 𝕜 n f) : ContDiff 𝕜 n fun x => (f x).1 :=
  cont_diff_fst.comp hf

/-- Precomposing `f` with `prod.fst` is `C^n` -/
theorem ContDiff.fst' {f : E → G} (hf : ContDiff 𝕜 n f) : ContDiff 𝕜 n fun x : E × F => f x.1 :=
  hf.comp cont_diff_fst

/-- The first projection on a domain in a product is `C^∞`. -/
theorem cont_diff_on_fst {s : Set (E × F)} : ContDiffOn 𝕜 n (Prod.fst : E × F → E) s :=
  ContDiff.cont_diff_on cont_diff_fst

theorem ContDiffOn.fst {f : E → F × G} {s : Set E} (hf : ContDiffOn 𝕜 n f s) : ContDiffOn 𝕜 n (fun x => (f x).1) s :=
  cont_diff_fst.comp_cont_diff_on hf

/-- The first projection at a point in a product is `C^∞`. -/
theorem cont_diff_at_fst {p : E × F} : ContDiffAt 𝕜 n (Prod.fst : E × F → E) p :=
  cont_diff_fst.ContDiffAt

/-- Postcomposing `f` with `prod.fst` is `C^n` at `(x, y)` -/
theorem ContDiffAt.fst {f : E → F × G} {x : E} (hf : ContDiffAt 𝕜 n f x) : ContDiffAt 𝕜 n (fun x => (f x).1) x :=
  cont_diff_at_fst.comp x hf

/-- Precomposing `f` with `prod.fst` is `C^n` at `(x, y)` -/
theorem ContDiffAt.fst' {f : E → G} {x : E} {y : F} (hf : ContDiffAt 𝕜 n f x) :
    ContDiffAt 𝕜 n (fun x : E × F => f x.1) (x, y) :=
  ContDiffAt.comp (x, y) hf cont_diff_at_fst

/-- Precomposing `f` with `prod.fst` is `C^n` at `x : E × F` -/
theorem ContDiffAt.fst'' {f : E → G} {x : E × F} (hf : ContDiffAt 𝕜 n f x.1) :
    ContDiffAt 𝕜 n (fun x : E × F => f x.1) x :=
  hf.comp x cont_diff_at_fst

/-- The first projection within a domain at a point in a product is `C^∞`. -/
theorem cont_diff_within_at_fst {s : Set (E × F)} {p : E × F} : ContDiffWithinAt 𝕜 n (Prod.fst : E × F → E) s p :=
  cont_diff_fst.ContDiffWithinAt

/-- The second projection in a product is `C^∞`. -/
theorem cont_diff_snd : ContDiff 𝕜 n (Prod.snd : E × F → F) :=
  IsBoundedLinearMap.cont_diff IsBoundedLinearMap.snd

/-- Postcomposing `f` with `prod.snd` is `C^n` -/
theorem ContDiff.snd {f : E → F × G} (hf : ContDiff 𝕜 n f) : ContDiff 𝕜 n fun x => (f x).2 :=
  cont_diff_snd.comp hf

/-- Precomposing `f` with `prod.snd` is `C^n` -/
theorem ContDiff.snd' {f : F → G} (hf : ContDiff 𝕜 n f) : ContDiff 𝕜 n fun x : E × F => f x.2 :=
  hf.comp cont_diff_snd

/-- The second projection on a domain in a product is `C^∞`. -/
theorem cont_diff_on_snd {s : Set (E × F)} : ContDiffOn 𝕜 n (Prod.snd : E × F → F) s :=
  ContDiff.cont_diff_on cont_diff_snd

theorem ContDiffOn.snd {f : E → F × G} {s : Set E} (hf : ContDiffOn 𝕜 n f s) : ContDiffOn 𝕜 n (fun x => (f x).2) s :=
  cont_diff_snd.comp_cont_diff_on hf

/-- The second projection at a point in a product is `C^∞`. -/
theorem cont_diff_at_snd {p : E × F} : ContDiffAt 𝕜 n (Prod.snd : E × F → F) p :=
  cont_diff_snd.ContDiffAt

/-- Postcomposing `f` with `prod.snd` is `C^n` at `x` -/
theorem ContDiffAt.snd {f : E → F × G} {x : E} (hf : ContDiffAt 𝕜 n f x) : ContDiffAt 𝕜 n (fun x => (f x).2) x :=
  cont_diff_at_snd.comp x hf

/-- Precomposing `f` with `prod.snd` is `C^n` at `(x, y)` -/
theorem ContDiffAt.snd' {f : F → G} {x : E} {y : F} (hf : ContDiffAt 𝕜 n f y) :
    ContDiffAt 𝕜 n (fun x : E × F => f x.2) (x, y) :=
  ContDiffAt.comp (x, y) hf cont_diff_at_snd

/-- Precomposing `f` with `prod.snd` is `C^n` at `x : E × F` -/
theorem ContDiffAt.snd'' {f : F → G} {x : E × F} (hf : ContDiffAt 𝕜 n f x.2) :
    ContDiffAt 𝕜 n (fun x : E × F => f x.2) x :=
  hf.comp x cont_diff_at_snd

/-- The second projection within a domain at a point in a product is `C^∞`. -/
theorem cont_diff_within_at_snd {s : Set (E × F)} {p : E × F} : ContDiffWithinAt 𝕜 n (Prod.snd : E × F → F) s p :=
  cont_diff_snd.ContDiffWithinAt

section NAry

variable {E₁ E₂ E₃ E₄ : Type _}

variable [NormedGroup E₁] [NormedGroup E₂] [NormedGroup E₃] [NormedGroup E₄]

variable [NormedSpace 𝕜 E₁] [NormedSpace 𝕜 E₂] [NormedSpace 𝕜 E₃] [NormedSpace 𝕜 E₄]

theorem ContDiff.comp₂ {g : E₁ × E₂ → G} {f₁ : F → E₁} {f₂ : F → E₂} (hg : ContDiff 𝕜 n g) (hf₁ : ContDiff 𝕜 n f₁)
    (hf₂ : ContDiff 𝕜 n f₂) : ContDiff 𝕜 n fun x => g (f₁ x, f₂ x) :=
  hg.comp <| hf₁.Prod hf₂

theorem ContDiff.comp₃ {g : E₁ × E₂ × E₃ → G} {f₁ : F → E₁} {f₂ : F → E₂} {f₃ : F → E₃} (hg : ContDiff 𝕜 n g)
    (hf₁ : ContDiff 𝕜 n f₁) (hf₂ : ContDiff 𝕜 n f₂) (hf₃ : ContDiff 𝕜 n f₃) :
    ContDiff 𝕜 n fun x => g (f₁ x, f₂ x, f₃ x) :=
  hg.comp₂ hf₁ <| hf₂.Prod hf₃

theorem ContDiff.comp_cont_diff_on₂ {g : E₁ × E₂ → G} {f₁ : F → E₁} {f₂ : F → E₂} {s : Set F} (hg : ContDiff 𝕜 n g)
    (hf₁ : ContDiffOn 𝕜 n f₁ s) (hf₂ : ContDiffOn 𝕜 n f₂ s) : ContDiffOn 𝕜 n (fun x => g (f₁ x, f₂ x)) s :=
  hg.comp_cont_diff_on <| hf₁.Prod hf₂

theorem ContDiff.comp_cont_diff_on₃ {g : E₁ × E₂ × E₃ → G} {f₁ : F → E₁} {f₂ : F → E₂} {f₃ : F → E₃} {s : Set F}
    (hg : ContDiff 𝕜 n g) (hf₁ : ContDiffOn 𝕜 n f₁ s) (hf₂ : ContDiffOn 𝕜 n f₂ s) (hf₃ : ContDiffOn 𝕜 n f₃ s) :
    ContDiffOn 𝕜 n (fun x => g (f₁ x, f₂ x, f₃ x)) s :=
  hg.comp_cont_diff_on₂ hf₁ <| hf₂.Prod hf₃

end NAry

/-- The natural equivalence `(E × F) × G ≃ E × (F × G)` is smooth.

Warning: if you think you need this lemma, it is likely that you can simplify your proof by
reformulating the lemma that you're applying next using the tips in
Note [continuity lemma statement]
-/
theorem cont_diff_prod_assoc : ContDiff 𝕜 ⊤ <| Equivₓ.prodAssoc E F G :=
  (LinearIsometryEquiv.prodAssoc 𝕜 E F G).ContDiff

/-- The natural equivalence `E × (F × G) ≃ (E × F) × G` is smooth.

Warning: see remarks attached to `cont_diff_prod_assoc`
-/
theorem cont_diff_prod_assoc_symm : ContDiff 𝕜 ⊤ <| (Equivₓ.prodAssoc E F G).symm :=
  (LinearIsometryEquiv.prodAssoc 𝕜 E F G).symm.ContDiff

/-! ### Bundled derivatives -/


/-- The bundled derivative of a `C^{n+1}` function is `C^n`. -/
theorem cont_diff_on_fderiv_within_apply {m n : WithTop ℕ} {s : Set E} {f : E → F} (hf : ContDiffOn 𝕜 n f s)
    (hs : UniqueDiffOn 𝕜 s) (hmn : m + 1 ≤ n) :
    ContDiffOn 𝕜 m (fun p : E × E => (fderivWithin 𝕜 f s p.1 : E →L[𝕜] F) p.2) (s ×ˢ (Univ : Set E)) := by
  have A : ContDiff 𝕜 m fun p : (E →L[𝕜] F) × E => p.1 p.2 := by
    apply IsBoundedBilinearMap.cont_diff
    exact is_bounded_bilinear_map_apply
  have B : ContDiffOn 𝕜 m (fun p : E × E => (fderivWithin 𝕜 f s p.fst, p.snd)) (s ×ˢ univ) := by
    apply ContDiffOn.prod _ _
    · have I : ContDiffOn 𝕜 m (fun x : E => fderivWithin 𝕜 f s x) s := hf.fderiv_within hs hmn
      have J : ContDiffOn 𝕜 m (fun x : E × E => x.1) (s ×ˢ univ) := cont_diff_fst.cont_diff_on
      exact ContDiffOn.comp I J (prod_subset_preimage_fst _ _)
      
    · apply ContDiff.cont_diff_on _
      apply is_bounded_linear_map.snd.cont_diff
      
  exact A.comp_cont_diff_on B

/-- The bundled derivative of a `C^{n+1}` function is `C^n`. -/
theorem ContDiff.cont_diff_fderiv_apply {f : E → F} (hf : ContDiff 𝕜 n f) (hmn : m + 1 ≤ n) :
    ContDiff 𝕜 m fun p : E × E => (fderiv 𝕜 f p.1 : E →L[𝕜] F) p.2 := by
  rw [← cont_diff_on_univ] at hf⊢
  rw [← fderiv_within_univ, ← univ_prod_univ]
  exact cont_diff_on_fderiv_within_apply hf unique_diff_on_univ hmn

/-!
### Smoothness of functions `f : E → Π i, F' i`
-/


section Pi

variable {ι ι' : Type _} [Fintype ι] [Fintype ι'] {F' : ι → Type _} [∀ i, NormedGroup (F' i)]
  [∀ i, NormedSpace 𝕜 (F' i)] {φ : ∀ i, E → F' i} {p' : ∀ i, E → FormalMultilinearSeries 𝕜 E (F' i)} {Φ : E → ∀ i, F' i}
  {P' : E → FormalMultilinearSeries 𝕜 E (∀ i, F' i)}

theorem has_ftaylor_series_up_to_on_pi :
    HasFtaylorSeriesUpToOn n (fun x i => φ i x) (fun x m => ContinuousMultilinearMap.pi fun i => p' i x m) s ↔
      ∀ i, HasFtaylorSeriesUpToOn n (φ i) (p' i) s :=
  by
  set pr := @ContinuousLinearMap.proj 𝕜 _ ι F' _ _ _
  let this : ∀ (m : ℕ) (i : ι), NormedSpace 𝕜 (E[×m]→L[𝕜] F' i) := fun m i => inferInstance
  set L : ∀ m : ℕ, (∀ i, E[×m]→L[𝕜] F' i) ≃ₗᵢ[𝕜] E[×m]→L[𝕜] ∀ i, F' i := fun m => ContinuousMultilinearMap.piₗᵢ _ _
  refine' ⟨fun h i => _, fun h => ⟨fun x hx => _, _, _⟩⟩
  · convert h.continuous_linear_map_comp (pr i)
    ext
    rfl
    
  · ext1 i
    exact (h i).zero_eq x hx
    
  · intro m hm x hx
    have := has_fderiv_within_at_pi.2 fun i => (h i).fderivWithin m hm x hx
    convert (L m).HasFderivAt.comp_has_fderiv_within_at x this
    
  · intro m hm
    have := continuous_on_pi.2 fun i => (h i).cont m hm
    convert (L m).Continuous.comp_continuous_on this
    

@[simp]
theorem has_ftaylor_series_up_to_on_pi' :
    HasFtaylorSeriesUpToOn n Φ P' s ↔
      ∀ i,
        HasFtaylorSeriesUpToOn n (fun x => Φ x i)
          (fun x m => (@ContinuousLinearMap.proj 𝕜 _ ι F' _ _ _ i).compContinuousMultilinearMap (P' x m)) s :=
  by
  convert has_ftaylor_series_up_to_on_pi
  ext
  rfl

theorem cont_diff_within_at_pi : ContDiffWithinAt 𝕜 n Φ s x ↔ ∀ i, ContDiffWithinAt 𝕜 n (fun x => Φ x i) s x := by
  set pr := @ContinuousLinearMap.proj 𝕜 _ ι F' _ _ _
  refine' ⟨fun h i => h.continuous_linear_map_comp (pr i), fun h m hm => _⟩
  choose u hux p hp using fun i => h i m hm
  exact ⟨⋂ i, u i, Filter.Inter_mem.2 hux, _, has_ftaylor_series_up_to_on_pi.2 fun i => (hp i).mono <| Inter_subset _ _⟩

theorem cont_diff_on_pi : ContDiffOn 𝕜 n Φ s ↔ ∀ i, ContDiffOn 𝕜 n (fun x => Φ x i) s :=
  ⟨fun h i x hx => cont_diff_within_at_pi.1 (h x hx) _, fun h x hx => cont_diff_within_at_pi.2 fun i => h i x hx⟩

theorem cont_diff_at_pi : ContDiffAt 𝕜 n Φ x ↔ ∀ i, ContDiffAt 𝕜 n (fun x => Φ x i) x :=
  cont_diff_within_at_pi

theorem cont_diff_pi : ContDiff 𝕜 n Φ ↔ ∀ i, ContDiff 𝕜 n fun x => Φ x i := by
  simp only [cont_diff_on_univ, ← cont_diff_on_pi]

variable (𝕜 E)

theorem cont_diff_apply (i : ι) : ContDiff 𝕜 n fun f : ι → E => f i :=
  cont_diff_pi.mp cont_diff_id i

theorem cont_diff_apply_apply (i : ι) (j : ι') : ContDiff 𝕜 n fun f : ι → ι' → E => f i j :=
  cont_diff_pi.mp (cont_diff_apply 𝕜 (ι' → E) i) j

variable {𝕜 E}

end Pi

/-! ### Sum of two functions -/


-- The sum is smooth.
theorem cont_diff_add : ContDiff 𝕜 n fun p : F × F => p.1 + p.2 :=
  (IsBoundedLinearMap.fst.add IsBoundedLinearMap.snd).ContDiff

/-- The sum of two `C^n` functions within a set at a point is `C^n` within this set
at this point. -/
theorem ContDiffWithinAt.add {s : Set E} {f g : E → F} (hf : ContDiffWithinAt 𝕜 n f s x)
    (hg : ContDiffWithinAt 𝕜 n g s x) : ContDiffWithinAt 𝕜 n (fun x => f x + g x) s x :=
  cont_diff_add.ContDiffWithinAt.comp x (hf.Prod hg) subset_preimage_univ

/-- The sum of two `C^n` functions at a point is `C^n` at this point. -/
theorem ContDiffAt.add {f g : E → F} (hf : ContDiffAt 𝕜 n f x) (hg : ContDiffAt 𝕜 n g x) :
    ContDiffAt 𝕜 n (fun x => f x + g x) x := by
  rw [← cont_diff_within_at_univ] at * <;> exact hf.add hg

/-- The sum of two `C^n`functions is `C^n`. -/
theorem ContDiff.add {f g : E → F} (hf : ContDiff 𝕜 n f) (hg : ContDiff 𝕜 n g) : ContDiff 𝕜 n fun x => f x + g x :=
  cont_diff_add.comp (hf.Prod hg)

/-- The sum of two `C^n` functions on a domain is `C^n`. -/
theorem ContDiffOn.add {s : Set E} {f g : E → F} (hf : ContDiffOn 𝕜 n f s) (hg : ContDiffOn 𝕜 n g s) :
    ContDiffOn 𝕜 n (fun x => f x + g x) s := fun x hx => (hf x hx).add (hg x hx)

/-! ### Negative -/


-- The negative is smooth.
theorem cont_diff_neg : ContDiff 𝕜 n fun p : F => -p :=
  IsBoundedLinearMap.id.neg.ContDiff

/-- The negative of a `C^n` function within a domain at a point is `C^n` within this domain at
this point. -/
theorem ContDiffWithinAt.neg {s : Set E} {f : E → F} (hf : ContDiffWithinAt 𝕜 n f s x) :
    ContDiffWithinAt 𝕜 n (fun x => -f x) s x :=
  cont_diff_neg.ContDiffWithinAt.comp x hf subset_preimage_univ

/-- The negative of a `C^n` function at a point is `C^n` at this point. -/
theorem ContDiffAt.neg {f : E → F} (hf : ContDiffAt 𝕜 n f x) : ContDiffAt 𝕜 n (fun x => -f x) x := by
  rw [← cont_diff_within_at_univ] at * <;> exact hf.neg

/-- The negative of a `C^n`function is `C^n`. -/
theorem ContDiff.neg {f : E → F} (hf : ContDiff 𝕜 n f) : ContDiff 𝕜 n fun x => -f x :=
  cont_diff_neg.comp hf

/-- The negative of a `C^n` function on a domain is `C^n`. -/
theorem ContDiffOn.neg {s : Set E} {f : E → F} (hf : ContDiffOn 𝕜 n f s) : ContDiffOn 𝕜 n (fun x => -f x) s :=
  fun x hx => (hf x hx).neg

/-! ### Subtraction -/


/-- The difference of two `C^n` functions within a set at a point is `C^n` within this set
at this point. -/
theorem ContDiffWithinAt.sub {s : Set E} {f g : E → F} (hf : ContDiffWithinAt 𝕜 n f s x)
    (hg : ContDiffWithinAt 𝕜 n g s x) : ContDiffWithinAt 𝕜 n (fun x => f x - g x) s x := by
  simpa only [← sub_eq_add_neg] using hf.add hg.neg

/-- The difference of two `C^n` functions at a point is `C^n` at this point. -/
theorem ContDiffAt.sub {f g : E → F} (hf : ContDiffAt 𝕜 n f x) (hg : ContDiffAt 𝕜 n g x) :
    ContDiffAt 𝕜 n (fun x => f x - g x) x := by
  simpa only [← sub_eq_add_neg] using hf.add hg.neg

/-- The difference of two `C^n` functions on a domain is `C^n`. -/
theorem ContDiffOn.sub {s : Set E} {f g : E → F} (hf : ContDiffOn 𝕜 n f s) (hg : ContDiffOn 𝕜 n g s) :
    ContDiffOn 𝕜 n (fun x => f x - g x) s := by
  simpa only [← sub_eq_add_neg] using hf.add hg.neg

/-- The difference of two `C^n` functions is `C^n`. -/
theorem ContDiff.sub {f g : E → F} (hf : ContDiff 𝕜 n f) (hg : ContDiff 𝕜 n g) : ContDiff 𝕜 n fun x => f x - g x := by
  simpa only [← sub_eq_add_neg] using hf.add hg.neg

/-! ### Sum of finitely many functions -/


theorem ContDiffWithinAt.sum {ι : Type _} {f : ι → E → F} {s : Finset ι} {t : Set E} {x : E}
    (h : ∀, ∀ i ∈ s, ∀, ContDiffWithinAt 𝕜 n (fun x => f i x) t x) :
    ContDiffWithinAt 𝕜 n (fun x => ∑ i in s, f i x) t x := by
  classical
  induction' s using Finset.induction_on with i s is IH
  · simp [← cont_diff_within_at_const]
    
  · simp only [← is, ← Finset.sum_insert, ← not_false_iff]
    exact (h _ (Finset.mem_insert_self i s)).add (IH fun j hj => h _ (Finset.mem_insert_of_mem hj))
    

theorem ContDiffAt.sum {ι : Type _} {f : ι → E → F} {s : Finset ι} {x : E}
    (h : ∀, ∀ i ∈ s, ∀, ContDiffAt 𝕜 n (fun x => f i x) x) : ContDiffAt 𝕜 n (fun x => ∑ i in s, f i x) x := by
  rw [← cont_diff_within_at_univ] at * <;> exact ContDiffWithinAt.sum h

theorem ContDiffOn.sum {ι : Type _} {f : ι → E → F} {s : Finset ι} {t : Set E}
    (h : ∀, ∀ i ∈ s, ∀, ContDiffOn 𝕜 n (fun x => f i x) t) : ContDiffOn 𝕜 n (fun x => ∑ i in s, f i x) t := fun x hx =>
  ContDiffWithinAt.sum fun i hi => h i hi x hx

theorem ContDiff.sum {ι : Type _} {f : ι → E → F} {s : Finset ι} (h : ∀, ∀ i ∈ s, ∀, ContDiff 𝕜 n fun x => f i x) :
    ContDiff 𝕜 n fun x => ∑ i in s, f i x := by
  simp [cont_diff_on_univ] at * <;> exact ContDiffOn.sum h

/-! ### Product of two functions -/


-- The product is smooth.
theorem cont_diff_mul : ContDiff 𝕜 n fun p : 𝕜 × 𝕜 => p.1 * p.2 :=
  is_bounded_bilinear_map_mul.ContDiff

/-- The product of two `C^n` functions within a set at a point is `C^n` within this set
at this point. -/
theorem ContDiffWithinAt.mul {s : Set E} {f g : E → 𝕜} (hf : ContDiffWithinAt 𝕜 n f s x)
    (hg : ContDiffWithinAt 𝕜 n g s x) : ContDiffWithinAt 𝕜 n (fun x => f x * g x) s x :=
  cont_diff_mul.ContDiffWithinAt.comp x (hf.Prod hg) subset_preimage_univ

/-- The product of two `C^n` functions at a point is `C^n` at this point. -/
theorem ContDiffAt.mul {f g : E → 𝕜} (hf : ContDiffAt 𝕜 n f x) (hg : ContDiffAt 𝕜 n g x) :
    ContDiffAt 𝕜 n (fun x => f x * g x) x := by
  rw [← cont_diff_within_at_univ] at * <;> exact hf.mul hg

/-- The product of two `C^n` functions on a domain is `C^n`. -/
theorem ContDiffOn.mul {s : Set E} {f g : E → 𝕜} (hf : ContDiffOn 𝕜 n f s) (hg : ContDiffOn 𝕜 n g s) :
    ContDiffOn 𝕜 n (fun x => f x * g x) s := fun x hx => (hf x hx).mul (hg x hx)

/-- The product of two `C^n`functions is `C^n`. -/
theorem ContDiff.mul {f g : E → 𝕜} (hf : ContDiff 𝕜 n f) (hg : ContDiff 𝕜 n g) : ContDiff 𝕜 n fun x => f x * g x :=
  cont_diff_mul.comp (hf.Prod hg)

theorem ContDiffWithinAt.div_const {f : E → 𝕜} {n} {c : 𝕜} (hf : ContDiffWithinAt 𝕜 n f s x) :
    ContDiffWithinAt 𝕜 n (fun x => f x / c) s x := by
  simpa only [← div_eq_mul_inv] using hf.mul cont_diff_within_at_const

theorem ContDiffAt.div_const {f : E → 𝕜} {n} {c : 𝕜} (hf : ContDiffAt 𝕜 n f x) : ContDiffAt 𝕜 n (fun x => f x / c) x :=
  by
  simpa only [← div_eq_mul_inv] using hf.mul cont_diff_at_const

theorem ContDiffOn.div_const {f : E → 𝕜} {n} {c : 𝕜} (hf : ContDiffOn 𝕜 n f s) : ContDiffOn 𝕜 n (fun x => f x / c) s :=
  by
  simpa only [← div_eq_mul_inv] using hf.mul cont_diff_on_const

theorem ContDiff.div_const {f : E → 𝕜} {n} {c : 𝕜} (hf : ContDiff 𝕜 n f) : ContDiff 𝕜 n fun x => f x / c := by
  simpa only [← div_eq_mul_inv] using hf.mul cont_diff_const

theorem ContDiff.pow {f : E → 𝕜} (hf : ContDiff 𝕜 n f) : ∀ m : ℕ, ContDiff 𝕜 n fun x => f x ^ m
  | 0 => by
    simpa using cont_diff_const
  | m + 1 => by
    simpa [← pow_succₓ] using hf.mul (ContDiff.pow m)

theorem ContDiffAt.pow {f : E → 𝕜} (hf : ContDiffAt 𝕜 n f x) (m : ℕ) : ContDiffAt 𝕜 n (fun y => f y ^ m) x :=
  (cont_diff_id.pow m).ContDiffAt.comp x hf

theorem ContDiffWithinAt.pow {f : E → 𝕜} (hf : ContDiffWithinAt 𝕜 n f s x) (m : ℕ) :
    ContDiffWithinAt 𝕜 n (fun y => f y ^ m) s x :=
  (cont_diff_id.pow m).ContDiffAt.comp_cont_diff_within_at x hf

theorem ContDiffOn.pow {f : E → 𝕜} (hf : ContDiffOn 𝕜 n f s) (m : ℕ) : ContDiffOn 𝕜 n (fun y => f y ^ m) s :=
  fun y hy => (hf y hy).pow m

/-! ### Scalar multiplication -/


-- The scalar multiplication is smooth.
theorem cont_diff_smul : ContDiff 𝕜 n fun p : 𝕜 × F => p.1 • p.2 :=
  is_bounded_bilinear_map_smul.ContDiff

/-- The scalar multiplication of two `C^n` functions within a set at a point is `C^n` within this
set at this point. -/
theorem ContDiffWithinAt.smul {s : Set E} {f : E → 𝕜} {g : E → F} (hf : ContDiffWithinAt 𝕜 n f s x)
    (hg : ContDiffWithinAt 𝕜 n g s x) : ContDiffWithinAt 𝕜 n (fun x => f x • g x) s x :=
  cont_diff_smul.ContDiffWithinAt.comp x (hf.Prod hg) subset_preimage_univ

/-- The scalar multiplication of two `C^n` functions at a point is `C^n` at this point. -/
theorem ContDiffAt.smul {f : E → 𝕜} {g : E → F} (hf : ContDiffAt 𝕜 n f x) (hg : ContDiffAt 𝕜 n g x) :
    ContDiffAt 𝕜 n (fun x => f x • g x) x := by
  rw [← cont_diff_within_at_univ] at * <;> exact hf.smul hg

/-- The scalar multiplication of two `C^n` functions is `C^n`. -/
theorem ContDiff.smul {f : E → 𝕜} {g : E → F} (hf : ContDiff 𝕜 n f) (hg : ContDiff 𝕜 n g) :
    ContDiff 𝕜 n fun x => f x • g x :=
  cont_diff_smul.comp (hf.Prod hg)

/-- The scalar multiplication of two `C^n` functions on a domain is `C^n`. -/
theorem ContDiffOn.smul {s : Set E} {f : E → 𝕜} {g : E → F} (hf : ContDiffOn 𝕜 n f s) (hg : ContDiffOn 𝕜 n g s) :
    ContDiffOn 𝕜 n (fun x => f x • g x) s := fun x hx => (hf x hx).smul (hg x hx)

/-! ### Cartesian product of two functions -/


section prod_map

variable {E' : Type _} [NormedGroup E'] [NormedSpace 𝕜 E']

variable {F' : Type _} [NormedGroup F'] [NormedSpace 𝕜 F']

/-- The product map of two `C^n` functions within a set at a point is `C^n`
within the product set at the product point. -/
theorem ContDiffWithinAt.prod_map' {s : Set E} {t : Set E'} {f : E → F} {g : E' → F'} {p : E × E'}
    (hf : ContDiffWithinAt 𝕜 n f s p.1) (hg : ContDiffWithinAt 𝕜 n g t p.2) :
    ContDiffWithinAt 𝕜 n (Prod.map f g) (s ×ˢ t) p :=
  (hf.comp p cont_diff_within_at_fst (prod_subset_preimage_fst _ _)).Prod
    (hg.comp p cont_diff_within_at_snd (prod_subset_preimage_snd _ _))

theorem ContDiffWithinAt.prod_map {s : Set E} {t : Set E'} {f : E → F} {g : E' → F'} {x : E} {y : E'}
    (hf : ContDiffWithinAt 𝕜 n f s x) (hg : ContDiffWithinAt 𝕜 n g t y) :
    ContDiffWithinAt 𝕜 n (Prod.map f g) (s ×ˢ t) (x, y) :=
  ContDiffWithinAt.prod_map' hf hg

/-- The product map of two `C^n` functions on a set is `C^n` on the product set. -/
theorem ContDiffOn.prod_map {E' : Type _} [NormedGroup E'] [NormedSpace 𝕜 E'] {F' : Type _} [NormedGroup F']
    [NormedSpace 𝕜 F'] {s : Set E} {t : Set E'} {f : E → F} {g : E' → F'} (hf : ContDiffOn 𝕜 n f s)
    (hg : ContDiffOn 𝕜 n g t) : ContDiffOn 𝕜 n (Prod.map f g) (s ×ˢ t) :=
  (hf.comp cont_diff_on_fst (prod_subset_preimage_fst _ _)).Prod
    (hg.comp cont_diff_on_snd (prod_subset_preimage_snd _ _))

/-- The product map of two `C^n` functions within a set at a point is `C^n`
within the product set at the product point. -/
theorem ContDiffAt.prod_map {f : E → F} {g : E' → F'} {x : E} {y : E'} (hf : ContDiffAt 𝕜 n f x)
    (hg : ContDiffAt 𝕜 n g y) : ContDiffAt 𝕜 n (Prod.map f g) (x, y) := by
  rw [ContDiffAt] at *
  convert hf.prod_map hg
  simp only [← univ_prod_univ]

/-- The product map of two `C^n` functions within a set at a point is `C^n`
within the product set at the product point. -/
theorem ContDiffAt.prod_map' {f : E → F} {g : E' → F'} {p : E × E'} (hf : ContDiffAt 𝕜 n f p.1)
    (hg : ContDiffAt 𝕜 n g p.2) : ContDiffAt 𝕜 n (Prod.map f g) p := by
  rcases p with ⟨⟩
  exact ContDiffAt.prod_map hf hg

/-- The product map of two `C^n` functions is `C^n`. -/
theorem ContDiff.prod_map {f : E → F} {g : E' → F'} (hf : ContDiff 𝕜 n f) (hg : ContDiff 𝕜 n g) :
    ContDiff 𝕜 n (Prod.map f g) := by
  rw [cont_diff_iff_cont_diff_at] at *
  exact fun ⟨x, y⟩ => (hf x).prod_map (hg y)

theorem cont_diff_prod_mk_left (f₀ : F) : ContDiff 𝕜 n fun e : E => (e, f₀) :=
  cont_diff_id.Prod cont_diff_const

theorem cont_diff_prod_mk_right (e₀ : E) : ContDiff 𝕜 n fun f : F => (e₀, f) :=
  cont_diff_const.Prod cont_diff_id

end prod_map

theorem ContDiff.clm_comp {g : X → F →L[𝕜] G} {f : X → E →L[𝕜] F} (hg : ContDiff 𝕜 n g) (hf : ContDiff 𝕜 n f) :
    ContDiff 𝕜 n fun x => (g x).comp (f x) :=
  is_bounded_bilinear_map_comp.ContDiff.comp₂ hg hf

theorem ContDiffOn.clm_comp {g : X → F →L[𝕜] G} {f : X → E →L[𝕜] F} {s : Set X} (hg : ContDiffOn 𝕜 n g s)
    (hf : ContDiffOn 𝕜 n f s) : ContDiffOn 𝕜 n (fun x => (g x).comp (f x)) s :=
  is_bounded_bilinear_map_comp.ContDiff.comp_cont_diff_on₂ hg hf

/-! ### Inversion in a complete normed algebra -/


section AlgebraInverse

variable (𝕜) {R : Type _} [NormedRing R] [NormedAlgebra 𝕜 R]

open NormedRing ContinuousLinearMap Ringₓ

/-- In a complete normed algebra, the operation of inversion is `C^n`, for all `n`, at each
invertible element.  The proof is by induction, bootstrapping using an identity expressing the
derivative of inversion as a bilinear map of inversion itself. -/
theorem cont_diff_at_ring_inverse [CompleteSpace R] (x : Rˣ) : ContDiffAt 𝕜 n Ring.inverse (x : R) := by
  induction' n using WithTop.nat_induction with n IH Itop
  · intro m hm
    refine' ⟨{ y : R | IsUnit y }, _, _⟩
    · simp [← nhds_within_univ]
      exact x.nhds
      
    · use ftaylorSeriesWithin 𝕜 inverse univ
      rw [le_antisymmₓ hm bot_le, has_ftaylor_series_up_to_on_zero_iff]
      constructor
      · rintro _ ⟨x', rfl⟩
        exact (inverse_continuous_at x').ContinuousWithinAt
        
      · simp [← ftaylorSeriesWithin]
        
      
    
  · apply cont_diff_at_succ_iff_has_fderiv_at.mpr
    refine' ⟨fun x : R => -lmul_left_right 𝕜 R (inverse x) (inverse x), _, _⟩
    · refine' ⟨{ y : R | IsUnit y }, x.nhds, _⟩
      rintro _ ⟨y, rfl⟩
      rw [inverse_unit]
      exact has_fderiv_at_ring_inverse y
      
    · convert (lmul_left_right_is_bounded_bilinear 𝕜 R).ContDiff.neg.comp_cont_diff_at (x : R) (IH.prod IH)
      
    
  · exact cont_diff_at_top.mpr Itop
    

variable (𝕜) {𝕜' : Type _} [NormedField 𝕜'] [NormedAlgebra 𝕜 𝕜'] [CompleteSpace 𝕜']

theorem cont_diff_at_inv {x : 𝕜'} (hx : x ≠ 0) {n} : ContDiffAt 𝕜 n Inv.inv x := by
  simpa only [← Ring.inverse_eq_inv'] using cont_diff_at_ring_inverse 𝕜 (Units.mk0 x hx)

theorem cont_diff_on_inv {n} : ContDiffOn 𝕜 n (Inv.inv : 𝕜' → 𝕜') ({0}ᶜ) := fun x hx =>
  (cont_diff_at_inv 𝕜 hx).ContDiffWithinAt

variable {𝕜}

-- TODO: the next few lemmas don't need `𝕜` or `𝕜'` to be complete
-- A good way to show this is to generalize `cont_diff_at_ring_inverse` to the setting
-- of a function `f` such that `∀ᶠ x in 𝓝 a, x * f x = 1`.
theorem ContDiffWithinAt.inv {f : E → 𝕜'} {n} (hf : ContDiffWithinAt 𝕜 n f s x) (hx : f x ≠ 0) :
    ContDiffWithinAt 𝕜 n (fun x => (f x)⁻¹) s x :=
  (cont_diff_at_inv 𝕜 hx).comp_cont_diff_within_at x hf

theorem ContDiffOn.inv {f : E → 𝕜'} {n} (hf : ContDiffOn 𝕜 n f s) (h : ∀, ∀ x ∈ s, ∀, f x ≠ 0) :
    ContDiffOn 𝕜 n (fun x => (f x)⁻¹) s := fun x hx => (hf.ContDiffWithinAt hx).inv (h x hx)

theorem ContDiffAt.inv {f : E → 𝕜'} {n} (hf : ContDiffAt 𝕜 n f x) (hx : f x ≠ 0) :
    ContDiffAt 𝕜 n (fun x => (f x)⁻¹) x :=
  hf.inv hx

theorem ContDiff.inv {f : E → 𝕜'} {n} (hf : ContDiff 𝕜 n f) (h : ∀ x, f x ≠ 0) : ContDiff 𝕜 n fun x => (f x)⁻¹ := by
  rw [cont_diff_iff_cont_diff_at]
  exact fun x => hf.cont_diff_at.inv (h x)

-- TODO: generalize to `f g : E → 𝕜'`
theorem ContDiffWithinAt.div [CompleteSpace 𝕜] {f g : E → 𝕜} {n} (hf : ContDiffWithinAt 𝕜 n f s x)
    (hg : ContDiffWithinAt 𝕜 n g s x) (hx : g x ≠ 0) : ContDiffWithinAt 𝕜 n (fun x => f x / g x) s x := by
  simpa only [← div_eq_mul_inv] using hf.mul (hg.inv hx)

theorem ContDiffOn.div [CompleteSpace 𝕜] {f g : E → 𝕜} {n} (hf : ContDiffOn 𝕜 n f s) (hg : ContDiffOn 𝕜 n g s)
    (h₀ : ∀, ∀ x ∈ s, ∀, g x ≠ 0) : ContDiffOn 𝕜 n (f / g) s := fun x hx => (hf x hx).div (hg x hx) (h₀ x hx)

theorem ContDiffAt.div [CompleteSpace 𝕜] {f g : E → 𝕜} {n} (hf : ContDiffAt 𝕜 n f x) (hg : ContDiffAt 𝕜 n g x)
    (hx : g x ≠ 0) : ContDiffAt 𝕜 n (fun x => f x / g x) x :=
  hf.div hg hx

theorem ContDiff.div [CompleteSpace 𝕜] {f g : E → 𝕜} {n} (hf : ContDiff 𝕜 n f) (hg : ContDiff 𝕜 n g)
    (h0 : ∀ x, g x ≠ 0) : ContDiff 𝕜 n fun x => f x / g x := by
  simp only [← cont_diff_iff_cont_diff_at] at *
  exact fun x => (hf x).div (hg x) (h0 x)

end AlgebraInverse

/-! ### Inversion of continuous linear maps between Banach spaces -/


section MapInverse

open ContinuousLinearMap

/-- At a continuous linear equivalence `e : E ≃L[𝕜] F` between Banach spaces, the operation of
inversion is `C^n`, for all `n`. -/
theorem cont_diff_at_map_inverse [CompleteSpace E] (e : E ≃L[𝕜] F) : ContDiffAt 𝕜 n inverse (e : E →L[𝕜] F) := by
  nontriviality E
  -- first, we use the lemma `to_ring_inverse` to rewrite in terms of `ring.inverse` in the ring
  -- `E →L[𝕜] E`
  let O₁ : (E →L[𝕜] E) → F →L[𝕜] E := fun f => f.comp (e.symm : F →L[𝕜] E)
  let O₂ : (E →L[𝕜] F) → E →L[𝕜] E := fun f => (e.symm : F →L[𝕜] E).comp f
  have : ContinuousLinearMap.inverse = O₁ ∘ Ring.inverse ∘ O₂ := funext (to_ring_inverse e)
  rw [this]
  -- `O₁` and `O₂` are `cont_diff`,
  -- so we reduce to proving that `ring.inverse` is `cont_diff`
  have h₁ : ContDiff 𝕜 n O₁ := cont_diff_id.clm_comp cont_diff_const
  have h₂ : ContDiff 𝕜 n O₂ := cont_diff_const.clm_comp cont_diff_id
  refine' h₁.cont_diff_at.comp _ (ContDiffAt.comp _ _ h₂.cont_diff_at)
  convert cont_diff_at_ring_inverse 𝕜 (1 : (E →L[𝕜] E)ˣ)
  simp [← O₂, ← one_def]

end MapInverse

section FunctionInverse

open ContinuousLinearMap

/-- If `f` is a local homeomorphism and the point `a` is in its target,
and if `f` is `n` times continuously differentiable at `f.symm a`,
and if the derivative at `f.symm a` is a continuous linear equivalence,
then `f.symm` is `n` times continuously differentiable at the point `a`.

This is one of the easy parts of the inverse function theorem: it assumes that we already have
an inverse function. -/
theorem LocalHomeomorph.cont_diff_at_symm [CompleteSpace E] (f : LocalHomeomorph E F) {f₀' : E ≃L[𝕜] F} {a : F}
    (ha : a ∈ f.Target) (hf₀' : HasFderivAt f (f₀' : E →L[𝕜] F) (f.symm a)) (hf : ContDiffAt 𝕜 n f (f.symm a)) :
    ContDiffAt 𝕜 n f.symm a := by
  -- We prove this by induction on `n`
  induction' n using WithTop.nat_induction with n IH Itop
  · rw [cont_diff_at_zero]
    exact ⟨f.target, IsOpen.mem_nhds f.open_target ha, f.continuous_inv_fun⟩
    
  · obtain ⟨f', ⟨u, hu, hff'⟩, hf'⟩ := cont_diff_at_succ_iff_has_fderiv_at.mp hf
    apply cont_diff_at_succ_iff_has_fderiv_at.mpr
    -- For showing `n.succ` times continuous differentiability (the main inductive step), it
    -- suffices to produce the derivative and show that it is `n` times continuously differentiable
    have eq_f₀' : f' (f.symm a) = f₀' := (hff' (f.symm a) (mem_of_mem_nhds hu)).unique hf₀'
    -- This follows by a bootstrapping formula expressing the derivative as a function of `f` itself
    refine' ⟨inverse ∘ f' ∘ f.symm, _, _⟩
    · -- We first check that the derivative of `f` is that formula
      have h_nhds : { y : E | ∃ e : E ≃L[𝕜] F, ↑e = f' y } ∈ 𝓝 (f.symm a) := by
        have hf₀' := f₀'.nhds
        rw [← eq_f₀'] at hf₀'
        exact hf'.continuous_at.preimage_mem_nhds hf₀'
      obtain ⟨t, htu, ht, htf⟩ := mem_nhds_iff.mp (Filter.inter_mem hu h_nhds)
      use f.target ∩ f.symm ⁻¹' t
      refine' ⟨IsOpen.mem_nhds _ _, _⟩
      · exact f.preimage_open_of_open_symm ht
        
      · exact mem_inter ha (mem_preimage.mpr htf)
        
      intro x hx
      obtain ⟨hxu, e, he⟩ := htu hx.2
      have h_deriv : HasFderivAt f (↑e) (f.symm x) := by
        rw [he]
        exact hff' (f.symm x) hxu
      convert f.has_fderiv_at_symm hx.1 h_deriv
      simp [he]
      
    · -- Then we check that the formula, being a composition of `cont_diff` pieces, is
      -- itself `cont_diff`
      have h_deriv₁ : ContDiffAt 𝕜 n inverse (f' (f.symm a)) := by
        rw [eq_f₀']
        exact cont_diff_at_map_inverse _
      have h_deriv₂ : ContDiffAt 𝕜 n f.symm a := by
        refine' IH (hf.of_le _)
        norm_cast
        exact Nat.le_succₓ n
      exact (h_deriv₁.comp _ hf').comp _ h_deriv₂
      
    
  · refine' cont_diff_at_top.mpr _
    intro n
    exact Itop n (cont_diff_at_top.mp hf n)
    

/-- If `f` is an `n` times continuously differentiable homeomorphism,
and if the derivative of `f` at each point is a continuous linear equivalence,
then `f.symm` is `n` times continuously differentiable.

This is one of the easy parts of the inverse function theorem: it assumes that we already have
an inverse function. -/
theorem Homeomorph.cont_diff_symm [CompleteSpace E] (f : E ≃ₜ F) {f₀' : E → E ≃L[𝕜] F}
    (hf₀' : ∀ a, HasFderivAt f (f₀' a : E →L[𝕜] F) a) (hf : ContDiff 𝕜 n (f : E → F)) : ContDiff 𝕜 n (f.symm : F → E) :=
  cont_diff_iff_cont_diff_at.2 fun x => f.toLocalHomeomorph.cont_diff_at_symm (mem_univ x) (hf₀' _) hf.ContDiffAt

/-- Let `f` be a local homeomorphism of a nondiscrete normed field, let `a` be a point in its
target. if `f` is `n` times continuously differentiable at `f.symm a`, and if the derivative at
`f.symm a` is nonzero, then `f.symm` is `n` times continuously differentiable at the point `a`.

This is one of the easy parts of the inverse function theorem: it assumes that we already have
an inverse function. -/
theorem LocalHomeomorph.cont_diff_at_symm_deriv [CompleteSpace 𝕜] (f : LocalHomeomorph 𝕜 𝕜) {f₀' a : 𝕜} (h₀ : f₀' ≠ 0)
    (ha : a ∈ f.Target) (hf₀' : HasDerivAt f f₀' (f.symm a)) (hf : ContDiffAt 𝕜 n f (f.symm a)) :
    ContDiffAt 𝕜 n f.symm a :=
  f.cont_diff_at_symm ha (hf₀'.has_fderiv_at_equiv h₀) hf

/-- Let `f` be an `n` times continuously differentiable homeomorphism of a nondiscrete normed field.
Suppose that the derivative of `f` is never equal to zero. Then `f.symm` is `n` times continuously
differentiable.

This is one of the easy parts of the inverse function theorem: it assumes that we already have
an inverse function. -/
theorem Homeomorph.cont_diff_symm_deriv [CompleteSpace 𝕜] (f : 𝕜 ≃ₜ 𝕜) {f' : 𝕜 → 𝕜} (h₀ : ∀ x, f' x ≠ 0)
    (hf' : ∀ x, HasDerivAt f (f' x) x) (hf : ContDiff 𝕜 n (f : 𝕜 → 𝕜)) : ContDiff 𝕜 n (f.symm : 𝕜 → 𝕜) :=
  cont_diff_iff_cont_diff_at.2 fun x =>
    f.toLocalHomeomorph.cont_diff_at_symm_deriv (h₀ _) (mem_univ x) (hf' _) hf.ContDiffAt

end FunctionInverse

/-! ### Finite dimensional results -/


section FiniteDimensional

open Function FiniteDimensional

variable [CompleteSpace 𝕜]

/-- A family of continuous linear maps is `C^n` on `s` if all its applications are. -/
theorem cont_diff_on_clm_apply {n : WithTop ℕ} {f : E → F →L[𝕜] G} {s : Set E} [FiniteDimensional 𝕜 F] :
    ContDiffOn 𝕜 n f s ↔ ∀ y, ContDiffOn 𝕜 n (fun x => f x y) s := by
  refine' ⟨fun h y => (ContinuousLinearMap.apply 𝕜 G y).ContDiff.comp_cont_diff_on h, fun h => _⟩
  let d := finrank 𝕜 F
  have hd : d = finrank 𝕜 (Finₓ d → 𝕜) := (finrank_fin_fun 𝕜).symm
  let e₁ := ContinuousLinearEquiv.ofFinrankEq hd
  let e₂ := (e₁.arrow_congr (1 : G ≃L[𝕜] G)).trans (ContinuousLinearEquiv.piRing (Finₓ d))
  rw [← comp.left_id f, ← e₂.symm_comp_self]
  exact e₂.symm.cont_diff.comp_cont_diff_on (cont_diff_on_pi.mpr fun i => h _)

theorem cont_diff_clm_apply {n : WithTop ℕ} {f : E → F →L[𝕜] G} [FiniteDimensional 𝕜 F] :
    ContDiff 𝕜 n f ↔ ∀ y, ContDiff 𝕜 n fun x => f x y := by
  simp_rw [← cont_diff_on_univ, cont_diff_on_clm_apply]

/-- This is a useful lemma to prove that a certain operation preserves functions being `C^n`.
When you do induction on `n`, this gives a useful characterization of a function being `C^(n+1)`,
assuming you have already computed the derivative. The advantage of this version over
`cont_diff_succ_iff_fderiv` is that both occurences of `cont_diff` are for functions with the same
domain and codomain (`E` and `F`). This is not the case for `cont_diff_succ_iff_fderiv`, which
often requires an inconvenient need to generalize `F`, which results in universe issues
(see the discussion in the section of `cont_diff.comp`).

This lemma avoids these universe issues, but only applies for finite dimensional `E`. -/
theorem cont_diff_succ_iff_fderiv_apply [FiniteDimensional 𝕜 E] {n : ℕ} {f : E → F} :
    ContDiff 𝕜 (n + 1 : ℕ) f ↔ Differentiable 𝕜 f ∧ ∀ y, ContDiff 𝕜 n fun x => fderiv 𝕜 f x y := by
  rw [cont_diff_succ_iff_fderiv, cont_diff_clm_apply]

theorem cont_diff_on_succ_of_fderiv_apply [FiniteDimensional 𝕜 E] {n : ℕ} {f : E → F} {s : Set E}
    (hf : DifferentiableOn 𝕜 f s) (h : ∀ y, ContDiffOn 𝕜 n (fun x => fderivWithin 𝕜 f s x y) s) :
    ContDiffOn 𝕜 (n + 1 : ℕ) f s :=
  cont_diff_on_succ_of_fderiv_within hf <| cont_diff_on_clm_apply.mpr h

theorem cont_diff_on_succ_iff_fderiv_apply [FiniteDimensional 𝕜 E] {n : ℕ} {f : E → F} {s : Set E}
    (hs : UniqueDiffOn 𝕜 s) :
    ContDiffOn 𝕜 (n + 1 : ℕ) f s ↔ DifferentiableOn 𝕜 f s ∧ ∀ y, ContDiffOn 𝕜 n (fun x => fderivWithin 𝕜 f s x y) s :=
  by
  rw [cont_diff_on_succ_iff_fderiv_within hs, cont_diff_on_clm_apply]

end FiniteDimensional

section Real

/-!
### Results over `ℝ` or `ℂ`
  The results in this section rely on the Mean Value Theorem, and therefore hold only over `ℝ` (and
  its extension fields such as `ℂ`).
-/


variable {𝕂 : Type _} [IsROrC 𝕂] {E' : Type _} [NormedGroup E'] [NormedSpace 𝕂 E'] {F' : Type _} [NormedGroup F']
  [NormedSpace 𝕂 F']

/-- If a function has a Taylor series at order at least 1, then at points in the interior of the
    domain of definition, the term of order 1 of this series is a strict derivative of `f`. -/
theorem HasFtaylorSeriesUpToOn.has_strict_fderiv_at {s : Set E'} {f : E' → F'} {x : E'}
    {p : E' → FormalMultilinearSeries 𝕂 E' F'} (hf : HasFtaylorSeriesUpToOn n f p s) (hn : 1 ≤ n) (hs : s ∈ 𝓝 x) :
    HasStrictFderivAt f ((continuousMultilinearCurryFin1 𝕂 E' F') (p x 1)) x :=
  has_strict_fderiv_at_of_has_fderiv_at_of_continuous_at (hf.eventually_has_fderiv_at hn hs) <|
    (continuousMultilinearCurryFin1 𝕂 E' F').ContinuousAt.comp <| (hf.cont 1 hn).ContinuousAt hs

/-- If a function is `C^n` with `1 ≤ n` around a point, and its derivative at that point is given to
us as `f'`, then `f'` is also a strict derivative. -/
theorem ContDiffAt.has_strict_fderiv_at' {f : E' → F'} {f' : E' →L[𝕂] F'} {x : E'} (hf : ContDiffAt 𝕂 n f x)
    (hf' : HasFderivAt f f' x) (hn : 1 ≤ n) : HasStrictFderivAt f f' x := by
  rcases hf 1 hn with ⟨u, H, p, hp⟩
  simp only [← nhds_within_univ, ← mem_univ, ← insert_eq_of_mem] at H
  have := hp.has_strict_fderiv_at le_rfl H
  rwa [hf'.unique this.has_fderiv_at]

/-- If a function is `C^n` with `1 ≤ n` around a point, and its derivative at that point is given to
us as `f'`, then `f'` is also a strict derivative. -/
theorem ContDiffAt.has_strict_deriv_at' {f : 𝕂 → F'} {f' : F'} {x : 𝕂} (hf : ContDiffAt 𝕂 n f x)
    (hf' : HasDerivAt f f' x) (hn : 1 ≤ n) : HasStrictDerivAt f f' x :=
  hf.has_strict_fderiv_at' hf' hn

/-- If a function is `C^n` with `1 ≤ n` around a point, then the derivative of `f` at this point
is also a strict derivative. -/
theorem ContDiffAt.has_strict_fderiv_at {f : E' → F'} {x : E'} (hf : ContDiffAt 𝕂 n f x) (hn : 1 ≤ n) :
    HasStrictFderivAt f (fderiv 𝕂 f x) x :=
  hf.has_strict_fderiv_at' (hf.DifferentiableAt hn).HasFderivAt hn

/-- If a function is `C^n` with `1 ≤ n` around a point, then the derivative of `f` at this point
is also a strict derivative. -/
theorem ContDiffAt.has_strict_deriv_at {f : 𝕂 → F'} {x : 𝕂} (hf : ContDiffAt 𝕂 n f x) (hn : 1 ≤ n) :
    HasStrictDerivAt f (deriv f x) x :=
  (hf.HasStrictFderivAt hn).HasStrictDerivAt

/-- If a function is `C^n` with `1 ≤ n`, then the derivative of `f` is also a strict derivative. -/
theorem ContDiff.has_strict_fderiv_at {f : E' → F'} {x : E'} (hf : ContDiff 𝕂 n f) (hn : 1 ≤ n) :
    HasStrictFderivAt f (fderiv 𝕂 f x) x :=
  hf.ContDiffAt.HasStrictFderivAt hn

/-- If a function is `C^n` with `1 ≤ n`, then the derivative of `f` is also a strict derivative. -/
theorem ContDiff.has_strict_deriv_at {f : 𝕂 → F'} {x : 𝕂} (hf : ContDiff 𝕂 n f) (hn : 1 ≤ n) :
    HasStrictDerivAt f (deriv f x) x :=
  hf.ContDiffAt.HasStrictDerivAt hn

/-- If `f` has a formal Taylor series `p` up to order `1` on `{x} ∪ s`, where `s` is a convex set,
and `∥p x 1∥₊ < K`, then `f` is `K`-Lipschitz in a neighborhood of `x` within `s`. -/
theorem HasFtaylorSeriesUpToOn.exists_lipschitz_on_with_of_nnnorm_lt {E F : Type _} [NormedGroup E] [NormedSpace ℝ E]
    [NormedGroup F] [NormedSpace ℝ F] {f : E → F} {p : E → FormalMultilinearSeries ℝ E F} {s : Set E} {x : E}
    (hf : HasFtaylorSeriesUpToOn 1 f p (insert x s)) (hs : Convex ℝ s) (K : ℝ≥0 ) (hK : ∥p x 1∥₊ < K) :
    ∃ t ∈ 𝓝[s] x, LipschitzOnWith K f t := by
  set f' := fun y => continuousMultilinearCurryFin1 ℝ E F (p y 1)
  have hder : ∀, ∀ y ∈ s, ∀, HasFderivWithinAt f (f' y) s y := fun y hy =>
    (hf.has_fderiv_within_at le_rfl (subset_insert x s hy)).mono (subset_insert x s)
  have hcont : ContinuousWithinAt f' s x :=
    (continuousMultilinearCurryFin1 ℝ E F).ContinuousAt.comp_continuous_within_at
      ((hf.cont _ le_rfl _ (mem_insert _ _)).mono (subset_insert x s))
  replace hK : ∥f' x∥₊ < K
  · simpa only [← LinearIsometryEquiv.nnnorm_map]
    
  exact
    hs.exists_nhds_within_lipschitz_on_with_of_has_fderiv_within_at_of_nnnorm_lt
      (eventually_nhds_within_iff.2 <| eventually_of_forall hder) hcont K hK

/-- If `f` has a formal Taylor series `p` up to order `1` on `{x} ∪ s`, where `s` is a convex set,
then `f` is Lipschitz in a neighborhood of `x` within `s`. -/
theorem HasFtaylorSeriesUpToOn.exists_lipschitz_on_with {E F : Type _} [NormedGroup E] [NormedSpace ℝ E] [NormedGroup F]
    [NormedSpace ℝ F] {f : E → F} {p : E → FormalMultilinearSeries ℝ E F} {s : Set E} {x : E}
    (hf : HasFtaylorSeriesUpToOn 1 f p (insert x s)) (hs : Convex ℝ s) : ∃ K, ∃ t ∈ 𝓝[s] x, LipschitzOnWith K f t :=
  (exists_gt _).imp <| hf.exists_lipschitz_on_with_of_nnnorm_lt hs

/-- If `f` is `C^1` within a conves set `s` at `x`, then it is Lipschitz on a neighborhood of `x`
within `s`. -/
theorem ContDiffWithinAt.exists_lipschitz_on_with {E F : Type _} [NormedGroup E] [NormedSpace ℝ E] [NormedGroup F]
    [NormedSpace ℝ F] {f : E → F} {s : Set E} {x : E} (hf : ContDiffWithinAt ℝ 1 f s x) (hs : Convex ℝ s) :
    ∃ K : ℝ≥0 , ∃ t ∈ 𝓝[s] x, LipschitzOnWith K f t := by
  rcases hf 1 le_rfl with ⟨t, hst, p, hp⟩
  rcases metric.mem_nhds_within_iff.mp hst with ⟨ε, ε0, hε⟩
  replace hp : HasFtaylorSeriesUpToOn 1 f p (Metric.Ball x ε ∩ insert x s) := hp.mono hε
  clear hst hε t
  rw [← insert_eq_of_mem (Metric.mem_ball_self ε0), ← insert_inter_distrib] at hp
  rcases hp.exists_lipschitz_on_with ((convex_ball _ _).inter hs) with ⟨K, t, hst, hft⟩
  rw [inter_comm, ← nhds_within_restrict' _ (Metric.ball_mem_nhds _ ε0)] at hst
  exact ⟨K, t, hst, hft⟩

/-- If `f` is `C^1` at `x` and `K > ∥fderiv 𝕂 f x∥`, then `f` is `K`-Lipschitz in a neighborhood of
`x`. -/
theorem ContDiffAt.exists_lipschitz_on_with_of_nnnorm_lt {f : E' → F'} {x : E'} (hf : ContDiffAt 𝕂 1 f x) (K : ℝ≥0 )
    (hK : ∥fderiv 𝕂 f x∥₊ < K) : ∃ t ∈ 𝓝 x, LipschitzOnWith K f t :=
  (hf.HasStrictFderivAt le_rfl).exists_lipschitz_on_with_of_nnnorm_lt K hK

/-- If `f` is `C^1` at `x`, then `f` is Lipschitz in a neighborhood of `x`. -/
theorem ContDiffAt.exists_lipschitz_on_with {f : E' → F'} {x : E'} (hf : ContDiffAt 𝕂 1 f x) :
    ∃ K, ∃ t ∈ 𝓝 x, LipschitzOnWith K f t :=
  (hf.HasStrictFderivAt le_rfl).exists_lipschitz_on_with

end Real

section deriv

/-!
### One dimension

All results up to now have been expressed in terms of the general Fréchet derivative `fderiv`. For
maps defined on the field, the one-dimensional derivative `deriv` is often easier to use. In this
paragraph, we reformulate some higher smoothness results in terms of `deriv`.
-/


variable {f₂ : 𝕜 → F} {s₂ : Set 𝕜}

open ContinuousLinearMap (smul_right)

/-- A function is `C^(n + 1)` on a domain with unique derivatives if and only if it is
differentiable there, and its derivative (formulated with `deriv_within`) is `C^n`. -/
theorem cont_diff_on_succ_iff_deriv_within {n : ℕ} (hs : UniqueDiffOn 𝕜 s₂) :
    ContDiffOn 𝕜 (n + 1 : ℕ) f₂ s₂ ↔ DifferentiableOn 𝕜 f₂ s₂ ∧ ContDiffOn 𝕜 n (derivWithin f₂ s₂) s₂ := by
  rw [cont_diff_on_succ_iff_fderiv_within hs]
  congr 2
  apply le_antisymmₓ
  · intro h
    have : derivWithin f₂ s₂ = (fun u : 𝕜 →L[𝕜] F => u 1) ∘ fderivWithin 𝕜 f₂ s₂ := by
      ext x
      rfl
    simp only [← this]
    apply ContDiff.comp_cont_diff_on _ h
    exact (is_bounded_bilinear_map_apply.is_bounded_linear_map_left _).ContDiff
    
  · intro h
    have : fderivWithin 𝕜 f₂ s₂ = smul_right (1 : 𝕜 →L[𝕜] 𝕜) ∘ derivWithin f₂ s₂ := by
      ext x
      simp [← derivWithin]
    simp only [← this]
    apply ContDiff.comp_cont_diff_on _ h
    have : IsBoundedBilinearMap 𝕜 fun _ : (𝕜 →L[𝕜] 𝕜) × F => _ := is_bounded_bilinear_map_smul_right
    exact (this.is_bounded_linear_map_right _).ContDiff
    

-- ./././Mathport/Syntax/Translate/Basic.lean:647:16: unsupported tactic `congrm #[[expr «expr ∧ »(_, _)]]
/-- A function is `C^(n + 1)` on an open domain if and only if it is
differentiable there, and its derivative (formulated with `deriv`) is `C^n`. -/
theorem cont_diff_on_succ_iff_deriv_of_open {n : ℕ} (hs : IsOpen s₂) :
    ContDiffOn 𝕜 (n + 1 : ℕ) f₂ s₂ ↔ DifferentiableOn 𝕜 f₂ s₂ ∧ ContDiffOn 𝕜 n (deriv f₂) s₂ := by
  rw [cont_diff_on_succ_iff_deriv_within hs.unique_diff_on]
  trace "./././Mathport/Syntax/Translate/Basic.lean:647:16: unsupported tactic `congrm #[[expr «expr ∧ »(_, _)]]"
  apply cont_diff_on_congr
  intro x hx
  exact deriv_within_of_open hs hx

/-- A function is `C^∞` on a domain with unique derivatives if and only if it is differentiable
there, and its derivative (formulated with `deriv_within`) is `C^∞`. -/
theorem cont_diff_on_top_iff_deriv_within (hs : UniqueDiffOn 𝕜 s₂) :
    ContDiffOn 𝕜 ∞ f₂ s₂ ↔ DifferentiableOn 𝕜 f₂ s₂ ∧ ContDiffOn 𝕜 ∞ (derivWithin f₂ s₂) s₂ := by
  constructor
  · intro h
    refine' ⟨h.differentiable_on le_top, _⟩
    apply cont_diff_on_top.2 fun n => ((cont_diff_on_succ_iff_deriv_within hs).1 _).2
    exact h.of_le le_top
    
  · intro h
    refine' cont_diff_on_top.2 fun n => _
    have A : (n : WithTop ℕ) ≤ ∞ := le_top
    apply ((cont_diff_on_succ_iff_deriv_within hs).2 ⟨h.1, h.2.of_le A⟩).of_le
    exact WithTop.coe_le_coe.2 (Nat.le_succₓ n)
    

-- ./././Mathport/Syntax/Translate/Basic.lean:647:16: unsupported tactic `congrm #[[expr «expr ∧ »(_, _)]]
/-- A function is `C^∞` on an open domain if and only if it is differentiable
there, and its derivative (formulated with `deriv`) is `C^∞`. -/
theorem cont_diff_on_top_iff_deriv_of_open (hs : IsOpen s₂) :
    ContDiffOn 𝕜 ∞ f₂ s₂ ↔ DifferentiableOn 𝕜 f₂ s₂ ∧ ContDiffOn 𝕜 ∞ (deriv f₂) s₂ := by
  rw [cont_diff_on_top_iff_deriv_within hs.unique_diff_on]
  trace "./././Mathport/Syntax/Translate/Basic.lean:647:16: unsupported tactic `congrm #[[expr «expr ∧ »(_, _)]]"
  apply cont_diff_on_congr
  intro x hx
  exact deriv_within_of_open hs hx

theorem ContDiffOn.deriv_within (hf : ContDiffOn 𝕜 n f₂ s₂) (hs : UniqueDiffOn 𝕜 s₂) (hmn : m + 1 ≤ n) :
    ContDiffOn 𝕜 m (derivWithin f₂ s₂) s₂ := by
  cases m
  · change ∞ + 1 ≤ n at hmn
    have : n = ∞ := by
      simpa using hmn
    rw [this] at hf
    exact ((cont_diff_on_top_iff_deriv_within hs).1 hf).2
    
  · change (m.succ : WithTop ℕ) ≤ n at hmn
    exact ((cont_diff_on_succ_iff_deriv_within hs).1 (hf.of_le hmn)).2
    

theorem ContDiffOn.deriv_of_open (hf : ContDiffOn 𝕜 n f₂ s₂) (hs : IsOpen s₂) (hmn : m + 1 ≤ n) :
    ContDiffOn 𝕜 m (deriv f₂) s₂ :=
  (hf.derivWithin hs.UniqueDiffOn hmn).congr fun x hx => (deriv_within_of_open hs hx).symm

theorem ContDiffOn.continuous_on_deriv_within (h : ContDiffOn 𝕜 n f₂ s₂) (hs : UniqueDiffOn 𝕜 s₂) (hn : 1 ≤ n) :
    ContinuousOn (derivWithin f₂ s₂) s₂ :=
  ((cont_diff_on_succ_iff_deriv_within hs).1 (h.of_le hn)).2.ContinuousOn

theorem ContDiffOn.continuous_on_deriv_of_open (h : ContDiffOn 𝕜 n f₂ s₂) (hs : IsOpen s₂) (hn : 1 ≤ n) :
    ContinuousOn (deriv f₂) s₂ :=
  ((cont_diff_on_succ_iff_deriv_of_open hs).1 (h.of_le hn)).2.ContinuousOn

/-- A function is `C^(n + 1)` if and only if it is differentiable,
  and its derivative (formulated in terms of `deriv`) is `C^n`. -/
theorem cont_diff_succ_iff_deriv {n : ℕ} : ContDiff 𝕜 (n + 1 : ℕ) f₂ ↔ Differentiable 𝕜 f₂ ∧ ContDiff 𝕜 n (deriv f₂) :=
  by
  simp only [cont_diff_on_univ, ← cont_diff_on_succ_iff_deriv_of_open, ← is_open_univ, ← differentiable_on_univ]

theorem cont_diff_one_iff_deriv : ContDiff 𝕜 1 f₂ ↔ Differentiable 𝕜 f₂ ∧ Continuous (deriv f₂) :=
  cont_diff_succ_iff_deriv.trans <| Iff.rfl.And cont_diff_zero

/-- A function is `C^∞` if and only if it is differentiable,
and its derivative (formulated in terms of `deriv`) is `C^∞`. -/
theorem cont_diff_top_iff_deriv : ContDiff 𝕜 ∞ f₂ ↔ Differentiable 𝕜 f₂ ∧ ContDiff 𝕜 ∞ (deriv f₂) := by
  simp [← cont_diff_on_univ.symm, ← differentiable_on_univ.symm, ← deriv_within_univ.symm, -deriv_within_univ]
  rw [cont_diff_on_top_iff_deriv_within unique_diff_on_univ]

theorem ContDiff.continuous_deriv (h : ContDiff 𝕜 n f₂) (hn : 1 ≤ n) : Continuous (deriv f₂) :=
  (cont_diff_succ_iff_deriv.mp (h.of_le hn)).2.Continuous

end deriv

section RestrictScalars

/-!
### Restricting from `ℂ` to `ℝ`, or generally from `𝕜'` to `𝕜`

If a function is `n` times continuously differentiable over `ℂ`, then it is `n` times continuously
differentiable over `ℝ`. In this paragraph, we give variants of this statement, in the general
situation where `ℂ` and `ℝ` are replaced respectively by `𝕜'` and `𝕜` where `𝕜'` is a normed algebra
over `𝕜`.
-/


variable (𝕜) {𝕜' : Type _} [NondiscreteNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜']

variable [NormedSpace 𝕜' E] [IsScalarTower 𝕜 𝕜' E]

variable [NormedSpace 𝕜' F] [IsScalarTower 𝕜 𝕜' F]

variable {p' : E → FormalMultilinearSeries 𝕜' E F}

theorem HasFtaylorSeriesUpToOn.restrict_scalars (h : HasFtaylorSeriesUpToOn n f p' s) :
    HasFtaylorSeriesUpToOn n f (fun x => (p' x).restrictScalars 𝕜) s :=
  { zero_eq := fun x hx => h.zero_eq x hx,
    fderivWithin := by
      intro m hm x hx
      convert
        (ContinuousMultilinearMap.restrictScalarsLinear 𝕜).HasFderivAt.comp_has_fderiv_within_at _
          ((h.fderiv_within m hm x hx).restrictScalars 𝕜),
    cont := fun m hm => ContinuousMultilinearMap.continuous_restrict_scalars.comp_continuous_on (h.cont m hm) }

theorem ContDiffWithinAt.restrict_scalars (h : ContDiffWithinAt 𝕜' n f s x) : ContDiffWithinAt 𝕜 n f s x := by
  intro m hm
  rcases h m hm with ⟨u, u_mem, p', hp'⟩
  exact ⟨u, u_mem, _, hp'.restrict_scalars _⟩

theorem ContDiffOn.restrict_scalars (h : ContDiffOn 𝕜' n f s) : ContDiffOn 𝕜 n f s := fun x hx =>
  (h x hx).restrictScalars _

theorem ContDiffAt.restrict_scalars (h : ContDiffAt 𝕜' n f x) : ContDiffAt 𝕜 n f x :=
  cont_diff_within_at_univ.1 <| h.ContDiffWithinAt.restrictScalars _

theorem ContDiff.restrict_scalars (h : ContDiff 𝕜' n f) : ContDiff 𝕜 n f :=
  cont_diff_iff_cont_diff_at.2 fun x => h.ContDiffAt.restrictScalars _

end RestrictScalars

