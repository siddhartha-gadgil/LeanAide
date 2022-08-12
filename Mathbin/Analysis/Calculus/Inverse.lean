/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Heather Macbeth, Sébastien Gouëzel
-/
import Mathbin.Analysis.Calculus.ContDiff
import Mathbin.Tactic.RingExp
import Mathbin.Analysis.NormedSpace.Banach
import Mathbin.Topology.LocalHomeomorph

/-!
# Inverse function theorem

In this file we prove the inverse function theorem. It says that if a map `f : E → F`
has an invertible strict derivative `f'` at `a`, then it is locally invertible,
and the inverse function has derivative `f' ⁻¹`.

We define `has_strict_deriv_at.to_local_homeomorph` that repacks a function `f`
with a `hf : has_strict_fderiv_at f f' a`, `f' : E ≃L[𝕜] F`, into a `local_homeomorph`.
The `to_fun` of this `local_homeomorph` is `defeq` to `f`, so one can apply theorems
about `local_homeomorph` to `hf.to_local_homeomorph f`, and get statements about `f`.

Then we define `has_strict_fderiv_at.local_inverse` to be the `inv_fun` of this `local_homeomorph`,
and prove two versions of the inverse function theorem:

* `has_strict_fderiv_at.to_local_inverse`: if `f` has an invertible derivative `f'` at `a` in the
  strict sense (`hf`), then `hf.local_inverse f f' a` has derivative `f'.symm` at `f a` in the
  strict sense;

* `has_strict_fderiv_at.to_local_left_inverse`: if `f` has an invertible derivative `f'` at `a` in
  the strict sense and `g` is locally left inverse to `f` near `a`, then `g` has derivative
  `f'.symm` at `f a` in the strict sense.

In the one-dimensional case we reformulate these theorems in terms of `has_strict_deriv_at` and
`f'⁻¹`.

We also reformulate the theorems in terms of `cont_diff`, to give that `C^k` (respectively,
smooth) inputs give `C^k` (smooth) inverses.  These versions require that continuous
differentiability implies strict differentiability; this is false over a general field, true over
`ℝ` or `ℂ` and implemented here assuming `is_R_or_C 𝕂`.

Some related theorems, providing the derivative and higher regularity assuming that we already know
the inverse function, are formulated in `fderiv.lean`, `deriv.lean`, and `cont_diff.lean`.

## Notations

In the section about `approximates_linear_on` we introduce some `local notation` to make formulas
shorter:

* by `N` we denote `∥f'⁻¹∥`;
* by `g` we denote the auxiliary contracting map `x ↦ x + f'.symm (y - f x)` used to prove that
  `{x | f x = y}` is nonempty.

## Tags

derivative, strictly differentiable, continuously differentiable, smooth, inverse function
-/


open Function Set Filter Metric

open TopologicalSpace Classical Nnreal

noncomputable section

variable {𝕜 : Type _} [NondiscreteNormedField 𝕜]

variable {E : Type _} [NormedGroup E] [NormedSpace 𝕜 E]

variable {F : Type _} [NormedGroup F] [NormedSpace 𝕜 F]

variable {G : Type _} [NormedGroup G] [NormedSpace 𝕜 G]

variable {G' : Type _} [NormedGroup G'] [NormedSpace 𝕜 G']

variable {ε : ℝ}

open Asymptotics Filter Metric Set

open ContinuousLinearMap (id)

/-!
### Non-linear maps close to affine maps

In this section we study a map `f` such that `∥f x - f y - f' (x - y)∥ ≤ c * ∥x - y∥` on an open set
`s`, where `f' : E →L[𝕜] F` is a continuous linear map and `c` is suitably small. Maps of this type
behave like `f a + f' (x - a)` near each `a ∈ s`.

When `f'` is onto, we show that `f` is locally onto.

When `f'` is a continuous linear equiv, we show that `f` is a homeomorphism
between `s` and `f '' s`. More precisely, we define `approximates_linear_on.to_local_homeomorph` to
be a `local_homeomorph` with `to_fun = f`, `source = s`, and `target = f '' s`.

Maps of this type naturally appear in the proof of the inverse function theorem (see next section),
and `approximates_linear_on.to_local_homeomorph` will imply that the locally inverse function
exists.

We define this auxiliary notion to split the proof of the inverse function theorem into small
lemmas. This approach makes it possible

- to prove a lower estimate on the size of the domain of the inverse function;

- to reuse parts of the proofs in the case if a function is not strictly differentiable. E.g., for a
  function `f : E × F → G` with estimates on `f x y₁ - f x y₂` but not on `f x₁ y - f x₂ y`.
-/


/-- We say that `f` approximates a continuous linear map `f'` on `s` with constant `c`,
if `∥f x - f y - f' (x - y)∥ ≤ c * ∥x - y∥` whenever `x, y ∈ s`.

This predicate is defined to facilitate the splitting of the inverse function theorem into small
lemmas. Some of these lemmas can be useful, e.g., to prove that the inverse function is defined
on a specific set. -/
def ApproximatesLinearOn (f : E → F) (f' : E →L[𝕜] F) (s : Set E) (c : ℝ≥0 ) : Prop :=
  ∀, ∀ x ∈ s, ∀, ∀ y ∈ s, ∀, ∥f x - f y - f' (x - y)∥ ≤ c * ∥x - y∥

@[simp]
theorem approximates_linear_on_empty (f : E → F) (f' : E →L[𝕜] F) (c : ℝ≥0 ) : ApproximatesLinearOn f f' ∅ c := by
  simp [← ApproximatesLinearOn]

namespace ApproximatesLinearOn

variable [cs : CompleteSpace E] {f : E → F}

/-! First we prove some properties of a function that `approximates_linear_on` a (not necessarily
invertible) continuous linear map. -/


section

variable {f' : E →L[𝕜] F} {s t : Set E} {c c' : ℝ≥0 }

theorem mono_num (hc : c ≤ c') (hf : ApproximatesLinearOn f f' s c) : ApproximatesLinearOn f f' s c' := fun x hx y hy =>
  le_transₓ (hf x hx y hy) (mul_le_mul_of_nonneg_right hc <| norm_nonneg _)

theorem mono_set (hst : s ⊆ t) (hf : ApproximatesLinearOn f f' t c) : ApproximatesLinearOn f f' s c := fun x hx y hy =>
  hf x (hst hx) y (hst hy)

theorem approximates_linear_on_iff_lipschitz_on_with {f : E → F} {f' : E →L[𝕜] F} {s : Set E} {c : ℝ≥0 } :
    ApproximatesLinearOn f f' s c ↔ LipschitzOnWith c (f - f') s := by
  have : ∀ x y, f x - f y - f' (x - y) = (f - f') x - (f - f') y := by
    intro x y
    simp only [← map_sub, ← Pi.sub_apply]
    abel
  simp only [← this, ← lipschitz_on_with_iff_norm_sub_le, ← ApproximatesLinearOn]

alias approximates_linear_on_iff_lipschitz_on_with ↔ LipschitzOnWith _root_.lipschitz_on_with.approximates_linear_on

theorem lipschitz_sub (hf : ApproximatesLinearOn f f' s c) : LipschitzWith c fun x : s => f x - f' x := by
  refine' LipschitzWith.of_dist_le_mul fun x y => _
  rw [dist_eq_norm, Subtype.dist_eq, dist_eq_norm]
  convert hf x x.2 y y.2 using 2
  rw [f'.map_sub]
  abel

protected theorem lipschitz (hf : ApproximatesLinearOn f f' s c) : LipschitzWith (∥f'∥₊ + c) (s.restrict f) := by
  simpa only [← restrict_apply, ← add_sub_cancel'_right] using (f'.lipschitz.restrict s).add hf.lipschitz_sub

protected theorem continuous (hf : ApproximatesLinearOn f f' s c) : Continuous (s.restrict f) :=
  hf.lipschitz.Continuous

protected theorem continuous_on (hf : ApproximatesLinearOn f f' s c) : ContinuousOn f s :=
  continuous_on_iff_continuous_restrict.2 hf.Continuous

end

section LocallyOnto

/-!
We prove that a function which is linearly approximated by a continuous linear map with a nonlinear
right inverse is locally onto. This will apply to the case where the approximating map is a linear
equivalence, for the local inverse theorem, but also whenever the approximating map is onto,
by Banach's open mapping theorem. -/


include cs

variable {s : Set E} {c : ℝ≥0 } {f' : E →L[𝕜] F}

/-- If a function is linearly approximated by a continuous linear map with a (possibly nonlinear)
right inverse, then it is locally onto: a ball of an explicit radius is included in the image
of the map. -/
theorem surj_on_closed_ball_of_nonlinear_right_inverse (hf : ApproximatesLinearOn f f' s c)
    (f'symm : f'.NonlinearRightInverse) {ε : ℝ} {b : E} (ε0 : 0 ≤ ε) (hε : ClosedBall b ε ⊆ s) :
    SurjOn f (ClosedBall b ε) (ClosedBall (f b) (((f'symm.nnnorm : ℝ)⁻¹ - c) * ε)) := by
  intro y hy
  cases' le_or_ltₓ (f'symm.nnnorm : ℝ)⁻¹ c with hc hc
  · refine'
      ⟨b, by
        simp [← ε0], _⟩
    have : dist y (f b) ≤ 0 :=
      (mem_closed_ball.1 hy).trans
        (mul_nonpos_of_nonpos_of_nonneg
          (by
            linarith)
          ε0)
    simp only [← dist_le_zero] at this
    rw [this]
    
  have If' : (0 : ℝ) < f'symm.nnnorm := by
    rw [← inv_pos]
    exact (Nnreal.coe_nonneg _).trans_lt hc
  have Icf' : (c : ℝ) * f'symm.nnnorm < 1 := by
    rwa [inv_eq_one_div, lt_div_iff If'] at hc
  have Jf' : (f'symm.nnnorm : ℝ) ≠ 0 := ne_of_gtₓ If'
  have Jcf' : (1 : ℝ) - c * f'symm.nnnorm ≠ 0 := by
    apply ne_of_gtₓ
    linarith
  /- We have to show that `y` can be written as `f x` for some `x ∈ closed_ball b ε`.
    The idea of the proof is to apply the Banach contraction principle to the map
    `g : x ↦ x + f'symm (y - f x)`, as a fixed point of this map satisfies `f x = y`.
    When `f'symm` is a genuine linear inverse, `g` is a contracting map. In our case, since `f'symm`
    is nonlinear, this map is not contracting (it is not even continuous), but still the proof of
    the contraction theorem holds: `uₙ = gⁿ b` is a Cauchy sequence, converging exponentially fast
    to the desired point `x`. Instead of appealing to general results, we check this by hand.
  
    The main point is that `f (u n)` becomes exponentially close to `y`, and therefore
    `dist (u (n+1)) (u n)` becomes exponentally small, making it possible to get an inductive
    bound on `dist (u n) b`, from which one checks that `u n` stays in the ball on which one has a
    control. Therefore, the bound can be checked at the next step, and so on inductively.
    -/
  set g := fun x => x + f'symm (y - f x) with hg
  set u := fun n : ℕ => (g^[n]) b with hu
  have usucc : ∀ n, u (n + 1) = g (u n) := by
    simp [← hu, iterate_succ_apply' g _ b]
  -- First bound: if `f z` is close to `y`, then `g z` is close to `z` (i.e., almost a fixed point).
  have A : ∀ z, dist (g z) z ≤ f'symm.nnnorm * dist (f z) y := by
    intro z
    rw [dist_eq_norm, hg, add_sub_cancel', dist_eq_norm']
    exact f'symm.bound _
  -- Second bound: if `z` and `g z` are in the set with good control, then `f (g z)` becomes closer
  -- to `y` than `f z` was (this uses the linear approximation property, and is the reason for the
  -- choice of the formula for `g`).
  have B : ∀, ∀ z ∈ closed_ball b ε, ∀, g z ∈ closed_ball b ε → dist (f (g z)) y ≤ c * f'symm.nnnorm * dist (f z) y :=
    by
    intro z hz hgz
    set v := f'symm (y - f z) with hv
    calc dist (f (g z)) y = ∥f (z + v) - y∥ := by
        rw [dist_eq_norm]_ = ∥f (z + v) - f z - f' v + f' v - (y - f z)∥ := by
        congr 1
        abel _ = ∥f (z + v) - f z - f' (z + v - z)∥ := by
        simp only [← ContinuousLinearMap.NonlinearRightInverse.right_inv, ← add_sub_cancel', ←
          sub_add_cancel]_ ≤ c * ∥z + v - z∥ :=
        hf _ (hε hgz) _ (hε hz)_ ≤ c * (f'symm.nnnorm * dist (f z) y) := by
        apply mul_le_mul_of_nonneg_left _ (Nnreal.coe_nonneg c)
        simpa [← hv, ← dist_eq_norm'] using f'symm.bound (y - f z)_ = c * f'symm.nnnorm * dist (f z) y := by
        ring
  -- Third bound: a complicated bound on `dist w b` (that will show up in the induction) is enough
  -- to check that `w` is in the ball on which one has controls. Will be used to check that `u n`
  -- belongs to this ball for all `n`.
  have C :
    ∀ (n : ℕ) (w : E),
      dist w b ≤ f'symm.nnnorm * (1 - (c * f'symm.nnnorm) ^ n) / (1 - c * f'symm.nnnorm) * dist (f b) y →
        w ∈ closed_ball b ε :=
    by
    intro n w hw
    apply hw.trans
    rw [div_mul_eq_mul_div, div_le_iff]
    swap
    · linarith
      
    calc
      (f'symm.nnnorm : ℝ) * (1 - (c * f'symm.nnnorm) ^ n) * dist (f b) y =
          f'symm.nnnorm * dist (f b) y * (1 - (c * f'symm.nnnorm) ^ n) :=
        by
        ring _ ≤ f'symm.nnnorm * dist (f b) y * 1 := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg (Nnreal.coe_nonneg _) dist_nonneg)
        rw [sub_le_self_iff]
        exact
          pow_nonneg (mul_nonneg (Nnreal.coe_nonneg _) (Nnreal.coe_nonneg _))
            _ _ ≤ f'symm.nnnorm * (((f'symm.nnnorm : ℝ)⁻¹ - c) * ε) :=
        by
        rw [mul_oneₓ]
        exact mul_le_mul_of_nonneg_left (mem_closed_ball'.1 hy) (Nnreal.coe_nonneg _)_ = ε * (1 - c * f'symm.nnnorm) :=
        by
        field_simp
        ring
  /- Main inductive control: `f (u n)` becomes exponentially close to `y`, and therefore
    `dist (u (n+1)) (u n)` becomes exponentally small, making it possible to get an inductive
    bound on `dist (u n) b`, from which one checks that `u n` remains in the ball on which we
    have estimates. -/
  have D :
    ∀ n : ℕ,
      dist (f (u n)) y ≤ (c * f'symm.nnnorm) ^ n * dist (f b) y ∧
        dist (u n) b ≤ f'symm.nnnorm * (1 - (c * f'symm.nnnorm) ^ n) / (1 - c * f'symm.nnnorm) * dist (f b) y :=
    by
    intro n
    induction' n with n IH
    · simp [← hu, ← le_reflₓ]
      
    rw [usucc]
    have Ign :
      dist (g (u n)) b ≤ f'symm.nnnorm * (1 - (c * f'symm.nnnorm) ^ n.succ) / (1 - c * f'symm.nnnorm) * dist (f b) y :=
      calc
        dist (g (u n)) b ≤ dist (g (u n)) (u n) + dist (u n) b := dist_triangle _ _ _
        _ ≤ f'symm.nnnorm * dist (f (u n)) y + dist (u n) b := add_le_add (A _) le_rfl
        _ ≤
            f'symm.nnnorm * ((c * f'symm.nnnorm) ^ n * dist (f b) y) +
              f'symm.nnnorm * (1 - (c * f'symm.nnnorm) ^ n) / (1 - c * f'symm.nnnorm) * dist (f b) y :=
          add_le_add (mul_le_mul_of_nonneg_left IH.1 (Nnreal.coe_nonneg _)) IH.2
        _ = f'symm.nnnorm * (1 - (c * f'symm.nnnorm) ^ n.succ) / (1 - c * f'symm.nnnorm) * dist (f b) y := by
          field_simp [← Jcf']
          ring_exp
        
    refine' ⟨_, Ign⟩
    calc dist (f (g (u n))) y ≤ c * f'symm.nnnorm * dist (f (u n)) y :=
        B _ (C n _ IH.2) (C n.succ _ Ign)_ ≤ c * f'symm.nnnorm * ((c * f'symm.nnnorm) ^ n * dist (f b) y) :=
        mul_le_mul_of_nonneg_left IH.1
          (mul_nonneg (Nnreal.coe_nonneg _) (Nnreal.coe_nonneg _))_ = (c * f'symm.nnnorm) ^ n.succ * dist (f b) y :=
        by
        ring_exp
  -- Deduce from the inductive bound that `uₙ` is a Cauchy sequence, therefore converging.
  have : CauchySeq u := by
    have : ∀ n : ℕ, dist (u n) (u (n + 1)) ≤ f'symm.nnnorm * dist (f b) y * (c * f'symm.nnnorm) ^ n := by
      intro n
      calc dist (u n) (u (n + 1)) = dist (g (u n)) (u n) := by
          rw [usucc, dist_comm]_ ≤ f'symm.nnnorm * dist (f (u n)) y :=
          A _ _ ≤ f'symm.nnnorm * ((c * f'symm.nnnorm) ^ n * dist (f b) y) :=
          mul_le_mul_of_nonneg_left (D n).1
            (Nnreal.coe_nonneg _)_ = f'symm.nnnorm * dist (f b) y * (c * f'symm.nnnorm) ^ n :=
          by
          ring
    exact cauchy_seq_of_le_geometric _ _ Icf' this
  obtain ⟨x, hx⟩ : ∃ x, tendsto u at_top (𝓝 x) := cauchy_seq_tendsto_of_complete this
  -- As all the `uₙ` belong to the ball `closed_ball b ε`, so does their limit `x`.
  have xmem : x ∈ closed_ball b ε := is_closed_ball.mem_of_tendsto hx (eventually_of_forall fun n => C n _ (D n).2)
  refine' ⟨x, xmem, _⟩
  -- It remains to check that `f x = y`. This follows from continuity of `f` on `closed_ball b ε`
  -- and from the fact that `f uₙ` is converging to `y` by construction.
  have hx' : tendsto u at_top (𝓝[closed_ball b ε] x) := by
    simp only [← nhdsWithin, ← tendsto_inf, ← hx, ← true_andₓ, ← ge_iff_le, ← tendsto_principal]
    exact eventually_of_forall fun n => C n _ (D n).2
  have T1 : tendsto (fun n => f (u n)) at_top (𝓝 (f x)) := (hf.continuous_on.mono hε x xmem).Tendsto.comp hx'
  have T2 : tendsto (fun n => f (u n)) at_top (𝓝 y) := by
    rw [tendsto_iff_dist_tendsto_zero]
    refine' squeeze_zero (fun n => dist_nonneg) (fun n => (D n).1) _
    simpa using
      (tendsto_pow_at_top_nhds_0_of_lt_1 (mul_nonneg (Nnreal.coe_nonneg _) (Nnreal.coe_nonneg _)) Icf').mul
        tendsto_const_nhds
  exact tendsto_nhds_unique T1 T2

theorem open_image (hf : ApproximatesLinearOn f f' s c) (f'symm : f'.NonlinearRightInverse) (hs : IsOpen s)
    (hc : Subsingleton F ∨ c < f'symm.nnnorm⁻¹) : IsOpen (f '' s) := by
  cases' hc with hE hc
  · skip
    apply is_open_discrete
    
  simp only [← is_open_iff_mem_nhds, ← nhds_basis_closed_ball.mem_iff, ← ball_image_iff] at hs⊢
  intro x hx
  rcases hs x hx with ⟨ε, ε0, hε⟩
  refine' ⟨(f'symm.nnnorm⁻¹ - c) * ε, mul_pos (sub_pos.2 hc) ε0, _⟩
  exact (hf.surj_on_closed_ball_of_nonlinear_right_inverse f'symm (le_of_ltₓ ε0) hε).mono hε (subset.refl _)

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (t «expr ⊆ » s)
theorem image_mem_nhds (hf : ApproximatesLinearOn f f' s c) (f'symm : f'.NonlinearRightInverse) {x : E} (hs : s ∈ 𝓝 x)
    (hc : Subsingleton F ∨ c < f'symm.nnnorm⁻¹) : f '' s ∈ 𝓝 (f x) := by
  obtain ⟨t, hts, ht, xt⟩ : ∃ (t : _)(_ : t ⊆ s), IsOpen t ∧ x ∈ t := _root_.mem_nhds_iff.1 hs
  have := IsOpen.mem_nhds ((hf.mono_set hts).open_image f'symm ht hc) (mem_image_of_mem _ xt)
  exact mem_of_superset this (image_subset _ hts)

theorem map_nhds_eq (hf : ApproximatesLinearOn f f' s c) (f'symm : f'.NonlinearRightInverse) {x : E} (hs : s ∈ 𝓝 x)
    (hc : Subsingleton F ∨ c < f'symm.nnnorm⁻¹) : map f (𝓝 x) = 𝓝 (f x) := by
  refine' le_antisymmₓ ((hf.continuous_on x (mem_of_mem_nhds hs)).ContinuousAt hs) (le_map fun t ht => _)
  have : f '' (s ∩ t) ∈ 𝓝 (f x) := (hf.mono_set (inter_subset_left s t)).image_mem_nhds f'symm (inter_mem hs ht) hc
  exact mem_of_superset this (image_subset _ (inter_subset_right _ _))

end LocallyOnto

/-!
From now on we assume that `f` approximates an invertible continuous linear map `f : E ≃L[𝕜] F`.

We also assume that either `E = {0}`, or `c < ∥f'⁻¹∥⁻¹`. We use `N` as an abbreviation for `∥f'⁻¹∥`.
-/


variable {f' : E ≃L[𝕜] F} {s : Set E} {c : ℝ≥0 }

-- mathport name: «exprN»
local notation "N" => ∥(f'.symm : F →L[𝕜] E)∥₊

protected theorem antilipschitz (hf : ApproximatesLinearOn f (f' : E →L[𝕜] F) s c) (hc : Subsingleton E ∨ c < N⁻¹) :
    AntilipschitzWith (N⁻¹ - c)⁻¹ (s.restrict f) := by
  cases' hc with hE hc
  · have : Subsingleton s := ⟨fun x y => Subtype.eq <| @Subsingleton.elimₓ _ hE _ _⟩
    exact AntilipschitzWith.of_subsingleton
    
  convert (f'.antilipschitz.restrict s).add_lipschitz_with hf.lipschitz_sub hc
  simp [← restrict]

protected theorem injective (hf : ApproximatesLinearOn f (f' : E →L[𝕜] F) s c) (hc : Subsingleton E ∨ c < N⁻¹) :
    Injective (s.restrict f) :=
  (hf.antilipschitz hc).Injective

protected theorem inj_on (hf : ApproximatesLinearOn f (f' : E →L[𝕜] F) s c) (hc : Subsingleton E ∨ c < N⁻¹) :
    InjOn f s :=
  inj_on_iff_injective.2 <| hf.Injective hc

protected theorem surjective [CompleteSpace E] (hf : ApproximatesLinearOn f (f' : E →L[𝕜] F) Univ c)
    (hc : Subsingleton E ∨ c < N⁻¹) : Surjective f := by
  cases' hc with hE hc
  · have : Subsingleton F := (Equivₓ.subsingleton_congr f'.to_linear_equiv.to_equiv).1 hE
    exact surjective_to_subsingleton _
    
  · apply forall_of_forall_mem_closed_ball (fun y : F => ∃ a, f a = y) (f 0) _
    have hc' : (0 : ℝ) < N⁻¹ - c := by
      rw [sub_pos]
      exact hc
    let p : ℝ → Prop := fun R => closed_ball (f 0) R ⊆ Set.Range f
    have hp : ∀ᶠ r : ℝ in at_top, p ((N⁻¹ - c) * r) := by
      have hr : ∀ᶠ r : ℝ in at_top, 0 ≤ r := eventually_ge_at_top 0
      refine' hr.mono fun r hr => subset.trans _ (image_subset_range f (closed_ball 0 r))
      refine' hf.surj_on_closed_ball_of_nonlinear_right_inverse f'.to_nonlinear_right_inverse hr _
      exact subset_univ _
    refine' ((tendsto_id.const_mul_at_top hc').Frequently hp.frequently).mono _
    exact fun R h y hy => h hy
    

/-- A map approximating a linear equivalence on a set defines a local equivalence on this set.
Should not be used outside of this file, because it is superseded by `to_local_homeomorph` below.

This is a first step towards the inverse function. -/
def toLocalEquiv (hf : ApproximatesLinearOn f (f' : E →L[𝕜] F) s c) (hc : Subsingleton E ∨ c < N⁻¹) : LocalEquiv E F :=
  (hf.InjOn hc).toLocalEquiv _ _

/-- The inverse function is continuous on `f '' s`. Use properties of `local_homeomorph` instead. -/
theorem inverse_continuous_on (hf : ApproximatesLinearOn f (f' : E →L[𝕜] F) s c) (hc : Subsingleton E ∨ c < N⁻¹) :
    ContinuousOn (hf.toLocalEquiv hc).symm (f '' s) := by
  apply continuous_on_iff_continuous_restrict.2
  refine' ((hf.antilipschitz hc).to_right_inv_on' _ (hf.to_local_equiv hc).right_inv').Continuous
  exact fun x hx => (hf.to_local_equiv hc).map_target hx

-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:63:9: parse error
/-- The inverse function is approximated linearly on `f '' s` by `f'.symm`. -/
theorem to_inv (hf : ApproximatesLinearOn f (f' : E →L[𝕜] F) s c) (hc : Subsingleton E ∨ c < N⁻¹) :
    ApproximatesLinearOn (hf.toLocalEquiv hc).symm (f'.symm : F →L[𝕜] E) (f '' s) (N * (N⁻¹ - c)⁻¹ * c) := by
  intro x hx y hy
  set A := hf.to_local_equiv hc with hA
  have Af : ∀ z, A z = f z := fun z => rfl
  rcases(mem_image _ _ _).1 hx with ⟨x', x's, rfl⟩
  rcases(mem_image _ _ _).1 hy with ⟨y', y's, rfl⟩
  rw [← Af x', ← Af y', A.left_inv x's, A.left_inv y's]
  calc ∥x' - y' - f'.symm (A x' - A y')∥ ≤ N * ∥f' (x' - y' - f'.symm (A x' - A y'))∥ :=
      (f' : E →L[𝕜] F).bound_of_antilipschitz f'.antilipschitz _ _ = N * ∥A y' - A x' - f' (y' - x')∥ := by
      congr 2
      simp only [← ContinuousLinearEquiv.apply_symm_apply, ← ContinuousLinearEquiv.map_sub]
      abel _ ≤ N * (c * ∥y' - x'∥) :=
      mul_le_mul_of_nonneg_left (hf _ y's _ x's)
        (Nnreal.coe_nonneg _)_ ≤ N * (c * (((N⁻¹ - c)⁻¹ : ℝ≥0 ) * ∥A y' - A x'∥)) :=
      by
      apply_rules [mul_le_mul_of_nonneg_left, Nnreal.coe_nonneg]
      rw [← dist_eq_norm, ← dist_eq_norm]
      exact (hf.antilipschitz hc).le_mul_dist ⟨y', y's⟩ ⟨x', x's⟩_ = (N * (N⁻¹ - c)⁻¹ * c : ℝ≥0 ) * ∥A x' - A y'∥ := by
      simp only [← norm_sub_rev, ← Nonneg.coe_mul]
      ring

include cs

section

variable (f s)

/-- Given a function `f` that approximates a linear equivalence on an open set `s`,
returns a local homeomorph with `to_fun = f` and `source = s`. -/
def toLocalHomeomorph (hf : ApproximatesLinearOn f (f' : E →L[𝕜] F) s c) (hc : Subsingleton E ∨ c < N⁻¹)
    (hs : IsOpen s) : LocalHomeomorph E F where
  toLocalEquiv := hf.toLocalEquiv hc
  open_source := hs
  open_target :=
    hf.open_image f'.toNonlinearRightInverse hs
      (by
        rwa [f'.to_linear_equiv.to_equiv.subsingleton_congr] at hc)
  continuous_to_fun := hf.ContinuousOn
  continuous_inv_fun := hf.inverse_continuous_on hc

/-- A function `f` that approximates a linear equivalence on the whole space is a homeomorphism. -/
def toHomeomorph (hf : ApproximatesLinearOn f (f' : E →L[𝕜] F) Univ c) (hc : Subsingleton E ∨ c < N⁻¹) : E ≃ₜ F := by
  refine' (hf.to_local_homeomorph _ _ hc is_open_univ).toHomeomorphOfSourceEqUnivTargetEqUniv rfl _
  change f '' univ = univ
  rw [image_univ, range_iff_surjective]
  exact hf.surjective hc

omit cs

/-- In a real vector space, a function `f` that approximates a linear equivalence on a subset `s`
can be extended to a homeomorphism of the whole space. -/
theorem exists_homeomorph_extension {E : Type _} [NormedGroup E] [NormedSpace ℝ E] {F : Type _} [NormedGroup F]
    [NormedSpace ℝ F] [FiniteDimensional ℝ F] {s : Set E} {f : E → F} {f' : E ≃L[ℝ] F} {c : ℝ≥0 }
    (hf : ApproximatesLinearOn f (f' : E →L[ℝ] F) s c)
    (hc : Subsingleton E ∨ lipschitzExtensionConstant F * c < ∥(f'.symm : F →L[ℝ] E)∥₊⁻¹) : ∃ g : E ≃ₜ F, EqOn f g s :=
  by
  -- the difference `f - f'` is Lipschitz on `s`. It can be extended to a Lipschitz function `u`
  -- on the whole space, with a slightly worse Lipschitz constant. Then `f' + u` will be the
  -- desired homeomorphism.
  obtain ⟨u, hu, uf⟩ : ∃ u : E → F, LipschitzWith (lipschitzExtensionConstant F * c) u ∧ eq_on (f - f') u s :=
    hf.lipschitz_on_with.extend_finite_dimension
  let g : E → F := fun x => f' x + u x
  have fg : eq_on f g s := fun x hx => by
    simp_rw [g, ← uf hx, Pi.sub_apply, add_sub_cancel'_right]
  have hg : ApproximatesLinearOn g (f' : E →L[ℝ] F) univ (lipschitzExtensionConstant F * c) := by
    apply LipschitzOnWith.approximates_linear_on
    rw [lipschitz_on_univ]
    convert hu
    ext x
    simp only [← add_sub_cancel', ← ContinuousLinearEquiv.coe_coe, ← Pi.sub_apply]
  have : FiniteDimensional ℝ E := f'.symm.to_linear_equiv.finite_dimensional
  exact ⟨hg.to_homeomorph g hc, fg⟩

end

@[simp]
theorem to_local_homeomorph_coe (hf : ApproximatesLinearOn f (f' : E →L[𝕜] F) s c) (hc : Subsingleton E ∨ c < N⁻¹)
    (hs : IsOpen s) : (hf.toLocalHomeomorph f s hc hs : E → F) = f :=
  rfl

@[simp]
theorem to_local_homeomorph_source (hf : ApproximatesLinearOn f (f' : E →L[𝕜] F) s c) (hc : Subsingleton E ∨ c < N⁻¹)
    (hs : IsOpen s) : (hf.toLocalHomeomorph f s hc hs).Source = s :=
  rfl

@[simp]
theorem to_local_homeomorph_target (hf : ApproximatesLinearOn f (f' : E →L[𝕜] F) s c) (hc : Subsingleton E ∨ c < N⁻¹)
    (hs : IsOpen s) : (hf.toLocalHomeomorph f s hc hs).Target = f '' s :=
  rfl

theorem closed_ball_subset_target (hf : ApproximatesLinearOn f (f' : E →L[𝕜] F) s c) (hc : Subsingleton E ∨ c < N⁻¹)
    (hs : IsOpen s) {b : E} (ε0 : 0 ≤ ε) (hε : ClosedBall b ε ⊆ s) :
    ClosedBall (f b) ((N⁻¹ - c) * ε) ⊆ (hf.toLocalHomeomorph f s hc hs).Target :=
  (hf.surj_on_closed_ball_of_nonlinear_right_inverse f'.toNonlinearRightInverse ε0 hε).mono hε (Subset.refl _)

end ApproximatesLinearOn

/-!
### Inverse function theorem

Now we prove the inverse function theorem. Let `f : E → F` be a map defined on a complete vector
space `E`. Assume that `f` has an invertible derivative `f' : E ≃L[𝕜] F` at `a : E` in the strict
sense. Then `f` approximates `f'` in the sense of `approximates_linear_on` on an open neighborhood
of `a`, and we can apply `approximates_linear_on.to_local_homeomorph` to construct the inverse
function. -/


namespace HasStrictFderivAt

/-- If `f` has derivative `f'` at `a` in the strict sense and `c > 0`, then `f` approximates `f'`
with constant `c` on some neighborhood of `a`. -/
theorem approximates_deriv_on_nhds {f : E → F} {f' : E →L[𝕜] F} {a : E} (hf : HasStrictFderivAt f f' a) {c : ℝ≥0 }
    (hc : Subsingleton E ∨ 0 < c) : ∃ s ∈ 𝓝 a, ApproximatesLinearOn f f' s c := by
  cases' hc with hE hc
  · refine' ⟨univ, IsOpen.mem_nhds is_open_univ trivialₓ, fun x hx y hy => _⟩
    simp [← @Subsingleton.elimₓ E hE x y]
    
  have := hf.def hc
  rw [nhds_prod_eq, Filter.Eventually, mem_prod_same_iff] at this
  rcases this with ⟨s, has, hs⟩
  exact ⟨s, has, fun x hx y hy => hs (mk_mem_prod hx hy)⟩

theorem map_nhds_eq_of_surj [CompleteSpace E] [CompleteSpace F] {f : E → F} {f' : E →L[𝕜] F} {a : E}
    (hf : HasStrictFderivAt f (f' : E →L[𝕜] F) a) (h : f'.range = ⊤) : map f (𝓝 a) = 𝓝 (f a) := by
  let f'symm := f'.nonlinear_right_inverse_of_surjective h
  set c : ℝ≥0 := f'symm.nnnorm⁻¹ / 2 with hc
  have f'symm_pos : 0 < f'symm.nnnorm := f'.nonlinear_right_inverse_of_surjective_nnnorm_pos h
  have cpos : 0 < c := by
    simp [← hc, ← Nnreal.half_pos, ← Nnreal.inv_pos, ← f'symm_pos]
  obtain ⟨s, s_nhds, hs⟩ : ∃ s ∈ 𝓝 a, ApproximatesLinearOn f f' s c := hf.approximates_deriv_on_nhds (Or.inr cpos)
  apply hs.map_nhds_eq f'symm s_nhds (Or.inr (Nnreal.half_lt_self _))
  simp [← ne_of_gtₓ f'symm_pos]

variable [cs : CompleteSpace E] {f : E → F} {f' : E ≃L[𝕜] F} {a : E}

theorem approximates_deriv_on_open_nhds (hf : HasStrictFderivAt f (f' : E →L[𝕜] F) a) :
    ∃ (s : Set E)(hs : a ∈ s ∧ IsOpen s), ApproximatesLinearOn f (f' : E →L[𝕜] F) s (∥(f'.symm : F →L[𝕜] E)∥₊⁻¹ / 2) :=
  by
  refine' ((nhds_basis_opens a).exists_iff _).1 _
  exact fun s t => ApproximatesLinearOn.mono_set
  exact
    hf.approximates_deriv_on_nhds <|
      (f'.subsingleton_or_nnnorm_symm_pos.imp id) fun hf' => Nnreal.half_pos <| Nnreal.inv_pos.2 <| hf'

include cs

variable (f)

/-- Given a function with an invertible strict derivative at `a`, returns a `local_homeomorph`
with `to_fun = f` and `a ∈ source`. This is a part of the inverse function theorem.
The other part `has_strict_fderiv_at.to_local_inverse` states that the inverse function
of this `local_homeomorph` has derivative `f'.symm`. -/
def toLocalHomeomorph (hf : HasStrictFderivAt f (f' : E →L[𝕜] F) a) : LocalHomeomorph E F :=
  ApproximatesLinearOn.toLocalHomeomorph f (Classical.some hf.approximates_deriv_on_open_nhds)
    (Classical.some_spec hf.approximates_deriv_on_open_nhds).snd
    ((f'.subsingleton_or_nnnorm_symm_pos.imp id) fun hf' => Nnreal.half_lt_self <| ne_of_gtₓ <| Nnreal.inv_pos.2 <| hf')
    (Classical.some_spec hf.approximates_deriv_on_open_nhds).fst.2

variable {f}

@[simp]
theorem to_local_homeomorph_coe (hf : HasStrictFderivAt f (f' : E →L[𝕜] F) a) : (hf.toLocalHomeomorph f : E → F) = f :=
  rfl

theorem mem_to_local_homeomorph_source (hf : HasStrictFderivAt f (f' : E →L[𝕜] F) a) :
    a ∈ (hf.toLocalHomeomorph f).Source :=
  (Classical.some_spec hf.approximates_deriv_on_open_nhds).fst.1

theorem image_mem_to_local_homeomorph_target (hf : HasStrictFderivAt f (f' : E →L[𝕜] F) a) :
    f a ∈ (hf.toLocalHomeomorph f).Target :=
  (hf.toLocalHomeomorph f).map_source hf.mem_to_local_homeomorph_source

theorem map_nhds_eq_of_equiv (hf : HasStrictFderivAt f (f' : E →L[𝕜] F) a) : map f (𝓝 a) = 𝓝 (f a) :=
  (hf.toLocalHomeomorph f).map_nhds_eq hf.mem_to_local_homeomorph_source

variable (f f' a)

/-- Given a function `f` with an invertible derivative, returns a function that is locally inverse
to `f`. -/
def localInverse (hf : HasStrictFderivAt f (f' : E →L[𝕜] F) a) : F → E :=
  (hf.toLocalHomeomorph f).symm

variable {f f' a}

theorem local_inverse_def (hf : HasStrictFderivAt f (f' : E →L[𝕜] F) a) :
    hf.localInverse f _ _ = (hf.toLocalHomeomorph f).symm :=
  rfl

theorem eventually_left_inverse (hf : HasStrictFderivAt f (f' : E →L[𝕜] F) a) :
    ∀ᶠ x in 𝓝 a, hf.localInverse f f' a (f x) = x :=
  (hf.toLocalHomeomorph f).eventually_left_inverse hf.mem_to_local_homeomorph_source

@[simp]
theorem local_inverse_apply_image (hf : HasStrictFderivAt f (f' : E →L[𝕜] F) a) : hf.localInverse f f' a (f a) = a :=
  hf.eventually_left_inverse.self_of_nhds

theorem eventually_right_inverse (hf : HasStrictFderivAt f (f' : E →L[𝕜] F) a) :
    ∀ᶠ y in 𝓝 (f a), f (hf.localInverse f f' a y) = y :=
  (hf.toLocalHomeomorph f).eventually_right_inverse' hf.mem_to_local_homeomorph_source

theorem local_inverse_continuous_at (hf : HasStrictFderivAt f (f' : E →L[𝕜] F) a) :
    ContinuousAt (hf.localInverse f f' a) (f a) :=
  (hf.toLocalHomeomorph f).continuous_at_symm hf.image_mem_to_local_homeomorph_target

theorem local_inverse_tendsto (hf : HasStrictFderivAt f (f' : E →L[𝕜] F) a) :
    Tendsto (hf.localInverse f f' a) (𝓝 <| f a) (𝓝 a) :=
  (hf.toLocalHomeomorph f).tendsto_symm hf.mem_to_local_homeomorph_source

theorem local_inverse_unique (hf : HasStrictFderivAt f (f' : E →L[𝕜] F) a) {g : F → E} (hg : ∀ᶠ x in 𝓝 a, g (f x) = x) :
    ∀ᶠ y in 𝓝 (f a), g y = localInverse f f' a hf y :=
  eventually_eq_of_left_inv_of_right_inv hg hf.eventually_right_inverse <|
    (hf.toLocalHomeomorph f).tendsto_symm hf.mem_to_local_homeomorph_source

/-- If `f` has an invertible derivative `f'` at `a` in the sense of strict differentiability `(hf)`,
then the inverse function `hf.local_inverse f` has derivative `f'.symm` at `f a`. -/
theorem to_local_inverse (hf : HasStrictFderivAt f (f' : E →L[𝕜] F) a) :
    HasStrictFderivAt (hf.localInverse f f' a) (f'.symm : F →L[𝕜] E) (f a) :=
  (hf.toLocalHomeomorph f).has_strict_fderiv_at_symm hf.image_mem_to_local_homeomorph_target <| by
    simpa [local_inverse_def] using hf

/-- If `f : E → F` has an invertible derivative `f'` at `a` in the sense of strict differentiability
and `g (f x) = x` in a neighborhood of `a`, then `g` has derivative `f'.symm` at `f a`.

For a version assuming `f (g y) = y` and continuity of `g` at `f a` but not `[complete_space E]`
see `of_local_left_inverse`.  -/
theorem to_local_left_inverse (hf : HasStrictFderivAt f (f' : E →L[𝕜] F) a) {g : F → E}
    (hg : ∀ᶠ x in 𝓝 a, g (f x) = x) : HasStrictFderivAt g (f'.symm : F →L[𝕜] E) (f a) :=
  hf.to_local_inverse.congr_of_eventually_eq <| (hf.local_inverse_unique hg).mono fun _ => Eq.symm

end HasStrictFderivAt

/-- If a function has an invertible strict derivative at all points, then it is an open map. -/
theorem open_map_of_strict_fderiv_equiv [CompleteSpace E] {f : E → F} {f' : E → E ≃L[𝕜] F}
    (hf : ∀ x, HasStrictFderivAt f (f' x : E →L[𝕜] F) x) : IsOpenMap f :=
  is_open_map_iff_nhds_le.2 fun x => (hf x).map_nhds_eq_of_equiv.Ge

/-!
### Inverse function theorem, 1D case

In this case we prove a version of the inverse function theorem for maps `f : 𝕜 → 𝕜`.
We use `continuous_linear_equiv.units_equiv_aut` to translate `has_strict_deriv_at f f' a` and
`f' ≠ 0` into `has_strict_fderiv_at f (_ : 𝕜 ≃L[𝕜] 𝕜) a`.
-/


namespace HasStrictDerivAt

variable [cs : CompleteSpace 𝕜] {f : 𝕜 → 𝕜} {f' a : 𝕜} (hf : HasStrictDerivAt f f' a) (hf' : f' ≠ 0)

include cs

variable (f f' a)

/-- A function that is inverse to `f` near `a`. -/
@[reducible]
def localInverse : 𝕜 → 𝕜 :=
  (hf.has_strict_fderiv_at_equiv hf').localInverse _ _ _

variable {f f' a}

theorem map_nhds_eq : map f (𝓝 a) = 𝓝 (f a) :=
  (hf.has_strict_fderiv_at_equiv hf').map_nhds_eq_of_equiv

theorem to_local_inverse : HasStrictDerivAt (hf.localInverse f f' a hf') f'⁻¹ (f a) :=
  (hf.has_strict_fderiv_at_equiv hf').to_local_inverse

theorem to_local_left_inverse {g : 𝕜 → 𝕜} (hg : ∀ᶠ x in 𝓝 a, g (f x) = x) : HasStrictDerivAt g f'⁻¹ (f a) :=
  (hf.has_strict_fderiv_at_equiv hf').to_local_left_inverse hg

end HasStrictDerivAt

/-- If a function has a non-zero strict derivative at all points, then it is an open map. -/
theorem open_map_of_strict_deriv [CompleteSpace 𝕜] {f f' : 𝕜 → 𝕜} (hf : ∀ x, HasStrictDerivAt f (f' x) x)
    (h0 : ∀ x, f' x ≠ 0) : IsOpenMap f :=
  is_open_map_iff_nhds_le.2 fun x => ((hf x).map_nhds_eq (h0 x)).Ge

/-!
### Inverse function theorem, smooth case

-/


namespace ContDiffAt

variable {𝕂 : Type _} [IsROrC 𝕂]

variable {E' : Type _} [NormedGroup E'] [NormedSpace 𝕂 E']

variable {F' : Type _} [NormedGroup F'] [NormedSpace 𝕂 F']

variable [CompleteSpace E'] (f : E' → F') {f' : E' ≃L[𝕂] F'} {a : E'}

/-- Given a `cont_diff` function over `𝕂` (which is `ℝ` or `ℂ`) with an invertible
derivative at `a`, returns a `local_homeomorph` with `to_fun = f` and `a ∈ source`. -/
def toLocalHomeomorph {n : WithTop ℕ} (hf : ContDiffAt 𝕂 n f a) (hf' : HasFderivAt f (f' : E' →L[𝕂] F') a)
    (hn : 1 ≤ n) : LocalHomeomorph E' F' :=
  (hf.has_strict_fderiv_at' hf' hn).toLocalHomeomorph f

variable {f}

@[simp]
theorem to_local_homeomorph_coe {n : WithTop ℕ} (hf : ContDiffAt 𝕂 n f a) (hf' : HasFderivAt f (f' : E' →L[𝕂] F') a)
    (hn : 1 ≤ n) : (hf.toLocalHomeomorph f hf' hn : E' → F') = f :=
  rfl

theorem mem_to_local_homeomorph_source {n : WithTop ℕ} (hf : ContDiffAt 𝕂 n f a)
    (hf' : HasFderivAt f (f' : E' →L[𝕂] F') a) (hn : 1 ≤ n) : a ∈ (hf.toLocalHomeomorph f hf' hn).Source :=
  (hf.has_strict_fderiv_at' hf' hn).mem_to_local_homeomorph_source

theorem image_mem_to_local_homeomorph_target {n : WithTop ℕ} (hf : ContDiffAt 𝕂 n f a)
    (hf' : HasFderivAt f (f' : E' →L[𝕂] F') a) (hn : 1 ≤ n) : f a ∈ (hf.toLocalHomeomorph f hf' hn).Target :=
  (hf.has_strict_fderiv_at' hf' hn).image_mem_to_local_homeomorph_target

/-- Given a `cont_diff` function over `𝕂` (which is `ℝ` or `ℂ`) with an invertible derivative
at `a`, returns a function that is locally inverse to `f`. -/
def localInverse {n : WithTop ℕ} (hf : ContDiffAt 𝕂 n f a) (hf' : HasFderivAt f (f' : E' →L[𝕂] F') a) (hn : 1 ≤ n) :
    F' → E' :=
  (hf.has_strict_fderiv_at' hf' hn).localInverse f f' a

theorem local_inverse_apply_image {n : WithTop ℕ} (hf : ContDiffAt 𝕂 n f a) (hf' : HasFderivAt f (f' : E' →L[𝕂] F') a)
    (hn : 1 ≤ n) : hf.localInverse hf' hn (f a) = a :=
  (hf.has_strict_fderiv_at' hf' hn).local_inverse_apply_image

/-- Given a `cont_diff` function over `𝕂` (which is `ℝ` or `ℂ`) with an invertible derivative
at `a`, the inverse function (produced by `cont_diff.to_local_homeomorph`) is
also `cont_diff`. -/
theorem to_local_inverse {n : WithTop ℕ} (hf : ContDiffAt 𝕂 n f a) (hf' : HasFderivAt f (f' : E' →L[𝕂] F') a)
    (hn : 1 ≤ n) : ContDiffAt 𝕂 n (hf.localInverse hf' hn) (f a) := by
  have := hf.local_inverse_apply_image hf' hn
  apply (hf.to_local_homeomorph f hf' hn).cont_diff_at_symm (image_mem_to_local_homeomorph_target hf hf' hn)
  · convert hf'
    
  · convert hf
    

end ContDiffAt

