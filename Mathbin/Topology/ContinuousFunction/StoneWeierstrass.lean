/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Heather Macbeth
-/
import Mathbin.Topology.ContinuousFunction.Weierstrass
import Mathbin.Analysis.Complex.Basic

/-!
# The Stone-Weierstrass theorem

If a subalgebra `A` of `C(X, ℝ)`, where `X` is a compact topological space,
separates points, then it is dense.

We argue as follows.

* In any subalgebra `A` of `C(X, ℝ)`, if `f ∈ A`, then `abs f ∈ A.topological_closure`.
  This follows from the Weierstrass approximation theorem on `[-∥f∥, ∥f∥]` by
  approximating `abs` uniformly thereon by polynomials.
* This ensures that `A.topological_closure` is actually a sublattice:
  if it contains `f` and `g`, then it contains the pointwise supremum `f ⊔ g`
  and the pointwise infimum `f ⊓ g`.
* Any nonempty sublattice `L` of `C(X, ℝ)` which separates points is dense,
  by a nice argument approximating a given `f` above and below using separating functions.
  For each `x y : X`, we pick a function `g x y ∈ L` so `g x y x = f x` and `g x y y = f y`.
  By continuity these functions remain close to `f` on small patches around `x` and `y`.
  We use compactness to identify a certain finitely indexed infimum of finitely indexed supremums
  which is then close to `f` everywhere, obtaining the desired approximation.
* Finally we put these pieces together. `L = A.topological_closure` is a nonempty sublattice
  which separates points since `A` does, and so is dense (in fact equal to `⊤`).

We then prove the complex version for self-adjoint subalgebras `A`, by separately approximating
the real and imaginary parts using the real subalgebra of real-valued functions in `A`
(which still separates points, by taking the norm-square of a separating function).

## Future work

Extend to cover the case of subalgebras of the continuous functions vanishing at infinity,
on non-compact spaces.

-/


noncomputable section

namespace ContinuousMap

variable {X : Type _} [TopologicalSpace X] [CompactSpace X]

/-- Turn a function `f : C(X, ℝ)` into a continuous map into `set.Icc (-∥f∥) (∥f∥)`,
thereby explicitly attaching bounds.
-/
def attachBound (f : C(X, ℝ)) :
    C(X, Set.Icc (-∥f∥) ∥f∥) where toFun := fun x => ⟨f x, ⟨neg_norm_le_apply f x, apply_le_norm f x⟩⟩

@[simp]
theorem attach_bound_apply_coe (f : C(X, ℝ)) (x : X) : ((attachBound f) x : ℝ) = f x :=
  rfl

theorem polynomial_comp_attach_bound (A : Subalgebra ℝ C(X, ℝ)) (f : A) (g : Polynomial ℝ) :
    (g.toContinuousMapOn (Set.Icc (-∥f∥) ∥f∥)).comp (f : C(X, ℝ)).attachBound = Polynomial.aeval f g := by
  ext
  simp only [← ContinuousMap.coe_comp, ← Function.comp_app, ← ContinuousMap.attach_bound_apply_coe, ←
    Polynomial.to_continuous_map_on_apply, ← Polynomial.aeval_subalgebra_coe, ← Polynomial.aeval_continuous_map_apply, ←
    Polynomial.to_continuous_map_apply]

/-- Given a continuous function `f` in a subalgebra of `C(X, ℝ)`, postcomposing by a polynomial
gives another function in `A`.

This lemma proves something slightly more subtle than this:
we take `f`, and think of it as a function into the restricted target `set.Icc (-∥f∥) ∥f∥)`,
and then postcompose with a polynomial function on that interval.
This is in fact the same situation as above, and so also gives a function in `A`.
-/
theorem polynomial_comp_attach_bound_mem (A : Subalgebra ℝ C(X, ℝ)) (f : A) (g : Polynomial ℝ) :
    (g.toContinuousMapOn (Set.Icc (-∥f∥) ∥f∥)).comp (f : C(X, ℝ)).attachBound ∈ A := by
  rw [polynomial_comp_attach_bound]
  apply SetLike.coe_mem

theorem comp_attach_bound_mem_closure (A : Subalgebra ℝ C(X, ℝ)) (f : A) (p : C(Set.Icc (-∥f∥) ∥f∥, ℝ)) :
    p.comp (attachBound f) ∈ A.topologicalClosure := by
  -- `p` itself is in the closure of polynomials, by the Weierstrass theorem,
  have mem_closure : p ∈ (polynomialFunctions (Set.Icc (-∥f∥) ∥f∥)).topologicalClosure :=
    continuous_map_mem_polynomial_functions_closure _ _ p
  -- and so there are polynomials arbitrarily close.
  have frequently_mem_polynomials := mem_closure_iff_frequently.mp mem_closure
  -- To prove `p.comp (attached_bound f)` is in the closure of `A`,
  -- we show there are elements of `A` arbitrarily close.
  apply mem_closure_iff_frequently.mpr
  -- To show that, we pull back the polynomials close to `p`,
  refine'
    ((comp_right_continuous_map ℝ (attach_bound (f : C(X, ℝ)))).ContinuousAt p).Tendsto.frequently_map _ _
      frequently_mem_polynomials
  -- but need to show that those pullbacks are actually in `A`.
  rintro _ ⟨g, ⟨-, rfl⟩⟩
  simp only [← SetLike.mem_coe, ← AlgHom.coe_to_ring_hom, ← comp_right_continuous_map_apply, ←
    Polynomial.to_continuous_map_on_alg_hom_apply]
  apply polynomial_comp_attach_bound_mem

theorem abs_mem_subalgebra_closure (A : Subalgebra ℝ C(X, ℝ)) (f : A) : (f : C(X, ℝ)).abs ∈ A.topologicalClosure := by
  let M := ∥f∥
  let f' := attach_bound (f : C(X, ℝ))
  let abs : C(Set.Icc (-∥f∥) ∥f∥, ℝ) := { toFun := fun x : Set.Icc (-∥f∥) ∥f∥ => abs (x : ℝ) }
  change abs.comp f' ∈ A.topological_closure
  apply comp_attach_bound_mem_closure

theorem inf_mem_subalgebra_closure (A : Subalgebra ℝ C(X, ℝ)) (f g : A) :
    (f : C(X, ℝ))⊓(g : C(X, ℝ)) ∈ A.topologicalClosure := by
  rw [inf_eq]
  refine'
    A.topological_closure.smul_mem
      (A.topological_closure.sub_mem
        (A.topological_closure.add_mem (A.subalgebra_topological_closure f.property)
          (A.subalgebra_topological_closure g.property))
        _)
      _
  exact_mod_cast abs_mem_subalgebra_closure A _

theorem inf_mem_closed_subalgebra (A : Subalgebra ℝ C(X, ℝ)) (h : IsClosed (A : Set C(X, ℝ))) (f g : A) :
    (f : C(X, ℝ))⊓(g : C(X, ℝ)) ∈ A := by
  convert inf_mem_subalgebra_closure A f g
  apply SetLike.ext'
  symm
  erw [closure_eq_iff_is_closed]
  exact h

theorem sup_mem_subalgebra_closure (A : Subalgebra ℝ C(X, ℝ)) (f g : A) :
    (f : C(X, ℝ))⊔(g : C(X, ℝ)) ∈ A.topologicalClosure := by
  rw [sup_eq]
  refine'
    A.topological_closure.smul_mem
      (A.topological_closure.add_mem
        (A.topological_closure.add_mem (A.subalgebra_topological_closure f.property)
          (A.subalgebra_topological_closure g.property))
        _)
      _
  exact_mod_cast abs_mem_subalgebra_closure A _

theorem sup_mem_closed_subalgebra (A : Subalgebra ℝ C(X, ℝ)) (h : IsClosed (A : Set C(X, ℝ))) (f g : A) :
    (f : C(X, ℝ))⊔(g : C(X, ℝ)) ∈ A := by
  convert sup_mem_subalgebra_closure A f g
  apply SetLike.ext'
  symm
  erw [closure_eq_iff_is_closed]
  exact h

open TopologicalSpace

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (f g «expr ∈ » L)
-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (f g «expr ∈ » L)
-- Here's the fun part of Stone-Weierstrass!
theorem sublattice_closure_eq_top (L : Set C(X, ℝ)) (nA : L.Nonempty)
    (inf_mem : ∀ (f g) (_ : f ∈ L) (_ : g ∈ L), f⊓g ∈ L) (sup_mem : ∀ (f g) (_ : f ∈ L) (_ : g ∈ L), f⊔g ∈ L)
    (sep : L.SeparatesPointsStrongly) : Closure L = ⊤ := by
  -- We start by boiling down to a statement about close approximation.
  apply eq_top_iff.mpr
  rintro f -
  refine' Filter.Frequently.mem_closure ((Filter.HasBasis.frequently_iff Metric.nhds_basis_ball).mpr fun ε pos => _)
  simp only [← exists_prop, ← Metric.mem_ball]
  -- It will be helpful to assume `X` is nonempty later,
  -- so we get that out of the way here.
  by_cases' nX : Nonempty X
  swap
  exact ⟨nA.some, (dist_lt_iff Pos).mpr fun x => False.elim (nX ⟨x⟩), nA.some_spec⟩
  /-
    The strategy now is to pick a family of continuous functions `g x y` in `A`
    with the property that `g x y x = f x` and `g x y y = f y`
    (this is immediate from `h : separates_points_strongly`)
    then use continuity to see that `g x y` is close to `f` near both `x` and `y`,
    and finally using compactness to produce the desired function `h`
    as a maximum over finitely many `x` of a minimum over finitely many `y` of the `g x y`.
    -/
  dsimp' [← Set.SeparatesPointsStrongly]  at sep
  let g : X → X → L := fun x y => (sep f x y).some
  have w₁ : ∀ x y, g x y x = f x := fun x y => (sep f x y).some_spec.1
  have w₂ : ∀ x y, g x y y = f y := fun x y => (sep f x y).some_spec.2
  -- For each `x y`, we define `U x y` to be `{z | f z - ε < g x y z}`,
  -- and observe this is a neighbourhood of `y`.
  let U : X → X → Set X := fun x y => { z | f z - ε < g x y z }
  have U_nhd_y : ∀ x y, U x y ∈ 𝓝 y := by
    intro x y
    refine' IsOpen.mem_nhds _ _
    · apply is_open_lt <;> continuity
      
    · rw [Set.mem_set_of_eq, w₂]
      exact sub_lt_self _ Pos
      
  -- Fixing `x` for a moment, we have a family of functions `λ y, g x y`
  -- which on different patches (the `U x y`) are greater than `f z - ε`.
  -- Taking the supremum of these functions
  -- indexed by a finite collection of patches which cover `X`
  -- will give us an element of `A` that is globally greater than `f z - ε`
  -- and still equal to `f x` at `x`.
  -- Since `X` is compact, for every `x` there is some finset `ys t`
  -- so the union of the `U x y` for `y ∈ ys x` still covers everything.
  let ys : ∀ x, Finset X := fun x => (CompactSpace.elim_nhds_subcover (U x) (U_nhd_y x)).some
  let ys_w : ∀ x, (⋃ y ∈ ys x, U x y) = ⊤ := fun x => (CompactSpace.elim_nhds_subcover (U x) (U_nhd_y x)).some_spec
  have ys_nonempty : ∀ x, (ys x).Nonempty := fun x => Set.nonempty_of_union_eq_top_of_nonempty _ _ nX (ys_w x)
  -- Thus for each `x` we have the desired `h x : A` so `f z - ε < h x z` everywhere
  -- and `h x x = f x`.
  let h : ∀ x, L := fun x =>
    ⟨(ys x).sup' (ys_nonempty x) fun y => (g x y : C(X, ℝ)), Finset.sup'_mem _ sup_mem _ _ _ fun y _ => (g x y).2⟩
  have lt_h : ∀ x z, f z - ε < h x z := by
    intro x z
    obtain ⟨y, ym, zm⟩ := Set.exists_set_mem_of_union_eq_top _ _ (ys_w x) z
    dsimp' [← h]
    simp only [← coe_fn_coe_base', ← Subtype.coe_mk, ← sup'_coe, ← Finset.sup'_apply, ← Finset.lt_sup'_iff]
    exact ⟨y, ym, zm⟩
  have h_eq : ∀ x, h x x = f x := by
    intro x
    simp only [← coe_fn_coe_base'] at w₁
    simp [← coe_fn_coe_base', ← w₁]
  -- For each `x`, we define `W x` to be `{z | h x z < f z + ε}`,
  let W : ∀ x, Set X := fun x => { z | h x z < f z + ε }
  -- This is still a neighbourhood of `x`.
  have W_nhd : ∀ x, W x ∈ 𝓝 x := by
    intro x
    refine' IsOpen.mem_nhds _ _
    · apply is_open_lt <;> continuity
      
    · dsimp' only [← W, ← Set.mem_set_of_eq]
      rw [h_eq]
      exact lt_add_of_pos_right _ Pos
      
  -- Since `X` is compact, there is some finset `ys t`
  -- so the union of the `W x` for `x ∈ xs` still covers everything.
  let xs : Finset X := (CompactSpace.elim_nhds_subcover W W_nhd).some
  let xs_w : (⋃ x ∈ xs, W x) = ⊤ := (CompactSpace.elim_nhds_subcover W W_nhd).some_spec
  have xs_nonempty : xs.nonempty := Set.nonempty_of_union_eq_top_of_nonempty _ _ nX xs_w
  -- Finally our candidate function is the infimum over `x ∈ xs` of the `h x`.
  -- This function is then globally less than `f z + ε`.
  let k : (L : Type _) :=
    ⟨xs.inf' xs_nonempty fun x => (h x : C(X, ℝ)), Finset.inf'_mem _ inf_mem _ _ _ fun x _ => (h x).2⟩
  refine' ⟨k.1, _, k.2⟩
  -- We just need to verify the bound, which we do pointwise.
  rw [dist_lt_iff Pos]
  intro z
  -- We rewrite into this particular form,
  -- so that simp lemmas about inequalities involving `finset.inf'` can fire.
  rw
    [show ∀ a b ε : ℝ, dist a b < ε ↔ a < b + ε ∧ b - ε < a by
      intros
      simp only [Metric.mem_ball, ← Real.ball_eq_Ioo, ← Set.mem_Ioo, ← and_comm]]
  fconstructor
  · dsimp' [← k]
    simp only [← Finset.inf'_lt_iff, ← ContinuousMap.inf'_apply]
    exact Set.exists_set_mem_of_union_eq_top _ _ xs_w z
    
  · dsimp' [← k]
    simp only [← Finset.lt_inf'_iff, ← ContinuousMap.inf'_apply]
    intro x xm
    apply lt_h
    

/-- The **Stone-Weierstrass Approximation Theorem**,
that a subalgebra `A` of `C(X, ℝ)`, where `X` is a compact topological space,
is dense if it separates points.
-/
theorem subalgebra_topological_closure_eq_top_of_separates_points (A : Subalgebra ℝ C(X, ℝ)) (w : A.SeparatesPoints) :
    A.topologicalClosure = ⊤ := by
  -- The closure of `A` is closed under taking `sup` and `inf`,
  -- and separates points strongly (since `A` does),
  -- so we can apply `sublattice_closure_eq_top`.
  apply SetLike.ext'
  let L := A.topological_closure
  have n : Set.Nonempty (L : Set C(X, ℝ)) := ⟨(1 : C(X, ℝ)), A.subalgebra_topological_closure A.one_mem⟩
  convert
    sublattice_closure_eq_top (L : Set C(X, ℝ)) n
      (fun f fm g gm => inf_mem_closed_subalgebra L A.is_closed_topological_closure ⟨f, fm⟩ ⟨g, gm⟩)
      (fun f fm g gm => sup_mem_closed_subalgebra L A.is_closed_topological_closure ⟨f, fm⟩ ⟨g, gm⟩)
      (Subalgebra.SeparatesPoints.strongly (Subalgebra.separates_points_monotone A.subalgebra_topological_closure w))
  · simp
    

/-- An alternative statement of the Stone-Weierstrass theorem.

If `A` is a subalgebra of `C(X, ℝ)` which separates points (and `X` is compact),
every real-valued continuous function on `X` is a uniform limit of elements of `A`.
-/
theorem continuous_map_mem_subalgebra_closure_of_separates_points (A : Subalgebra ℝ C(X, ℝ)) (w : A.SeparatesPoints)
    (f : C(X, ℝ)) : f ∈ A.topologicalClosure := by
  rw [subalgebra_topological_closure_eq_top_of_separates_points A w]
  simp

/-- An alternative statement of the Stone-Weierstrass theorem,
for those who like their epsilons.

If `A` is a subalgebra of `C(X, ℝ)` which separates points (and `X` is compact),
every real-valued continuous function on `X` is within any `ε > 0` of some element of `A`.
-/
theorem exists_mem_subalgebra_near_continuous_map_of_separates_points (A : Subalgebra ℝ C(X, ℝ)) (w : A.SeparatesPoints)
    (f : C(X, ℝ)) (ε : ℝ) (pos : 0 < ε) : ∃ g : A, ∥(g : C(X, ℝ)) - f∥ < ε := by
  have w := mem_closure_iff_frequently.mp (continuous_map_mem_subalgebra_closure_of_separates_points A w f)
  rw [metric.nhds_basis_ball.frequently_iff] at w
  obtain ⟨g, H, m⟩ := w ε Pos
  rw [Metric.mem_ball, dist_eq_norm] at H
  exact ⟨⟨g, m⟩, H⟩

/-- An alternative statement of the Stone-Weierstrass theorem,
for those who like their epsilons and don't like bundled continuous functions.

If `A` is a subalgebra of `C(X, ℝ)` which separates points (and `X` is compact),
every real-valued continuous function on `X` is within any `ε > 0` of some element of `A`.
-/
theorem exists_mem_subalgebra_near_continuous_of_separates_points (A : Subalgebra ℝ C(X, ℝ)) (w : A.SeparatesPoints)
    (f : X → ℝ) (c : Continuous f) (ε : ℝ) (pos : 0 < ε) : ∃ g : A, ∀ x, ∥g x - f x∥ < ε := by
  obtain ⟨g, b⟩ := exists_mem_subalgebra_near_continuous_map_of_separates_points A w ⟨f, c⟩ ε Pos
  use g
  rwa [norm_lt_iff _ Pos] at b

end ContinuousMap

section IsROrC

open IsROrC

-- Redefine `X`, since for the next few lemmas it need not be compact
variable {𝕜 : Type _} {X : Type _} [IsROrC 𝕜] [TopologicalSpace X]

namespace ContinuousMap

/-- A real subalgebra of `C(X, 𝕜)` is `conj_invariant`, if it contains all its conjugates. -/
def ConjInvariantSubalgebra (A : Subalgebra ℝ C(X, 𝕜)) : Prop :=
  A.map (conjAe.toAlgHom.compLeftContinuous ℝ conjCle.Continuous) ≤ A

theorem mem_conj_invariant_subalgebra {A : Subalgebra ℝ C(X, 𝕜)} (hA : ConjInvariantSubalgebra A) {f : C(X, 𝕜)}
    (hf : f ∈ A) : (conjAe.toAlgHom.compLeftContinuous ℝ conjCle.Continuous) f ∈ A :=
  hA ⟨f, hf, rfl⟩

end ContinuousMap

open ContinuousMap

/-- If a conjugation-invariant subalgebra of `C(X, 𝕜)` separates points, then the real subalgebra
of its purely real-valued elements also separates points. -/
theorem Subalgebra.SeparatesPoints.is_R_or_C_to_real {A : Subalgebra 𝕜 C(X, 𝕜)} (hA : A.SeparatesPoints)
    (hA' : ConjInvariantSubalgebra (A.restrictScalars ℝ)) :
    ((A.restrictScalars ℝ).comap (ofRealAm.compLeftContinuous ℝ continuous_of_real)).SeparatesPoints := by
  intro x₁ x₂ hx
  -- Let `f` in the subalgebra `A` separate the points `x₁`, `x₂`
  obtain ⟨_, ⟨f, hfA, rfl⟩, hf⟩ := hA hx
  let F : C(X, 𝕜) := f - const _ (f x₂)
  -- Subtract the constant `f x₂` from `f`; this is still an element of the subalgebra
  have hFA : F ∈ A := by
    refine' A.sub_mem hfA _
    convert A.smul_mem A.one_mem (f x₂)
    ext1
    simp
  -- Consider now the function `λ x, |f x - f x₂| ^ 2`
  refine' ⟨_, ⟨(⟨IsROrC.normSq, continuous_norm_sq⟩ : C(𝕜, ℝ)).comp F, _, rfl⟩, _⟩
  · -- This is also an element of the subalgebra, and takes only real values
    rw [SetLike.mem_coe, Subalgebra.mem_comap]
    convert (A.restrict_scalars ℝ).mul_mem (mem_conj_invariant_subalgebra hA' hFA) hFA
    ext1
    rw [mul_comm]
    exact (IsROrC.mul_conj _).symm
    
  · -- And it also separates the points `x₁`, `x₂`
    have : f x₁ - f x₂ ≠ 0 := sub_ne_zero.mpr hf
    simpa using this
    

variable [CompactSpace X]

/-- The Stone-Weierstrass approximation theorem, `is_R_or_C` version,
that a subalgebra `A` of `C(X, 𝕜)`, where `X` is a compact topological space and `is_R_or_C 𝕜`,
is dense if it is conjugation-invariant and separates points.
-/
theorem ContinuousMap.subalgebra_is_R_or_C_topological_closure_eq_top_of_separates_points (A : Subalgebra 𝕜 C(X, 𝕜))
    (hA : A.SeparatesPoints) (hA' : ConjInvariantSubalgebra (A.restrictScalars ℝ)) : A.topologicalClosure = ⊤ := by
  rw [Algebra.eq_top_iff]
  -- Let `I` be the natural inclusion of `C(X, ℝ)` into `C(X, 𝕜)`
  let I : C(X, ℝ) →ₗ[ℝ] C(X, 𝕜) := of_real_clm.comp_left_continuous ℝ X
  -- The main point of the proof is that its range (i.e., every real-valued function) is contained
  -- in the closure of `A`
  have key : I.range ≤ (A.to_submodule.restrict_scalars ℝ).topologicalClosure := by
    -- Let `A₀` be the subalgebra of `C(X, ℝ)` consisting of `A`'s purely real elements; it is the
    -- preimage of `A` under `I`.  In this argument we only need its submodule structure.
    let A₀ : Submodule ℝ C(X, ℝ) := (A.to_submodule.restrict_scalars ℝ).comap I
    -- By `subalgebra.separates_points.complex_to_real`, this subalgebra also separates points, so
    -- we may apply the real Stone-Weierstrass result to it.
    have SW : A₀.topological_closure = ⊤ := by
      have := subalgebra_topological_closure_eq_top_of_separates_points _ (hA.is_R_or_C_to_real hA')
      exact congr_arg Subalgebra.toSubmodule this
    rw [← Submodule.map_top, ← SW]
    -- So it suffices to prove that the image under `I` of the closure of `A₀` is contained in the
    -- closure of `A`, which follows by abstract nonsense
    have h₁ := A₀.topological_closure_map ((@of_real_clm 𝕜 _).compLeftContinuousCompact X)
    have h₂ := (A.to_submodule.restrict_scalars ℝ).map_comap_le I
    exact h₁.trans (Submodule.topological_closure_mono h₂)
  -- In particular, for a function `f` in `C(X, 𝕜)`, the real and imaginary parts of `f` are in the
  -- closure of `A`
  intro f
  let f_re : C(X, ℝ) := (⟨IsROrC.re, is_R_or_C.re_clm.continuous⟩ : C(𝕜, ℝ)).comp f
  let f_im : C(X, ℝ) := (⟨IsROrC.im, is_R_or_C.im_clm.continuous⟩ : C(𝕜, ℝ)).comp f
  have h_f_re : I f_re ∈ A.topological_closure := key ⟨f_re, rfl⟩
  have h_f_im : I f_im ∈ A.topological_closure := key ⟨f_im, rfl⟩
  -- So `f_re + I • f_im` is in the closure of `A`
  convert A.topological_closure.add_mem h_f_re (A.topological_closure.smul_mem h_f_im IsROrC.i)
  -- And this, of course, is just `f`
  ext
  apply Eq.symm
  simp [← I, ← mul_comm IsROrC.i _]

end IsROrC

