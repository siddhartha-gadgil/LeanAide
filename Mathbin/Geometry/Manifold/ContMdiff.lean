/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathbin.Geometry.Manifold.Mfderiv
import Mathbin.Geometry.Manifold.LocalInvariantProperties

/-!
# Smooth functions between smooth manifolds

We define `Cⁿ` functions between smooth manifolds, as functions which are `Cⁿ` in charts, and prove
basic properties of these notions.

## Main definitions and statements

Let `M ` and `M'` be two smooth manifolds, with respect to model with corners `I` and `I'`. Let
`f : M → M'`.

* `cont_mdiff_within_at I I' n f s x` states that the function `f` is `Cⁿ` within the set `s`
  around the point `x`.
* `cont_mdiff_at I I' n f x` states that the function `f` is `Cⁿ` around `x`.
* `cont_mdiff_on I I' n f s` states that the function `f` is `Cⁿ` on the set `s`
* `cont_mdiff I I' n f` states that the function `f` is `Cⁿ`.
* `cont_mdiff_on.comp` gives the invariance of the `Cⁿ` property under composition
* `cont_mdiff_on.cont_mdiff_on_tangent_map_within` states that the bundled derivative
  of a `Cⁿ` function in a domain is `Cᵐ` when `m + 1 ≤ n`.
* `cont_mdiff.cont_mdiff_tangent_map` states that the bundled derivative
  of a `Cⁿ` function is `Cᵐ` when `m + 1 ≤ n`.
* `cont_mdiff_iff_cont_diff` states that, for functions between vector spaces,
  manifold-smoothness is equivalent to usual smoothness.

We also give many basic properties of smooth functions between manifolds, following the API of
smooth functions between vector spaces.

## Implementation details

Many properties follow for free from the corresponding properties of functions in vector spaces,
as being `Cⁿ` is a local property invariant under the smooth groupoid. We take advantage of the
general machinery developed in `local_invariant_properties.lean` to get these properties
automatically. For instance, the fact that being `Cⁿ` does not depend on the chart one considers
is given by `lift_prop_within_at_indep_chart`.

For this to work, the definition of `cont_mdiff_within_at` and friends has to
follow definitionally the setup of local invariant properties. Still, we recast the definition
in terms of extended charts in `cont_mdiff_on_iff` and `cont_mdiff_iff`.
-/


open Set Function Filter ChartedSpace SmoothManifoldWithCorners

open TopologicalSpace Manifold

/-! ### Definition of smooth functions between manifolds -/


variable {𝕜 : Type _} [NondiscreteNormedField 𝕜]
  -- declare a smooth manifold `M` over the pair `(E, H)`.
  {E : Type _}
  [NormedGroup E] [NormedSpace 𝕜 E] {H : Type _} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) {M : Type _}
  [TopologicalSpace M] [ChartedSpace H M] [Is : SmoothManifoldWithCorners I M]
  -- declare a smooth manifold `M'` over the pair `(E', H')`.
  {E' : Type _}
  [NormedGroup E'] [NormedSpace 𝕜 E'] {H' : Type _} [TopologicalSpace H'] (I' : ModelWithCorners 𝕜 E' H') {M' : Type _}
  [TopologicalSpace M'] [ChartedSpace H' M'] [I's : SmoothManifoldWithCorners I' M']
  -- declare a smooth manifold `N` over the pair `(F, G)`.
  {F : Type _}
  [NormedGroup F] [NormedSpace 𝕜 F] {G : Type _} [TopologicalSpace G] {J : ModelWithCorners 𝕜 F G} {N : Type _}
  [TopologicalSpace N] [ChartedSpace G N] [Js : SmoothManifoldWithCorners J N]
  -- declare a smooth manifold `N'` over the pair `(F', G')`.
  {F' : Type _}
  [NormedGroup F'] [NormedSpace 𝕜 F'] {G' : Type _} [TopologicalSpace G'] {J' : ModelWithCorners 𝕜 F' G'} {N' : Type _}
  [TopologicalSpace N'] [ChartedSpace G' N'] [J's : SmoothManifoldWithCorners J' N']
  -- declare functions, sets, points and smoothness indices
  {f f₁ : M → M'}
  {s s₁ t : Set M} {x : M} {m n : WithTop ℕ}

/-- Property in the model space of a model with corners of being `C^n` within at set at a point,
when read in the model vector space. This property will be lifted to manifolds to define smooth
functions between manifolds. -/
def ContDiffWithinAtProp (n : WithTop ℕ) (f : H → H') (s : Set H) (x : H) : Prop :=
  ContDiffWithinAt 𝕜 n (I' ∘ f ∘ I.symm) (I.symm ⁻¹' s ∩ Range I) (I x)

/-- Being `Cⁿ` in the model space is a local property, invariant under smooth maps. Therefore,
it will lift nicely to manifolds. -/
theorem cont_diff_within_at_local_invariant_prop (n : WithTop ℕ) :
    (contDiffGroupoid ∞ I).LocalInvariantProp (contDiffGroupoid ∞ I') (ContDiffWithinAtProp I I' n) :=
  { is_local := by
      intro s x u f u_open xu
      have : I.symm ⁻¹' (s ∩ u) ∩ range I = I.symm ⁻¹' s ∩ range I ∩ I.symm ⁻¹' u := by
        simp only [← inter_right_comm, ← preimage_inter]
      rw [ContDiffWithinAtProp, ContDiffWithinAtProp, this]
      symm
      apply cont_diff_within_at_inter
      have : u ∈ 𝓝 (I.symm (I x)) := by
        rw [ModelWithCorners.left_inv]
        exact IsOpen.mem_nhds u_open xu
      apply ContinuousAt.preimage_mem_nhds I.continuous_symm.continuous_at this,
    right_invariance := by
      intro s x f e he hx h
      rw [ContDiffWithinAtProp] at h⊢
      have : I x = (I ∘ e.symm ∘ I.symm) (I (e x)) := by
        simp' only [← hx] with mfld_simps
      rw [this] at h
      have : I (e x) ∈ I.symm ⁻¹' e.target ∩ range I := by
        simp' only [← hx] with mfld_simps
      have := ((mem_groupoid_of_pregroupoid.2 he).2.ContDiffWithinAt this).ofLe le_top
      convert (h.comp' _ this).mono_of_mem _ using 1
      · ext y
        simp' only with mfld_simps
        
      refine'
        mem_nhds_within.mpr
          ⟨I.symm ⁻¹' e.target, e.open_target.preimage I.continuous_symm, by
            simp_rw [mem_preimage, I.left_inv, e.maps_to hx], _⟩
      mfld_set_tac,
    congr_of_forall := by
      intro s x f g h hx hf
      apply hf.congr
      · intro y hy
        simp' only with mfld_simps  at hy
        simp' only [← h, ← hy] with mfld_simps
        
      · simp' only [← hx] with mfld_simps
        ,
    left_invariance' := by
      intro s x f e' he' hs hx h
      rw [ContDiffWithinAtProp] at h⊢
      have A : (I' ∘ f ∘ I.symm) (I x) ∈ I'.symm ⁻¹' e'.source ∩ range I' := by
        simp' only [← hx] with mfld_simps
      have := ((mem_groupoid_of_pregroupoid.2 he').1.ContDiffWithinAt A).ofLe le_top
      convert this.comp _ h _
      · ext y
        simp' only with mfld_simps
        
      · intro y hy
        simp' only with mfld_simps  at hy
        simpa only [← hy] with mfld_simps using hs hy.1
         }

theorem cont_diff_within_at_prop_mono (n : WithTop ℕ) ⦃s x t⦄ ⦃f : H → H'⦄ (hts : t ⊆ s)
    (h : ContDiffWithinAtProp I I' n f s x) : ContDiffWithinAtProp I I' n f t x := by
  apply h.mono fun y hy => _
  simp' only with mfld_simps  at hy
  simp' only [← hy, ← hts _] with mfld_simps

theorem cont_diff_within_at_prop_id (x : H) : ContDiffWithinAtProp I I ∞ id Univ x := by
  simp [← ContDiffWithinAtProp]
  have : ContDiffWithinAt 𝕜 ∞ id (range I) (I x) := cont_diff_id.cont_diff_at.cont_diff_within_at
  apply this.congr fun y hy => _
  · simp' only with mfld_simps
    
  · simp' only [← ModelWithCorners.right_inv I hy] with mfld_simps
    

/-- A function is `n` times continuously differentiable within a set at a point in a manifold if
it is continuous and it is `n` times continuously differentiable in this set around this point, when
read in the preferred chart at this point. -/
def ContMdiffWithinAt (n : WithTop ℕ) (f : M → M') (s : Set M) (x : M) :=
  LiftPropWithinAt (ContDiffWithinAtProp I I' n) f s x

/-- Abbreviation for `cont_mdiff_within_at I I' ⊤ f s x`. See also documentation for `smooth`.
-/
@[reducible]
def SmoothWithinAt (f : M → M') (s : Set M) (x : M) :=
  ContMdiffWithinAt I I' ⊤ f s x

/-- A function is `n` times continuously differentiable at a point in a manifold if
it is continuous and it is `n` times continuously differentiable around this point, when
read in the preferred chart at this point. -/
def ContMdiffAt (n : WithTop ℕ) (f : M → M') (x : M) :=
  ContMdiffWithinAt I I' n f Univ x

theorem cont_mdiff_at_iff {n : WithTop ℕ} {f : M → M'} {x : M} :
    ContMdiffAt I I' n f x ↔
      ContinuousAt f x ∧
        ContDiffWithinAt 𝕜 n (extChartAt I' (f x) ∘ f ∘ (extChartAt I x).symm) (Range I) (extChartAt I x x) :=
  lift_prop_at_iff.trans <| by
    rw [ContDiffWithinAtProp, preimage_univ, univ_inter]
    rfl

/-- Abbreviation for `cont_mdiff_at I I' ⊤ f x`. See also documentation for `smooth`. -/
@[reducible]
def SmoothAt (f : M → M') (x : M) :=
  ContMdiffAt I I' ⊤ f x

/-- A function is `n` times continuously differentiable in a set of a manifold if it is continuous
and, for any pair of points, it is `n` times continuously differentiable on this set in the charts
around these points. -/
def ContMdiffOn (n : WithTop ℕ) (f : M → M') (s : Set M) :=
  ∀, ∀ x ∈ s, ∀, ContMdiffWithinAt I I' n f s x

/-- Abbreviation for `cont_mdiff_on I I' ⊤ f s`. See also documentation for `smooth`. -/
@[reducible]
def SmoothOn (f : M → M') (s : Set M) :=
  ContMdiffOn I I' ⊤ f s

/-- A function is `n` times continuously differentiable in a manifold if it is continuous
and, for any pair of points, it is `n` times continuously differentiable in the charts
around these points. -/
def ContMdiff (n : WithTop ℕ) (f : M → M') :=
  ∀ x, ContMdiffAt I I' n f x

/-- Abbreviation for `cont_mdiff I I' ⊤ f`.
Short note to work with these abbreviations: a lemma of the form `cont_mdiff_foo.bar` will
apply fine to an assumption `smooth_foo` using dot notation or normal notation.
If the consequence `bar` of the lemma involves `cont_diff`, it is still better to restate
the lemma replacing `cont_diff` with `smooth` both in the assumption and in the conclusion,
to make it possible to use `smooth` consistently.
This also applies to `smooth_at`, `smooth_on` and `smooth_within_at`.-/
@[reducible]
def Smooth (f : M → M') :=
  ContMdiff I I' ⊤ f

/-! ### Basic properties of smooth functions between manifolds -/


variable {I I'}

theorem ContMdiff.smooth (h : ContMdiff I I' ⊤ f) : Smooth I I' f :=
  h

theorem Smooth.cont_mdiff (h : Smooth I I' f) : ContMdiff I I' ⊤ f :=
  h

theorem ContMdiffOn.smooth_on (h : ContMdiffOn I I' ⊤ f s) : SmoothOn I I' f s :=
  h

theorem SmoothOn.cont_mdiff_on (h : SmoothOn I I' f s) : ContMdiffOn I I' ⊤ f s :=
  h

theorem ContMdiffAt.smooth_at (h : ContMdiffAt I I' ⊤ f x) : SmoothAt I I' f x :=
  h

theorem SmoothAt.cont_mdiff_at (h : SmoothAt I I' f x) : ContMdiffAt I I' ⊤ f x :=
  h

theorem ContMdiffWithinAt.smooth_within_at (h : ContMdiffWithinAt I I' ⊤ f s x) : SmoothWithinAt I I' f s x :=
  h

theorem SmoothWithinAt.cont_mdiff_within_at (h : SmoothWithinAt I I' f s x) : ContMdiffWithinAt I I' ⊤ f s x :=
  h

theorem ContMdiff.cont_mdiff_at (h : ContMdiff I I' n f) : ContMdiffAt I I' n f x :=
  h x

theorem Smooth.smooth_at (h : Smooth I I' f) : SmoothAt I I' f x :=
  ContMdiff.cont_mdiff_at h

theorem cont_mdiff_within_at_univ : ContMdiffWithinAt I I' n f Univ x ↔ ContMdiffAt I I' n f x :=
  Iff.rfl

theorem smooth_at_univ : SmoothWithinAt I I' f Univ x ↔ SmoothAt I I' f x :=
  cont_mdiff_within_at_univ

theorem cont_mdiff_on_univ : ContMdiffOn I I' n f Univ ↔ ContMdiff I I' n f := by
  simp only [← ContMdiffOn, ← ContMdiff, ← cont_mdiff_within_at_univ, ← forall_prop_of_true, ← mem_univ]

theorem smooth_on_univ : SmoothOn I I' f Univ ↔ Smooth I I' f :=
  cont_mdiff_on_univ

/-- One can reformulate smoothness within a set at a point as continuity within this set at this
point, and smoothness in the corresponding extended chart. -/
theorem cont_mdiff_within_at_iff :
    ContMdiffWithinAt I I' n f s x ↔
      ContinuousWithinAt f s x ∧
        ContDiffWithinAt 𝕜 n (extChartAt I' (f x) ∘ f ∘ (extChartAt I x).symm) ((extChartAt I x).symm ⁻¹' s ∩ Range I)
          (extChartAt I x x) :=
  Iff.rfl

/-- One can reformulate smoothness within a set at a point as continuity within this set at this
point, and smoothness in the corresponding extended chart. This form states smoothness of `f`
written in such a way that the set is restricted to lie within the domain/codomain of the
corresponding charts.
Even though this expression is more complicated than the one in `cont_mdiff_within_at_iff`, it is
a smaller set, but their germs at `ext_chart_at I x x` are equal. It is sometimes useful to rewrite
using this in the goal.
-/
theorem cont_mdiff_within_at_iff' :
    ContMdiffWithinAt I I' n f s x ↔
      ContinuousWithinAt f s x ∧
        ContDiffWithinAt 𝕜 n (extChartAt I' (f x) ∘ f ∘ (extChartAt I x).symm)
          ((extChartAt I x).Target ∩ (extChartAt I x).symm ⁻¹' (s ∩ f ⁻¹' (extChartAt I' (f x)).Source))
          (extChartAt I x x) :=
  by
  rw [cont_mdiff_within_at_iff, And.congr_right_iff]
  set e := extChartAt I x
  set e' := extChartAt I' (f x)
  refine' fun hc => cont_diff_within_at_congr_nhds _
  rw [← e.image_source_inter_eq', ← ext_chart_at_map_nhds_within_eq_image, ← ext_chart_at_map_nhds_within, inter_comm,
    nhds_within_inter_of_mem]
  exact hc (ext_chart_at_source_mem_nhds _ _)

/-- One can reformulate smoothness within a set at a point as continuity within this set at this
point, and smoothness in the corresponding extended chart in the target. -/
theorem cont_mdiff_within_at_iff_target :
    ContMdiffWithinAt I I' n f s x ↔
      ContinuousWithinAt f s x ∧ ContMdiffWithinAt I 𝓘(𝕜, E') n (extChartAt I' (f x) ∘ f) s x :=
  by
  simp_rw [ContMdiffWithinAt, lift_prop_within_at, ← and_assoc]
  have cont : ContinuousWithinAt f s x ∧ ContinuousWithinAt (extChartAt I' (f x) ∘ f) s x ↔ ContinuousWithinAt f s x :=
    by
    refine' ⟨fun h => h.1, fun h => ⟨h, _⟩⟩
    have h₂ := (chart_at H' (f x)).continuous_to_fun.ContinuousWithinAt (mem_chart_source _ _)
    refine' ((I'.continuous_at.comp_continuous_within_at h₂).comp' h).mono_of_mem _
    exact
      inter_mem self_mem_nhds_within
        (h.preimage_mem_nhds_within <| (chart_at _ _).open_source.mem_nhds <| mem_chart_source _ _)
  simp_rw [cont, ContDiffWithinAtProp, extChartAt, LocalEquiv.coe_trans, ModelWithCorners.to_local_equiv_coe,
    LocalHomeomorph.coe_coe, model_with_corners_self_coe, chart_at_self_eq, LocalHomeomorph.refl_apply, comp.left_id]

theorem smooth_within_at_iff :
    SmoothWithinAt I I' f s x ↔
      ContinuousWithinAt f s x ∧
        ContDiffWithinAt 𝕜 ∞ (extChartAt I' (f x) ∘ f ∘ (extChartAt I x).symm) ((extChartAt I x).symm ⁻¹' s ∩ Range I)
          (extChartAt I x x) :=
  cont_mdiff_within_at_iff

theorem smooth_within_at_iff_target :
    SmoothWithinAt I I' f s x ↔ ContinuousWithinAt f s x ∧ SmoothWithinAt I 𝓘(𝕜, E') (extChartAt I' (f x) ∘ f) s x :=
  cont_mdiff_within_at_iff_target

include Is I's

/-- One can reformulate smoothness within a set at a point as continuity within this set at this
point, and smoothness in any chart containing that point. -/
theorem cont_mdiff_within_at_iff_of_mem_source {x' : M} {y : M'} (hx : x' ∈ (chartAt H x).Source)
    (hy : f x' ∈ (chartAt H' y).Source) :
    ContMdiffWithinAt I I' n f s x' ↔
      ContinuousWithinAt f s x' ∧
        ContDiffWithinAt 𝕜 n (extChartAt I' y ∘ f ∘ (extChartAt I x).symm) ((extChartAt I x).symm ⁻¹' s ∩ Range I)
          (extChartAt I x x') :=
  (cont_diff_within_at_local_invariant_prop I I' n).lift_prop_within_at_indep_chart
    (StructureGroupoid.chart_mem_maximal_atlas _ x) hx (StructureGroupoid.chart_mem_maximal_atlas _ y) hy

theorem cont_mdiff_within_at_iff_of_mem_source' {x' : M} {y : M'} (hx : x' ∈ (chartAt H x).Source)
    (hy : f x' ∈ (chartAt H' y).Source) :
    ContMdiffWithinAt I I' n f s x' ↔
      ContinuousWithinAt f s x' ∧
        ContDiffWithinAt 𝕜 n (extChartAt I' y ∘ f ∘ (extChartAt I x).symm)
          ((extChartAt I x).Target ∩ (extChartAt I x).symm ⁻¹' (s ∩ f ⁻¹' (extChartAt I' y).Source))
          (extChartAt I x x') :=
  by
  refine' (cont_mdiff_within_at_iff_of_mem_source hx hy).trans _
  rw [← ext_chart_at_source I] at hx
  rw [← ext_chart_at_source I'] at hy
  rw [And.congr_right_iff]
  set e := extChartAt I x
  set e' := extChartAt I' (f x)
  refine' fun hc => cont_diff_within_at_congr_nhds _
  rw [← e.image_source_inter_eq', ← ext_chart_at_map_nhds_within_eq_image' I x hx, ←
    ext_chart_at_map_nhds_within' I x hx, inter_comm, nhds_within_inter_of_mem]
  exact hc ((ext_chart_at_open_source _ _).mem_nhds hy)

theorem cont_mdiff_at_iff_of_mem_source {x' : M} {y : M'} (hx : x' ∈ (chartAt H x).Source)
    (hy : f x' ∈ (chartAt H' y).Source) :
    ContMdiffAt I I' n f x' ↔
      ContinuousAt f x' ∧
        ContDiffWithinAt 𝕜 n (extChartAt I' y ∘ f ∘ (extChartAt I x).symm) (Range I) (extChartAt I x x') :=
  (cont_mdiff_within_at_iff_of_mem_source hx hy).trans <| by
    rw [continuous_within_at_univ, preimage_univ, univ_inter]

omit I's

theorem cont_mdiff_at_ext_chart_at' {x' : M} (h : x' ∈ (chartAt H x).Source) :
    ContMdiffAt I 𝓘(𝕜, E) n (extChartAt I x) x' := by
  refine' (cont_mdiff_at_iff_of_mem_source h (mem_chart_source _ _)).mpr _
  rw [← ext_chart_at_source I] at h
  refine' ⟨ext_chart_at_continuous_at' _ _ h, _⟩
  refine' cont_diff_within_at_id.congr_of_eventually_eq _ _
  · refine' eventually_eq_of_mem (ext_chart_at_target_mem_nhds_within' I x h) fun x₂ hx₂ => _
    simp_rw [Function.comp_applyₓ, (extChartAt I x).right_inv hx₂]
    rfl
    
  simp_rw [Function.comp_applyₓ, (extChartAt I x).right_inv ((extChartAt I x).MapsTo h)]
  rfl

theorem cont_mdiff_at_ext_chart_at : ContMdiffAt I 𝓘(𝕜, E) n (extChartAt I x) x :=
  cont_mdiff_at_ext_chart_at' <| mem_chart_source H x

include I's

/-- One can reformulate smoothness on a set as continuity on this set, and smoothness in any
extended chart. -/
theorem cont_mdiff_on_iff :
    ContMdiffOn I I' n f s ↔
      ContinuousOn f s ∧
        ∀ (x : M) (y : M'),
          ContDiffOn 𝕜 n (extChartAt I' y ∘ f ∘ (extChartAt I x).symm)
            ((extChartAt I x).Target ∩ (extChartAt I x).symm ⁻¹' (s ∩ f ⁻¹' (extChartAt I' y).Source)) :=
  by
  constructor
  · intro h
    refine' ⟨fun x hx => (h x hx).1, fun x y z hz => _⟩
    simp' only with mfld_simps  at hz
    let w := (extChartAt I x).symm z
    have : w ∈ s := by
      simp' only [← w, ← hz] with mfld_simps
    specialize h w this
    have w1 : w ∈ (chart_at H x).Source := by
      simp' only [← w, ← hz] with mfld_simps
    have w2 : f w ∈ (chart_at H' y).Source := by
      simp' only [← w, ← hz] with mfld_simps
    convert ((cont_mdiff_within_at_iff_of_mem_source w1 w2).mp h).2.mono _
    · simp' only [← w, ← hz] with mfld_simps
      
    · mfld_set_tac
      
    
  · rintro ⟨hcont, hdiff⟩ x hx
    refine' ((cont_diff_within_at_local_invariant_prop I I' n).lift_prop_within_at_iff <| hcont x hx).mpr _
    dsimp' [← ContDiffWithinAtProp]
    convert
      hdiff x (f x) (extChartAt I x x)
        (by
          simp' only [← hx] with mfld_simps) using
      1
    mfld_set_tac
    

/-- One can reformulate smoothness on a set as continuity on this set, and smoothness in any
extended chart in the target. -/
theorem cont_mdiff_on_iff_target :
    ContMdiffOn I I' n f s ↔
      ContinuousOn f s ∧
        ∀ y : M', ContMdiffOn I 𝓘(𝕜, E') n (extChartAt I' y ∘ f) (s ∩ f ⁻¹' (extChartAt I' y).Source) :=
  by
  inhabit E'
  simp only [← cont_mdiff_on_iff, ← ModelWithCorners.source_eq, ← chart_at_self_eq, ← LocalHomeomorph.refl_local_equiv,
    ← LocalEquiv.refl_trans, ← extChartAt.equations._eqn_1, ← Set.preimage_univ, ← Set.inter_univ, ←
    And.congr_right_iff]
  intro h
  constructor
  · refine' fun h' y => ⟨_, fun x _ => h' x y⟩
    have h'' : ContinuousOn _ univ := (ModelWithCorners.continuous I').ContinuousOn
    convert (h''.comp' (chart_at H' y).continuous_to_fun).comp' h
    simp
    
  · exact fun h' x y => (h' y).2 x default
    

theorem smooth_on_iff :
    SmoothOn I I' f s ↔
      ContinuousOn f s ∧
        ∀ (x : M) (y : M'),
          ContDiffOn 𝕜 ⊤ (extChartAt I' y ∘ f ∘ (extChartAt I x).symm)
            ((extChartAt I x).Target ∩ (extChartAt I x).symm ⁻¹' (s ∩ f ⁻¹' (extChartAt I' y).Source)) :=
  cont_mdiff_on_iff

theorem smooth_on_iff_target :
    SmoothOn I I' f s ↔
      ContinuousOn f s ∧ ∀ y : M', SmoothOn I 𝓘(𝕜, E') (extChartAt I' y ∘ f) (s ∩ f ⁻¹' (extChartAt I' y).Source) :=
  cont_mdiff_on_iff_target

/-- One can reformulate smoothness as continuity and smoothness in any extended chart. -/
theorem cont_mdiff_iff :
    ContMdiff I I' n f ↔
      Continuous f ∧
        ∀ (x : M) (y : M'),
          ContDiffOn 𝕜 n (extChartAt I' y ∘ f ∘ (extChartAt I x).symm)
            ((extChartAt I x).Target ∩ (extChartAt I x).symm ⁻¹' (f ⁻¹' (extChartAt I' y).Source)) :=
  by
  simp [cont_mdiff_on_univ, ← cont_mdiff_on_iff, ← continuous_iff_continuous_on_univ]

/-- One can reformulate smoothness as continuity and smoothness in any extended chart in the
target. -/
theorem cont_mdiff_iff_target :
    ContMdiff I I' n f ↔
      Continuous f ∧ ∀ y : M', ContMdiffOn I 𝓘(𝕜, E') n (extChartAt I' y ∘ f) (f ⁻¹' (extChartAt I' y).Source) :=
  by
  rw [← cont_mdiff_on_univ, cont_mdiff_on_iff_target]
  simp [← continuous_iff_continuous_on_univ]

theorem smooth_iff :
    Smooth I I' f ↔
      Continuous f ∧
        ∀ (x : M) (y : M'),
          ContDiffOn 𝕜 ⊤ (extChartAt I' y ∘ f ∘ (extChartAt I x).symm)
            ((extChartAt I x).Target ∩ (extChartAt I x).symm ⁻¹' (f ⁻¹' (extChartAt I' y).Source)) :=
  cont_mdiff_iff

theorem smooth_iff_target :
    Smooth I I' f ↔
      Continuous f ∧ ∀ y : M', SmoothOn I 𝓘(𝕜, E') (extChartAt I' y ∘ f) (f ⁻¹' (extChartAt I' y).Source) :=
  cont_mdiff_iff_target

omit Is I's

/-! ### Deducing smoothness from higher smoothness -/


theorem ContMdiffWithinAt.of_le (hf : ContMdiffWithinAt I I' n f s x) (le : m ≤ n) : ContMdiffWithinAt I I' m f s x :=
  ⟨hf.1, hf.2.ofLe le⟩

theorem ContMdiffAt.of_le (hf : ContMdiffAt I I' n f x) (le : m ≤ n) : ContMdiffAt I I' m f x :=
  ContMdiffWithinAt.of_le hf le

theorem ContMdiffOn.of_le (hf : ContMdiffOn I I' n f s) (le : m ≤ n) : ContMdiffOn I I' m f s := fun x hx =>
  (hf x hx).ofLe le

theorem ContMdiff.of_le (hf : ContMdiff I I' n f) (le : m ≤ n) : ContMdiff I I' m f := fun x => (hf x).ofLe le

/-! ### Deducing smoothness from smoothness one step beyond -/


theorem ContMdiffWithinAt.of_succ {n : ℕ} (h : ContMdiffWithinAt I I' n.succ f s x) : ContMdiffWithinAt I I' n f s x :=
  h.ofLe (WithTop.coe_le_coe.2 (Nat.le_succₓ n))

theorem ContMdiffAt.of_succ {n : ℕ} (h : ContMdiffAt I I' n.succ f x) : ContMdiffAt I I' n f x :=
  ContMdiffWithinAt.of_succ h

theorem ContMdiffOn.of_succ {n : ℕ} (h : ContMdiffOn I I' n.succ f s) : ContMdiffOn I I' n f s := fun x hx =>
  (h x hx).of_succ

theorem ContMdiff.of_succ {n : ℕ} (h : ContMdiff I I' n.succ f) : ContMdiff I I' n f := fun x => (h x).of_succ

/-! ### Deducing continuity from smoothness-/


theorem ContMdiffWithinAt.continuous_within_at (hf : ContMdiffWithinAt I I' n f s x) : ContinuousWithinAt f s x :=
  hf.1

theorem ContMdiffAt.continuous_at (hf : ContMdiffAt I I' n f x) : ContinuousAt f x :=
  (continuous_within_at_univ _ _).1 <| ContMdiffWithinAt.continuous_within_at hf

theorem ContMdiffOn.continuous_on (hf : ContMdiffOn I I' n f s) : ContinuousOn f s := fun x hx =>
  (hf x hx).ContinuousWithinAt

theorem ContMdiff.continuous (hf : ContMdiff I I' n f) : Continuous f :=
  continuous_iff_continuous_at.2 fun x => (hf x).ContinuousAt

/-! ### Deducing differentiability from smoothness -/


theorem ContMdiffWithinAt.mdifferentiable_within_at (hf : ContMdiffWithinAt I I' n f s x) (hn : 1 ≤ n) :
    MdifferentiableWithinAt I I' f s x := by
  suffices h : MdifferentiableWithinAt I I' f (s ∩ f ⁻¹' (extChartAt I' (f x)).Source) x
  · rwa [mdifferentiable_within_at_inter'] at h
    apply hf.1.preimage_mem_nhds_within
    exact IsOpen.mem_nhds (ext_chart_at_open_source I' (f x)) (mem_ext_chart_source I' (f x))
    
  rw [mdifferentiable_within_at_iff]
  exact
    ⟨hf.1.mono (inter_subset_left _ _),
      (hf.2.DifferentiableWithinAt hn).mono
        (by
          mfld_set_tac)⟩

theorem ContMdiffAt.mdifferentiable_at (hf : ContMdiffAt I I' n f x) (hn : 1 ≤ n) : MdifferentiableAt I I' f x :=
  mdifferentiable_within_at_univ.1 <| ContMdiffWithinAt.mdifferentiable_within_at hf hn

theorem ContMdiffOn.mdifferentiable_on (hf : ContMdiffOn I I' n f s) (hn : 1 ≤ n) : MdifferentiableOn I I' f s :=
  fun x hx => (hf x hx).MdifferentiableWithinAt hn

theorem ContMdiff.mdifferentiable (hf : ContMdiff I I' n f) (hn : 1 ≤ n) : Mdifferentiable I I' f := fun x =>
  (hf x).MdifferentiableAt hn

theorem Smooth.mdifferentiable (hf : Smooth I I' f) : Mdifferentiable I I' f :=
  ContMdiff.mdifferentiable hf le_top

theorem Smooth.mdifferentiable_at (hf : Smooth I I' f) : MdifferentiableAt I I' f x :=
  hf.Mdifferentiable x

theorem Smooth.mdifferentiable_within_at (hf : Smooth I I' f) : MdifferentiableWithinAt I I' f s x :=
  hf.MdifferentiableAt.MdifferentiableWithinAt

/-! ### `C^∞` smoothness -/


theorem cont_mdiff_within_at_top : SmoothWithinAt I I' f s x ↔ ∀ n : ℕ, ContMdiffWithinAt I I' n f s x :=
  ⟨fun h n => ⟨h.1, cont_diff_within_at_top.1 h.2 n⟩, fun H => ⟨(H 0).1, cont_diff_within_at_top.2 fun n => (H n).2⟩⟩

theorem cont_mdiff_at_top : SmoothAt I I' f x ↔ ∀ n : ℕ, ContMdiffAt I I' n f x :=
  cont_mdiff_within_at_top

theorem cont_mdiff_on_top : SmoothOn I I' f s ↔ ∀ n : ℕ, ContMdiffOn I I' n f s :=
  ⟨fun h n => h.ofLe le_top, fun h x hx => cont_mdiff_within_at_top.2 fun n => h n x hx⟩

theorem cont_mdiff_top : Smooth I I' f ↔ ∀ n : ℕ, ContMdiff I I' n f :=
  ⟨fun h n => h.ofLe le_top, fun h x => cont_mdiff_within_at_top.2 fun n => h n x⟩

theorem cont_mdiff_within_at_iff_nat :
    ContMdiffWithinAt I I' n f s x ↔ ∀ m : ℕ, (m : WithTop ℕ) ≤ n → ContMdiffWithinAt I I' m f s x := by
  refine' ⟨fun h m hm => h.ofLe hm, fun h => _⟩
  cases n
  · exact cont_mdiff_within_at_top.2 fun n => h n le_top
    
  · exact h n le_rfl
    

/-! ### Restriction to a smaller set -/


theorem ContMdiffWithinAt.mono (hf : ContMdiffWithinAt I I' n f s x) (hts : t ⊆ s) : ContMdiffWithinAt I I' n f t x :=
  StructureGroupoid.LocalInvariantProp.lift_prop_within_at_mono (cont_diff_within_at_prop_mono I I' n) hf hts

theorem ContMdiffAt.cont_mdiff_within_at (hf : ContMdiffAt I I' n f x) : ContMdiffWithinAt I I' n f s x :=
  ContMdiffWithinAt.mono hf (subset_univ _)

theorem SmoothAt.smooth_within_at (hf : SmoothAt I I' f x) : SmoothWithinAt I I' f s x :=
  ContMdiffAt.cont_mdiff_within_at hf

theorem ContMdiffOn.mono (hf : ContMdiffOn I I' n f s) (hts : t ⊆ s) : ContMdiffOn I I' n f t := fun x hx =>
  (hf x (hts hx)).mono hts

theorem ContMdiff.cont_mdiff_on (hf : ContMdiff I I' n f) : ContMdiffOn I I' n f s := fun x hx =>
  (hf x).ContMdiffWithinAt

theorem Smooth.smooth_on (hf : Smooth I I' f) : SmoothOn I I' f s :=
  ContMdiff.cont_mdiff_on hf

theorem cont_mdiff_within_at_inter' (ht : t ∈ 𝓝[s] x) :
    ContMdiffWithinAt I I' n f (s ∩ t) x ↔ ContMdiffWithinAt I I' n f s x :=
  (cont_diff_within_at_local_invariant_prop I I' n).lift_prop_within_at_inter' ht

theorem cont_mdiff_within_at_inter (ht : t ∈ 𝓝 x) :
    ContMdiffWithinAt I I' n f (s ∩ t) x ↔ ContMdiffWithinAt I I' n f s x :=
  (cont_diff_within_at_local_invariant_prop I I' n).lift_prop_within_at_inter ht

theorem ContMdiffWithinAt.cont_mdiff_at (h : ContMdiffWithinAt I I' n f s x) (ht : s ∈ 𝓝 x) : ContMdiffAt I I' n f x :=
  (cont_diff_within_at_local_invariant_prop I I' n).lift_prop_at_of_lift_prop_within_at h ht

theorem SmoothWithinAt.smooth_at (h : SmoothWithinAt I I' f s x) (ht : s ∈ 𝓝 x) : SmoothAt I I' f x :=
  ContMdiffWithinAt.cont_mdiff_at h ht

include Is

theorem cont_mdiff_on_ext_chart_at : ContMdiffOn I 𝓘(𝕜, E) n (extChartAt I x) (chartAt H x).Source := fun x' hx' =>
  (cont_mdiff_at_ext_chart_at' hx').ContMdiffWithinAt

include I's

/-- A function is `C^n` within a set at a point, for `n : ℕ`, if and only if it is `C^n` on
a neighborhood of this point. -/
theorem cont_mdiff_within_at_iff_cont_mdiff_on_nhds {n : ℕ} :
    ContMdiffWithinAt I I' n f s x ↔ ∃ u ∈ 𝓝[insert x s] x, ContMdiffOn I I' n f u := by
  constructor
  · intro h
    -- the property is true in charts. We will pull such a good neighborhood in the chart to the
    -- manifold. For this, we need to restrict to a small enough set where everything makes sense
    obtain ⟨o, o_open, xo, ho, h'o⟩ :
      ∃ o : Set M, IsOpen o ∧ x ∈ o ∧ o ⊆ (chart_at H x).Source ∧ o ∩ s ⊆ f ⁻¹' (chart_at H' (f x)).Source := by
      have : (chart_at H' (f x)).Source ∈ 𝓝 (f x) :=
        IsOpen.mem_nhds (LocalHomeomorph.open_source _) (mem_chart_source H' (f x))
      rcases mem_nhds_within.1 (h.1.preimage_mem_nhds_within this) with ⟨u, u_open, xu, hu⟩
      refine' ⟨u ∩ (chart_at H x).Source, _, ⟨xu, mem_chart_source _ _⟩, _, _⟩
      · exact IsOpen.inter u_open (LocalHomeomorph.open_source _)
        
      · intro y hy
        exact hy.2
        
      · intro y hy
        exact hu ⟨hy.1.1, hy.2⟩
        
    have h' : ContMdiffWithinAt I I' n f (s ∩ o) x := h.mono (inter_subset_left _ _)
    simp only [← ContMdiffWithinAt, ← lift_prop_within_at, ← ContDiffWithinAtProp] at h'
    -- let `u` be a good neighborhood in the chart where the function is smooth
    rcases h.2.ContDiffOn le_rfl with ⟨u, u_nhds, u_subset, hu⟩
    -- pull it back to the manifold, and intersect with a suitable neighborhood of `x`, to get the
    -- desired good neighborhood `v`.
    let v := insert x s ∩ o ∩ extChartAt I x ⁻¹' u
    have v_incl : v ⊆ (chart_at H x).Source := fun y hy => ho hy.1.2
    have v_incl' : ∀, ∀ y ∈ v, ∀, f y ∈ (chart_at H' (f x)).Source := by
      intro y hy
      rcases hy.1.1 with (rfl | h')
      · simp' only with mfld_simps
        
      · apply h'o ⟨hy.1.2, h'⟩
        
    refine' ⟨v, _, _⟩
    show v ∈ 𝓝[insert x s] x
    · rw [nhds_within_restrict _ xo o_open]
      refine' Filter.inter_mem self_mem_nhds_within _
      suffices : u ∈ 𝓝[extChartAt I x '' (insert x s ∩ o)] extChartAt I x x
      exact (ext_chart_at_continuous_at I x).ContinuousWithinAt.preimage_mem_nhds_within' this
      apply nhds_within_mono _ _ u_nhds
      rw [image_subset_iff]
      intro y hy
      rcases hy.1 with (rfl | h')
      · simp' only [← mem_insert_iff] with mfld_simps
        
      · simp' only [← mem_insert_iff, ← ho hy.2, ← h', ← h'o ⟨hy.2, h'⟩] with mfld_simps
        
      
    show ContMdiffOn I I' n f v
    · intro y hy
      have : ContinuousWithinAt f v y := by
        apply
          (((ext_chart_at_continuous_on_symm I' (f x) _ _).comp' (hu _ hy.2).ContinuousWithinAt).comp'
              (ext_chart_at_continuous_on I x _ _)).congr_mono
        · intro z hz
          simp' only [← v_incl hz, ← v_incl' z hz] with mfld_simps
          
        · intro z hz
          simp' only [← v_incl hz, ← v_incl' z hz] with mfld_simps
          exact hz.2
          
        · simp' only [← v_incl hy, ← v_incl' y hy] with mfld_simps
          
        · simp' only [← v_incl hy, ← v_incl' y hy] with mfld_simps
          
        · simp' only [← v_incl hy] with mfld_simps
          
      refine' (cont_mdiff_within_at_iff_of_mem_source' (v_incl hy) (v_incl' y hy)).mpr ⟨this, _⟩
      · apply hu.mono
        · intro z hz
          simp' only [← v] with mfld_simps  at hz
          have : I ((chart_at H x) ((chart_at H x).symm (I.symm z))) ∈ u := by
            simp only [← hz]
          simpa only [← hz] with mfld_simps using this
          
        · have exty : I (chart_at H x y) ∈ u := hy.2
          simp' only [← v_incl hy, ← v_incl' y hy, ← exty, ← hy.1.1, ← hy.1.2] with mfld_simps
          
        
      
    
  · rintro ⟨u, u_nhds, hu⟩
    have : ContMdiffWithinAt I I' (↑n) f (insert x s ∩ u) x := by
      have : x ∈ insert x s := mem_insert x s
      exact hu.mono (inter_subset_right _ _) _ ⟨this, mem_of_mem_nhds_within this u_nhds⟩
    rw [cont_mdiff_within_at_inter' u_nhds] at this
    exact this.mono (subset_insert x s)
    

/-- A function is `C^n` at a point, for `n : ℕ`, if and only if it is `C^n` on
a neighborhood of this point. -/
theorem cont_mdiff_at_iff_cont_mdiff_on_nhds {n : ℕ} : ContMdiffAt I I' n f x ↔ ∃ u ∈ 𝓝 x, ContMdiffOn I I' n f u := by
  simp [cont_mdiff_within_at_univ, ← cont_mdiff_within_at_iff_cont_mdiff_on_nhds, ← nhds_within_univ]

omit Is I's

/-! ### Congruence lemmas -/


theorem ContMdiffWithinAt.congr (h : ContMdiffWithinAt I I' n f s x) (h₁ : ∀, ∀ y ∈ s, ∀, f₁ y = f y)
    (hx : f₁ x = f x) : ContMdiffWithinAt I I' n f₁ s x :=
  (cont_diff_within_at_local_invariant_prop I I' n).lift_prop_within_at_congr h h₁ hx

theorem cont_mdiff_within_at_congr (h₁ : ∀, ∀ y ∈ s, ∀, f₁ y = f y) (hx : f₁ x = f x) :
    ContMdiffWithinAt I I' n f₁ s x ↔ ContMdiffWithinAt I I' n f s x :=
  (cont_diff_within_at_local_invariant_prop I I' n).lift_prop_within_at_congr_iff h₁ hx

theorem ContMdiffWithinAt.congr_of_eventually_eq (h : ContMdiffWithinAt I I' n f s x) (h₁ : f₁ =ᶠ[𝓝[s] x] f)
    (hx : f₁ x = f x) : ContMdiffWithinAt I I' n f₁ s x :=
  (cont_diff_within_at_local_invariant_prop I I' n).lift_prop_within_at_congr_of_eventually_eq h h₁ hx

theorem Filter.EventuallyEq.cont_mdiff_within_at_iff (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) :
    ContMdiffWithinAt I I' n f₁ s x ↔ ContMdiffWithinAt I I' n f s x :=
  (cont_diff_within_at_local_invariant_prop I I' n).lift_prop_within_at_congr_iff_of_eventually_eq h₁ hx

theorem ContMdiffAt.congr_of_eventually_eq (h : ContMdiffAt I I' n f x) (h₁ : f₁ =ᶠ[𝓝 x] f) : ContMdiffAt I I' n f₁ x :=
  (cont_diff_within_at_local_invariant_prop I I' n).lift_prop_at_congr_of_eventually_eq h h₁

theorem Filter.EventuallyEq.cont_mdiff_at_iff (h₁ : f₁ =ᶠ[𝓝 x] f) : ContMdiffAt I I' n f₁ x ↔ ContMdiffAt I I' n f x :=
  (cont_diff_within_at_local_invariant_prop I I' n).lift_prop_at_congr_iff_of_eventually_eq h₁

theorem ContMdiffOn.congr (h : ContMdiffOn I I' n f s) (h₁ : ∀, ∀ y ∈ s, ∀, f₁ y = f y) : ContMdiffOn I I' n f₁ s :=
  (cont_diff_within_at_local_invariant_prop I I' n).lift_prop_on_congr h h₁

theorem cont_mdiff_on_congr (h₁ : ∀, ∀ y ∈ s, ∀, f₁ y = f y) : ContMdiffOn I I' n f₁ s ↔ ContMdiffOn I I' n f s :=
  (cont_diff_within_at_local_invariant_prop I I' n).lift_prop_on_congr_iff h₁

/-! ### Locality -/


/-- Being `C^n` is a local property. -/
theorem cont_mdiff_on_of_locally_cont_mdiff_on
    (h : ∀, ∀ x ∈ s, ∀, ∃ u, IsOpen u ∧ x ∈ u ∧ ContMdiffOn I I' n f (s ∩ u)) : ContMdiffOn I I' n f s :=
  (cont_diff_within_at_local_invariant_prop I I' n).lift_prop_on_of_locally_lift_prop_on h

theorem cont_mdiff_of_locally_cont_mdiff_on (h : ∀ x, ∃ u, IsOpen u ∧ x ∈ u ∧ ContMdiffOn I I' n f u) :
    ContMdiff I I' n f :=
  (cont_diff_within_at_local_invariant_prop I I' n).lift_prop_of_locally_lift_prop_on h

/-! ### Smoothness of the composition of smooth functions between manifolds -/


section Composition

variable {E'' : Type _} [NormedGroup E''] [NormedSpace 𝕜 E''] {H'' : Type _} [TopologicalSpace H'']
  {I'' : ModelWithCorners 𝕜 E'' H''} {M'' : Type _} [TopologicalSpace M''] [ChartedSpace H'' M'']

/-- The composition of `C^n` functions within domains at points is `C^n`. -/
theorem ContMdiffWithinAt.comp {t : Set M'} {g : M' → M''} (x : M) (hg : ContMdiffWithinAt I' I'' n g t (f x))
    (hf : ContMdiffWithinAt I I' n f s x) (st : MapsTo f s t) : ContMdiffWithinAt I I'' n (g ∘ f) s x := by
  rw [cont_mdiff_within_at_iff] at hg hf⊢
  refine' ⟨hg.1.comp hf.1 st, _⟩
  set e := extChartAt I x
  set e' := extChartAt I' (f x)
  set e'' := extChartAt I'' (g (f x))
  have : e' (f x) = (writtenInExtChartAt I I' x f) (e x) := by
    simp' only [← e, ← e'] with mfld_simps
  rw [this] at hg
  have A :
    ∀ᶠ y in 𝓝[e.symm ⁻¹' s ∩ range I] e x,
      y ∈ e.target ∧ f (e.symm y) ∈ t ∧ f (e.symm y) ∈ e'.source ∧ g (f (e.symm y)) ∈ e''.source :=
    by
    simp only [ext_chart_at_map_nhds_within, ← eventually_map]
    filter_upwards [hf.1.Tendsto (ext_chart_at_source_mem_nhds I' (f x)),
      (hg.1.comp hf.1 st).Tendsto (ext_chart_at_source_mem_nhds I'' (g (f x))),
      inter_mem_nhds_within s (ext_chart_at_source_mem_nhds I x)]
    rintro x' (hfx' : f x' ∈ _) (hgfx' : g (f x') ∈ _) ⟨hx's, hx'⟩
    simp only [← e.map_source hx', ← true_andₓ, ← e.left_inv hx', ← st hx's, *]
  refine'
    ((hg.2.comp _ (hf.2.mono (inter_subset_right _ _)) (inter_subset_left _ _)).mono_of_mem
          (inter_mem _ self_mem_nhds_within)).congr_of_eventually_eq
      _ _
  · filter_upwards [A]
    rintro x' ⟨hx', ht, hfx', hgfx'⟩
    simp only [*, ← mem_preimage, ← writtenInExtChartAt, ← (· ∘ ·), ← mem_inter_eq, ← e'.left_inv, ← true_andₓ]
    exact mem_range_self _
    
  · filter_upwards [A]
    rintro x' ⟨hx', ht, hfx', hgfx'⟩
    simp only [*, ← (· ∘ ·), ← writtenInExtChartAt, ← e'.left_inv]
    
  · simp only [← writtenInExtChartAt, ← (· ∘ ·), ← mem_ext_chart_source, ← e.left_inv, ← e'.left_inv]
    

/-- The composition of `C^n` functions on domains is `C^n`. -/
theorem ContMdiffOn.comp {t : Set M'} {g : M' → M''} (hg : ContMdiffOn I' I'' n g t) (hf : ContMdiffOn I I' n f s)
    (st : s ⊆ f ⁻¹' t) : ContMdiffOn I I'' n (g ∘ f) s := fun x hx => (hg _ (st hx)).comp x (hf x hx) st

/-- The composition of `C^n` functions on domains is `C^n`. -/
theorem ContMdiffOn.comp' {t : Set M'} {g : M' → M''} (hg : ContMdiffOn I' I'' n g t) (hf : ContMdiffOn I I' n f s) :
    ContMdiffOn I I'' n (g ∘ f) (s ∩ f ⁻¹' t) :=
  hg.comp (hf.mono (inter_subset_left _ _)) (inter_subset_right _ _)

/-- The composition of `C^n` functions is `C^n`. -/
theorem ContMdiff.comp {g : M' → M''} (hg : ContMdiff I' I'' n g) (hf : ContMdiff I I' n f) :
    ContMdiff I I'' n (g ∘ f) := by
  rw [← cont_mdiff_on_univ] at hf hg⊢
  exact hg.comp hf subset_preimage_univ

/-- The composition of `C^n` functions within domains at points is `C^n`. -/
theorem ContMdiffWithinAt.comp' {t : Set M'} {g : M' → M''} (x : M) (hg : ContMdiffWithinAt I' I'' n g t (f x))
    (hf : ContMdiffWithinAt I I' n f s x) : ContMdiffWithinAt I I'' n (g ∘ f) (s ∩ f ⁻¹' t) x :=
  hg.comp x (hf.mono (inter_subset_left _ _)) (inter_subset_right _ _)

/-- `g ∘ f` is `C^n` within `s` at `x` if `g` is `C^n` at `f x` and
`f` is `C^n` within `s` at `x`. -/
theorem ContMdiffAt.comp_cont_mdiff_within_at {g : M' → M''} (x : M) (hg : ContMdiffAt I' I'' n g (f x))
    (hf : ContMdiffWithinAt I I' n f s x) : ContMdiffWithinAt I I'' n (g ∘ f) s x :=
  hg.comp x hf (maps_to_univ _ _)

/-- The composition of `C^n` functions at points is `C^n`. -/
theorem ContMdiffAt.comp {g : M' → M''} (x : M) (hg : ContMdiffAt I' I'' n g (f x)) (hf : ContMdiffAt I I' n f x) :
    ContMdiffAt I I'' n (g ∘ f) x :=
  hg.comp x hf (maps_to_univ _ _)

theorem ContMdiff.comp_cont_mdiff_on {f : M → M'} {g : M' → M''} {s : Set M} (hg : ContMdiff I' I'' n g)
    (hf : ContMdiffOn I I' n f s) : ContMdiffOn I I'' n (g ∘ f) s :=
  hg.ContMdiffOn.comp hf Set.subset_preimage_univ

theorem Smooth.comp_smooth_on {f : M → M'} {g : M' → M''} {s : Set M} (hg : Smooth I' I'' g) (hf : SmoothOn I I' f s) :
    SmoothOn I I'' (g ∘ f) s :=
  hg.SmoothOn.comp hf Set.subset_preimage_univ

theorem ContMdiffOn.comp_cont_mdiff {t : Set M'} {g : M' → M''} (hg : ContMdiffOn I' I'' n g t)
    (hf : ContMdiff I I' n f) (ht : ∀ x, f x ∈ t) : ContMdiff I I'' n (g ∘ f) :=
  cont_mdiff_on_univ.mp <| hg.comp hf.ContMdiffOn fun x _ => ht x

theorem SmoothOn.comp_smooth {t : Set M'} {g : M' → M''} (hg : SmoothOn I' I'' g t) (hf : Smooth I I' f)
    (ht : ∀ x, f x ∈ t) : Smooth I I'' (g ∘ f) :=
  hg.comp_cont_mdiff hf ht

end Composition

/-! ### Atlas members are smooth -/


section Atlas

variable {e : LocalHomeomorph M H}

include Is

/-- An atlas member is `C^n` for any `n`. -/
theorem cont_mdiff_on_of_mem_maximal_atlas (h : e ∈ MaximalAtlas I M) : ContMdiffOn I I n e e.Source :=
  ContMdiffOn.of_le
    ((cont_diff_within_at_local_invariant_prop I I ∞).lift_prop_on_of_mem_maximal_atlas (cont_diff_within_at_prop_id I)
      h)
    le_top

/-- The inverse of an atlas member is `C^n` for any `n`. -/
theorem cont_mdiff_on_symm_of_mem_maximal_atlas (h : e ∈ MaximalAtlas I M) : ContMdiffOn I I n e.symm e.Target :=
  ContMdiffOn.of_le
    ((cont_diff_within_at_local_invariant_prop I I ∞).lift_prop_on_symm_of_mem_maximal_atlas
      (cont_diff_within_at_prop_id I) h)
    le_top

theorem cont_mdiff_on_chart : ContMdiffOn I I n (chartAt H x) (chartAt H x).Source :=
  cont_mdiff_on_of_mem_maximal_atlas ((contDiffGroupoid ⊤ I).chart_mem_maximal_atlas x)

theorem cont_mdiff_on_chart_symm : ContMdiffOn I I n (chartAt H x).symm (chartAt H x).Target :=
  cont_mdiff_on_symm_of_mem_maximal_atlas ((contDiffGroupoid ⊤ I).chart_mem_maximal_atlas x)

end Atlas

/-! ### The identity is smooth -/


section id

theorem cont_mdiff_id : ContMdiff I I n (id : M → M) :=
  ContMdiff.of_le ((cont_diff_within_at_local_invariant_prop I I ∞).lift_prop_id (cont_diff_within_at_prop_id I)) le_top

theorem smooth_id : Smooth I I (id : M → M) :=
  cont_mdiff_id

theorem cont_mdiff_on_id : ContMdiffOn I I n (id : M → M) s :=
  cont_mdiff_id.ContMdiffOn

theorem smooth_on_id : SmoothOn I I (id : M → M) s :=
  cont_mdiff_on_id

theorem cont_mdiff_at_id : ContMdiffAt I I n (id : M → M) x :=
  cont_mdiff_id.ContMdiffAt

theorem smooth_at_id : SmoothAt I I (id : M → M) x :=
  cont_mdiff_at_id

theorem cont_mdiff_within_at_id : ContMdiffWithinAt I I n (id : M → M) s x :=
  cont_mdiff_at_id.ContMdiffWithinAt

theorem smooth_within_at_id : SmoothWithinAt I I (id : M → M) s x :=
  cont_mdiff_within_at_id

end id

/-! ### Constants are smooth -/


section id

variable {c : M'}

theorem cont_mdiff_const : ContMdiff I I' n fun x : M => c := by
  intro x
  refine' ⟨continuous_within_at_const, _⟩
  simp only [← ContDiffWithinAtProp, ← (· ∘ ·)]
  exact cont_diff_within_at_const

@[to_additive]
theorem cont_mdiff_one [One M'] : ContMdiff I I' n (1 : M → M') := by
  simp only [← Pi.one_def, ← cont_mdiff_const]

theorem smooth_const : Smooth I I' fun x : M => c :=
  cont_mdiff_const

@[to_additive]
theorem smooth_one [One M'] : Smooth I I' (1 : M → M') := by
  simp only [← Pi.one_def, ← smooth_const]

theorem cont_mdiff_on_const : ContMdiffOn I I' n (fun x : M => c) s :=
  cont_mdiff_const.ContMdiffOn

@[to_additive]
theorem cont_mdiff_on_one [One M'] : ContMdiffOn I I' n (1 : M → M') s :=
  cont_mdiff_one.ContMdiffOn

theorem smooth_on_const : SmoothOn I I' (fun x : M => c) s :=
  cont_mdiff_on_const

@[to_additive]
theorem smooth_on_one [One M'] : SmoothOn I I' (1 : M → M') s :=
  cont_mdiff_on_one

theorem cont_mdiff_at_const : ContMdiffAt I I' n (fun x : M => c) x :=
  cont_mdiff_const.ContMdiffAt

@[to_additive]
theorem cont_mdiff_at_one [One M'] : ContMdiffAt I I' n (1 : M → M') x :=
  cont_mdiff_one.ContMdiffAt

theorem smooth_at_const : SmoothAt I I' (fun x : M => c) x :=
  cont_mdiff_at_const

@[to_additive]
theorem smooth_at_one [One M'] : SmoothAt I I' (1 : M → M') x :=
  cont_mdiff_at_one

theorem cont_mdiff_within_at_const : ContMdiffWithinAt I I' n (fun x : M => c) s x :=
  cont_mdiff_at_const.ContMdiffWithinAt

@[to_additive]
theorem cont_mdiff_within_at_one [One M'] : ContMdiffWithinAt I I' n (1 : M → M') s x :=
  cont_mdiff_at_const.ContMdiffWithinAt

theorem smooth_within_at_const : SmoothWithinAt I I' (fun x : M => c) s x :=
  cont_mdiff_within_at_const

@[to_additive]
theorem smooth_within_at_one [One M'] : SmoothWithinAt I I' (1 : M → M') s x :=
  cont_mdiff_within_at_one

end id

theorem cont_mdiff_of_support {f : M → F} (hf : ∀, ∀ x ∈ Tsupport f, ∀, ContMdiffAt I 𝓘(𝕜, F) n f x) :
    ContMdiff I 𝓘(𝕜, F) n f := by
  intro x
  by_cases' hx : x ∈ Tsupport f
  · exact hf x hx
    
  · refine' ContMdiffAt.congr_of_eventually_eq _ (eventually_eq_zero_nhds.2 hx)
    exact cont_mdiff_at_const
    

/-! ### Equivalence with the basic definition for functions between vector spaces -/


section Module

theorem cont_mdiff_within_at_iff_cont_diff_within_at {f : E → E'} {s : Set E} {x : E} :
    ContMdiffWithinAt 𝓘(𝕜, E) 𝓘(𝕜, E') n f s x ↔ ContDiffWithinAt 𝕜 n f s x := by
  simp'(config := { contextual := true }) only [← ContMdiffWithinAt, ← lift_prop_within_at, ← ContDiffWithinAtProp, ←
    iff_def] with mfld_simps
  exact ContDiffWithinAt.continuous_within_at

alias cont_mdiff_within_at_iff_cont_diff_within_at ↔
  ContMdiffWithinAt.cont_diff_within_at ContDiffWithinAt.cont_mdiff_within_at

theorem cont_mdiff_at_iff_cont_diff_at {f : E → E'} {x : E} : ContMdiffAt 𝓘(𝕜, E) 𝓘(𝕜, E') n f x ↔ ContDiffAt 𝕜 n f x :=
  by
  rw [← cont_mdiff_within_at_univ, cont_mdiff_within_at_iff_cont_diff_within_at, cont_diff_within_at_univ]

alias cont_mdiff_at_iff_cont_diff_at ↔ ContMdiffAt.cont_diff_at ContDiffAt.cont_mdiff_at

theorem cont_mdiff_on_iff_cont_diff_on {f : E → E'} {s : Set E} :
    ContMdiffOn 𝓘(𝕜, E) 𝓘(𝕜, E') n f s ↔ ContDiffOn 𝕜 n f s :=
  forall_congrₓ <| by
    simp [← cont_mdiff_within_at_iff_cont_diff_within_at]

alias cont_mdiff_on_iff_cont_diff_on ↔ ContMdiffOn.cont_diff_on ContDiffOn.cont_mdiff_on

theorem cont_mdiff_iff_cont_diff {f : E → E'} : ContMdiff 𝓘(𝕜, E) 𝓘(𝕜, E') n f ↔ ContDiff 𝕜 n f := by
  rw [← cont_diff_on_univ, ← cont_mdiff_on_univ, cont_mdiff_on_iff_cont_diff_on]

alias cont_mdiff_iff_cont_diff ↔ ContMdiff.cont_diff ContDiff.cont_mdiff

end Module

/-! ### The tangent map of a smooth function is smooth -/


section tangentMap

/-- If a function is `C^n` with `1 ≤ n` on a domain with unique derivatives, then its bundled
derivative is continuous. In this auxiliary lemma, we prove this fact when the source and target
space are model spaces in models with corners. The general fact is proved in
`cont_mdiff_on.continuous_on_tangent_map_within`-/
theorem ContMdiffOn.continuous_on_tangent_map_within_aux {f : H → H'} {s : Set H} (hf : ContMdiffOn I I' n f s)
    (hn : 1 ≤ n) (hs : UniqueMdiffOn I s) : ContinuousOn (tangentMapWithin I I' f s) (TangentBundle.proj I H ⁻¹' s) :=
  by
  suffices h :
    ContinuousOn
      (fun p : H × E =>
        (f p.fst,
          (fderivWithin 𝕜 (writtenInExtChartAt I I' p.fst f) (I.symm ⁻¹' s ∩ range I) ((extChartAt I p.fst) p.fst) :
              E →L[𝕜] E')
            p.snd))
      (Prod.fst ⁻¹' s)
  · have A := (tangentBundleModelSpaceHomeomorph H I).Continuous
    rw [continuous_iff_continuous_on_univ] at A
    have B := ((tangentBundleModelSpaceHomeomorph H' I').symm.Continuous.comp_continuous_on h).comp' A
    have : univ ∩ ⇑(tangentBundleModelSpaceHomeomorph H I) ⁻¹' (Prod.fst ⁻¹' s) = TangentBundle.proj I H ⁻¹' s := by
      ext ⟨x, v⟩
      simp' only with mfld_simps
    rw [this] at B
    apply B.congr
    rintro ⟨x, v⟩ hx
    dsimp' [← tangentMapWithin]
    ext
    · rfl
      
    simp' only with mfld_simps
    apply congr_fun
    apply congr_arg
    rw [MdifferentiableWithinAt.mfderiv_within (hf.mdifferentiable_on hn x hx)]
    rfl
    
  suffices h :
    ContinuousOn
      (fun p : H × E => (fderivWithin 𝕜 (I' ∘ f ∘ I.symm) (I.symm ⁻¹' s ∩ range I) (I p.fst) : E →L[𝕜] E') p.snd)
      (Prod.fst ⁻¹' s)
  · dsimp' [← writtenInExtChartAt, ← extChartAt]
    apply ContinuousOn.prod (ContinuousOn.comp hf.continuous_on continuous_fst.continuous_on (subset.refl _))
    apply h.congr
    intro p hp
    rfl
    
  suffices h : ContinuousOn (fderivWithin 𝕜 (I' ∘ f ∘ I.symm) (I.symm ⁻¹' s ∩ range I)) (I '' s)
  · have C := ContinuousOn.comp h I.continuous_to_fun.continuous_on (subset.refl _)
    have A : Continuous fun q : (E →L[𝕜] E') × E => q.1 q.2 := is_bounded_bilinear_map_apply.continuous
    have B :
      ContinuousOn (fun p : H × E => (fderivWithin 𝕜 (I' ∘ f ∘ I.symm) (I.symm ⁻¹' s ∩ range I) (I p.1), p.2))
        (Prod.fst ⁻¹' s) :=
      by
      apply ContinuousOn.prod _ continuous_snd.continuous_on
      refine' (ContinuousOn.comp C continuous_fst.continuous_on _ : _)
      exact preimage_mono (subset_preimage_image _ _)
    exact A.comp_continuous_on B
    
  rw [cont_mdiff_on_iff] at hf
  let x : H := I.symm (0 : E)
  let y : H' := I'.symm (0 : E')
  have A := hf.2 x y
  simp' only [← I.image_eq, ← inter_comm] with mfld_simps  at A⊢
  apply A.continuous_on_fderiv_within _ hn
  convert hs.unique_diff_on_target_inter x using 1
  simp' only [← inter_comm] with mfld_simps

/-- If a function is `C^n` on a domain with unique derivatives, then its bundled derivative is
`C^m` when `m+1 ≤ n`. In this auxiliary lemma, we prove this fact when the source and target space
are model spaces in models with corners. The general fact is proved in
`cont_mdiff_on.cont_mdiff_on_tangent_map_within` -/
theorem ContMdiffOn.cont_mdiff_on_tangent_map_within_aux {f : H → H'} {s : Set H} (hf : ContMdiffOn I I' n f s)
    (hmn : m + 1 ≤ n) (hs : UniqueMdiffOn I s) :
    ContMdiffOn I.tangent I'.tangent m (tangentMapWithin I I' f s) (TangentBundle.proj I H ⁻¹' s) := by
  have m_le_n : m ≤ n := by
    apply le_transₓ _ hmn
    have : m + 0 ≤ m + 1 := add_le_add_left (zero_le _) _
    simpa only [← add_zeroₓ] using this
  have one_le_n : 1 ≤ n := by
    apply le_transₓ _ hmn
    change 0 + 1 ≤ m + 1
    exact add_le_add_right (zero_le _) _
  have U' : UniqueDiffOn 𝕜 (range I ∩ I.symm ⁻¹' s) := by
    intro y hy
    simpa only [← UniqueMdiffOn, ← UniqueMdiffWithinAt, ← hy.1, ← inter_comm] with mfld_simps using hs (I.symm y) hy.2
  have U : UniqueDiffOn 𝕜 ((range I ∩ I.symm ⁻¹' s) ×ˢ (univ : Set E)) := U'.prod unique_diff_on_univ
  rw [cont_mdiff_on_iff]
  refine' ⟨hf.continuous_on_tangent_map_within_aux one_le_n hs, fun p q => _⟩
  have A :
    range I ×ˢ (univ : Set E) ∩
        ((Equivₓ.sigmaEquivProd H E).symm ∘ fun p : E × E => (I.symm p.fst, p.snd)) ⁻¹' (TangentBundle.proj I H ⁻¹' s) =
      (range I ∩ I.symm ⁻¹' s) ×ˢ (univ : Set E) :=
    by
    ext ⟨x, v⟩
    simp' only with mfld_simps
  suffices h :
    ContDiffOn 𝕜 m
      (((fun p : H' × E' => (I' p.fst, p.snd)) ∘ Equivₓ.sigmaEquivProd H' E') ∘
        tangentMapWithin I I' f s ∘ (Equivₓ.sigmaEquivProd H E).symm ∘ fun p : E × E => (I.symm p.fst, p.snd))
      ((range ⇑I ∩ ⇑I.symm ⁻¹' s) ×ˢ (univ : Set E))
  · simpa [← A] using h
    
  change
    ContDiffOn 𝕜 m
      (fun p : E × E => ((I' (f (I.symm p.fst)), (mfderivWithin I I' f s (I.symm p.fst) : E → E') p.snd) : E' × E'))
      ((range I ∩ I.symm ⁻¹' s) ×ˢ (univ : Set E))
  -- check that all bits in this formula are `C^n`
  have hf' := cont_mdiff_on_iff.1 hf
  have A : ContDiffOn 𝕜 m (I' ∘ f ∘ I.symm) (range I ∩ I.symm ⁻¹' s) := by
    simpa only with mfld_simps using (hf'.2 (I.symm 0) (I'.symm 0)).ofLe m_le_n
  have B : ContDiffOn 𝕜 m ((I' ∘ f ∘ I.symm) ∘ Prod.fst) ((range I ∩ I.symm ⁻¹' s) ×ˢ (univ : Set E)) :=
    A.comp cont_diff_fst.cont_diff_on (prod_subset_preimage_fst _ _)
  suffices C :
    ContDiffOn 𝕜 m (fun p : E × E => (fderivWithin 𝕜 (I' ∘ f ∘ I.symm) (I.symm ⁻¹' s ∩ range I) p.1 : _) p.2)
      ((range I ∩ I.symm ⁻¹' s) ×ˢ (univ : Set E))
  · apply ContDiffOn.prod B _
    apply C.congr fun p hp => _
    simp' only with mfld_simps  at hp
    simp' only [← mfderivWithin, ← hf.mdifferentiable_on one_le_n _ hp.2, ← hp.1, ← dif_pos] with mfld_simps
    
  have D :
    ContDiffOn 𝕜 m (fun x => fderivWithin 𝕜 (I' ∘ f ∘ I.symm) (I.symm ⁻¹' s ∩ range I) x) (range I ∩ I.symm ⁻¹' s) := by
    have : ContDiffOn 𝕜 n (I' ∘ f ∘ I.symm) (range I ∩ I.symm ⁻¹' s) := by
      simpa only with mfld_simps using hf'.2 (I.symm 0) (I'.symm 0)
    simpa only [← inter_comm] using this.fderiv_within U' hmn
  have := D.comp cont_diff_fst.cont_diff_on (prod_subset_preimage_fst _ _)
  have := ContDiffOn.prod this cont_diff_snd.cont_diff_on
  exact is_bounded_bilinear_map_apply.cont_diff.comp_cont_diff_on this

include Is I's

/-- If a function is `C^n` on a domain with unique derivatives, then its bundled derivative
is `C^m` when `m+1 ≤ n`. -/
theorem ContMdiffOn.cont_mdiff_on_tangent_map_within (hf : ContMdiffOn I I' n f s) (hmn : m + 1 ≤ n)
    (hs : UniqueMdiffOn I s) :
    ContMdiffOn I.tangent I'.tangent m (tangentMapWithin I I' f s) (TangentBundle.proj I M ⁻¹' s) := by
  /- The strategy of the proof is to avoid unfolding the definitions, and reduce by functoriality
    to the case of functions on the model spaces, where we have already proved the result.
    Let `l` and `r` be the charts to the left and to the right, so that we have
    ```
       l^{-1}      f       r
    H --------> M ---> M' ---> H'
    ```
    Then the tangent map `T(r ∘ f ∘ l)` is smooth by a previous result. Consider the composition
    ```
        Tl        T(r ∘ f ∘ l^{-1})         Tr^{-1}
    TM -----> TH -------------------> TH' ---------> TM'
    ```
    where `Tr^{-1}` and `Tl` are the tangent maps of `r^{-1}` and `l`. Writing `Tl` and `Tr^{-1}` as
    composition of charts (called `Dl` and `il` for `l` and `Dr` and `ir` in the proof below), it
    follows that they are smooth. The composition of all these maps is `Tf`, and is therefore smooth
    as a composition of smooth maps.
    -/
  have m_le_n : m ≤ n := by
    apply le_transₓ _ hmn
    have : m + 0 ≤ m + 1 := add_le_add_left (zero_le _) _
    simpa only [← add_zeroₓ]
  have one_le_n : 1 ≤ n := by
    apply le_transₓ _ hmn
    change 0 + 1 ≤ m + 1
    exact add_le_add_right (zero_le _) _
  -- First step: local reduction on the space, to a set `s'` which is contained in chart domains.
  refine' cont_mdiff_on_of_locally_cont_mdiff_on fun p hp => _
  have hf' := cont_mdiff_on_iff.1 hf
  simp [← TangentBundle.proj] at hp
  let l := chart_at H p.1
  set Dl := chart_at (ModelProd H E) p with hDl
  let r := chart_at H' (f p.1)
  let Dr := chart_at (ModelProd H' E') (tangentMapWithin I I' f s p)
  let il := chart_at (ModelProd H E) (tangentMap I I l p)
  let ir := chart_at (ModelProd H' E') (tangentMap I I' (r ∘ f) p)
  let s' := f ⁻¹' r.source ∩ s ∩ l.source
  let s'_lift := TangentBundle.proj I M ⁻¹' s'
  let s'l := l.target ∩ l.symm ⁻¹' s'
  let s'l_lift := TangentBundle.proj I H ⁻¹' s'l
  rcases continuous_on_iff'.1 hf'.1 r.source r.open_source with ⟨o, o_open, ho⟩
  suffices h : ContMdiffOn I.tangent I'.tangent m (tangentMapWithin I I' f s) s'_lift
  · refine' ⟨TangentBundle.proj I M ⁻¹' (o ∩ l.source), _, _, _⟩
    show IsOpen (TangentBundle.proj I M ⁻¹' (o ∩ l.source))
    exact (IsOpen.inter o_open l.open_source).Preimage (tangent_bundle_proj_continuous _ _)
    show p ∈ TangentBundle.proj I M ⁻¹' (o ∩ l.source)
    · simp [← TangentBundle.proj]
      have : p.1 ∈ f ⁻¹' r.source ∩ s := by
        simp [← hp]
      rw [ho] at this
      exact this.1
      
    · have : TangentBundle.proj I M ⁻¹' s ∩ TangentBundle.proj I M ⁻¹' (o ∩ l.source) = s'_lift := by
        dsimp' only [← s'_lift, ← s']
        rw [ho]
        mfld_set_tac
      rw [this]
      exact h
      
    
  /- Second step: check that all functions are smooth, and use the chain rule to write the bundled
    derivative as a composition of a function between model spaces and of charts.
    Convention: statements about the differentiability of `a ∘ b ∘ c` are named `diff_abc`. Statements
    about differentiability in the bundle have a `_lift` suffix. -/
  have U' : UniqueMdiffOn I s' := by
    apply UniqueMdiffOn.inter _ l.open_source
    rw [ho, inter_comm]
    exact hs.inter o_open
  have U'l : UniqueMdiffOn I s'l := U'.unique_mdiff_on_preimage (mdifferentiable_chart _ _)
  have diff_f : ContMdiffOn I I' n f s' :=
    hf.mono
      (by
        mfld_set_tac)
  have diff_r : ContMdiffOn I' I' n r r.source := cont_mdiff_on_chart
  have diff_rf : ContMdiffOn I I' n (r ∘ f) s' := by
    apply ContMdiffOn.comp diff_r diff_f fun x hx => _
    simp' only [← s'] with mfld_simps  at hx
    simp' only [← hx] with mfld_simps
  have diff_l : ContMdiffOn I I n l.symm s'l := by
    have A : ContMdiffOn I I n l.symm l.target := cont_mdiff_on_chart_symm
    exact
      A.mono
        (by
          mfld_set_tac)
  have diff_rfl : ContMdiffOn I I' n (r ∘ f ∘ l.symm) s'l := by
    apply ContMdiffOn.comp diff_rf diff_l
    mfld_set_tac
  have diff_rfl_lift : ContMdiffOn I.tangent I'.tangent m (tangentMapWithin I I' (r ∘ f ∘ l.symm) s'l) s'l_lift :=
    diff_rfl.cont_mdiff_on_tangent_map_within_aux hmn U'l
  have diff_irrfl_lift :
    ContMdiffOn I.tangent I'.tangent m (ir ∘ tangentMapWithin I I' (r ∘ f ∘ l.symm) s'l) s'l_lift := by
    have A : ContMdiffOn I'.tangent I'.tangent m ir ir.source := cont_mdiff_on_chart
    exact
      ContMdiffOn.comp A diff_rfl_lift fun p hp => by
        simp' only [← ir] with mfld_simps
  have diff_Drirrfl_lift :
    ContMdiffOn I.tangent I'.tangent m (Dr.symm ∘ ir ∘ tangentMapWithin I I' (r ∘ f ∘ l.symm) s'l) s'l_lift := by
    have A : ContMdiffOn I'.tangent I'.tangent m Dr.symm Dr.target := cont_mdiff_on_chart_symm
    apply ContMdiffOn.comp A diff_irrfl_lift fun p hp => _
    simp' only [← s'l_lift, ← TangentBundle.proj] with mfld_simps  at hp
    simp' only [← ir, ← @LocalEquiv.refl_coe (ModelProd H' E'), ← hp] with mfld_simps
  -- conclusion of this step: the composition of all the maps above is smooth
  have diff_DrirrflilDl :
    ContMdiffOn I.tangent I'.tangent m (Dr.symm ∘ (ir ∘ tangentMapWithin I I' (r ∘ f ∘ l.symm) s'l) ∘ il.symm ∘ Dl)
      s'_lift :=
    by
    have A : ContMdiffOn I.tangent I.tangent m Dl Dl.source := cont_mdiff_on_chart
    have A' : ContMdiffOn I.tangent I.tangent m Dl s'_lift := by
      apply A.mono fun p hp => _
      simp' only [← s'_lift, ← TangentBundle.proj] with mfld_simps  at hp
      simp' only [← Dl, ← hp] with mfld_simps
    have B : ContMdiffOn I.tangent I.tangent m il.symm il.target := cont_mdiff_on_chart_symm
    have C : ContMdiffOn I.tangent I.tangent m (il.symm ∘ Dl) s'_lift :=
      ContMdiffOn.comp B A' fun p hp => by
        simp' only [← il] with mfld_simps
    apply ContMdiffOn.comp diff_Drirrfl_lift C fun p hp => _
    simp' only [← s'_lift, ← TangentBundle.proj] with mfld_simps  at hp
    simp' only [← il, ← s'l_lift, ← hp, ← TangentBundle.proj] with mfld_simps
  /- Third step: check that the composition of all the maps indeed coincides with the derivative we
    are looking for -/
  have eq_comp :
    ∀,
      ∀ q ∈ s'_lift,
        ∀, tangentMapWithin I I' f s q = (Dr.symm ∘ ir ∘ tangentMapWithin I I' (r ∘ f ∘ l.symm) s'l ∘ il.symm ∘ Dl) q :=
    by
    intro q hq
    simp' only [← s'_lift, ← TangentBundle.proj] with mfld_simps  at hq
    have U'q : UniqueMdiffWithinAt I s' q.1 := by
      apply U'
      simp' only [← hq, ← s'] with mfld_simps
    have U'lq : UniqueMdiffWithinAt I s'l (Dl q).1 := by
      apply U'l
      simp' only [← hq, ← s'l] with mfld_simps
    have A :
      tangentMapWithin I I' ((r ∘ f) ∘ l.symm) s'l (il.symm (Dl q)) =
        tangentMapWithin I I' (r ∘ f) s' (tangentMapWithin I I l.symm s'l (il.symm (Dl q))) :=
      by
      refine' tangent_map_within_comp_at (il.symm (Dl q)) _ _ (fun p hp => _) U'lq
      · apply diff_rf.mdifferentiable_on one_le_n
        simp' only [← hq] with mfld_simps
        
      · apply diff_l.mdifferentiable_on one_le_n
        simp' only [← s'l, ← hq] with mfld_simps
        
      · simp' only with mfld_simps  at hp
        simp' only [← hp] with mfld_simps
        
    have B : tangentMapWithin I I l.symm s'l (il.symm (Dl q)) = q := by
      have : tangentMapWithin I I l.symm s'l (il.symm (Dl q)) = tangentMap I I l.symm (il.symm (Dl q)) := by
        refine' tangent_map_within_eq_tangent_map U'lq _
        refine' mdifferentiable_at_atlas_symm _ (chart_mem_atlas _ _) _
        simp' only [← hq] with mfld_simps
      rw [this, tangent_map_chart_symm, hDl]
      · simp' only [← hq] with mfld_simps
        have : q ∈ (chart_at (ModelProd H E) p).Source := by
          simp' only [← hq] with mfld_simps
        exact (chart_at (ModelProd H E) p).left_inv this
        
      · simp' only [← hq] with mfld_simps
        
    have C : tangentMapWithin I I' (r ∘ f) s' q = tangentMapWithin I' I' r r.source (tangentMapWithin I I' f s' q) := by
      refine' tangent_map_within_comp_at q _ _ (fun r hr => _) U'q
      · apply diff_r.mdifferentiable_on one_le_n
        simp' only [← hq] with mfld_simps
        
      · apply diff_f.mdifferentiable_on one_le_n
        simp' only [← hq] with mfld_simps
        
      · simp' only [← s'] with mfld_simps  at hr
        simp' only [← hr] with mfld_simps
        
    have D :
      Dr.symm (ir (tangentMapWithin I' I' r r.source (tangentMapWithin I I' f s' q))) = tangentMapWithin I I' f s' q :=
      by
      have A :
        tangentMapWithin I' I' r r.source (tangentMapWithin I I' f s' q) =
          tangentMap I' I' r (tangentMapWithin I I' f s' q) :=
        by
        apply tangent_map_within_eq_tangent_map
        · apply IsOpen.unique_mdiff_within_at _ r.open_source
          simp [← hq]
          
        · refine' mdifferentiable_at_atlas _ (chart_mem_atlas _ _) _
          simp' only [← hq] with mfld_simps
          
      have : f p.1 = (tangentMapWithin I I' f s p).1 := rfl
      rw [A]
      dsimp' [← r, ← Dr]
      rw [this, tangent_map_chart]
      · simp' only [← hq] with mfld_simps
        have : tangentMapWithin I I' f s' q ∈ (chart_at (ModelProd H' E') (tangentMapWithin I I' f s p)).Source := by
          simp' only [← hq] with mfld_simps
        exact (chart_at (ModelProd H' E') (tangentMapWithin I I' f s p)).left_inv this
        
      · simp' only [← hq] with mfld_simps
        
    have E : tangentMapWithin I I' f s' q = tangentMapWithin I I' f s q := by
      refine'
        tangent_map_within_subset
          (by
            mfld_set_tac)
          U'q _
      apply hf.mdifferentiable_on one_le_n
      simp' only [← hq] with mfld_simps
    simp only [← (· ∘ ·), ← A, ← B, ← C, ← D, ← E.symm]
  exact diff_DrirrflilDl.congr eq_comp

/-- If a function is `C^n` on a domain with unique derivatives, with `1 ≤ n`, then its bundled
derivative is continuous there. -/
theorem ContMdiffOn.continuous_on_tangent_map_within (hf : ContMdiffOn I I' n f s) (hmn : 1 ≤ n)
    (hs : UniqueMdiffOn I s) : ContinuousOn (tangentMapWithin I I' f s) (TangentBundle.proj I M ⁻¹' s) := by
  have : ContMdiffOn I.tangent I'.tangent 0 (tangentMapWithin I I' f s) (TangentBundle.proj I M ⁻¹' s) :=
    hf.cont_mdiff_on_tangent_map_within hmn hs
  exact this.continuous_on

/-- If a function is `C^n`, then its bundled derivative is `C^m` when `m+1 ≤ n`. -/
theorem ContMdiff.cont_mdiff_tangent_map (hf : ContMdiff I I' n f) (hmn : m + 1 ≤ n) :
    ContMdiff I.tangent I'.tangent m (tangentMap I I' f) := by
  rw [← cont_mdiff_on_univ] at hf⊢
  convert hf.cont_mdiff_on_tangent_map_within hmn unique_mdiff_on_univ
  rw [tangent_map_within_univ]

/-- If a function is `C^n`, with `1 ≤ n`, then its bundled derivative is continuous. -/
theorem ContMdiff.continuous_tangent_map (hf : ContMdiff I I' n f) (hmn : 1 ≤ n) : Continuous (tangentMap I I' f) := by
  rw [← cont_mdiff_on_univ] at hf
  rw [continuous_iff_continuous_on_univ]
  convert hf.continuous_on_tangent_map_within hmn unique_mdiff_on_univ
  rw [tangent_map_within_univ]

end tangentMap

/-! ### Smoothness of the projection in a basic smooth bundle -/


namespace BasicSmoothVectorBundleCore

variable (Z : BasicSmoothVectorBundleCore I M E')

theorem cont_mdiff_proj : ContMdiff (I.Prod 𝓘(𝕜, E')) I n Z.toTopologicalVectorBundleCore.proj := by
  intro x
  rw [ContMdiffAt, cont_mdiff_within_at_iff']
  refine' ⟨Z.to_topological_vector_bundle_core.continuous_proj.continuous_within_at, _⟩
  simp' only [← (· ∘ ·), ← chart_at, ← chart] with mfld_simps
  apply cont_diff_within_at_fst.congr
  · rintro ⟨a, b⟩ hab
    simp' only with mfld_simps  at hab
    simp' only [← hab] with mfld_simps
    
  · simp' only with mfld_simps
    

theorem smooth_proj : Smooth (I.Prod 𝓘(𝕜, E')) I Z.toTopologicalVectorBundleCore.proj :=
  cont_mdiff_proj Z

theorem cont_mdiff_on_proj {s : Set Z.toTopologicalVectorBundleCore.TotalSpace} :
    ContMdiffOn (I.Prod 𝓘(𝕜, E')) I n Z.toTopologicalVectorBundleCore.proj s :=
  Z.cont_mdiff_proj.ContMdiffOn

theorem smooth_on_proj {s : Set Z.toTopologicalVectorBundleCore.TotalSpace} :
    SmoothOn (I.Prod 𝓘(𝕜, E')) I Z.toTopologicalVectorBundleCore.proj s :=
  cont_mdiff_on_proj Z

theorem cont_mdiff_at_proj {p : Z.toTopologicalVectorBundleCore.TotalSpace} :
    ContMdiffAt (I.Prod 𝓘(𝕜, E')) I n Z.toTopologicalVectorBundleCore.proj p :=
  Z.cont_mdiff_proj.ContMdiffAt

theorem smooth_at_proj {p : Z.toTopologicalVectorBundleCore.TotalSpace} :
    SmoothAt (I.Prod 𝓘(𝕜, E')) I Z.toTopologicalVectorBundleCore.proj p :=
  Z.cont_mdiff_at_proj

theorem cont_mdiff_within_at_proj {s : Set Z.toTopologicalVectorBundleCore.TotalSpace}
    {p : Z.toTopologicalVectorBundleCore.TotalSpace} :
    ContMdiffWithinAt (I.Prod 𝓘(𝕜, E')) I n Z.toTopologicalVectorBundleCore.proj s p :=
  Z.cont_mdiff_at_proj.ContMdiffWithinAt

theorem smooth_within_at_proj {s : Set Z.toTopologicalVectorBundleCore.TotalSpace}
    {p : Z.toTopologicalVectorBundleCore.TotalSpace} :
    SmoothWithinAt (I.Prod 𝓘(𝕜, E')) I Z.toTopologicalVectorBundleCore.proj s p :=
  Z.cont_mdiff_within_at_proj

/-- If an element of `E'` is invariant under all coordinate changes, then one can define a
corresponding section of the fiber bundle, which is smooth. This applies in particular to the
zero section of a vector bundle. Another example (not yet defined) would be the identity
section of the endomorphism bundle of a vector bundle. -/
theorem smooth_const_section (v : E')
    (h : ∀ i j : Atlas H M, ∀, ∀ x ∈ i.1.Source ∩ j.1.Source, ∀, Z.coordChange i j (i.1 x) v = v) :
    Smooth I (I.Prod 𝓘(𝕜, E')) (show M → Z.toTopologicalVectorBundleCore.TotalSpace from fun x => ⟨x, v⟩) := by
  intro x
  rw [ContMdiffAt, cont_mdiff_within_at_iff']
  constructor
  · apply Continuous.continuous_within_at
    apply TopologicalFiberBundleCore.continuous_const_section
    intro i j y hy
    exact h _ _ _ hy
    
  · have : ContDiff 𝕜 ⊤ fun y : E => (y, v) := cont_diff_id.prod cont_diff_const
    apply this.cont_diff_within_at.congr
    · intro y hy
      simp' only with mfld_simps  at hy
      simp' only [← chart, ← hy, ← chart_at, ← Prod.mk.inj_iff, ← to_topological_vector_bundle_core] with mfld_simps
      apply h
      simp' only [← hy, ← Subtype.val_eq_coe] with mfld_simps
      exact mem_chart_source H ((chart_at H x).symm ((ModelWithCorners.symm I) y))
      
    · simp' only [← chart, ← chart_at, ← Prod.mk.inj_iff, ← to_topological_vector_bundle_core] with mfld_simps
      apply h
      simp' only [← Subtype.val_eq_coe] with mfld_simps
      exact mem_chart_source H x
      
    

end BasicSmoothVectorBundleCore

/-! ### Smoothness of the tangent bundle projection -/


namespace TangentBundle

include Is

theorem cont_mdiff_proj : ContMdiff I.tangent I n (proj I M) :=
  BasicSmoothVectorBundleCore.cont_mdiff_proj _

theorem smooth_proj : Smooth I.tangent I (proj I M) :=
  BasicSmoothVectorBundleCore.smooth_proj _

theorem cont_mdiff_on_proj {s : Set (TangentBundle I M)} : ContMdiffOn I.tangent I n (proj I M) s :=
  BasicSmoothVectorBundleCore.cont_mdiff_on_proj _

theorem smooth_on_proj {s : Set (TangentBundle I M)} : SmoothOn I.tangent I (proj I M) s :=
  BasicSmoothVectorBundleCore.smooth_on_proj _

theorem cont_mdiff_at_proj {p : TangentBundle I M} : ContMdiffAt I.tangent I n (proj I M) p :=
  BasicSmoothVectorBundleCore.cont_mdiff_at_proj _

theorem smooth_at_proj {p : TangentBundle I M} : SmoothAt I.tangent I (proj I M) p :=
  BasicSmoothVectorBundleCore.smooth_at_proj _

theorem cont_mdiff_within_at_proj {s : Set (TangentBundle I M)} {p : TangentBundle I M} :
    ContMdiffWithinAt I.tangent I n (proj I M) s p :=
  BasicSmoothVectorBundleCore.cont_mdiff_within_at_proj _

theorem smooth_within_at_proj {s : Set (TangentBundle I M)} {p : TangentBundle I M} :
    SmoothWithinAt I.tangent I (proj I M) s p :=
  BasicSmoothVectorBundleCore.smooth_within_at_proj _

variable (I M)

/-- The zero section of the tangent bundle -/
def zeroSection : M → TangentBundle I M := fun x => ⟨x, 0⟩

variable {I M}

theorem smooth_zero_section : Smooth I I.tangent (zeroSection I M) := by
  apply BasicSmoothVectorBundleCore.smooth_const_section (tangentBundleCore I M) 0
  intro i j x hx
  simp' only [← tangentBundleCore, ← ContinuousLinearMap.map_zero, ← ContinuousLinearMap.coe_coe] with mfld_simps

open Bundle

/-- The derivative of the zero section of the tangent bundle maps `⟨x, v⟩` to `⟨⟨x, 0⟩, ⟨v, 0⟩⟩`.

Note that, as currently framed, this is a statement in coordinates, thus reliant on the choice
of the coordinate system we use on the tangent bundle.

However, the result itself is coordinate-dependent only to the extent that the coordinates
determine a splitting of the tangent bundle.  Moreover, there is a canonical splitting at each
point of the zero section (since there is a canonical horizontal space there, the tangent space
to the zero section, in addition to the canonical vertical space which is the kernel of the
derivative of the projection), and this canonical splitting is also the one that comes from the
coordinates on the tangent bundle in our definitions. So this statement is not as crazy as it
may seem.

TODO define splittings of vector bundles; state this result invariantly. -/
theorem tangent_map_tangent_bundle_pure (p : TangentBundle I M) :
    tangentMap I I.tangent (TangentBundle.zeroSection I M) p = ⟨⟨p.1, 0⟩, ⟨p.2, 0⟩⟩ := by
  rcases p with ⟨x, v⟩
  have N : I.symm ⁻¹' (chart_at H x).Target ∈ 𝓝 (I ((chart_at H x) x)) := by
    apply IsOpen.mem_nhds
    apply (LocalHomeomorph.open_target _).Preimage I.continuous_inv_fun
    simp' only with mfld_simps
  have A : MdifferentiableAt I I.tangent (fun x => @total_space_mk M (TangentSpace I) x 0) x :=
    tangent_bundle.smooth_zero_section.mdifferentiable_at
  have B : fderivWithin 𝕜 (fun x_1 : E => (x_1, (0 : E))) (Set.Range ⇑I) (I ((chart_at H x) x)) v = (v, 0) := by
    rw [fderiv_within_eq_fderiv, DifferentiableAt.fderiv_prod]
    · simp
      
    · exact differentiable_at_id'
      
    · exact differentiable_at_const _
      
    · exact ModelWithCorners.unique_diff_at_image I
      
    · exact differentiable_at_id'.prod (differentiable_at_const _)
      
  simp' only [← TangentBundle.zeroSection, ← tangentMap, ← mfderiv, ← A, ← dif_pos, ← chart_at, ←
    BasicSmoothVectorBundleCore.chart, ← BasicSmoothVectorBundleCore.toTopologicalVectorBundleCore, ← tangentBundleCore,
    ← Function.comp, ← ContinuousLinearMap.map_zero] with mfld_simps
  rw [← fderiv_within_inter N (I.unique_diff (I ((chart_at H x) x)) (Set.mem_range_self _))] at B
  rw [← fderiv_within_inter N (I.unique_diff (I ((chart_at H x) x)) (Set.mem_range_self _)), ← B]
  congr 2
  apply fderiv_within_congr _ fun y hy => _
  · simp' only [← Prod.mk.inj_iff] with mfld_simps
    exact
      ((tangentBundleCore I M).toTopologicalVectorBundleCore.coordChange
          ((tangentBundleCore I M).toTopologicalVectorBundleCore.indexAt
            ((chart_at H x).symm (I.symm (I ((chart_at H x) x)))))
          ⟨chart_at H x, _⟩ ((chart_at H x).symm (I.symm (I ((chart_at H x) x))))).map_zero
    
  · apply UniqueDiffWithinAt.inter (I.unique_diff _ _) N
    simp' only with mfld_simps
    
  · simp' only with mfld_simps  at hy
    simp' only [← hy, ← Prod.mk.inj_iff] with mfld_simps
    exact
      ((tangentBundleCore I M).toTopologicalVectorBundleCore.coordChange
          ((tangentBundleCore I M).toTopologicalVectorBundleCore.indexAt ((chart_at H x).symm (I.symm y)))
          ⟨chart_at H x, _⟩ ((chart_at H x).symm (I.symm y))).map_zero
    

end TangentBundle

/-! ### Smoothness of standard maps associated to the product of manifolds -/


section ProdMk

theorem ContMdiffWithinAt.prod_mk {f : M → M'} {g : M → N'} (hf : ContMdiffWithinAt I I' n f s x)
    (hg : ContMdiffWithinAt I J' n g s x) : ContMdiffWithinAt I (I'.Prod J') n (fun x => (f x, g x)) s x := by
  rw [cont_mdiff_within_at_iff] at *
  exact ⟨hf.1.Prod hg.1, hf.2.Prod hg.2⟩

theorem ContMdiffWithinAt.prod_mk_space {f : M → E'} {g : M → F'} (hf : ContMdiffWithinAt I 𝓘(𝕜, E') n f s x)
    (hg : ContMdiffWithinAt I 𝓘(𝕜, F') n g s x) : ContMdiffWithinAt I 𝓘(𝕜, E' × F') n (fun x => (f x, g x)) s x := by
  rw [cont_mdiff_within_at_iff] at *
  exact ⟨hf.1.Prod hg.1, hf.2.Prod hg.2⟩

theorem ContMdiffAt.prod_mk {f : M → M'} {g : M → N'} (hf : ContMdiffAt I I' n f x) (hg : ContMdiffAt I J' n g x) :
    ContMdiffAt I (I'.Prod J') n (fun x => (f x, g x)) x :=
  hf.prod_mk hg

theorem ContMdiffAt.prod_mk_space {f : M → E'} {g : M → F'} (hf : ContMdiffAt I 𝓘(𝕜, E') n f x)
    (hg : ContMdiffAt I 𝓘(𝕜, F') n g x) : ContMdiffAt I 𝓘(𝕜, E' × F') n (fun x => (f x, g x)) x :=
  hf.prod_mk_space hg

theorem ContMdiffOn.prod_mk {f : M → M'} {g : M → N'} (hf : ContMdiffOn I I' n f s) (hg : ContMdiffOn I J' n g s) :
    ContMdiffOn I (I'.Prod J') n (fun x => (f x, g x)) s := fun x hx => (hf x hx).prod_mk (hg x hx)

theorem ContMdiffOn.prod_mk_space {f : M → E'} {g : M → F'} (hf : ContMdiffOn I 𝓘(𝕜, E') n f s)
    (hg : ContMdiffOn I 𝓘(𝕜, F') n g s) : ContMdiffOn I 𝓘(𝕜, E' × F') n (fun x => (f x, g x)) s := fun x hx =>
  (hf x hx).prod_mk_space (hg x hx)

theorem ContMdiff.prod_mk {f : M → M'} {g : M → N'} (hf : ContMdiff I I' n f) (hg : ContMdiff I J' n g) :
    ContMdiff I (I'.Prod J') n fun x => (f x, g x) := fun x => (hf x).prod_mk (hg x)

theorem ContMdiff.prod_mk_space {f : M → E'} {g : M → F'} (hf : ContMdiff I 𝓘(𝕜, E') n f)
    (hg : ContMdiff I 𝓘(𝕜, F') n g) : ContMdiff I 𝓘(𝕜, E' × F') n fun x => (f x, g x) := fun x =>
  (hf x).prod_mk_space (hg x)

theorem SmoothWithinAt.prod_mk {f : M → M'} {g : M → N'} (hf : SmoothWithinAt I I' f s x)
    (hg : SmoothWithinAt I J' g s x) : SmoothWithinAt I (I'.Prod J') (fun x => (f x, g x)) s x :=
  hf.prod_mk hg

theorem SmoothWithinAt.prod_mk_space {f : M → E'} {g : M → F'} (hf : SmoothWithinAt I 𝓘(𝕜, E') f s x)
    (hg : SmoothWithinAt I 𝓘(𝕜, F') g s x) : SmoothWithinAt I 𝓘(𝕜, E' × F') (fun x => (f x, g x)) s x :=
  hf.prod_mk_space hg

theorem SmoothAt.prod_mk {f : M → M'} {g : M → N'} (hf : SmoothAt I I' f x) (hg : SmoothAt I J' g x) :
    SmoothAt I (I'.Prod J') (fun x => (f x, g x)) x :=
  hf.prod_mk hg

theorem SmoothAt.prod_mk_space {f : M → E'} {g : M → F'} (hf : SmoothAt I 𝓘(𝕜, E') f x) (hg : SmoothAt I 𝓘(𝕜, F') g x) :
    SmoothAt I 𝓘(𝕜, E' × F') (fun x => (f x, g x)) x :=
  hf.prod_mk_space hg

theorem SmoothOn.prod_mk {f : M → M'} {g : M → N'} (hf : SmoothOn I I' f s) (hg : SmoothOn I J' g s) :
    SmoothOn I (I'.Prod J') (fun x => (f x, g x)) s :=
  hf.prod_mk hg

theorem SmoothOn.prod_mk_space {f : M → E'} {g : M → F'} (hf : SmoothOn I 𝓘(𝕜, E') f s) (hg : SmoothOn I 𝓘(𝕜, F') g s) :
    SmoothOn I 𝓘(𝕜, E' × F') (fun x => (f x, g x)) s :=
  hf.prod_mk_space hg

theorem Smooth.prod_mk {f : M → M'} {g : M → N'} (hf : Smooth I I' f) (hg : Smooth I J' g) :
    Smooth I (I'.Prod J') fun x => (f x, g x) :=
  hf.prod_mk hg

theorem Smooth.prod_mk_space {f : M → E'} {g : M → F'} (hf : Smooth I 𝓘(𝕜, E') f) (hg : Smooth I 𝓘(𝕜, F') g) :
    Smooth I 𝓘(𝕜, E' × F') fun x => (f x, g x) :=
  hf.prod_mk_space hg

end ProdMk

section Projections

theorem cont_mdiff_within_at_fst {s : Set (M × N)} {p : M × N} : ContMdiffWithinAt (I.Prod J) I n Prod.fst s p := by
  rw [cont_mdiff_within_at_iff']
  refine' ⟨continuous_within_at_fst, _⟩
  refine' cont_diff_within_at_fst.congr (fun y hy => _) _
  · simp' only with mfld_simps  at hy
    simp' only [← hy] with mfld_simps
    
  · simp' only with mfld_simps
    

theorem cont_mdiff_at_fst {p : M × N} : ContMdiffAt (I.Prod J) I n Prod.fst p :=
  cont_mdiff_within_at_fst

theorem cont_mdiff_on_fst {s : Set (M × N)} : ContMdiffOn (I.Prod J) I n Prod.fst s := fun x hx =>
  cont_mdiff_within_at_fst

theorem cont_mdiff_fst : ContMdiff (I.Prod J) I n (@Prod.fst M N) := fun x => cont_mdiff_at_fst

theorem smooth_within_at_fst {s : Set (M × N)} {p : M × N} : SmoothWithinAt (I.Prod J) I Prod.fst s p :=
  cont_mdiff_within_at_fst

theorem smooth_at_fst {p : M × N} : SmoothAt (I.Prod J) I Prod.fst p :=
  cont_mdiff_at_fst

theorem smooth_on_fst {s : Set (M × N)} : SmoothOn (I.Prod J) I Prod.fst s :=
  cont_mdiff_on_fst

theorem smooth_fst : Smooth (I.Prod J) I (@Prod.fst M N) :=
  cont_mdiff_fst

theorem cont_mdiff_within_at_snd {s : Set (M × N)} {p : M × N} : ContMdiffWithinAt (I.Prod J) J n Prod.snd s p := by
  rw [cont_mdiff_within_at_iff']
  refine' ⟨continuous_within_at_snd, _⟩
  refine' cont_diff_within_at_snd.congr (fun y hy => _) _
  · simp' only with mfld_simps  at hy
    simp' only [← hy] with mfld_simps
    
  · simp' only with mfld_simps
    

theorem cont_mdiff_at_snd {p : M × N} : ContMdiffAt (I.Prod J) J n Prod.snd p :=
  cont_mdiff_within_at_snd

theorem cont_mdiff_on_snd {s : Set (M × N)} : ContMdiffOn (I.Prod J) J n Prod.snd s := fun x hx =>
  cont_mdiff_within_at_snd

theorem cont_mdiff_snd : ContMdiff (I.Prod J) J n (@Prod.snd M N) := fun x => cont_mdiff_at_snd

theorem smooth_within_at_snd {s : Set (M × N)} {p : M × N} : SmoothWithinAt (I.Prod J) J Prod.snd s p :=
  cont_mdiff_within_at_snd

theorem smooth_at_snd {p : M × N} : SmoothAt (I.Prod J) J Prod.snd p :=
  cont_mdiff_at_snd

theorem smooth_on_snd {s : Set (M × N)} : SmoothOn (I.Prod J) J Prod.snd s :=
  cont_mdiff_on_snd

theorem smooth_snd : Smooth (I.Prod J) J (@Prod.snd M N) :=
  cont_mdiff_snd

theorem smooth_iff_proj_smooth {f : M → M' × N'} :
    Smooth I (I'.Prod J') f ↔ Smooth I I' (Prod.fst ∘ f) ∧ Smooth I J' (Prod.snd ∘ f) := by
  constructor
  · intro h
    exact ⟨smooth_fst.comp h, smooth_snd.comp h⟩
    
  · rintro ⟨h_fst, h_snd⟩
    simpa only [← Prod.mk.eta] using h_fst.prod_mk h_snd
    

end Projections

section prod_map

variable {g : N → N'} {r : Set N} {y : N}

/-- The product map of two `C^n` functions within a set at a point is `C^n`
within the product set at the product point. -/
theorem ContMdiffWithinAt.prod_map' {p : M × N} (hf : ContMdiffWithinAt I I' n f s p.1)
    (hg : ContMdiffWithinAt J J' n g r p.2) : ContMdiffWithinAt (I.Prod J) (I'.Prod J') n (Prod.map f g) (s ×ˢ r) p :=
  (hf.comp p cont_mdiff_within_at_fst (prod_subset_preimage_fst _ _)).prod_mk <|
    hg.comp p cont_mdiff_within_at_snd (prod_subset_preimage_snd _ _)

theorem ContMdiffWithinAt.prod_map (hf : ContMdiffWithinAt I I' n f s x) (hg : ContMdiffWithinAt J J' n g r y) :
    ContMdiffWithinAt (I.Prod J) (I'.Prod J') n (Prod.map f g) (s ×ˢ r) (x, y) :=
  ContMdiffWithinAt.prod_map' hf hg

theorem ContMdiffAt.prod_map (hf : ContMdiffAt I I' n f x) (hg : ContMdiffAt J J' n g y) :
    ContMdiffAt (I.Prod J) (I'.Prod J') n (Prod.map f g) (x, y) := by
  rw [← cont_mdiff_within_at_univ] at *
  convert hf.prod_map hg
  exact univ_prod_univ.symm

theorem ContMdiffAt.prod_map' {p : M × N} (hf : ContMdiffAt I I' n f p.1) (hg : ContMdiffAt J J' n g p.2) :
    ContMdiffAt (I.Prod J) (I'.Prod J') n (Prod.map f g) p := by
  rcases p with ⟨⟩
  exact hf.prod_map hg

theorem ContMdiffOn.prod_map (hf : ContMdiffOn I I' n f s) (hg : ContMdiffOn J J' n g r) :
    ContMdiffOn (I.Prod J) (I'.Prod J') n (Prod.map f g) (s ×ˢ r) :=
  (hf.comp cont_mdiff_on_fst (prod_subset_preimage_fst _ _)).prod_mk <|
    hg.comp cont_mdiff_on_snd (prod_subset_preimage_snd _ _)

theorem ContMdiff.prod_map (hf : ContMdiff I I' n f) (hg : ContMdiff J J' n g) :
    ContMdiff (I.Prod J) (I'.Prod J') n (Prod.map f g) := by
  intro p
  exact (hf p.1).prod_map' (hg p.2)

theorem SmoothWithinAt.prod_map (hf : SmoothWithinAt I I' f s x) (hg : SmoothWithinAt J J' g r y) :
    SmoothWithinAt (I.Prod J) (I'.Prod J') (Prod.map f g) (s ×ˢ r) (x, y) :=
  hf.prod_map hg

theorem SmoothAt.prod_map (hf : SmoothAt I I' f x) (hg : SmoothAt J J' g y) :
    SmoothAt (I.Prod J) (I'.Prod J') (Prod.map f g) (x, y) :=
  hf.prod_map hg

theorem SmoothOn.prod_map (hf : SmoothOn I I' f s) (hg : SmoothOn J J' g r) :
    SmoothOn (I.Prod J) (I'.Prod J') (Prod.map f g) (s ×ˢ r) :=
  hf.prod_map hg

theorem Smooth.prod_map (hf : Smooth I I' f) (hg : Smooth J J' g) : Smooth (I.Prod J) (I'.Prod J') (Prod.map f g) :=
  hf.prod_map hg

end prod_map

section PiSpace

/-!
### Smoothness of functions with codomain `Π i, F i`

We have no `model_with_corners.pi` yet, so we prove lemmas about functions `f : M → Π i, F i` and
use `𝓘(𝕜, Π i, F i)` as the model space.
-/


variable {ι : Type _} [Fintype ι] {Fi : ι → Type _} [∀ i, NormedGroup (Fi i)] [∀ i, NormedSpace 𝕜 (Fi i)]
  {φ : M → ∀ i, Fi i}

theorem cont_mdiff_within_at_pi_space :
    ContMdiffWithinAt I 𝓘(𝕜, ∀ i, Fi i) n φ s x ↔ ∀ i, ContMdiffWithinAt I 𝓘(𝕜, Fi i) n (fun x => φ x i) s x := by
  simp only [← cont_mdiff_within_at_iff, ← continuous_within_at_pi, ← cont_diff_within_at_pi, ← forall_and_distrib, ←
    writtenInExtChartAt, ← ext_chart_model_space_eq_id, ← (· ∘ ·), ← LocalEquiv.refl_coe, ← id]

theorem cont_mdiff_on_pi_space :
    ContMdiffOn I 𝓘(𝕜, ∀ i, Fi i) n φ s ↔ ∀ i, ContMdiffOn I 𝓘(𝕜, Fi i) n (fun x => φ x i) s :=
  ⟨fun h i x hx => cont_mdiff_within_at_pi_space.1 (h x hx) i, fun h x hx =>
    cont_mdiff_within_at_pi_space.2 fun i => h i x hx⟩

theorem cont_mdiff_at_pi_space :
    ContMdiffAt I 𝓘(𝕜, ∀ i, Fi i) n φ x ↔ ∀ i, ContMdiffAt I 𝓘(𝕜, Fi i) n (fun x => φ x i) x :=
  cont_mdiff_within_at_pi_space

theorem cont_mdiff_pi_space : ContMdiff I 𝓘(𝕜, ∀ i, Fi i) n φ ↔ ∀ i, ContMdiff I 𝓘(𝕜, Fi i) n fun x => φ x i :=
  ⟨fun h i x => cont_mdiff_at_pi_space.1 (h x) i, fun h x => cont_mdiff_at_pi_space.2 fun i => h i x⟩

theorem smooth_within_at_pi_space :
    SmoothWithinAt I 𝓘(𝕜, ∀ i, Fi i) φ s x ↔ ∀ i, SmoothWithinAt I 𝓘(𝕜, Fi i) (fun x => φ x i) s x :=
  cont_mdiff_within_at_pi_space

theorem smooth_on_pi_space : SmoothOn I 𝓘(𝕜, ∀ i, Fi i) φ s ↔ ∀ i, SmoothOn I 𝓘(𝕜, Fi i) (fun x => φ x i) s :=
  cont_mdiff_on_pi_space

theorem smooth_at_pi_space : SmoothAt I 𝓘(𝕜, ∀ i, Fi i) φ x ↔ ∀ i, SmoothAt I 𝓘(𝕜, Fi i) (fun x => φ x i) x :=
  cont_mdiff_at_pi_space

theorem smooth_pi_space : Smooth I 𝓘(𝕜, ∀ i, Fi i) φ ↔ ∀ i, Smooth I 𝓘(𝕜, Fi i) fun x => φ x i :=
  cont_mdiff_pi_space

end PiSpace

/-! ### Linear maps between normed spaces are smooth -/


theorem ContinuousLinearMap.cont_mdiff (L : E →L[𝕜] F) : ContMdiff 𝓘(𝕜, E) 𝓘(𝕜, F) n L :=
  L.ContDiff.ContMdiff

/-! ### Smoothness of standard operations -/


variable {V : Type _} [NormedGroup V] [NormedSpace 𝕜 V]

/-- On any vector space, multiplication by a scalar is a smooth operation. -/
theorem smooth_smul : Smooth (𝓘(𝕜).Prod 𝓘(𝕜, V)) 𝓘(𝕜, V) fun p : 𝕜 × V => p.1 • p.2 :=
  smooth_iff.2 ⟨continuous_smul, fun x y => cont_diff_smul.ContDiffOn⟩

theorem Smooth.smul {N : Type _} [TopologicalSpace N] [ChartedSpace H N] {f : N → 𝕜} {g : N → V} (hf : Smooth I 𝓘(𝕜) f)
    (hg : Smooth I 𝓘(𝕜, V) g) : Smooth I 𝓘(𝕜, V) fun p => f p • g p :=
  smooth_smul.comp (hf.prod_mk hg)

theorem SmoothOn.smul {N : Type _} [TopologicalSpace N] [ChartedSpace H N] {f : N → 𝕜} {g : N → V} {s : Set N}
    (hf : SmoothOn I 𝓘(𝕜) f s) (hg : SmoothOn I 𝓘(𝕜, V) g s) : SmoothOn I 𝓘(𝕜, V) (fun p => f p • g p) s :=
  smooth_smul.comp_smooth_on (hf.prod_mk hg)

theorem SmoothAt.smul {N : Type _} [TopologicalSpace N] [ChartedSpace H N] {f : N → 𝕜} {g : N → V} {x : N}
    (hf : SmoothAt I 𝓘(𝕜) f x) (hg : SmoothAt I 𝓘(𝕜, V) g x) : SmoothAt I 𝓘(𝕜, V) (fun p => f p • g p) x :=
  smooth_smul.SmoothAt.comp _ (hf.prod_mk hg)

