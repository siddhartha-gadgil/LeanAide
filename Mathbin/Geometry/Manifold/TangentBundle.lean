/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathbin.Topology.VectorBundle.Basic
import Mathbin.Geometry.Manifold.SmoothManifoldWithCorners
import Mathbin.Data.Set.Prod

/-!
# Basic smooth bundles

In general, a smooth bundle is a bundle over a smooth manifold, whose fiber is a manifold, and
for which the coordinate changes are smooth. In this definition, there are charts involved at
several places: in the manifold structure of the base, in the manifold structure of the fibers, and
in the local trivializations. This makes it a complicated object in general. There is however a
specific situation where things are much simpler: when the fiber is a vector space (no need for
charts for the fibers), and when the local trivializations of the bundle and the charts of the base
coincide. Then everything is expressed in terms of the charts of the base, making for a much
simpler overall structure, which is easier to manipulate formally.

Most vector bundles that naturally occur in differential geometry are of this form:
the tangent bundle, the cotangent bundle, differential forms (used to define de Rham cohomology)
and the bundle of Riemannian metrics. Therefore, it is worth defining a specific constructor for
this kind of bundle, that we call basic smooth bundles.

A basic smooth bundle is thus a smooth bundle over a smooth manifold whose fiber is a vector space,
and which is trivial in the coordinate charts of the base. (We recall that in our notion of manifold
there is a distinguished atlas, which does not need to be maximal: we require the triviality above
this specific atlas). It can be constructed from a basic smooth bundled core, defined below,
specifying the changes in the fiber when one goes from one coordinate chart to another one.

## Main definitions

* `basic_smooth_vector_bundle_core I M F`: assuming that `M` is a smooth manifold over the model
  with corners `I` on `(𝕜, E, H)`, and `F` is a normed vector space over `𝕜`, this structure
  registers, for each pair of charts of `M`, a linear change of coordinates on `F` depending
  smoothly on the base point. This is the core structure from which one will build a smooth vector
  bundle with fiber `F` over `M`.

Let `Z` be a basic smooth bundle core over `M` with fiber `F`. We define
`Z.to_topological_vector_bundle_core`, the (topological) vector bundle core associated to `Z`. From
it, we get a space `Z.to_topological_vector_bundle_core.total_space` (which as a Type is just
`Σ (x : M), F`), with the fiber bundle topology. It inherits a manifold structure (where the
charts are in bijection with the charts of the basis). We show that this manifold is smooth.

Then we use this machinery to construct the tangent bundle of a smooth manifold.

* `tangent_bundle_core I M`: the basic smooth bundle core associated to a smooth manifold `M` over
  a model with corners `I`.
* `tangent_bundle I M`     : the total space of `tangent_bundle_core I M`. It is itself a
  smooth manifold over the model with corners `I.tangent`, the product of `I` and the trivial model
  with corners on `E`.
* `tangent_space I x`      : the tangent space to `M` at `x`
* `tangent_bundle.proj I M`: the projection from the tangent bundle to the base manifold

## Implementation notes

We register the vector space structure on the fibers of the tangent bundle, but we do not register
the normed space structure coming from that of `F` (as it is not canonical, and we also want to
keep the possibility to add a Riemannian structure on the manifold later on without having two
competing normed space instances on the tangent spaces).

We require `F` to be a normed space, and not just a topological vector space, as we want to talk
about smooth functions on `F`. The notion of derivative requires a norm to be defined.

## TODO
construct the cotangent bundle, and the bundles of differential forms. They should follow
functorially from the description of the tangent bundle as a basic smooth bundle.

## Tags
Smooth fiber bundle, vector bundle, tangent space, tangent bundle
-/


noncomputable section

universe u

open TopologicalSpace Set

open Manifold TopologicalSpace

/-- Core structure used to create a smooth bundle above `M` (a manifold over the model with
corner `I`) with fiber the normed vector space `F` over `𝕜`, which is trivial in the chart domains
of `M`. This structure registers the changes in the fibers when one changes coordinate charts in the
base. We require the change of coordinates of the fibers to be linear, so that the resulting bundle
is a vector bundle. -/
structure BasicSmoothVectorBundleCore {𝕜 : Type _} [NondiscreteNormedField 𝕜] {E : Type _} [NormedGroup E]
  [NormedSpace 𝕜 E] {H : Type _} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) (M : Type _) [TopologicalSpace M]
  [ChartedSpace H M] [SmoothManifoldWithCorners I M] (F : Type _) [NormedGroup F] [NormedSpace 𝕜 F] where
  coordChange : Atlas H M → Atlas H M → H → F →L[𝕜] F
  coord_change_self : ∀ i : Atlas H M, ∀, ∀ x ∈ i.1.Target, ∀, ∀ v, coord_change i i x v = v
  coord_change_comp :
    ∀ i j k : Atlas H M,
      ∀,
        ∀ x ∈ ((i.1.symm.trans j.1).trans (j.1.symm.trans k.1)).Source,
          ∀, ∀ v, (coord_change j k ((i.1.symm.trans j.1) x)) (coord_change i j x v) = coord_change i k x v
  coord_change_smooth_clm :
    ∀ i j : Atlas H M, ContDiffOn 𝕜 ∞ (coord_change i j ∘ I.symm) (I '' (i.1.symm.trans j.1).Source)

/-- The trivial basic smooth bundle core, in which all the changes of coordinates are the
identity. -/
def trivialBasicSmoothVectorBundleCore {𝕜 : Type _} [NondiscreteNormedField 𝕜] {E : Type _} [NormedGroup E]
    [NormedSpace 𝕜 E] {H : Type _} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) (M : Type _) [TopologicalSpace M]
    [ChartedSpace H M] [SmoothManifoldWithCorners I M] (F : Type _) [NormedGroup F] [NormedSpace 𝕜 F] :
    BasicSmoothVectorBundleCore I M F where
  coordChange := fun i j x => ContinuousLinearMap.id 𝕜 F
  coord_change_self := fun i x hx v => rfl
  coord_change_comp := fun i j k x hx v => rfl
  coord_change_smooth_clm := fun i j => by
    dsimp'
    exact cont_diff_on_const

namespace BasicSmoothVectorBundleCore

variable {𝕜 : Type _} [NondiscreteNormedField 𝕜] {E : Type _} [NormedGroup E] [NormedSpace 𝕜 E] {H : Type _}
  [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {M : Type _} [TopologicalSpace M] [ChartedSpace H M]
  [SmoothManifoldWithCorners I M] {F : Type _} [NormedGroup F] [NormedSpace 𝕜 F] (Z : BasicSmoothVectorBundleCore I M F)

instance : Inhabited (BasicSmoothVectorBundleCore I M F) :=
  ⟨trivialBasicSmoothVectorBundleCore I M F⟩

theorem coord_change_continuous (i j : Atlas H M) : ContinuousOn (Z.coordChange i j) (i.1.symm.trans j.1).Source := by
  intro x hx
  apply
    (((Z.coord_change_smooth_clm i j).ContinuousOn.ContinuousWithinAt (mem_image_of_mem I hx)).comp
        I.continuous_within_at _).congr
  · intro y hy
    simp' only with mfld_simps
    
  · simp' only with mfld_simps
    
  · exact maps_to_image I _
    

theorem coord_change_smooth (i j : Atlas H M) :
    ContDiffOn 𝕜 ∞ (fun p : E × F => Z.coordChange i j (I.symm p.1) p.2)
      ((I '' (i.1.symm.trans j.1).Source) ×ˢ (Univ : Set F)) :=
  by
  have A : ContDiff 𝕜 ∞ fun p : (F →L[𝕜] F) × F => p.1 p.2 := by
    apply IsBoundedBilinearMap.cont_diff
    exact is_bounded_bilinear_map_apply
  have B :
    ContDiffOn 𝕜 ∞ (fun p : E × F => (Z.coord_change i j (I.symm p.1), p.snd))
      ((I '' (i.1.symm.trans j.1).Source) ×ˢ (univ : Set F)) :=
    by
    apply ContDiffOn.prod _ _
    · exact (Z.coord_change_smooth_clm i j).comp cont_diff_fst.cont_diff_on (prod_subset_preimage_fst _ _)
      
    · exact is_bounded_linear_map.snd.cont_diff.cont_diff_on
      
  exact A.comp_cont_diff_on B

/-- Vector bundle core associated to a basic smooth bundle core -/
@[simps coordChange indexAt]
def toTopologicalVectorBundleCore : TopologicalVectorBundleCore 𝕜 M F (Atlas H M) where
  BaseSet := fun i => i.1.Source
  is_open_base_set := fun i => i.1.open_source
  indexAt := fun x => ⟨chartAt H x, chart_mem_atlas H x⟩
  mem_base_set_at := fun x => mem_chart_source H x
  coordChange := fun i j x => Z.coordChange i j (i.1 x)
  coord_change_self := fun i x hx v => Z.coord_change_self i (i.1 x) (i.1.map_source hx) v
  coord_change_comp := fun i j k x ⟨⟨hx1, hx2⟩, hx3⟩ v => by
    have := Z.coord_change_comp i j k (i.1 x) _ v
    convert this using 2
    · simp' only [← hx1] with mfld_simps
      
    · simp' only [← hx1, ← hx2, ← hx3] with mfld_simps
      
  coord_change_continuous := fun i j => by
    refine' ((Z.coord_change_continuous i j).comp' i.1.ContinuousOn).mono _
    rintro p ⟨hp₁, hp₂⟩
    refine' ⟨hp₁, i.1.MapsTo hp₁, _⟩
    simp' only [← i.1.left_inv hp₁, ← hp₂] with mfld_simps

@[simp, mfld_simps]
theorem base_set (i : Atlas H M) : (Z.toTopologicalVectorBundleCore.localTriv i).BaseSet = i.1.Source :=
  rfl

@[simp, mfld_simps]
theorem target (i : Atlas H M) : (Z.toTopologicalVectorBundleCore.localTriv i).Target = i.1.Source ×ˢ (Univ : Set F) :=
  rfl

/-- Local chart for the total space of a basic smooth bundle -/
def chart {e : LocalHomeomorph M H} (he : e ∈ Atlas H M) :
    LocalHomeomorph Z.toTopologicalVectorBundleCore.TotalSpace (ModelProd H F) :=
  (Z.toTopologicalVectorBundleCore.localTriv ⟨e, he⟩).toLocalHomeomorph.trans
    (LocalHomeomorph.prod e (LocalHomeomorph.refl F))

@[simp, mfld_simps]
theorem chart_source (e : LocalHomeomorph M H) (he : e ∈ Atlas H M) :
    (Z.chart he).Source = Z.toTopologicalVectorBundleCore.proj ⁻¹' e.Source := by
  simp only [← chart, ← mem_prod]
  mfld_set_tac

@[simp, mfld_simps]
theorem chart_target (e : LocalHomeomorph M H) (he : e ∈ Atlas H M) :
    (Z.chart he).Target = e.Target ×ˢ (Univ : Set F) := by
  simp only [← chart]
  mfld_set_tac

/-- The total space of a basic smooth bundle is endowed with a charted space structure, where the
charts are in bijection with the charts of the basis. -/
@[simps (config := lemmasOnly) chartAt]
instance toChartedSpace : ChartedSpace (ModelProd H F) Z.toTopologicalVectorBundleCore.TotalSpace where
  Atlas := ⋃ (e : LocalHomeomorph M H) (he : e ∈ Atlas H M), {Z.chart he}
  chartAt := fun p => Z.chart (chart_mem_atlas H p.1)
  mem_chart_source := fun p => by
    simp [← mem_chart_source]
  chart_mem_atlas := fun p => by
    simp only [← mem_Union, ← mem_singleton_iff, ← chart_mem_atlas]
    exact ⟨chart_at H p.1, chart_mem_atlas H p.1, rfl⟩

theorem mem_atlas_iff (f : LocalHomeomorph Z.toTopologicalVectorBundleCore.TotalSpace (ModelProd H F)) :
    f ∈ Atlas (ModelProd H F) Z.toTopologicalVectorBundleCore.TotalSpace ↔
      ∃ (e : LocalHomeomorph M H)(he : e ∈ Atlas H M), f = Z.chart he :=
  by
  simp only [← atlas, ← mem_Union, ← mem_singleton_iff]

@[simp, mfld_simps]
theorem mem_chart_source_iff (p q : Z.toTopologicalVectorBundleCore.TotalSpace) :
    p ∈ (chartAt (ModelProd H F) q).Source ↔ p.1 ∈ (chartAt H q.1).Source := by
  simp' only [← chart_at] with mfld_simps

@[simp, mfld_simps]
theorem mem_chart_target_iff (p : H × F) (q : Z.toTopologicalVectorBundleCore.TotalSpace) :
    p ∈ (chartAt (ModelProd H F) q).Target ↔ p.1 ∈ (chartAt H q.1).Target := by
  simp' only [← chart_at] with mfld_simps

@[simp, mfld_simps]
theorem coe_chart_at_fst (p q : Z.toTopologicalVectorBundleCore.TotalSpace) :
    ((chartAt (ModelProd H F) q) p).1 = chartAt H q.1 p.1 :=
  rfl

@[simp, mfld_simps]
theorem coe_chart_at_symm_fst (p : H × F) (q : Z.toTopologicalVectorBundleCore.TotalSpace) :
    ((chartAt (ModelProd H F) q).symm p).1 = ((chartAt H q.1).symm : H → M) p.1 :=
  rfl

/-- Smooth manifold structure on the total space of a basic smooth bundle -/
instance to_smooth_manifold : SmoothManifoldWithCorners (I.Prod 𝓘(𝕜, F)) Z.toTopologicalVectorBundleCore.TotalSpace :=
  by
  /- We have to check that the charts belong to the smooth groupoid, i.e., they are smooth on their
    source, and their inverses are smooth on the target. Since both objects are of the same kind, it
    suffices to prove the first statement in A below, and then glue back the pieces at the end. -/
  let J := ModelWithCorners.toLocalEquiv (I.prod 𝓘(𝕜, F))
  have A :
    ∀ (e e' : LocalHomeomorph M H) (he : e ∈ atlas H M) (he' : e' ∈ atlas H M),
      ContDiffOn 𝕜 ∞ (J ∘ (Z.chart he).symm.trans (Z.chart he') ∘ J.symm)
        (J.symm ⁻¹' ((Z.chart he).symm.trans (Z.chart he')).Source ∩ range J) :=
    by
    intro e e' he he'
    have :
      J.symm ⁻¹' ((chart Z he).symm.trans (chart Z he')).Source ∩ range J =
        (I.symm ⁻¹' (e.symm.trans e').Source ∩ range I) ×ˢ (univ : Set F) :=
      by
      simp only [← J, ← chart, ← ModelWithCorners.prod]
      mfld_set_tac
    rw [this]
    -- check separately that the two components of the coordinate change are smooth
    apply ContDiffOn.prod
    show
      ContDiffOn 𝕜 ∞ (fun p : E × F => (I ∘ e' ∘ e.symm ∘ I.symm) p.1)
        ((I.symm ⁻¹' (e.symm.trans e').Source ∩ range I) ×ˢ (univ : Set F))
    · -- the coordinate change on the base is just a coordinate change for `M`, smooth since
      -- `M` is smooth
      have A : ContDiffOn 𝕜 ∞ (I ∘ e.symm.trans e' ∘ I.symm) (I.symm ⁻¹' (e.symm.trans e').Source ∩ range I) :=
        (HasGroupoid.compatible (contDiffGroupoid ∞ I) he he').1
      have B :
        ContDiffOn 𝕜 ∞ (fun p : E × F => p.1) ((I.symm ⁻¹' (e.symm.trans e').Source ∩ range I) ×ˢ (univ : Set F)) :=
        cont_diff_fst.cont_diff_on
      exact ContDiffOn.comp A B (prod_subset_preimage_fst _ _)
      
    show
      ContDiffOn 𝕜 ∞
        (fun p : E × F =>
          Z.coord_change ⟨chart_at H (e.symm (I.symm p.1)), _⟩ ⟨e', he'⟩
            ((chart_at H (e.symm (I.symm p.1)) : M → H) (e.symm (I.symm p.1)))
            (Z.coord_change ⟨e, he⟩ ⟨chart_at H (e.symm (I.symm p.1)), _⟩ (e (e.symm (I.symm p.1))) p.2))
        ((I.symm ⁻¹' (e.symm.trans e').Source ∩ range I) ×ˢ (univ : Set F))
    · /- The coordinate change in the fiber is more complicated as its definition involves the
            reference chart chosen at each point. However, it appears with its inverse, so using the
            cocycle property one can get rid of it, and then conclude using the smoothness of the
            cocycle as given in the definition of basic smooth bundles. -/
      have := Z.coord_change_smooth ⟨e, he⟩ ⟨e', he'⟩
      rw [I.image_eq] at this
      apply ContDiffOn.congr this
      rintro ⟨x, v⟩ hx
      simp' only with mfld_simps  at hx
      let f := chart_at H (e.symm (I.symm x))
      have A : I.symm x ∈ ((e.symm.trans f).trans (f.symm.trans e')).Source := by
        simp' only [← hx.1.1, ← hx.1.2] with mfld_simps
      rw [e.right_inv hx.1.1]
      have := Z.coord_change_comp ⟨e, he⟩ ⟨f, chart_mem_atlas _ _⟩ ⟨e', he'⟩ (I.symm x) A v
      simpa only using this
      
  refine' @SmoothManifoldWithCorners.mk _ _ _ _ _ _ _ _ _ _ _ ⟨_⟩
  intro e₀ e₀' he₀ he₀'
  rcases(Z.mem_atlas_iff _).1 he₀ with ⟨e, he, rfl⟩
  rcases(Z.mem_atlas_iff _).1 he₀' with ⟨e', he', rfl⟩
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid]
  exact ⟨A e e' he he', A e' e he' he⟩

end BasicSmoothVectorBundleCore

section TangentBundle

variable {𝕜 : Type _} [NondiscreteNormedField 𝕜] {E : Type _} [NormedGroup E] [NormedSpace 𝕜 E] {H : Type _}
  [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) (M : Type _) [TopologicalSpace M] [ChartedSpace H M]
  [SmoothManifoldWithCorners I M]

/-- Basic smooth bundle core version of the tangent bundle of a smooth manifold `M` modelled over a
model with corners `I` on `(E, H)`. The fibers are equal to `E`, and the coordinate change in the
fiber corresponds to the derivative of the coordinate change in `M`. -/
@[simps]
def tangentBundleCore : BasicSmoothVectorBundleCore I M E where
  coordChange := fun i j x => fderivWithin 𝕜 (I ∘ j.1 ∘ i.1.symm ∘ I.symm) (Range I) (I x)
  coord_change_smooth_clm := fun i j => by
    rw [I.image_eq]
    have A : ContDiffOn 𝕜 ∞ (I ∘ i.1.symm.trans j.1 ∘ I.symm) (I.symm ⁻¹' (i.1.symm.trans j.1).Source ∩ range I) :=
      (HasGroupoid.compatible (contDiffGroupoid ∞ I) i.2 j.2).1
    have B : UniqueDiffOn 𝕜 (I.symm ⁻¹' (i.1.symm.trans j.1).Source ∩ range I) := I.unique_diff_preimage_source
    have C :
      ContDiffOn 𝕜 ∞
        (fun p : E × E =>
          (fderivWithin 𝕜 (I ∘ j.1 ∘ i.1.symm ∘ I.symm) (I.symm ⁻¹' (i.1.symm.trans j.1).Source ∩ range I) p.1 : E → E)
            p.2)
        ((I.symm ⁻¹' (i.1.symm.trans j.1).Source ∩ range I) ×ˢ (univ : Set E)) :=
      cont_diff_on_fderiv_within_apply A B le_top
    have D :
      ∀,
        ∀ x ∈ I.symm ⁻¹' (i.1.symm.trans j.1).Source ∩ range I,
          ∀,
            fderivWithin 𝕜 (I ∘ j.1 ∘ i.1.symm ∘ I.symm) (range I) x =
              fderivWithin 𝕜 (I ∘ j.1 ∘ i.1.symm ∘ I.symm) (I.symm ⁻¹' (i.1.symm.trans j.1).Source ∩ range I) x :=
      by
      intro x hx
      have N : I.symm ⁻¹' (i.1.symm.trans j.1).Source ∈ nhds x :=
        I.continuous_symm.continuous_at.preimage_mem_nhds (IsOpen.mem_nhds (LocalHomeomorph.open_source _) hx.1)
      symm
      rw [inter_comm]
      exact fderiv_within_inter N (I.unique_diff _ hx.2)
    apply (A.fderiv_within B le_top).congr
    intro x hx
    simp' only with mfld_simps  at hx
    simp' only [← hx, ← D] with mfld_simps
  coord_change_self := fun i x hx v => by
    /- Locally, a self-change of coordinate is just the identity, thus its derivative is the
        identity. One just needs to write this carefully, paying attention to the sets where the
        functions are defined. -/
    have A : I.symm ⁻¹' (i.1.symm.trans i.1).Source ∩ range I ∈ 𝓝[range I] I x := by
      rw [inter_comm]
      apply inter_mem_nhds_within
      apply I.continuous_symm.continuous_at.preimage_mem_nhds (IsOpen.mem_nhds (LocalHomeomorph.open_source _) _)
      simp' only [← hx, ← i.1.map_target] with mfld_simps
    have B : ∀ᶠ y in 𝓝[range I] I x, (I ∘ i.1 ∘ i.1.symm ∘ I.symm) y = (id : E → E) y := by
      filter_upwards [A] with _ hy
      rw [← I.image_eq] at hy
      rcases hy with ⟨z, hz⟩
      simp' only with mfld_simps  at hz
      simp' only [← hz.2.symm, ← hz.1] with mfld_simps
    have C :
      fderivWithin 𝕜 (I ∘ i.1 ∘ i.1.symm ∘ I.symm) (range I) (I x) = fderivWithin 𝕜 (id : E → E) (range I) (I x) :=
      Filter.EventuallyEq.fderiv_within_eq I.unique_diff_at_image B
        (by
          simp' only [← hx] with mfld_simps)
    rw [fderiv_within_id I.unique_diff_at_image] at C
    rw [C]
    rfl
  coord_change_comp := fun i j u x hx => by
    /- The cocycle property is just the fact that the derivative of a composition is the product of
        the derivatives. One needs however to check that all the functions one considers are smooth, and
        to pay attention to the domains where these functions are defined, making this proof a little
        bit cumbersome although there is nothing complicated here. -/
    have M : I x ∈ I.symm ⁻¹' ((i.1.symm.trans j.1).trans (j.1.symm.trans u.1)).Source ∩ range I :=
      ⟨by
        simpa only [← mem_preimage, ← ModelWithCorners.left_inv] using hx, mem_range_self _⟩
    have U :
      UniqueDiffWithinAt 𝕜 (I.symm ⁻¹' ((i.1.symm.trans j.1).trans (j.1.symm.trans u.1)).Source ∩ range I) (I x) :=
      I.unique_diff_preimage_source _ M
    have A :
      fderivWithin 𝕜 ((I ∘ u.1 ∘ j.1.symm ∘ I.symm) ∘ I ∘ j.1 ∘ i.1.symm ∘ I.symm)
          (I.symm ⁻¹' ((i.1.symm.trans j.1).trans (j.1.symm.trans u.1)).Source ∩ range I) (I x) =
        (fderivWithin 𝕜 (I ∘ u.1 ∘ j.1.symm ∘ I.symm) (I.symm ⁻¹' (j.1.symm.trans u.1).Source ∩ range I)
              ((I ∘ j.1 ∘ i.1.symm ∘ I.symm) (I x))).comp
          (fderivWithin 𝕜 (I ∘ j.1 ∘ i.1.symm ∘ I.symm)
            (I.symm ⁻¹' ((i.1.symm.trans j.1).trans (j.1.symm.trans u.1)).Source ∩ range I) (I x)) :=
      by
      apply fderivWithin.comp _ _ _ _ U
      show
        DifferentiableWithinAt 𝕜 (I ∘ j.1 ∘ i.1.symm ∘ I.symm)
          (I.symm ⁻¹' ((i.1.symm.trans j.1).trans (j.1.symm.trans u.1)).Source ∩ range I) (I x)
      · have A : ContDiffOn 𝕜 ∞ (I ∘ i.1.symm.trans j.1 ∘ I.symm) (I.symm ⁻¹' (i.1.symm.trans j.1).Source ∩ range I) :=
          (HasGroupoid.compatible (contDiffGroupoid ∞ I) i.2 j.2).1
        have B :
          DifferentiableOn 𝕜 (I ∘ j.1 ∘ i.1.symm ∘ I.symm)
            (I.symm ⁻¹' ((i.1.symm.trans j.1).trans (j.1.symm.trans u.1)).Source ∩ range I) :=
          by
          apply (A.differentiable_on le_top).mono
          have : ((i.1.symm.trans j.1).trans (j.1.symm.trans u.1)).Source ⊆ (i.1.symm.trans j.1).Source :=
            inter_subset_left _ _
          exact inter_subset_inter (preimage_mono this) (subset.refl (range I))
        apply B
        simpa only with mfld_simps using hx
        
      show
        DifferentiableWithinAt 𝕜 (I ∘ u.1 ∘ j.1.symm ∘ I.symm) (I.symm ⁻¹' (j.1.symm.trans u.1).Source ∩ range I)
          ((I ∘ j.1 ∘ i.1.symm ∘ I.symm) (I x))
      · have A : ContDiffOn 𝕜 ∞ (I ∘ j.1.symm.trans u.1 ∘ I.symm) (I.symm ⁻¹' (j.1.symm.trans u.1).Source ∩ range I) :=
          (HasGroupoid.compatible (contDiffGroupoid ∞ I) j.2 u.2).1
        apply A.differentiable_on le_top
        rw [LocalHomeomorph.trans_source] at hx
        simp' only with mfld_simps
        exact hx.2
        
      show
        I.symm ⁻¹' ((i.1.symm.trans j.1).trans (j.1.symm.trans u.1)).Source ∩ range I ⊆
          I ∘ j.1 ∘ i.1.symm ∘ I.symm ⁻¹' (I.symm ⁻¹' (j.1.symm.trans u.1).Source ∩ range I)
      · intro y hy
        simp' only with mfld_simps  at hy
        rw [LocalHomeomorph.left_inv] at hy
        · simp' only [← hy] with mfld_simps
          
        · exact hy.1.1.2
          
        
    have B :
      fderivWithin 𝕜 ((I ∘ u.1 ∘ j.1.symm ∘ I.symm) ∘ I ∘ j.1 ∘ i.1.symm ∘ I.symm)
          (I.symm ⁻¹' ((i.1.symm.trans j.1).trans (j.1.symm.trans u.1)).Source ∩ range I) (I x) =
        fderivWithin 𝕜 (I ∘ u.1 ∘ i.1.symm ∘ I.symm)
          (I.symm ⁻¹' ((i.1.symm.trans j.1).trans (j.1.symm.trans u.1)).Source ∩ range I) (I x) :=
      by
      have E :
        ∀,
          ∀ y ∈ I.symm ⁻¹' ((i.1.symm.trans j.1).trans (j.1.symm.trans u.1)).Source ∩ range I,
            ∀, ((I ∘ u.1 ∘ j.1.symm ∘ I.symm) ∘ I ∘ j.1 ∘ i.1.symm ∘ I.symm) y = (I ∘ u.1 ∘ i.1.symm ∘ I.symm) y :=
        by
        intro y hy
        simp only [← Function.comp_app, ← ModelWithCorners.left_inv]
        rw [j.1.left_inv]
        exact hy.1.1.2
      exact fderiv_within_congr U E (E _ M)
    have C :
      fderivWithin 𝕜 (I ∘ u.1 ∘ i.1.symm ∘ I.symm)
          (I.symm ⁻¹' ((i.1.symm.trans j.1).trans (j.1.symm.trans u.1)).Source ∩ range I) (I x) =
        fderivWithin 𝕜 (I ∘ u.1 ∘ i.1.symm ∘ I.symm) (range I) (I x) :=
      by
      rw [inter_comm]
      apply fderiv_within_inter _ I.unique_diff_at_image
      apply I.continuous_symm.continuous_at.preimage_mem_nhds (IsOpen.mem_nhds (LocalHomeomorph.open_source _) _)
      simpa only [← ModelWithCorners.left_inv] using hx
    have D :
      fderivWithin 𝕜 (I ∘ u.1 ∘ j.1.symm ∘ I.symm) (I.symm ⁻¹' (j.1.symm.trans u.1).Source ∩ range I)
          ((I ∘ j.1 ∘ i.1.symm ∘ I.symm) (I x)) =
        fderivWithin 𝕜 (I ∘ u.1 ∘ j.1.symm ∘ I.symm) (range I) ((I ∘ j.1 ∘ i.1.symm ∘ I.symm) (I x)) :=
      by
      rw [inter_comm]
      apply fderiv_within_inter _ I.unique_diff_at_image
      apply I.continuous_symm.continuous_at.preimage_mem_nhds (IsOpen.mem_nhds (LocalHomeomorph.open_source _) _)
      rw [LocalHomeomorph.trans_source] at hx
      simp' only with mfld_simps
      exact hx.2
    have E :
      fderivWithin 𝕜 (I ∘ j.1 ∘ i.1.symm ∘ I.symm)
          (I.symm ⁻¹' ((i.1.symm.trans j.1).trans (j.1.symm.trans u.1)).Source ∩ range I) (I x) =
        fderivWithin 𝕜 (I ∘ j.1 ∘ i.1.symm ∘ I.symm) (range I) (I x) :=
      by
      rw [inter_comm]
      apply fderiv_within_inter _ I.unique_diff_at_image
      apply I.continuous_symm.continuous_at.preimage_mem_nhds (IsOpen.mem_nhds (LocalHomeomorph.open_source _) _)
      simpa only [← ModelWithCorners.left_inv] using hx
    rw [B, C, D, E] at A
    simp' only [← A, ← ContinuousLinearMap.coe_comp'] with mfld_simps

variable {M}

include I

/-- The tangent space at a point of the manifold `M`. It is just `E`. We could use instead
`(tangent_bundle_core I M).to_topological_vector_bundle_core.fiber x`, but we use `E` to help the
kernel.
-/
@[nolint unused_arguments]
def TangentSpace (x : M) : Type _ :=
  E

omit I

variable (M)

/-- The tangent bundle to a smooth manifold, as a Sigma type. Defined in terms of
`bundle.total_space` to be able to put a suitable topology on it. -/
-- is empty if the base manifold is empty
@[nolint has_inhabited_instance, reducible]
def TangentBundle :=
  Bundle.TotalSpace (TangentSpace I : M → Type _)

-- mathport name: «exprTM»
local notation "TM" => TangentBundle I M

/-- The projection from the tangent bundle of a smooth manifold to the manifold. As the tangent
bundle is represented internally as a sigma type, the notation `p.1` also works for the projection
of the point `p`. -/
def TangentBundle.proj : TM → M := fun p => p.1

variable {M}

@[simp, mfld_simps]
theorem TangentBundle.proj_apply (x : M) (v : TangentSpace I x) : TangentBundle.proj I M ⟨x, v⟩ = x :=
  rfl

section TangentBundleInstances

/- In general, the definition of tangent_bundle and tangent_space are not reducible, so that type
class inference does not pick wrong instances. In this section, we record the right instances for
them, noting in particular that the tangent bundle is a smooth manifold. -/
section

attribute [local reducible] TangentSpace

variable {M} (x : M)

instance : TopologicalSpace (TangentSpace I x) := by
  infer_instance

instance : AddCommGroupₓ (TangentSpace I x) := by
  infer_instance

instance : TopologicalAddGroup (TangentSpace I x) := by
  infer_instance

instance : Module 𝕜 (TangentSpace I x) := by
  infer_instance

instance : Inhabited (TangentSpace I x) :=
  ⟨0⟩

end

variable (M)

instance : TopologicalSpace TM :=
  (tangentBundleCore I M).toTopologicalVectorBundleCore.toTopologicalSpace (Atlas H M)

instance : ChartedSpace (ModelProd H E) TM :=
  (tangentBundleCore I M).toChartedSpace

instance : SmoothManifoldWithCorners I.tangent TM :=
  (tangentBundleCore I M).to_smooth_manifold

instance : TopologicalVectorBundle 𝕜 E (TangentSpace I : M → Type _) :=
  TopologicalVectorBundleCore.Fiber.topologicalVectorBundle (tangentBundleCore I M).toTopologicalVectorBundleCore

end TangentBundleInstances

variable (M)

/-- The tangent bundle projection on the basis is a continuous map. -/
theorem tangent_bundle_proj_continuous : Continuous (TangentBundle.proj I M) :=
  (tangentBundleCore I M).toTopologicalVectorBundleCore.continuous_proj

/-- The tangent bundle projection on the basis is an open map. -/
theorem tangent_bundle_proj_open : IsOpenMap (TangentBundle.proj I M) :=
  (tangentBundleCore I M).toTopologicalVectorBundleCore.is_open_map_proj

/-- In the tangent bundle to the model space, the charts are just the canonical identification
between a product type and a sigma type, a.k.a. `equiv.sigma_equiv_prod`. -/
@[simp, mfld_simps]
theorem tangent_bundle_model_space_chart_at (p : TangentBundle I H) :
    (chartAt (ModelProd H E) p).toLocalEquiv = (Equivₓ.sigmaEquivProd H E).toLocalEquiv := by
  have A : ∀ x_fst, fderivWithin 𝕜 (I ∘ I.symm) (range I) (I x_fst) = ContinuousLinearMap.id 𝕜 E := by
    intro x_fst
    have : fderivWithin 𝕜 (I ∘ I.symm) (range I) (I x_fst) = fderivWithin 𝕜 id (range I) (I x_fst) := by
      refine'
        fderiv_within_congr I.unique_diff_at_image (fun y hy => _)
          (by
            simp )
      exact ModelWithCorners.right_inv _ hy
    rwa [fderiv_within_id I.unique_diff_at_image] at this
  ext x : 1
  show (chart_at (ModelProd H E) p : TangentBundle I H → ModelProd H E) x = (Equivₓ.sigmaEquivProd H E) x
  · cases x
    simp' only [← chart_at, ← BasicSmoothVectorBundleCore.chart, ← tangentBundleCore, ←
      BasicSmoothVectorBundleCore.toTopologicalVectorBundleCore, ← A, ← Prod.mk.inj_iff, ←
      ContinuousLinearMap.coe_id'] with mfld_simps
    exact (tangentBundleCore I H).coord_change_self _ _ trivialₓ x_snd
    
  show ∀ x, (chart_at (ModelProd H E) p).toLocalEquiv.symm x = (Equivₓ.sigmaEquivProd H E).symm x
  · rintro ⟨x_fst, x_snd⟩
    simp' only [← BasicSmoothVectorBundleCore.toTopologicalVectorBundleCore, ← tangentBundleCore, ← A, ←
      ContinuousLinearMap.coe_id', ← BasicSmoothVectorBundleCore.chart, ← chart_at, ← ContinuousLinearMap.coe_coe, ←
      Sigma.mk.inj_iff] with mfld_simps
    
  show (chart_at (ModelProd H E) p).toLocalEquiv.Source = univ
  · simp' only [← chart_at] with mfld_simps
    

@[simp, mfld_simps]
theorem tangent_bundle_model_space_coe_chart_at (p : TangentBundle I H) :
    ⇑(chartAt (ModelProd H E) p) = Equivₓ.sigmaEquivProd H E := by
  unfold_coes
  simp' only with mfld_simps

@[simp, mfld_simps]
theorem tangent_bundle_model_space_coe_chart_at_symm (p : TangentBundle I H) :
    ((chartAt (ModelProd H E) p).symm : ModelProd H E → TangentBundle I H) = (Equivₓ.sigmaEquivProd H E).symm := by
  unfold_coes
  simp' only with mfld_simps

variable (H)

/-- The canonical identification between the tangent bundle to the model space and the product,
as a homeomorphism -/
def tangentBundleModelSpaceHomeomorph : TangentBundle I H ≃ₜ ModelProd H E :=
  { Equivₓ.sigmaEquivProd H E with
    continuous_to_fun := by
      let p : TangentBundle I H := ⟨I.symm (0 : E), (0 : E)⟩
      have : Continuous (chart_at (ModelProd H E) p) := by
        rw [continuous_iff_continuous_on_univ]
        convert LocalHomeomorph.continuous_on _
        simp' only with mfld_simps
      simpa only with mfld_simps using this,
    continuous_inv_fun := by
      let p : TangentBundle I H := ⟨I.symm (0 : E), (0 : E)⟩
      have : Continuous (chart_at (ModelProd H E) p).symm := by
        rw [continuous_iff_continuous_on_univ]
        convert LocalHomeomorph.continuous_on _
        simp' only with mfld_simps
      simpa only with mfld_simps using this }

@[simp, mfld_simps]
theorem tangent_bundle_model_space_homeomorph_coe :
    (tangentBundleModelSpaceHomeomorph H I : TangentBundle I H → ModelProd H E) = Equivₓ.sigmaEquivProd H E :=
  rfl

@[simp, mfld_simps]
theorem tangent_bundle_model_space_homeomorph_coe_symm :
    ((tangentBundleModelSpaceHomeomorph H I).symm : ModelProd H E → TangentBundle I H) =
      (Equivₓ.sigmaEquivProd H E).symm :=
  rfl

end TangentBundle

