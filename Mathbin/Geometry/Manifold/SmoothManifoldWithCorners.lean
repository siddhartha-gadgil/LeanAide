/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathbin.Analysis.Calculus.ContDiff
import Mathbin.Geometry.Manifold.ChartedSpace

/-!
# Smooth manifolds (possibly with boundary or corners)

A smooth manifold is a manifold modelled on a normed vector space, or a subset like a
half-space (to get manifolds with boundaries) for which the changes of coordinates are smooth maps.
We define a model with corners as a map `I : H → E` embedding nicely the topological space `H` in
the vector space `E` (or more precisely as a structure containing all the relevant properties).
Given such a model with corners `I` on `(E, H)`, we define the groupoid of local
homeomorphisms of `H` which are smooth when read in `E` (for any regularity `n : with_top ℕ`).
With this groupoid at hand and the general machinery of charted spaces, we thus get the notion
of `C^n` manifold with respect to any model with corners `I` on `(E, H)`. We also introduce a
specific type class for `C^∞` manifolds as these are the most commonly used.

## Main definitions

* `model_with_corners 𝕜 E H` :
  a structure containing informations on the way a space `H` embeds in a
  model vector space E over the field `𝕜`. This is all that is needed to
  define a smooth manifold with model space `H`, and model vector space `E`.
* `model_with_corners_self 𝕜 E` :
  trivial model with corners structure on the space `E` embedded in itself by the identity.
* `cont_diff_groupoid n I` :
  when `I` is a model with corners on `(𝕜, E, H)`, this is the groupoid of local homeos of `H`
  which are of class `C^n` over the normed field `𝕜`, when read in `E`.
* `smooth_manifold_with_corners I M` :
  a type class saying that the charted space `M`, modelled on the space `H`, has `C^∞` changes of
  coordinates with respect to the model with corners `I` on `(𝕜, E, H)`. This type class is just
  a shortcut for `has_groupoid M (cont_diff_groupoid ∞ I)`.
* `ext_chart_at I x`:
  in a smooth manifold with corners with the model `I` on `(E, H)`, the charts take values in `H`,
  but often we may want to use their `E`-valued version, obtained by composing the charts with `I`.
  Since the target is in general not open, we can not register them as local homeomorphisms, but
  we register them as local equivs. `ext_chart_at I x` is the canonical such local equiv around `x`.

As specific examples of models with corners, we define (in the file `real_instances.lean`)
* `model_with_corners_self ℝ (euclidean_space (fin n))` for the model space used to define
  `n`-dimensional real manifolds without boundary (with notation `𝓡 n` in the locale `manifold`)
* `model_with_corners ℝ (euclidean_space (fin n)) (euclidean_half_space n)` for the model space
  used to define `n`-dimensional real manifolds with boundary (with notation `𝓡∂ n` in the locale
  `manifold`)
* `model_with_corners ℝ (euclidean_space (fin n)) (euclidean_quadrant n)` for the model space used
  to define `n`-dimensional real manifolds with corners

With these definitions at hand, to invoke an `n`-dimensional real manifold without boundary,
one could use

  `variables {n : ℕ} {M : Type*} [topological_space M] [charted_space (euclidean_space (fin n)) M]
   [smooth_manifold_with_corners (𝓡 n) M]`.

However, this is not the recommended way: a theorem proved using this assumption would not apply
for instance to the tangent space of such a manifold, which is modelled on
`(euclidean_space (fin n)) × (euclidean_space (fin n))` and not on `euclidean_space (fin (2 * n))`!
In the same way, it would not apply to product manifolds, modelled on
`(euclidean_space (fin n)) × (euclidean_space (fin m))`.
The right invocation does not focus on one specific construction, but on all constructions sharing
the right properties, like

  `variables {E : Type*} [normed_group E] [normed_space ℝ E] [finite_dimensional ℝ E]
  {I : model_with_corners ℝ E E} [I.boundaryless]
  {M : Type*} [topological_space M] [charted_space E M] [smooth_manifold_with_corners I M]`

Here, `I.boundaryless` is a typeclass property ensuring that there is no boundary (this is for
instance the case for `model_with_corners_self`, or products of these). Note that one could consider
as a natural assumption to only use the trivial model with corners `model_with_corners_self ℝ E`,
but again in product manifolds the natural model with corners will not be this one but the product
one (and they are not defeq as `(λp : E × F, (p.1, p.2))` is not defeq to the identity). So, it is
important to use the above incantation to maximize the applicability of theorems.

## Implementation notes

We want to talk about manifolds modelled on a vector space, but also on manifolds with
boundary, modelled on a half space (or even manifolds with corners). For the latter examples,
we still want to define smooth functions, tangent bundles, and so on. As smooth functions are
well defined on vector spaces or subsets of these, one could take for model space a subtype of a
vector space. With the drawback that the whole vector space itself (which is the most basic
example) is not directly a subtype of itself: the inclusion of `univ : set E` in `set E` would
show up in the definition, instead of `id`.

A good abstraction covering both cases it to have a vector
space `E` (with basic example the Euclidean space), a model space `H` (with basic example the upper
half space), and an embedding of `H` into `E` (which can be the identity for `H = E`, or
`subtype.val` for manifolds with corners). We say that the pair `(E, H)` with their embedding is a
model with corners, and we encompass all the relevant properties (in particular the fact that the
image of `H` in `E` should have unique differentials) in the definition of `model_with_corners`.

We concentrate on `C^∞` manifolds: all the definitions work equally well for `C^n` manifolds, but
later on it is a pain to carry all over the smoothness parameter, especially when one wants to deal
with `C^k` functions as there would be additional conditions `k ≤ n` everywhere. Since one deals
almost all the time with `C^∞` (or analytic) manifolds, this seems to be a reasonable choice that
one could revisit later if needed. `C^k` manifolds are still available, but they should be called
using `has_groupoid M (cont_diff_groupoid k I)` where `I` is the model with corners.

I have considered using the model with corners `I` as a typeclass argument, possibly `out_param`, to
get lighter notations later on, but it did not turn out right, as on `E × F` there are two natural
model with corners, the trivial (identity) one, and the product one, and they are not defeq and one
needs to indicate to Lean which one we want to use.
This means that when talking on objects on manifolds one will most often need to specify the model
with corners one is using. For instance, the tangent bundle will be `tangent_bundle I M` and the
derivative will be `mfderiv I I' f`, instead of the more natural notations `tangent_bundle 𝕜 M` and
`mfderiv 𝕜 f` (the field has to be explicit anyway, as some manifolds could be considered both as
real and complex manifolds).
-/


noncomputable section

universe u v w u' v' w'

open Set Filter

open Manifold Filter TopologicalSpace

-- mathport name: «expr∞»
localized [Manifold] notation "∞" => (⊤ : WithTop ℕ)

section ModelWithCorners

/-! ### Models with corners. -/


/-- A structure containing informations on the way a space `H` embeds in a
model vector space `E` over the field `𝕜`. This is all what is needed to
define a smooth manifold with model space `H`, and model vector space `E`.
-/
@[nolint has_inhabited_instance]
structure ModelWithCorners (𝕜 : Type _) [NondiscreteNormedField 𝕜] (E : Type _) [NormedGroup E] [NormedSpace 𝕜 E]
  (H : Type _) [TopologicalSpace H] extends LocalEquiv H E where
  source_eq : source = univ
  unique_diff' : UniqueDiffOn 𝕜 to_local_equiv.Target
  continuous_to_fun : Continuous to_fun := by
    run_tac
      tactic.interactive.continuity'
  continuous_inv_fun : Continuous inv_fun := by
    run_tac
      tactic.interactive.continuity'

attribute [simp, mfld_simps] ModelWithCorners.source_eq

/-- A vector space is a model with corners. -/
def modelWithCornersSelf (𝕜 : Type _) [NondiscreteNormedField 𝕜] (E : Type _) [NormedGroup E] [NormedSpace 𝕜 E] :
    ModelWithCorners 𝕜 E E where
  toLocalEquiv := LocalEquiv.refl E
  source_eq := rfl
  unique_diff' := unique_diff_on_univ
  continuous_to_fun := continuous_id
  continuous_inv_fun := continuous_id

-- mathport name: «expr𝓘( , )»
localized [Manifold] notation "𝓘(" 𝕜 ", " E ")" => modelWithCornersSelf 𝕜 E

-- mathport name: «expr𝓘( )»
localized [Manifold] notation "𝓘(" 𝕜 ")" => modelWithCornersSelf 𝕜 𝕜

section

variable {𝕜 : Type _} [NondiscreteNormedField 𝕜] {E : Type _} [NormedGroup E] [NormedSpace 𝕜 E] {H : Type _}
  [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)

namespace ModelWithCorners

instance : CoeFun (ModelWithCorners 𝕜 E H) fun _ => H → E :=
  ⟨fun e => e.toFun⟩

/-- The inverse to a model with corners, only registered as a local equiv. -/
protected def symm : LocalEquiv E H :=
  I.toLocalEquiv.symm

/-- See Note [custom simps projection]. We need to specify this projection explicitly in this case,
  because it is a composition of multiple projections. -/
def Simps.apply (𝕜 : Type _) [NondiscreteNormedField 𝕜] (E : Type _) [NormedGroup E] [NormedSpace 𝕜 E] (H : Type _)
    [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) : H → E :=
  I

/-- See Note [custom simps projection] -/
def Simps.symmApply (𝕜 : Type _) [NondiscreteNormedField 𝕜] (E : Type _) [NormedGroup E] [NormedSpace 𝕜 E] (H : Type _)
    [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) : E → H :=
  I.symm

initialize_simps_projections ModelWithCorners (to_local_equiv_to_fun → apply, to_local_equiv_inv_fun → symmApply,
  to_local_equiv_source → Source, to_local_equiv_target → Target, -toLocalEquiv)

-- Register a few lemmas to make sure that `simp` puts expressions in normal form
@[simp, mfld_simps]
theorem to_local_equiv_coe : (I.toLocalEquiv : H → E) = I :=
  rfl

@[simp, mfld_simps]
theorem mk_coe (e : LocalEquiv H E) (a b c d) :
    ((ModelWithCorners.mk e a b c d : ModelWithCorners 𝕜 E H) : H → E) = (e : H → E) :=
  rfl

@[simp, mfld_simps]
theorem to_local_equiv_coe_symm : (I.toLocalEquiv.symm : E → H) = I.symm :=
  rfl

@[simp, mfld_simps]
theorem mk_symm (e : LocalEquiv H E) (a b c d) :
    (ModelWithCorners.mk e a b c d : ModelWithCorners 𝕜 E H).symm = e.symm :=
  rfl

@[continuity]
protected theorem continuous : Continuous I :=
  I.continuous_to_fun

protected theorem continuous_at {x} : ContinuousAt I x :=
  I.Continuous.ContinuousAt

protected theorem continuous_within_at {s x} : ContinuousWithinAt I s x :=
  I.ContinuousAt.ContinuousWithinAt

@[continuity]
theorem continuous_symm : Continuous I.symm :=
  I.continuous_inv_fun

theorem continuous_at_symm {x} : ContinuousAt I.symm x :=
  I.continuous_symm.ContinuousAt

theorem continuous_within_at_symm {s x} : ContinuousWithinAt I.symm s x :=
  I.continuous_symm.ContinuousWithinAt

theorem continuous_on_symm {s} : ContinuousOn I.symm s :=
  I.continuous_symm.ContinuousOn

@[simp, mfld_simps]
theorem target_eq : I.Target = Range (I : H → E) := by
  rw [← image_univ, ← I.source_eq]
  exact I.to_local_equiv.image_source_eq_target.symm

protected theorem unique_diff : UniqueDiffOn 𝕜 (Range I) :=
  I.target_eq ▸ I.unique_diff'

@[simp, mfld_simps]
protected theorem left_inv (x : H) : I.symm (I x) = x := by
  refine' I.left_inv' _
  simp

protected theorem left_inverse : Function.LeftInverse I.symm I :=
  I.left_inv

@[simp, mfld_simps]
theorem symm_comp_self : I.symm ∘ I = id :=
  I.LeftInverse.comp_eq_id

protected theorem right_inv_on : RightInvOn I.symm I (Range I) :=
  I.LeftInverse.right_inv_on_range

@[simp, mfld_simps]
protected theorem right_inv {x : E} (hx : x ∈ Range I) : I (I.symm x) = x :=
  I.RightInvOn hx

protected theorem image_eq (s : Set H) : I '' s = I.symm ⁻¹' s ∩ Range I := by
  refine' (I.to_local_equiv.image_eq_target_inter_inv_preimage _).trans _
  · rw [I.source_eq]
    exact subset_univ _
    
  · rw [inter_comm, I.target_eq, I.to_local_equiv_coe_symm]
    

protected theorem closed_embedding : ClosedEmbedding I :=
  I.LeftInverse.ClosedEmbedding I.continuous_symm I.Continuous

theorem closed_range : IsClosed (Range I) :=
  I.ClosedEmbedding.closed_range

theorem map_nhds_eq (x : H) : map I (𝓝 x) = 𝓝[Range I] I x :=
  I.ClosedEmbedding.toEmbedding.map_nhds_eq x

theorem image_mem_nhds_within {x : H} {s : Set H} (hs : s ∈ 𝓝 x) : I '' s ∈ 𝓝[Range I] I x :=
  I.map_nhds_eq x ▸ image_mem_map hs

theorem symm_map_nhds_within_range (x : H) : map I.symm (𝓝[Range I] I x) = 𝓝 x := by
  rw [← I.map_nhds_eq, map_map, I.symm_comp_self, map_id]

theorem unique_diff_preimage {s : Set H} (hs : IsOpen s) : UniqueDiffOn 𝕜 (I.symm ⁻¹' s ∩ Range I) := by
  rw [inter_comm]
  exact I.unique_diff.inter (hs.preimage I.continuous_inv_fun)

theorem unique_diff_preimage_source {β : Type _} [TopologicalSpace β] {e : LocalHomeomorph H β} :
    UniqueDiffOn 𝕜 (I.symm ⁻¹' e.Source ∩ Range I) :=
  I.unique_diff_preimage e.open_source

theorem unique_diff_at_image {x : H} : UniqueDiffWithinAt 𝕜 (Range I) (I x) :=
  I.unique_diff _ (mem_range_self _)

protected theorem locally_compact [LocallyCompactSpace E] (I : ModelWithCorners 𝕜 E H) : LocallyCompactSpace H := by
  have : ∀ x : H, (𝓝 x).HasBasis (fun s => s ∈ 𝓝 (I x) ∧ IsCompact s) fun s => I.symm '' (s ∩ range ⇑I) := by
    intro x
    rw [← I.symm_map_nhds_within_range]
    exact ((compact_basis_nhds (I x)).inf_principal _).map _
  refine' locally_compact_space_of_has_basis this _
  rintro x s ⟨-, hsc⟩
  exact (hsc.inter_right I.closed_range).Image I.continuous_symm

open TopologicalSpace

protected theorem second_countable_topology [SecondCountableTopology E] (I : ModelWithCorners 𝕜 E H) :
    SecondCountableTopology H :=
  I.ClosedEmbedding.toEmbedding.SecondCountableTopology

end ModelWithCorners

section

variable (𝕜 E)

/-- In the trivial model with corners, the associated local equiv is the identity. -/
@[simp, mfld_simps]
theorem model_with_corners_self_local_equiv : 𝓘(𝕜, E).toLocalEquiv = LocalEquiv.refl E :=
  rfl

@[simp, mfld_simps]
theorem model_with_corners_self_coe : (𝓘(𝕜, E) : E → E) = id :=
  rfl

@[simp, mfld_simps]
theorem model_with_corners_self_coe_symm : (𝓘(𝕜, E).symm : E → E) = id :=
  rfl

end

end

section ModelWithCornersProd

/-- Given two model_with_corners `I` on `(E, H)` and `I'` on `(E', H')`, we define the model with
corners `I.prod I'` on `(E × E', model_prod H H')`. This appears in particular for the manifold
structure on the tangent bundle to a manifold modelled on `(E, H)`: it will be modelled on
`(E × E, H × E)`. See note [Manifold type tags] for explanation about `model_prod H H'`
vs `H × H'`. -/
@[simps (config := lemmasOnly)]
def ModelWithCorners.prod {𝕜 : Type u} [NondiscreteNormedField 𝕜] {E : Type v} [NormedGroup E] [NormedSpace 𝕜 E]
    {H : Type w} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) {E' : Type v'} [NormedGroup E'] [NormedSpace 𝕜 E']
    {H' : Type w'} [TopologicalSpace H'] (I' : ModelWithCorners 𝕜 E' H') :
    ModelWithCorners 𝕜 (E × E') (ModelProd H H') :=
  { I.toLocalEquiv.Prod I'.toLocalEquiv with toFun := fun x => (I x.1, I' x.2),
    invFun := fun x => (I.symm x.1, I'.symm x.2), Source := { x | x.1 ∈ I.Source ∧ x.2 ∈ I'.Source },
    source_eq := by
      simp' only [← set_of_true] with mfld_simps,
    unique_diff' := I.unique_diff'.Prod I'.unique_diff',
    continuous_to_fun := I.continuous_to_fun.prod_map I'.continuous_to_fun,
    continuous_inv_fun := I.continuous_inv_fun.prod_map I'.continuous_inv_fun }

/-- Given a finite family of `model_with_corners` `I i` on `(E i, H i)`, we define the model with
corners `pi I` on `(Π i, E i, model_pi H)`. See note [Manifold type tags] for explanation about
`model_pi H`. -/
def ModelWithCorners.pi {𝕜 : Type u} [NondiscreteNormedField 𝕜] {ι : Type v} [Fintype ι] {E : ι → Type w}
    [∀ i, NormedGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] {H : ι → Type u'} [∀ i, TopologicalSpace (H i)]
    (I : ∀ i, ModelWithCorners 𝕜 (E i) (H i)) : ModelWithCorners 𝕜 (∀ i, E i) (ModelPi H) where
  toLocalEquiv := LocalEquiv.pi fun i => (I i).toLocalEquiv
  source_eq := by
    simp' only [← Set.pi_univ] with mfld_simps
  unique_diff' := UniqueDiffOn.pi ι E _ _ fun i _ => (I i).unique_diff'
  continuous_to_fun := continuous_pi fun i => (I i).Continuous.comp (continuous_apply i)
  continuous_inv_fun := continuous_pi fun i => (I i).continuous_symm.comp (continuous_apply i)

/-- Special case of product model with corners, which is trivial on the second factor. This shows up
as the model to tangent bundles. -/
@[reducible]
def ModelWithCorners.tangent {𝕜 : Type u} [NondiscreteNormedField 𝕜] {E : Type v} [NormedGroup E] [NormedSpace 𝕜 E]
    {H : Type w} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) : ModelWithCorners 𝕜 (E × E) (ModelProd H E) :=
  I.Prod 𝓘(𝕜, E)

variable {𝕜 : Type _} [NondiscreteNormedField 𝕜] {E : Type _} [NormedGroup E] [NormedSpace 𝕜 E] {E' : Type _}
  [NormedGroup E'] [NormedSpace 𝕜 E'] {F : Type _} [NormedGroup F] [NormedSpace 𝕜 F] {F' : Type _} [NormedGroup F']
  [NormedSpace 𝕜 F'] {H : Type _} [TopologicalSpace H] {H' : Type _} [TopologicalSpace H'] {G : Type _}
  [TopologicalSpace G] {G' : Type _} [TopologicalSpace G'] {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F G}

@[simp, mfld_simps]
theorem model_with_corners_prod_to_local_equiv : (I.Prod J).toLocalEquiv = I.toLocalEquiv.Prod J.toLocalEquiv :=
  rfl

@[simp, mfld_simps]
theorem model_with_corners_prod_coe (I : ModelWithCorners 𝕜 E H) (I' : ModelWithCorners 𝕜 E' H') :
    (I.Prod I' : _ × _ → _ × _) = Prod.map I I' :=
  rfl

@[simp, mfld_simps]
theorem model_with_corners_prod_coe_symm (I : ModelWithCorners 𝕜 E H) (I' : ModelWithCorners 𝕜 E' H') :
    ((I.Prod I').symm : _ × _ → _ × _) = Prod.map I.symm I'.symm :=
  rfl

end ModelWithCornersProd

section Boundaryless

/-- Property ensuring that the model with corners `I` defines manifolds without boundary. -/
class ModelWithCorners.Boundaryless {𝕜 : Type _} [NondiscreteNormedField 𝕜] {E : Type _} [NormedGroup E]
  [NormedSpace 𝕜 E] {H : Type _} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) : Prop where
  range_eq_univ : Range I = univ

/-- The trivial model with corners has no boundary -/
instance model_with_corners_self_boundaryless (𝕜 : Type _) [NondiscreteNormedField 𝕜] (E : Type _) [NormedGroup E]
    [NormedSpace 𝕜 E] : (modelWithCornersSelf 𝕜 E).Boundaryless :=
  ⟨by
    simp ⟩

/-- If two model with corners are boundaryless, their product also is -/
instance ModelWithCorners.range_eq_univ_prod {𝕜 : Type u} [NondiscreteNormedField 𝕜] {E : Type v} [NormedGroup E]
    [NormedSpace 𝕜 E] {H : Type w} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) [I.Boundaryless] {E' : Type v'}
    [NormedGroup E'] [NormedSpace 𝕜 E'] {H' : Type w'} [TopologicalSpace H'] (I' : ModelWithCorners 𝕜 E' H')
    [I'.Boundaryless] : (I.Prod I').Boundaryless := by
  constructor
  dsimp' [← ModelWithCorners.prod, ← ModelProd]
  rw [← prod_range_range_eq, ModelWithCorners.Boundaryless.range_eq_univ, ModelWithCorners.Boundaryless.range_eq_univ,
    univ_prod_univ]

end Boundaryless

section contDiffGroupoid

/-! ### Smooth functions on models with corners -/


variable {m n : WithTop ℕ} {𝕜 : Type _} [NondiscreteNormedField 𝕜] {E : Type _} [NormedGroup E] [NormedSpace 𝕜 E]
  {H : Type _} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) {M : Type _} [TopologicalSpace M]

variable (n)

/-- Given a model with corners `(E, H)`, we define the groupoid of `C^n` transformations of `H` as
the maps that are `C^n` when read in `E` through `I`. -/
def contDiffGroupoid : StructureGroupoid H :=
  Pregroupoid.groupoid
    { property := fun f s => ContDiffOn 𝕜 n (I ∘ f ∘ I.symm) (I.symm ⁻¹' s ∩ Range I),
      comp := fun f g u v hf hg hu hv huv => by
        have : I ∘ (g ∘ f) ∘ I.symm = (I ∘ g ∘ I.symm) ∘ I ∘ f ∘ I.symm := by
          ext x
          simp
        rw [this]
        apply ContDiffOn.comp hg _
        · rintro x ⟨hx1, hx2⟩
          simp' only with mfld_simps  at hx1⊢
          exact hx1.2
          
        · refine' hf.mono _
          rintro x ⟨hx1, hx2⟩
          exact ⟨hx1.1, hx2⟩
          ,
      id_mem := by
        apply ContDiffOn.congr cont_diff_id.cont_diff_on
        rintro x ⟨hx1, hx2⟩
        rcases mem_range.1 hx2 with ⟨y, hy⟩
        rw [← hy]
        simp' only with mfld_simps,
      locality := fun f u hu H => by
        apply cont_diff_on_of_locally_cont_diff_on
        rintro y ⟨hy1, hy2⟩
        rcases mem_range.1 hy2 with ⟨x, hx⟩
        rw [← hx] at hy1⊢
        simp' only with mfld_simps  at hy1⊢
        rcases H x hy1 with ⟨v, v_open, xv, hv⟩
        have : I.symm ⁻¹' (u ∩ v) ∩ range I = I.symm ⁻¹' u ∩ range I ∩ I.symm ⁻¹' v := by
          rw [preimage_inter, inter_assoc, inter_assoc]
          congr 1
          rw [inter_comm]
        rw [this] at hv
        exact
          ⟨I.symm ⁻¹' v, v_open.preimage I.continuous_symm, by
            simpa, hv⟩,
      congr := fun f g u hu fg hf => by
        apply hf.congr
        rintro y ⟨hy1, hy2⟩
        rcases mem_range.1 hy2 with ⟨x, hx⟩
        rw [← hx] at hy1⊢
        simp' only with mfld_simps  at hy1⊢
        rw [fg _ hy1] }

variable {n}

/-- Inclusion of the groupoid of `C^n` local diffeos in the groupoid of `C^m` local diffeos when
`m ≤ n` -/
theorem cont_diff_groupoid_le (h : m ≤ n) : contDiffGroupoid n I ≤ contDiffGroupoid m I := by
  rw [contDiffGroupoid, contDiffGroupoid]
  apply groupoid_of_pregroupoid_le
  intro f s hfs
  exact ContDiffOn.of_le hfs h

/-- The groupoid of `0`-times continuously differentiable maps is just the groupoid of all
local homeomorphisms -/
theorem cont_diff_groupoid_zero_eq : contDiffGroupoid 0 I = continuousGroupoid H := by
  apply le_antisymmₓ le_top
  intro u hu
  -- we have to check that every local homeomorphism belongs to `cont_diff_groupoid 0 I`,
  -- by unfolding its definition
  change u ∈ contDiffGroupoid 0 I
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid]
  simp only [← cont_diff_on_zero]
  constructor
  · refine' I.continuous.comp_continuous_on (u.continuous_on.comp I.continuous_on_symm _)
    exact (maps_to_preimage _ _).mono_left (inter_subset_left _ _)
    
  · refine' I.continuous.comp_continuous_on (u.symm.continuous_on.comp I.continuous_on_symm _)
    exact (maps_to_preimage _ _).mono_left (inter_subset_left _ _)
    

variable (n)

/-- An identity local homeomorphism belongs to the `C^n` groupoid. -/
theorem of_set_mem_cont_diff_groupoid {s : Set H} (hs : IsOpen s) : LocalHomeomorph.ofSet s hs ∈ contDiffGroupoid n I :=
  by
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid]
  suffices h : ContDiffOn 𝕜 n (I ∘ I.symm) (I.symm ⁻¹' s ∩ range I)
  · simp [← h]
    
  have : ContDiffOn 𝕜 n id (univ : Set E) := cont_diff_id.cont_diff_on
  exact
    this.congr_mono
      (fun x hx => by
        simp [← hx.2])
      (subset_univ _)

/-- The composition of a local homeomorphism from `H` to `M` and its inverse belongs to
the `C^n` groupoid. -/
theorem symm_trans_mem_cont_diff_groupoid (e : LocalHomeomorph M H) : e.symm.trans e ∈ contDiffGroupoid n I := by
  have : e.symm.trans e ≈ LocalHomeomorph.ofSet e.target e.open_target := LocalHomeomorph.trans_symm_self _
  exact StructureGroupoid.eq_on_source _ (of_set_mem_cont_diff_groupoid n I e.open_target) this

variable {E' : Type _} [NormedGroup E'] [NormedSpace 𝕜 E'] {H' : Type _} [TopologicalSpace H']

/-- The product of two smooth local homeomorphisms is smooth. -/
theorem cont_diff_groupoid_prod {I : ModelWithCorners 𝕜 E H} {I' : ModelWithCorners 𝕜 E' H'} {e : LocalHomeomorph H H}
    {e' : LocalHomeomorph H' H'} (he : e ∈ contDiffGroupoid ⊤ I) (he' : e' ∈ contDiffGroupoid ⊤ I') :
    e.Prod e' ∈ contDiffGroupoid ⊤ (I.Prod I') := by
  cases' he with he he_symm
  cases' he' with he' he'_symm
  simp only at he he_symm he' he'_symm
  constructor <;> simp only [← LocalEquiv.prod_source, ← LocalHomeomorph.prod_to_local_equiv]
  · have h3 := ContDiffOn.prod_map he he'
    rw [← I.image_eq, ← I'.image_eq, Set.prod_image_image_eq] at h3
    rw [← (I.prod I').image_eq]
    exact h3
    
  · have h3 := ContDiffOn.prod_map he_symm he'_symm
    rw [← I.image_eq, ← I'.image_eq, Set.prod_image_image_eq] at h3
    rw [← (I.prod I').image_eq]
    exact h3
    

/-- The `C^n` groupoid is closed under restriction. -/
instance : ClosedUnderRestriction (contDiffGroupoid n I) :=
  (closed_under_restriction_iff_id_le _).mpr
    (by
      apply structure_groupoid.le_iff.mpr
      rintro e ⟨s, hs, hes⟩
      apply (contDiffGroupoid n I).eq_on_source' _ _ _ hes
      exact of_set_mem_cont_diff_groupoid n I hs)

end contDiffGroupoid

end ModelWithCorners

section SmoothManifoldWithCorners

/-! ### Smooth manifolds with corners -/


/-- Typeclass defining smooth manifolds with corners with respect to a model with corners, over a
field `𝕜` and with infinite smoothness to simplify typeclass search and statements later on. -/
@[ancestor HasGroupoid]
class SmoothManifoldWithCorners {𝕜 : Type _} [NondiscreteNormedField 𝕜] {E : Type _} [NormedGroup E] [NormedSpace 𝕜 E]
  {H : Type _} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) (M : Type _) [TopologicalSpace M]
  [ChartedSpace H M] extends HasGroupoid M (contDiffGroupoid ∞ I) : Prop

theorem SmoothManifoldWithCorners.mk' {𝕜 : Type _} [NondiscreteNormedField 𝕜] {E : Type _} [NormedGroup E]
    [NormedSpace 𝕜 E] {H : Type _} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) (M : Type _) [TopologicalSpace M]
    [ChartedSpace H M] [gr : HasGroupoid M (contDiffGroupoid ∞ I)] : SmoothManifoldWithCorners I M :=
  { gr with }

theorem smooth_manifold_with_corners_of_cont_diff_on {𝕜 : Type _} [NondiscreteNormedField 𝕜] {E : Type _}
    [NormedGroup E] [NormedSpace 𝕜 E] {H : Type _} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) (M : Type _)
    [TopologicalSpace M] [ChartedSpace H M]
    (h :
      ∀ e e' : LocalHomeomorph M H,
        e ∈ Atlas H M →
          e' ∈ Atlas H M → ContDiffOn 𝕜 ⊤ (I ∘ e.symm ≫ₕ e' ∘ I.symm) (I.symm ⁻¹' (e.symm ≫ₕ e').Source ∩ Range I)) :
    SmoothManifoldWithCorners I M :=
  { compatible := by
      have : HasGroupoid M (contDiffGroupoid ∞ I) := has_groupoid_of_pregroupoid _ h
      apply StructureGroupoid.compatible }

/-- For any model with corners, the model space is a smooth manifold -/
instance model_space_smooth {𝕜 : Type _} [NondiscreteNormedField 𝕜] {E : Type _} [NormedGroup E] [NormedSpace 𝕜 E]
    {H : Type _} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} : SmoothManifoldWithCorners I H :=
  { has_groupoid_model_space _ _ with }

end SmoothManifoldWithCorners

namespace SmoothManifoldWithCorners

/- We restate in the namespace `smooth_manifolds_with_corners` some lemmas that hold for general
charted space with a structure groupoid, avoiding the need to specify the groupoid
`cont_diff_groupoid ∞ I` explicitly. -/
variable {𝕜 : Type _} [NondiscreteNormedField 𝕜] {E : Type _} [NormedGroup E] [NormedSpace 𝕜 E] {H : Type _}
  [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) (M : Type _) [TopologicalSpace M] [ChartedSpace H M]

/-- The maximal atlas of `M` for the smooth manifold with corners structure corresponding to the
model with corners `I`. -/
def MaximalAtlas :=
  (contDiffGroupoid ∞ I).MaximalAtlas M

variable {M}

theorem mem_maximal_atlas_of_mem_atlas [SmoothManifoldWithCorners I M] {e : LocalHomeomorph M H} (he : e ∈ Atlas H M) :
    e ∈ MaximalAtlas I M :=
  StructureGroupoid.mem_maximal_atlas_of_mem_atlas _ he

theorem chart_mem_maximal_atlas [SmoothManifoldWithCorners I M] (x : M) : chartAt H x ∈ MaximalAtlas I M :=
  StructureGroupoid.chart_mem_maximal_atlas _ x

variable {I}

theorem compatible_of_mem_maximal_atlas {e e' : LocalHomeomorph M H} (he : e ∈ MaximalAtlas I M)
    (he' : e' ∈ MaximalAtlas I M) : e.symm.trans e' ∈ contDiffGroupoid ∞ I :=
  StructureGroupoid.compatible_of_mem_maximal_atlas he he'

/-- The product of two smooth manifolds with corners is naturally a smooth manifold with corners. -/
instance prod {𝕜 : Type _} [NondiscreteNormedField 𝕜] {E : Type _} [NormedGroup E] [NormedSpace 𝕜 E] {E' : Type _}
    [NormedGroup E'] [NormedSpace 𝕜 E'] {H : Type _} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {H' : Type _}
    [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'} (M : Type _) [TopologicalSpace M] [ChartedSpace H M]
    [SmoothManifoldWithCorners I M] (M' : Type _) [TopologicalSpace M'] [ChartedSpace H' M']
    [SmoothManifoldWithCorners I' M'] :
    SmoothManifoldWithCorners (I.Prod I') (M × M') where compatible := by
    rintro f g ⟨f1, f2, hf1, hf2, rfl⟩ ⟨g1, g2, hg1, hg2, rfl⟩
    rw [LocalHomeomorph.prod_symm, LocalHomeomorph.prod_trans]
    have h1 := HasGroupoid.compatible (contDiffGroupoid ⊤ I) hf1 hg1
    have h2 := HasGroupoid.compatible (contDiffGroupoid ⊤ I') hf2 hg2
    exact cont_diff_groupoid_prod h1 h2

end SmoothManifoldWithCorners

theorem LocalHomeomorph.singleton_smooth_manifold_with_corners {𝕜 : Type _} [NondiscreteNormedField 𝕜] {E : Type _}
    [NormedGroup E] [NormedSpace 𝕜 E] {H : Type _} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) {M : Type _}
    [TopologicalSpace M] (e : LocalHomeomorph M H) (h : e.Source = Set.Univ) :
    @SmoothManifoldWithCorners 𝕜 _ E _ _ H _ I M _ (e.singletonChartedSpace h) :=
  @SmoothManifoldWithCorners.mk' _ _ _ _ _ _ _ _ _ _ (id _) <| e.singleton_has_groupoid h (contDiffGroupoid ∞ I)

theorem OpenEmbedding.singleton_smooth_manifold_with_corners {𝕜 : Type _} [NondiscreteNormedField 𝕜] {E : Type _}
    [NormedGroup E] [NormedSpace 𝕜 E] {H : Type _} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) {M : Type _}
    [TopologicalSpace M] [Nonempty M] {f : M → H} (h : OpenEmbedding f) :
    @SmoothManifoldWithCorners 𝕜 _ E _ _ H _ I M _ h.singletonChartedSpace :=
  (h.toLocalHomeomorph f).singleton_smooth_manifold_with_corners I
    (by
      simp )

namespace TopologicalSpace.Opens

open TopologicalSpace

variable {𝕜 : Type _} [NondiscreteNormedField 𝕜] {E : Type _} [NormedGroup E] [NormedSpace 𝕜 E] {H : Type _}
  [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) {M : Type _} [TopologicalSpace M] [ChartedSpace H M]
  [SmoothManifoldWithCorners I M] (s : Opens M)

instance : SmoothManifoldWithCorners I s :=
  { s.HasGroupoid (contDiffGroupoid ∞ I) with }

end TopologicalSpace.Opens

section ExtendedCharts

open TopologicalSpace

variable {𝕜 : Type _} [NondiscreteNormedField 𝕜] {E : Type _} [NormedGroup E] [NormedSpace 𝕜 E] {H : Type _}
  [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) {M : Type _} [TopologicalSpace M] [ChartedSpace H M] (x : M)
  {s t : Set M}

/-!
### Extended charts

In a smooth manifold with corners, the model space is the space `H`. However, we will also
need to use extended charts taking values in the model vector space `E`. These extended charts are
not `local_homeomorph` as the target is not open in `E` in general, but we can still register them
as `local_equiv`.
-/


/-- The preferred extended chart on a manifold with corners around a point `x`, from a neighborhood
of `x` to the model vector space. -/
@[simp, mfld_simps]
def extChartAt (x : M) : LocalEquiv M E :=
  (chartAt H x).toLocalEquiv.trans I.toLocalEquiv

theorem ext_chart_at_coe : ⇑(extChartAt I x) = I ∘ chartAt H x :=
  rfl

theorem ext_chart_at_coe_symm : ⇑(extChartAt I x).symm = (chartAt H x).symm ∘ I.symm :=
  rfl

theorem ext_chart_at_source : (extChartAt I x).Source = (chartAt H x).Source := by
  rw [extChartAt, LocalEquiv.trans_source, I.source_eq, preimage_univ, inter_univ]

theorem ext_chart_at_open_source : IsOpen (extChartAt I x).Source := by
  rw [ext_chart_at_source]
  exact (chart_at H x).open_source

theorem mem_ext_chart_source : x ∈ (extChartAt I x).Source := by
  simp only [← ext_chart_at_source, ← mem_chart_source]

theorem ext_chart_at_to_inv : (extChartAt I x).symm ((extChartAt I x) x) = x :=
  (extChartAt I x).left_inv (mem_ext_chart_source I x)

theorem ext_chart_at_source_mem_nhds' {x' : M} (h : x' ∈ (extChartAt I x).Source) : (extChartAt I x).Source ∈ 𝓝 x' :=
  IsOpen.mem_nhds (ext_chart_at_open_source I x) h

theorem ext_chart_at_source_mem_nhds : (extChartAt I x).Source ∈ 𝓝 x :=
  ext_chart_at_source_mem_nhds' I x (mem_ext_chart_source I x)

theorem ext_chart_at_source_mem_nhds_within' {x' : M} (h : x' ∈ (extChartAt I x).Source) :
    (extChartAt I x).Source ∈ 𝓝[s] x' :=
  mem_nhds_within_of_mem_nhds (ext_chart_at_source_mem_nhds' I x h)

theorem ext_chart_at_source_mem_nhds_within : (extChartAt I x).Source ∈ 𝓝[s] x :=
  mem_nhds_within_of_mem_nhds (ext_chart_at_source_mem_nhds I x)

theorem ext_chart_at_continuous_on : ContinuousOn (extChartAt I x) (extChartAt I x).Source := by
  refine' I.continuous.comp_continuous_on _
  rw [ext_chart_at_source]
  exact (chart_at H x).ContinuousOn

theorem ext_chart_at_continuous_at' {x' : M} (h : x' ∈ (extChartAt I x).Source) : ContinuousAt (extChartAt I x) x' :=
  (ext_chart_at_continuous_on I x).ContinuousAt <| ext_chart_at_source_mem_nhds' I x h

theorem ext_chart_at_continuous_at : ContinuousAt (extChartAt I x) x :=
  ext_chart_at_continuous_at' _ _ (mem_ext_chart_source I x)

theorem ext_chart_at_continuous_on_symm : ContinuousOn (extChartAt I x).symm (extChartAt I x).Target :=
  (chartAt H x).continuous_on_symm.comp I.continuous_on_symm <|
    (maps_to_preimage _ _).mono_left (inter_subset_right _ _)

theorem ext_chart_at_map_nhds' {x y : M} (hy : y ∈ (extChartAt I x).Source) :
    map (extChartAt I x) (𝓝 y) = 𝓝[Range I] extChartAt I x y := by
  rw [ext_chart_at_coe, (· ∘ ·), ← I.map_nhds_eq, ← (chart_at H x).map_nhds_eq, map_map]
  rwa [ext_chart_at_source] at hy

theorem ext_chart_at_map_nhds : map (extChartAt I x) (𝓝 x) = 𝓝[Range I] extChartAt I x x :=
  ext_chart_at_map_nhds' I <| mem_ext_chart_source I x

theorem ext_chart_at_target_mem_nhds_within' {y : M} (hy : y ∈ (extChartAt I x).Source) :
    (extChartAt I x).Target ∈ 𝓝[Range I] extChartAt I x y := by
  rw [← LocalEquiv.image_source_eq_target, ← ext_chart_at_map_nhds' I hy]
  exact image_mem_map (ext_chart_at_source_mem_nhds' _ _ hy)

theorem ext_chart_at_target_mem_nhds_within : (extChartAt I x).Target ∈ 𝓝[Range I] extChartAt I x x :=
  ext_chart_at_target_mem_nhds_within' I x (mem_ext_chart_source I x)

theorem ext_chart_at_target_subset_range : (extChartAt I x).Target ⊆ Range I := by
  simp' only with mfld_simps

theorem nhds_within_ext_chart_target_eq' {y : M} (hy : y ∈ (extChartAt I x).Source) :
    𝓝[(extChartAt I x).Target] extChartAt I x y = 𝓝[Range I] extChartAt I x y :=
  (nhds_within_mono _ (ext_chart_at_target_subset_range _ _)).antisymm <|
    nhds_within_le_of_mem (ext_chart_at_target_mem_nhds_within' _ _ hy)

theorem nhds_within_ext_chart_target_eq :
    𝓝[(extChartAt I x).Target] (extChartAt I x) x = 𝓝[Range I] (extChartAt I x) x :=
  nhds_within_ext_chart_target_eq' I x (mem_ext_chart_source I x)

theorem ext_chart_continuous_at_symm'' {y : E} (h : y ∈ (extChartAt I x).Target) :
    ContinuousAt (extChartAt I x).symm y :=
  ContinuousAt.comp ((chartAt H x).continuous_at_symm h.2) I.continuous_symm.ContinuousAt

theorem ext_chart_continuous_at_symm' {x' : M} (h : x' ∈ (extChartAt I x).Source) :
    ContinuousAt (extChartAt I x).symm (extChartAt I x x') :=
  ext_chart_continuous_at_symm'' I _ <| (extChartAt I x).map_source h

theorem ext_chart_continuous_at_symm : ContinuousAt (extChartAt I x).symm ((extChartAt I x) x) :=
  ext_chart_continuous_at_symm' I x (mem_ext_chart_source I x)

theorem ext_chart_continuous_on_symm : ContinuousOn (extChartAt I x).symm (extChartAt I x).Target := fun y hy =>
  (ext_chart_continuous_at_symm'' _ _ hy).ContinuousWithinAt

theorem ext_chart_preimage_open_of_open' {s : Set E} (hs : IsOpen s) :
    IsOpen ((extChartAt I x).Source ∩ extChartAt I x ⁻¹' s) :=
  (ext_chart_at_continuous_on I x).preimage_open_of_open (ext_chart_at_open_source _ _) hs

theorem ext_chart_preimage_open_of_open {s : Set E} (hs : IsOpen s) :
    IsOpen ((chartAt H x).Source ∩ extChartAt I x ⁻¹' s) := by
  rw [← ext_chart_at_source I]
  exact ext_chart_preimage_open_of_open' I x hs

theorem ext_chart_at_map_nhds_within_eq_image' {y : M} (hy : y ∈ (extChartAt I x).Source) :
    map (extChartAt I x) (𝓝[s] y) = 𝓝[extChartAt I x '' ((extChartAt I x).Source ∩ s)] extChartAt I x y := by
  set e := extChartAt I x <;>
    calc map e (𝓝[s] y) = map e (𝓝[e.source ∩ s] y) :=
        congr_arg (map e)
          (nhds_within_inter_of_mem
              (ext_chart_at_source_mem_nhds_within' I x hy)).symm _ = 𝓝[e '' (e.source ∩ s)] e y :=
        ((extChartAt I x).LeftInvOn.mono <| inter_subset_left _ _).map_nhds_within_eq ((extChartAt I x).left_inv hy)
          (ext_chart_continuous_at_symm' I x hy).ContinuousWithinAt
          (ext_chart_at_continuous_at' I x hy).ContinuousWithinAt

theorem ext_chart_at_map_nhds_within_eq_image :
    map (extChartAt I x) (𝓝[s] x) = 𝓝[extChartAt I x '' ((extChartAt I x).Source ∩ s)] extChartAt I x x :=
  ext_chart_at_map_nhds_within_eq_image' I x (mem_ext_chart_source I x)

theorem ext_chart_at_map_nhds_within' {y : M} (hy : y ∈ (extChartAt I x).Source) :
    map (extChartAt I x) (𝓝[s] y) = 𝓝[(extChartAt I x).symm ⁻¹' s ∩ Range I] extChartAt I x y := by
  rw [ext_chart_at_map_nhds_within_eq_image' I x hy, nhds_within_inter, ← nhds_within_ext_chart_target_eq' _ _ hy, ←
    nhds_within_inter, (extChartAt I x).image_source_inter_eq', inter_comm]

theorem ext_chart_at_map_nhds_within :
    map (extChartAt I x) (𝓝[s] x) = 𝓝[(extChartAt I x).symm ⁻¹' s ∩ Range I] extChartAt I x x :=
  ext_chart_at_map_nhds_within' I x (mem_ext_chart_source I x)

theorem ext_chart_at_symm_map_nhds_within' {y : M} (hy : y ∈ (extChartAt I x).Source) :
    map (extChartAt I x).symm (𝓝[(extChartAt I x).symm ⁻¹' s ∩ Range I] extChartAt I x y) = 𝓝[s] y := by
  rw [← ext_chart_at_map_nhds_within' I x hy, map_map, map_congr, map_id]
  exact (extChartAt I x).LeftInvOn.EqOn.eventually_eq_of_mem (ext_chart_at_source_mem_nhds_within' _ _ hy)

theorem ext_chart_at_symm_map_nhds_within_range' {y : M} (hy : y ∈ (extChartAt I x).Source) :
    map (extChartAt I x).symm (𝓝[Range I] extChartAt I x y) = 𝓝 y := by
  rw [← nhds_within_univ, ← ext_chart_at_symm_map_nhds_within' I x hy, preimage_univ, univ_inter]

theorem ext_chart_at_symm_map_nhds_within :
    map (extChartAt I x).symm (𝓝[(extChartAt I x).symm ⁻¹' s ∩ Range I] extChartAt I x x) = 𝓝[s] x :=
  ext_chart_at_symm_map_nhds_within' I x (mem_ext_chart_source I x)

theorem ext_chart_at_symm_map_nhds_within_range : map (extChartAt I x).symm (𝓝[Range I] extChartAt I x x) = 𝓝 x :=
  ext_chart_at_symm_map_nhds_within_range' I x (mem_ext_chart_source I x)

/-- Technical lemma ensuring that the preimage under an extended chart of a neighborhood of a point
in the source is a neighborhood of the preimage, within a set. -/
theorem ext_chart_preimage_mem_nhds_within' {x' : M} (h : x' ∈ (extChartAt I x).Source) (ht : t ∈ 𝓝[s] x') :
    (extChartAt I x).symm ⁻¹' t ∈ 𝓝[(extChartAt I x).symm ⁻¹' s ∩ Range I] (extChartAt I x) x' := by
  rwa [← ext_chart_at_symm_map_nhds_within' I x h, mem_map] at ht

/-- Technical lemma ensuring that the preimage under an extended chart of a neighborhood of the
base point is a neighborhood of the preimage, within a set. -/
theorem ext_chart_preimage_mem_nhds_within (ht : t ∈ 𝓝[s] x) :
    (extChartAt I x).symm ⁻¹' t ∈ 𝓝[(extChartAt I x).symm ⁻¹' s ∩ Range I] (extChartAt I x) x :=
  ext_chart_preimage_mem_nhds_within' I x (mem_ext_chart_source I x) ht

/-- Technical lemma ensuring that the preimage under an extended chart of a neighborhood of a point
is a neighborhood of the preimage. -/
theorem ext_chart_preimage_mem_nhds (ht : t ∈ 𝓝 x) : (extChartAt I x).symm ⁻¹' t ∈ 𝓝 ((extChartAt I x) x) := by
  apply (ext_chart_continuous_at_symm I x).preimage_mem_nhds
  rwa [(extChartAt I x).left_inv (mem_ext_chart_source _ _)]

/-- Technical lemma to rewrite suitably the preimage of an intersection under an extended chart, to
bring it into a convenient form to apply derivative lemmas. -/
theorem ext_chart_preimage_inter_eq :
    (extChartAt I x).symm ⁻¹' (s ∩ t) ∩ Range I = (extChartAt I x).symm ⁻¹' s ∩ Range I ∩ (extChartAt I x).symm ⁻¹' t :=
  by
  mfld_set_tac

end ExtendedCharts

/-- In the case of the manifold structure on a vector space, the extended charts are just the
identity.-/
theorem ext_chart_model_space_eq_id (𝕜 : Type _) [NondiscreteNormedField 𝕜] {E : Type _} [NormedGroup E]
    [NormedSpace 𝕜 E] (x : E) : extChartAt (modelWithCornersSelf 𝕜 E) x = LocalEquiv.refl E := by
  simp' only with mfld_simps

