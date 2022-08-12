/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import Mathbin.Analysis.Complex.Circle
import Mathbin.Analysis.NormedSpace.BallAction
import Mathbin.Analysis.InnerProductSpace.Calculus
import Mathbin.Analysis.InnerProductSpace.PiL2
import Mathbin.Geometry.Manifold.Algebra.LieGroup
import Mathbin.Geometry.Manifold.Instances.Real

/-!
# Manifold structure on the sphere

This file defines stereographic projection from the sphere in an inner product space `E`, and uses
it to put a smooth manifold structure on the sphere.

## Main results

For a unit vector `v` in `E`, the definition `stereographic` gives the stereographic projection
centred at `v`, a local homeomorphism from the sphere to `(ℝ ∙ v)ᗮ` (the orthogonal complement of
`v`).

For finite-dimensional `E`, we then construct a smooth manifold instance on the sphere; the charts
here are obtained by composing the local homeomorphisms `stereographic` with arbitrary isometries
from `(ℝ ∙ v)ᗮ` to Euclidean space.

We prove two lemmas about smooth maps:
* `cont_mdiff_coe_sphere` states that the coercion map from the sphere into `E` is smooth;
  this is a useful tool for constructing smooth maps *from* the sphere.
* `cont_mdiff.cod_restrict_sphere` states that a map from a manifold into the sphere is
  smooth if its lift to a map to `E` is smooth; this is a useful tool for constructing smooth maps
  *to* the sphere.

As an application we prove `cont_mdiff_neg_sphere`, that the antipodal map is smooth.

Finally, we equip the `circle` (defined in `analysis.complex.circle` to be the sphere in `ℂ`
centred at `0` of radius `1`) with the following structure:
* a charted space with model space `euclidean_space ℝ (fin 1)` (inherited from `metric.sphere`)
* a Lie group with model with corners `𝓡 1`

We furthermore show that `exp_map_circle` (defined in `analysis.complex.circle` to be the natural
map `λ t, exp (t * I)` from `ℝ` to `circle`) is smooth.


## Implementation notes

The model space for the charted space instance is `euclidean_space ℝ (fin n)`, where `n` is a
natural number satisfying the typeclass assumption `[fact (finrank ℝ E = n + 1)]`.  This may seem a
little awkward, but it is designed to circumvent the problem that the literal expression for the
dimension of the model space (up to definitional equality) determines the type.  If one used the
naive expression `euclidean_space ℝ (fin (finrank ℝ E - 1))` for the model space, then the sphere in
`ℂ` would be a manifold with model space `euclidean_space ℝ (fin (2 - 1))` but not with model space
`euclidean_space ℝ (fin 1)`.
-/


variable {E : Type _} [InnerProductSpace ℝ E]

noncomputable section

open Metric FiniteDimensional

open Manifold

attribute [local instance] fact_finite_dimensional_of_finrank_eq_succ

section StereographicProjection

variable (v : E)

/-! ### Construction of the stereographic projection -/


/-- Stereographic projection, forward direction. This is a map from an inner product space `E` to
the orthogonal complement of an element `v` of `E`. It is smooth away from the affine hyperplane
through `v` parallel to the orthogonal complement.  It restricts on the sphere to the stereographic
projection. -/
def stereoToFun [CompleteSpace E] (x : E) : (ℝ∙v)ᗮ :=
  (2 / ((1 : ℝ) - innerSL v x)) • orthogonalProjection (ℝ∙v)ᗮ x

variable {v}

@[simp]
theorem stereo_to_fun_apply [CompleteSpace E] (x : E) :
    stereoToFun v x = (2 / ((1 : ℝ) - innerSL v x)) • orthogonalProjection (ℝ∙v)ᗮ x :=
  rfl

theorem cont_diff_on_stereo_to_fun [CompleteSpace E] :
    ContDiffOn ℝ ⊤ (stereoToFun v) { x : E | innerSL v x ≠ (1 : ℝ) } := by
  refine' ContDiffOn.smul _ (orthogonalProjection (ℝ∙v)ᗮ).ContDiff.ContDiffOn
  refine' cont_diff_const.cont_diff_on.div _ _
  · exact (cont_diff_const.sub (innerSL v).ContDiff).ContDiffOn
    
  · intro x h h'
    exact h (sub_eq_zero.mp h').symm
    

theorem continuous_on_stereo_to_fun [CompleteSpace E] :
    ContinuousOn (stereoToFun v) { x : E | innerSL v x ≠ (1 : ℝ) } :=
  (@cont_diff_on_stereo_to_fun E _ v _).ContinuousOn

variable (v)

/-- Auxiliary function for the construction of the reverse direction of the stereographic
projection.  This is a map from the orthogonal complement of a unit vector `v` in an inner product
space `E` to `E`; we will later prove that it takes values in the unit sphere.

For most purposes, use `stereo_inv_fun`, not `stereo_inv_fun_aux`. -/
def stereoInvFunAux (w : E) : E :=
  (∥w∥ ^ 2 + 4)⁻¹ • ((4 : ℝ) • w + (∥w∥ ^ 2 - 4) • v)

variable {v}

@[simp]
theorem stereo_inv_fun_aux_apply (w : E) : stereoInvFunAux v w = (∥w∥ ^ 2 + 4)⁻¹ • ((4 : ℝ) • w + (∥w∥ ^ 2 - 4) • v) :=
  rfl

theorem stereo_inv_fun_aux_mem (hv : ∥v∥ = 1) {w : E} (hw : w ∈ (ℝ∙v)ᗮ) : stereoInvFunAux v w ∈ Sphere (0 : E) 1 := by
  have h₁ : 0 ≤ ∥w∥ ^ 2 + 4 := by
    nlinarith
  suffices ∥(4 : ℝ) • w + (∥w∥ ^ 2 - 4) • v∥ = ∥w∥ ^ 2 + 4 by
    have h₂ : ∥w∥ ^ 2 + 4 ≠ 0 := by
      nlinarith
    simp only [← mem_sphere_zero_iff_norm, ← norm_smul, ← Real.norm_eq_abs, ← abs_inv, ← this, ← abs_of_nonneg h₁, ←
      stereo_inv_fun_aux_apply]
    field_simp
  suffices ∥(4 : ℝ) • w + (∥w∥ ^ 2 - 4) • v∥ ^ 2 = (∥w∥ ^ 2 + 4) ^ 2 by
    have h₃ : 0 ≤ ∥stereoInvFunAux v w∥ := norm_nonneg _
    simpa [← h₁, ← h₃, -one_pow] using this
  simp [← norm_add_sq_real, ← norm_smul, ← inner_smul_left, ← inner_smul_right, ←
    inner_left_of_mem_orthogonal_singleton _ hw, ← mul_powₓ, ← Real.norm_eq_abs, ← hv]
  ring

theorem cont_diff_stereo_inv_fun_aux : ContDiff ℝ ⊤ (stereoInvFunAux v) := by
  have h₀ : ContDiff ℝ ⊤ fun w : E => ∥w∥ ^ 2 := cont_diff_norm_sq
  have h₁ : ContDiff ℝ ⊤ fun w : E => (∥w∥ ^ 2 + 4)⁻¹ := by
    refine' (h₀.add cont_diff_const).inv _
    intro x
    nlinarith
  have h₂ : ContDiff ℝ ⊤ fun w => (4 : ℝ) • w + (∥w∥ ^ 2 - 4) • v := by
    refine' (cont_diff_const.smul cont_diff_id).add _
    refine' (h₀.sub cont_diff_const).smul cont_diff_const
  exact h₁.smul h₂

/-- Stereographic projection, reverse direction.  This is a map from the orthogonal complement of a
unit vector `v` in an inner product space `E` to the unit sphere in `E`. -/
def stereoInvFun (hv : ∥v∥ = 1) (w : (ℝ∙v)ᗮ) : Sphere (0 : E) 1 :=
  ⟨stereoInvFunAux v (w : E), stereo_inv_fun_aux_mem hv w.2⟩

@[simp]
theorem stereo_inv_fun_apply (hv : ∥v∥ = 1) (w : (ℝ∙v)ᗮ) :
    (stereoInvFun hv w : E) = (∥w∥ ^ 2 + 4)⁻¹ • ((4 : ℝ) • w + (∥w∥ ^ 2 - 4) • v) :=
  rfl

theorem stereo_inv_fun_ne_north_pole (hv : ∥v∥ = 1) (w : (ℝ∙v)ᗮ) :
    stereoInvFun hv w ≠
      (⟨v, by
        simp [← hv]⟩ :
        Sphere (0 : E) 1) :=
  by
  refine' Subtype.ne_of_val_ne _
  rw [← inner_lt_one_iff_real_of_norm_one _ hv]
  · have hw : ⟪v, w⟫_ℝ = 0 := inner_right_of_mem_orthogonal_singleton v w.2
    have hw' : (∥(w : E)∥ ^ 2 + 4)⁻¹ * (∥(w : E)∥ ^ 2 - 4) < 1 := by
      refine' (inv_mul_lt_iff' _).mpr _
      · nlinarith
        
      linarith
    simpa [← real_inner_comm, ← inner_add_right, ← inner_smul_right, ← real_inner_self_eq_norm_mul_norm, ← hw, ←
      hv] using hw'
    
  · simpa using stereo_inv_fun_aux_mem hv w.2
    

theorem continuous_stereo_inv_fun (hv : ∥v∥ = 1) : Continuous (stereoInvFun hv) :=
  continuous_induced_rng (cont_diff_stereo_inv_fun_aux.Continuous.comp continuous_subtype_coe)

variable [CompleteSpace E]

theorem stereo_left_inv (hv : ∥v∥ = 1) {x : Sphere (0 : E) 1} (hx : (x : E) ≠ v) :
    stereoInvFun hv (stereoToFun v x) = x := by
  ext
  simp only [← stereo_to_fun_apply, ← stereo_inv_fun_apply, ← smul_add]
  -- name two frequently-occuring quantities and write down their basic properties
  set a : ℝ := innerSL v x
  set y := orthogonalProjection (ℝ∙v)ᗮ x
  have split : ↑x = a • v + ↑y := by
    convert eq_sum_orthogonal_projection_self_orthogonal_complement (ℝ∙v) x
    exact (orthogonal_projection_unit_singleton ℝ hv x).symm
  have hvy : ⟪v, y⟫_ℝ = 0 := inner_right_of_mem_orthogonal_singleton v y.2
  have pythag : 1 = a ^ 2 + ∥y∥ ^ 2 := by
    have hvy' : ⟪a • v, y⟫_ℝ = 0 := by
      simp [← inner_smul_left, ← hvy]
    convert norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ hvy' using 2
    · simp [split]
      
    · simp [← norm_smul, ← hv, sq, ← sq_abs]
      
    · exact sq _
      
  -- two facts which will be helpful for clearing denominators in the main calculation
  have ha : 1 - a ≠ 0 := by
    have : a < 1 :=
      (inner_lt_one_iff_real_of_norm_one hv
            (by
              simp )).mpr
        hx.symm
    linarith
  have : 2 ^ 2 * ∥y∥ ^ 2 + 4 * (1 - a) ^ 2 ≠ 0 := by
    refine' ne_of_gtₓ _
    have := norm_nonneg (y : E)
    have : 0 < (1 - a) ^ 2 := sq_pos_of_ne_zero (1 - a) ha
    nlinarith
  -- the core of the problem is these two algebraic identities:
  have h₁ : (2 ^ 2 / (1 - a) ^ 2 * ∥y∥ ^ 2 + 4)⁻¹ * 4 * (2 / (1 - a)) = 1 := by
    field_simp
    simp only [← Submodule.coe_norm] at *
    nlinarith
  have h₂ : (2 ^ 2 / (1 - a) ^ 2 * ∥y∥ ^ 2 + 4)⁻¹ * (2 ^ 2 / (1 - a) ^ 2 * ∥y∥ ^ 2 - 4) = a := by
    field_simp
    trans (1 - a) ^ 2 * (a * (2 ^ 2 * ∥y∥ ^ 2 + 4 * (1 - a) ^ 2))
    · congr
      simp only [← Submodule.coe_norm] at *
      nlinarith
      
    ring
  -- deduce the result
  convert congr_arg2ₓ Add.add (congr_arg (fun t => t • (y : E)) h₁) (congr_arg (fun t => t • v) h₂) using 1
  · simp [← inner_add_right, ← inner_smul_right, ← hvy, ← real_inner_self_eq_norm_mul_norm, ← hv, ← mul_smul, ←
      mul_powₓ, ← Real.norm_eq_abs, ← sq_abs, ← norm_smul]
    
  · simp [← split, ← add_commₓ]
    

theorem stereo_right_inv (hv : ∥v∥ = 1) (w : (ℝ∙v)ᗮ) : stereoToFun v (stereoInvFun hv w) = w := by
  have : 2 / (1 - (∥(w : E)∥ ^ 2 + 4)⁻¹ * (∥(w : E)∥ ^ 2 - 4)) * (∥(w : E)∥ ^ 2 + 4)⁻¹ * 4 = 1 := by
    have : ∥(w : E)∥ ^ 2 + 4 ≠ 0 := by
      nlinarith
    have : (4 : ℝ) + 4 ≠ 0 := by
      nlinarith
    field_simp
    ring
  convert congr_arg (fun c => c • w) this
  · have h₁ : orthogonalProjection (ℝ∙v)ᗮ v = 0 := orthogonal_projection_orthogonal_complement_singleton_eq_zero v
    have h₂ : orthogonalProjection (ℝ∙v)ᗮ w = w := orthogonal_projection_mem_subspace_eq_self w
    have h₃ : innerSL v w = (0 : ℝ) := inner_right_of_mem_orthogonal_singleton v w.2
    have h₄ : innerSL v v = (1 : ℝ) := by
      simp [← real_inner_self_eq_norm_mul_norm, ← hv]
    simp [← h₁, ← h₂, ← h₃, ← h₄, ← ContinuousLinearMap.map_add, ← ContinuousLinearMap.map_smul, ← mul_smul]
    
  · simp
    

/-- Stereographic projection from the unit sphere in `E`, centred at a unit vector `v` in `E`; this
is the version as a local homeomorphism. -/
def stereographic (hv : ∥v∥ = 1) : LocalHomeomorph (Sphere (0 : E) 1) (ℝ∙v)ᗮ where
  toFun := stereoToFun v ∘ coe
  invFun := stereoInvFun hv
  Source :=
    {⟨v, by
          simp [← hv]⟩}ᶜ
  Target := Set.Univ
  map_source' := by
    simp
  map_target' := fun w _ => stereo_inv_fun_ne_north_pole hv w
  left_inv' := fun _ hx => stereo_left_inv hv fun h => hx (Subtype.ext h)
  right_inv' := fun w _ => stereo_right_inv hv w
  open_source := is_open_compl_singleton
  open_target := is_open_univ
  continuous_to_fun :=
    continuous_on_stereo_to_fun.comp continuous_subtype_coe.ContinuousOn fun w h =>
      h ∘
        Subtype.ext ∘
          Eq.symm ∘
            (inner_eq_norm_mul_iff_of_norm_one hv
                (by
                  simp )).mp
  continuous_inv_fun := (continuous_stereo_inv_fun hv).ContinuousOn

theorem stereographic_apply (hv : ∥v∥ = 1) (x : Sphere (0 : E) 1) :
    stereographic hv x = (2 / ((1 : ℝ) - inner v x)) • orthogonalProjection (ℝ∙v)ᗮ x :=
  rfl

@[simp]
theorem stereographic_source (hv : ∥v∥ = 1) :
    (stereographic hv).Source =
      {⟨v, by
            simp [← hv]⟩}ᶜ :=
  rfl

@[simp]
theorem stereographic_target (hv : ∥v∥ = 1) : (stereographic hv).Target = Set.Univ :=
  rfl

end StereographicProjection

section ChartedSpace

/-!
### Charted space structure on the sphere

In this section we construct a charted space structure on the unit sphere in a finite-dimensional
real inner product space `E`; that is, we show that it is locally homeomorphic to the Euclidean
space of dimension one less than `E`.

The restriction to finite dimension is for convenience.  The most natural `charted_space`
structure for the sphere uses the stereographic projection from the antipodes of a point as the
canonical chart at this point.  However, the codomain of the stereographic projection constructed
in the previous section is `(ℝ ∙ v)ᗮ`, the orthogonal complement of the vector `v` in `E` which is
the "north pole" of the projection, so a priori these charts all have different codomains.

So it is necessary to prove that these codomains are all continuously linearly equivalent to a
fixed normed space.  This could be proved in general by a simple case of Gram-Schmidt
orthogonalization, but in the finite-dimensional case it follows more easily by dimension-counting.
-/


/-- Variant of the stereographic projection, for the sphere in an `n + 1`-dimensional inner product
space `E`.  This version has codomain the Euclidean space of dimension `n`, and is obtained by
composing the original sterographic projection (`stereographic`) with an arbitrary linear isometry
from `(ℝ ∙ v)ᗮ` to the Euclidean space. -/
def stereographic' (n : ℕ) [Fact (finrank ℝ E = n + 1)] (v : Sphere (0 : E) 1) :
    LocalHomeomorph (Sphere (0 : E) 1) (EuclideanSpace ℝ (Finₓ n)) :=
  stereographic (norm_eq_of_mem_sphere v) ≫ₕ
    (OrthonormalBasis.fromOrthogonalSpanSingleton n (ne_zero_of_mem_unit_sphere v)).repr.toHomeomorph.toLocalHomeomorph

@[simp]
theorem stereographic'_source {n : ℕ} [Fact (finrank ℝ E = n + 1)] (v : Sphere (0 : E) 1) :
    (stereographic' n v).Source = {v}ᶜ := by
  simp [← stereographic']

@[simp]
theorem stereographic'_target {n : ℕ} [Fact (finrank ℝ E = n + 1)] (v : Sphere (0 : E) 1) :
    (stereographic' n v).Target = Set.Univ := by
  simp [← stereographic']

/-- The unit sphere in an `n + 1`-dimensional inner product space `E` is a charted space
modelled on the Euclidean space of dimension `n`. -/
instance {n : ℕ} [Fact (finrank ℝ E = n + 1)] : ChartedSpace (EuclideanSpace ℝ (Finₓ n)) (Sphere (0 : E) 1) where
  Atlas := { f | ∃ v : Sphere (0 : E) 1, f = stereographic' n v }
  chartAt := fun v => stereographic' n (-v)
  mem_chart_source := fun v => by
    simpa using ne_neg_of_mem_unit_sphere ℝ v
  chart_mem_atlas := fun v => ⟨-v, rfl⟩

end ChartedSpace

section SmoothManifold

theorem sphere_ext_iff (u v : Sphere (0 : E) 1) : u = v ↔ ⟪(u : E), v⟫_ℝ = 1 := by
  simp [← Subtype.ext_iff, ← inner_eq_norm_mul_iff_of_norm_one]

theorem stereographic'_symm_apply {n : ℕ} [Fact (finrank ℝ E = n + 1)] (v : Sphere (0 : E) 1)
    (x : EuclideanSpace ℝ (Finₓ n)) :
    ((stereographic' n v).symm x : E) =
      let U : (ℝ∙(v : E))ᗮ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Finₓ n) :=
        (OrthonormalBasis.fromOrthogonalSpanSingleton n (ne_zero_of_mem_unit_sphere v)).repr
      (∥(U.symm x : E)∥ ^ 2 + 4)⁻¹ • (4 : ℝ) • (U.symm x : E) +
        (∥(U.symm x : E)∥ ^ 2 + 4)⁻¹ • (∥(U.symm x : E)∥ ^ 2 - 4) • v :=
  by
  simp [← real_inner_comm, ← stereographic, ← stereographic', Submodule.coe_norm]

/-! ### Smooth manifold structure on the sphere -/


/-- The unit sphere in an `n + 1`-dimensional inner product space `E` is a smooth manifold,
modelled on the Euclidean space of dimension `n`. -/
instance {n : ℕ} [Fact (finrank ℝ E = n + 1)] : SmoothManifoldWithCorners (𝓡 n) (Sphere (0 : E) 1) :=
  smooth_manifold_with_corners_of_cont_diff_on (𝓡 n) (Sphere (0 : E) 1)
    (by
      rintro _ _ ⟨v, rfl⟩ ⟨v', rfl⟩
      let U :=
        (-- Removed type ascription, and this helped for some reason with timeout issues?
            OrthonormalBasis.fromOrthogonalSpanSingleton
            n (ne_zero_of_mem_unit_sphere v)).repr
      let U' :=
        (-- Removed type ascription, and this helped for some reason with timeout issues?
            OrthonormalBasis.fromOrthogonalSpanSingleton
            n (ne_zero_of_mem_unit_sphere v')).repr
      have hUv : stereographic' n v = stereographic (norm_eq_of_mem_sphere v) ≫ₕ U.to_homeomorph.to_local_homeomorph :=
        rfl
      have hU'v' :
        stereographic' n v' = (stereographic (norm_eq_of_mem_sphere v')).trans U'.to_homeomorph.to_local_homeomorph :=
        rfl
      have H₁ := U'.cont_diff.comp_cont_diff_on cont_diff_on_stereo_to_fun
      have H₂ := (cont_diff_stereo_inv_fun_aux.comp (ℝ∙(v : E))ᗮ.subtypeL.ContDiff).comp U.symm.cont_diff
      convert H₁.comp' (H₂.cont_diff_on : ContDiffOn ℝ ⊤ _ Set.Univ) using 1
      ext
      simp [← sphere_ext_iff, ← stereographic'_symm_apply, ← real_inner_comm])

/-- The inclusion map (i.e., `coe`) from the sphere in `E` to `E` is smooth.  -/
theorem cont_mdiff_coe_sphere {n : ℕ} [Fact (finrank ℝ E = n + 1)] :
    ContMdiff (𝓡 n) 𝓘(ℝ, E) ∞ (coe : Sphere (0 : E) 1 → E) := by
  rw [cont_mdiff_iff]
  constructor
  · exact continuous_subtype_coe
    
  · intro v _
    let U :=
      (-- Again, removing type ascription...
          OrthonormalBasis.fromOrthogonalSpanSingleton
          n (ne_zero_of_mem_unit_sphere (-v))).repr
    exact ((cont_diff_stereo_inv_fun_aux.comp (ℝ∙(-v : E))ᗮ.subtypeL.ContDiff).comp U.symm.cont_diff).ContDiffOn
    

variable {F : Type _} [NormedGroup F] [NormedSpace ℝ F]

variable {H : Type _} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}

variable {M : Type _} [TopologicalSpace M] [ChartedSpace H M] [SmoothManifoldWithCorners I M]

/-- If a `cont_mdiff` function `f : M → E`, where `M` is some manifold, takes values in the
sphere, then it restricts to a `cont_mdiff` function from `M` to the sphere. -/
theorem ContMdiff.cod_restrict_sphere {n : ℕ} [Fact (finrank ℝ E = n + 1)] {m : WithTop ℕ} {f : M → E}
    (hf : ContMdiff I 𝓘(ℝ, E) m f) (hf' : ∀ x, f x ∈ Sphere (0 : E) 1) :
    ContMdiff I (𝓡 n) m (Set.codRestrict _ _ hf' : M → Sphere (0 : E) 1) := by
  rw [cont_mdiff_iff_target]
  refine' ⟨continuous_induced_rng hf.continuous, _⟩
  intro v
  let U :=
    (-- Again, removing type ascription... Weird that this helps!
        OrthonormalBasis.fromOrthogonalSpanSingleton
        n (ne_zero_of_mem_unit_sphere (-v))).repr
  have h : ContDiffOn ℝ ⊤ _ Set.Univ := U.cont_diff.cont_diff_on
  have H₁ := (h.comp' cont_diff_on_stereo_to_fun).ContMdiffOn
  have H₂ : ContMdiffOn _ _ _ _ Set.Univ := hf.cont_mdiff_on
  convert (H₁.of_le le_top).comp' H₂ using 1
  ext x
  have hfxv : f x = -↑v ↔ ⟪f x, -↑v⟫_ℝ = 1 := by
    have hfx : ∥f x∥ = 1 := by
      simpa using hf' x
    rw [inner_eq_norm_mul_iff_of_norm_one hfx]
    exact norm_eq_of_mem_sphere (-v)
  dsimp' [← chart_at]
  simp [← not_iff_not, ← Subtype.ext_iff, ← hfxv, ← real_inner_comm]

/-- The antipodal map is smooth. -/
theorem cont_mdiff_neg_sphere {n : ℕ} [Fact (finrank ℝ E = n + 1)] :
    ContMdiff (𝓡 n) (𝓡 n) ∞ fun x : Sphere (0 : E) 1 => -x := by
  -- this doesn't elaborate well in term mode
  apply ContMdiff.cod_restrict_sphere
  apply cont_diff_neg.cont_mdiff.comp _
  exact cont_mdiff_coe_sphere

end SmoothManifold

section circle

open Complex

attribute [local instance] finrank_real_complex_fact

/-- The unit circle in `ℂ` is a charted space modelled on `euclidean_space ℝ (fin 1)`.  This
follows by definition from the corresponding result for `metric.sphere`. -/
instance : ChartedSpace (EuclideanSpace ℝ (Finₓ 1)) circle :=
  Metric.Sphere.chartedSpace

instance : SmoothManifoldWithCorners (𝓡 1) circle :=
  Metric.Sphere.smooth_manifold_with_corners

/-- The unit circle in `ℂ` is a Lie group. -/
instance : LieGroup (𝓡 1) circle where
  smooth_mul := by
    apply ContMdiff.cod_restrict_sphere
    let c : circle → ℂ := coe
    have h₂ : ContMdiff (𝓘(ℝ, ℂ).Prod 𝓘(ℝ, ℂ)) 𝓘(ℝ, ℂ) ∞ fun z : ℂ × ℂ => z.fst * z.snd := by
      rw [cont_mdiff_iff]
      exact ⟨continuous_mul, fun x y => (cont_diff_mul.restrict_scalars ℝ).ContDiffOn⟩
    suffices h₁ : ContMdiff _ _ _ (Prod.map c c)
    · apply h₂.comp h₁
      
    -- this elaborates much faster with `apply`
      apply ContMdiff.prod_map <;>
      exact cont_mdiff_coe_sphere
  smooth_inv := by
    apply ContMdiff.cod_restrict_sphere
    simp only [coe_inv_circle, ← coe_inv_circle_eq_conj]
    exact complex.conj_cle.cont_diff.cont_mdiff.comp cont_mdiff_coe_sphere

/-- The map `λ t, exp (t * I)` from `ℝ` to the unit circle in `ℂ` is smooth. -/
theorem cont_mdiff_exp_map_circle : ContMdiff 𝓘(ℝ, ℝ) (𝓡 1) ∞ expMapCircle :=
  (cont_diff_exp.comp (cont_diff_id.smul cont_diff_const)).ContMdiff.cod_restrict_sphere _

end circle

