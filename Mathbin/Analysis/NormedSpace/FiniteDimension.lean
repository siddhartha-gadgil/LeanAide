/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathbin.Analysis.Asymptotics.AsymptoticEquivalent
import Mathbin.Analysis.NormedSpace.AffineIsometry
import Mathbin.Analysis.NormedSpace.OperatorNorm
import Mathbin.Analysis.NormedSpace.RieszLemma
import Mathbin.LinearAlgebra.Matrix.ToLin
import Mathbin.Topology.Algebra.Module.FiniteDimension
import Mathbin.Topology.Instances.Matrix

/-!
# Finite dimensional normed spaces over complete fields

Over a complete nondiscrete field, in finite dimension, all norms are equivalent and all linear maps
are continuous. Moreover, a finite-dimensional subspace is always complete and closed.

## Main results:

* `finite_dimensional.complete` : a finite-dimensional space over a complete field is complete. This
  is not registered as an instance, as the field would be an unknown metavariable in typeclass
  resolution.
* `submodule.closed_of_finite_dimensional` : a finite-dimensional subspace over a complete field is
  closed
* `finite_dimensional.proper` : a finite-dimensional space over a proper field is proper. This
  is not registered as an instance, as the field would be an unknown metavariable in typeclass
  resolution. It is however registered as an instance for `𝕜 = ℝ` and `𝕜 = ℂ`. As properness
  implies completeness, there is no need to also register `finite_dimensional.complete` on `ℝ` or
  `ℂ`.
* `finite_dimensional_of_is_compact_closed_ball`: Riesz' theorem: if the closed unit ball is
  compact, then the space is finite-dimensional.

## Implementation notes

The fact that all norms are equivalent is not written explicitly, as it would mean having two norms
on a single space, which is not the way type classes work. However, if one has a
finite-dimensional vector space `E` with a norm, and a copy `E'` of this type with another norm,
then the identities from `E` to `E'` and from `E'`to `E` are continuous thanks to
`linear_map.continuous_of_finite_dimensional`. This gives the desired norm equivalence.
-/


universe u v w x

noncomputable section

open Set FiniteDimensional TopologicalSpace Filter Asymptotics

open Classical BigOperators Filter TopologicalSpace Asymptotics Nnreal

namespace LinearIsometry

open LinearMap

variable {R : Type _} [Semiringₓ R]

variable {F E₁ : Type _} [SemiNormedGroup F] [NormedGroup E₁] [Module R E₁]

variable {R₁ : Type _} [Field R₁] [Module R₁ E₁] [Module R₁ F] [FiniteDimensional R₁ E₁] [FiniteDimensional R₁ F]

/-- A linear isometry between finite dimensional spaces of equal dimension can be upgraded
    to a linear isometry equivalence. -/
def toLinearIsometryEquiv (li : E₁ →ₗᵢ[R₁] F) (h : finrank R₁ E₁ = finrank R₁ F) : E₁ ≃ₗᵢ[R₁] F where
  toLinearEquiv := li.toLinearMap.linearEquivOfInjective li.Injective h
  norm_map' := li.norm_map'

@[simp]
theorem coe_to_linear_isometry_equiv (li : E₁ →ₗᵢ[R₁] F) (h : finrank R₁ E₁ = finrank R₁ F) :
    (li.toLinearIsometryEquiv h : E₁ → F) = li :=
  rfl

@[simp]
theorem to_linear_isometry_equiv_apply (li : E₁ →ₗᵢ[R₁] F) (h : finrank R₁ E₁ = finrank R₁ F) (x : E₁) :
    (li.toLinearIsometryEquiv h) x = li x :=
  rfl

end LinearIsometry

namespace AffineIsometry

open AffineMap

variable {𝕜 : Type _} {V₁ V₂ : Type _} {P₁ P₂ : Type _} [NormedField 𝕜] [NormedGroup V₁] [SemiNormedGroup V₂]
  [NormedSpace 𝕜 V₁] [NormedSpace 𝕜 V₂] [MetricSpace P₁] [PseudoMetricSpace P₂] [NormedAddTorsor V₁ P₁]
  [NormedAddTorsor V₂ P₂]

variable [FiniteDimensional 𝕜 V₁] [FiniteDimensional 𝕜 V₂]

/-- An affine isometry between finite dimensional spaces of equal dimension can be upgraded
    to an affine isometry equivalence. -/
def toAffineIsometryEquiv [Inhabited P₁] (li : P₁ →ᵃⁱ[𝕜] P₂) (h : finrank 𝕜 V₁ = finrank 𝕜 V₂) : P₁ ≃ᵃⁱ[𝕜] P₂ :=
  AffineIsometryEquiv.mk' li (li.LinearIsometry.toLinearIsometryEquiv h) (arbitrary P₁) fun p => by
    simp

@[simp]
theorem coe_to_affine_isometry_equiv [Inhabited P₁] (li : P₁ →ᵃⁱ[𝕜] P₂) (h : finrank 𝕜 V₁ = finrank 𝕜 V₂) :
    (li.toAffineIsometryEquiv h : P₁ → P₂) = li :=
  rfl

@[simp]
theorem to_affine_isometry_equiv_apply [Inhabited P₁] (li : P₁ →ᵃⁱ[𝕜] P₂) (h : finrank 𝕜 V₁ = finrank 𝕜 V₂) (x : P₁) :
    (li.toAffineIsometryEquiv h) x = li x :=
  rfl

end AffineIsometry

section CompleteField

variable {𝕜 : Type u} [NondiscreteNormedField 𝕜] {E : Type v} [NormedGroup E] [NormedSpace 𝕜 E] {F : Type w}
  [NormedGroup F] [NormedSpace 𝕜 F] {F' : Type x} [AddCommGroupₓ F'] [Module 𝕜 F'] [TopologicalSpace F']
  [TopologicalAddGroup F'] [HasContinuousSmul 𝕜 F'] [CompleteSpace 𝕜]

section Affine

variable {PE PF : Type _} [MetricSpace PE] [NormedAddTorsor E PE] [MetricSpace PF] [NormedAddTorsor F PF]
  [FiniteDimensional 𝕜 E]

include E F

theorem AffineMap.continuous_of_finite_dimensional (f : PE →ᵃ[𝕜] PF) : Continuous f :=
  AffineMap.continuous_linear_iff.1 f.linear.continuous_of_finite_dimensional

theorem AffineEquiv.continuous_of_finite_dimensional (f : PE ≃ᵃ[𝕜] PF) : Continuous f :=
  f.toAffineMap.continuous_of_finite_dimensional

/-- Reinterpret an affine equivalence as a homeomorphism. -/
def AffineEquiv.toHomeomorphOfFiniteDimensional (f : PE ≃ᵃ[𝕜] PF) : PE ≃ₜ PF where
  toEquiv := f.toEquiv
  continuous_to_fun := f.continuous_of_finite_dimensional
  continuous_inv_fun := by
    have : FiniteDimensional 𝕜 F := f.linear.finite_dimensional
    exact f.symm.continuous_of_finite_dimensional

@[simp]
theorem AffineEquiv.coe_to_homeomorph_of_finite_dimensional (f : PE ≃ᵃ[𝕜] PF) :
    ⇑f.toHomeomorphOfFiniteDimensional = f :=
  rfl

@[simp]
theorem AffineEquiv.coe_to_homeomorph_of_finite_dimensional_symm (f : PE ≃ᵃ[𝕜] PF) :
    ⇑f.toHomeomorphOfFiniteDimensional.symm = f.symm :=
  rfl

end Affine

theorem ContinuousLinearMap.continuous_det : Continuous fun f : E →L[𝕜] E => f.det := by
  change Continuous fun f : E →L[𝕜] E => (f : E →ₗ[𝕜] E).det
  by_cases' h : ∃ s : Finset E, Nonempty (Basis (↥s) 𝕜 E)
  · rcases h with ⟨s, ⟨b⟩⟩
    have : FiniteDimensional 𝕜 E := FiniteDimensional.of_finset_basis b
    simp_rw [LinearMap.det_eq_det_to_matrix_of_finset b]
    refine' Continuous.matrix_det _
    exact ((LinearMap.toMatrix b b).toLinearMap.comp (ContinuousLinearMap.coeLm 𝕜)).continuous_of_finite_dimensional
    
  · unfold LinearMap.det
    simpa only [← h, ← MonoidHom.one_apply, ← dif_neg, ← not_false_iff] using continuous_const
    

/-- Any `K`-Lipschitz map from a subset `s` of a metric space `α` to a finite-dimensional real
vector space `E'` can be extended to a Lipschitz map on the whole space `α`, with a slightly worse
constant `C * K` where `C` only depends on `E'`. We record a working value for this constant `C`
as `lipschitz_extension_constant E'`. -/
irreducible_def lipschitzExtensionConstant (E' : Type _) [NormedGroup E'] [NormedSpace ℝ E']
  [FiniteDimensional ℝ E'] : ℝ≥0 :=
  let A := (Basis.ofVectorSpace ℝ E').equivFun.toContinuousLinearEquiv
  max (∥A.symm.toContinuousLinearMap∥₊ * ∥A.toContinuousLinearMap∥₊) 1

theorem lipschitz_extension_constant_pos (E' : Type _) [NormedGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] :
    0 < lipschitzExtensionConstant E' := by
  rw [lipschitzExtensionConstant]
  exact zero_lt_one.trans_le (le_max_rightₓ _ _)

/-- Any `K`-Lipschitz map from a subset `s` of a metric space `α` to a finite-dimensional real
vector space `E'` can be extended to a Lipschitz map on the whole space `α`, with a slightly worse
constant `lipschitz_extension_constant E' * K`. -/
theorem LipschitzOnWith.extend_finite_dimension {α : Type _} [PseudoMetricSpace α] {E' : Type _} [NormedGroup E']
    [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] {s : Set α} {f : α → E'} {K : ℝ≥0 } (hf : LipschitzOnWith K f s) :
    ∃ g : α → E', LipschitzWith (lipschitzExtensionConstant E' * K) g ∧ EqOn f g s := by
  /- This result is already known for spaces `ι → ℝ`. We use a continuous linear equiv between
    `E'` and such a space to transfer the result to `E'`. -/
  let ι : Type _ := Basis.OfVectorSpaceIndex ℝ E'
  let A := (Basis.ofVectorSpace ℝ E').equivFun.toContinuousLinearEquiv
  have LA : LipschitzWith ∥A.to_continuous_linear_map∥₊ A := by
    apply A.lipschitz
  have L : LipschitzOnWith (∥A.to_continuous_linear_map∥₊ * K) (A ∘ f) s := LA.comp_lipschitz_on_with hf
  obtain ⟨g, hg, gs⟩ : ∃ g : α → ι → ℝ, LipschitzWith (∥A.to_continuous_linear_map∥₊ * K) g ∧ eq_on (A ∘ f) g s :=
    L.extend_pi
  refine' ⟨A.symm ∘ g, _, _⟩
  · have LAsymm : LipschitzWith ∥A.symm.to_continuous_linear_map∥₊ A.symm := by
      apply A.symm.lipschitz
    apply (LAsymm.comp hg).weaken
    rw [lipschitzExtensionConstant, ← mul_assoc]
    refine' mul_le_mul' (le_max_leftₓ _ _) le_rfl
    
  · intro x hx
    have : A (f x) = g x := gs hx
    simp only [← (· ∘ ·), this, ← A.symm_apply_apply]
    

theorem LinearMap.exists_antilipschitz_with [FiniteDimensional 𝕜 E] (f : E →ₗ[𝕜] F) (hf : f.ker = ⊥) :
    ∃ K > 0, AntilipschitzWith K f := by
  cases subsingleton_or_nontrivial E <;> skip
  · exact ⟨1, zero_lt_one, AntilipschitzWith.of_subsingleton⟩
    
  · rw [LinearMap.ker_eq_bot] at hf
    let e : E ≃L[𝕜] f.range := (LinearEquiv.ofInjective f hf).toContinuousLinearEquiv
    exact ⟨_, e.nnnorm_symm_pos, e.antilipschitz⟩
    

protected theorem LinearIndependent.eventually {ι} [Fintype ι] {f : ι → E} (hf : LinearIndependent 𝕜 f) :
    ∀ᶠ g in 𝓝 f, LinearIndependent 𝕜 g := by
  simp only [← Fintype.linear_independent_iff'] at hf⊢
  rcases LinearMap.exists_antilipschitz_with _ hf with ⟨K, K0, hK⟩
  have : tendsto (fun g : ι → E => ∑ i, ∥g i - f i∥) (𝓝 f) (𝓝 <| ∑ i, ∥f i - f i∥) :=
    tendsto_finset_sum _ fun i hi => tendsto.norm <| ((continuous_apply i).Tendsto _).sub tendsto_const_nhds
  simp only [← sub_self, ← norm_zero, ← Finset.sum_const_zero] at this
  refine' (this.eventually (gt_mem_nhds <| inv_pos.2 K0)).mono fun g hg => _
  replace hg : (∑ i, ∥g i - f i∥₊) < K⁻¹
  · rw [← Nnreal.coe_lt_coe]
    push_cast
    exact hg
    
  rw [LinearMap.ker_eq_bot]
  refine' (hK.add_sub_lipschitz_with (LipschitzWith.of_dist_le_mul fun v u => _) hg).Injective
  simp only [← dist_eq_norm, ← LinearMap.lsum_apply, ← Pi.sub_apply, ← LinearMap.sum_apply, ← LinearMap.comp_apply, ←
    LinearMap.proj_apply, ← LinearMap.smul_right_apply, ← LinearMap.id_apply, Finset.sum_sub_distrib, smul_sub,
    sub_smul, ← Nnreal.coe_sum, ← coe_nnnorm, ← Finset.sum_mul]
  refine' norm_sum_le_of_le _ fun i _ => _
  rw [norm_smul, mul_comm]
  exact mul_le_mul_of_nonneg_left (norm_le_pi_norm (v - u) i) (norm_nonneg _)

theorem is_open_set_of_linear_independent {ι : Type _} [Fintype ι] : IsOpen { f : ι → E | LinearIndependent 𝕜 f } :=
  is_open_iff_mem_nhds.2 fun f => LinearIndependent.eventually

theorem is_open_set_of_nat_le_rank (n : ℕ) : IsOpen { f : E →L[𝕜] F | ↑n ≤ rank (f : E →ₗ[𝕜] F) } := by
  simp only [← le_rank_iff_exists_linear_independent_finset, ← set_of_exists, exists_prop]
  refine' is_open_bUnion fun t ht => _
  have : Continuous fun f : E →L[𝕜] F => fun x : (t : Set E) => f x :=
    continuous_pi fun x => (ContinuousLinearMap.apply 𝕜 F (x : E)).Continuous
  exact is_open_set_of_linear_independent.preimage this

/-- Two finite-dimensional normed spaces are continuously linearly equivalent if they have the same
(finite) dimension. -/
theorem FiniteDimensional.nonempty_continuous_linear_equiv_of_finrank_eq [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
    (cond : finrank 𝕜 E = finrank 𝕜 F) : Nonempty (E ≃L[𝕜] F) :=
  (nonempty_linear_equiv_of_finrank_eq cond).map LinearEquiv.toContinuousLinearEquiv

/-- Two finite-dimensional normed spaces are continuously linearly equivalent if and only if they
have the same (finite) dimension. -/
theorem FiniteDimensional.nonempty_continuous_linear_equiv_iff_finrank_eq [FiniteDimensional 𝕜 E]
    [FiniteDimensional 𝕜 F] : Nonempty (E ≃L[𝕜] F) ↔ finrank 𝕜 E = finrank 𝕜 F :=
  ⟨fun ⟨h⟩ => h.toLinearEquiv.finrank_eq, fun h => FiniteDimensional.nonempty_continuous_linear_equiv_of_finrank_eq h⟩

/-- A continuous linear equivalence between two finite-dimensional normed spaces of the same
(finite) dimension. -/
def ContinuousLinearEquiv.ofFinrankEq [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
    (cond : finrank 𝕜 E = finrank 𝕜 F) : E ≃L[𝕜] F :=
  (LinearEquiv.ofFinrankEq E F cond).toContinuousLinearEquiv

variable {ι : Type _} [Fintype ι]

/-- Construct a continuous linear map given the value at a finite basis. -/
def Basis.constrL (v : Basis ι 𝕜 E) (f : ι → F) : E →L[𝕜] F :=
  have : FiniteDimensional 𝕜 E := FiniteDimensional.of_fintype_basis v
  (v.constr 𝕜 f).toContinuousLinearMap

@[simp, norm_cast]
theorem Basis.coe_constrL (v : Basis ι 𝕜 E) (f : ι → F) : (v.constrL f : E →ₗ[𝕜] F) = v.constr 𝕜 f :=
  rfl

/-- The continuous linear equivalence between a vector space over `𝕜` with a finite basis and
functions from its basis indexing type to `𝕜`. -/
def Basis.equivFunL (v : Basis ι 𝕜 E) : E ≃L[𝕜] ι → 𝕜 :=
  { v.equivFun with
    continuous_to_fun := by
      have : FiniteDimensional 𝕜 E := FiniteDimensional.of_fintype_basis v
      exact v.equiv_fun.to_linear_map.continuous_of_finite_dimensional,
    continuous_inv_fun := by
      change Continuous v.equiv_fun.symm.to_fun
      exact v.equiv_fun.symm.to_linear_map.continuous_of_finite_dimensional }

@[simp]
theorem Basis.constrL_apply (v : Basis ι 𝕜 E) (f : ι → F) (e : E) : (v.constrL f) e = ∑ i, v.equivFun e i • f i :=
  v.constr_apply_fintype 𝕜 _ _

@[simp]
theorem Basis.constrL_basis (v : Basis ι 𝕜 E) (f : ι → F) (i : ι) : (v.constrL f) (v i) = f i :=
  v.constr_basis 𝕜 _ _

theorem Basis.op_nnnorm_le {ι : Type _} [Fintype ι] (v : Basis ι 𝕜 E) {u : E →L[𝕜] F} (M : ℝ≥0 )
    (hu : ∀ i, ∥u (v i)∥₊ ≤ M) : ∥u∥₊ ≤ Fintype.card ι • ∥v.equivFunL.toContinuousLinearMap∥₊ * M :=
  (u.op_nnnorm_le_bound _) fun e => by
    set φ := v.equiv_funL.to_continuous_linear_map
    calc ∥u e∥₊ = ∥u (∑ i, v.equiv_fun e i • v i)∥₊ := by
        rw [v.sum_equiv_fun]_ = ∥∑ i, v.equiv_fun e i • (u <| v i)∥₊ := by
        simp [← u.map_sum, ← LinearMap.map_smul]_ ≤ ∑ i, ∥v.equiv_fun e i • (u <| v i)∥₊ :=
        nnnorm_sum_le _ _ _ = ∑ i, ∥v.equiv_fun e i∥₊ * ∥u (v i)∥₊ := by
        simp only [← nnnorm_smul]_ ≤ ∑ i, ∥v.equiv_fun e i∥₊ * M :=
        Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hu i) (zero_le _)_ = (∑ i, ∥v.equiv_fun e i∥₊) * M :=
        finset.sum_mul.symm _ ≤ Fintype.card ι • (∥φ∥₊ * ∥e∥₊) * M :=
        suffices _ from mul_le_mul_of_nonneg_right this (zero_le M)
        calc
          (∑ i, ∥v.equiv_fun e i∥₊) ≤ Fintype.card ι • ∥φ e∥₊ := Pi.sum_nnnorm_apply_le_nnnorm _
          _ ≤ Fintype.card ι • (∥φ∥₊ * ∥e∥₊) := nsmul_le_nsmul_of_le_right (φ.le_op_nnnorm e) _
          _ = Fintype.card ι • ∥φ∥₊ * M * ∥e∥₊ :=
        by
        simp only [← smul_mul_assoc, ← mul_right_commₓ]

theorem Basis.op_norm_le {ι : Type _} [Fintype ι] (v : Basis ι 𝕜 E) {u : E →L[𝕜] F} {M : ℝ} (hM : 0 ≤ M)
    (hu : ∀ i, ∥u (v i)∥ ≤ M) : ∥u∥ ≤ Fintype.card ι • ∥v.equivFunL.toContinuousLinearMap∥ * M := by
  simpa using nnreal.coe_le_coe.mpr (v.op_nnnorm_le ⟨M, hM⟩ hu)

/-- A weaker version of `basis.op_nnnorm_le` that abstracts away the value of `C`. -/
theorem Basis.exists_op_nnnorm_le {ι : Type _} [Fintype ι] (v : Basis ι 𝕜 E) :
    ∃ C > (0 : ℝ≥0 ), ∀ {u : E →L[𝕜] F} (M : ℝ≥0 ), (∀ i, ∥u (v i)∥₊ ≤ M) → ∥u∥₊ ≤ C * M :=
  ⟨max (Fintype.card ι • ∥v.equivFunL.toContinuousLinearMap∥₊) 1, zero_lt_one.trans_le (le_max_rightₓ _ _),
    fun u M hu => (v.op_nnnorm_le M hu).trans <| mul_le_mul_of_nonneg_right (le_max_leftₓ _ _) (zero_le M)⟩

/-- A weaker version of `basis.op_norm_le` that abstracts away the value of `C`. -/
theorem Basis.exists_op_norm_le {ι : Type _} [Fintype ι] (v : Basis ι 𝕜 E) :
    ∃ C > (0 : ℝ), ∀ {u : E →L[𝕜] F} {M : ℝ}, 0 ≤ M → (∀ i, ∥u (v i)∥ ≤ M) → ∥u∥ ≤ C * M :=
  let ⟨C, hC, h⟩ := v.exists_op_nnnorm_le
  ⟨C, hC, fun u => Subtype.forall'.mpr h⟩

instance [FiniteDimensional 𝕜 E] [SecondCountableTopology F] : SecondCountableTopology (E →L[𝕜] F) := by
  set d := FiniteDimensional.finrank 𝕜 E
  suffices : ∀, ∀ ε > (0 : ℝ), ∀, ∃ n : (E →L[𝕜] F) → Finₓ d → ℕ, ∀ f g : E →L[𝕜] F, n f = n g → dist f g ≤ ε
  exact
    Metric.second_countable_of_countable_discretization fun ε ε_pos =>
      ⟨Finₓ d → ℕ, by
        infer_instance, this ε ε_pos⟩
  intro ε ε_pos
  obtain ⟨u : ℕ → F, hu : DenseRange u⟩ := exists_dense_seq F
  let v := FiniteDimensional.finBasis 𝕜 E
  obtain ⟨C : ℝ, C_pos : 0 < C, hC : ∀ {φ : E →L[𝕜] F} {M : ℝ}, 0 ≤ M → (∀ i, ∥φ (v i)∥ ≤ M) → ∥φ∥ ≤ C * M⟩ :=
    v.exists_op_norm_le
  have h_2C : 0 < 2 * C := mul_pos zero_lt_two C_pos
  have hε2C : 0 < ε / (2 * C) := div_pos ε_pos h_2C
  have : ∀ φ : E →L[𝕜] F, ∃ n : Finₓ d → ℕ, ∥φ - (v.constrL <| u ∘ n)∥ ≤ ε / 2 := by
    intro φ
    have : ∀ i, ∃ n, ∥φ (v i) - u n∥ ≤ ε / (2 * C) := by
      simp only [← norm_sub_rev]
      intro i
      have : φ (v i) ∈ Closure (range u) := hu _
      obtain ⟨n, hn⟩ : ∃ n, ∥u n - φ (v i)∥ < ε / (2 * C) := by
        rw [mem_closure_iff_nhds_basis Metric.nhds_basis_ball] at this
        specialize this (ε / (2 * C)) hε2C
        simpa [← dist_eq_norm]
      exact ⟨n, le_of_ltₓ hn⟩
    choose n hn using this
    use n
    replace hn : ∀ i : Finₓ d, ∥(φ - (v.constrL <| u ∘ n)) (v i)∥ ≤ ε / (2 * C)
    · simp [← hn]
      
    have : C * (ε / (2 * C)) = ε / 2 := by
      rw [eq_div_iff (two_ne_zero : (2 : ℝ) ≠ 0), mul_comm, ← mul_assoc, mul_div_cancel' _ (ne_of_gtₓ h_2C)]
    specialize hC (le_of_ltₓ hε2C) hn
    rwa [this] at hC
  choose n hn using this
  set Φ := fun φ : E →L[𝕜] F => v.constrL <| u ∘ n φ
  change ∀ z, dist z (Φ z) ≤ ε / 2 at hn
  use n
  intro x y hxy
  calc dist x y ≤ dist x (Φ x) + dist (Φ x) y := dist_triangle _ _ _ _ = dist x (Φ x) + dist y (Φ y) := by
      simp [← Φ, ← hxy, ← dist_comm]_ ≤ ε := by
      linarith [hn x, hn y]

variable (𝕜 E)

theorem FiniteDimensional.complete [FiniteDimensional 𝕜 E] : CompleteSpace E := by
  set e := ContinuousLinearEquiv.ofFinrankEq (@finrank_fin_fun 𝕜 _ (finrank 𝕜 E)).symm
  have : UniformEmbedding e.to_linear_equiv.to_equiv.symm := e.symm.uniform_embedding
  exact
    (complete_space_congr this).1
      (by
        infer_instance)

variable {𝕜 E}

/-- A finite-dimensional subspace is complete. -/
theorem Submodule.complete_of_finite_dimensional (s : Submodule 𝕜 E) [FiniteDimensional 𝕜 s] : IsComplete (s : Set E) :=
  complete_space_coe_iff_is_complete.1 (FiniteDimensional.complete 𝕜 s)

/-- A finite-dimensional subspace is closed. -/
theorem Submodule.closed_of_finite_dimensional (s : Submodule 𝕜 E) [FiniteDimensional 𝕜 s] : IsClosed (s : Set E) :=
  s.complete_of_finite_dimensional.IsClosed

theorem AffineSubspace.closed_of_finite_dimensional {P : Type _} [MetricSpace P] [NormedAddTorsor E P]
    (s : AffineSubspace 𝕜 P) [FiniteDimensional 𝕜 s.direction] : IsClosed (s : Set P) :=
  s.is_closed_direction_iff.mp s.direction.closed_of_finite_dimensional

section Riesz

/-- In an infinite dimensional space, given a finite number of points, one may find a point
with norm at most `R` which is at distance at least `1` of all these points. -/
theorem exists_norm_le_le_norm_sub_of_finset {c : 𝕜} (hc : 1 < ∥c∥) {R : ℝ} (hR : ∥c∥ < R) (h : ¬FiniteDimensional 𝕜 E)
    (s : Finset E) : ∃ x : E, ∥x∥ ≤ R ∧ ∀, ∀ y ∈ s, ∀, 1 ≤ ∥y - x∥ := by
  let F := Submodule.span 𝕜 (s : Set E)
  have : FiniteDimensional 𝕜 F :=
    Module.finite_def.2 ((Submodule.fg_top _).2 (Submodule.fg_def.2 ⟨s, Finset.finite_to_set _, rfl⟩))
  have Fclosed : IsClosed (F : Set E) := Submodule.closed_of_finite_dimensional _
  have : ∃ x, x ∉ F := by
    contrapose! h
    have : (⊤ : Submodule 𝕜 E) = F := by
      ext x
      simp [← h]
    have : FiniteDimensional 𝕜 (⊤ : Submodule 𝕜 E) := by
      rwa [this]
    refine' Module.finite_def.2 ((Submodule.fg_top _).1 (Module.finite_def.1 this))
  obtain ⟨x, xR, hx⟩ : ∃ x : E, ∥x∥ ≤ R ∧ ∀ y : E, y ∈ F → 1 ≤ ∥x - y∥ := riesz_lemma_of_norm_lt hc hR Fclosed this
  have hx' : ∀ y : E, y ∈ F → 1 ≤ ∥y - x∥ := by
    intro y hy
    rw [← norm_neg]
    simpa using hx y hy
  exact ⟨x, xR, fun y hy => hx' _ (Submodule.subset_span hy)⟩

/-- In an infinite-dimensional normed space, there exists a sequence of points which are all
bounded by `R` and at distance at least `1`. For a version not assuming `c` and `R`, see
`exists_seq_norm_le_one_le_norm_sub`. -/
theorem exists_seq_norm_le_one_le_norm_sub' {c : 𝕜} (hc : 1 < ∥c∥) {R : ℝ} (hR : ∥c∥ < R) (h : ¬FiniteDimensional 𝕜 E) :
    ∃ f : ℕ → E, (∀ n, ∥f n∥ ≤ R) ∧ ∀ m n, m ≠ n → 1 ≤ ∥f m - f n∥ := by
  have : IsSymm E fun x y : E => 1 ≤ ∥x - y∥ := by
    constructor
    intro x y hxy
    rw [← norm_neg]
    simpa
  apply exists_seq_of_forall_finset_exists' (fun x : E => ∥x∥ ≤ R) fun (x : E) (y : E) => 1 ≤ ∥x - y∥
  intro s hs
  exact exists_norm_le_le_norm_sub_of_finset hc hR h s

theorem exists_seq_norm_le_one_le_norm_sub (h : ¬FiniteDimensional 𝕜 E) :
    ∃ (R : ℝ)(f : ℕ → E), 1 < R ∧ (∀ n, ∥f n∥ ≤ R) ∧ ∀ m n, m ≠ n → 1 ≤ ∥f m - f n∥ := by
  obtain ⟨c, hc⟩ : ∃ c : 𝕜, 1 < ∥c∥ := NormedField.exists_one_lt_norm 𝕜
  have A : ∥c∥ < ∥c∥ + 1 := by
    linarith
  rcases exists_seq_norm_le_one_le_norm_sub' hc A h with ⟨f, hf⟩
  exact ⟨∥c∥ + 1, f, hc.trans A, hf.1, hf.2⟩

variable (𝕜)

/-- **Riesz's theorem**: if a closed ball with center zero of positive radius is compact in a vector
space, then the space is finite-dimensional. -/
theorem finite_dimensional_of_is_compact_closed_ball₀ {r : ℝ} (rpos : 0 < r)
    (h : IsCompact (Metric.ClosedBall (0 : E) r)) : FiniteDimensional 𝕜 E := by
  by_contra hfin
  obtain ⟨R, f, Rgt, fle, lef⟩ : ∃ (R : ℝ)(f : ℕ → E), 1 < R ∧ (∀ n, ∥f n∥ ≤ R) ∧ ∀ m n, m ≠ n → 1 ≤ ∥f m - f n∥ :=
    exists_seq_norm_le_one_le_norm_sub hfin
  have rRpos : 0 < r / R := div_pos rpos (zero_lt_one.trans Rgt)
  obtain ⟨c, hc⟩ : ∃ c : 𝕜, 0 < ∥c∥ ∧ ∥c∥ < r / R := NormedField.exists_norm_lt _ rRpos
  let g := fun n : ℕ => c • f n
  have A : ∀ n, g n ∈ Metric.ClosedBall (0 : E) r := by
    intro n
    simp only [← norm_smul, ← dist_zero_right, ← Metric.mem_closed_ball]
    calc ∥c∥ * ∥f n∥ ≤ r / R * R := mul_le_mul hc.2.le (fle n) (norm_nonneg _) rRpos.le _ = r := by
        field_simp [← (zero_lt_one.trans Rgt).ne']
  obtain ⟨x, hx, φ, φmono, φlim⟩ :
    ∃ (x : E)(H : x ∈ Metric.ClosedBall (0 : E) r)(φ : ℕ → ℕ), StrictMono φ ∧ tendsto (g ∘ φ) at_top (𝓝 x) :=
    h.tendsto_subseq A
  have B : CauchySeq (g ∘ φ) := φlim.cauchy_seq
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → dist ((g ∘ φ) n) ((g ∘ φ) N) < ∥c∥ := Metric.cauchy_seq_iff'.1 B ∥c∥ hc.1
  apply lt_irreflₓ ∥c∥
  calc ∥c∥ ≤ dist (g (φ (N + 1))) (g (φ N)) := by
      conv_lhs => rw [← mul_oneₓ ∥c∥]
      simp only [← g, ← dist_eq_norm, smul_sub, ← norm_smul, -mul_oneₓ]
      apply mul_le_mul_of_nonneg_left (lef _ _ (ne_of_gtₓ _)) (norm_nonneg _)
      exact φmono (Nat.lt_succ_selfₓ N)_ < ∥c∥ := hN (N + 1) (Nat.le_succₓ N)

/-- **Riesz's theorem**: if a closed ball of positive radius is compact in a vector space, then the
space is finite-dimensional. -/
theorem finite_dimensional_of_is_compact_closed_ball {r : ℝ} (rpos : 0 < r) {c : E}
    (h : IsCompact (Metric.ClosedBall c r)) : FiniteDimensional 𝕜 E := by
  apply finite_dimensional_of_is_compact_closed_ball₀ 𝕜 rpos
  have : Continuous fun x => -c + x := continuous_const.add continuous_id
  simpa using h.image this

end Riesz

/-- An injective linear map with finite-dimensional domain is a closed embedding. -/
theorem LinearEquiv.closed_embedding_of_injective {f : E →ₗ[𝕜] F} (hf : f.ker = ⊥) [FiniteDimensional 𝕜 E] :
    ClosedEmbedding ⇑f :=
  let g := LinearEquiv.ofInjective f (LinearMap.ker_eq_bot.mp hf)
  { embedding_subtype_coe.comp g.toContinuousLinearEquiv.toHomeomorph.Embedding with
    closed_range := by
      have := f.finite_dimensional_range
      simpa [← f.range_coe] using f.range.closed_of_finite_dimensional }

theorem ContinuousLinearMap.exists_right_inverse_of_surjective [FiniteDimensional 𝕜 F] (f : E →L[𝕜] F)
    (hf : f.range = ⊤) : ∃ g : F →L[𝕜] E, f.comp g = ContinuousLinearMap.id 𝕜 F :=
  let ⟨g, hg⟩ := (f : E →ₗ[𝕜] F).exists_right_inverse_of_surjective hf
  ⟨g.toContinuousLinearMap, ContinuousLinearMap.ext <| LinearMap.ext_iff.1 hg⟩

theorem closed_embedding_smul_left {c : E} (hc : c ≠ 0) : ClosedEmbedding fun x : 𝕜 => x • c :=
  LinearEquiv.closed_embedding_of_injective (LinearMap.ker_to_span_singleton 𝕜 E hc)

-- `smul` is a closed map in the first argument.
theorem is_closed_map_smul_left (c : E) : IsClosedMap fun x : 𝕜 => x • c := by
  by_cases' hc : c = 0
  · simp_rw [hc, smul_zero]
    exact is_closed_map_const
    
  · exact (closed_embedding_smul_left hc).IsClosedMap
    

open ContinuousLinearMap

/-- Continuous linear equivalence between continuous linear functions `𝕜ⁿ → E` and `Eⁿ`.
The spaces `𝕜ⁿ` and `Eⁿ` are represented as `ι → 𝕜` and `ι → E`, respectively,
where `ι` is a finite type. -/
def ContinuousLinearEquiv.piRing (ι : Type _) [Fintype ι] [DecidableEq ι] : ((ι → 𝕜) →L[𝕜] E) ≃L[𝕜] ι → E :=
  { LinearMap.toContinuousLinearMap.symm.trans (LinearEquiv.piRing 𝕜 E ι 𝕜) with
    continuous_to_fun := by
      refine' continuous_pi fun i => _
      exact (ContinuousLinearMap.apply 𝕜 E (Pi.single i 1)).Continuous,
    continuous_inv_fun := by
      simp_rw [LinearEquiv.inv_fun_eq_symm, LinearEquiv.trans_symm, LinearEquiv.symm_symm]
      change
        Continuous
          (linear_map.to_continuous_linear_map.to_linear_map.comp (LinearEquiv.piRing 𝕜 E ι 𝕜).symm.toLinearMap)
      apply AddMonoidHomClass.continuous_of_bound _ (Fintype.card ι : ℝ) fun g => _
      rw [← nsmul_eq_mul]
      apply op_norm_le_bound _ (nsmul_nonneg (norm_nonneg g) (Fintype.card ι)) fun t => _
      simp_rw [LinearMap.coe_comp, LinearEquiv.coe_to_linear_map, Function.comp_app,
        LinearMap.coe_to_continuous_linear_map', LinearEquiv.pi_ring_symm_apply]
      apply le_transₓ (norm_sum_le _ _)
      rw [smul_mul_assoc]
      refine' Finset.sum_le_card_nsmul _ _ _ fun i hi => _
      rw [norm_smul, mul_comm]
      exact mul_le_mul (norm_le_pi_norm g i) (norm_le_pi_norm t i) (norm_nonneg _) (norm_nonneg g) }

/-- A family of continuous linear maps is continuous on `s` if all its applications are. -/
theorem continuous_on_clm_apply {X : Type _} [TopologicalSpace X] [FiniteDimensional 𝕜 E] {f : X → E →L[𝕜] F}
    {s : Set X} : ContinuousOn f s ↔ ∀ y, ContinuousOn (fun x => f x y) s := by
  refine' ⟨fun h y => (ContinuousLinearMap.apply 𝕜 F y).Continuous.comp_continuous_on h, fun h => _⟩
  let d := finrank 𝕜 E
  have hd : d = finrank 𝕜 (Finₓ d → 𝕜) := (finrank_fin_fun 𝕜).symm
  let e₁ : E ≃L[𝕜] Finₓ d → 𝕜 := ContinuousLinearEquiv.ofFinrankEq hd
  let e₂ : (E →L[𝕜] F) ≃L[𝕜] Finₓ d → F :=
    (e₁.arrow_congr (1 : F ≃L[𝕜] F)).trans (ContinuousLinearEquiv.piRing (Finₓ d))
  rw [← Function.comp.left_id f, ← e₂.symm_comp_self]
  exact e₂.symm.continuous.comp_continuous_on (continuous_on_pi.mpr fun i => h _)

theorem continuous_clm_apply {X : Type _} [TopologicalSpace X] [FiniteDimensional 𝕜 E] {f : X → E →L[𝕜] F} :
    Continuous f ↔ ∀ y, Continuous fun x => f x y := by
  simp_rw [continuous_iff_continuous_on_univ, continuous_on_clm_apply]

end CompleteField

section ProperField

variable (𝕜 : Type u) [NondiscreteNormedField 𝕜] (E : Type v) [NormedGroup E] [NormedSpace 𝕜 E] [ProperSpace 𝕜]

/-- Any finite-dimensional vector space over a proper field is proper.
We do not register this as an instance to avoid an instance loop when trying to prove the
properness of `𝕜`, and the search for `𝕜` as an unknown metavariable. Declare the instance
explicitly when needed. -/
theorem FiniteDimensional.proper [FiniteDimensional 𝕜 E] : ProperSpace E := by
  set e := ContinuousLinearEquiv.ofFinrankEq (@finrank_fin_fun 𝕜 _ (finrank 𝕜 E)).symm
  exact e.symm.antilipschitz.proper_space e.symm.continuous e.symm.surjective

end ProperField

/- Over the real numbers, we can register the previous statement as an instance as it will not
cause problems in instance resolution since the properness of `ℝ` is already known. -/
instance (priority := 900) FiniteDimensional.proper_real (E : Type u) [NormedGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] : ProperSpace E :=
  FiniteDimensional.proper ℝ E

/-- If `E` is a finite dimensional normed real vector space, `x : E`, and `s` is a neighborhood of
`x` that is not equal to the whole space, then there exists a point `y ∈ frontier s` at distance
`metric.inf_dist x sᶜ` from `x`. See also
`is_compact.exists_mem_frontier_inf_dist_compl_eq_dist`. -/
theorem exists_mem_frontier_inf_dist_compl_eq_dist {E : Type _} [NormedGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {x : E} {s : Set E} (hx : x ∈ s) (hs : s ≠ univ) :
    ∃ y ∈ Frontier s, Metric.infDist x (sᶜ) = dist x y := by
  rcases Metric.exists_mem_closure_inf_dist_eq_dist (nonempty_compl.2 hs) x with ⟨y, hys, hyd⟩
  rw [closure_compl] at hys
  refine' ⟨y, ⟨Metric.closed_ball_inf_dist_compl_subset_closure hx <| Metric.mem_closed_ball.2 <| ge_of_eq _, hys⟩, hyd⟩
  rwa [dist_comm]

/-- If `K` is a compact set in a nontrivial real normed space and `x ∈ K`, then there exists a point
`y` of the boundary of `K` at distance `metric.inf_dist x Kᶜ` from `x`. See also
`exists_mem_frontier_inf_dist_compl_eq_dist`. -/
theorem IsCompact.exists_mem_frontier_inf_dist_compl_eq_dist {E : Type _} [NormedGroup E] [NormedSpace ℝ E]
    [Nontrivial E] {x : E} {K : Set E} (hK : IsCompact K) (hx : x ∈ K) :
    ∃ y ∈ Frontier K, Metric.infDist x (Kᶜ) = dist x y := by
  obtain hx' | hx' : x ∈ Interior K ∪ Frontier K := by
    rw [← closure_eq_interior_union_frontier]
    exact subset_closure hx
  · rw [mem_interior_iff_mem_nhds, metric.nhds_basis_closed_ball.mem_iff] at hx'
    rcases hx' with ⟨r, hr₀, hrK⟩
    have : FiniteDimensional ℝ E :=
      finite_dimensional_of_is_compact_closed_ball ℝ hr₀ (compact_of_is_closed_subset hK Metric.is_closed_ball hrK)
    exact exists_mem_frontier_inf_dist_compl_eq_dist hx hK.ne_univ
    
  · refine' ⟨x, hx', _⟩
    rw [frontier_eq_closure_inter_closure] at hx'
    rw [Metric.inf_dist_zero_of_mem_closure hx'.2, dist_self]
    

/-- In a finite dimensional vector space over `ℝ`, the series `∑ x, ∥f x∥` is unconditionally
summable if and only if the series `∑ x, f x` is unconditionally summable. One implication holds in
any complete normed space, while the other holds only in finite dimensional spaces. -/
theorem summable_norm_iff {α E : Type _} [NormedGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {f : α → E} :
    (Summable fun x => ∥f x∥) ↔ Summable f := by
  refine' ⟨summable_of_summable_norm, fun hf => _⟩
  -- First we use a finite basis to reduce the problem to the case `E = fin N → ℝ`
  suffices ∀ {N : ℕ} {g : α → Finₓ N → ℝ}, Summable g → Summable fun x => ∥g x∥ by
    obtain v := fin_basis ℝ E
    set e := v.equiv_funL
    have : Summable fun x => ∥e (f x)∥ := this (e.summable.2 hf)
    refine' summable_of_norm_bounded _ (this.mul_left ↑∥(e.symm : (Finₓ (finrank ℝ E) → ℝ) →L[ℝ] E)∥₊) fun i => _
    simpa using (e.symm : (Finₓ (finrank ℝ E) → ℝ) →L[ℝ] E).le_op_norm (e <| f i)
  clear! E
  -- Now we deal with `g : α → fin N → ℝ`
  intro N g hg
  have : ∀ i, Summable fun x => ∥g x i∥ := fun i => (Pi.summable.1 hg i).abs
  refine' summable_of_norm_bounded _ (summable_sum fun i (hi : i ∈ Finset.univ) => this i) fun x => _
  rw [norm_norm, pi_norm_le_iff]
  · refine' fun i => Finset.single_le_sum (fun i hi => _) (Finset.mem_univ i)
    exact norm_nonneg (g x i)
    
  · exact Finset.sum_nonneg fun _ _ => norm_nonneg _
    

theorem summable_of_is_O' {ι E F : Type _} [NormedGroup E] [CompleteSpace E] [NormedGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] {f : ι → E} {g : ι → F} (hg : Summable g) (h : f =O[cofinite] g) : Summable f :=
  summable_of_is_O (summable_norm_iff.mpr hg) h.norm_right

theorem summable_of_is_O_nat' {E F : Type _} [NormedGroup E] [CompleteSpace E] [NormedGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] {f : ℕ → E} {g : ℕ → F} (hg : Summable g) (h : f =O[at_top] g) : Summable f :=
  summable_of_is_O_nat (summable_norm_iff.mpr hg) h.norm_right

theorem summable_of_is_equivalent {ι E : Type _} [NormedGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {f : ι → E}
    {g : ι → E} (hg : Summable g) (h : f ~[cofinite] g) : Summable f :=
  hg.trans_sub (summable_of_is_O' hg h.IsO.IsO)

theorem summable_of_is_equivalent_nat {E : Type _} [NormedGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {f : ℕ → E}
    {g : ℕ → E} (hg : Summable g) (h : f ~[at_top] g) : Summable f :=
  hg.trans_sub (summable_of_is_O_nat' hg h.IsO.IsO)

theorem IsEquivalent.summable_iff {ι E : Type _} [NormedGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {f : ι → E}
    {g : ι → E} (h : f ~[cofinite] g) : Summable f ↔ Summable g :=
  ⟨fun hf => summable_of_is_equivalent hf h.symm, fun hg => summable_of_is_equivalent hg h⟩

theorem IsEquivalent.summable_iff_nat {E : Type _} [NormedGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {f : ℕ → E}
    {g : ℕ → E} (h : f ~[at_top] g) : Summable f ↔ Summable g :=
  ⟨fun hf => summable_of_is_equivalent_nat hf h.symm, fun hg => summable_of_is_equivalent_nat hg h⟩

