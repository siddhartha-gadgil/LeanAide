/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Anatole Dedecker
-/
import Mathbin.Analysis.LocallyConvex.BalancedCoreHull

/-!
# Finite dimensional topological vector spaces over complete fields

Let `𝕜` be a nondiscrete and complete normed field, and `E` a topological vector space (TVS) over
`𝕜` (i.e we have `[add_comm_group E] [module 𝕜 E] [topological_space E] [topological_add_group E]`
and `[has_continuous_smul 𝕜 E]`).

If `E` is finite dimensional and Hausdorff, then all linear maps from `E` to any other TVS are
continuous.

When `E` is a normed space, this gets us the equivalence of norms in finite dimension.

## Main results :

* `linear_map.continuous_iff_is_closed_ker` : a linear form is continuous if and only if its kernel
  is closed.
* `linear_map.continuous_of_finite_dimensional` : a linear map on a finite-dimensional Hausdorff
  space over a complete field is continuous.

## TODO

Generalize more of `analysis/normed_space/finite_dimension` to general TVSs.

## Implementation detail

The main result from which everything follows is the fact that, if `ξ : ι → E` is a finite basis,
then `ξ.equiv_fun : E →ₗ (ι → 𝕜)` is continuous. However, for technical reasons, it is easier to
prove this when `ι` and `E` live ine the same universe. So we start by doing that as a private
lemma, then we deduce `linear_map.continuous_of_finite_dimensional` from it, and then the general
result follows as `continuous_equiv_fun_basis`.

-/


universe u v w x

noncomputable section

open Set FiniteDimensional TopologicalSpace Filter

open BigOperators

section Semiringₓ

variable {ι 𝕜 F : Type _} [Fintype ι] [Semiringₓ 𝕜] [TopologicalSpace 𝕜] [AddCommMonoidₓ F] [Module 𝕜 F]
  [TopologicalSpace F] [HasContinuousAdd F] [HasContinuousSmul 𝕜 F]

/-- A linear map on `ι → 𝕜` (where `ι` is a fintype) is continuous -/
theorem LinearMap.continuous_on_pi (f : (ι → 𝕜) →ₗ[𝕜] F) : Continuous f := by
  classical
  -- for the proof, write `f` in the standard basis, and use that each coordinate is a continuous
  -- function.
  have : (f : (ι → 𝕜) → F) = fun x => ∑ i : ι, x i • f fun j => if i = j then 1 else 0 := by
    ext x
    exact f.pi_apply_eq_sum_univ x
  rw [this]
  refine' continuous_finset_sum _ fun i hi => _
  exact (continuous_apply i).smul continuous_const

end Semiringₓ

section Field

variable {ι 𝕜 E F : Type _} [Fintype ι] [Field 𝕜] [TopologicalSpace 𝕜] [AddCommGroupₓ E] [Module 𝕜 E]
  [TopologicalSpace E] [AddCommGroupₓ F] [Module 𝕜 F] [TopologicalSpace F] [TopologicalAddGroup F]
  [HasContinuousSmul 𝕜 F]

/-- The space of continuous linear maps between finite-dimensional spaces is finite-dimensional. -/
instance [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] : FiniteDimensional 𝕜 (E →L[𝕜] F) :=
  FiniteDimensional.of_injective (ContinuousLinearMap.coeLm 𝕜 : (E →L[𝕜] F) →ₗ[𝕜] E →ₗ[𝕜] F)
    ContinuousLinearMap.coe_injective

end Field

section NormedField

variable {𝕜 : Type u} [hnorm : NondiscreteNormedField 𝕜] {E : Type v} [AddCommGroupₓ E] [Module 𝕜 E]
  [TopologicalSpace E] [TopologicalAddGroup E] [HasContinuousSmul 𝕜 E] {F : Type w} [AddCommGroupₓ F] [Module 𝕜 F]
  [TopologicalSpace F] [TopologicalAddGroup F] [HasContinuousSmul 𝕜 F] {F' : Type x} [AddCommGroupₓ F'] [Module 𝕜 F']
  [TopologicalSpace F'] [TopologicalAddGroup F'] [HasContinuousSmul 𝕜 F']

include hnorm

/-- If `𝕜` is a nondiscrete normed field, any T2 topology on `𝕜` which makes it a topological vector
    space over itself (with the norm topology) is *equal* to the norm topology. -/
theorem unique_topology_of_t2 {t : TopologicalSpace 𝕜} (h₁ : @TopologicalAddGroup 𝕜 t _)
    (h₂ : @HasContinuousSmul 𝕜 𝕜 _ hnorm.toUniformSpace.toTopologicalSpace t) (h₃ : @T2Space 𝕜 t) :
    t = hnorm.toUniformSpace.toTopologicalSpace := by
  -- Let `𝓣₀` denote the topology on `𝕜` induced by the norm, and `𝓣` be any T2 vector
  -- topology on `𝕜`. To show that `𝓣₀ = 𝓣`, it suffices to show that they have the same
  -- neighborhoods of 0.
  refine' TopologicalAddGroup.ext h₁ inferInstance (le_antisymmₓ _ _)
  · -- To show `𝓣 ≤ 𝓣₀`, we have to show that closed balls are `𝓣`-neighborhoods of 0.
    rw [metric.nhds_basis_closed_ball.ge_iff]
    -- Let `ε > 0`. Since `𝕜` is nondiscrete, we have `0 < ∥ξ₀∥ < ε` for some `ξ₀ : 𝕜`.
    intro ε hε
    rcases NormedField.exists_norm_lt 𝕜 hε with ⟨ξ₀, hξ₀, hξ₀ε⟩
    -- Since `ξ₀ ≠ 0` and `𝓣` is T2, we know that `{ξ₀}ᶜ` is a `𝓣`-neighborhood of 0.
    have : {ξ₀}ᶜ ∈ @nhds 𝕜 t 0 := IsOpen.mem_nhds is_open_compl_singleton (Ne.symm <| norm_ne_zero_iff.mp hξ₀.ne.symm)
    -- Thus, its balanced core `𝓑` is too. Let's show that the closed ball of radius `ε` contains
    -- `𝓑`, which will imply that the closed ball is indeed a `𝓣`-neighborhood of 0.
    have : BalancedCore 𝕜 ({ξ₀}ᶜ) ∈ @nhds 𝕜 t 0 := balanced_core_mem_nhds_zero this
    refine' mem_of_superset this fun ξ hξ => _
    -- Let `ξ ∈ 𝓑`. We want to show `∥ξ∥ < ε`. If `ξ = 0`, this is trivial.
    by_cases' hξ0 : ξ = 0
    · rw [hξ0]
      exact Metric.mem_closed_ball_self hε.le
      
    · rw [mem_closed_ball_zero_iff]
      -- Now suppose `ξ ≠ 0`. By contradiction, let's assume `ε < ∥ξ∥`, and show that
      -- `ξ₀ ∈ 𝓑 ⊆ {ξ₀}ᶜ`, which is a contradiction.
      by_contra' h
      suffices (ξ₀ * ξ⁻¹) • ξ ∈ BalancedCore 𝕜 ({ξ₀}ᶜ) by
        rw [smul_eq_mul 𝕜, mul_assoc, inv_mul_cancel hξ0, mul_oneₓ] at this
        exact not_mem_compl_iff.mpr (mem_singleton ξ₀) ((balanced_core_subset _) this)
      -- For that, we use that `𝓑` is balanced : since `∥ξ₀∥ < ε < ∥ξ∥`, we have `∥ξ₀ / ξ∥ ≤ 1`,
      -- hence `ξ₀ = (ξ₀ / ξ) • ξ ∈ 𝓑` because `ξ ∈ 𝓑`.
      refine' (balanced_core_balanced _).smul_mem _ hξ
      rw [norm_mul, norm_inv, mul_inv_le_iff (norm_pos_iff.mpr hξ0), mul_oneₓ]
      exact (hξ₀ε.trans h).le
      
    
  · -- Finally, to show `𝓣₀ ≤ 𝓣`, we simply argue that `id = (λ x, x • 1)` is continuous from
    -- `(𝕜, 𝓣₀)` to `(𝕜, 𝓣)` because `(•) : (𝕜, 𝓣₀) × (𝕜, 𝓣) → (𝕜, 𝓣)` is continuous.
    calc
      @nhds 𝕜 hnorm.to_uniform_space.to_topological_space 0 =
          map id (@nhds 𝕜 hnorm.to_uniform_space.to_topological_space 0) :=
        map_id.symm _ = map (fun x => id x • 1) (@nhds 𝕜 hnorm.to_uniform_space.to_topological_space 0) := by
        conv_rhs => congr ext rw [smul_eq_mul, mul_oneₓ] <;> rfl _ ≤ @nhds 𝕜 t ((0 : 𝕜) • 1) :=
        @tendsto.smul_const _ _ _ hnorm.to_uniform_space.to_topological_space t _ _ _ _ _ tendsto_id
          (1 : 𝕜)_ = @nhds 𝕜 t 0 :=
        by
        rw [zero_smul]
    

/-- Any linear form on a topological vector space over a nondiscrete normed field is continuous if
    its kernel is closed. -/
theorem LinearMap.continuous_of_is_closed_ker (l : E →ₗ[𝕜] 𝕜) (hl : IsClosed (l.ker : Set E)) : Continuous l := by
  -- `l` is either constant or surjective. If it is constant, the result is trivial.
  by_cases' H : finrank 𝕜 l.range = 0
  · rw [finrank_eq_zero, LinearMap.range_eq_bot] at H
    rw [H]
    exact continuous_zero
    
  · -- In the case where `l` is surjective, we factor it as `φ : (E ⧸ l.ker) ≃ₗ[𝕜] 𝕜`. Note that
    -- `E ⧸ l.ker` is T2 since `l.ker` is closed.
    have : finrank 𝕜 l.range = 1 := le_antisymmₓ (finrank_self 𝕜 ▸ l.range.finrank_le) (zero_lt_iff.mpr H)
    have hi : Function.Injective (l.ker.liftq l (le_reflₓ _)) := by
      rw [← LinearMap.ker_eq_bot]
      exact Submodule.ker_liftq_eq_bot _ _ _ (le_reflₓ _)
    have hs : Function.Surjective (l.ker.liftq l (le_reflₓ _)) := by
      rw [← LinearMap.range_eq_top, Submodule.range_liftq]
      exact eq_top_of_finrank_eq ((finrank_self 𝕜).symm ▸ this)
    let φ : (E ⧸ l.ker) ≃ₗ[𝕜] 𝕜 := LinearEquiv.ofBijective (l.ker.liftq l (le_reflₓ _)) hi hs
    have hlφ : (l : E → 𝕜) = φ ∘ l.ker.mkq := by
      ext <;> rfl
    -- Since the quotient map `E →ₗ[𝕜] (E ⧸ l.ker)` is continuous, the continuity of `l` will follow
    -- form the continuity of `φ`.
    suffices Continuous φ.to_equiv by
      rw [hlφ]
      exact this.comp continuous_quot_mk
    -- The pullback by `φ.symm` of the quotient topology is a T2 topology on `𝕜`, because `φ.symm`
    -- is injective. Since `φ.symm` is linear, it is also a vector space topology.
    -- Hence, we know that it is equal to the topology induced by the norm.
    have : induced φ.to_equiv.symm inferInstance = hnorm.to_uniform_space.to_topological_space := by
      refine'
        unique_topology_of_t2 (topological_add_group_induced φ.symm.to_linear_map)
          (has_continuous_smul_induced φ.symm.to_linear_map) _
      rw [t2_space_iff]
      exact fun x y hxy =>
        @separated_by_continuous _ _ (induced _ _) _ _ _ continuous_induced_dom _ _ (φ.to_equiv.symm.injective.ne hxy)
    -- Finally, the pullback by `φ.symm` is exactly the pushforward by `φ`, so we have to prove
    -- that `φ` is continuous when `𝕜` is endowed with the pushforward by `φ` of the quotient
    -- topology, which is trivial by definition of the pushforward.
    rw [this.symm, Equivₓ.induced_symm]
    exact continuous_coinduced_rng
    

/-- Any linear form on a topological vector space over a nondiscrete normed field is continuous if
    and only if its kernel is closed. -/
theorem LinearMap.continuous_iff_is_closed_ker (l : E →ₗ[𝕜] 𝕜) : Continuous l ↔ IsClosed (l.ker : Set E) :=
  ⟨fun h => is_closed_singleton.Preimage h, l.continuous_of_is_closed_ker⟩

variable [CompleteSpace 𝕜]

/-- This version imposes `ι` and `E` to live in the same universe, so you should instead use
`continuous_equiv_fun_basis` which gives the same result without universe restrictions. -/
private theorem continuous_equiv_fun_basis_aux [ht2 : T2Space E] {ι : Type v} [Fintype ι] (ξ : Basis ι 𝕜 E) :
    Continuous ξ.equivFun := by
  let this : UniformSpace E := TopologicalAddGroup.toUniformSpace E
  let this : UniformAddGroup E := topological_add_group_is_uniform
  let this : SeparatedSpace E := separated_iff_t2.mpr ht2
  induction' hn : Fintype.card ι with n IH generalizing ι E
  · rw [Fintype.card_eq_zero_iff] at hn
    exact continuous_of_const fun x y => funext hn.elim
    
  · have : FiniteDimensional 𝕜 E := of_fintype_basis ξ
    -- first step: thanks to the induction hypothesis, any n-dimensional subspace is equivalent
    -- to a standard space of dimension n, hence it is complete and therefore closed.
    have H₁ : ∀ s : Submodule 𝕜 E, finrank 𝕜 s = n → IsClosed (s : Set E) := by
      intro s s_dim
      let this : UniformAddGroup s := s.to_add_subgroup.uniform_add_group
      let b := Basis.ofVectorSpace 𝕜 s
      have U : UniformEmbedding b.equiv_fun.symm.to_equiv := by
        have : Fintype.card (Basis.OfVectorSpaceIndex 𝕜 s) = n := by
          rw [← s_dim]
          exact (finrank_eq_card_basis b).symm
        have : Continuous b.equiv_fun := IH b this
        exact b.equiv_fun.symm.uniform_embedding b.equiv_fun.symm.to_linear_map.continuous_on_pi this
      have : IsComplete (s : Set E) :=
        complete_space_coe_iff_is_complete.1
          ((complete_space_congr U).1
            (by
              infer_instance))
      exact this.is_closed
    -- second step: any linear form is continuous, as its kernel is closed by the first step
    have H₂ : ∀ f : E →ₗ[𝕜] 𝕜, Continuous f := by
      intro f
      by_cases' H : finrank 𝕜 f.range = 0
      · rw [finrank_eq_zero, LinearMap.range_eq_bot] at H
        rw [H]
        exact continuous_zero
        
      · have : finrank 𝕜 f.ker = n := by
          have Z := f.finrank_range_add_finrank_ker
          rw [finrank_eq_card_basis ξ, hn] at Z
          have : finrank 𝕜 f.range = 1 := le_antisymmₓ (finrank_self 𝕜 ▸ f.range.finrank_le) (zero_lt_iff.mpr H)
          rw [this, add_commₓ, Nat.add_one] at Z
          exact Nat.succ.injₓ Z
        have : IsClosed (f.ker : Set E) := H₁ _ this
        exact LinearMap.continuous_of_is_closed_ker f this
        
    rw [continuous_pi_iff]
    intro i
    change Continuous (ξ.coord i)
    exact H₂ (ξ.coord i)
    

/-- Any linear map on a finite dimensional space over a complete field is continuous. -/
theorem LinearMap.continuous_of_finite_dimensional [T2Space E] [FiniteDimensional 𝕜 E] (f : E →ₗ[𝕜] F') :
    Continuous f := by
  -- for the proof, go to a model vector space `b → 𝕜` thanks to `continuous_equiv_fun_basis`, and
  -- argue that all linear maps there are continuous.
  let b := Basis.ofVectorSpace 𝕜 E
  have A : Continuous b.equiv_fun := continuous_equiv_fun_basis_aux b
  have B : Continuous (f.comp (b.equiv_fun.symm : (Basis.OfVectorSpaceIndex 𝕜 E → 𝕜) →ₗ[𝕜] E)) :=
    LinearMap.continuous_on_pi _
  have : Continuous (f.comp (b.equiv_fun.symm : (Basis.OfVectorSpaceIndex 𝕜 E → 𝕜) →ₗ[𝕜] E) ∘ b.equiv_fun) := B.comp A
  convert this
  ext x
  dsimp'
  rw [Basis.equiv_fun_symm_apply, Basis.sum_repr]

instance LinearMap.continuousLinearMapClassOfFiniteDimensional [T2Space E] [FiniteDimensional 𝕜 E] :
    ContinuousLinearMapClass (E →ₗ[𝕜] F') 𝕜 E F' :=
  { LinearMap.semilinearMapClass with map_continuous := fun f => f.continuous_of_finite_dimensional }

/-- In finite dimensions over a non-discrete complete normed field, the canonical identification
(in terms of a basis) with `𝕜^n` (endowed with the product topology) is continuous.
This is the key fact wich makes all linear maps from a T2 finite dimensional TVS over such a field
continuous (see `linear_map.continuous_of_finite_dimensional`), which in turn implies that all
norms are equivalent in finite dimensions. -/
theorem continuous_equiv_fun_basis [T2Space E] {ι : Type _} [Fintype ι] (ξ : Basis ι 𝕜 E) : Continuous ξ.equivFun := by
  have : FiniteDimensional 𝕜 E := of_fintype_basis ξ
  exact ξ.equiv_fun.to_linear_map.continuous_of_finite_dimensional

namespace LinearMap

variable [T2Space E] [FiniteDimensional 𝕜 E]

/-- The continuous linear map induced by a linear map on a finite dimensional space -/
def toContinuousLinearMap : (E →ₗ[𝕜] F') ≃ₗ[𝕜] E →L[𝕜] F' where
  toFun := fun f => ⟨f, f.continuous_of_finite_dimensional⟩
  invFun := coe
  map_add' := fun f g => rfl
  map_smul' := fun c f => rfl
  left_inv := fun f => rfl
  right_inv := fun f => ContinuousLinearMap.coe_injective rfl

@[simp]
theorem coe_to_continuous_linear_map' (f : E →ₗ[𝕜] F') : ⇑f.toContinuousLinearMap = f :=
  rfl

@[simp]
theorem coe_to_continuous_linear_map (f : E →ₗ[𝕜] F') : (f.toContinuousLinearMap : E →ₗ[𝕜] F') = f :=
  rfl

@[simp]
theorem coe_to_continuous_linear_map_symm : ⇑(toContinuousLinearMap : (E →ₗ[𝕜] F') ≃ₗ[𝕜] E →L[𝕜] F').symm = coe :=
  rfl

@[simp]
theorem det_to_continuous_linear_map (f : E →ₗ[𝕜] E) : f.toContinuousLinearMap.det = f.det :=
  rfl

end LinearMap

namespace LinearEquiv

variable [T2Space E] [T2Space F] [FiniteDimensional 𝕜 E]

/-- The continuous linear equivalence induced by a linear equivalence on a finite dimensional
space. -/
def toContinuousLinearEquiv (e : E ≃ₗ[𝕜] F) : E ≃L[𝕜] F :=
  { e with continuous_to_fun := e.toLinearMap.continuous_of_finite_dimensional,
    continuous_inv_fun := by
      have : FiniteDimensional 𝕜 F := e.finite_dimensional
      exact e.symm.to_linear_map.continuous_of_finite_dimensional }

@[simp]
theorem coe_to_continuous_linear_equiv (e : E ≃ₗ[𝕜] F) : (e.toContinuousLinearEquiv : E →ₗ[𝕜] F) = e :=
  rfl

@[simp]
theorem coe_to_continuous_linear_equiv' (e : E ≃ₗ[𝕜] F) : (e.toContinuousLinearEquiv : E → F) = e :=
  rfl

@[simp]
theorem coe_to_continuous_linear_equiv_symm (e : E ≃ₗ[𝕜] F) : (e.toContinuousLinearEquiv.symm : F →ₗ[𝕜] E) = e.symm :=
  rfl

@[simp]
theorem coe_to_continuous_linear_equiv_symm' (e : E ≃ₗ[𝕜] F) : (e.toContinuousLinearEquiv.symm : F → E) = e.symm :=
  rfl

@[simp]
theorem to_linear_equiv_to_continuous_linear_equiv (e : E ≃ₗ[𝕜] F) : e.toContinuousLinearEquiv.toLinearEquiv = e := by
  ext x
  rfl

@[simp]
theorem to_linear_equiv_to_continuous_linear_equiv_symm (e : E ≃ₗ[𝕜] F) :
    e.toContinuousLinearEquiv.symm.toLinearEquiv = e.symm := by
  ext x
  rfl

end LinearEquiv

namespace ContinuousLinearMap

variable [T2Space E] [FiniteDimensional 𝕜 E]

/-- Builds a continuous linear equivalence from a continuous linear map on a finite-dimensional
vector space whose determinant is nonzero. -/
def toContinuousLinearEquivOfDetNeZero (f : E →L[𝕜] E) (hf : f.det ≠ 0) : E ≃L[𝕜] E :=
  ((f : E →ₗ[𝕜] E).equivOfDetNeZero hf).toContinuousLinearEquiv

@[simp]
theorem coe_to_continuous_linear_equiv_of_det_ne_zero (f : E →L[𝕜] E) (hf : f.det ≠ 0) :
    (f.toContinuousLinearEquivOfDetNeZero hf : E →L[𝕜] E) = f := by
  ext x
  rfl

@[simp]
theorem to_continuous_linear_equiv_of_det_ne_zero_apply (f : E →L[𝕜] E) (hf : f.det ≠ 0) (x : E) :
    f.toContinuousLinearEquivOfDetNeZero hf x = f x :=
  rfl

-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `«expr!![ »
-- ./././Mathport/Syntax/Translate/Basic.lean:1144:14: unsupported user notation matrix.notation
theorem _root_.matrix.to_lin_fin_two_prod_to_continuous_linear_map (a b c d : 𝕜) :
    (Matrix.toLin (Basis.finTwoProd 𝕜) (Basis.finTwoProd 𝕜)
          («expr!![ »
            "./././Mathport/Syntax/Translate/Basic.lean:1144:14: unsupported user notation matrix.notation")).toContinuousLinearMap =
      (a • ContinuousLinearMap.fst 𝕜 𝕜 𝕜 + b • ContinuousLinearMap.snd 𝕜 𝕜 𝕜).Prod
        (c • ContinuousLinearMap.fst 𝕜 𝕜 𝕜 + d • ContinuousLinearMap.snd 𝕜 𝕜 𝕜) :=
  ContinuousLinearMap.ext <| Matrix.to_lin_fin_two_prod_apply _ _ _ _

end ContinuousLinearMap

end NormedField

