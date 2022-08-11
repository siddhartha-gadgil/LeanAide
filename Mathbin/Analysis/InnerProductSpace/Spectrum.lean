/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import Mathbin.Analysis.InnerProductSpace.Rayleigh
import Mathbin.Analysis.InnerProductSpace.PiL2

/-! # Spectral theory of self-adjoint operators

This file covers the spectral theory of self-adjoint operators on an inner product space.

The first part of the file covers general properties, true without any condition on boundedness or
compactness of the operator or finite-dimensionality of the underlying space, notably:
* `is_self_adjoint.conj_eigenvalue_eq_self`: the eigenvalues are real
* `is_self_adjoint.orthogonal_family_eigenspaces`: the eigenspaces are orthogonal
* `is_self_adjoint.orthogonal_supr_eigenspaces`: the restriction of the operator to the mutual
  orthogonal complement of the eigenspaces has, itself, no eigenvectors

The second part of the file covers properties of self-adjoint operators in finite dimension.
Letting `T` be a self-adjoint operator on a finite-dimensional inner product space `T`,
* The definition `is_self_adjoint.diagonalization` provides a linear isometry equivalence `E` to
  the direct sum of the eigenspaces of `T`.  The theorem
  `is_self_adjoint.diagonalization_apply_self_apply` states that, when `T` is transferred via this
  equivalence to an operator on the direct sum, it acts diagonally.
* The definition `is_self_adjoint.eigenvector_basis` provides an orthonormal basis for `E`
  consisting of eigenvectors of `T`, with `is_self_adjoint.eigenvalues` giving the corresponding
  list of eigenvalues, as real numbers.  The definition `is_self_adjoint.diagonalization_basis`
  gives the associated linear isometry equivalence from `E` to Euclidean space, and the theorem
  `is_self_adjoint.diagonalization_basis_apply_self_apply` states that, when `T` is transferred via
  this equivalence to an operator on Euclidean space, it acts diagonally.

These are forms of the *diagonalization theorem* for self-adjoint operators on finite-dimensional
inner product spaces.

## TODO

Spectral theory for compact self-adjoint operators, bounded self-adjoint operators.

## Tags

self-adjoint operator, spectral theorem, diagonalization theorem

-/


variable {𝕜 : Type _} [IsROrC 𝕜] [dec_𝕜 : DecidableEq 𝕜]

variable {E : Type _} [InnerProductSpace 𝕜 E]

-- mathport name: «expr⟪ , ⟫»
local notation "⟪" x ", " y "⟫" => @inner 𝕜 E _ x y

open BigOperators ComplexConjugate

open Module.End

namespace InnerProductSpace

namespace IsSelfAdjoint

variable {T : E →ₗ[𝕜] E} (hT : IsSelfAdjoint T)

include hT

/-- A self-adjoint operator preserves orthogonal complements of its eigenspaces. -/
theorem invariant_orthogonal_eigenspace (μ : 𝕜) (v : E) (hv : v ∈ (eigenspace T μ)ᗮ) : T v ∈ (eigenspace T μ)ᗮ := by
  intro w hw
  have : T w = (μ : 𝕜) • w := by
    rwa [mem_eigenspace_iff] at hw
  simp [hT w, ← this, ← inner_smul_left, ← hv w hw]

/-- The eigenvalues of a self-adjoint operator are real. -/
theorem conj_eigenvalue_eq_self {μ : 𝕜} (hμ : HasEigenvalue T μ) : conj μ = μ := by
  obtain ⟨v, hv₁, hv₂⟩ := hμ.exists_has_eigenvector
  rw [mem_eigenspace_iff] at hv₁
  simpa [← hv₂, ← inner_smul_left, ← inner_smul_right, ← hv₁] using hT v v

/-- The eigenspaces of a self-adjoint operator are mutually orthogonal. -/
theorem orthogonal_family_eigenspaces :
    @OrthogonalFamily 𝕜 _ _ _ _ (fun μ => eigenspace T μ) _ fun μ => (eigenspace T μ).subtypeₗᵢ := by
  rintro μ ν hμν ⟨v, hv⟩ ⟨w, hw⟩
  by_cases' hv' : v = 0
  · simp [← hv']
    
  have H := hT.conj_eigenvalue_eq_self (has_eigenvalue_of_has_eigenvector ⟨hv, hv'⟩)
  rw [mem_eigenspace_iff] at hv hw
  refine' Or.resolve_left _ hμν.symm
  simpa [← inner_smul_left, ← inner_smul_right, ← hv, ← hw, ← H] using (hT v w).symm

theorem orthogonal_family_eigenspaces' :
    @OrthogonalFamily 𝕜 _ _ _ _ (fun μ : Eigenvalues T => eigenspace T μ) _ fun μ => (eigenspace T μ).subtypeₗᵢ :=
  hT.orthogonal_family_eigenspaces.comp Subtype.coe_injective

/-- The mutual orthogonal complement of the eigenspaces of a self-adjoint operator on an inner
product space is an invariant subspace of the operator. -/
theorem orthogonal_supr_eigenspaces_invariant ⦃v : E⦄ (hv : v ∈ (⨆ μ, eigenspace T μ)ᗮ) :
    T v ∈ (⨆ μ, eigenspace T μ)ᗮ := by
  rw [← Submodule.infi_orthogonal] at hv⊢
  exact T.infi_invariant hT.invariant_orthogonal_eigenspace v hv

/-- The mutual orthogonal complement of the eigenspaces of a self-adjoint operator on an inner
product space has no eigenvalues. -/
theorem orthogonal_supr_eigenspaces (μ : 𝕜) : eigenspace (T.restrict hT.orthogonal_supr_eigenspaces_invariant) μ = ⊥ :=
  by
  set p : Submodule 𝕜 E := (⨆ μ, eigenspace T μ)ᗮ
  refine' eigenspace_restrict_eq_bot hT.orthogonal_supr_eigenspaces_invariant _
  have H₂ : p ≤ (eigenspace T μ)ᗮ := Submodule.orthogonal_le (le_supr _ _)
  exact (eigenspace T μ).orthogonal_disjoint.mono_right H₂

/-! ### Finite-dimensional theory -/


variable [FiniteDimensional 𝕜 E]

/-- The mutual orthogonal complement of the eigenspaces of a self-adjoint operator on a
finite-dimensional inner product space is trivial. -/
theorem orthogonal_supr_eigenspaces_eq_bot : (⨆ μ, eigenspace T μ)ᗮ = ⊥ := by
  have hT' : is_self_adjoint _ := hT.restrict_invariant hT.orthogonal_supr_eigenspaces_invariant
  -- a self-adjoint operator on a nontrivial inner product space has an eigenvalue
  have := hT'.subsingleton_of_no_eigenvalue_finite_dimensional hT.orthogonal_supr_eigenspaces
  exact Submodule.eq_bot_of_subsingleton _

theorem orthogonal_supr_eigenspaces_eq_bot' : (⨆ μ : Eigenvalues T, eigenspace T μ)ᗮ = ⊥ :=
  show (⨆ μ : { μ // eigenspace T μ ≠ ⊥ }, eigenspace T μ)ᗮ = ⊥ by
    rw [supr_ne_bot_subtype, hT.orthogonal_supr_eigenspaces_eq_bot]

include dec_𝕜

/-- The eigenspaces of a self-adjoint operator on a finite-dimensional inner product space `E` give
an internal direct sum decomposition of `E`. -/
theorem direct_sum_is_internal : DirectSum.IsInternal fun μ : Eigenvalues T => eigenspace T μ :=
  hT.orthogonal_family_eigenspaces'.is_internal_iff.mpr hT.orthogonal_supr_eigenspaces_eq_bot'

section Version1

/-- Isometry from an inner product space `E` to the direct sum of the eigenspaces of some
self-adjoint operator `T` on `E`. -/
noncomputable def diagonalization : E ≃ₗᵢ[𝕜] PiLp 2 fun μ : Eigenvalues T => eigenspace T μ :=
  hT.direct_sum_is_internal.isometryL2OfOrthogonalFamily hT.orthogonal_family_eigenspaces'

@[simp]
theorem diagonalization_symm_apply (w : PiLp 2 fun μ : Eigenvalues T => eigenspace T μ) :
    hT.diagonalization.symm w = ∑ μ, w μ :=
  hT.direct_sum_is_internal.isometry_L2_of_orthogonal_family_symm_apply hT.orthogonal_family_eigenspaces' w

/-- *Diagonalization theorem*, *spectral theorem*; version 1: A self-adjoint operator `T` on a
finite-dimensional inner product space `E` acts diagonally on the decomposition of `E` into the
direct sum of the eigenspaces of `T`. -/
theorem diagonalization_apply_self_apply (v : E) (μ : Eigenvalues T) :
    hT.diagonalization (T v) μ = (μ : 𝕜) • hT.diagonalization v μ := by
  suffices
    ∀ w : PiLp 2 fun μ : eigenvalues T => eigenspace T μ,
      T (hT.diagonalization.symm w) = hT.diagonalization.symm fun μ => (μ : 𝕜) • w μ
    by
    simpa [← LinearIsometryEquiv.symm_apply_apply, -is_self_adjoint.diagonalization_symm_apply] using
      congr_arg (fun w => hT.diagonalization w μ) (this (hT.diagonalization v))
  intro w
  have hwT : ∀ μ : eigenvalues T, T (w μ) = (μ : 𝕜) • w μ := by
    intro μ
    simpa [← mem_eigenspace_iff] using (w μ).Prop
  simp [← hwT]

end Version1

section Version2

variable {n : ℕ} (hn : FiniteDimensional.finrank 𝕜 E = n)

/-- A choice of orthonormal basis of eigenvectors for self-adjoint operator `T` on a
finite-dimensional inner product space `E`.

TODO Postcompose with a permutation so that these eigenvectors are listed in increasing order of
eigenvalue. -/
noncomputable def eigenvectorBasis : OrthonormalBasis (Finₓ n) 𝕜 E :=
  hT.direct_sum_is_internal.subordinateOrthonormalBasis hn hT.orthogonal_family_eigenspaces'

/-- The sequence of real eigenvalues associated to the standard orthonormal basis of eigenvectors
for a self-adjoint operator `T` on `E`.

TODO Postcompose with a permutation so that these eigenvalues are listed in increasing order. -/
noncomputable def eigenvalues (i : Finₓ n) : ℝ :=
  @IsROrC.re 𝕜 _ <| hT.direct_sum_is_internal.subordinateOrthonormalBasisIndex hn i hT.orthogonal_family_eigenspaces'

theorem has_eigenvector_eigenvector_basis (i : Finₓ n) :
    HasEigenvector T (hT.Eigenvalues hn i) (hT.eigenvectorBasis hn i) := by
  let v : E := hT.eigenvector_basis hn i
  let μ : 𝕜 := hT.direct_sum_is_internal.subordinate_orthonormal_basis_index hn i hT.orthogonal_family_eigenspaces'
  change has_eigenvector T (IsROrC.re μ) v
  have key : has_eigenvector T μ v := by
    have H₁ : v ∈ eigenspace T μ :=
      hT.direct_sum_is_internal.subordinate_orthonormal_basis_subordinate hn i hT.orthogonal_family_eigenspaces'
    have H₂ : v ≠ 0 := by
      simpa using (hT.eigenvector_basis hn).toBasis.ne_zero i
    exact ⟨H₁, H₂⟩
  have re_μ : ↑(IsROrC.re μ) = μ := by
    rw [← IsROrC.eq_conj_iff_re]
    exact hT.conj_eigenvalue_eq_self (has_eigenvalue_of_has_eigenvector key)
  simpa [← re_μ] using key

theorem has_eigenvalue_eigenvalues (i : Finₓ n) : HasEigenvalue T (hT.Eigenvalues hn i) :=
  Module.End.has_eigenvalue_of_has_eigenvector (hT.has_eigenvector_eigenvector_basis hn i)

@[simp]
theorem apply_eigenvector_basis (i : Finₓ n) :
    T (hT.eigenvectorBasis hn i) = (hT.Eigenvalues hn i : 𝕜) • hT.eigenvectorBasis hn i :=
  mem_eigenspace_iff.mp (hT.has_eigenvector_eigenvector_basis hn i).1

/-- *Diagonalization theorem*, *spectral theorem*; version 2: A self-adjoint operator `T` on a
finite-dimensional inner product space `E` acts diagonally on the identification of `E` with
Euclidean space induced by an orthonormal basis of eigenvectors of `T`. -/
theorem diagonalization_basis_apply_self_apply (v : E) (i : Finₓ n) :
    (hT.eigenvectorBasis hn).repr (T v) i = hT.Eigenvalues hn i * (hT.eigenvectorBasis hn).repr v i := by
  suffices
    ∀ w : EuclideanSpace 𝕜 (Finₓ n),
      T ((hT.eigenvector_basis hn).repr.symm w) = (hT.eigenvector_basis hn).repr.symm fun i => hT.eigenvalues hn i * w i
    by
    simpa [← OrthonormalBasis.sum_repr_symm] using
      congr_arg (fun v => (hT.eigenvector_basis hn).repr v i) (this ((hT.eigenvector_basis hn).repr v))
  intro w
  simp_rw [← OrthonormalBasis.sum_repr_symm, LinearMap.map_sum, LinearMap.map_smul, apply_eigenvector_basis]
  apply Fintype.sum_congr
  intro a
  rw [smul_smul, mul_comm]

end Version2

end IsSelfAdjoint

end InnerProductSpace

section Nonneg

@[simp]
theorem inner_product_apply_eigenvector {μ : 𝕜} {v : E} {T : E →ₗ[𝕜] E} (h : v ∈ Module.End.eigenspace T μ) :
    ⟪v, T v⟫ = μ * ∥v∥ ^ 2 := by
  simp only [← mem_eigenspace_iff.mp h, ← inner_smul_right, ← inner_self_eq_norm_sq_to_K]

theorem eigenvalue_nonneg_of_nonneg {μ : ℝ} {T : E →ₗ[𝕜] E} (hμ : HasEigenvalue T μ)
    (hnn : ∀ x : E, 0 ≤ IsROrC.re ⟪x, T x⟫) : 0 ≤ μ := by
  obtain ⟨v, hv⟩ := hμ.exists_has_eigenvector
  have hpos : 0 < ∥v∥ ^ 2 := by
    simpa only [← sq_pos_iff, ← norm_ne_zero_iff] using hv.2
  have : IsROrC.re ⟪v, T v⟫ = μ * ∥v∥ ^ 2 := by
    exact_mod_cast congr_arg IsROrC.re (inner_product_apply_eigenvector hv.1)
  exact (zero_le_mul_right hpos).mp (this ▸ hnn v)

theorem eigenvalue_pos_of_pos {μ : ℝ} {T : E →ₗ[𝕜] E} (hμ : HasEigenvalue T μ) (hnn : ∀ x : E, 0 < IsROrC.re ⟪x, T x⟫) :
    0 < μ := by
  obtain ⟨v, hv⟩ := hμ.exists_has_eigenvector
  have hpos : 0 < ∥v∥ ^ 2 := by
    simpa only [← sq_pos_iff, ← norm_ne_zero_iff] using hv.2
  have : IsROrC.re ⟪v, T v⟫ = μ * ∥v∥ ^ 2 := by
    exact_mod_cast congr_arg IsROrC.re (inner_product_apply_eigenvector hv.1)
  exact (zero_lt_mul_right hpos).mp (this ▸ hnn v)

end Nonneg

