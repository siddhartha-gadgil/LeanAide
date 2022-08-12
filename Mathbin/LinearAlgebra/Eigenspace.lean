/-
Copyright (c) 2020 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp
-/
import Mathbin.LinearAlgebra.Charpoly.Basic
import Mathbin.LinearAlgebra.Finsupp
import Mathbin.LinearAlgebra.Matrix.ToLin
import Mathbin.Algebra.Algebra.Spectrum
import Mathbin.Order.Hom.Basic

/-!
# Eigenvectors and eigenvalues

This file defines eigenspaces, eigenvalues, and eigenvalues, as well as their generalized
counterparts. We follow Axler's approach [axler2015] because it allows us to derive many properties
without choosing a basis and without using matrices.

An eigenspace of a linear map `f` for a scalar `μ` is the kernel of the map `(f - μ • id)`. The
nonzero elements of an eigenspace are eigenvectors `x`. They have the property `f x = μ • x`. If
there are eigenvectors for a scalar `μ`, the scalar `μ` is called an eigenvalue.

There is no consensus in the literature whether `0` is an eigenvector. Our definition of
`has_eigenvector` permits only nonzero vectors. For an eigenvector `x` that may also be `0`, we
write `x ∈ f.eigenspace μ`.

A generalized eigenspace of a linear map `f` for a natural number `k` and a scalar `μ` is the kernel
of the map `(f - μ • id) ^ k`. The nonzero elements of a generalized eigenspace are generalized
eigenvectors `x`. If there are generalized eigenvectors for a natural number `k` and a scalar `μ`,
the scalar `μ` is called a generalized eigenvalue.

## References

* [Sheldon Axler, *Linear Algebra Done Right*][axler2015]
* https://en.wikipedia.org/wiki/Eigenvalues_and_eigenvectors

## Tags

eigenspace, eigenvector, eigenvalue, eigen
-/


universe u v w

namespace Module

namespace End

open Module PrincipalIdealRing Polynomial FiniteDimensional

open Polynomial

variable {K R : Type v} {V M : Type w} [CommRingₓ R] [AddCommGroupₓ M] [Module R M] [Field K] [AddCommGroupₓ V]
  [Module K V]

/-- The submodule `eigenspace f μ` for a linear map `f` and a scalar `μ` consists of all vectors `x`
    such that `f x = μ • x`. (Def 5.36 of [axler2015])-/
def eigenspace (f : End R M) (μ : R) : Submodule R M :=
  (f - algebraMap R (End R M) μ).ker

@[simp]
theorem eigenspace_zero (f : End R M) : f.eigenspace 0 = f.ker := by
  simp [← eigenspace]

/-- A nonzero element of an eigenspace is an eigenvector. (Def 5.7 of [axler2015]) -/
def HasEigenvector (f : End R M) (μ : R) (x : M) : Prop :=
  x ∈ eigenspace f μ ∧ x ≠ 0

/-- A scalar `μ` is an eigenvalue for a linear map `f` if there are nonzero vectors `x`
    such that `f x = μ • x`. (Def 5.5 of [axler2015]) -/
def HasEigenvalue (f : End R M) (a : R) : Prop :=
  eigenspace f a ≠ ⊥

/-- The eigenvalues of the endomorphism `f`, as a subtype of `R`. -/
def Eigenvalues (f : End R M) : Type _ :=
  { μ : R // f.HasEigenvalue μ }

instance (f : End R M) : Coe f.Eigenvalues R :=
  coeSubtype

theorem has_eigenvalue_of_has_eigenvector {f : End R M} {μ : R} {x : M} (h : HasEigenvector f μ x) :
    HasEigenvalue f μ := by
  rw [has_eigenvalue, Submodule.ne_bot_iff]
  use x
  exact h

theorem mem_eigenspace_iff {f : End R M} {μ : R} {x : M} : x ∈ eigenspace f μ ↔ f x = μ • x := by
  rw [eigenspace, LinearMap.mem_ker, LinearMap.sub_apply, algebra_map_End_apply, sub_eq_zero]

theorem HasEigenvector.apply_eq_smul {f : End R M} {μ : R} {x : M} (hx : f.HasEigenvector μ x) : f x = μ • x :=
  mem_eigenspace_iff.mp hx.1

theorem HasEigenvalue.exists_has_eigenvector {f : End R M} {μ : R} (hμ : f.HasEigenvalue μ) :
    ∃ v, f.HasEigenvector μ v :=
  Submodule.exists_mem_ne_zero_of_ne_bot hμ

theorem mem_spectrum_of_has_eigenvalue {f : End R M} {μ : R} (hμ : HasEigenvalue f μ) : μ ∈ Spectrum R f := by
  refine' spectrum.mem_iff.mpr fun h_unit => _
  set f' := LinearMap.GeneralLinearGroup.toLinearEquiv h_unit.unit
  rcases hμ.exists_has_eigenvector with ⟨v, hv⟩
  refine' hv.2 ((linear_map.ker_eq_bot'.mp f'.ker) v (_ : μ • v - f v = 0))
  rw [hv.apply_eq_smul, sub_self]

theorem has_eigenvalue_iff_mem_spectrum [FiniteDimensional K V] {f : End K V} {μ : K} :
    f.HasEigenvalue μ ↔ μ ∈ Spectrum K f :=
  Iff.intro mem_spectrum_of_has_eigenvalue fun h => by
    rwa [Spectrum.mem_iff, IsUnit.sub_iff, LinearMap.is_unit_iff_ker_eq_bot] at h

theorem eigenspace_div (f : End K V) (a b : K) (hb : b ≠ 0) :
    eigenspace f (a / b) = (b • f - algebraMap K (End K V) a).ker :=
  calc
    eigenspace f (a / b) = eigenspace f (b⁻¹ * a) := by
      rw [div_eq_mul_inv, mul_comm]
    _ = (f - (b⁻¹ * a) • LinearMap.id).ker := rfl
    _ = (f - b⁻¹ • a • LinearMap.id).ker := by
      rw [smul_smul]
    _ = (f - b⁻¹ • algebraMap K (End K V) a).ker := rfl
    _ = (b • (f - b⁻¹ • algebraMap K (End K V) a)).ker := by
      rw [LinearMap.ker_smul _ b hb]
    _ = (b • f - algebraMap K (End K V) a).ker := by
      rw [smul_sub, smul_inv_smul₀ hb]
    

theorem eigenspace_aeval_polynomial_degree_1 (f : End K V) (q : K[X]) (hq : degree q = 1) :
    eigenspace f (-q.coeff 0 / q.leadingCoeff) = (aeval f q).ker :=
  calc
    eigenspace f (-q.coeff 0 / q.leadingCoeff) = (q.leadingCoeff • f - algebraMap K (End K V) (-q.coeff 0)).ker := by
      rw [eigenspace_div]
      intro h
      rw [leading_coeff_eq_zero_iff_deg_eq_bot.1 h] at hq
      cases hq
    _ = (aeval f (c q.leadingCoeff * X + c (q.coeff 0))).ker := by
      rw [C_mul', aeval_def]
      simp [← algebraMap, ← Algebra.toRingHom]
    _ = (aeval f q).ker := by
      rwa [← eq_X_add_C_of_degree_eq_one]
    

theorem ker_aeval_ring_hom'_unit_polynomial (f : End K V) (c : K[X]ˣ) : (aeval f (c : K[X])).ker = ⊥ := by
  rw [Polynomial.eq_C_of_degree_eq_zero (degree_coe_units c)]
  simp only [← aeval_def, ← eval₂_C]
  apply ker_algebra_map_End
  apply coeff_coe_units_zero_ne_zero c

theorem aeval_apply_of_has_eigenvector {f : End K V} {p : K[X]} {μ : K} {x : V} (h : f.HasEigenvector μ x) :
    aeval f p x = p.eval μ • x := by
  apply p.induction_on
  · intro a
    simp [← Module.algebra_map_End_apply]
    
  · intro p q hp hq
    simp [← hp, ← hq, ← add_smul]
    
  · intro n a hna
    rw [mul_comm, pow_succₓ, mul_assoc, AlgHom.map_mul, LinearMap.mul_apply, mul_comm, hna]
    simp only [← mem_eigenspace_iff.1 h.1, ← smul_smul, ← aeval_X, ← eval_mul, ← eval_C, ← eval_pow, ← eval_X, ←
      LinearMap.map_smulₛₗ, ← RingHom.id_apply, ← mul_comm]
    

section minpoly

theorem is_root_of_has_eigenvalue {f : End K V} {μ : K} (h : f.HasEigenvalue μ) : (minpoly K f).IsRoot μ := by
  rcases(Submodule.ne_bot_iff _).1 h with ⟨w, ⟨H, ne0⟩⟩
  refine' Or.resolve_right (smul_eq_zero.1 _) ne0
  simp [aeval_apply_of_has_eigenvector ⟨H, ne0⟩, ← minpoly.aeval K f]

variable [FiniteDimensional K V] (f : End K V)

variable {f} {μ : K}

theorem has_eigenvalue_of_is_root (h : (minpoly K f).IsRoot μ) : f.HasEigenvalue μ := by
  cases' dvd_iff_is_root.2 h with p hp
  rw [has_eigenvalue, eigenspace]
  intro con
  cases' (LinearMap.is_unit_iff_ker_eq_bot _).2 Con with u hu
  have p_ne_0 : p ≠ 0 := by
    intro con
    apply minpoly.ne_zero f.is_integral
    rw [hp, Con, mul_zero]
  have h_deg := minpoly.degree_le_of_ne_zero K f p_ne_0 _
  · rw [hp, degree_mul, degree_X_sub_C, Polynomial.degree_eq_nat_degree p_ne_0] at h_deg
    norm_cast  at h_deg
    linarith
    
  · have h_aeval := minpoly.aeval K f
    revert h_aeval
    simp [← hp, hu]
    

theorem has_eigenvalue_iff_is_root : f.HasEigenvalue μ ↔ (minpoly K f).IsRoot μ :=
  ⟨is_root_of_has_eigenvalue, has_eigenvalue_of_is_root⟩

/-- An endomorphism of a finite-dimensional vector space has finitely many eigenvalues. -/
noncomputable instance (f : End K V) : Fintype f.Eigenvalues :=
  Set.Finite.fintype
    (by
      have h : minpoly K f ≠ 0 := minpoly.ne_zero f.is_integral
      convert (minpoly K f).root_set_finite K
      ext μ
      have : μ ∈ { μ : K | f.eigenspace μ = ⊥ → False } ↔ ¬f.eigenspace μ = ⊥ := by
        tauto
      convert rfl.mpr this
      simp [← Polynomial.root_set_def, ← Polynomial.mem_roots h, has_eigenvalue_iff_is_root, ← has_eigenvalue])

end minpoly

/-- Every linear operator on a vector space over an algebraically closed field has
    an eigenvalue. -/
-- This is Lemma 5.21 of [axler2015], although we are no longer following that proof.
theorem exists_eigenvalue [IsAlgClosed K] [FiniteDimensional K V] [Nontrivial V] (f : End K V) :
    ∃ c : K, f.HasEigenvalue c := by
  simp_rw [has_eigenvalue_iff_mem_spectrum]
  exact Spectrum.nonempty_of_is_alg_closed_of_finite_dimensional K f

noncomputable instance [IsAlgClosed K] [FiniteDimensional K V] [Nontrivial V] (f : End K V) : Inhabited f.Eigenvalues :=
  ⟨⟨f.exists_eigenvalue.some, f.exists_eigenvalue.some_spec⟩⟩

/-- The eigenspaces of a linear operator form an independent family of subspaces of `V`.  That is,
any eigenspace has trivial intersection with the span of all the other eigenspaces. -/
theorem eigenspaces_independent (f : End K V) : CompleteLattice.Independent f.eigenspace := by
  classical
  -- Define an operation from `Π₀ μ : K, f.eigenspace μ`, the vector space of of finitely-supported
  -- choices of an eigenvector from each eigenspace, to `V`, by sending a collection to its sum.
  let S :
    @LinearMap K K _ _ (RingHom.id K) (Π₀ μ : K, f.eigenspace μ) V
      (@Dfinsupp.addCommMonoid K (fun μ => f.eigenspace μ) _) _ (@Dfinsupp.module K _ (fun μ => f.eigenspace μ) _ _ _)
      _ :=
    @Dfinsupp.lsum K K ℕ _ V _ _ _ _ _ _ _ _ _ fun μ => (f.eigenspace μ).Subtype
  -- We need to show that if a finitely-supported collection `l` of representatives of the
  -- eigenspaces has sum `0`, then it itself is zero.
  suffices ∀ l : Π₀ μ, f.eigenspace μ, S l = 0 → l = 0 by
    rw [CompleteLattice.independent_iff_dfinsupp_lsum_injective]
    change Function.Injective S
    rw [← @LinearMap.ker_eq_bot K K (Π₀ μ, f.eigenspace μ) V _ _ (@Dfinsupp.addCommGroup K (fun μ => f.eigenspace μ) _)]
    rw [eq_bot_iff]
    exact this
  intro l hl
  -- We apply induction on the finite set of eigenvalues from which `l` selects a nonzero
  -- eigenvector, i.e. on the support of `l`.
  induction' h_l_support : l.support using Finset.induction with μ₀ l_support' hμ₀ ih generalizing l
  -- If the support is empty, all coefficients are zero and we are done.
  · exact Dfinsupp.support_eq_empty.1 h_l_support
    
  -- Now assume that the support of `l` contains at least one eigenvalue `μ₀`. We define a new
  -- collection of representatives `l'` to apply the induction hypothesis on later. The collection
  -- of representatives `l'` is derived from `l` by multiplying the coefficient of the eigenvector
  -- with eigenvalue `μ` by `μ - μ₀`.
  · let l' := Dfinsupp.mapRange.linearMap (fun μ => (μ - μ₀) • @LinearMap.id K (f.eigenspace μ) _ _ _) l
    -- The support of `l'` is the support of `l` without `μ₀`.
    have h_l_support' : l'.support = l_support' := by
      rw [← Finset.erase_insert hμ₀, ← h_l_support]
      ext a
      have : ¬(a = μ₀ ∨ l a = 0) ↔ ¬a = μ₀ ∧ ¬l a = 0 := not_or_distrib
      simp only [← l', ← Dfinsupp.mapRange.linear_map_apply, ← Dfinsupp.map_range_apply, ← Dfinsupp.mem_support_iff, ←
        Finset.mem_erase, ← id.def, ← LinearMap.id_coe, ← LinearMap.smul_apply, ← Ne.def, ← smul_eq_zero, ← sub_eq_zero,
        ← this]
    -- The entries of `l'` add up to `0`.
    have total_l' : S l' = 0 := by
      let g := f - algebraMap K (End K V) μ₀
      let a : Π₀ μ : K, V := Dfinsupp.mapRange.linearMap (fun μ => (f.eigenspace μ).Subtype) l
      calc S l' = Dfinsupp.lsum ℕ (fun μ => (f.eigenspace μ).Subtype.comp ((μ - μ₀) • LinearMap.id)) l :=
          _ _ = Dfinsupp.lsum ℕ (fun μ => g.comp (f.eigenspace μ).Subtype) l := _ _ = Dfinsupp.lsum ℕ (fun μ => g) a :=
          _ _ = g (Dfinsupp.lsum ℕ (fun μ => (LinearMap.id : V →ₗ[K] V)) a) := _ _ = g (S l) := _ _ = 0 := by
          rw [hl, g.map_zero]
      · exact Dfinsupp.sum_map_range_index.linear_map
        
      · congr
        ext μ v
        simp only [← g, ← eq_self_iff_true, ← Function.comp_app, ← id.def, ← LinearMap.coe_comp, ← LinearMap.id_coe, ←
          LinearMap.smul_apply, ← LinearMap.sub_apply, ← Module.algebra_map_End_apply, ← sub_left_inj, ← sub_smul, ←
          Submodule.coe_smul_of_tower, ← Submodule.coe_sub, ← Submodule.subtype_apply, ← mem_eigenspace_iff.1 v.prop]
        
      · rw [Dfinsupp.sum_map_range_index.linear_map]
        
      · simp only [← Dfinsupp.sum_add_hom_apply, ← LinearMap.id_coe, ← LinearMap.map_dfinsupp_sum, ← id.def, ←
          LinearMap.to_add_monoid_hom_coe, ← Dfinsupp.lsum_apply_apply]
        
      · congr
        simp only [← S, ← a, ← Dfinsupp.sum_map_range_index.linear_map, ← LinearMap.id_comp]
        
    -- Therefore, by the induction hypothesis, all entries of `l'` are zero.
    have l'_eq_0 := ih l' total_l' h_l_support'
    -- By the definition of `l'`, this means that `(μ - μ₀) • l μ = 0` for all `μ`.
    have h_smul_eq_0 : ∀ μ, (μ - μ₀) • l μ = 0 := by
      intro μ
      calc (μ - μ₀) • l μ = l' μ := by
          simp only [← l', ← LinearMap.id_coe, ← id.def, ← LinearMap.smul_apply, ← Dfinsupp.map_range_apply, ←
            Dfinsupp.mapRange.linear_map_apply]_ = 0 :=
          by
          rw [l'_eq_0]
          rfl
    -- Thus, the eigenspace-representatives in `l` for all `μ ≠ μ₀` are `0`.
    have h_lμ_eq_0 : ∀ μ : K, μ ≠ μ₀ → l μ = 0 := by
      intro μ hμ
      apply or_iff_not_imp_left.1 (smul_eq_zero.1 (h_smul_eq_0 μ))
      rwa [sub_eq_zero]
    -- So if we sum over all these representatives, we obtain `0`.
    have h_sum_l_support'_eq_0 : (Finset.sum l_support' fun μ => (l μ : V)) = 0 := by
      rw [← Finset.sum_const_zero]
      apply Finset.sum_congr rfl
      intro μ hμ
      rw [Submodule.coe_eq_zero, h_lμ_eq_0]
      rintro rfl
      exact hμ₀ hμ
    -- The only potentially nonzero eigenspace-representative in `l` is the one corresponding to
    -- `μ₀`. But since the overall sum is `0` by assumption, this representative must also be `0`.
    have : l μ₀ = 0 := by
      simp only [← S, ← Dfinsupp.lsum_apply_apply, ← Dfinsupp.sum_add_hom_apply, ← LinearMap.to_add_monoid_hom_coe, ←
        Dfinsupp.sum, ← h_l_support, ← Submodule.subtype_apply, ← Submodule.coe_eq_zero, ← Finset.sum_insert hμ₀, ←
        h_sum_l_support'_eq_0, ← add_zeroₓ] at hl
      exact hl
    -- Thus, all coefficients in `l` are `0`.
    show l = 0
    · ext μ
      by_cases' h_cases : μ = μ₀
      · rwa [h_cases, SetLike.coe_eq_coe, Dfinsupp.coe_zero, Pi.zero_apply]
        
      exact congr_arg (coe : _ → V) (h_lμ_eq_0 μ h_cases)
      
    

/-- Eigenvectors corresponding to distinct eigenvalues of a linear operator are linearly
    independent. (Lemma 5.10 of [axler2015])

    We use the eigenvalues as indexing set to ensure that there is only one eigenvector for each
    eigenvalue in the image of `xs`. -/
theorem eigenvectors_linear_independent (f : End K V) (μs : Set K) (xs : μs → V)
    (h_eigenvec : ∀ μ : μs, f.HasEigenvector μ (xs μ)) : LinearIndependent K xs :=
  CompleteLattice.Independent.linear_independent _ (f.eigenspaces_independent.comp Subtype.coe_injective)
    (fun μ => (h_eigenvec μ).1) fun μ => (h_eigenvec μ).2

/-- The generalized eigenspace for a linear map `f`, a scalar `μ`, and an exponent `k ∈ ℕ` is the
kernel of `(f - μ • id) ^ k`. (Def 8.10 of [axler2015]). Furthermore, a generalized eigenspace for
some exponent `k` is contained in the generalized eigenspace for exponents larger than `k`. -/
def generalizedEigenspace (f : End R M) (μ : R) : ℕ →o Submodule R M where
  toFun := fun k => ((f - algebraMap R (End R M) μ) ^ k).ker
  monotone' := fun k m hm => by
    simp only [pow_sub_mul_pow _ hm]
    exact LinearMap.ker_le_ker_comp ((f - algebraMap R (End R M) μ) ^ k) ((f - algebraMap R (End R M) μ) ^ (m - k))

@[simp]
theorem mem_generalized_eigenspace (f : End R M) (μ : R) (k : ℕ) (m : M) :
    m ∈ f.generalizedEigenspace μ k ↔ ((f - μ • 1) ^ k) m = 0 :=
  Iff.rfl

@[simp]
theorem generalized_eigenspace_zero (f : End R M) (k : ℕ) : f.generalizedEigenspace 0 k = (f ^ k).ker := by
  simp [← Module.End.generalizedEigenspace]

/-- A nonzero element of a generalized eigenspace is a generalized eigenvector.
    (Def 8.9 of [axler2015])-/
def HasGeneralizedEigenvector (f : End R M) (μ : R) (k : ℕ) (x : M) : Prop :=
  x ≠ 0 ∧ x ∈ generalizedEigenspace f μ k

/-- A scalar `μ` is a generalized eigenvalue for a linear map `f` and an exponent `k ∈ ℕ` if there
    are generalized eigenvectors for `f`, `k`, and `μ`. -/
def HasGeneralizedEigenvalue (f : End R M) (μ : R) (k : ℕ) : Prop :=
  generalizedEigenspace f μ k ≠ ⊥

/-- The generalized eigenrange for a linear map `f`, a scalar `μ`, and an exponent `k ∈ ℕ` is the
    range of `(f - μ • id) ^ k`. -/
def generalizedEigenrange (f : End R M) (μ : R) (k : ℕ) : Submodule R M :=
  ((f - algebraMap R (End R M) μ) ^ k).range

/-- The exponent of a generalized eigenvalue is never 0. -/
theorem exp_ne_zero_of_has_generalized_eigenvalue {f : End R M} {μ : R} {k : ℕ} (h : f.HasGeneralizedEigenvalue μ k) :
    k ≠ 0 := by
  rintro rfl
  exact h LinearMap.ker_id

/-- The union of the kernels of `(f - μ • id) ^ k` over all `k`. -/
def maximalGeneralizedEigenspace (f : End R M) (μ : R) : Submodule R M :=
  ⨆ k, f.generalizedEigenspace μ k

theorem generalized_eigenspace_le_maximal (f : End R M) (μ : R) (k : ℕ) :
    f.generalizedEigenspace μ k ≤ f.maximalGeneralizedEigenspace μ :=
  le_supr _ _

@[simp]
theorem mem_maximal_generalized_eigenspace (f : End R M) (μ : R) (m : M) :
    m ∈ f.maximalGeneralizedEigenspace μ ↔ ∃ k : ℕ, ((f - μ • 1) ^ k) m = 0 := by
  simp only [← maximal_generalized_eigenspace, mem_generalized_eigenspace, ← Submodule.mem_supr_of_chain]

/-- If there exists a natural number `k` such that the kernel of `(f - μ • id) ^ k` is the
maximal generalized eigenspace, then this value is the least such `k`. If not, this value is not
meaningful. -/
noncomputable def maximalGeneralizedEigenspaceIndex (f : End R M) (μ : R) :=
  monotonicSequenceLimitIndex (f.generalizedEigenspace μ)

/-- For an endomorphism of a Noetherian module, the maximal eigenspace is always of the form kernel
`(f - μ • id) ^ k` for some `k`. -/
theorem maximal_generalized_eigenspace_eq [h : IsNoetherian R M] (f : End R M) (μ : R) :
    maximalGeneralizedEigenspace f μ = f.generalizedEigenspace μ (maximalGeneralizedEigenspaceIndex f μ) := by
  rw [is_noetherian_iff_well_founded] at h
  exact (WellFounded.supr_eq_monotonic_sequence_limit h (f.generalized_eigenspace μ) : _)

/-- A generalized eigenvalue for some exponent `k` is also
    a generalized eigenvalue for exponents larger than `k`. -/
theorem has_generalized_eigenvalue_of_has_generalized_eigenvalue_of_le {f : End R M} {μ : R} {k : ℕ} {m : ℕ}
    (hm : k ≤ m) (hk : f.HasGeneralizedEigenvalue μ k) : f.HasGeneralizedEigenvalue μ m := by
  unfold has_generalized_eigenvalue  at *
  contrapose! hk
  rw [← le_bot_iff, ← hk]
  exact (f.generalized_eigenspace μ).Monotone hm

/-- The eigenspace is a subspace of the generalized eigenspace. -/
theorem eigenspace_le_generalized_eigenspace {f : End R M} {μ : R} {k : ℕ} (hk : 0 < k) :
    f.eigenspace μ ≤ f.generalizedEigenspace μ k :=
  (f.generalizedEigenspace μ).Monotone (Nat.succ_le_of_ltₓ hk)

/-- All eigenvalues are generalized eigenvalues. -/
theorem has_generalized_eigenvalue_of_has_eigenvalue {f : End R M} {μ : R} {k : ℕ} (hk : 0 < k)
    (hμ : f.HasEigenvalue μ) : f.HasGeneralizedEigenvalue μ k := by
  apply has_generalized_eigenvalue_of_has_generalized_eigenvalue_of_le hk
  rw [has_generalized_eigenvalue, generalized_eigenspace, OrderHom.coe_fun_mk, pow_oneₓ]
  exact hμ

/-- All generalized eigenvalues are eigenvalues. -/
theorem has_eigenvalue_of_has_generalized_eigenvalue {f : End R M} {μ : R} {k : ℕ}
    (hμ : f.HasGeneralizedEigenvalue μ k) : f.HasEigenvalue μ := by
  intro contra
  apply hμ
  erw [LinearMap.ker_eq_bot] at contra⊢
  rw [LinearMap.coe_pow]
  exact Function.Injective.iterate contra k

/-- Generalized eigenvalues are actually just eigenvalues. -/
@[simp]
theorem has_generalized_eigenvalue_iff_has_eigenvalue {f : End R M} {μ : R} {k : ℕ} (hk : 0 < k) :
    f.HasGeneralizedEigenvalue μ k ↔ f.HasEigenvalue μ :=
  ⟨has_eigenvalue_of_has_generalized_eigenvalue, has_generalized_eigenvalue_of_has_eigenvalue hk⟩

/-- Every generalized eigenvector is a generalized eigenvector for exponent `finrank K V`.
    (Lemma 8.11 of [axler2015]) -/
theorem generalized_eigenspace_le_generalized_eigenspace_finrank [FiniteDimensional K V] (f : End K V) (μ : K) (k : ℕ) :
    f.generalizedEigenspace μ k ≤ f.generalizedEigenspace μ (finrank K V) :=
  ker_pow_le_ker_pow_finrank _ _

/-- Generalized eigenspaces for exponents at least `finrank K V` are equal to each other. -/
theorem generalized_eigenspace_eq_generalized_eigenspace_finrank_of_le [FiniteDimensional K V] (f : End K V) (μ : K)
    {k : ℕ} (hk : finrank K V ≤ k) : f.generalizedEigenspace μ k = f.generalizedEigenspace μ (finrank K V) :=
  ker_pow_eq_ker_pow_finrank_of_le hk

/-- If `f` maps a subspace `p` into itself, then the generalized eigenspace of the restriction
    of `f` to `p` is the part of the generalized eigenspace of `f` that lies in `p`. -/
theorem generalized_eigenspace_restrict (f : End R M) (p : Submodule R M) (k : ℕ) (μ : R)
    (hfp : ∀ x : M, x ∈ p → f x ∈ p) :
    generalizedEigenspace (LinearMap.restrict f hfp) μ k = Submodule.comap p.Subtype (f.generalizedEigenspace μ k) := by
  simp only [← generalized_eigenspace, ← OrderHom.coe_fun_mk, LinearMap.ker_comp]
  induction' k with k ih
  · rw [pow_zeroₓ, pow_zeroₓ, LinearMap.one_eq_id]
    apply (Submodule.ker_subtype _).symm
    
  · erw [pow_succ'ₓ, pow_succ'ₓ, LinearMap.ker_comp, LinearMap.ker_comp, ih, ← LinearMap.ker_comp, LinearMap.comp_assoc]
    

/-- If `p` is an invariant submodule of an endomorphism `f`, then the `μ`-eigenspace of the
restriction of `f` to `p` is a submodule of the `μ`-eigenspace of `f`. -/
theorem eigenspace_restrict_le_eigenspace (f : End R M) {p : Submodule R M} (hfp : ∀, ∀ x ∈ p, ∀, f x ∈ p) (μ : R) :
    (eigenspace (f.restrict hfp) μ).map p.Subtype ≤ f.eigenspace μ := by
  rintro a ⟨x, hx, rfl⟩
  simp only [← SetLike.mem_coe, ← mem_eigenspace_iff, ← LinearMap.restrict_apply] at hx⊢
  exact congr_arg coe hx

/-- Generalized eigenrange and generalized eigenspace for exponent `finrank K V` are disjoint. -/
theorem generalized_eigenvec_disjoint_range_ker [FiniteDimensional K V] (f : End K V) (μ : K) :
    Disjoint (f.generalizedEigenrange μ (finrank K V)) (f.generalizedEigenspace μ (finrank K V)) := by
  have h :=
    calc
      Submodule.comap ((f - algebraMap _ _ μ) ^ finrank K V) (f.generalized_eigenspace μ (finrank K V)) =
          ((f - algebraMap _ _ μ) ^ finrank K V * (f - algebraMap K (End K V) μ) ^ finrank K V).ker :=
        by
        simpa only [← generalized_eigenspace, ← OrderHom.coe_fun_mk, LinearMap.ker_comp]
      _ = f.generalized_eigenspace μ (finrank K V + finrank K V) := by
        rw [← pow_addₓ]
        rfl
      _ = f.generalized_eigenspace μ (finrank K V) := by
        rw [generalized_eigenspace_eq_generalized_eigenspace_finrank_of_le]
        linarith
      
  rw [Disjoint, generalized_eigenrange, LinearMap.range_eq_map, Submodule.map_inf_eq_map_inf_comap, top_inf_eq, h]
  apply Submodule.map_comap_le

/-- If an invariant subspace `p` of an endomorphism `f` is disjoint from the `μ`-eigenspace of `f`,
then the restriction of `f` to `p` has trivial `μ`-eigenspace. -/
theorem eigenspace_restrict_eq_bot {f : End R M} {p : Submodule R M} (hfp : ∀, ∀ x ∈ p, ∀, f x ∈ p) {μ : R}
    (hμp : Disjoint (f.eigenspace μ) p) : eigenspace (f.restrict hfp) μ = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  simpa using hμp ⟨eigenspace_restrict_le_eigenspace f hfp μ ⟨x, hx, rfl⟩, x.prop⟩

/-- The generalized eigenspace of an eigenvalue has positive dimension for positive exponents. -/
theorem pos_finrank_generalized_eigenspace_of_has_eigenvalue [FiniteDimensional K V] {f : End K V} {k : ℕ} {μ : K}
    (hx : f.HasEigenvalue μ) (hk : 0 < k) : 0 < finrank K (f.generalizedEigenspace μ k) :=
  calc
    0 = finrank K (⊥ : Submodule K V) := by
      rw [finrank_bot]
    _ < finrank K (f.eigenspace μ) := Submodule.finrank_lt_finrank_of_lt (bot_lt_iff_ne_bot.2 hx)
    _ ≤ finrank K (f.generalizedEigenspace μ k) :=
      Submodule.finrank_mono ((f.generalizedEigenspace μ).Monotone (Nat.succ_le_of_ltₓ hk))
    

/-- A linear map maps a generalized eigenrange into itself. -/
theorem map_generalized_eigenrange_le {f : End K V} {μ : K} {n : ℕ} :
    Submodule.map f (f.generalizedEigenrange μ n) ≤ f.generalizedEigenrange μ n :=
  calc
    Submodule.map f (f.generalizedEigenrange μ n) = (f * (f - algebraMap _ _ μ) ^ n).range :=
      (LinearMap.range_comp _ _).symm
    _ = ((f - algebraMap _ _ μ) ^ n * f).range := by
      rw [Algebra.mul_sub_algebra_map_pow_commutes]
    _ = Submodule.map ((f - algebraMap _ _ μ) ^ n) f.range := LinearMap.range_comp _ _
    _ ≤ f.generalizedEigenrange μ n := LinearMap.map_le_range
    

/-- The generalized eigenvectors span the entire vector space (Lemma 8.21 of [axler2015]). -/
theorem supr_generalized_eigenspace_eq_top [IsAlgClosed K] [FiniteDimensional K V] (f : End K V) :
    (⨆ (μ : K) (k : ℕ), f.generalizedEigenspace μ k) = ⊤ := by
  -- We prove the claim by strong induction on the dimension of the vector space.
  induction' h_dim : finrank K V using Nat.strong_induction_onₓ with n ih generalizing V
  cases n
  -- If the vector space is 0-dimensional, the result is trivial.
  · rw [← top_le_iff]
    simp only [← finrank_eq_zero.1 (Eq.trans finrank_top h_dim), ← bot_le]
    
  -- Otherwise the vector space is nontrivial.
  · have : Nontrivial V :=
      finrank_pos_iff.1
        (by
          rw [h_dim]
          apply Nat.zero_lt_succₓ)
    -- Hence, `f` has an eigenvalue `μ₀`.
    obtain ⟨μ₀, hμ₀⟩ : ∃ μ₀, f.has_eigenvalue μ₀ := exists_eigenvalue f
    -- We define `ES` to be the generalized eigenspace
    let ES := f.generalized_eigenspace μ₀ (finrank K V)
    -- and `ER` to be the generalized eigenrange.
    let ER := f.generalized_eigenrange μ₀ (finrank K V)
    -- `f` maps `ER` into itself.
    have h_f_ER : ∀ x : V, x ∈ ER → f x ∈ ER := fun x hx => map_generalized_eigenrange_le (Submodule.mem_map_of_mem hx)
    -- Therefore, we can define the restriction `f'` of `f` to `ER`.
    let f' : End K ER := f.restrict h_f_ER
    -- The dimension of `ES` is positive
    have h_dim_ES_pos : 0 < finrank K ES := by
      dsimp' only [← ES]
      rw [h_dim]
      apply pos_finrank_generalized_eigenspace_of_has_eigenvalue hμ₀ (Nat.zero_lt_succₓ n)
    -- and the dimensions of `ES` and `ER` add up to `finrank K V`.
    have h_dim_add : finrank K ER + finrank K ES = finrank K V := by
      apply LinearMap.finrank_range_add_finrank_ker
    -- Therefore the dimension `ER` mus be smaller than `finrank K V`.
    have h_dim_ER : finrank K ER < n.succ := by
      linarith
    -- This allows us to apply the induction hypothesis on `ER`:
    have ih_ER : (⨆ (μ : K) (k : ℕ), f'.generalized_eigenspace μ k) = ⊤ := ih (finrank K ER) h_dim_ER f' rfl
    -- The induction hypothesis gives us a statement about subspaces of `ER`. We can transfer this
    -- to a statement about subspaces of `V` via `submodule.subtype`:
    have ih_ER' : (⨆ (μ : K) (k : ℕ), (f'.generalized_eigenspace μ k).map ER.subtype) = ER := by
      simp only [← (Submodule.map_supr _ _).symm, ← ih_ER, ← Submodule.map_subtype_top ER]
    -- Moreover, every generalized eigenspace of `f'` is contained in the corresponding generalized
    -- eigenspace of `f`.
    have hff' : ∀ μ k, (f'.generalized_eigenspace μ k).map ER.subtype ≤ f.generalized_eigenspace μ k := by
      intros
      rw [generalized_eigenspace_restrict]
      apply Submodule.map_comap_le
    -- It follows that `ER` is contained in the span of all generalized eigenvectors.
    have hER : ER ≤ ⨆ (μ : K) (k : ℕ), f.generalized_eigenspace μ k := by
      rw [← ih_ER']
      exact supr₂_mono hff'
    -- `ES` is contained in this span by definition.
    have hES : ES ≤ ⨆ (μ : K) (k : ℕ), f.generalized_eigenspace μ k :=
      le_transₓ (le_supr (fun k => f.generalized_eigenspace μ₀ k) (finrank K V))
        (le_supr (fun μ : K => ⨆ k : ℕ, f.generalized_eigenspace μ k) μ₀)
    -- Moreover, we know that `ER` and `ES` are disjoint.
    have h_disjoint : Disjoint ER ES := generalized_eigenvec_disjoint_range_ker f μ₀
    -- Since the dimensions of `ER` and `ES` add up to the dimension of `V`, it follows that the
    -- span of all generalized eigenvectors is all of `V`.
    show (⨆ (μ : K) (k : ℕ), f.generalized_eigenspace μ k) = ⊤
    · rw [← top_le_iff, ← Submodule.eq_top_of_disjoint ER ES h_dim_add h_disjoint]
      apply sup_le hER hES
      
    

end End

end Module

