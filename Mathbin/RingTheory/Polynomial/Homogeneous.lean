/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Eric Wieser
-/
import Mathbin.Algebra.DirectSum.Internal
import Mathbin.Algebra.GradedMonoid
import Mathbin.Data.Fintype.Card
import Mathbin.Data.MvPolynomial.Variables

/-!
# Homogeneous polynomials

A multivariate polynomial `φ` is homogeneous of degree `n`
if all monomials occuring in `φ` have degree `n`.

## Main definitions/lemmas

* `is_homogeneous φ n`: a predicate that asserts that `φ` is homogeneous of degree `n`.
* `homogeneous_submodule σ R n`: the submodule of homogeneous polynomials of degree `n`.
* `homogeneous_component n`: the additive morphism that projects polynomials onto
  their summand that is homogeneous of degree `n`.
* `sum_homogeneous_component`: every polynomial is the sum of its homogeneous components

-/


open BigOperators

namespace MvPolynomial

variable {σ : Type _} {τ : Type _} {R : Type _} {S : Type _}

/-- A multivariate polynomial `φ` is homogeneous of degree `n`
if all monomials occuring in `φ` have degree `n`. -/
/-
TODO
* create definition for `∑ i in d.support, d i`
* show that `mv_polynomial σ R ≃ₐ[R] ⨁ i, homogeneous_submodule σ R i`
-/
def IsHomogeneous [CommSemiringₓ R] (φ : MvPolynomial σ R) (n : ℕ) :=
  ∀ ⦃d⦄, coeff d φ ≠ 0 → (∑ i in d.support, d i) = n

variable (σ R)

/-- The submodule of homogeneous `mv_polynomial`s of degree `n`. -/
def homogeneousSubmodule [CommSemiringₓ R] (n : ℕ) : Submodule R (MvPolynomial σ R) where
  Carrier := { x | x.IsHomogeneous n }
  smul_mem' := fun r a ha c hc => by
    rw [coeff_smul] at hc
    apply ha
    intro h
    apply hc
    rw [h]
    exact smul_zero r
  zero_mem' := fun d hd => False.elim (hd <| coeff_zero _)
  add_mem' := fun a b ha hb c hc => by
    rw [coeff_add] at hc
    obtain h | h : coeff c a ≠ 0 ∨ coeff c b ≠ 0 := by
      contrapose! hc
      simp only [← hc, ← add_zeroₓ]
    · exact ha h
      
    · exact hb h
      

variable {σ R}

@[simp]
theorem mem_homogeneous_submodule [CommSemiringₓ R] (n : ℕ) (p : MvPolynomial σ R) :
    p ∈ homogeneousSubmodule σ R n ↔ p.IsHomogeneous n :=
  Iff.rfl

variable (σ R)

/-- While equal, the former has a convenient definitional reduction. -/
theorem homogeneous_submodule_eq_finsupp_supported [CommSemiringₓ R] (n : ℕ) :
    homogeneousSubmodule σ R n = Finsupp.supported _ R { d | (∑ i in d.support, d i) = n } := by
  ext
  rw [Finsupp.mem_supported, Set.subset_def]
  simp only [← Finsupp.mem_support_iff, ← Finset.mem_coe]
  rfl

variable {σ R}

theorem homogeneous_submodule_mul [CommSemiringₓ R] (m n : ℕ) :
    homogeneousSubmodule σ R m * homogeneousSubmodule σ R n ≤ homogeneousSubmodule σ R (m + n) := by
  rw [Submodule.mul_le]
  intro φ hφ ψ hψ c hc
  rw [coeff_mul] at hc
  obtain ⟨⟨d, e⟩, hde, H⟩ := Finset.exists_ne_zero_of_sum_ne_zero hc
  have aux : coeff d φ ≠ 0 ∧ coeff e ψ ≠ 0 := by
    contrapose! H
    by_cases' h : coeff d φ = 0 <;> simp_all only [← Ne.def, ← not_false_iff, ← zero_mul, ← mul_zero]
  specialize hφ aux.1
  specialize hψ aux.2
  rw [Finsupp.mem_antidiagonal] at hde
  classical
  have hd' : d.support ⊆ d.support ∪ e.support := Finset.subset_union_left _ _
  have he' : e.support ⊆ d.support ∪ e.support := Finset.subset_union_right _ _
  rw [← hde, ← hφ, ← hψ, Finset.sum_subset Finsupp.support_add, Finset.sum_subset hd', Finset.sum_subset he', ←
    Finset.sum_add_distrib]
  · congr
    
  all_goals
    intro i hi
    apply finsupp.not_mem_support_iff.mp

section

variable [CommSemiringₓ R]

variable {σ R}

theorem is_homogeneous_monomial (d : σ →₀ ℕ) (r : R) (n : ℕ) (hn : (∑ i in d.support, d i) = n) :
    IsHomogeneous (monomial d r) n := by
  intro c hc
  classical
  rw [coeff_monomial] at hc
  split_ifs  at hc with h
  · subst c
    exact hn
    
  · contradiction
    

variable (σ) {R}

theorem is_homogeneous_of_total_degree_zero {p : MvPolynomial σ R} (hp : p.totalDegree = 0) : IsHomogeneous p 0 := by
  erw [total_degree, Finset.sup_eq_bot_iff] at hp
  -- we have to do this in two steps to stop simp changing bot to zero
  simp_rw [mem_support_iff] at hp
  exact hp

theorem is_homogeneous_C (r : R) : IsHomogeneous (c r : MvPolynomial σ R) 0 := by
  apply is_homogeneous_monomial
  simp only [← Finsupp.zero_apply, ← Finset.sum_const_zero]

variable (σ R)

theorem is_homogeneous_zero (n : ℕ) : IsHomogeneous (0 : MvPolynomial σ R) n :=
  (homogeneousSubmodule σ R n).zero_mem

theorem is_homogeneous_one : IsHomogeneous (1 : MvPolynomial σ R) 0 :=
  is_homogeneous_C _ _

variable {σ} (R)

theorem is_homogeneous_X (i : σ) : IsHomogeneous (x i : MvPolynomial σ R) 1 := by
  apply is_homogeneous_monomial
  simp only [← Finsupp.support_single_ne_zero _ one_ne_zero, ← Finset.sum_singleton]
  exact Finsupp.single_eq_same

end

namespace IsHomogeneous

variable [CommSemiringₓ R] {φ ψ : MvPolynomial σ R} {m n : ℕ}

theorem coeff_eq_zero (hφ : IsHomogeneous φ n) (d : σ →₀ ℕ) (hd : (∑ i in d.support, d i) ≠ n) : coeff d φ = 0 := by
  have aux := mt (@hφ d) hd
  classical
  rwa [not_not] at aux

theorem inj_right (hm : IsHomogeneous φ m) (hn : IsHomogeneous φ n) (hφ : φ ≠ 0) : m = n := by
  obtain ⟨d, hd⟩ : ∃ d, coeff d φ ≠ 0 := exists_coeff_ne_zero hφ
  rw [← hm hd, ← hn hd]

theorem add (hφ : IsHomogeneous φ n) (hψ : IsHomogeneous ψ n) : IsHomogeneous (φ + ψ) n :=
  (homogeneousSubmodule σ R n).add_mem hφ hψ

theorem sum {ι : Type _} (s : Finset ι) (φ : ι → MvPolynomial σ R) (n : ℕ) (h : ∀, ∀ i ∈ s, ∀, IsHomogeneous (φ i) n) :
    IsHomogeneous (∑ i in s, φ i) n :=
  (homogeneousSubmodule σ R n).sum_mem h

theorem mul (hφ : IsHomogeneous φ m) (hψ : IsHomogeneous ψ n) : IsHomogeneous (φ * ψ) (m + n) :=
  homogeneous_submodule_mul m n <| Submodule.mul_mem_mul hφ hψ

theorem prod {ι : Type _} (s : Finset ι) (φ : ι → MvPolynomial σ R) (n : ι → ℕ)
    (h : ∀, ∀ i ∈ s, ∀, IsHomogeneous (φ i) (n i)) : IsHomogeneous (∏ i in s, φ i) (∑ i in s, n i) := by
  classical
  revert h
  apply Finset.induction_on s
  · intro
    simp only [← is_homogeneous_one, ← Finset.sum_empty, ← Finset.prod_empty]
    
  · intro i s his IH h
    simp only [← his, ← Finset.prod_insert, ← Finset.sum_insert, ← not_false_iff]
    apply (h i (Finset.mem_insert_self _ _)).mul (IH _)
    intro j hjs
    exact h j (Finset.mem_insert_of_mem hjs)
    

theorem total_degree (hφ : IsHomogeneous φ n) (h : φ ≠ 0) : totalDegree φ = n := by
  rw [total_degree]
  apply le_antisymmₓ
  · apply Finset.sup_le
    intro d hd
    rw [mem_support_iff] at hd
    rw [Finsupp.sum, hφ hd]
    
  · obtain ⟨d, hd⟩ : ∃ d, coeff d φ ≠ 0 := exists_coeff_ne_zero h
    simp only [hφ hd, ← Finsupp.sum]
    replace hd := finsupp.mem_support_iff.mpr hd
    exact Finset.le_sup hd
    

/-- The homogeneous submodules form a graded ring. This instance is used by `direct_sum.comm_semiring`
and `direct_sum.algebra`. -/
instance HomogeneousSubmodule.gcomm_semiring : SetLike.GradedMonoid (homogeneousSubmodule σ R) where
  one_mem := is_homogeneous_one σ R
  mul_mem := fun i j xi xj => IsHomogeneous.mul

open DirectSum

noncomputable example : CommSemiringₓ (⨁ i, homogeneousSubmodule σ R i) :=
  inferInstance

noncomputable example : Algebra R (⨁ i, homogeneousSubmodule σ R i) :=
  inferInstance

end IsHomogeneous

section

noncomputable section

open Classical

open Finset

/-- `homogeneous_component n φ` is the part of `φ` that is homogeneous of degree `n`.
See `sum_homogeneous_component` for the statement that `φ` is equal to the sum
of all its homogeneous components. -/
def homogeneousComponent [CommSemiringₓ R] (n : ℕ) : MvPolynomial σ R →ₗ[R] MvPolynomial σ R :=
  (Submodule.subtype _).comp <| Finsupp.restrictDom _ _ { d | (∑ i in d.support, d i) = n }

section HomogeneousComponent

open Finset

variable [CommSemiringₓ R] (n : ℕ) (φ ψ : MvPolynomial σ R)

theorem coeff_homogeneous_component (d : σ →₀ ℕ) :
    coeff d (homogeneousComponent n φ) = if (∑ i in d.support, d i) = n then coeff d φ else 0 := by
  convert Finsupp.filter_apply (fun d : σ →₀ ℕ => (∑ i in d.support, d i) = n) φ d

theorem homogeneous_component_apply :
    homogeneousComponent n φ = ∑ d in φ.support.filter fun d => (∑ i in d.support, d i) = n, monomial d (coeff d φ) :=
  by
  convert Finsupp.filter_eq_sum (fun d : σ →₀ ℕ => (∑ i in d.support, d i) = n) φ

theorem homogeneous_component_is_homogeneous : (homogeneousComponent n φ).IsHomogeneous n := by
  intro d hd
  contrapose! hd
  rw [coeff_homogeneous_component, if_neg hd]

@[simp]
theorem homogeneous_component_zero : homogeneousComponent 0 φ = c (coeff 0 φ) := by
  ext1 d
  rcases em (d = 0) with (rfl | hd)
  · simp only [← coeff_homogeneous_component, ← sum_eq_zero_iff, ← Finsupp.zero_apply, ← if_true, ← coeff_C, ←
      eq_self_iff_true, ← forall_true_iff]
    
  · rw [coeff_homogeneous_component, if_neg, coeff_C, if_neg (Ne.symm hd)]
    simp only [← Finsupp.ext_iff, ← Finsupp.zero_apply] at hd
    simp [← hd]
    

@[simp]
theorem homogeneous_component_C_mul (n : ℕ) (r : R) :
    homogeneousComponent n (c r * φ) = c r * homogeneousComponent n φ := by
  simp only [← C_mul', ← LinearMap.map_smul]

theorem homogeneous_component_eq_zero' (h : ∀ d : σ →₀ ℕ, d ∈ φ.support → (∑ i in d.support, d i) ≠ n) :
    homogeneousComponent n φ = 0 := by
  rw [homogeneous_component_apply, sum_eq_zero]
  intro d hd
  rw [mem_filter] at hd
  exfalso
  exact h _ hd.1 hd.2

theorem homogeneous_component_eq_zero (h : φ.totalDegree < n) : homogeneousComponent n φ = 0 := by
  apply homogeneous_component_eq_zero'
  rw [total_degree, Finset.sup_lt_iff] at h
  · intro d hd
    exact ne_of_ltₓ (h d hd)
    
  · exact lt_of_le_of_ltₓ (Nat.zero_leₓ _) h
    

theorem sum_homogeneous_component : (∑ i in range (φ.totalDegree + 1), homogeneousComponent i φ) = φ := by
  ext1 d
  suffices φ.total_degree < d.support.sum d → 0 = coeff d φ by
    simpa [← coeff_sum, ← coeff_homogeneous_component]
  exact fun h => (coeff_eq_zero_of_total_degree_lt h).symm

theorem homogeneous_component_homogeneous_polynomial (m n : ℕ) (p : MvPolynomial σ R)
    (h : p ∈ homogeneousSubmodule σ R n) : homogeneousComponent m p = if m = n then p else 0 := by
  simp only [← mem_homogeneous_submodule] at h
  ext x
  rw [coeff_homogeneous_component]
  by_cases' zero_coeff : coeff x p = 0
  · split_ifs
    all_goals
      simp only [← zero_coeff, ← coeff_zero]
    
  · rw [h zero_coeff]
    simp only [← show n = m ↔ m = n from eq_comm]
    split_ifs with h1
    · rfl
      
    · simp only [← coeff_zero]
      
    

end HomogeneousComponent

end

end MvPolynomial

