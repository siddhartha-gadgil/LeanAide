/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kenny Lau
-/
import Mathbin.Algebra.BigOperators.NatAntidiagonal
import Mathbin.Data.Finsupp.Interval
import Mathbin.Data.MvPolynomial.Basic
import Mathbin.Data.Polynomial.AlgebraMap
import Mathbin.Data.Polynomial.Coeff
import Mathbin.LinearAlgebra.StdBasis
import Mathbin.RingTheory.Ideal.LocalRing
import Mathbin.RingTheory.Multiplicity
import Mathbin.Tactic.Linarith.Default

/-!
# Formal power series

This file defines (multivariate) formal power series
and develops the basic properties of these objects.

A formal power series is to a polynomial like an infinite sum is to a finite sum.

We provide the natural inclusion from polynomials to formal power series.

## Generalities

The file starts with setting up the (semi)ring structure on multivariate power series.

`trunc n φ` truncates a formal power series to the polynomial
that has the same coefficients as `φ`, for all `m < n`, and `0` otherwise.

If the constant coefficient of a formal power series is invertible,
then this formal power series is invertible.

Formal power series over a local ring form a local ring.

## Formal power series in one variable

We prove that if the ring of coefficients is an integral domain,
then formal power series in one variable form an integral domain.

The `order` of a formal power series `φ` is the multiplicity of the variable `X` in `φ`.

If the coefficients form an integral domain, then `order` is a valuation
(`order_mul`, `le_order_add`).

## Implementation notes

In this file we define multivariate formal power series with
variables indexed by `σ` and coefficients in `R` as
`mv_power_series σ R := (σ →₀ ℕ) → R`.
Unfortunately there is not yet enough API to show that they are the completion
of the ring of multivariate polynomials. However, we provide most of the infrastructure
that is needed to do this. Once I-adic completion (topological or algebraic) is available
it should not be hard to fill in the details.

Formal power series in one variable are defined as
`power_series R := mv_power_series unit R`.

This allows us to port a lot of proofs and properties
from the multivariate case to the single variable case.
However, it means that formal power series are indexed by `unit →₀ ℕ`,
which is of course canonically isomorphic to `ℕ`.
We then build some glue to treat formal power series as if they are indexed by `ℕ`.
Occasionally this leads to proofs that are uglier than expected.
-/


noncomputable section

open Classical BigOperators Polynomial

/-- Multivariate formal power series, where `σ` is the index set of the variables
and `R` is the coefficient ring.-/
def MvPowerSeries (σ : Type _) (R : Type _) :=
  (σ →₀ ℕ) → R

namespace MvPowerSeries

open Finsupp

variable {σ R : Type _}

instance [Inhabited R] : Inhabited (MvPowerSeries σ R) :=
  ⟨fun _ => default⟩

instance [Zero R] : Zero (MvPowerSeries σ R) :=
  Pi.hasZero

instance [AddMonoidₓ R] : AddMonoidₓ (MvPowerSeries σ R) :=
  Pi.addMonoid

instance [AddGroupₓ R] : AddGroupₓ (MvPowerSeries σ R) :=
  Pi.addGroup

instance [AddCommMonoidₓ R] : AddCommMonoidₓ (MvPowerSeries σ R) :=
  Pi.addCommMonoid

instance [AddCommGroupₓ R] : AddCommGroupₓ (MvPowerSeries σ R) :=
  Pi.addCommGroup

instance [Nontrivial R] : Nontrivial (MvPowerSeries σ R) :=
  Function.nontrivial

instance {A} [Semiringₓ R] [AddCommMonoidₓ A] [Module R A] : Module R (MvPowerSeries σ A) :=
  Pi.module _ _ _

instance {A S} [Semiringₓ R] [Semiringₓ S] [AddCommMonoidₓ A] [Module R A] [Module S A] [HasSmul R S]
    [IsScalarTower R S A] : IsScalarTower R S (MvPowerSeries σ A) :=
  Pi.is_scalar_tower

section Semiringₓ

variable (R) [Semiringₓ R]

/-- The `n`th monomial with coefficient `a` as multivariate formal power series.-/
def monomial (n : σ →₀ ℕ) : R →ₗ[R] MvPowerSeries σ R :=
  LinearMap.stdBasis R _ n

/-- The `n`th coefficient of a multivariate formal power series.-/
def coeff (n : σ →₀ ℕ) : MvPowerSeries σ R →ₗ[R] R :=
  LinearMap.proj n

variable {R}

/-- Two multivariate formal power series are equal if all their coefficients are equal.-/
@[ext]
theorem ext {φ ψ} (h : ∀ n : σ →₀ ℕ, coeff R n φ = coeff R n ψ) : φ = ψ :=
  funext h

/-- Two multivariate formal power series are equal
 if and only if all their coefficients are equal.-/
theorem ext_iff {φ ψ : MvPowerSeries σ R} : φ = ψ ↔ ∀ n : σ →₀ ℕ, coeff R n φ = coeff R n ψ :=
  Function.funext_iffₓ

theorem monomial_def [DecidableEq σ] (n : σ →₀ ℕ) : monomial R n = LinearMap.stdBasis R _ n := by
  convert rfl

-- unify the `decidable` arguments
theorem coeff_monomial [DecidableEq σ] (m n : σ →₀ ℕ) (a : R) : coeff R m (monomial R n a) = if m = n then a else 0 :=
  by
  rw [coeff, monomial_def, LinearMap.proj_apply, LinearMap.std_basis_apply, Function.update_apply, Pi.zero_apply]

@[simp]
theorem coeff_monomial_same (n : σ →₀ ℕ) (a : R) : coeff R n (monomial R n a) = a :=
  LinearMap.std_basis_same R _ n a

theorem coeff_monomial_ne {m n : σ →₀ ℕ} (h : m ≠ n) (a : R) : coeff R m (monomial R n a) = 0 :=
  LinearMap.std_basis_ne R _ _ _ h a

theorem eq_of_coeff_monomial_ne_zero {m n : σ →₀ ℕ} {a : R} (h : coeff R m (monomial R n a) ≠ 0) : m = n :=
  by_contra fun h' => h <| coeff_monomial_ne h' a

@[simp]
theorem coeff_comp_monomial (n : σ →₀ ℕ) : (coeff R n).comp (monomial R n) = LinearMap.id :=
  LinearMap.ext <| coeff_monomial_same n

@[simp]
theorem coeff_zero (n : σ →₀ ℕ) : coeff R n (0 : MvPowerSeries σ R) = 0 :=
  rfl

variable (m n : σ →₀ ℕ) (φ ψ : MvPowerSeries σ R)

instance : One (MvPowerSeries σ R) :=
  ⟨monomial R (0 : σ →₀ ℕ) 1⟩

theorem coeff_one [DecidableEq σ] : coeff R n (1 : MvPowerSeries σ R) = if n = 0 then 1 else 0 :=
  coeff_monomial _ _ _

theorem coeff_zero_one : coeff R (0 : σ →₀ ℕ) 1 = 1 :=
  coeff_monomial_same 0 1

theorem monomial_zero_one : monomial R (0 : σ →₀ ℕ) 1 = 1 :=
  rfl

instance : AddMonoidWithOneₓ (MvPowerSeries σ R) :=
  { MvPowerSeries.addMonoid with natCast := fun n => monomial R 0 n,
    nat_cast_zero := by
      simp [← Nat.castₓ],
    nat_cast_succ := by
      simp [← Nat.castₓ, ← monomial_zero_one],
    one := 1 }

instance : Mul (MvPowerSeries σ R) :=
  ⟨fun φ ψ n => ∑ p in Finsupp.antidiagonal n, coeff R p.1 φ * coeff R p.2 ψ⟩

theorem coeff_mul : coeff R n (φ * ψ) = ∑ p in Finsupp.antidiagonal n, coeff R p.1 φ * coeff R p.2 ψ :=
  rfl

protected theorem zero_mul : (0 : MvPowerSeries σ R) * φ = 0 :=
  ext fun n => by
    simp [← coeff_mul]

protected theorem mul_zero : φ * 0 = 0 :=
  ext fun n => by
    simp [← coeff_mul]

theorem coeff_monomial_mul (a : R) : coeff R m (monomial R n a * φ) = if n ≤ m then a * coeff R (m - n) φ else 0 := by
  have :
    ∀, ∀ p ∈ antidiagonal m, ∀, coeff R (p : (σ →₀ ℕ) × (σ →₀ ℕ)).1 (monomial R n a) * coeff R p.2 φ ≠ 0 → p.1 = n :=
    fun p _ hp => eq_of_coeff_monomial_ne_zero (left_ne_zero_of_mul hp)
  rw [coeff_mul, ← Finset.sum_filter_of_ne this, antidiagonal_filter_fst_eq, Finset.sum_ite_index]
  simp only [← Finset.sum_singleton, ← coeff_monomial_same, ← Finset.sum_empty]

theorem coeff_mul_monomial (a : R) : coeff R m (φ * monomial R n a) = if n ≤ m then coeff R (m - n) φ * a else 0 := by
  have :
    ∀, ∀ p ∈ antidiagonal m, ∀, coeff R (p : (σ →₀ ℕ) × (σ →₀ ℕ)).1 φ * coeff R p.2 (monomial R n a) ≠ 0 → p.2 = n :=
    fun p _ hp => eq_of_coeff_monomial_ne_zero (right_ne_zero_of_mul hp)
  rw [coeff_mul, ← Finset.sum_filter_of_ne this, antidiagonal_filter_snd_eq, Finset.sum_ite_index]
  simp only [← Finset.sum_singleton, ← coeff_monomial_same, ← Finset.sum_empty]

theorem coeff_add_monomial_mul (a : R) : coeff R (m + n) (monomial R m a * φ) = a * coeff R n φ := by
  rw [coeff_monomial_mul, if_pos, add_tsub_cancel_left]
  exact le_add_right le_rfl

theorem coeff_add_mul_monomial (a : R) : coeff R (m + n) (φ * monomial R n a) = coeff R m φ * a := by
  rw [coeff_mul_monomial, if_pos, add_tsub_cancel_right]
  exact le_add_left le_rfl

protected theorem one_mul : (1 : MvPowerSeries σ R) * φ = φ :=
  ext fun n => by
    simpa using coeff_add_monomial_mul 0 n φ 1

protected theorem mul_one : φ * 1 = φ :=
  ext fun n => by
    simpa using coeff_add_mul_monomial n 0 φ 1

protected theorem mul_add (φ₁ φ₂ φ₃ : MvPowerSeries σ R) : φ₁ * (φ₂ + φ₃) = φ₁ * φ₂ + φ₁ * φ₃ :=
  ext fun n => by
    simp only [← coeff_mul, ← mul_addₓ, ← Finset.sum_add_distrib, ← LinearMap.map_add]

protected theorem add_mul (φ₁ φ₂ φ₃ : MvPowerSeries σ R) : (φ₁ + φ₂) * φ₃ = φ₁ * φ₃ + φ₂ * φ₃ :=
  ext fun n => by
    simp only [← coeff_mul, ← add_mulₓ, ← Finset.sum_add_distrib, ← LinearMap.map_add]

protected theorem mul_assoc (φ₁ φ₂ φ₃ : MvPowerSeries σ R) : φ₁ * φ₂ * φ₃ = φ₁ * (φ₂ * φ₃) := by
  ext1 n
  simp only [← coeff_mul, ← Finset.sum_mul, ← Finset.mul_sum, ← Finset.sum_sigma']
  refine' Finset.sum_bij (fun p _ => ⟨(p.2.1, p.2.2 + p.1.2), (p.2.2, p.1.2)⟩) _ _ _ _ <;>
    simp only [← mem_antidiagonal, ← Finset.mem_sigma, ← heq_iff_eq, ← Prod.mk.inj_iff, ← and_imp, ← exists_prop]
  · rintro ⟨⟨i, j⟩, ⟨k, l⟩⟩
    dsimp' only
    rintro rfl rfl
    simp [← add_assocₓ]
    
  · rintro ⟨⟨a, b⟩, ⟨c, d⟩⟩
    dsimp' only
    rintro rfl rfl
    apply mul_assoc
    
  · rintro ⟨⟨a, b⟩, ⟨c, d⟩⟩ ⟨⟨i, j⟩, ⟨k, l⟩⟩
    dsimp' only
    rintro rfl rfl - rfl rfl - rfl rfl
    rfl
    
  · rintro ⟨⟨i, j⟩, ⟨k, l⟩⟩
    dsimp' only
    rintro rfl rfl
    refine' ⟨⟨(i + k, l), (i, k)⟩, _, _⟩ <;> simp [← add_assocₓ]
    

instance : Semiringₓ (MvPowerSeries σ R) :=
  { MvPowerSeries.addMonoidWithOne, MvPowerSeries.hasMul, MvPowerSeries.addCommMonoid with
    mul_one := MvPowerSeries.mul_one, one_mul := MvPowerSeries.one_mul, mul_assoc := MvPowerSeries.mul_assoc,
    mul_zero := MvPowerSeries.mul_zero, zero_mul := MvPowerSeries.zero_mul, left_distrib := MvPowerSeries.mul_add,
    right_distrib := MvPowerSeries.add_mul }

end Semiringₓ

instance [CommSemiringₓ R] : CommSemiringₓ (MvPowerSeries σ R) :=
  { MvPowerSeries.semiring with
    mul_comm := fun φ ψ =>
      ext fun n => by
        simpa only [← coeff_mul, ← mul_comm] using sum_antidiagonal_swap n fun a b => coeff R a φ * coeff R b ψ }

instance [Ringₓ R] : Ringₓ (MvPowerSeries σ R) :=
  { MvPowerSeries.semiring, MvPowerSeries.addCommGroup with }

instance [CommRingₓ R] : CommRingₓ (MvPowerSeries σ R) :=
  { MvPowerSeries.commSemiring, MvPowerSeries.addCommGroup with }

section Semiringₓ

variable [Semiringₓ R]

theorem monomial_mul_monomial (m n : σ →₀ ℕ) (a b : R) : monomial R m a * monomial R n b = monomial R (m + n) (a * b) :=
  by
  ext k
  simp only [← coeff_mul_monomial, ← coeff_monomial]
  split_ifs with h₁ h₂ h₃ h₃ h₂ <;>
    try
      rfl
  · rw [← h₂, tsub_add_cancel_of_le h₁] at h₃
    exact (h₃ rfl).elim
    
  · rw [h₃, add_tsub_cancel_right] at h₂
    exact (h₂ rfl).elim
    
  · exact zero_mul b
    
  · rw [h₂] at h₁
    exact (h₁ <| le_add_left le_rfl).elim
    

variable (σ) (R)

/-- The constant multivariate formal power series.-/
def c : R →+* MvPowerSeries σ R :=
  { monomial R (0 : σ →₀ ℕ) with map_one' := rfl, map_mul' := fun a b => (monomial_mul_monomial 0 0 a b).symm,
    map_zero' := (monomial R (0 : _)).map_zero }

variable {σ} {R}

@[simp]
theorem monomial_zero_eq_C : ⇑(monomial R (0 : σ →₀ ℕ)) = c σ R :=
  rfl

theorem monomial_zero_eq_C_apply (a : R) : monomial R (0 : σ →₀ ℕ) a = c σ R a :=
  rfl

theorem coeff_C [DecidableEq σ] (n : σ →₀ ℕ) (a : R) : coeff R n (c σ R a) = if n = 0 then a else 0 :=
  coeff_monomial _ _ _

theorem coeff_zero_C (a : R) : coeff R (0 : σ →₀ ℕ) (c σ R a) = a :=
  coeff_monomial_same 0 a

/-- The variables of the multivariate formal power series ring.-/
def x (s : σ) : MvPowerSeries σ R :=
  monomial R (single s 1) 1

theorem coeff_X [DecidableEq σ] (n : σ →₀ ℕ) (s : σ) :
    coeff R n (x s : MvPowerSeries σ R) = if n = single s 1 then 1 else 0 :=
  coeff_monomial _ _ _

theorem coeff_index_single_X [DecidableEq σ] (s t : σ) :
    coeff R (single t 1) (x s : MvPowerSeries σ R) = if t = s then 1 else 0 := by
  simp only [← coeff_X, ← single_left_inj one_ne_zero]

@[simp]
theorem coeff_index_single_self_X (s : σ) : coeff R (single s 1) (x s : MvPowerSeries σ R) = 1 :=
  coeff_monomial_same _ _

theorem coeff_zero_X (s : σ) : coeff R (0 : σ →₀ ℕ) (x s : MvPowerSeries σ R) = 0 := by
  rw [coeff_X, if_neg]
  intro h
  exact one_ne_zero (single_eq_zero.mp h.symm)

theorem X_def (s : σ) : x s = monomial R (single s 1) 1 :=
  rfl

theorem X_pow_eq (s : σ) (n : ℕ) : (x s : MvPowerSeries σ R) ^ n = monomial R (single s n) 1 := by
  induction' n with n ih
  · rw [pow_zeroₓ, Finsupp.single_zero, monomial_zero_one]
    
  · rw [pow_succ'ₓ, ih, Nat.succ_eq_add_one, Finsupp.single_add, X, monomial_mul_monomial, one_mulₓ]
    

theorem coeff_X_pow [DecidableEq σ] (m : σ →₀ ℕ) (s : σ) (n : ℕ) :
    coeff R m ((x s : MvPowerSeries σ R) ^ n) = if m = single s n then 1 else 0 := by
  rw [X_pow_eq s n, coeff_monomial]

@[simp]
theorem coeff_mul_C (n : σ →₀ ℕ) (φ : MvPowerSeries σ R) (a : R) : coeff R n (φ * c σ R a) = coeff R n φ * a := by
  simpa using coeff_add_mul_monomial n 0 φ a

@[simp]
theorem coeff_C_mul (n : σ →₀ ℕ) (φ : MvPowerSeries σ R) (a : R) : coeff R n (c σ R a * φ) = a * coeff R n φ := by
  simpa using coeff_add_monomial_mul 0 n φ a

theorem coeff_zero_mul_X (φ : MvPowerSeries σ R) (s : σ) : coeff R (0 : σ →₀ ℕ) (φ * x s) = 0 := by
  have : ¬single s 1 ≤ 0 := fun h => by
    simpa using h s
  simp only [← X, ← coeff_mul_monomial, ← if_neg this]

theorem coeff_zero_X_mul (φ : MvPowerSeries σ R) (s : σ) : coeff R (0 : σ →₀ ℕ) (x s * φ) = 0 := by
  have : ¬single s 1 ≤ 0 := fun h => by
    simpa using h s
  simp only [← X, ← coeff_monomial_mul, ← if_neg this]

variable (σ) (R)

/-- The constant coefficient of a formal power series.-/
def constantCoeff : MvPowerSeries σ R →+* R :=
  { coeff R (0 : σ →₀ ℕ) with toFun := coeff R (0 : σ →₀ ℕ), map_one' := coeff_zero_one,
    map_mul' := fun φ ψ => by
      simp [← coeff_mul, ← support_single_ne_zero],
    map_zero' := LinearMap.map_zero _ }

variable {σ} {R}

@[simp]
theorem coeff_zero_eq_constant_coeff : ⇑(coeff R (0 : σ →₀ ℕ)) = constantCoeff σ R :=
  rfl

theorem coeff_zero_eq_constant_coeff_apply (φ : MvPowerSeries σ R) : coeff R (0 : σ →₀ ℕ) φ = constantCoeff σ R φ :=
  rfl

@[simp]
theorem constant_coeff_C (a : R) : constantCoeff σ R (c σ R a) = a :=
  rfl

@[simp]
theorem constant_coeff_comp_C : (constantCoeff σ R).comp (c σ R) = RingHom.id R :=
  rfl

@[simp]
theorem constant_coeff_zero : constantCoeff σ R 0 = 0 :=
  rfl

@[simp]
theorem constant_coeff_one : constantCoeff σ R 1 = 1 :=
  rfl

@[simp]
theorem constant_coeff_X (s : σ) : constantCoeff σ R (x s) = 0 :=
  coeff_zero_X s

/-- If a multivariate formal power series is invertible,
 then so is its constant coefficient.-/
theorem is_unit_constant_coeff (φ : MvPowerSeries σ R) (h : IsUnit φ) : IsUnit (constantCoeff σ R φ) :=
  h.map _

@[simp]
theorem coeff_smul (f : MvPowerSeries σ R) (n) (a : R) : coeff _ n (a • f) = a * coeff _ n f :=
  rfl

theorem smul_eq_C_mul (f : MvPowerSeries σ R) (a : R) : a • f = c σ R a * f := by
  ext
  simp

theorem X_inj [Nontrivial R] {s t : σ} : (x s : MvPowerSeries σ R) = x t ↔ s = t :=
  ⟨by
    intro h
    replace h := congr_arg (coeff R (single s 1)) h
    rw [coeff_X, if_pos rfl, coeff_X] at h
    split_ifs  at h with H
    · rw [Finsupp.single_eq_single_iff] at H
      cases H
      · exact H.1
        
      · exfalso
        exact one_ne_zero H.1
        
      
    · exfalso
      exact one_ne_zero h
      ,
    congr_arg x⟩

end Semiringₓ

section Map

variable {S T : Type _} [Semiringₓ R] [Semiringₓ S] [Semiringₓ T]

variable (f : R →+* S) (g : S →+* T)

variable (σ)

/-- The map between multivariate formal power series induced by a map on the coefficients.-/
def map : MvPowerSeries σ R →+* MvPowerSeries σ S where
  toFun := fun φ n => f <| coeff R n φ
  map_zero' := ext fun n => f.map_zero
  map_one' :=
    ext fun n =>
      show f ((coeff R n) 1) = (coeff S n) 1 by
        rw [coeff_one, coeff_one]
        split_ifs <;> simp [← f.map_one, ← f.map_zero]
  map_add' := fun φ ψ =>
    ext fun n =>
      show f ((coeff R n) (φ + ψ)) = f ((coeff R n) φ) + f ((coeff R n) ψ) by
        simp
  map_mul' := fun φ ψ =>
    ext fun n =>
      show f _ = _ by
        rw [coeff_mul, f.map_sum, coeff_mul, Finset.sum_congr rfl]
        rintro ⟨i, j⟩ hij
        rw [f.map_mul]
        rfl

variable {σ}

@[simp]
theorem map_id : map σ (RingHom.id R) = RingHom.id _ :=
  rfl

theorem map_comp : map σ (g.comp f) = (map σ g).comp (map σ f) :=
  rfl

@[simp]
theorem coeff_map (n : σ →₀ ℕ) (φ : MvPowerSeries σ R) : coeff S n (map σ f φ) = f (coeff R n φ) :=
  rfl

@[simp]
theorem constant_coeff_map (φ : MvPowerSeries σ R) : constantCoeff σ S (map σ f φ) = f (constantCoeff σ R φ) :=
  rfl

@[simp]
theorem map_monomial (n : σ →₀ ℕ) (a : R) : map σ f (monomial R n a) = monomial S n (f a) := by
  ext m
  simp [← coeff_monomial, ← apply_ite f]

@[simp]
theorem map_C (a : R) : map σ f (c σ R a) = c σ S (f a) :=
  map_monomial _ _ _

@[simp]
theorem map_X (s : σ) : map σ f (x s) = x s := by
  simp [← MvPowerSeries.x]

end Map

section Algebra

variable {A : Type _} [CommSemiringₓ R] [Semiringₓ A] [Algebra R A]

instance : Algebra R (MvPowerSeries σ A) :=
  { MvPowerSeries.module with
    commutes' := fun a φ => by
      ext n
      simp [← Algebra.commutes],
    smul_def' := fun a σ => by
      ext n
      simp [← (coeff A n).map_smul_of_tower a, ← Algebra.smul_def],
    toRingHom := (MvPowerSeries.map σ (algebraMap R A)).comp (c σ R) }

theorem C_eq_algebra_map : c σ R = algebraMap R (MvPowerSeries σ R) :=
  rfl

theorem algebra_map_apply {r : R} : algebraMap R (MvPowerSeries σ A) r = c σ A (algebraMap R A r) := by
  change (MvPowerSeries.map σ (algebraMap R A)).comp (C σ R) r = _
  simp

instance [Nonempty σ] [Nontrivial R] : Nontrivial (Subalgebra R (MvPowerSeries σ R)) :=
  ⟨⟨⊥, ⊤, by
      rw [Ne.def, SetLike.ext_iff, not_forall]
      inhabit σ
      refine' ⟨X default, _⟩
      simp only [← Algebra.mem_bot, ← not_exists, ← Set.mem_range, ← iff_trueₓ, ← Algebra.mem_top]
      intro x
      rw [ext_iff, not_forall]
      refine' ⟨Finsupp.single default 1, _⟩
      simp [← algebra_map_apply, ← coeff_C]⟩⟩

end Algebra

section Trunc

variable [CommSemiringₓ R] (n : σ →₀ ℕ)

/-- Auxiliary definition for the truncation function. -/
def truncFun (φ : MvPowerSeries σ R) : MvPolynomial σ R :=
  ∑ m in Finset.iio n, MvPolynomial.monomial m (coeff R m φ)

theorem coeff_trunc_fun (m : σ →₀ ℕ) (φ : MvPowerSeries σ R) :
    (truncFun n φ).coeff m = if m < n then coeff R m φ else 0 := by
  simp [← trunc_fun, ← MvPolynomial.coeff_sum]

variable (R)

/-- The `n`th truncation of a multivariate formal power series to a multivariate polynomial -/
def trunc : MvPowerSeries σ R →+ MvPolynomial σ R where
  toFun := truncFun n
  map_zero' := by
    ext
    simp [← coeff_trunc_fun]
  map_add' := by
    intros
    ext
    simp [← coeff_trunc_fun, ← ite_add]
    split_ifs <;> rfl

variable {R}

theorem coeff_trunc (m : σ →₀ ℕ) (φ : MvPowerSeries σ R) : (trunc R n φ).coeff m = if m < n then coeff R m φ else 0 :=
  by
  simp [← Trunc, ← coeff_trunc_fun]

@[simp]
theorem trunc_one (hnn : n ≠ 0) : trunc R n 1 = 1 :=
  (MvPolynomial.ext _ _) fun m => by
    rw [coeff_trunc, coeff_one]
    split_ifs with H H' H'
    · subst m
      simp
      
    · symm
      rw [MvPolynomial.coeff_one]
      exact if_neg (Ne.symm H')
      
    · symm
      rw [MvPolynomial.coeff_one]
      refine' if_neg _
      rintro rfl
      apply H
      exact Ne.bot_lt hnn
      

@[simp]
theorem trunc_C (hnn : n ≠ 0) (a : R) : trunc R n (c σ R a) = MvPolynomial.c a :=
  (MvPolynomial.ext _ _) fun m => by
    rw [coeff_trunc, coeff_C, MvPolynomial.coeff_C]
    split_ifs with H <;>
      first |
        rfl|
        try
          simp_all
    exfalso
    apply H
    subst m
    exact Ne.bot_lt hnn

end Trunc

section CommSemiringₓ

variable [CommSemiringₓ R]

theorem X_pow_dvd_iff {s : σ} {n : ℕ} {φ : MvPowerSeries σ R} :
    (x s : MvPowerSeries σ R) ^ n ∣ φ ↔ ∀ m : σ →₀ ℕ, m s < n → coeff R m φ = 0 := by
  constructor
  · rintro ⟨φ, rfl⟩ m h
    rw [coeff_mul, Finset.sum_eq_zero]
    rintro ⟨i, j⟩ hij
    rw [coeff_X_pow, if_neg, zero_mul]
    contrapose! h
    subst i
    rw [Finsupp.mem_antidiagonal] at hij
    rw [← hij, Finsupp.add_apply, Finsupp.single_eq_same]
    exact Nat.le_add_rightₓ n _
    
  · intro h
    refine' ⟨fun m => coeff R (m + single s n) φ, _⟩
    ext m
    by_cases' H : m - single s n + single s n = m
    · rw [coeff_mul, Finset.sum_eq_single (single s n, m - single s n)]
      · rw [coeff_X_pow, if_pos rfl, one_mulₓ]
        simpa using congr_arg (fun m : σ →₀ ℕ => coeff R m φ) H.symm
        
      · rintro ⟨i, j⟩ hij hne
        rw [Finsupp.mem_antidiagonal] at hij
        rw [coeff_X_pow]
        split_ifs with hi
        · exfalso
          apply hne
          rw [← hij, ← hi, Prod.mk.inj_iff]
          refine' ⟨rfl, _⟩
          ext t
          simp only [← add_tsub_cancel_left, ← Finsupp.add_apply, ← Finsupp.tsub_apply]
          
        · exact zero_mul _
          
        
      · intro hni
        exfalso
        apply hni
        rwa [Finsupp.mem_antidiagonal, add_commₓ]
        
      
    · rw [h, coeff_mul, Finset.sum_eq_zero]
      · rintro ⟨i, j⟩ hij
        rw [Finsupp.mem_antidiagonal] at hij
        rw [coeff_X_pow]
        split_ifs with hi
        · exfalso
          apply H
          rw [← hij, hi]
          ext
          rw [coe_add, coe_add, Pi.add_apply, Pi.add_apply, add_tsub_cancel_left, add_commₓ]
          
        · exact zero_mul _
          
        
      · classical
        contrapose! H
        ext t
        by_cases' hst : s = t
        · subst t
          simpa using tsub_add_cancel_of_le H
          
        · simp [← Finsupp.single_apply, ← hst]
          
        
      
    

theorem X_dvd_iff {s : σ} {φ : MvPowerSeries σ R} :
    (x s : MvPowerSeries σ R) ∣ φ ↔ ∀ m : σ →₀ ℕ, m s = 0 → coeff R m φ = 0 := by
  rw [← pow_oneₓ (X s : MvPowerSeries σ R), X_pow_dvd_iff]
  constructor <;> intro h m hm
  · exact h m (hm.symm ▸ zero_lt_one)
    
  · exact h m (Nat.eq_zero_of_le_zeroₓ <| Nat.le_of_succ_le_succₓ hm)
    

end CommSemiringₓ

section Ringₓ

variable [Ringₓ R]

/-- Auxiliary definition that unifies
 the totalised inverse formal power series `(_)⁻¹` and
 the inverse formal power series that depends on
 an inverse of the constant coefficient `inv_of_unit`.-/
/-
The inverse of a multivariate formal power series is defined by
well-founded recursion on the coeffients of the inverse.
-/
protected noncomputable def Inv.aux (a : R) (φ : MvPowerSeries σ R) : MvPowerSeries σ R
  | n => if n = 0 then a else -a * ∑ x in n.antidiagonal, if h : x.2 < n then coeff R x.1 φ * inv.aux x.2 else 0

theorem coeff_inv_aux [DecidableEq σ] (n : σ →₀ ℕ) (a : R) (φ : MvPowerSeries σ R) :
    coeff R n (Inv.aux a φ) =
      if n = 0 then a
      else -a * ∑ x in n.antidiagonal, if x.2 < n then coeff R x.1 φ * coeff R x.2 (Inv.aux a φ) else 0 :=
  show Inv.aux a φ n = _ by
    rw [inv.aux]
    convert rfl

/-- A multivariate formal power series is invertible if the constant coefficient is invertible.-/
-- unify `decidable` instances
def invOfUnit (φ : MvPowerSeries σ R) (u : Rˣ) : MvPowerSeries σ R :=
  Inv.aux (↑u⁻¹) φ

theorem coeff_inv_of_unit [DecidableEq σ] (n : σ →₀ ℕ) (φ : MvPowerSeries σ R) (u : Rˣ) :
    coeff R n (invOfUnit φ u) =
      if n = 0 then ↑u⁻¹
      else -↑u⁻¹ * ∑ x in n.antidiagonal, if x.2 < n then coeff R x.1 φ * coeff R x.2 (invOfUnit φ u) else 0 :=
  coeff_inv_aux n (↑u⁻¹) φ

@[simp]
theorem constant_coeff_inv_of_unit (φ : MvPowerSeries σ R) (u : Rˣ) : constantCoeff σ R (invOfUnit φ u) = ↑u⁻¹ := by
  rw [← coeff_zero_eq_constant_coeff_apply, coeff_inv_of_unit, if_pos rfl]

theorem mul_inv_of_unit (φ : MvPowerSeries σ R) (u : Rˣ) (h : constantCoeff σ R φ = u) : φ * invOfUnit φ u = 1 :=
  ext fun n =>
    if H : n = 0 then by
      rw [H]
      simp [← coeff_mul, ← support_single_ne_zero, ← h]
    else by
      have : ((0 : σ →₀ ℕ), n) ∈ n.antidiagonal := by
        rw [Finsupp.mem_antidiagonal, zero_addₓ]
      rw [coeff_one, if_neg H, coeff_mul, ← Finset.insert_erase this, Finset.sum_insert (Finset.not_mem_erase _ _),
        coeff_zero_eq_constant_coeff_apply, h, coeff_inv_of_unit, if_neg H, neg_mul, mul_neg, Units.mul_inv_cancel_left,
        ← Finset.insert_erase this, Finset.sum_insert (Finset.not_mem_erase _ _), Finset.insert_erase this,
        if_neg (not_lt_of_geₓ <| le_rfl), zero_addₓ, add_commₓ, ← sub_eq_add_neg, sub_eq_zero, Finset.sum_congr rfl]
      rintro ⟨i, j⟩ hij
      rw [Finset.mem_erase, Finsupp.mem_antidiagonal] at hij
      cases' hij with h₁ h₂
      subst n
      rw [if_pos]
      suffices (0 : _) + j < i + j by
        simpa
      apply add_lt_add_right
      constructor
      · intro s
        exact Nat.zero_leₓ _
        
      · intro H
        apply h₁
        suffices i = 0 by
          simp [← this]
        ext1 s
        exact Nat.eq_zero_of_le_zeroₓ (H s)
        

end Ringₓ

section CommRingₓ

variable [CommRingₓ R]

/-- Multivariate formal power series over a local ring form a local ring. -/
instance [LocalRing R] : LocalRing (MvPowerSeries σ R) :=
  LocalRing.of_is_unit_or_is_unit_one_sub_self <| by
    intro φ
    rcases LocalRing.is_unit_or_is_unit_one_sub_self (constant_coeff σ R φ) with (⟨u, h⟩ | ⟨u, h⟩) <;> [left, right] <;>
      · refine' is_unit_of_mul_eq_one _ _ (mul_inv_of_unit _ u _)
        simpa using h.symm
        

-- TODO(jmc): once adic topology lands, show that this is complete
end CommRingₓ

section LocalRing

variable {S : Type _} [CommRingₓ R] [CommRingₓ S] (f : R →+* S) [IsLocalRingHom f]

/-- The map `A[[X]] → B[[X]]` induced by a local ring hom `A → B` is local -/
-- Thanks to the linter for informing us that  this instance does
-- not actually need R and S to be local rings!
instance map.is_local_ring_hom : IsLocalRingHom (map σ f) :=
  ⟨by
    rintro φ ⟨ψ, h⟩
    replace h := congr_arg (constant_coeff σ S) h
    rw [constant_coeff_map] at h
    have : IsUnit (constant_coeff σ S ↑ψ) := @is_unit_constant_coeff σ S _ (↑ψ) ψ.is_unit
    rw [h] at this
    rcases is_unit_of_map_unit f _ this with ⟨c, hc⟩
    exact is_unit_of_mul_eq_one φ (inv_of_unit φ c) (mul_inv_of_unit φ c hc.symm)⟩

end LocalRing

section Field

variable {k : Type _} [Field k]

/-- The inverse `1/f` of a multivariable power series `f` over a field -/
protected def inv (φ : MvPowerSeries σ k) : MvPowerSeries σ k :=
  Inv.aux (constantCoeff σ k φ)⁻¹ φ

instance : Inv (MvPowerSeries σ k) :=
  ⟨MvPowerSeries.inv⟩

theorem coeff_inv [DecidableEq σ] (n : σ →₀ ℕ) (φ : MvPowerSeries σ k) :
    coeff k n φ⁻¹ =
      if n = 0 then (constantCoeff σ k φ)⁻¹
      else -(constantCoeff σ k φ)⁻¹ * ∑ x in n.antidiagonal, if x.2 < n then coeff k x.1 φ * coeff k x.2 φ⁻¹ else 0 :=
  coeff_inv_aux n _ φ

@[simp]
theorem constant_coeff_inv (φ : MvPowerSeries σ k) : constantCoeff σ k φ⁻¹ = (constantCoeff σ k φ)⁻¹ := by
  rw [← coeff_zero_eq_constant_coeff_apply, coeff_inv, if_pos rfl]

theorem inv_eq_zero {φ : MvPowerSeries σ k} : φ⁻¹ = 0 ↔ constantCoeff σ k φ = 0 :=
  ⟨fun h => by
    simpa using congr_arg (constant_coeff σ k) h, fun h =>
    ext fun n => by
      rw [coeff_inv]
      split_ifs <;> simp only [← h, ← MvPowerSeries.coeff_zero, ← zero_mul, ← inv_zero, ← neg_zero]⟩

@[simp]
theorem zero_inv : (0 : MvPowerSeries σ k)⁻¹ = 0 := by
  rw [inv_eq_zero, constant_coeff_zero]

@[simp]
theorem inv_of_unit_eq (φ : MvPowerSeries σ k) (h : constantCoeff σ k φ ≠ 0) : invOfUnit φ (Units.mk0 _ h) = φ⁻¹ :=
  rfl

@[simp]
theorem inv_of_unit_eq' (φ : MvPowerSeries σ k) (u : Units k) (h : constantCoeff σ k φ = u) : invOfUnit φ u = φ⁻¹ := by
  rw [← inv_of_unit_eq φ (h.symm ▸ u.ne_zero)]
  congr 1
  rw [Units.ext_iff]
  exact h.symm

@[simp]
protected theorem mul_inv_cancel (φ : MvPowerSeries σ k) (h : constantCoeff σ k φ ≠ 0) : φ * φ⁻¹ = 1 := by
  rw [← inv_of_unit_eq φ h, mul_inv_of_unit φ (Units.mk0 _ h) rfl]

@[simp]
protected theorem inv_mul_cancel (φ : MvPowerSeries σ k) (h : constantCoeff σ k φ ≠ 0) : φ⁻¹ * φ = 1 := by
  rw [mul_comm, φ.mul_inv_cancel h]

protected theorem eq_mul_inv_iff_mul_eq {φ₁ φ₂ φ₃ : MvPowerSeries σ k} (h : constantCoeff σ k φ₃ ≠ 0) :
    φ₁ = φ₂ * φ₃⁻¹ ↔ φ₁ * φ₃ = φ₂ :=
  ⟨fun k => by
    simp [← k, ← mul_assoc, ← MvPowerSeries.inv_mul_cancel _ h], fun k => by
    simp [k, ← mul_assoc, ← MvPowerSeries.mul_inv_cancel _ h]⟩

protected theorem eq_inv_iff_mul_eq_one {φ ψ : MvPowerSeries σ k} (h : constantCoeff σ k ψ ≠ 0) : φ = ψ⁻¹ ↔ φ * ψ = 1 :=
  by
  rw [← MvPowerSeries.eq_mul_inv_iff_mul_eq h, one_mulₓ]

protected theorem inv_eq_iff_mul_eq_one {φ ψ : MvPowerSeries σ k} (h : constantCoeff σ k ψ ≠ 0) : ψ⁻¹ = φ ↔ φ * ψ = 1 :=
  by
  rw [eq_comm, MvPowerSeries.eq_inv_iff_mul_eq_one h]

@[simp]
protected theorem mul_inv_rev (φ ψ : MvPowerSeries σ k) : (φ * ψ)⁻¹ = ψ⁻¹ * φ⁻¹ := by
  by_cases' h : constant_coeff σ k (φ * ψ) = 0
  · rw [inv_eq_zero.mpr h]
    simp only [← map_mul, ← mul_eq_zero] at h
    -- we don't have `no_zero_divisors (mw_power_series σ k)` yet,
      cases h <;>
      simp [← inv_eq_zero.mpr h]
    
  · rw [MvPowerSeries.inv_eq_iff_mul_eq_one h]
    simp only [← not_or_distrib, ← map_mul, ← mul_eq_zero] at h
    rw [← mul_assoc, mul_assoc _⁻¹, MvPowerSeries.inv_mul_cancel _ h.left, mul_oneₓ,
      MvPowerSeries.inv_mul_cancel _ h.right]
    

@[simp]
theorem inv_one : (1 : MvPowerSeries σ k)⁻¹ = 1 := by
  rw [MvPowerSeries.inv_eq_iff_mul_eq_one, mul_oneₓ]
  simp

@[simp]
theorem C_inv (r : k) : (c σ k r)⁻¹ = c σ k r⁻¹ := by
  rcases eq_or_ne r 0 with (rfl | hr)
  · simp
    
  rw [MvPowerSeries.inv_eq_iff_mul_eq_one, ← map_mul, inv_mul_cancel hr, map_one]
  simpa using hr

@[simp]
theorem X_inv (s : σ) : (x s : MvPowerSeries σ k)⁻¹ = 0 := by
  rw [inv_eq_zero, constant_coeff_X]

@[simp]
theorem smul_inv (r : k) (φ : MvPowerSeries σ k) : (r • φ)⁻¹ = r⁻¹ • φ⁻¹ := by
  simp [← smul_eq_C_mul, ← mul_comm]

end Field

end MvPowerSeries

namespace MvPolynomial

open Finsupp

variable {σ : Type _} {R : Type _} [CommSemiringₓ R] (φ ψ : MvPolynomial σ R)

/-- The natural inclusion from multivariate polynomials into multivariate formal power series.-/
instance coeToMvPowerSeries : Coe (MvPolynomial σ R) (MvPowerSeries σ R) :=
  ⟨fun φ n => coeff n φ⟩

theorem coe_def : (φ : MvPowerSeries σ R) = fun n => coeff n φ :=
  rfl

@[simp, norm_cast]
theorem coeff_coe (n : σ →₀ ℕ) : MvPowerSeries.coeff R n ↑φ = coeff n φ :=
  rfl

@[simp, norm_cast]
theorem coe_monomial (n : σ →₀ ℕ) (a : R) : (monomial n a : MvPowerSeries σ R) = MvPowerSeries.monomial R n a :=
  MvPowerSeries.ext fun m => by
    rw [coeff_coe, coeff_monomial, MvPowerSeries.coeff_monomial]
    split_ifs with h₁ h₂ <;>
      first |
          rfl|
          subst m <;>
        contradiction

@[simp, norm_cast]
theorem coe_zero : ((0 : MvPolynomial σ R) : MvPowerSeries σ R) = 0 :=
  rfl

@[simp, norm_cast]
theorem coe_one : ((1 : MvPolynomial σ R) : MvPowerSeries σ R) = 1 :=
  coe_monomial _ _

@[simp, norm_cast]
theorem coe_add : ((φ + ψ : MvPolynomial σ R) : MvPowerSeries σ R) = φ + ψ :=
  rfl

@[simp, norm_cast]
theorem coe_mul : ((φ * ψ : MvPolynomial σ R) : MvPowerSeries σ R) = φ * ψ :=
  MvPowerSeries.ext fun n => by
    simp only [← coeff_coe, ← MvPowerSeries.coeff_mul, ← coeff_mul]

@[simp, norm_cast]
theorem coe_C (a : R) : ((c a : MvPolynomial σ R) : MvPowerSeries σ R) = MvPowerSeries.c σ R a :=
  coe_monomial _ _

@[simp, norm_cast]
theorem coe_bit0 : ((bit0 φ : MvPolynomial σ R) : MvPowerSeries σ R) = bit0 (φ : MvPowerSeries σ R) :=
  coe_add _ _

@[simp, norm_cast]
theorem coe_bit1 : ((bit1 φ : MvPolynomial σ R) : MvPowerSeries σ R) = bit1 (φ : MvPowerSeries σ R) := by
  rw [bit1, bit1, coe_add, coe_one, coe_bit0]

@[simp, norm_cast]
theorem coe_X (s : σ) : ((x s : MvPolynomial σ R) : MvPowerSeries σ R) = MvPowerSeries.x s :=
  coe_monomial _ _

variable (σ R)

theorem coe_injective : Function.Injective (coe : MvPolynomial σ R → MvPowerSeries σ R) := fun x y h => by
  ext
  simp_rw [← coeff_coe, h]

variable {σ R φ ψ}

@[simp, norm_cast]
theorem coe_inj : (φ : MvPowerSeries σ R) = ψ ↔ φ = ψ :=
  (coe_injective σ R).eq_iff

@[simp]
theorem coe_eq_zero_iff : (φ : MvPowerSeries σ R) = 0 ↔ φ = 0 := by
  rw [← coe_zero, coe_inj]

@[simp]
theorem coe_eq_one_iff : (φ : MvPowerSeries σ R) = 1 ↔ φ = 1 := by
  rw [← coe_one, coe_inj]

/-- The coercion from multivariable polynomials to multivariable power series
as a ring homomorphism.
-/
def coeToMvPowerSeries.ringHom : MvPolynomial σ R →+* MvPowerSeries σ R where
  toFun := (coe : MvPolynomial σ R → MvPowerSeries σ R)
  map_zero' := coe_zero
  map_one' := coe_one
  map_add' := coe_add
  map_mul' := coe_mul

@[simp, norm_cast]
theorem coe_pow (n : ℕ) : ((φ ^ n : MvPolynomial σ R) : MvPowerSeries σ R) = (φ : MvPowerSeries σ R) ^ n :=
  coeToMvPowerSeries.ringHom.map_pow _ _

variable (φ ψ)

@[simp]
theorem coeToMvPowerSeries.ring_hom_apply : coeToMvPowerSeries.ringHom φ = φ :=
  rfl

section Algebra

variable (A : Type _) [CommSemiringₓ A] [Algebra R A]

theorem algebra_map_apply (r : R) : algebraMap R (MvPolynomial σ A) r = c (algebraMap R A r) :=
  rfl

/-- The coercion from multivariable polynomials to multivariable power series
as an algebra homomorphism.
-/
def coeToMvPowerSeries.algHom : MvPolynomial σ R →ₐ[R] MvPowerSeries σ A :=
  { (MvPowerSeries.map σ (algebraMap R A)).comp coeToMvPowerSeries.ringHom with
    commutes' := fun r => by
      simp [← algebra_map_apply, ← MvPowerSeries.algebra_map_apply] }

@[simp]
theorem coeToMvPowerSeries.alg_hom_apply : coeToMvPowerSeries.algHom A φ = MvPowerSeries.map σ (algebraMap R A) ↑φ :=
  rfl

end Algebra

end MvPolynomial

namespace MvPowerSeries

variable {σ R A : Type _} [CommSemiringₓ R] [CommSemiringₓ A] [Algebra R A] (f : MvPowerSeries σ R)

instance algebraMvPolynomial : Algebra (MvPolynomial σ R) (MvPowerSeries σ A) :=
  RingHom.toAlgebra (MvPolynomial.coeToMvPowerSeries.algHom A).toRingHom

instance algebraMvPowerSeries : Algebra (MvPowerSeries σ R) (MvPowerSeries σ A) :=
  (map σ (algebraMap R A)).toAlgebra

variable (A)

theorem algebra_map_apply' (p : MvPolynomial σ R) :
    algebraMap (MvPolynomial σ R) (MvPowerSeries σ A) p = map σ (algebraMap R A) p :=
  rfl

theorem algebra_map_apply'' : algebraMap (MvPowerSeries σ R) (MvPowerSeries σ A) f = map σ (algebraMap R A) f :=
  rfl

end MvPowerSeries

/-- Formal power series over the coefficient ring `R`.-/
def PowerSeries (R : Type _) :=
  MvPowerSeries Unit R

namespace PowerSeries

open Finsupp (single)

variable {R : Type _}

section

attribute [local reducible] PowerSeries

instance [Inhabited R] : Inhabited (PowerSeries R) := by
  infer_instance

instance [AddMonoidₓ R] : AddMonoidₓ (PowerSeries R) := by
  infer_instance

instance [AddGroupₓ R] : AddGroupₓ (PowerSeries R) := by
  infer_instance

instance [AddCommMonoidₓ R] : AddCommMonoidₓ (PowerSeries R) := by
  infer_instance

instance [AddCommGroupₓ R] : AddCommGroupₓ (PowerSeries R) := by
  infer_instance

instance [Semiringₓ R] : Semiringₓ (PowerSeries R) := by
  infer_instance

instance [CommSemiringₓ R] : CommSemiringₓ (PowerSeries R) := by
  infer_instance

instance [Ringₓ R] : Ringₓ (PowerSeries R) := by
  infer_instance

instance [CommRingₓ R] : CommRingₓ (PowerSeries R) := by
  infer_instance

instance [Nontrivial R] : Nontrivial (PowerSeries R) := by
  infer_instance

instance {A} [Semiringₓ R] [AddCommMonoidₓ A] [Module R A] : Module R (PowerSeries A) := by
  infer_instance

instance {A S} [Semiringₓ R] [Semiringₓ S] [AddCommMonoidₓ A] [Module R A] [Module S A] [HasSmul R S]
    [IsScalarTower R S A] : IsScalarTower R S (PowerSeries A) :=
  Pi.is_scalar_tower

instance {A} [Semiringₓ A] [CommSemiringₓ R] [Algebra R A] : Algebra R (PowerSeries A) := by
  infer_instance

end

section Semiringₓ

variable (R) [Semiringₓ R]

/-- The `n`th coefficient of a formal power series.-/
def coeff (n : ℕ) : PowerSeries R →ₗ[R] R :=
  MvPowerSeries.coeff R (single () n)

/-- The `n`th monomial with coefficient `a` as formal power series.-/
def monomial (n : ℕ) : R →ₗ[R] PowerSeries R :=
  MvPowerSeries.monomial R (single () n)

variable {R}

theorem coeff_def {s : Unit →₀ ℕ} {n : ℕ} (h : s () = n) : coeff R n = MvPowerSeries.coeff R s := by
  erw [coeff, ← h, ← Finsupp.unique_single s]

/-- Two formal power series are equal if all their coefficients are equal.-/
@[ext]
theorem ext {φ ψ : PowerSeries R} (h : ∀ n, coeff R n φ = coeff R n ψ) : φ = ψ :=
  MvPowerSeries.ext fun n => by
    rw [← coeff_def]
    · apply h
      
    rfl

/-- Two formal power series are equal if all their coefficients are equal.-/
theorem ext_iff {φ ψ : PowerSeries R} : φ = ψ ↔ ∀ n, coeff R n φ = coeff R n ψ :=
  ⟨fun h n => congr_arg (coeff R n) h, ext⟩

/-- Constructor for formal power series.-/
def mk {R} (f : ℕ → R) : PowerSeries R := fun s => f (s ())

@[simp]
theorem coeff_mk (n : ℕ) (f : ℕ → R) : coeff R n (mk f) = f n :=
  congr_arg f Finsupp.single_eq_same

theorem coeff_monomial (m n : ℕ) (a : R) : coeff R m (monomial R n a) = if m = n then a else 0 :=
  calc
    coeff R m (monomial R n a) = _ := MvPowerSeries.coeff_monomial _ _ _
    _ = if m = n then a else 0 := by
      simp only [← Finsupp.unique_single_eq_iff]
    

theorem monomial_eq_mk (n : ℕ) (a : R) : monomial R n a = mk fun m => if m = n then a else 0 :=
  ext fun m => by
    rw [coeff_monomial, coeff_mk]

@[simp]
theorem coeff_monomial_same (n : ℕ) (a : R) : coeff R n (monomial R n a) = a :=
  MvPowerSeries.coeff_monomial_same _ _

@[simp]
theorem coeff_comp_monomial (n : ℕ) : (coeff R n).comp (monomial R n) = LinearMap.id :=
  LinearMap.ext <| coeff_monomial_same n

variable (R)

/-- The constant coefficient of a formal power series. -/
def constantCoeff : PowerSeries R →+* R :=
  MvPowerSeries.constantCoeff Unit R

/-- The constant formal power series.-/
def c : R →+* PowerSeries R :=
  MvPowerSeries.c Unit R

variable {R}

/-- The variable of the formal power series ring.-/
def x : PowerSeries R :=
  MvPowerSeries.x ()

@[simp]
theorem coeff_zero_eq_constant_coeff : ⇑(coeff R 0) = constantCoeff R := by
  rw [coeff, Finsupp.single_zero]
  rfl

theorem coeff_zero_eq_constant_coeff_apply (φ : PowerSeries R) : coeff R 0 φ = constantCoeff R φ := by
  rw [coeff_zero_eq_constant_coeff] <;> rfl

@[simp]
theorem monomial_zero_eq_C : ⇑(monomial R 0) = c R := by
  rw [monomial, Finsupp.single_zero, MvPowerSeries.monomial_zero_eq_C, C]

theorem monomial_zero_eq_C_apply (a : R) : monomial R 0 a = c R a := by
  simp

theorem coeff_C (n : ℕ) (a : R) : coeff R n (c R a : PowerSeries R) = if n = 0 then a else 0 := by
  rw [← monomial_zero_eq_C_apply, coeff_monomial]

@[simp]
theorem coeff_zero_C (a : R) : coeff R 0 (c R a) = a := by
  rw [← monomial_zero_eq_C_apply, coeff_monomial_same 0 a]

theorem X_eq : (x : PowerSeries R) = monomial R 1 1 :=
  rfl

theorem coeff_X (n : ℕ) : coeff R n (x : PowerSeries R) = if n = 1 then 1 else 0 := by
  rw [X_eq, coeff_monomial]

@[simp]
theorem coeff_zero_X : coeff R 0 (x : PowerSeries R) = 0 := by
  rw [coeff, Finsupp.single_zero, X, MvPowerSeries.coeff_zero_X]

@[simp]
theorem coeff_one_X : coeff R 1 (x : PowerSeries R) = 1 := by
  rw [coeff_X, if_pos rfl]

@[simp]
theorem X_ne_zero [Nontrivial R] : (x : PowerSeries R) ≠ 0 := fun H => by
  simpa only [← coeff_one_X, ← one_ne_zero, ← map_zero] using congr_arg (coeff R 1) H

theorem X_pow_eq (n : ℕ) : (x : PowerSeries R) ^ n = monomial R n 1 :=
  MvPowerSeries.X_pow_eq _ n

theorem coeff_X_pow (m n : ℕ) : coeff R m ((x : PowerSeries R) ^ n) = if m = n then 1 else 0 := by
  rw [X_pow_eq, coeff_monomial]

@[simp]
theorem coeff_X_pow_self (n : ℕ) : coeff R n ((x : PowerSeries R) ^ n) = 1 := by
  rw [coeff_X_pow, if_pos rfl]

@[simp]
theorem coeff_one (n : ℕ) : coeff R n (1 : PowerSeries R) = if n = 0 then 1 else 0 :=
  coeff_C n 1

theorem coeff_zero_one : coeff R 0 (1 : PowerSeries R) = 1 :=
  coeff_zero_C 1

theorem coeff_mul (n : ℕ) (φ ψ : PowerSeries R) :
    coeff R n (φ * ψ) = ∑ p in Finset.Nat.antidiagonal n, coeff R p.1 φ * coeff R p.2 ψ := by
  symm
  apply Finset.sum_bij fun (p : ℕ × ℕ) h => (single () p.1, single () p.2)
  · rintro ⟨i, j⟩ hij
    rw [Finset.Nat.mem_antidiagonal] at hij
    rw [Finsupp.mem_antidiagonal, ← Finsupp.single_add, hij]
    
  · rintro ⟨i, j⟩ hij
    rfl
    
  · rintro ⟨i, j⟩ ⟨k, l⟩ hij hkl
    simpa only [← Prod.mk.inj_iff, ← Finsupp.unique_single_eq_iff] using id
    
  · rintro ⟨f, g⟩ hfg
    refine' ⟨(f (), g ()), _, _⟩
    · rw [Finsupp.mem_antidiagonal] at hfg
      rw [Finset.Nat.mem_antidiagonal, ← Finsupp.add_apply, hfg, Finsupp.single_eq_same]
      
    · rw [Prod.mk.inj_iff]
      dsimp'
      exact ⟨Finsupp.unique_single f, Finsupp.unique_single g⟩
      
    

@[simp]
theorem coeff_mul_C (n : ℕ) (φ : PowerSeries R) (a : R) : coeff R n (φ * c R a) = coeff R n φ * a :=
  MvPowerSeries.coeff_mul_C _ φ a

@[simp]
theorem coeff_C_mul (n : ℕ) (φ : PowerSeries R) (a : R) : coeff R n (c R a * φ) = a * coeff R n φ :=
  MvPowerSeries.coeff_C_mul _ φ a

@[simp]
theorem coeff_smul {S : Type _} [Semiringₓ S] [Module R S] (n : ℕ) (φ : PowerSeries S) (a : R) :
    coeff S n (a • φ) = a • coeff S n φ :=
  rfl

theorem smul_eq_C_mul (f : PowerSeries R) (a : R) : a • f = c R a * f := by
  ext
  simp

@[simp]
theorem coeff_succ_mul_X (n : ℕ) (φ : PowerSeries R) : coeff R (n + 1) (φ * X) = coeff R n φ := by
  simp only [← coeff, ← Finsupp.single_add]
  convert φ.coeff_add_mul_monomial (single () n) (single () 1) _
  rw [mul_oneₓ]

@[simp]
theorem coeff_succ_X_mul (n : ℕ) (φ : PowerSeries R) : coeff R (n + 1) (X * φ) = coeff R n φ := by
  simp only [← coeff, ← Finsupp.single_add, ← add_commₓ n 1]
  convert φ.coeff_add_monomial_mul (single () 1) (single () n) _
  rw [one_mulₓ]

@[simp]
theorem constant_coeff_C (a : R) : constantCoeff R (c R a) = a :=
  rfl

@[simp]
theorem constant_coeff_comp_C : (constantCoeff R).comp (c R) = RingHom.id R :=
  rfl

@[simp]
theorem constant_coeff_zero : constantCoeff R 0 = 0 :=
  rfl

@[simp]
theorem constant_coeff_one : constantCoeff R 1 = 1 :=
  rfl

@[simp]
theorem constant_coeff_X : constantCoeff R x = 0 :=
  MvPowerSeries.coeff_zero_X _

theorem coeff_zero_mul_X (φ : PowerSeries R) : coeff R 0 (φ * X) = 0 := by
  simp

theorem coeff_zero_X_mul (φ : PowerSeries R) : coeff R 0 (X * φ) = 0 := by
  simp

-- The following section duplicates the api of `data.polynomial.coeff` and should attempt to keep
-- up to date with that
section

theorem coeff_C_mul_X_pow (x : R) (k n : ℕ) : coeff R n (c R x * X ^ k : PowerSeries R) = if n = k then x else 0 := by
  simp [← X_pow_eq, ← coeff_monomial]

@[simp]
theorem coeff_mul_X_pow (p : PowerSeries R) (n d : ℕ) : coeff R (d + n) (p * X ^ n) = coeff R d p := by
  rw [coeff_mul, Finset.sum_eq_single (d, n), coeff_X_pow, if_pos rfl, mul_oneₓ]
  · rintro ⟨i, j⟩ h1 h2
    rw [coeff_X_pow, if_neg, mul_zero]
    rintro rfl
    apply h2
    rw [Finset.Nat.mem_antidiagonal, add_right_cancel_iffₓ] at h1
    subst h1
    
  · exact fun h1 => (h1 (Finset.Nat.mem_antidiagonal.2 rfl)).elim
    

@[simp]
theorem coeff_X_pow_mul (p : PowerSeries R) (n d : ℕ) : coeff R (d + n) (X ^ n * p) = coeff R d p := by
  rw [coeff_mul, Finset.sum_eq_single (n, d), coeff_X_pow, if_pos rfl, one_mulₓ]
  · rintro ⟨i, j⟩ h1 h2
    rw [coeff_X_pow, if_neg, zero_mul]
    rintro rfl
    apply h2
    rw [Finset.Nat.mem_antidiagonal, add_commₓ, add_right_cancel_iffₓ] at h1
    subst h1
    
  · rw [add_commₓ]
    exact fun h1 => (h1 (Finset.Nat.mem_antidiagonal.2 rfl)).elim
    

theorem coeff_mul_X_pow' (p : PowerSeries R) (n d : ℕ) : coeff R d (p * X ^ n) = ite (n ≤ d) (coeff R (d - n) p) 0 := by
  split_ifs
  · rw [← tsub_add_cancel_of_le h, coeff_mul_X_pow, add_tsub_cancel_right]
    
  · refine' (coeff_mul _ _ _).trans (Finset.sum_eq_zero fun x hx => _)
    rw [coeff_X_pow, if_neg, mul_zero]
    exact ((le_of_add_le_right (finset.nat.mem_antidiagonal.mp hx).le).trans_lt <| not_le.mp h).Ne
    

theorem coeff_X_pow_mul' (p : PowerSeries R) (n d : ℕ) : coeff R d (X ^ n * p) = ite (n ≤ d) (coeff R (d - n) p) 0 := by
  split_ifs
  · rw [← tsub_add_cancel_of_le h, coeff_X_pow_mul]
    simp
    
  · refine' (coeff_mul _ _ _).trans (Finset.sum_eq_zero fun x hx => _)
    rw [coeff_X_pow, if_neg, zero_mul]
    have := finset.nat.mem_antidiagonal.mp hx
    rw [add_commₓ] at this
    exact ((le_of_add_le_right this.le).trans_lt <| not_le.mp h).Ne
    

end

/-- If a formal power series is invertible, then so is its constant coefficient.-/
theorem is_unit_constant_coeff (φ : PowerSeries R) (h : IsUnit φ) : IsUnit (constantCoeff R φ) :=
  MvPowerSeries.is_unit_constant_coeff φ h

/-- Split off the constant coefficient. -/
theorem eq_shift_mul_X_add_const (φ : PowerSeries R) :
    φ = (mk fun p => coeff R (p + 1) φ) * X + c R (constantCoeff R φ) := by
  ext (_ | n)
  · simp only [← RingHom.map_add, ← constant_coeff_C, ← constant_coeff_X, ← coeff_zero_eq_constant_coeff, ← zero_addₓ, ←
      mul_zero, ← RingHom.map_mul]
    
  · simp only [← coeff_succ_mul_X, ← coeff_mk, ← LinearMap.map_add, ← coeff_C, ← n.succ_ne_zero, ← sub_zero, ← if_false,
      ← add_zeroₓ]
    

/-- Split off the constant coefficient. -/
theorem eq_X_mul_shift_add_const (φ : PowerSeries R) :
    φ = (X * mk fun p => coeff R (p + 1) φ) + c R (constantCoeff R φ) := by
  ext (_ | n)
  · simp only [← RingHom.map_add, ← constant_coeff_C, ← constant_coeff_X, ← coeff_zero_eq_constant_coeff, ← zero_addₓ, ←
      zero_mul, ← RingHom.map_mul]
    
  · simp only [← coeff_succ_X_mul, ← coeff_mk, ← LinearMap.map_add, ← coeff_C, ← n.succ_ne_zero, ← sub_zero, ← if_false,
      ← add_zeroₓ]
    

section Map

variable {S : Type _} {T : Type _} [Semiringₓ S] [Semiringₓ T]

variable (f : R →+* S) (g : S →+* T)

/-- The map between formal power series induced by a map on the coefficients.-/
def map : PowerSeries R →+* PowerSeries S :=
  MvPowerSeries.map _ f

@[simp]
theorem map_id : (map (RingHom.id R) : PowerSeries R → PowerSeries R) = id :=
  rfl

theorem map_comp : map (g.comp f) = (map g).comp (map f) :=
  rfl

@[simp]
theorem coeff_map (n : ℕ) (φ : PowerSeries R) : coeff S n (map f φ) = f (coeff R n φ) :=
  rfl

@[simp]
theorem map_C (r : R) : map f (c _ r) = c _ (f r) := by
  ext
  simp [← coeff_C, ← apply_ite f]

@[simp]
theorem map_X : map f x = X := by
  ext
  simp [← coeff_X, ← apply_ite f]

end Map

end Semiringₓ

section CommSemiringₓ

variable [CommSemiringₓ R]

theorem X_pow_dvd_iff {n : ℕ} {φ : PowerSeries R} : (x : PowerSeries R) ^ n ∣ φ ↔ ∀ m, m < n → coeff R m φ = 0 := by
  convert @MvPowerSeries.X_pow_dvd_iff Unit R _ () n φ
  apply propext
  classical
  constructor <;> intro h m hm
  · rw [Finsupp.unique_single m]
    convert h _ hm
    
  · apply h
    simpa only [← Finsupp.single_eq_same] using hm
    

theorem X_dvd_iff {φ : PowerSeries R} : (x : PowerSeries R) ∣ φ ↔ constantCoeff R φ = 0 := by
  rw [← pow_oneₓ (X : PowerSeries R), X_pow_dvd_iff, ← coeff_zero_eq_constant_coeff_apply]
  constructor <;> intro h
  · exact h 0 zero_lt_one
    
  · intro m hm
    rwa [Nat.eq_zero_of_le_zeroₓ (Nat.le_of_succ_le_succₓ hm)]
    

open Finset Nat

/-- The ring homomorphism taking a power series `f(X)` to `f(aX)`. -/
noncomputable def rescale (a : R) : PowerSeries R →+* PowerSeries R where
  toFun := fun f => PowerSeries.mk fun n => a ^ n * PowerSeries.coeff R n f
  map_zero' := by
    ext
    simp only [← LinearMap.map_zero, ← PowerSeries.coeff_mk, ← mul_zero]
  map_one' := by
    ext1
    simp only [← mul_boole, ← PowerSeries.coeff_mk, ← PowerSeries.coeff_one]
    split_ifs
    · rw [h, pow_zeroₓ]
      
    rfl
  map_add' := by
    intros
    ext
    exact mul_addₓ _ _ _
  map_mul' := fun f g => by
    ext
    rw [PowerSeries.coeff_mul, PowerSeries.coeff_mk, PowerSeries.coeff_mul, Finset.mul_sum]
    apply sum_congr rfl
    simp only [← coeff_mk, ← Prod.forall, ← nat.mem_antidiagonal]
    intro b c H
    rw [← H, pow_addₓ, mul_mul_mul_commₓ]

@[simp]
theorem coeff_rescale (f : PowerSeries R) (a : R) (n : ℕ) : coeff R n (rescale a f) = a ^ n * coeff R n f :=
  coeff_mk n _

@[simp]
theorem rescale_zero : rescale 0 = (c R).comp (constantCoeff R) := by
  ext
  simp only [← Function.comp_app, ← RingHom.coe_comp, ← rescale, ← RingHom.coe_mk, ← PowerSeries.coeff_mk _ _, ←
    coeff_C]
  split_ifs
  · simp only [← h, ← one_mulₓ, ← coeff_zero_eq_constant_coeff, ← pow_zeroₓ]
    
  · rw [zero_pow' n h, zero_mul]
    

theorem rescale_zero_apply : rescale 0 x = c R (constantCoeff R x) := by
  simp

@[simp]
theorem rescale_one : rescale 1 = RingHom.id (PowerSeries R) := by
  ext
  simp only [← RingHom.id_apply, ← rescale, ← one_pow, ← coeff_mk, ← one_mulₓ, ← RingHom.coe_mk]

theorem rescale_mk (f : ℕ → R) (a : R) : rescale a (mk f) = mk fun n : ℕ => a ^ n * f n := by
  ext
  rw [coeff_rescale, coeff_mk, coeff_mk]

theorem rescale_rescale (f : PowerSeries R) (a b : R) : rescale b (rescale a f) = rescale (a * b) f := by
  ext
  repeat'
    rw [coeff_rescale]
  rw [mul_powₓ, mul_comm _ (b ^ n), mul_assoc]

theorem rescale_mul (a b : R) : rescale (a * b) = (rescale b).comp (rescale a) := by
  ext
  simp [rescale_rescale]

section Trunc

/-- The `n`th truncation of a formal power series to a polynomial -/
def trunc (n : ℕ) (φ : PowerSeries R) : R[X] :=
  ∑ m in ico 0 n, Polynomial.monomial m (coeff R m φ)

theorem coeff_trunc (m) (n) (φ : PowerSeries R) : (trunc n φ).coeff m = if m < n then coeff R m φ else 0 := by
  simp [← Trunc, ← Polynomial.coeff_sum, ← Polynomial.coeff_monomial, ← Nat.lt_succ_iffₓ]

@[simp]
theorem trunc_zero (n) : trunc n (0 : PowerSeries R) = 0 :=
  Polynomial.ext fun m => by
    rw [coeff_trunc, LinearMap.map_zero, Polynomial.coeff_zero]
    split_ifs <;> rfl

@[simp]
theorem trunc_one (n) : trunc (n + 1) (1 : PowerSeries R) = 1 :=
  Polynomial.ext fun m => by
    rw [coeff_trunc, coeff_one]
    split_ifs with H H' H' <;> rw [Polynomial.coeff_one]
    · subst m
      rw [if_pos rfl]
      
    · symm
      exact if_neg (Ne.elim (Ne.symm H'))
      
    · symm
      refine' if_neg _
      rintro rfl
      apply H
      exact Nat.zero_lt_succₓ _
      

@[simp]
theorem trunc_C (n) (a : R) : trunc (n + 1) (c R a) = Polynomial.c a :=
  Polynomial.ext fun m => by
    rw [coeff_trunc, coeff_C, Polynomial.coeff_C]
    split_ifs with H <;>
      first |
        rfl|
        try
          simp_all

@[simp]
theorem trunc_add (n) (φ ψ : PowerSeries R) : trunc n (φ + ψ) = trunc n φ + trunc n ψ :=
  Polynomial.ext fun m => by
    simp only [← coeff_trunc, ← AddMonoidHom.map_add, ← Polynomial.coeff_add]
    split_ifs with H
    · rfl
      
    · rw [zero_addₓ]
      

end Trunc

end CommSemiringₓ

section Ringₓ

variable [Ringₓ R]

/-- Auxiliary function used for computing inverse of a power series -/
protected def Inv.aux : R → PowerSeries R → PowerSeries R :=
  MvPowerSeries.Inv.aux

theorem coeff_inv_aux (n : ℕ) (a : R) (φ : PowerSeries R) :
    coeff R n (Inv.aux a φ) =
      if n = 0 then a
      else -a * ∑ x in Finset.Nat.antidiagonal n, if x.2 < n then coeff R x.1 φ * coeff R x.2 (Inv.aux a φ) else 0 :=
  by
  rw [coeff, inv.aux, MvPowerSeries.coeff_inv_aux]
  simp only [← Finsupp.single_eq_zero]
  split_ifs
  · rfl
    
  congr 1
  symm
  apply Finset.sum_bij fun (p : ℕ × ℕ) h => (single () p.1, single () p.2)
  · rintro ⟨i, j⟩ hij
    rw [Finset.Nat.mem_antidiagonal] at hij
    rw [Finsupp.mem_antidiagonal, ← Finsupp.single_add, hij]
    
  · rintro ⟨i, j⟩ hij
    by_cases' H : j < n
    · rw [if_pos H, if_pos]
      · rfl
        
      constructor
      · rintro ⟨⟩
        simpa [← Finsupp.single_eq_same] using le_of_ltₓ H
        
      · intro hh
        rw [lt_iff_not_geₓ] at H
        apply H
        simpa [← Finsupp.single_eq_same] using hh ()
        
      
    · rw [if_neg H, if_neg]
      rintro ⟨h₁, h₂⟩
      apply h₂
      rintro ⟨⟩
      simpa [← Finsupp.single_eq_same] using not_ltₓ.1 H
      
    
  · rintro ⟨i, j⟩ ⟨k, l⟩ hij hkl
    simpa only [← Prod.mk.inj_iff, ← Finsupp.unique_single_eq_iff] using id
    
  · rintro ⟨f, g⟩ hfg
    refine' ⟨(f (), g ()), _, _⟩
    · rw [Finsupp.mem_antidiagonal] at hfg
      rw [Finset.Nat.mem_antidiagonal, ← Finsupp.add_apply, hfg, Finsupp.single_eq_same]
      
    · rw [Prod.mk.inj_iff]
      dsimp'
      exact ⟨Finsupp.unique_single f, Finsupp.unique_single g⟩
      
    

/-- A formal power series is invertible if the constant coefficient is invertible.-/
def invOfUnit (φ : PowerSeries R) (u : Rˣ) : PowerSeries R :=
  MvPowerSeries.invOfUnit φ u

theorem coeff_inv_of_unit (n : ℕ) (φ : PowerSeries R) (u : Rˣ) :
    coeff R n (invOfUnit φ u) =
      if n = 0 then ↑u⁻¹
      else
        -↑u⁻¹ * ∑ x in Finset.Nat.antidiagonal n, if x.2 < n then coeff R x.1 φ * coeff R x.2 (invOfUnit φ u) else 0 :=
  coeff_inv_aux n (↑u⁻¹) φ

@[simp]
theorem constant_coeff_inv_of_unit (φ : PowerSeries R) (u : Rˣ) : constantCoeff R (invOfUnit φ u) = ↑u⁻¹ := by
  rw [← coeff_zero_eq_constant_coeff_apply, coeff_inv_of_unit, if_pos rfl]

theorem mul_inv_of_unit (φ : PowerSeries R) (u : Rˣ) (h : constantCoeff R φ = u) : φ * invOfUnit φ u = 1 :=
  MvPowerSeries.mul_inv_of_unit φ u <| h

/-- Two ways of removing the constant coefficient of a power series are the same. -/
theorem sub_const_eq_shift_mul_X (φ : PowerSeries R) :
    φ - c R (constantCoeff R φ) = (PowerSeries.mk fun p => coeff R (p + 1) φ) * X :=
  sub_eq_iff_eq_add.mpr (eq_shift_mul_X_add_const φ)

theorem sub_const_eq_X_mul_shift (φ : PowerSeries R) :
    φ - c R (constantCoeff R φ) = X * PowerSeries.mk fun p => coeff R (p + 1) φ :=
  sub_eq_iff_eq_add.mpr (eq_X_mul_shift_add_const φ)

end Ringₓ

section CommRingₓ

variable {A : Type _} [CommRingₓ A]

@[simp]
theorem rescale_X (a : A) : rescale a x = c A a * X := by
  ext
  simp only [← coeff_rescale, ← coeff_C_mul, ← coeff_X]
  split_ifs with h <;> simp [← h]

theorem rescale_neg_one_X : rescale (-1 : A) x = -X := by
  rw [rescale_X, map_neg, map_one, neg_one_mul]

/-- The ring homomorphism taking a power series `f(X)` to `f(-X)`. -/
noncomputable def evalNegHom : PowerSeries A →+* PowerSeries A :=
  rescale (-1 : A)

@[simp]
theorem eval_neg_hom_X : evalNegHom (x : PowerSeries A) = -X :=
  rescale_neg_one_X

end CommRingₓ

section Domain

variable [Ringₓ R] [IsDomain R]

theorem eq_zero_or_eq_zero_of_mul_eq_zero (φ ψ : PowerSeries R) (h : φ * ψ = 0) : φ = 0 ∨ ψ = 0 := by
  rw [or_iff_not_imp_left]
  intro H
  have ex : ∃ m, coeff R m φ ≠ 0 := by
    contrapose! H
    exact ext H
  let m := Nat.findₓ ex
  have hm₁ : coeff R m φ ≠ 0 := Nat.find_specₓ ex
  have hm₂ : ∀, ∀ k < m, ∀, ¬coeff R k φ ≠ 0 := fun k => Nat.find_minₓ ex
  ext n
  rw [(coeff R n).map_zero]
  apply Nat.strong_induction_onₓ n
  clear n
  intro n ih
  replace h := congr_arg (coeff R (m + n)) h
  rw [LinearMap.map_zero, coeff_mul, Finset.sum_eq_single (m, n)] at h
  · replace h := eq_zero_or_eq_zero_of_mul_eq_zero h
    rw [or_iff_not_imp_left] at h
    exact h hm₁
    
  · rintro ⟨i, j⟩ hij hne
    by_cases' hj : j < n
    · rw [ih j hj, mul_zero]
      
    by_cases' hi : i < m
    · specialize hm₂ _ hi
      push_neg  at hm₂
      rw [hm₂, zero_mul]
      
    rw [Finset.Nat.mem_antidiagonal] at hij
    push_neg  at hi hj
    suffices m < i by
      have : m + n < i + j := add_lt_add_of_lt_of_le this hj
      exfalso
      exact ne_of_ltₓ this hij.symm
    contrapose! hne
    obtain rfl := le_antisymmₓ hi hne
    simpa [← Ne.def, ← Prod.mk.inj_iff] using (add_right_injₓ m).mp hij
    
  · contrapose!
    intro h
    rw [Finset.Nat.mem_antidiagonal]
    

instance : IsDomain (PowerSeries R) :=
  { PowerSeries.nontrivial with eq_zero_or_eq_zero_of_mul_eq_zero := eq_zero_or_eq_zero_of_mul_eq_zero }

end Domain

section IsDomain

variable [CommRingₓ R] [IsDomain R]

/-- The ideal spanned by the variable in the power series ring
 over an integral domain is a prime ideal.-/
theorem span_X_is_prime : (Ideal.span ({x} : Set (PowerSeries R))).IsPrime := by
  suffices Ideal.span ({X} : Set (PowerSeries R)) = (constant_coeff R).ker by
    rw [this]
    exact RingHom.ker_is_prime _
  apply Ideal.ext
  intro φ
  rw [RingHom.mem_ker, Ideal.mem_span_singleton, X_dvd_iff]

/-- The variable of the power series ring over an integral domain is prime.-/
theorem X_prime : Prime (x : PowerSeries R) := by
  rw [← Ideal.span_singleton_prime]
  · exact span_X_is_prime
    
  · intro h
    simpa using congr_arg (coeff R 1) h
    

theorem rescale_injective {a : R} (ha : a ≠ 0) : Function.Injective (rescale a) := by
  intro p q h
  rw [PowerSeries.ext_iff] at *
  intro n
  specialize h n
  rw [coeff_rescale, coeff_rescale, mul_eq_mul_left_iff] at h
  apply h.resolve_right
  intro h'
  exact ha (pow_eq_zero h')

end IsDomain

section LocalRing

variable {S : Type _} [CommRingₓ R] [CommRingₓ S] (f : R →+* S) [IsLocalRingHom f]

instance map.is_local_ring_hom : IsLocalRingHom (map f) :=
  MvPowerSeries.map.is_local_ring_hom f

variable [LocalRing R] [LocalRing S]

instance : LocalRing (PowerSeries R) :=
  MvPowerSeries.local_ring

end LocalRing

section Algebra

variable {A : Type _} [CommSemiringₓ R] [Semiringₓ A] [Algebra R A]

theorem C_eq_algebra_map {r : R} : c R r = (algebraMap R (PowerSeries R)) r :=
  rfl

theorem algebra_map_apply {r : R} : algebraMap R (PowerSeries A) r = c A (algebraMap R A r) :=
  MvPowerSeries.algebra_map_apply

instance [Nontrivial R] : Nontrivial (Subalgebra R (PowerSeries R)) :=
  MvPowerSeries.Subalgebra.nontrivial

end Algebra

section Field

variable {k : Type _} [Field k]

/-- The inverse 1/f of a power series f defined over a field -/
protected def inv : PowerSeries k → PowerSeries k :=
  MvPowerSeries.inv

instance : Inv (PowerSeries k) :=
  ⟨PowerSeries.inv⟩

theorem inv_eq_inv_aux (φ : PowerSeries k) : φ⁻¹ = Inv.aux (constantCoeff k φ)⁻¹ φ :=
  rfl

theorem coeff_inv (n) (φ : PowerSeries k) :
    coeff k n φ⁻¹ =
      if n = 0 then (constantCoeff k φ)⁻¹
      else
        -(constantCoeff k φ)⁻¹ *
          ∑ x in Finset.Nat.antidiagonal n, if x.2 < n then coeff k x.1 φ * coeff k x.2 φ⁻¹ else 0 :=
  by
  rw [inv_eq_inv_aux, coeff_inv_aux n (constant_coeff k φ)⁻¹ φ]

@[simp]
theorem constant_coeff_inv (φ : PowerSeries k) : constantCoeff k φ⁻¹ = (constantCoeff k φ)⁻¹ :=
  MvPowerSeries.constant_coeff_inv φ

theorem inv_eq_zero {φ : PowerSeries k} : φ⁻¹ = 0 ↔ constantCoeff k φ = 0 :=
  MvPowerSeries.inv_eq_zero

@[simp]
theorem zero_inv : (0 : PowerSeries k)⁻¹ = 0 :=
  MvPowerSeries.zero_inv

@[simp]
theorem inv_of_unit_eq (φ : PowerSeries k) (h : constantCoeff k φ ≠ 0) : invOfUnit φ (Units.mk0 _ h) = φ⁻¹ :=
  MvPowerSeries.inv_of_unit_eq _ _

@[simp]
theorem inv_of_unit_eq' (φ : PowerSeries k) (u : Units k) (h : constantCoeff k φ = u) : invOfUnit φ u = φ⁻¹ :=
  MvPowerSeries.inv_of_unit_eq' φ _ h

@[simp]
protected theorem mul_inv_cancel (φ : PowerSeries k) (h : constantCoeff k φ ≠ 0) : φ * φ⁻¹ = 1 :=
  MvPowerSeries.mul_inv_cancel φ h

@[simp]
protected theorem inv_mul_cancel (φ : PowerSeries k) (h : constantCoeff k φ ≠ 0) : φ⁻¹ * φ = 1 :=
  MvPowerSeries.inv_mul_cancel φ h

theorem eq_mul_inv_iff_mul_eq {φ₁ φ₂ φ₃ : PowerSeries k} (h : constantCoeff k φ₃ ≠ 0) : φ₁ = φ₂ * φ₃⁻¹ ↔ φ₁ * φ₃ = φ₂ :=
  MvPowerSeries.eq_mul_inv_iff_mul_eq h

theorem eq_inv_iff_mul_eq_one {φ ψ : PowerSeries k} (h : constantCoeff k ψ ≠ 0) : φ = ψ⁻¹ ↔ φ * ψ = 1 :=
  MvPowerSeries.eq_inv_iff_mul_eq_one h

theorem inv_eq_iff_mul_eq_one {φ ψ : PowerSeries k} (h : constantCoeff k ψ ≠ 0) : ψ⁻¹ = φ ↔ φ * ψ = 1 :=
  MvPowerSeries.inv_eq_iff_mul_eq_one h

@[simp]
protected theorem mul_inv_rev (φ ψ : PowerSeries k) : (φ * ψ)⁻¹ = ψ⁻¹ * φ⁻¹ :=
  MvPowerSeries.mul_inv_rev _ _

@[simp]
theorem inv_one : (1 : PowerSeries k)⁻¹ = 1 :=
  MvPowerSeries.inv_one

@[simp]
theorem C_inv (r : k) : (c k r)⁻¹ = c k r⁻¹ :=
  MvPowerSeries.C_inv _

@[simp]
theorem X_inv : (x : PowerSeries k)⁻¹ = 0 :=
  MvPowerSeries.X_inv _

@[simp]
theorem smul_inv (r : k) (φ : PowerSeries k) : (r • φ)⁻¹ = r⁻¹ • φ⁻¹ :=
  MvPowerSeries.smul_inv _ _

end Field

end PowerSeries

namespace PowerSeries

variable {R : Type _}

attribute [local instance] Classical.propDecidable

noncomputable section

section OrderBasic

open multiplicity

variable [Semiringₓ R] {φ : PowerSeries R}

theorem exists_coeff_ne_zero_iff_ne_zero : (∃ n : ℕ, coeff R n φ ≠ 0) ↔ φ ≠ 0 := by
  refine' not_iff_not.mp _
  push_neg
  simp [← PowerSeries.ext_iff]

/-- The order of a formal power series `φ` is the greatest `n : part_enat`
such that `X^n` divides `φ`. The order is `⊤` if and only if `φ = 0`. -/
def order (φ : PowerSeries R) : PartEnat :=
  if h : φ = 0 then ⊤ else Nat.findₓ (exists_coeff_ne_zero_iff_ne_zero.mpr h)

/-- The order of the `0` power series is infinite.-/
@[simp]
theorem order_zero : order (0 : PowerSeries R) = ⊤ :=
  dif_pos rfl

theorem order_finite_iff_ne_zero : (order φ).Dom ↔ φ ≠ 0 := by
  simp only [← order]
  constructor
  · split_ifs with h h <;> intro H
    · contrapose! H
      simpa [Part.eq_none_iff']
      
    · exact h
      
    
  · intro h
    simp [← h]
    

/-- If the order of a formal power series is finite,
then the coefficient indexed by the order is nonzero.-/
theorem coeff_order (h : (order φ).Dom) : coeff R (φ.order.get h) φ ≠ 0 := by
  simp only [← order, ← order_finite_iff_ne_zero.mp h, ← not_false_iff, ← dif_neg, ← PartEnat.get_coe']
  generalize_proofs h
  exact Nat.find_specₓ h

/-- If the `n`th coefficient of a formal power series is nonzero,
then the order of the power series is less than or equal to `n`.-/
theorem order_le (n : ℕ) (h : coeff R n φ ≠ 0) : order φ ≤ n := by
  have := Exists.introₓ n h
  rw [order, dif_neg]
  · simp only [← PartEnat.coe_le_coe, ← Nat.find_le_iff]
    exact ⟨n, le_rfl, h⟩
    
  · exact exists_coeff_ne_zero_iff_ne_zero.mp ⟨n, h⟩
    

/-- The `n`th coefficient of a formal power series is `0` if `n` is strictly
smaller than the order of the power series.-/
theorem coeff_of_lt_order (n : ℕ) (h : ↑n < order φ) : coeff R n φ = 0 := by
  contrapose! h
  exact order_le _ h

/-- The `0` power series is the unique power series with infinite order.-/
@[simp]
theorem order_eq_top {φ : PowerSeries R} : φ.order = ⊤ ↔ φ = 0 := by
  constructor
  · intro h
    ext n
    rw [(coeff R n).map_zero, coeff_of_lt_order]
    simp [← h]
    
  · rintro rfl
    exact order_zero
    

/-- The order of a formal power series is at least `n` if
the `i`th coefficient is `0` for all `i < n`.-/
theorem nat_le_order (φ : PowerSeries R) (n : ℕ) (h : ∀, ∀ i < n, ∀, coeff R i φ = 0) : ↑n ≤ order φ := by
  by_contra H
  rw [not_leₓ] at H
  have : (order φ).Dom := PartEnat.dom_of_le_coe H.le
  rw [← PartEnat.coe_get this, PartEnat.coe_lt_coe] at H
  exact coeff_order this (h _ H)

/-- The order of a formal power series is at least `n` if
the `i`th coefficient is `0` for all `i < n`.-/
theorem le_order (φ : PowerSeries R) (n : PartEnat) (h : ∀ i : ℕ, ↑i < n → coeff R i φ = 0) : n ≤ order φ := by
  induction n using PartEnat.cases_on
  · show _ ≤ _
    rw [top_le_iff, order_eq_top]
    ext i
    exact h _ (PartEnat.coe_lt_top i)
    
  · apply nat_le_order
    simpa only [← PartEnat.coe_lt_coe] using h
    

/-- The order of a formal power series is exactly `n` if the `n`th coefficient is nonzero,
and the `i`th coefficient is `0` for all `i < n`.-/
theorem order_eq_nat {φ : PowerSeries R} {n : ℕ} : order φ = n ↔ coeff R n φ ≠ 0 ∧ ∀ i, i < n → coeff R i φ = 0 := by
  rcases eq_or_ne φ 0 with (rfl | hφ)
  · simpa using (PartEnat.coe_ne_top _).symm
    
  simp [← order, ← dif_neg hφ, ← Nat.find_eq_iff]

/-- The order of a formal power series is exactly `n` if the `n`th coefficient is nonzero,
and the `i`th coefficient is `0` for all `i < n`.-/
theorem order_eq {φ : PowerSeries R} {n : PartEnat} :
    order φ = n ↔ (∀ i : ℕ, ↑i = n → coeff R i φ ≠ 0) ∧ ∀ i : ℕ, ↑i < n → coeff R i φ = 0 := by
  induction n using PartEnat.cases_on
  · rw [order_eq_top]
    constructor
    · rintro rfl
      constructor <;> intros
      · exfalso
        exact PartEnat.coe_ne_top ‹_› ‹_›
        
      · exact (coeff _ _).map_zero
        
      
    · rintro ⟨h₁, h₂⟩
      ext i
      exact h₂ i (PartEnat.coe_lt_top i)
      
    
  · simpa [← PartEnat.coe_inj] using order_eq_nat
    

/-- The order of the sum of two formal power series
 is at least the minimum of their orders.-/
theorem le_order_add (φ ψ : PowerSeries R) : min (order φ) (order ψ) ≤ order (φ + ψ) := by
  refine' le_order _ _ _
  simp (config := { contextual := true })[← coeff_of_lt_order]

private theorem order_add_of_order_eq.aux (φ ψ : PowerSeries R) (h : order φ ≠ order ψ) (H : order φ < order ψ) :
    order (φ + ψ) ≤ order φ⊓order ψ := by
  suffices order (φ + ψ) = order φ by
    rw [le_inf_iff, this]
    exact ⟨le_rfl, le_of_ltₓ H⟩
  · rw [order_eq]
    constructor
    · intro i hi
      rw [← hi] at H
      rw [(coeff _ _).map_add, coeff_of_lt_order i H, add_zeroₓ]
      exact (order_eq_nat.1 hi.symm).1
      
    · intro i hi
      rw [(coeff _ _).map_add, coeff_of_lt_order i hi, coeff_of_lt_order i (lt_transₓ hi H), zero_addₓ]
      
    

/-- The order of the sum of two formal power series
 is the minimum of their orders if their orders differ.-/
theorem order_add_of_order_eq (φ ψ : PowerSeries R) (h : order φ ≠ order ψ) : order (φ + ψ) = order φ⊓order ψ := by
  refine' le_antisymmₓ _ (le_order_add _ _)
  by_cases' H₁ : order φ < order ψ
  · apply order_add_of_order_eq.aux _ _ h H₁
    
  by_cases' H₂ : order ψ < order φ
  · simpa only [← add_commₓ, ← inf_comm] using order_add_of_order_eq.aux _ _ h.symm H₂
    
  exfalso
  exact h (le_antisymmₓ (not_ltₓ.1 H₂) (not_ltₓ.1 H₁))

/-- The order of the product of two formal power series
 is at least the sum of their orders.-/
theorem order_mul_ge (φ ψ : PowerSeries R) : order φ + order ψ ≤ order (φ * ψ) := by
  apply le_order
  intro n hn
  rw [coeff_mul, Finset.sum_eq_zero]
  rintro ⟨i, j⟩ hij
  by_cases' hi : ↑i < order φ
  · rw [coeff_of_lt_order i hi, zero_mul]
    
  by_cases' hj : ↑j < order ψ
  · rw [coeff_of_lt_order j hj, mul_zero]
    
  rw [not_ltₓ] at hi hj
  rw [Finset.Nat.mem_antidiagonal] at hij
  exfalso
  apply ne_of_ltₓ (lt_of_lt_of_leₓ hn <| add_le_add hi hj)
  rw [← Nat.cast_addₓ, hij]

/-- The order of the monomial `a*X^n` is infinite if `a = 0` and `n` otherwise.-/
theorem order_monomial (n : ℕ) (a : R) [Decidable (a = 0)] : order (monomial R n a) = if a = 0 then ⊤ else n := by
  split_ifs with h
  · rw [h, order_eq_top, LinearMap.map_zero]
    
  · rw [order_eq]
    constructor <;> intro i hi
    · rw [PartEnat.coe_inj] at hi
      rwa [hi, coeff_monomial_same]
      
    · rw [PartEnat.coe_lt_coe] at hi
      rw [coeff_monomial, if_neg]
      exact ne_of_ltₓ hi
      
    

/-- The order of the monomial `a*X^n` is `n` if `a ≠ 0`.-/
theorem order_monomial_of_ne_zero (n : ℕ) (a : R) (h : a ≠ 0) : order (monomial R n a) = n := by
  rw [order_monomial, if_neg h]

/-- If `n` is strictly smaller than the order of `ψ`, then the `n`th coefficient of its product
with any other power series is `0`. -/
theorem coeff_mul_of_lt_order {φ ψ : PowerSeries R} {n : ℕ} (h : ↑n < ψ.order) : coeff R n (φ * ψ) = 0 := by
  suffices : coeff R n (φ * ψ) = ∑ p in Finset.Nat.antidiagonal n, 0
  rw [this, Finset.sum_const_zero]
  rw [coeff_mul]
  apply Finset.sum_congr rfl fun x hx => _
  refine' mul_eq_zero_of_right (coeff R x.fst φ) (coeff_of_lt_order x.snd (lt_of_le_of_ltₓ _ h))
  rw [Finset.Nat.mem_antidiagonal] at hx
  norm_cast
  linarith

theorem coeff_mul_one_sub_of_lt_order {R : Type _} [CommRingₓ R] {φ ψ : PowerSeries R} (n : ℕ) (h : ↑n < ψ.order) :
    coeff R n (φ * (1 - ψ)) = coeff R n φ := by
  simp [← coeff_mul_of_lt_order h, ← mul_sub]

theorem coeff_mul_prod_one_sub_of_lt_order {R ι : Type _} [CommRingₓ R] (k : ℕ) (s : Finset ι) (φ : PowerSeries R)
    (f : ι → PowerSeries R) : (∀, ∀ i ∈ s, ∀, ↑k < (f i).order) → coeff R k (φ * ∏ i in s, 1 - f i) = coeff R k φ := by
  apply Finset.induction_on s
  · simp
    
  · intro a s ha ih t
    simp only [← Finset.mem_insert, ← forall_eq_or_imp] at t
    rw [Finset.prod_insert ha, ← mul_assoc, mul_right_commₓ, coeff_mul_one_sub_of_lt_order _ t.1]
    exact ih t.2
    

-- TODO: link with `X_pow_dvd_iff`
theorem X_pow_order_dvd (h : (order φ).Dom) : X ^ (order φ).get h ∣ φ := by
  refine' ⟨PowerSeries.mk fun n => coeff R (n + (order φ).get h) φ, _⟩
  ext n
  simp only [← coeff_mul, ← coeff_X_pow, ← coeff_mk, ← boole_mul, ← Finset.sum_ite, ←
    Finset.Nat.filter_fst_eq_antidiagonal, ← Finset.sum_const_zero, ← add_zeroₓ]
  split_ifs with hn hn
  · simp [← tsub_add_cancel_of_le hn]
    
  · simp only [← Finset.sum_empty]
    refine' coeff_of_lt_order _ _
    simpa [← PartEnat.coe_lt_iff] using fun _ => hn
    

theorem order_eq_multiplicity_X {R : Type _} [CommSemiringₓ R] (φ : PowerSeries R) : order φ = multiplicity x φ := by
  rcases eq_or_ne φ 0 with (rfl | hφ)
  · simp
    
  induction' ho : order φ using PartEnat.cases_on with n
  · simpa [← hφ] using ho
    
  have hn : φ.order.get (order_finite_iff_ne_zero.mpr hφ) = n := by
    simp [← ho]
  rw [← hn]
  refine'
    le_antisymmₓ (le_multiplicity_of_pow_dvd <| X_pow_order_dvd (order_finite_iff_ne_zero.mpr hφ))
      (PartEnat.find_le _ _ _)
  rintro ⟨ψ, H⟩
  have := congr_arg (coeff R n) H
  rw [mul_comm, coeff_mul_of_lt_order, ← hn] at this
  · exact coeff_order _ this
    
  · rw [X_pow_eq, order_monomial]
    split_ifs
    · exact PartEnat.coe_lt_top _
      
    · rw [← hn, PartEnat.coe_lt_coe]
      exact Nat.lt_succ_selfₓ _
      
    

end OrderBasic

section OrderZeroNeOne

variable [Semiringₓ R] [Nontrivial R]

/-- The order of the formal power series `1` is `0`.-/
@[simp]
theorem order_one : order (1 : PowerSeries R) = 0 := by
  simpa using order_monomial_of_ne_zero 0 (1 : R) one_ne_zero

/-- The order of the formal power series `X` is `1`.-/
@[simp]
theorem order_X : order (x : PowerSeries R) = 1 := by
  simpa only [← Nat.cast_oneₓ] using order_monomial_of_ne_zero 1 (1 : R) one_ne_zero

/-- The order of the formal power series `X^n` is `n`.-/
@[simp]
theorem order_X_pow (n : ℕ) : order ((x : PowerSeries R) ^ n) = n := by
  rw [X_pow_eq, order_monomial_of_ne_zero]
  exact one_ne_zero

end OrderZeroNeOne

section OrderIsDomain

-- TODO: generalize to `[semiring R] [no_zero_divisors R]`
variable [CommRingₓ R] [IsDomain R]

/-- The order of the product of two formal power series over an integral domain
 is the sum of their orders.-/
theorem order_mul (φ ψ : PowerSeries R) : order (φ * ψ) = order φ + order ψ := by
  simp_rw [order_eq_multiplicity_X]
  exact multiplicity.mul X_prime

end OrderIsDomain

end PowerSeries

namespace Polynomial

open Finsupp

variable {σ : Type _} {R : Type _} [CommSemiringₓ R] (φ ψ : R[X])

/-- The natural inclusion from polynomials into formal power series.-/
instance coeToPowerSeries : Coe R[X] (PowerSeries R) :=
  ⟨fun φ => PowerSeries.mk fun n => coeff φ n⟩

theorem coe_def : (φ : PowerSeries R) = PowerSeries.mk (coeff φ) :=
  rfl

@[simp, norm_cast]
theorem coeff_coe (n) : PowerSeries.coeff R n φ = coeff φ n :=
  congr_arg (coeff φ) Finsupp.single_eq_same

@[simp, norm_cast]
theorem coe_monomial (n : ℕ) (a : R) : (monomial n a : PowerSeries R) = PowerSeries.monomial R n a := by
  ext
  simp [← coeff_coe, ← PowerSeries.coeff_monomial, ← Polynomial.coeff_monomial, ← eq_comm]

@[simp, norm_cast]
theorem coe_zero : ((0 : R[X]) : PowerSeries R) = 0 :=
  rfl

@[simp, norm_cast]
theorem coe_one : ((1 : R[X]) : PowerSeries R) = 1 := by
  have := coe_monomial 0 (1 : R)
  rwa [PowerSeries.monomial_zero_eq_C_apply] at this

@[simp, norm_cast]
theorem coe_add : ((φ + ψ : R[X]) : PowerSeries R) = φ + ψ := by
  ext
  simp

@[simp, norm_cast]
theorem coe_mul : ((φ * ψ : R[X]) : PowerSeries R) = φ * ψ :=
  PowerSeries.ext fun n => by
    simp only [← coeff_coe, ← PowerSeries.coeff_mul, ← coeff_mul]

@[simp, norm_cast]
theorem coe_C (a : R) : ((c a : R[X]) : PowerSeries R) = PowerSeries.c R a := by
  have := coe_monomial 0 a
  rwa [PowerSeries.monomial_zero_eq_C_apply] at this

@[simp, norm_cast]
theorem coe_bit0 : ((bit0 φ : R[X]) : PowerSeries R) = bit0 (φ : PowerSeries R) :=
  coe_add φ φ

@[simp, norm_cast]
theorem coe_bit1 : ((bit1 φ : R[X]) : PowerSeries R) = bit1 (φ : PowerSeries R) := by
  rw [bit1, bit1, coe_add, coe_one, coe_bit0]

@[simp, norm_cast]
theorem coe_X : ((x : R[X]) : PowerSeries R) = PowerSeries.x :=
  coe_monomial _ _

@[simp]
theorem constant_coeff_coe : PowerSeries.constantCoeff R φ = φ.coeff 0 :=
  rfl

variable (R)

theorem coe_injective : Function.Injective (coe : R[X] → PowerSeries R) := fun x y h => by
  ext
  simp_rw [← coeff_coe, h]

variable {R φ ψ}

@[simp, norm_cast]
theorem coe_inj : (φ : PowerSeries R) = ψ ↔ φ = ψ :=
  (coe_injective R).eq_iff

@[simp]
theorem coe_eq_zero_iff : (φ : PowerSeries R) = 0 ↔ φ = 0 := by
  rw [← coe_zero, coe_inj]

@[simp]
theorem coe_eq_one_iff : (φ : PowerSeries R) = 1 ↔ φ = 1 := by
  rw [← coe_one, coe_inj]

variable (φ ψ)

/-- The coercion from polynomials to power series
as a ring homomorphism.
-/
def coeToPowerSeries.ringHom : R[X] →+* PowerSeries R where
  toFun := (coe : R[X] → PowerSeries R)
  map_zero' := coe_zero
  map_one' := coe_one
  map_add' := coe_add
  map_mul' := coe_mul

@[simp]
theorem coeToPowerSeries.ring_hom_apply : coeToPowerSeries.ringHom φ = φ :=
  rfl

@[simp, norm_cast]
theorem coe_pow (n : ℕ) : ((φ ^ n : R[X]) : PowerSeries R) = (φ : PowerSeries R) ^ n :=
  coeToPowerSeries.ringHom.map_pow _ _

variable (A : Type _) [Semiringₓ A] [Algebra R A]

/-- The coercion from polynomials to power series
as an algebra homomorphism.
-/
def coeToPowerSeries.algHom : R[X] →ₐ[R] PowerSeries A :=
  { (PowerSeries.map (algebraMap R A)).comp coeToPowerSeries.ringHom with
    commutes' := fun r => by
      simp [← algebra_map_apply, ← PowerSeries.algebra_map_apply] }

@[simp]
theorem coeToPowerSeries.alg_hom_apply : coeToPowerSeries.algHom A φ = PowerSeries.map (algebraMap R A) ↑φ :=
  rfl

end Polynomial

namespace PowerSeries

variable {R A : Type _} [CommSemiringₓ R] [CommSemiringₓ A] [Algebra R A] (f : PowerSeries R)

instance algebraPolynomial : Algebra R[X] (PowerSeries A) :=
  RingHom.toAlgebra (Polynomial.coeToPowerSeries.algHom A).toRingHom

instance algebraPowerSeries : Algebra (PowerSeries R) (PowerSeries A) :=
  (map (algebraMap R A)).toAlgebra

-- see Note [lower instance priority]
instance (priority := 100) algebraPolynomial' {A : Type _} [CommSemiringₓ A] [Algebra R (Polynomial A)] :
    Algebra R (PowerSeries A) :=
  RingHom.toAlgebra <| Polynomial.coeToPowerSeries.ringHom.comp (algebraMap R (Polynomial A))

variable (A)

theorem algebra_map_apply' (p : R[X]) : algebraMap R[X] (PowerSeries A) p = map (algebraMap R A) p :=
  rfl

theorem algebra_map_apply'' : algebraMap (PowerSeries R) (PowerSeries A) f = map (algebraMap R A) f :=
  rfl

end PowerSeries

