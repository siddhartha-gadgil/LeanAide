/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Johan Commelin, Mario Carneiro
-/
import Mathbin.RingTheory.Adjoin.Basic
import Mathbin.Data.Finsupp.Antidiagonal
import Mathbin.Algebra.MonoidAlgebra.Basic
import Mathbin.Order.SymmDiff

/-!
# Multivariate polynomials

This file defines polynomial rings over a base ring (or even semiring),
with variables from a general type `σ` (which could be infinite).

## Important definitions

Let `R` be a commutative ring (or a semiring) and let `σ` be an arbitrary
type. This file creates the type `mv_polynomial σ R`, which mathematicians
might denote $R[X_i : i \in σ]$. It is the type of multivariate
(a.k.a. multivariable) polynomials, with variables
corresponding to the terms in `σ`, and coefficients in `R`.

### Notation

In the definitions below, we use the following notation:

+ `σ : Type*` (indexing the variables)

+ `R : Type*` `[comm_semiring R]` (the coefficients)

+ `s : σ →₀ ℕ`, a function from `σ` to `ℕ` which is zero away from a finite set.
This will give rise to a monomial in `mv_polynomial σ R` which mathematicians might call `X^s`

+ `a : R`

+ `i : σ`, with corresponding monomial `X i`, often denoted `X_i` by mathematicians

+ `p : mv_polynomial σ R`

### Definitions

* `mv_polynomial σ R` : the type of polynomials with variables of type `σ` and coefficients
  in the commutative semiring `R`

* `monomial s a` : the monomial which mathematically would be denoted `a * X^s`

* `C a` : the constant polynomial with value `a`

* `X i` : the degree one monomial corresponding to i; mathematically this might be denoted `Xᵢ`.

* `coeff s p` : the coefficient of `s` in `p`.

* `eval₂ (f : R → S₁) (g : σ → S₁) p` : given a semiring homomorphism from `R` to another
  semiring `S₁`, and a map `σ → S₁`, evaluates `p` at this valuation, returning a term of type `S₁`.
  Note that `eval₂` can be made using `eval` and `map` (see below), and it has been suggested
  that sticking to `eval` and `map` might make the code less brittle.

* `eval (g : σ → R) p` : given a map `σ → R`, evaluates `p` at this valuation,
  returning a term of type `R`

* `map (f : R → S₁) p` : returns the multivariate polynomial obtained from `p` by the change of
  coefficient semiring corresponding to `f`

## Implementation notes

Recall that if `Y` has a zero, then `X →₀ Y` is the type of functions from `X` to `Y` with finite
support, i.e. such that only finitely many elements of `X` get sent to non-zero terms in `Y`.
The definition of `mv_polynomial σ R` is `(σ →₀ ℕ) →₀ R` ; here `σ →₀ ℕ` denotes the space of all
monomials in the variables, and the function to `R` sends a monomial to its coefficient in
the polynomial being represented.

## Tags

polynomial, multivariate polynomial, multivariable polynomial

-/


noncomputable section

open Classical BigOperators

open Set Function Finsupp AddMonoidAlgebra

open BigOperators

universe u v w x

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

/-- Multivariate polynomial, where `σ` is the index set of the variables and
  `R` is the coefficient ring -/
def MvPolynomial (σ : Type _) (R : Type _) [CommSemiringₓ R] :=
  AddMonoidAlgebra R (σ →₀ ℕ)

namespace MvPolynomial

variable {σ : Type _} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

section CommSemiringₓ

section Instances

instance decidableEqMvPolynomial [CommSemiringₓ R] [DecidableEq σ] [DecidableEq R] : DecidableEq (MvPolynomial σ R) :=
  Finsupp.decidableEq

instance [CommSemiringₓ R] : CommSemiringₓ (MvPolynomial σ R) :=
  AddMonoidAlgebra.commSemiring

instance [CommSemiringₓ R] : Inhabited (MvPolynomial σ R) :=
  ⟨0⟩

instance [Monoidₓ R] [CommSemiringₓ S₁] [DistribMulAction R S₁] : DistribMulAction R (MvPolynomial σ S₁) :=
  AddMonoidAlgebra.distribMulAction

instance [Monoidₓ R] [CommSemiringₓ S₁] [DistribMulAction R S₁] [HasFaithfulSmul R S₁] :
    HasFaithfulSmul R (MvPolynomial σ S₁) :=
  AddMonoidAlgebra.has_faithful_smul

instance [Semiringₓ R] [CommSemiringₓ S₁] [Module R S₁] : Module R (MvPolynomial σ S₁) :=
  AddMonoidAlgebra.module

instance [Monoidₓ R] [Monoidₓ S₁] [CommSemiringₓ S₂] [HasSmul R S₁] [DistribMulAction R S₂] [DistribMulAction S₁ S₂]
    [IsScalarTower R S₁ S₂] : IsScalarTower R S₁ (MvPolynomial σ S₂) :=
  AddMonoidAlgebra.is_scalar_tower

instance [Monoidₓ R] [Monoidₓ S₁] [CommSemiringₓ S₂] [DistribMulAction R S₂] [DistribMulAction S₁ S₂]
    [SmulCommClass R S₁ S₂] : SmulCommClass R S₁ (MvPolynomial σ S₂) :=
  AddMonoidAlgebra.smul_comm_class

instance [Monoidₓ R] [CommSemiringₓ S₁] [DistribMulAction R S₁] [DistribMulAction Rᵐᵒᵖ S₁] [IsCentralScalar R S₁] :
    IsCentralScalar R (MvPolynomial σ S₁) :=
  AddMonoidAlgebra.is_central_scalar

instance [CommSemiringₓ R] [CommSemiringₓ S₁] [Algebra R S₁] : Algebra R (MvPolynomial σ S₁) :=
  AddMonoidAlgebra.algebra

-- Register with high priority to avoid timeout in `data.mv_polynomial.pderiv`
instance is_scalar_tower' [CommSemiringₓ R] [CommSemiringₓ S₁] [Algebra R S₁] :
    IsScalarTower R (MvPolynomial σ S₁) (MvPolynomial σ S₁) :=
  IsScalarTower.right

/-- If `R` is a subsingleton, then `mv_polynomial σ R` has a unique element -/
-- TODO[gh-6025]: make this an instance once safe to do so
protected def unique [CommSemiringₓ R] [Subsingleton R] : Unique (MvPolynomial σ R) :=
  AddMonoidAlgebra.unique

end Instances

variable [CommSemiringₓ R] [CommSemiringₓ S₁] {p q : MvPolynomial σ R}

/-- `monomial s a` is the monomial with coefficient `a` and exponents given by `s`  -/
def monomial (s : σ →₀ ℕ) : R →ₗ[R] MvPolynomial σ R :=
  lsingle s

theorem single_eq_monomial (s : σ →₀ ℕ) (a : R) : single s a = monomial s a :=
  rfl

theorem mul_def : p * q = p.Sum fun m a => q.Sum fun n b => monomial (m + n) (a * b) :=
  rfl

/-- `C a` is the constant polynomial with value `a` -/
def c : R →+* MvPolynomial σ R :=
  { singleZeroRingHom with toFun := monomial 0 }

variable (R σ)

theorem algebra_map_eq : algebraMap R (MvPolynomial σ R) = C :=
  rfl

variable {R σ}

/-- `X n` is the degree `1` monomial $X_n$. -/
def x (n : σ) : MvPolynomial σ R :=
  monomial (single n 1) 1

theorem C_apply : (c a : MvPolynomial σ R) = monomial 0 a :=
  rfl

@[simp]
theorem C_0 : c 0 = (0 : MvPolynomial σ R) := by
  simp [← C_apply, ← monomial]

@[simp]
theorem C_1 : c 1 = (1 : MvPolynomial σ R) :=
  rfl

theorem C_mul_monomial : c a * monomial s a' = monomial s (a * a') := by
  simp [← C_apply, ← monomial, ← single_mul_single]

@[simp]
theorem C_add : (c (a + a') : MvPolynomial σ R) = c a + c a' :=
  single_add _ _ _

@[simp]
theorem C_mul : (c (a * a') : MvPolynomial σ R) = c a * c a' :=
  C_mul_monomial.symm

@[simp]
theorem C_pow (a : R) (n : ℕ) : (c (a ^ n) : MvPolynomial σ R) = c a ^ n := by
  induction n <;> simp [← pow_succₓ, *]

theorem C_injective (σ : Type _) (R : Type _) [CommSemiringₓ R] : Function.Injective (c : R → MvPolynomial σ R) :=
  Finsupp.single_injective _

theorem C_surjective {R : Type _} [CommSemiringₓ R] (σ : Type _) [IsEmpty σ] :
    Function.Surjective (c : R → MvPolynomial σ R) := by
  refine' fun p => ⟨p.toFun 0, Finsupp.ext fun a => _⟩
  simpa [← (Finsupp.ext isEmptyElim : a = 0), ← C_apply, ← monomial]

@[simp]
theorem C_inj {σ : Type _} (R : Type _) [CommSemiringₓ R] (r s : R) : (c r : MvPolynomial σ R) = c s ↔ r = s :=
  (C_injective σ R).eq_iff

instance infinite_of_infinite (σ : Type _) (R : Type _) [CommSemiringₓ R] [Infinite R] : Infinite (MvPolynomial σ R) :=
  Infinite.of_injective c (C_injective _ _)

instance infinite_of_nonempty (σ : Type _) (R : Type _) [Nonempty σ] [CommSemiringₓ R] [Nontrivial R] :
    Infinite (MvPolynomial σ R) :=
  Infinite.of_injective ((fun s : σ →₀ ℕ => monomial s 1) ∘ single (Classical.arbitrary σ)) <|
    Function.Injective.comp (fun m n => (Finsupp.single_left_inj one_ne_zero).mp) (Finsupp.single_injective _)

theorem C_eq_coe_nat (n : ℕ) : (c ↑n : MvPolynomial σ R) = n := by
  induction n <;> simp [← Nat.succ_eq_add_one, *]

theorem C_mul' : MvPolynomial.c a * p = a • p :=
  (Algebra.smul_def a p).symm

theorem smul_eq_C_mul (p : MvPolynomial σ R) (a : R) : a • p = c a * p :=
  C_mul'.symm

theorem C_eq_smul_one : (c a : MvPolynomial σ R) = a • 1 := by
  rw [← C_mul', mul_oneₓ]

theorem monomial_pow : monomial s a ^ e = monomial (e • s) (a ^ e) :=
  AddMonoidAlgebra.single_pow e

@[simp]
theorem monomial_mul {s s' : σ →₀ ℕ} {a b : R} : monomial s a * monomial s' b = monomial (s + s') (a * b) :=
  AddMonoidAlgebra.single_mul_single

variable (σ R)

/-- `λ s, monomial s 1` as a homomorphism. -/
def monomialOneHom : Multiplicative (σ →₀ ℕ) →* MvPolynomial σ R :=
  AddMonoidAlgebra.of _ _

variable {σ R}

@[simp]
theorem monomial_one_hom_apply : monomialOneHom R σ s = (monomial s 1 : MvPolynomial σ R) :=
  rfl

theorem X_pow_eq_monomial : x n ^ e = monomial (single n e) (1 : R) := by
  simp [← X, ← monomial_pow]

theorem monomial_add_single : monomial (s + single n e) a = monomial s a * x n ^ e := by
  rw [X_pow_eq_monomial, monomial_mul, mul_oneₓ]

theorem monomial_single_add : monomial (single n e + s) a = x n ^ e * monomial s a := by
  rw [X_pow_eq_monomial, monomial_mul, one_mulₓ]

theorem monomial_eq_C_mul_X {s : σ} {a : R} {n : ℕ} : monomial (single s n) a = c a * x s ^ n := by
  rw [← zero_addₓ (single s n), monomial_add_single, C_apply]

@[simp]
theorem monomial_zero {s : σ →₀ ℕ} : monomial s (0 : R) = 0 :=
  single_zero _

@[simp]
theorem monomial_zero' : (monomial (0 : σ →₀ ℕ) : R → MvPolynomial σ R) = C :=
  rfl

@[simp]
theorem monomial_eq_zero {s : σ →₀ ℕ} {b : R} : monomial s b = 0 ↔ b = 0 :=
  Finsupp.single_eq_zero

@[simp]
theorem sum_monomial_eq {A : Type _} [AddCommMonoidₓ A] {u : σ →₀ ℕ} {r : R} {b : (σ →₀ ℕ) → R → A} (w : b u 0 = 0) :
    Sum (monomial u r) b = b u r :=
  sum_single_index w

@[simp]
theorem sum_C {A : Type _} [AddCommMonoidₓ A] {b : (σ →₀ ℕ) → R → A} (w : b 0 0 = 0) : Sum (c a) b = b 0 a :=
  sum_monomial_eq w

theorem monomial_sum_one {α : Type _} (s : Finset α) (f : α → σ →₀ ℕ) :
    (monomial (∑ i in s, f i) 1 : MvPolynomial σ R) = ∏ i in s, monomial (f i) 1 :=
  (monomialOneHom R σ).map_prod (fun i => Multiplicative.ofAdd (f i)) s

theorem monomial_sum_index {α : Type _} (s : Finset α) (f : α → σ →₀ ℕ) (a : R) :
    monomial (∑ i in s, f i) a = c a * ∏ i in s, monomial (f i) 1 := by
  rw [← monomial_sum_one, C_mul', ← (monomial _).map_smul, smul_eq_mul, mul_oneₓ]

theorem monomial_finsupp_sum_index {α β : Type _} [Zero β] (f : α →₀ β) (g : α → β → σ →₀ ℕ) (a : R) :
    monomial (f.Sum g) a = c a * f.Prod fun a b => monomial (g a b) 1 :=
  monomial_sum_index _ _ _

theorem monomial_eq_monomial_iff {α : Type _} (a₁ a₂ : α →₀ ℕ) (b₁ b₂ : R) :
    monomial a₁ b₁ = monomial a₂ b₂ ↔ a₁ = a₂ ∧ b₁ = b₂ ∨ b₁ = 0 ∧ b₂ = 0 :=
  Finsupp.single_eq_single_iff _ _ _ _

theorem monomial_eq : monomial s a = c a * (s.Prod fun n e => x n ^ e : MvPolynomial σ R) := by
  simp only [← X_pow_eq_monomial, monomial_finsupp_sum_index, ← Finsupp.sum_single]

theorem induction_on_monomial {M : MvPolynomial σ R → Prop} (h_C : ∀ a, M (c a)) (h_X : ∀ p n, M p → M (p * x n)) :
    ∀ s a, M (monomial s a) := by
  intro s a
  apply @Finsupp.induction σ ℕ _ _ s
  · show M (monomial 0 a)
    exact h_C a
    
  · intro n e p hpn he ih
    have : ∀ e : ℕ, M (monomial p a * X n ^ e) := by
      intro e
      induction e
      · simp [← ih]
        
      · simp [← ih, ← pow_succ'ₓ, ← (mul_assoc _ _ _).symm, ← h_X, ← e_ih]
        
    simp [← add_commₓ, ← monomial_add_single, ← this]
    

/-- Analog of `polynomial.induction_on'`.
To prove something about mv_polynomials,
it suffices to show the condition is closed under taking sums,
and it holds for monomials. -/
@[elab_as_eliminator]
theorem induction_on' {P : MvPolynomial σ R → Prop} (p : MvPolynomial σ R)
    (h1 : ∀ (u : σ →₀ ℕ) (a : R), P (monomial u a)) (h2 : ∀ p q : MvPolynomial σ R, P p → P q → P (p + q)) : P p :=
  Finsupp.induction p
    (suffices P (monomial 0 0) by
      rwa [monomial_zero] at this
    show P (monomial 0 0) from h1 0 0)
    fun a b f ha hb hPf => h2 _ _ (h1 _ _) hPf

/-- Similar to `mv_polynomial.induction_on` but only a weak form of `h_add` is required.-/
theorem induction_on''' {M : MvPolynomial σ R → Prop} (p : MvPolynomial σ R) (h_C : ∀ a, M (c a))
    (h_add_weak : ∀ (a : σ →₀ ℕ) (b : R) (f : (σ →₀ ℕ) →₀ R), a ∉ f.support → b ≠ 0 → M f → M (monomial a b + f)) :
    M p :=
  Finsupp.induction p (C_0.rec <| h_C 0) h_add_weak

/-- Similar to `mv_polynomial.induction_on` but only a yet weaker form of `h_add` is required.-/
theorem induction_on'' {M : MvPolynomial σ R → Prop} (p : MvPolynomial σ R) (h_C : ∀ a, M (c a))
    (h_add_weak :
      ∀ (a : σ →₀ ℕ) (b : R) (f : (σ →₀ ℕ) →₀ R), a ∉ f.support → b ≠ 0 → M f → M (monomial a b) → M (monomial a b + f))
    (h_X : ∀ (p : MvPolynomial σ R) (n : σ), M p → M (p * MvPolynomial.x n)) : M p :=
  induction_on''' p h_C fun a b f ha hb hf => h_add_weak a b f ha hb hf <| induction_on_monomial h_C h_X a b

/-- Analog of `polynomial.induction_on`.-/
@[recursor 5]
theorem induction_on {M : MvPolynomial σ R → Prop} (p : MvPolynomial σ R) (h_C : ∀ a, M (c a))
    (h_add : ∀ p q, M p → M q → M (p + q)) (h_X : ∀ p n, M p → M (p * x n)) : M p :=
  induction_on'' p h_C (fun a b f ha hb hf hm => h_add (monomial a b) f hm hf) h_X

theorem ring_hom_ext {A : Type _} [Semiringₓ A] {f g : MvPolynomial σ R →+* A} (hC : ∀ r, f (c r) = g (c r))
    (hX : ∀ i, f (x i) = g (x i)) : f = g := by
  ext
  exacts[hC _, hX _]

/-- See note [partially-applied ext lemmas]. -/
@[ext]
theorem ring_hom_ext' {A : Type _} [Semiringₓ A] {f g : MvPolynomial σ R →+* A} (hC : f.comp c = g.comp c)
    (hX : ∀ i, f (x i) = g (x i)) : f = g :=
  ring_hom_ext (RingHom.ext_iff.1 hC) hX

theorem hom_eq_hom [Semiringₓ S₂] (f g : MvPolynomial σ R →+* S₂) (hC : f.comp c = g.comp c)
    (hX : ∀ n : σ, f (x n) = g (x n)) (p : MvPolynomial σ R) : f p = g p :=
  RingHom.congr_fun (ring_hom_ext' hC hX) p

theorem is_id (f : MvPolynomial σ R →+* MvPolynomial σ R) (hC : f.comp c = C) (hX : ∀ n : σ, f (x n) = x n)
    (p : MvPolynomial σ R) : f p = p :=
  hom_eq_hom f (RingHom.id _) hC hX p

@[ext]
theorem alg_hom_ext' {A B : Type _} [CommSemiringₓ A] [CommSemiringₓ B] [Algebra R A] [Algebra R B]
    {f g : MvPolynomial σ A →ₐ[R] B}
    (h₁ :
      f.comp (IsScalarTower.toAlgHom R A (MvPolynomial σ A)) = g.comp (IsScalarTower.toAlgHom R A (MvPolynomial σ A)))
    (h₂ : ∀ i, f (x i) = g (x i)) : f = g :=
  AlgHom.coe_ring_hom_injective (MvPolynomial.ring_hom_ext' (congr_arg AlgHom.toRingHom h₁) h₂)

@[ext]
theorem alg_hom_ext {A : Type _} [Semiringₓ A] [Algebra R A] {f g : MvPolynomial σ R →ₐ[R] A}
    (hf : ∀ i : σ, f (x i) = g (x i)) : f = g :=
  AddMonoidAlgebra.alg_hom_ext' (mul_hom_ext' fun x : σ => MonoidHom.ext_mnat (hf x))

@[simp]
theorem alg_hom_C (f : MvPolynomial σ R →ₐ[R] MvPolynomial σ R) (r : R) : f (c r) = c r :=
  f.commutes r

@[simp]
theorem adjoin_range_X : Algebra.adjoin R (Range (x : σ → MvPolynomial σ R)) = ⊤ := by
  set S := Algebra.adjoin R (range (X : σ → MvPolynomial σ R))
  refine' top_unique fun p hp => _
  clear hp
  induction p using MvPolynomial.induction_on
  case h_C =>
    exact S.algebra_map_mem _
  case h_add p q hp hq =>
    exact S.add_mem hp hq
  case h_X p i hp =>
    exact S.mul_mem hp (Algebra.subset_adjoin <| mem_range_self _)

@[ext]
theorem linear_map_ext {M : Type _} [AddCommMonoidₓ M] [Module R M] {f g : MvPolynomial σ R →ₗ[R] M}
    (h : ∀ s, f ∘ₗ monomial s = g ∘ₗ monomial s) : f = g :=
  Finsupp.lhom_ext' h

section Support

/-- The finite set of all `m : σ →₀ ℕ` such that `X^m` has a non-zero coefficient.
-/
def support (p : MvPolynomial σ R) : Finset (σ →₀ ℕ) :=
  p.support

theorem finsupp_support_eq_support (p : MvPolynomial σ R) : Finsupp.support p = p.support :=
  rfl

theorem support_monomial [Decidable (a = 0)] : (monomial s a).support = if a = 0 then ∅ else {s} := by
  convert rfl

theorem support_monomial_subset : (monomial s a).support ⊆ {s} :=
  support_single_subset

theorem support_add : (p + q).support ⊆ p.support ∪ q.support :=
  Finsupp.support_add

theorem support_X [Nontrivial R] : (x n : MvPolynomial σ R).support = {single n 1} := by
  rw [X, support_monomial, if_neg] <;> exact one_ne_zero

theorem support_X_pow [Nontrivial R] (s : σ) (n : ℕ) : (x s ^ n : MvPolynomial σ R).support = {Finsupp.single s n} := by
  rw [X_pow_eq_monomial, support_monomial, if_neg (@one_ne_zero R _ _)]

@[simp]
theorem support_zero : (0 : MvPolynomial σ R).support = ∅ :=
  rfl

theorem support_sum {α : Type _} {s : Finset α} {f : α → MvPolynomial σ R} :
    (∑ x in s, f x).support ⊆ s.bUnion fun x => (f x).support :=
  Finsupp.support_finset_sum

end Support

section Coeff

/-- The coefficient of the monomial `m` in the multi-variable polynomial `p`. -/
def coeff (m : σ →₀ ℕ) (p : MvPolynomial σ R) : R :=
  @coeFn _ _ (MonoidAlgebra.hasCoeToFun _ _) p m

@[simp]
theorem mem_support_iff {p : MvPolynomial σ R} {m : σ →₀ ℕ} : m ∈ p.support ↔ p.coeff m ≠ 0 := by
  simp [← support, ← coeff]

theorem not_mem_support_iff {p : MvPolynomial σ R} {m : σ →₀ ℕ} : m ∉ p.support ↔ p.coeff m = 0 := by
  simp

theorem sum_def {A} [AddCommMonoidₓ A] {p : MvPolynomial σ R} {b : (σ →₀ ℕ) → R → A} :
    p.Sum b = ∑ m in p.support, b m (p.coeff m) := by
  simp [← support, ← Finsupp.sum, ← coeff]

theorem support_mul (p q : MvPolynomial σ R) :
    (p * q).support ⊆ p.support.bUnion fun a => q.support.bUnion fun b => {a + b} := by
  convert AddMonoidAlgebra.support_mul p q <;> ext <;> convert Iff.rfl

@[ext]
theorem ext (p q : MvPolynomial σ R) : (∀ m, coeff m p = coeff m q) → p = q :=
  ext

theorem ext_iff (p q : MvPolynomial σ R) : p = q ↔ ∀ m, coeff m p = coeff m q :=
  ⟨fun h m => by
    rw [h], ext p q⟩

@[simp]
theorem coeff_add (m : σ →₀ ℕ) (p q : MvPolynomial σ R) : coeff m (p + q) = coeff m p + coeff m q :=
  add_apply p q m

@[simp]
theorem coeff_smul {S₁ : Type _} [Monoidₓ S₁] [DistribMulAction S₁ R] (m : σ →₀ ℕ) (c : S₁) (p : MvPolynomial σ R) :
    coeff m (c • p) = c • coeff m p :=
  smul_apply c p m

@[simp]
theorem coeff_zero (m : σ →₀ ℕ) : coeff m (0 : MvPolynomial σ R) = 0 :=
  rfl

@[simp]
theorem coeff_zero_X (i : σ) : coeff 0 (x i : MvPolynomial σ R) = 0 :=
  single_eq_of_ne fun h => by
    cases single_eq_zero.1 h

/-- `mv_polynomial.coeff m` but promoted to an `add_monoid_hom`. -/
@[simps]
def coeffAddMonoidHom (m : σ →₀ ℕ) : MvPolynomial σ R →+ R where
  toFun := coeff m
  map_zero' := coeff_zero m
  map_add' := coeff_add m

theorem coeff_sum {X : Type _} (s : Finset X) (f : X → MvPolynomial σ R) (m : σ →₀ ℕ) :
    coeff m (∑ x in s, f x) = ∑ x in s, coeff m (f x) :=
  (@coeffAddMonoidHom R σ _ _).map_sum _ s

theorem monic_monomial_eq (m) : monomial m (1 : R) = (m.Prod fun n e => x n ^ e : MvPolynomial σ R) := by
  simp [← monomial_eq]

@[simp]
theorem coeff_monomial [DecidableEq σ] (m n) (a) : coeff m (monomial n a : MvPolynomial σ R) = if n = m then a else 0 :=
  single_apply

@[simp]
theorem coeff_C [DecidableEq σ] (m) (a) : coeff m (c a : MvPolynomial σ R) = if 0 = m then a else 0 :=
  single_apply

theorem coeff_one [DecidableEq σ] (m) : coeff m (1 : MvPolynomial σ R) = if 0 = m then 1 else 0 :=
  coeff_C m 1

@[simp]
theorem coeff_zero_C (a) : coeff 0 (c a : MvPolynomial σ R) = a :=
  single_eq_same

@[simp]
theorem coeff_zero_one : coeff 0 (1 : MvPolynomial σ R) = 1 :=
  coeff_zero_C 1

theorem coeff_X_pow [DecidableEq σ] (i : σ) (m) (k : ℕ) :
    coeff m (x i ^ k : MvPolynomial σ R) = if single i k = m then 1 else 0 := by
  have := coeff_monomial m (Finsupp.single i k) (1 : R)
  rwa [@monomial_eq _ _ (1 : R) (Finsupp.single i k) _, C_1, one_mulₓ, Finsupp.prod_single_index] at this
  exact pow_zeroₓ _

theorem coeff_X' [DecidableEq σ] (i : σ) (m) : coeff m (x i : MvPolynomial σ R) = if single i 1 = m then 1 else 0 := by
  rw [← coeff_X_pow, pow_oneₓ]

@[simp]
theorem coeff_X (i : σ) : coeff (single i 1) (x i : MvPolynomial σ R) = 1 := by
  rw [coeff_X', if_pos rfl]

@[simp]
theorem coeff_C_mul (m) (a : R) (p : MvPolynomial σ R) : coeff m (c a * p) = a * coeff m p := by
  rw [mul_def, sum_C]
  · simp (config := { contextual := true })[← sum_def, ← coeff_sum]
    
  simp

theorem coeff_mul (p q : MvPolynomial σ R) (n : σ →₀ ℕ) :
    coeff n (p * q) = ∑ x in antidiagonal n, coeff x.1 p * coeff x.2 q :=
  (AddMonoidAlgebra.mul_apply_antidiagonal p q _ _) fun p => mem_antidiagonal

@[simp]
theorem coeff_mul_monomial (m) (s : σ →₀ ℕ) (r : R) (p : MvPolynomial σ R) :
    coeff (m + s) (p * monomial s r) = coeff m p * r :=
  AddMonoidAlgebra.mul_single_apply_aux p _ _ _ _ fun a => add_left_injₓ _

@[simp]
theorem coeff_monomial_mul (m) (s : σ →₀ ℕ) (r : R) (p : MvPolynomial σ R) :
    coeff (s + m) (monomial s r * p) = r * coeff m p :=
  AddMonoidAlgebra.single_mul_apply_aux p _ _ _ _ fun a => add_right_injₓ _

@[simp]
theorem coeff_mul_X (m) (s : σ) (p : MvPolynomial σ R) : coeff (m + single s 1) (p * x s) = coeff m p :=
  (coeff_mul_monomial _ _ _ _).trans (mul_oneₓ _)

@[simp]
theorem coeff_X_mul (m) (s : σ) (p : MvPolynomial σ R) : coeff (single s 1 + m) (x s * p) = coeff m p :=
  (coeff_monomial_mul _ _ _ _).trans (one_mulₓ _)

@[simp]
theorem support_mul_X (s : σ) (p : MvPolynomial σ R) :
    (p * x s).support = p.support.map (addRightEmbedding (single s 1)) :=
  AddMonoidAlgebra.support_mul_single p _
    (by
      simp )
    _

@[simp]
theorem support_X_mul (s : σ) (p : MvPolynomial σ R) :
    (x s * p).support = p.support.map (addLeftEmbedding (single s 1)) :=
  AddMonoidAlgebra.support_single_mul p _
    (by
      simp )
    _

theorem support_sdiff_support_subset_support_add [DecidableEq σ] (p q : MvPolynomial σ R) :
    p.support \ q.support ⊆ (p + q).support := by
  intro m hm
  simp only [← not_not, ← mem_support_iff, ← Finset.mem_sdiff, ← Ne.def] at hm
  simp [← hm.2, ← hm.1]

theorem support_symm_diff_support_subset_support_add [DecidableEq σ] (p q : MvPolynomial σ R) :
    p.support ∆ q.support ⊆ (p + q).support := by
  rw [symm_diff_def, Finset.sup_eq_union]
  apply Finset.union_subset
  · exact support_sdiff_support_subset_support_add p q
    
  · rw [add_commₓ]
    exact support_sdiff_support_subset_support_add q p
    

theorem coeff_mul_monomial' (m) (s : σ →₀ ℕ) (r : R) (p : MvPolynomial σ R) :
    coeff m (p * monomial s r) = if s ≤ m then coeff (m - s) p * r else 0 := by
  obtain rfl | hr := eq_or_ne r 0
  · simp only [← monomial_zero, ← coeff_zero, ← mul_zero, ← if_t_t]
    
  have : Nontrivial R := nontrivial_of_ne _ _ hr
  split_ifs with h h
  · conv_rhs => rw [← coeff_mul_monomial _ s]
    congr with t
    rw [tsub_add_cancel_of_le h]
    
  · rw [← not_mem_support_iff]
    intro hm
    apply h
    have H := support_mul _ _ hm
    simp only [← Finset.mem_bUnion] at H
    rcases H with ⟨j, hj, i', hi', H⟩
    rw [support_monomial, if_neg hr, Finset.mem_singleton] at hi'
    subst i'
    rw [Finset.mem_singleton] at H
    subst m
    exact le_add_left le_rfl
    

theorem coeff_monomial_mul' (m) (s : σ →₀ ℕ) (r : R) (p : MvPolynomial σ R) :
    coeff m (monomial s r * p) = if s ≤ m then r * coeff (m - s) p else 0 := by
  -- note that if we allow `R` to be non-commutative we will have to duplicate the proof above.
  rw [mul_comm, mul_comm r]
  exact coeff_mul_monomial' _ _ _ _

theorem coeff_mul_X' [DecidableEq σ] (m) (s : σ) (p : MvPolynomial σ R) :
    coeff m (p * x s) = if s ∈ m.support then coeff (m - single s 1) p else 0 := by
  refine' (coeff_mul_monomial' _ _ _ _).trans _
  simp_rw [Finsupp.single_le_iff, Finsupp.mem_support_iff, Nat.succ_le_iff, pos_iff_ne_zero, mul_oneₓ]

theorem coeff_X_mul' [DecidableEq σ] (m) (s : σ) (p : MvPolynomial σ R) :
    coeff m (x s * p) = if s ∈ m.support then coeff (m - single s 1) p else 0 := by
  refine' (coeff_monomial_mul' _ _ _ _).trans _
  simp_rw [Finsupp.single_le_iff, Finsupp.mem_support_iff, Nat.succ_le_iff, pos_iff_ne_zero, one_mulₓ]

theorem eq_zero_iff {p : MvPolynomial σ R} : p = 0 ↔ ∀ d, coeff d p = 0 := by
  rw [ext_iff]
  simp only [← coeff_zero]

theorem ne_zero_iff {p : MvPolynomial σ R} : p ≠ 0 ↔ ∃ d, coeff d p ≠ 0 := by
  rw [Ne.def, eq_zero_iff]
  push_neg

theorem exists_coeff_ne_zero {p : MvPolynomial σ R} (h : p ≠ 0) : ∃ d, coeff d p ≠ 0 :=
  ne_zero_iff.mp h

theorem C_dvd_iff_dvd_coeff (r : R) (φ : MvPolynomial σ R) : c r ∣ φ ↔ ∀ i, r ∣ φ.coeff i := by
  constructor
  · rintro ⟨φ, rfl⟩ c
    rw [coeff_C_mul]
    apply dvd_mul_right
    
  · intro h
    choose c hc using h
    classical
    let c' : (σ →₀ ℕ) → R := fun i => if i ∈ φ.support then c i else 0
    let ψ : MvPolynomial σ R := ∑ i in φ.support, monomial i (c' i)
    use ψ
    apply MvPolynomial.ext
    intro i
    simp only [← coeff_C_mul, ← coeff_sum, ← coeff_monomial, ← Finset.sum_ite_eq', ← c']
    split_ifs with hi hi
    · rw [hc]
      
    · rw [not_mem_support_iff] at hi
      rwa [mul_zero]
      
    

end Coeff

section ConstantCoeff

/-- `constant_coeff p` returns the constant term of the polynomial `p`, defined as `coeff 0 p`.
This is a ring homomorphism.
-/
def constantCoeff : MvPolynomial σ R →+* R where
  toFun := coeff 0
  map_one' := by
    simp [← coeff, ← AddMonoidAlgebra.one_def]
  map_mul' := by
    simp [← coeff_mul, ← Finsupp.support_single_ne_zero]
  map_zero' := coeff_zero _
  map_add' := coeff_add _

theorem constant_coeff_eq : (constantCoeff : MvPolynomial σ R → R) = coeff 0 :=
  rfl

@[simp]
theorem constant_coeff_C (r : R) : constantCoeff (c r : MvPolynomial σ R) = r := by
  simp [← constant_coeff_eq]

@[simp]
theorem constant_coeff_X (i : σ) : constantCoeff (x i : MvPolynomial σ R) = 0 := by
  simp [← constant_coeff_eq]

theorem constant_coeff_monomial [DecidableEq σ] (d : σ →₀ ℕ) (r : R) :
    constantCoeff (monomial d r) = if d = 0 then r else 0 := by
  rw [constant_coeff_eq, coeff_monomial]

variable (σ R)

@[simp]
theorem constant_coeff_comp_C : constantCoeff.comp (c : R →+* MvPolynomial σ R) = RingHom.id R := by
  ext
  apply constant_coeff_C

@[simp]
theorem constant_coeff_comp_algebra_map : constantCoeff.comp (algebraMap R (MvPolynomial σ R)) = RingHom.id R :=
  constant_coeff_comp_C _ _

end ConstantCoeff

section AsSum

@[simp]
theorem support_sum_monomial_coeff (p : MvPolynomial σ R) : (∑ v in p.support, monomial v (coeff v p)) = p :=
  Finsupp.sum_single p

theorem as_sum (p : MvPolynomial σ R) : p = ∑ v in p.support, monomial v (coeff v p) :=
  (support_sum_monomial_coeff p).symm

end AsSum

section Eval₂

variable (f : R →+* S₁) (g : σ → S₁)

/-- Evaluate a polynomial `p` given a valuation `g` of all the variables
  and a ring hom `f` from the scalar ring to the target -/
def eval₂ (p : MvPolynomial σ R) : S₁ :=
  p.Sum fun s a => f a * s.Prod fun n e => g n ^ e

theorem eval₂_eq (g : R →+* S₁) (x : σ → S₁) (f : MvPolynomial σ R) :
    f.eval₂ g x = ∑ d in f.support, g (f.coeff d) * ∏ i in d.support, x i ^ d i :=
  rfl

theorem eval₂_eq' [Fintype σ] (g : R →+* S₁) (x : σ → S₁) (f : MvPolynomial σ R) :
    f.eval₂ g x = ∑ d in f.support, g (f.coeff d) * ∏ i, x i ^ d i := by
  simp only [← eval₂_eq, Finsupp.prod_pow]
  rfl

@[simp]
theorem eval₂_zero : (0 : MvPolynomial σ R).eval₂ f g = 0 :=
  Finsupp.sum_zero_index

section

@[simp]
theorem eval₂_add : (p + q).eval₂ f g = p.eval₂ f g + q.eval₂ f g :=
  Finsupp.sum_add_index
    (by
      simp [← f.map_zero])
    (by
      simp [← add_mulₓ, ← f.map_add])

@[simp]
theorem eval₂_monomial : (monomial s a).eval₂ f g = f a * s.Prod fun n e => g n ^ e :=
  Finsupp.sum_single_index
    (by
      simp [← f.map_zero])

@[simp]
theorem eval₂_C (a) : (c a).eval₂ f g = f a := by
  rw [C_apply, eval₂_monomial, prod_zero_index, mul_oneₓ]

@[simp]
theorem eval₂_one : (1 : MvPolynomial σ R).eval₂ f g = 1 :=
  (eval₂_C _ _ _).trans f.map_one

@[simp]
theorem eval₂_X (n) : (x n).eval₂ f g = g n := by
  simp [← eval₂_monomial, ← f.map_one, ← X, ← prod_single_index, ← pow_oneₓ]

theorem eval₂_mul_monomial : ∀ {s a}, (p * monomial s a).eval₂ f g = p.eval₂ f g * f a * s.Prod fun n e => g n ^ e := by
  apply MvPolynomial.induction_on p
  · intro a' s a
    simp [← C_mul_monomial, ← eval₂_monomial, ← f.map_mul]
    
  · intro p q ih_p ih_q
    simp [← add_mulₓ, ← eval₂_add, ← ih_p, ← ih_q]
    
  · intro p n ih s a
    exact
      calc
        (p * X n * monomial s a).eval₂ f g = (p * monomial (single n 1 + s) a).eval₂ f g := by
          rw [monomial_single_add, pow_oneₓ, mul_assoc]
        _ = (p * monomial (single n 1) 1).eval₂ f g * f a * s.prod fun n e => g n ^ e := by
          simp [← ih, ← prod_single_index, ← prod_add_index, ← pow_oneₓ, ← pow_addₓ, ← mul_assoc, ← mul_left_commₓ, ←
            f.map_one, -add_commₓ]
        
    

theorem eval₂_mul_C : (p * c a).eval₂ f g = p.eval₂ f g * f a :=
  (eval₂_mul_monomial _ _).trans <| by
    simp

@[simp]
theorem eval₂_mul : ∀ {p}, (p * q).eval₂ f g = p.eval₂ f g * q.eval₂ f g := by
  apply MvPolynomial.induction_on q
  · simp [← eval₂_C, ← eval₂_mul_C]
    
  · simp (config := { contextual := true })[← mul_addₓ, ← eval₂_add]
    
  · simp (config := { contextual := true })[← X, ← eval₂_monomial, ← eval₂_mul_monomial, mul_assoc]
    

@[simp]
theorem eval₂_pow {p : MvPolynomial σ R} : ∀ {n : ℕ}, (p ^ n).eval₂ f g = p.eval₂ f g ^ n
  | 0 => by
    rw [pow_zeroₓ, pow_zeroₓ]
    exact eval₂_one _ _
  | n + 1 => by
    rw [pow_addₓ, pow_oneₓ, pow_addₓ, pow_oneₓ, eval₂_mul, eval₂_pow]

/-- `mv_polynomial.eval₂` as a `ring_hom`. -/
def eval₂Hom (f : R →+* S₁) (g : σ → S₁) : MvPolynomial σ R →+* S₁ where
  toFun := eval₂ f g
  map_one' := eval₂_one _ _
  map_mul' := fun p q => eval₂_mul _ _
  map_zero' := eval₂_zero _ _
  map_add' := fun p q => eval₂_add _ _

@[simp]
theorem coe_eval₂_hom (f : R →+* S₁) (g : σ → S₁) : ⇑(eval₂Hom f g) = eval₂ f g :=
  rfl

theorem eval₂_hom_congr {f₁ f₂ : R →+* S₁} {g₁ g₂ : σ → S₁} {p₁ p₂ : MvPolynomial σ R} :
    f₁ = f₂ → g₁ = g₂ → p₁ = p₂ → eval₂Hom f₁ g₁ p₁ = eval₂Hom f₂ g₂ p₂ := by
  rintro rfl rfl rfl <;> rfl

end

@[simp]
theorem eval₂_hom_C (f : R →+* S₁) (g : σ → S₁) (r : R) : eval₂Hom f g (c r) = f r :=
  eval₂_C f g r

@[simp]
theorem eval₂_hom_X' (f : R →+* S₁) (g : σ → S₁) (i : σ) : eval₂Hom f g (x i) = g i :=
  eval₂_X f g i

@[simp]
theorem comp_eval₂_hom [CommSemiringₓ S₂] (f : R →+* S₁) (g : σ → S₁) (φ : S₁ →+* S₂) :
    φ.comp (eval₂Hom f g) = eval₂Hom (φ.comp f) fun i => φ (g i) := by
  apply MvPolynomial.ring_hom_ext
  · intro r
    rw [RingHom.comp_apply, eval₂_hom_C, eval₂_hom_C, RingHom.comp_apply]
    
  · intro i
    rw [RingHom.comp_apply, eval₂_hom_X', eval₂_hom_X']
    

theorem map_eval₂_hom [CommSemiringₓ S₂] (f : R →+* S₁) (g : σ → S₁) (φ : S₁ →+* S₂) (p : MvPolynomial σ R) :
    φ (eval₂Hom f g p) = eval₂Hom (φ.comp f) (fun i => φ (g i)) p := by
  rw [← comp_eval₂_hom]
  rfl

theorem eval₂_hom_monomial (f : R →+* S₁) (g : σ → S₁) (d : σ →₀ ℕ) (r : R) :
    eval₂Hom f g (monomial d r) = f r * d.Prod fun i k => g i ^ k := by
  simp only [← monomial_eq, ← RingHom.map_mul, ← eval₂_hom_C, ← Finsupp.prod, ← RingHom.map_prod, ← RingHom.map_pow, ←
    eval₂_hom_X']

section

theorem eval₂_comp_left {S₂} [CommSemiringₓ S₂] (k : S₁ →+* S₂) (f : R →+* S₁) (g : σ → S₁) (p) :
    k (eval₂ f g p) = eval₂ (k.comp f) (k ∘ g) p := by
  apply MvPolynomial.induction_on p <;>
    simp (config := { contextual := true })[← eval₂_add, ← k.map_add, ← eval₂_mul, ← k.map_mul]

end

@[simp]
theorem eval₂_eta (p : MvPolynomial σ R) : eval₂ c x p = p := by
  apply MvPolynomial.induction_on p <;> simp (config := { contextual := true })[← eval₂_add, ← eval₂_mul]

theorem eval₂_congr (g₁ g₂ : σ → S₁) (h : ∀ {i : σ} {c : σ →₀ ℕ}, i ∈ c.support → coeff c p ≠ 0 → g₁ i = g₂ i) :
    p.eval₂ f g₁ = p.eval₂ f g₂ := by
  apply Finset.sum_congr rfl
  intro c hc
  dsimp'
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  dsimp'
  congr 1
  apply h hi
  rwa [Finsupp.mem_support_iff] at hc

@[simp]
theorem eval₂_prod (s : Finset S₂) (p : S₂ → MvPolynomial σ R) :
    eval₂ f g (∏ x in s, p x) = ∏ x in s, eval₂ f g (p x) :=
  (eval₂Hom f g).map_prod _ s

@[simp]
theorem eval₂_sum (s : Finset S₂) (p : S₂ → MvPolynomial σ R) : eval₂ f g (∑ x in s, p x) = ∑ x in s, eval₂ f g (p x) :=
  (eval₂Hom f g).map_sum _ s

attribute [to_additive] eval₂_prod

theorem eval₂_assoc (q : S₂ → MvPolynomial σ R) (p : MvPolynomial S₂ R) :
    eval₂ f (fun t => eval₂ f g (q t)) p = eval₂ f g (eval₂ c q p) := by
  show _ = eval₂_hom f g (eval₂ C q p)
  rw [eval₂_comp_left (eval₂_hom f g)]
  congr with a
  simp

end Eval₂

section Eval

variable {f : σ → R}

/-- Evaluate a polynomial `p` given a valuation `f` of all the variables -/
def eval (f : σ → R) : MvPolynomial σ R →+* R :=
  eval₂Hom (RingHom.id _) f

theorem eval_eq (x : σ → R) (f : MvPolynomial σ R) :
    eval x f = ∑ d in f.support, f.coeff d * ∏ i in d.support, x i ^ d i :=
  rfl

theorem eval_eq' [Fintype σ] (x : σ → R) (f : MvPolynomial σ R) :
    eval x f = ∑ d in f.support, f.coeff d * ∏ i, x i ^ d i :=
  eval₂_eq' (RingHom.id R) x f

theorem eval_monomial : eval f (monomial s a) = a * s.Prod fun n e => f n ^ e :=
  eval₂_monomial _ _

@[simp]
theorem eval_C : ∀ a, eval f (c a) = a :=
  eval₂_C _ _

@[simp]
theorem eval_X : ∀ n, eval f (x n) = f n :=
  eval₂_X _ _

@[simp]
theorem smul_eval (x) (p : MvPolynomial σ R) (s) : eval x (s • p) = s * eval x p := by
  rw [smul_eq_C_mul, (eval x).map_mul, eval_C]

theorem eval_sum {ι : Type _} (s : Finset ι) (f : ι → MvPolynomial σ R) (g : σ → R) :
    eval g (∑ i in s, f i) = ∑ i in s, eval g (f i) :=
  (eval g).map_sum _ _

@[to_additive]
theorem eval_prod {ι : Type _} (s : Finset ι) (f : ι → MvPolynomial σ R) (g : σ → R) :
    eval g (∏ i in s, f i) = ∏ i in s, eval g (f i) :=
  (eval g).map_prod _ _

theorem eval_assoc {τ} (f : σ → MvPolynomial τ R) (g : τ → R) (p : MvPolynomial σ R) :
    eval (eval g ∘ f) p = eval g (eval₂ c f p) := by
  rw [eval₂_comp_left (eval g)]
  unfold eval
  simp only [← coe_eval₂_hom]
  congr with a
  simp

end Eval

section Map

variable (f : R →+* S₁)

/-- `map f p` maps a polynomial `p` across a ring hom `f` -/
def map : MvPolynomial σ R →+* MvPolynomial σ S₁ :=
  eval₂Hom (c.comp f) x

@[simp]
theorem map_monomial (s : σ →₀ ℕ) (a : R) : map f (monomial s a) = monomial s (f a) :=
  (eval₂_monomial _ _).trans monomial_eq.symm

@[simp]
theorem map_C : ∀ a : R, map f (c a : MvPolynomial σ R) = c (f a) :=
  map_monomial _ _

@[simp]
theorem map_X : ∀ n : σ, map f (x n : MvPolynomial σ R) = x n :=
  eval₂_X _ _

theorem map_id : ∀ p : MvPolynomial σ R, map (RingHom.id R) p = p :=
  eval₂_eta

theorem map_map [CommSemiringₓ S₂] (g : S₁ →+* S₂) (p : MvPolynomial σ R) : map g (map f p) = map (g.comp f) p :=
  (eval₂_comp_left (map g) (c.comp f) x p).trans <| by
    congr
    · ext1 a
      simp only [← map_C, ← comp_app, ← RingHom.coe_comp]
      
    · ext1 n
      simp only [← map_X, ← comp_app]
      

theorem eval₂_eq_eval_map (g : σ → S₁) (p : MvPolynomial σ R) : p.eval₂ f g = eval g (map f p) := by
  unfold map eval
  simp only [← coe_eval₂_hom]
  have h := eval₂_comp_left (eval₂_hom _ g)
  dsimp'  at h
  rw [h]
  congr
  · ext1 a
    simp only [← coe_eval₂_hom, ← RingHom.id_apply, ← comp_app, ← eval₂_C, ← RingHom.coe_comp]
    
  · ext1 n
    simp only [← comp_app, ← eval₂_X]
    

theorem eval₂_comp_right {S₂} [CommSemiringₓ S₂] (k : S₁ →+* S₂) (f : R →+* S₁) (g : σ → S₁) (p) :
    k (eval₂ f g p) = eval₂ k (k ∘ g) (map f p) := by
  apply MvPolynomial.induction_on p
  · intro r
    rw [eval₂_C, map_C, eval₂_C]
    
  · intro p q hp hq
    rw [eval₂_add, k.map_add, (map f).map_add, eval₂_add, hp, hq]
    
  · intro p s hp
    rw [eval₂_mul, k.map_mul, (map f).map_mul, eval₂_mul, map_X, hp, eval₂_X, eval₂_X]
    

theorem map_eval₂ (f : R →+* S₁) (g : S₂ → MvPolynomial S₃ R) (p : MvPolynomial S₂ R) :
    map f (eval₂ c g p) = eval₂ c (map f ∘ g) (map f p) := by
  apply MvPolynomial.induction_on p
  · intro r
    rw [eval₂_C, map_C, map_C, eval₂_C]
    
  · intro p q hp hq
    rw [eval₂_add, (map f).map_add, hp, hq, (map f).map_add, eval₂_add]
    
  · intro p s hp
    rw [eval₂_mul, (map f).map_mul, hp, (map f).map_mul, map_X, eval₂_mul, eval₂_X, eval₂_X]
    

theorem coeff_map (p : MvPolynomial σ R) : ∀ m : σ →₀ ℕ, coeff m (map f p) = f (coeff m p) := by
  apply MvPolynomial.induction_on p <;> clear p
  · intro r m
    rw [map_C]
    simp only [← coeff_C]
    split_ifs
    · rfl
      
    rw [f.map_zero]
    
  · intro p q hp hq m
    simp only [← hp, ← hq, ← (map f).map_add, ← coeff_add]
    rw [f.map_add]
    
  · intro p i hp m
    simp only [← hp, ← (map f).map_mul, ← map_X]
    simp only [← hp, ← mem_support_iff, ← coeff_mul_X']
    split_ifs
    · rfl
      
    rw [f.map_zero]
    

theorem map_injective (hf : Function.Injective f) : Function.Injective (map f : MvPolynomial σ R → MvPolynomial σ S₁) :=
  by
  intro p q h
  simp only [← ext_iff, ← coeff_map] at h⊢
  intro m
  exact hf (h m)

theorem map_surjective (hf : Function.Surjective f) :
    Function.Surjective (map f : MvPolynomial σ R → MvPolynomial σ S₁) := fun p => by
  induction' p using MvPolynomial.induction_on' with i fr a b ha hb
  · obtain ⟨r, rfl⟩ := hf fr
    exact ⟨monomial i r, map_monomial _ _ _⟩
    
  · obtain ⟨a, rfl⟩ := ha
    obtain ⟨b, rfl⟩ := hb
    exact ⟨a + b, RingHom.map_add _ _ _⟩
    

/-- If `f` is a left-inverse of `g` then `map f` is a left-inverse of `map g`. -/
theorem map_left_inverse {f : R →+* S₁} {g : S₁ →+* R} (hf : Function.LeftInverse f g) :
    Function.LeftInverse (map f : MvPolynomial σ R → MvPolynomial σ S₁) (map g) := fun x => by
  rw [map_map, (RingHom.ext hf : f.comp g = RingHom.id _), map_id]

/-- If `f` is a right-inverse of `g` then `map f` is a right-inverse of `map g`. -/
theorem map_right_inverse {f : R →+* S₁} {g : S₁ →+* R} (hf : Function.RightInverse f g) :
    Function.RightInverse (map f : MvPolynomial σ R → MvPolynomial σ S₁) (map g) :=
  (map_left_inverse hf.LeftInverse).RightInverse

@[simp]
theorem eval_map (f : R →+* S₁) (g : σ → S₁) (p : MvPolynomial σ R) : eval g (map f p) = eval₂ f g p := by
  apply MvPolynomial.induction_on p <;>
    · simp (config := { contextual := true })
      

@[simp]
theorem eval₂_map [CommSemiringₓ S₂] (f : R →+* S₁) (g : σ → S₂) (φ : S₁ →+* S₂) (p : MvPolynomial σ R) :
    eval₂ φ g (map f p) = eval₂ (φ.comp f) g p := by
  rw [← eval_map, ← eval_map, map_map]

@[simp]
theorem eval₂_hom_map_hom [CommSemiringₓ S₂] (f : R →+* S₁) (g : σ → S₂) (φ : S₁ →+* S₂) (p : MvPolynomial σ R) :
    eval₂Hom φ g (map f p) = eval₂Hom (φ.comp f) g p :=
  eval₂_map f g φ p

@[simp]
theorem constant_coeff_map (f : R →+* S₁) (φ : MvPolynomial σ R) :
    constantCoeff (MvPolynomial.map f φ) = f (constantCoeff φ) :=
  coeff_map f φ 0

theorem constant_coeff_comp_map (f : R →+* S₁) :
    (constantCoeff : MvPolynomial σ S₁ →+* S₁).comp (MvPolynomial.map f) = f.comp constantCoeff := by
  ext <;> simp

theorem support_map_subset (p : MvPolynomial σ R) : (map f p).support ⊆ p.support := by
  intro x
  simp only [← mem_support_iff]
  contrapose!
  change p.coeff x = 0 → (map f p).coeff x = 0
  rw [coeff_map]
  intro hx
  rw [hx]
  exact RingHom.map_zero f

theorem support_map_of_injective (p : MvPolynomial σ R) {f : R →+* S₁} (hf : Injective f) :
    (map f p).support = p.support := by
  apply Finset.Subset.antisymm
  · exact MvPolynomial.support_map_subset _ _
    
  intro x hx
  rw [mem_support_iff]
  contrapose! hx
  simp only [← not_not, ← mem_support_iff]
  change (map f p).coeff x = 0 at hx
  rw [coeff_map, ← f.map_zero] at hx
  exact hf hx

theorem C_dvd_iff_map_hom_eq_zero (q : R →+* S₁) (r : R) (hr : ∀ r' : R, q r' = 0 ↔ r ∣ r') (φ : MvPolynomial σ R) :
    c r ∣ φ ↔ map q φ = 0 := by
  rw [C_dvd_iff_dvd_coeff, MvPolynomial.ext_iff]
  simp only [← coeff_map, ← coeff_zero, ← hr]

theorem map_map_range_eq_iff (f : R →+* S₁) (g : S₁ → R) (hg : g 0 = 0) (φ : MvPolynomial σ S₁) :
    map f (Finsupp.mapRange g hg φ) = φ ↔ ∀ d, f (g (coeff d φ)) = coeff d φ := by
  rw [MvPolynomial.ext_iff]
  apply forall_congrₓ
  intro m
  rw [coeff_map]
  apply eq_iff_eq_cancel_right.mpr
  rfl

/-- If `f : S₁ →ₐ[R] S₂` is a morphism of `R`-algebras, then so is `mv_polynomial.map f`. -/
@[simps]
def mapAlgHom [CommSemiringₓ S₂] [Algebra R S₁] [Algebra R S₂] (f : S₁ →ₐ[R] S₂) :
    MvPolynomial σ S₁ →ₐ[R] MvPolynomial σ S₂ :=
  { map ↑f with toFun := map ↑f,
    commutes' := fun r => by
      have h₁ : algebraMap R (MvPolynomial σ S₁) r = C (algebraMap R S₁ r) := rfl
      have h₂ : algebraMap R (MvPolynomial σ S₂) r = C (algebraMap R S₂ r) := rfl
      rw [h₁, h₂, map, eval₂_hom_C, RingHom.comp_apply, AlgHom.coe_to_ring_hom, AlgHom.commutes] }

@[simp]
theorem map_alg_hom_id [Algebra R S₁] : mapAlgHom (AlgHom.id R S₁) = AlgHom.id R (MvPolynomial σ S₁) :=
  AlgHom.ext map_id

@[simp]
theorem map_alg_hom_coe_ring_hom [CommSemiringₓ S₂] [Algebra R S₁] [Algebra R S₂] (f : S₁ →ₐ[R] S₂) :
    ↑(mapAlgHom f : _ →ₐ[R] MvPolynomial σ S₂) = (map ↑f : MvPolynomial σ S₁ →+* MvPolynomial σ S₂) :=
  RingHom.mk_coe _ _ _ _ _

end Map

section Aeval

/-! ### The algebra of multivariate polynomials -/


variable [Algebra R S₁] [CommSemiringₓ S₂]

variable (f : σ → S₁)

/-- A map `σ → S₁` where `S₁` is an algebra over `R` generates an `R`-algebra homomorphism
from multivariate polynomials over `σ` to `S₁`. -/
def aeval : MvPolynomial σ R →ₐ[R] S₁ :=
  { eval₂Hom (algebraMap R S₁) f with commutes' := fun r => eval₂_C _ _ _ }

theorem aeval_def (p : MvPolynomial σ R) : aeval f p = eval₂ (algebraMap R S₁) f p :=
  rfl

theorem aeval_eq_eval₂_hom (p : MvPolynomial σ R) : aeval f p = eval₂Hom (algebraMap R S₁) f p :=
  rfl

@[simp]
theorem aeval_X (s : σ) : aeval f (x s : MvPolynomial _ R) = f s :=
  eval₂_X _ _ _

@[simp]
theorem aeval_C (r : R) : aeval f (c r) = algebraMap R S₁ r :=
  eval₂_C _ _ _

theorem aeval_unique (φ : MvPolynomial σ R →ₐ[R] S₁) : φ = aeval (φ ∘ X) := by
  ext i
  simp

theorem comp_aeval {B : Type _} [CommSemiringₓ B] [Algebra R B] (φ : S₁ →ₐ[R] B) :
    φ.comp (aeval f) = aeval fun i => φ (f i) := by
  ext i
  simp

@[simp]
theorem map_aeval {B : Type _} [CommSemiringₓ B] (g : σ → S₁) (φ : S₁ →+* B) (p : MvPolynomial σ R) :
    φ (aeval g p) = eval₂Hom (φ.comp (algebraMap R S₁)) (fun i => φ (g i)) p := by
  rw [← comp_eval₂_hom]
  rfl

@[simp]
theorem eval₂_hom_zero (f : R →+* S₂) (p : MvPolynomial σ R) : eval₂Hom f (0 : σ → S₂) p = f (constantCoeff p) := by
  suffices : eval₂_hom f (0 : σ → S₂) = f.comp constant_coeff
  exact RingHom.congr_fun this p
  ext <;> simp

@[simp]
theorem eval₂_hom_zero' (f : R →+* S₂) (p : MvPolynomial σ R) :
    eval₂Hom f (fun _ => 0 : σ → S₂) p = f (constantCoeff p) :=
  eval₂_hom_zero f p

@[simp]
theorem aeval_zero (p : MvPolynomial σ R) : aeval (0 : σ → S₁) p = algebraMap _ _ (constantCoeff p) :=
  eval₂_hom_zero (algebraMap R S₁) p

@[simp]
theorem aeval_zero' (p : MvPolynomial σ R) : aeval (fun _ => 0 : σ → S₁) p = algebraMap _ _ (constantCoeff p) :=
  aeval_zero p

theorem aeval_monomial (g : σ → S₁) (d : σ →₀ ℕ) (r : R) :
    aeval g (monomial d r) = algebraMap _ _ r * d.Prod fun i k => g i ^ k :=
  eval₂_hom_monomial _ _ _ _

theorem eval₂_hom_eq_zero (f : R →+* S₂) (g : σ → S₂) (φ : MvPolynomial σ R)
    (h : ∀ d, φ.coeff d ≠ 0 → ∃ i ∈ d.support, g i = 0) : eval₂Hom f g φ = 0 := by
  rw [φ.as_sum, RingHom.map_sum, Finset.sum_eq_zero]
  intro d hd
  obtain ⟨i, hi, hgi⟩ : ∃ i ∈ d.support, g i = 0 := h d (finsupp.mem_support_iff.mp hd)
  rw [eval₂_hom_monomial, Finsupp.prod, Finset.prod_eq_zero hi, mul_zero]
  rw [hgi, zero_pow]
  rwa [pos_iff_ne_zero, ← Finsupp.mem_support_iff]

theorem aeval_eq_zero [Algebra R S₂] (f : σ → S₂) (φ : MvPolynomial σ R)
    (h : ∀ d, φ.coeff d ≠ 0 → ∃ i ∈ d.support, f i = 0) : aeval f φ = 0 :=
  eval₂_hom_eq_zero _ _ _ h

theorem aeval_sum {ι : Type _} (s : Finset ι) (φ : ι → MvPolynomial σ R) :
    aeval f (∑ i in s, φ i) = ∑ i in s, aeval f (φ i) :=
  (MvPolynomial.aeval f).map_sum _ _

@[to_additive]
theorem aeval_prod {ι : Type _} (s : Finset ι) (φ : ι → MvPolynomial σ R) :
    aeval f (∏ i in s, φ i) = ∏ i in s, aeval f (φ i) :=
  (MvPolynomial.aeval f).map_prod _ _

variable (R)

theorem _root_.algebra.adjoin_range_eq_range_aeval : Algebra.adjoin R (Set.Range f) = (MvPolynomial.aeval f).range := by
  simp only [Algebra.map_top, MvPolynomial.adjoin_range_X, ← AlgHom.map_adjoin, Set.range_comp, ← (· ∘ ·), ←
    MvPolynomial.aeval_X]

theorem _root_.algebra.adjoin_eq_range (s : Set S₁) : Algebra.adjoin R s = (MvPolynomial.aeval (coe : s → S₁)).range :=
  by
  rw [← Algebra.adjoin_range_eq_range_aeval, Subtype.range_coe]

end Aeval

section AevalTower

variable {S A B : Type _} [CommSemiringₓ S] [CommSemiringₓ A] [CommSemiringₓ B]

variable [Algebra S R] [Algebra S A] [Algebra S B]

/-- Version of `aeval` for defining algebra homs out of `mv_polynomial σ R` over a smaller base ring
  than `R`. -/
def aevalTower (f : R →ₐ[S] A) (x : σ → A) : MvPolynomial σ R →ₐ[S] A :=
  { eval₂Hom (↑f) x with
    commutes' := fun r => by
      simp [← IsScalarTower.algebra_map_eq S R (MvPolynomial σ R), ← algebra_map_eq] }

variable (g : R →ₐ[S] A) (y : σ → A)

@[simp]
theorem aeval_tower_X (i : σ) : aevalTower g y (x i) = y i :=
  eval₂_X _ _ _

@[simp]
theorem aeval_tower_C (x : R) : aevalTower g y (c x) = g x :=
  eval₂_C _ _ _

@[simp]
theorem aeval_tower_comp_C : (aevalTower g y : MvPolynomial σ R →+* A).comp c = g :=
  RingHom.ext <| aeval_tower_C _ _

@[simp]
theorem aeval_tower_algebra_map (x : R) : aevalTower g y (algebraMap R (MvPolynomial σ R) x) = g x :=
  eval₂_C _ _ _

@[simp]
theorem aeval_tower_comp_algebra_map :
    (aevalTower g y : MvPolynomial σ R →+* A).comp (algebraMap R (MvPolynomial σ R)) = g :=
  aeval_tower_comp_C _ _

theorem aeval_tower_to_alg_hom (x : R) : aevalTower g y (IsScalarTower.toAlgHom S R (MvPolynomial σ R) x) = g x :=
  aeval_tower_algebra_map _ _ _

@[simp]
theorem aeval_tower_comp_to_alg_hom : (aevalTower g y).comp (IsScalarTower.toAlgHom S R (MvPolynomial σ R)) = g :=
  AlgHom.coe_ring_hom_injective <| aeval_tower_comp_algebra_map _ _

@[simp]
theorem aeval_tower_id : aevalTower (AlgHom.id S S) = (aeval : (σ → S) → MvPolynomial σ S →ₐ[S] S) := by
  ext
  simp only [← aeval_tower_X, ← aeval_X]

@[simp]
theorem aeval_tower_of_id : aevalTower (Algebra.ofId S A) = (aeval : (σ → A) → MvPolynomial σ S →ₐ[S] A) := by
  ext
  simp only [← aeval_X, ← aeval_tower_X]

end AevalTower

end CommSemiringₓ

end MvPolynomial

