/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Johan Commelin, Mario Carneiro
-/
import Mathbin.Data.MvPolynomial.Variables

/-!
# Multivariate polynomials over a ring

Many results about polynomials hold when the coefficient ring is a commutative semiring.
Some stronger results can be derived when we assume this semiring is a ring.

This file does not define any new operations, but proves some of these stronger results.

## Notation

As in other polynomial files, we typically use the notation:

+ `σ : Type*` (indexing the variables)

+ `R : Type*` `[comm_ring R]` (the coefficients)

+ `s : σ →₀ ℕ`, a function from `σ` to `ℕ` which is zero away from a finite set.
This will give rise to a monomial in `mv_polynomial σ R` which mathematicians might call `X^s`

+ `a : R`

+ `i : σ`, with corresponding monomial `X i`, often denoted `X_i` by mathematicians

+ `p : mv_polynomial σ R`

-/


noncomputable section

open Classical BigOperators

open Set Function Finsupp AddMonoidAlgebra

open BigOperators

universe u v

variable {R : Type u} {S : Type v}

namespace MvPolynomial

variable {σ : Type _} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

section CommRingₓ

variable [CommRingₓ R]

variable {p q : MvPolynomial σ R}

instance : CommRingₓ (MvPolynomial σ R) :=
  AddMonoidAlgebra.commRing

variable (σ a a')

@[simp]
theorem C_sub : (c (a - a') : MvPolynomial σ R) = c a - c a' :=
  RingHom.map_sub _ _ _

@[simp]
theorem C_neg : (c (-a) : MvPolynomial σ R) = -c a :=
  RingHom.map_neg _ _

@[simp]
theorem coeff_neg (m : σ →₀ ℕ) (p : MvPolynomial σ R) : coeff m (-p) = -coeff m p :=
  Finsupp.neg_apply _ _

@[simp]
theorem coeff_sub (m : σ →₀ ℕ) (p q : MvPolynomial σ R) : coeff m (p - q) = coeff m p - coeff m q :=
  Finsupp.sub_apply _ _ _

@[simp]
theorem support_neg : (-p).support = p.support :=
  Finsupp.support_neg p

theorem support_sub (p q : MvPolynomial σ R) : (p - q).support ⊆ p.support ∪ q.support :=
  Finsupp.support_sub

variable {σ} (p)

section Degrees

theorem degrees_neg (p : MvPolynomial σ R) : (-p).degrees = p.degrees := by
  rw [degrees, support_neg] <;> rfl

theorem degrees_sub (p q : MvPolynomial σ R) : (p - q).degrees ≤ p.degrees⊔q.degrees := by
  simpa only [← sub_eq_add_neg] using
    le_transₓ (degrees_add p (-q))
      (by
        rw [degrees_neg])

end Degrees

section Vars

variable (p q)

@[simp]
theorem vars_neg : (-p).vars = p.vars := by
  simp [← vars, ← degrees_neg]

theorem vars_sub_subset : (p - q).vars ⊆ p.vars ∪ q.vars := by
  convert vars_add_subset p (-q) using 2 <;> simp [← sub_eq_add_neg]

variable {p q}

@[simp]
theorem vars_sub_of_disjoint (hpq : Disjoint p.vars q.vars) : (p - q).vars = p.vars ∪ q.vars := by
  rw [← vars_neg q] at hpq
  convert vars_add_of_disjoint hpq using 2 <;> simp [← sub_eq_add_neg]

end Vars

section Eval₂

variable [CommRingₓ S]

variable (f : R →+* S) (g : σ → S)

@[simp]
theorem eval₂_sub : (p - q).eval₂ f g = p.eval₂ f g - q.eval₂ f g :=
  (eval₂Hom f g).map_sub _ _

@[simp]
theorem eval₂_neg : (-p).eval₂ f g = -p.eval₂ f g :=
  (eval₂Hom f g).map_neg _

theorem hom_C (f : MvPolynomial σ ℤ →+* S) (n : ℤ) : f (c n) = (n : S) :=
  (f.comp c).eq_int_cast n

/-- A ring homomorphism f : Z[X_1, X_2, ...] → R
is determined by the evaluations f(X_1), f(X_2), ... -/
@[simp]
theorem eval₂_hom_X {R : Type u} (c : ℤ →+* S) (f : MvPolynomial R ℤ →+* S) (x : MvPolynomial R ℤ) :
    eval₂ c (f ∘ X) x = f x :=
  MvPolynomial.induction_on x
    (fun n => by
      rw [hom_C f, eval₂_C]
      exact c.eq_int_cast n)
    (fun p q hp hq => by
      rw [eval₂_add, hp, hq]
      exact (f.map_add _ _).symm)
    fun p n hp => by
    rw [eval₂_mul, eval₂_X, hp]
    exact (f.map_mul _ _).symm

/-- Ring homomorphisms out of integer polynomials on a type `σ` are the same as
functions out of the type `σ`, -/
def homEquiv : (MvPolynomial σ ℤ →+* S) ≃ (σ → S) where
  toFun := fun f => ⇑f ∘ X
  invFun := fun f => eval₂Hom (Int.castRingHom S) f
  left_inv := fun f => RingHom.ext <| eval₂_hom_X _ _
  right_inv := fun f =>
    funext fun x => by
      simp only [← coe_eval₂_hom, ← Function.comp_app, ← eval₂_X]

end Eval₂

section DegreeOf

theorem degree_of_sub_lt {x : σ} {f g : MvPolynomial σ R} {k : ℕ} (h : 0 < k)
    (hf : ∀ m : σ →₀ ℕ, m ∈ f.support → k ≤ m x → coeff m f = coeff m g)
    (hg : ∀ m : σ →₀ ℕ, m ∈ g.support → k ≤ m x → coeff m f = coeff m g) : degreeOf x (f - g) < k := by
  rw [degree_of_lt_iff h]
  intro m hm
  by_contra hc
  simp only [← not_ltₓ] at hc
  have h := support_sub σ f g hm
  simp only [← mem_support_iff, ← Ne.def, ← coeff_sub, ← sub_eq_zero] at hm
  cases' Finset.mem_union.1 h with cf cg
  · exact hm (hf m cf hc)
    
  · exact hm (hg m cg hc)
    

end DegreeOf

section TotalDegree

@[simp]
theorem total_degree_neg (a : MvPolynomial σ R) : (-a).totalDegree = a.totalDegree := by
  simp only [← total_degree, ← support_neg]

theorem total_degree_sub (a b : MvPolynomial σ R) : (a - b).totalDegree ≤ max a.totalDegree b.totalDegree :=
  calc
    (a - b).totalDegree = (a + -b).totalDegree := by
      rw [sub_eq_add_neg]
    _ ≤ max a.totalDegree (-b).totalDegree := total_degree_add a (-b)
    _ = max a.totalDegree b.totalDegree := by
      rw [total_degree_neg]
    

end TotalDegree

end CommRingₓ

end MvPolynomial

