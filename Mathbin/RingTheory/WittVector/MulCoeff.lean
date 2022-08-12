/-
Copyright (c) 2022 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Heather Macbeth
-/
import Mathbin.RingTheory.WittVector.Truncated
import Mathbin.Data.MvPolynomial.Supported

/-!
# Leading terms of Witt vector multiplication

The goal of this file is to study the leading terms of the formula for the `n+1`st coefficient
of a product of Witt vectors `x` and `y` over a ring of characteristic `p`.
We aim to isolate the `n+1`st coefficients of `x` and `y`, and express the rest of the product
in terms of a function of the lower coefficients.

For most of this file we work with terms of type `mv_polynomial (fin 2 × ℕ) ℤ`.
We will eventually evaluate them in `k`, but first we must take care of a calculation
that needs to happen in characteristic 0.

## Main declarations

* `witt_vector.nth_mul_coeff`: expresses the coefficient of a product of Witt vectors
  in terms of the previous coefficients of the multiplicands.

-/


noncomputable section

namespace WittVector

variable (p : ℕ) [hp : Fact p.Prime]

variable {k : Type _} [CommRingₓ k]

-- mathport name: «expr𝕎»
local notation "𝕎" => WittVector p

open Finset MvPolynomial

open BigOperators

/-- ```
(∑ i in range n, (y.coeff i)^(p^(n-i)) * p^i.val) *
  (∑ i in range n, (y.coeff i)^(p^(n-i)) * p^i.val)
```
-/
def wittPolyProd (n : ℕ) : MvPolynomial (Finₓ 2 × ℕ) ℤ :=
  rename (Prod.mk (0 : Finₓ 2)) (wittPolynomial p ℤ n) * rename (Prod.mk (1 : Finₓ 2)) (wittPolynomial p ℤ n)

include hp

theorem witt_poly_prod_vars (n : ℕ) : (wittPolyProd p n).vars ⊆ Finset.univ.product (Finset.range (n + 1)) := by
  rw [witt_poly_prod]
  apply subset.trans (vars_mul _ _)
  apply union_subset <;>
    · apply subset.trans (vars_rename _ _)
      simp [← witt_polynomial_vars, ← image_subset_iff]
      

/-- The "remainder term" of `witt_vector.witt_poly_prod`. See `mul_poly_of_interest_aux2`. -/
def wittPolyProdRemainder (n : ℕ) : MvPolynomial (Finₓ 2 × ℕ) ℤ :=
  ∑ i in range n, p ^ i * wittMul p i ^ p ^ (n - i)

theorem witt_poly_prod_remainder_vars (n : ℕ) :
    (wittPolyProdRemainder p n).vars ⊆ Finset.univ.product (Finset.range n) := by
  rw [witt_poly_prod_remainder]
  apply subset.trans (vars_sum_subset _ _)
  rw [bUnion_subset]
  intro x hx
  apply subset.trans (vars_mul _ _)
  apply union_subset
  · apply subset.trans (vars_pow _ _)
    have : (p : MvPolynomial (Finₓ 2 × ℕ) ℤ) = C (p : ℤ) := by
      simp only [← Int.cast_coe_nat, ← RingHom.eq_int_cast]
    rw [this, vars_C]
    apply empty_subset
    
  · apply subset.trans (vars_pow _ _)
    apply subset.trans (witt_mul_vars _ _)
    apply product_subset_product (subset.refl _)
    simp only [← mem_range, ← range_subset] at hx⊢
    exact hx
    

omit hp

/-- `remainder p n` represents the remainder term from `mul_poly_of_interest_aux3`.
`witt_poly_prod p (n+1)` will have variables up to `n+1`,
but `remainder` will only have variables up to `n`.
-/
def remainder (n : ℕ) : MvPolynomial (Finₓ 2 × ℕ) ℤ :=
  (∑ x : ℕ in range (n + 1), (rename (Prod.mk 0)) ((monomial (Finsupp.single x (p ^ (n + 1 - x)))) (↑p ^ x))) *
    ∑ x : ℕ in range (n + 1), (rename (Prod.mk 1)) ((monomial (Finsupp.single x (p ^ (n + 1 - x)))) (↑p ^ x))

include hp

theorem remainder_vars (n : ℕ) : (remainder p n).vars ⊆ univ.product (range (n + 1)) := by
  rw [remainder]
  apply subset.trans (vars_mul _ _)
  apply union_subset <;>
    · apply subset.trans (vars_sum_subset _ _)
      rw [bUnion_subset]
      intro x hx
      rw [rename_monomial, vars_monomial, Finsupp.map_domain_single]
      · apply subset.trans Finsupp.support_single_subset
        simp [← hx]
        
      · apply pow_ne_zero
        exact_mod_cast hp.out.ne_zero
        
      

/-- This is the polynomial whose degree we want to get a handle on. -/
def polyOfInterest (n : ℕ) : MvPolynomial (Finₓ 2 × ℕ) ℤ :=
  wittMul p (n + 1) + p ^ (n + 1) * x (0, n + 1) * x (1, n + 1) -
      x (0, n + 1) * rename (Prod.mk (1 : Finₓ 2)) (wittPolynomial p ℤ (n + 1)) -
    x (1, n + 1) * rename (Prod.mk (0 : Finₓ 2)) (wittPolynomial p ℤ (n + 1))

theorem mul_poly_of_interest_aux1 (n : ℕ) :
    (∑ i in range (n + 1), p ^ i * wittMul p i ^ p ^ (n - i) : MvPolynomial (Finₓ 2 × ℕ) ℤ) = wittPolyProd p n := by
  simp only [← witt_poly_prod]
  convert witt_structure_int_prop p (X (0 : Finₓ 2) * X 1) n using 1
  · simp only [← wittPolynomial, ← witt_mul]
    rw [AlgHom.map_sum]
    congr 1 with i
    congr 1
    have hsupp : (Finsupp.single i (p ^ (n - i))).support = {i} := by
      rw [Finsupp.support_eq_singleton]
      simp only [← and_trueₓ, ← Finsupp.single_eq_same, ← eq_self_iff_true, ← Ne.def]
      exact pow_ne_zero _ hp.out.ne_zero
    simp only [← bind₁_monomial, ← hsupp, ← Int.cast_coe_nat, ← prod_singleton, ← RingHom.eq_int_cast, ←
      Finsupp.single_eq_same, ← C_pow, ← mul_eq_mul_left_iff, ← true_orₓ, ← eq_self_iff_true]
    
  · simp only [← map_mul, ← bind₁_X_right]
    

theorem mul_poly_of_interest_aux2 (n : ℕ) :
    (p ^ n * wittMul p n : MvPolynomial (Finₓ 2 × ℕ) ℤ) + wittPolyProdRemainder p n = wittPolyProd p n := by
  convert mul_poly_of_interest_aux1 p n
  rw [sum_range_succ, add_commₓ, Nat.sub_self, pow_zeroₓ, pow_oneₓ]
  rfl

omit hp

theorem mul_poly_of_interest_aux3 (n : ℕ) :
    wittPolyProd p (n + 1) =
      -(p ^ (n + 1) * x (0, n + 1)) * (p ^ (n + 1) * x (1, n + 1)) +
            p ^ (n + 1) * x (0, n + 1) * rename (Prod.mk (1 : Finₓ 2)) (wittPolynomial p ℤ (n + 1)) +
          p ^ (n + 1) * x (1, n + 1) * rename (Prod.mk (0 : Finₓ 2)) (wittPolynomial p ℤ (n + 1)) +
        remainder p n :=
  by
  -- a useful auxiliary fact
  have mvpz : (p ^ (n + 1) : MvPolynomial (Finₓ 2 × ℕ) ℤ) = MvPolynomial.c (↑p ^ (n + 1)) := by
    simp only [← Int.cast_coe_nat, ← RingHom.eq_int_cast, ← C_pow, ← eq_self_iff_true]
  -- unfold definitions and peel off the last entries of the sums.
  rw [witt_poly_prod, wittPolynomial, AlgHom.map_sum, AlgHom.map_sum, sum_range_succ]
  -- these are sums up to `n+2`, so be careful to only unfold to `n+1`.
  conv_lhs => congr skip rw [sum_range_succ]
  simp only [← add_mulₓ, ← mul_addₓ, ← tsub_self, ← pow_zeroₓ, ← AlgHom.map_sum]
  -- rearrange so that the first summand on rhs and lhs is `remainder`, and peel off
  conv_rhs => rw [add_commₓ]
  simp only [← add_assocₓ]
  apply congr_arg (Add.add _)
  conv_rhs => rw [sum_range_succ]
  -- the rest is equal with proper unfolding and `ring`
  simp only [← rename_monomial, ← monomial_eq_C_mul_X, ← map_mul, ← rename_C, ← pow_oneₓ, ← rename_X, ← mvpz]
  simp only [← Int.cast_coe_nat, ← map_pow, ← RingHom.eq_int_cast, ← rename_X, ← pow_oneₓ, ← tsub_self, ← pow_zeroₓ]
  ring

include hp

theorem mul_poly_of_interest_aux4 (n : ℕ) :
    (p ^ (n + 1) * wittMul p (n + 1) : MvPolynomial (Finₓ 2 × ℕ) ℤ) =
      -(p ^ (n + 1) * x (0, n + 1)) * (p ^ (n + 1) * x (1, n + 1)) +
            p ^ (n + 1) * x (0, n + 1) * rename (Prod.mk (1 : Finₓ 2)) (wittPolynomial p ℤ (n + 1)) +
          p ^ (n + 1) * x (1, n + 1) * rename (Prod.mk (0 : Finₓ 2)) (wittPolynomial p ℤ (n + 1)) +
        (remainder p n - wittPolyProdRemainder p (n + 1)) :=
  by
  rw [← add_sub_assoc, eq_sub_iff_add_eq, mul_poly_of_interest_aux2]
  exact mul_poly_of_interest_aux3 _ _

theorem mul_poly_of_interest_aux5 (n : ℕ) :
    (p ^ (n + 1) : MvPolynomial (Finₓ 2 × ℕ) ℤ) * polyOfInterest p n =
      remainder p n - wittPolyProdRemainder p (n + 1) :=
  by
  simp only [← poly_of_interest, ← mul_sub, ← mul_addₓ, ← sub_eq_iff_eq_add']
  rw [mul_poly_of_interest_aux4 p n]
  ring

theorem mul_poly_of_interest_vars (n : ℕ) :
    ((p ^ (n + 1) : MvPolynomial (Finₓ 2 × ℕ) ℤ) * polyOfInterest p n).vars ⊆ univ.product (range (n + 1)) := by
  rw [mul_poly_of_interest_aux5]
  apply subset.trans (vars_sub_subset _ _)
  apply union_subset
  · apply remainder_vars
    
  · apply witt_poly_prod_remainder_vars
    

theorem poly_of_interest_vars_eq (n : ℕ) :
    (polyOfInterest p n).vars =
      ((p ^ (n + 1) : MvPolynomial (Finₓ 2 × ℕ) ℤ) *
          (wittMul p (n + 1) + p ^ (n + 1) * x (0, n + 1) * x (1, n + 1) -
              x (0, n + 1) * rename (Prod.mk (1 : Finₓ 2)) (wittPolynomial p ℤ (n + 1)) -
            x (1, n + 1) * rename (Prod.mk (0 : Finₓ 2)) (wittPolynomial p ℤ (n + 1)))).vars :=
  by
  have : (p ^ (n + 1) : MvPolynomial (Finₓ 2 × ℕ) ℤ) = C (p ^ (n + 1) : ℤ) := by
    simp only [← Int.cast_coe_nat, ← RingHom.eq_int_cast, ← C_pow, ← eq_self_iff_true]
  rw [poly_of_interest, this, vars_C_mul]
  apply pow_ne_zero
  exact_mod_cast hp.out.ne_zero

theorem poly_of_interest_vars (n : ℕ) : (polyOfInterest p n).vars ⊆ univ.product (range (n + 1)) := by
  rw [poly_of_interest_vars_eq] <;> apply mul_poly_of_interest_vars

theorem peval_poly_of_interest (n : ℕ) (x y : 𝕎 k) :
    peval (polyOfInterest p n) ![fun i => x.coeff i, fun i => y.coeff i] =
      ((x * y).coeff (n + 1) + p ^ (n + 1) * x.coeff (n + 1) * y.coeff (n + 1) -
          y.coeff (n + 1) * ∑ i in range (n + 1 + 1), p ^ i * x.coeff i ^ p ^ (n + 1 - i)) -
        x.coeff (n + 1) * ∑ i in range (n + 1 + 1), p ^ i * y.coeff i ^ p ^ (n + 1 - i) :=
  by
  simp only [← poly_of_interest, ← peval, ← map_nat_cast, ← Matrix.head_cons, ← map_pow, ← Function.uncurry_apply_pair,
    ← aeval_X, ← Matrix.cons_val_one, ← map_mul, ← Matrix.cons_val_zero, ← map_sub]
  rw [sub_sub, add_commₓ (_ * _), ← sub_sub]
  have mvpz : (p : MvPolynomial ℕ ℤ) = MvPolynomial.c ↑p := by
    rw [RingHom.eq_int_cast, Int.cast_coe_nat]
  have : ∀ (f : ℤ →+* k) (g : ℕ → k), eval₂ f g p = f p := by
    intros
    rw [mvpz, MvPolynomial.eval₂_C]
  simp [← witt_polynomial_eq_sum_C_mul_X_pow, ← aeval, ← eval₂_rename, ← this, ← mul_coeff, ← peval, ← map_nat_cast, ←
    map_add, ← map_pow, ← map_mul]

variable [CharP k p]

/-- The characteristic `p` version of `peval_poly_of_interest` -/
theorem peval_poly_of_interest' (n : ℕ) (x y : 𝕎 k) :
    peval (polyOfInterest p n) ![fun i => x.coeff i, fun i => y.coeff i] =
      (x * y).coeff (n + 1) - y.coeff (n + 1) * x.coeff 0 ^ p ^ (n + 1) - x.coeff (n + 1) * y.coeff 0 ^ p ^ (n + 1) :=
  by
  rw [peval_poly_of_interest]
  have : (p : k) = 0 := CharP.cast_eq_zero k p
  simp only [← this, ← add_zeroₓ, ← zero_mul, ← Nat.succ_ne_zero, ← Ne.def, ← not_false_iff, ← zero_pow']
  have sum_zero_pow_mul_pow_p :
    ∀ y : 𝕎 k, (∑ x : ℕ in range (n + 1 + 1), 0 ^ x * y.coeff x ^ p ^ (n + 1 - x)) = y.coeff 0 ^ p ^ (n + 1) := by
    intro y
    rw [Finset.sum_eq_single_of_mem 0]
    · simp
      
    · simp
      
    · intro j _ hj
      simp [← zero_pow (zero_lt_iff.mpr hj)]
      
  congr <;> apply sum_zero_pow_mul_pow_p

variable (k)

-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:30:4: unsupported: too many args: fin_cases ... #[[]]
theorem nth_mul_coeff' (n : ℕ) :
    ∃ f : TruncatedWittVector p (n + 1) k → TruncatedWittVector p (n + 1) k → k,
      ∀ x y : 𝕎 k,
        f (truncateFun (n + 1) x) (truncateFun (n + 1) y) =
          (x * y).coeff (n + 1) - y.coeff (n + 1) * x.coeff 0 ^ p ^ (n + 1) -
            x.coeff (n + 1) * y.coeff 0 ^ p ^ (n + 1) :=
  by
  simp only [peval_poly_of_interest']
  obtain ⟨f₀, hf₀⟩ := exists_restrict_to_vars k (poly_of_interest_vars p n)
  let f : TruncatedWittVector p (n + 1) k → TruncatedWittVector p (n + 1) k → k := by
    intro x y
    apply f₀
    rintro ⟨a, ha⟩
    apply Function.uncurry ![x, y]
    simp only [← true_andₓ, ← Multiset.mem_cons, ← range_coe, ← product_val, ← Multiset.mem_range, ←
      Multiset.mem_product, ← Multiset.range_succ, ← mem_univ_val] at ha
    refine' ⟨a.fst, ⟨a.snd, _⟩⟩
    cases' ha with ha ha <;> linarith only [ha]
  use f
  intro x y
  dsimp' [← peval]
  rw [← hf₀]
  simp only [← f, ← Function.uncurry_apply_pair]
  congr
  ext a
  cases' a with a ha
  cases' a with i m
  simp only [← true_andₓ, ← Multiset.mem_cons, ← range_coe, ← product_val, ← Multiset.mem_range, ← Multiset.mem_product,
    ← Multiset.range_succ, ← mem_univ_val] at ha
  have ha' : m < n + 1 := by
    cases' ha with ha ha <;> linarith only [ha]
  fin_cases i <;>-- surely this case split is not necessary
    · simpa only using x.coeff_truncate_fun ⟨m, ha'⟩
      

theorem nth_mul_coeff (n : ℕ) :
    ∃ f : TruncatedWittVector p (n + 1) k → TruncatedWittVector p (n + 1) k → k,
      ∀ x y : 𝕎 k,
        (x * y).coeff (n + 1) =
          x.coeff (n + 1) * y.coeff 0 ^ p ^ (n + 1) + y.coeff (n + 1) * x.coeff 0 ^ p ^ (n + 1) +
            f (truncateFun (n + 1) x) (truncateFun (n + 1) y) :=
  by
  obtain ⟨f, hf⟩ := nth_mul_coeff' p k n
  use f
  intro x y
  rw [hf x y]
  ring

variable {k}

/-- Produces the "remainder function" of the `n+1`st coefficient, which does not depend on the `n+1`st
coefficients of the inputs. -/
def nthRemainder (n : ℕ) : (Finₓ (n + 1) → k) → (Finₓ (n + 1) → k) → k :=
  Classical.some (nth_mul_coeff p k n)

theorem nth_remainder_spec (n : ℕ) (x y : 𝕎 k) :
    (x * y).coeff (n + 1) =
      x.coeff (n + 1) * y.coeff 0 ^ p ^ (n + 1) + y.coeff (n + 1) * x.coeff 0 ^ p ^ (n + 1) +
        nthRemainder p n (truncateFun (n + 1) x) (truncateFun (n + 1) y) :=
  Classical.some_spec (nth_mul_coeff p k n) _ _

end WittVector

