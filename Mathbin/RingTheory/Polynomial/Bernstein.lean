/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.Data.Polynomial.Derivative
import Mathbin.Data.Nat.Choose.Sum
import Mathbin.RingTheory.Polynomial.Pochhammer
import Mathbin.Data.Polynomial.AlgebraMap
import Mathbin.LinearAlgebra.LinearIndependent
import Mathbin.Data.MvPolynomial.Pderiv

/-!
# Bernstein polynomials

The definition of the Bernstein polynomials
```
bernstein_polynomial (R : Type*) [comm_ring R] (n ν : ℕ) : R[X] :=
(choose n ν) * X^ν * (1 - X)^(n - ν)
```
and the fact that for `ν : fin (n+1)` these are linearly independent over `ℚ`.

We prove the basic identities
* `(finset.range (n + 1)).sum (λ ν, bernstein_polynomial R n ν) = 1`
* `(finset.range (n + 1)).sum (λ ν, ν • bernstein_polynomial R n ν) = n • X`
* `(finset.range (n + 1)).sum (λ ν, (ν * (ν-1)) • bernstein_polynomial R n ν) = (n * (n-1)) • X^2`

## Notes

See also `analysis.special_functions.bernstein`, which defines the Bernstein approximations
of a continuous function `f : C([0,1], ℝ)`, and shows that these converge uniformly to `f`.
-/


noncomputable section

open Nat (choose)

open Polynomial (x)

open BigOperators Polynomial

variable (R : Type _) [CommRingₓ R]

/-- `bernstein_polynomial R n ν` is `(choose n ν) * X^ν * (1 - X)^(n - ν)`.

Although the coefficients are integers, it is convenient to work over an arbitrary commutative ring.
-/
def bernsteinPolynomial (n ν : ℕ) : R[X] :=
  choose n ν * X ^ ν * (1 - X) ^ (n - ν)

example : bernsteinPolynomial ℤ 3 2 = 3 * X ^ 2 - 3 * X ^ 3 := by
  norm_num [← bernsteinPolynomial, ← choose]
  ring

namespace bernsteinPolynomial

theorem eq_zero_of_lt {n ν : ℕ} (h : n < ν) : bernsteinPolynomial R n ν = 0 := by
  simp [← bernsteinPolynomial, ← Nat.choose_eq_zero_of_lt h]

section

variable {R} {S : Type _} [CommRingₓ S]

@[simp]
theorem map (f : R →+* S) (n ν : ℕ) : (bernsteinPolynomial R n ν).map f = bernsteinPolynomial S n ν := by
  simp [← bernsteinPolynomial]

end

theorem flip (n ν : ℕ) (h : ν ≤ n) : (bernsteinPolynomial R n ν).comp (1 - X) = bernsteinPolynomial R n (n - ν) := by
  dsimp' [← bernsteinPolynomial]
  simp [← h, ← tsub_tsub_assoc, ← mul_right_commₓ]

theorem flip' (n ν : ℕ) (h : ν ≤ n) : bernsteinPolynomial R n ν = (bernsteinPolynomial R n (n - ν)).comp (1 - X) := by
  rw [← flip _ _ _ h, Polynomial.comp_assoc]
  simp

theorem eval_at_0 (n ν : ℕ) : (bernsteinPolynomial R n ν).eval 0 = if ν = 0 then 1 else 0 := by
  dsimp' [← bernsteinPolynomial]
  split_ifs
  · subst h
    simp
    
  · simp [← zero_pow (Nat.pos_of_ne_zeroₓ h)]
    

theorem eval_at_1 (n ν : ℕ) : (bernsteinPolynomial R n ν).eval 1 = if ν = n then 1 else 0 := by
  dsimp' [← bernsteinPolynomial]
  split_ifs
  · subst h
    simp
    
  · obtain w | w := (n - ν).eq_zero_or_pos
    · simp [← Nat.choose_eq_zero_of_lt ((tsub_eq_zero_iff_le.mp w).lt_of_ne (Ne.symm h))]
      
    · simp [← zero_pow w]
      
    

theorem derivative_succ_aux (n ν : ℕ) :
    (bernsteinPolynomial R (n + 1) (ν + 1)).derivative =
      (n + 1) * (bernsteinPolynomial R n ν - bernsteinPolynomial R n (ν + 1)) :=
  by
  dsimp' [← bernsteinPolynomial]
  suffices
    ↑((n + 1).choose (ν + 1)) * ((↑ν + 1) * X ^ ν) * (1 - X) ^ (n - ν) -
        ↑((n + 1).choose (ν + 1)) * X ^ (ν + 1) * (↑(n - ν) * (1 - X) ^ (n - ν - 1)) =
      (↑n + 1) *
        (↑(n.choose ν) * X ^ ν * (1 - X) ^ (n - ν) - ↑(n.choose (ν + 1)) * X ^ (ν + 1) * (1 - X) ^ (n - (ν + 1)))
    by
    simpa [← Polynomial.derivative_pow, sub_eq_add_neg]
  conv_rhs => rw [mul_sub]
  -- We'll prove the two terms match up separately.
  refine' congr (congr_arg Sub.sub _) _
  · simp only [mul_assoc]
    refine' congr (congr_arg (· * ·) (congr (congr_arg (· * ·) _) rfl)) rfl
    -- Now it's just about binomial coefficients
    exact_mod_cast congr_arg (fun m : ℕ => (m : R[X])) (Nat.succ_mul_choose_eq n ν).symm
    
  · rw [← tsub_add_eq_tsub_tsub, ← mul_assoc, ← mul_assoc]
    congr 1
    rw [mul_comm]
    rw [← mul_assoc, ← mul_assoc]
    congr 1
    norm_cast
    congr 1
    convert (Nat.choose_mul_succ_eq n (ν + 1)).symm using 1
    · convert mul_comm _ _ using 2
      simp
      
    · apply mul_comm
      
    

theorem derivative_succ (n ν : ℕ) :
    (bernsteinPolynomial R n (ν + 1)).derivative =
      n * (bernsteinPolynomial R (n - 1) ν - bernsteinPolynomial R (n - 1) (ν + 1)) :=
  by
  cases n
  · simp [← bernsteinPolynomial]
    
  · rw [Nat.cast_succₓ]
    apply derivative_succ_aux
    

theorem derivative_zero (n : ℕ) : (bernsteinPolynomial R n 0).derivative = -n * bernsteinPolynomial R (n - 1) 0 := by
  dsimp' [← bernsteinPolynomial]
  simp [← Polynomial.derivative_pow]

theorem iterate_derivative_at_0_eq_zero_of_lt (n : ℕ) {ν k : ℕ} :
    k < ν → ((Polynomial.derivative^[k]) (bernsteinPolynomial R n ν)).eval 0 = 0 := by
  cases ν
  · rintro ⟨⟩
    
  · rw [Nat.lt_succ_iffₓ]
    induction' k with k ih generalizing n ν
    · simp [← eval_at_0]
      
    · simp only [← derivative_succ, ← Int.coe_nat_eq_zero, ← mul_eq_zero, ← Function.comp_app, ← Function.iterate_succ,
        ← Polynomial.iterate_derivative_sub, ← Polynomial.iterate_derivative_cast_nat_mul, ← Polynomial.eval_mul, ←
        Polynomial.eval_nat_cast, ← Polynomial.eval_sub]
      intro h
      apply mul_eq_zero_of_right
      rw [ih _ _ (Nat.le_of_succ_leₓ h), sub_zero]
      convert ih _ _ (Nat.pred_le_predₓ h)
      exact (Nat.succ_pred_eq_of_posₓ (k.succ_pos.trans_le h)).symm
      
    

@[simp]
theorem iterate_derivative_succ_at_0_eq_zero (n ν : ℕ) :
    ((Polynomial.derivative^[ν]) (bernsteinPolynomial R n (ν + 1))).eval 0 = 0 :=
  iterate_derivative_at_0_eq_zero_of_lt R n (lt_add_one ν)

open Polynomial

@[simp]
theorem iterate_derivative_at_0 (n ν : ℕ) :
    ((Polynomial.derivative^[ν]) (bernsteinPolynomial R n ν)).eval 0 = (pochhammer R ν).eval (n - (ν - 1) : ℕ) := by
  by_cases' h : ν ≤ n
  · induction' ν with ν ih generalizing n h
    · simp [← eval_at_0]
      
    · have h' : ν ≤ n - 1 := le_tsub_of_add_le_right h
      simp only [← derivative_succ, ← ih (n - 1) h', ← iterate_derivative_succ_at_0_eq_zero, ← Nat.succ_sub_succ_eq_sub,
        ← tsub_zero, ← sub_zero, ← iterate_derivative_sub, ← iterate_derivative_cast_nat_mul, ← eval_one, ← eval_mul, ←
        eval_add, ← eval_sub, ← eval_X, ← eval_comp, ← eval_nat_cast, ← Function.comp_app, ← Function.iterate_succ, ←
        pochhammer_succ_left]
      obtain rfl | h'' := ν.eq_zero_or_pos
      · simp
        
      · have : n - 1 - (ν - 1) = n - ν := by
          rw [← Nat.succ_le_iff] at h''
          rw [← tsub_add_eq_tsub_tsub, add_commₓ, tsub_add_cancel_of_le h'']
        rw [this, pochhammer_eval_succ]
        rw_mod_cast[tsub_add_cancel_of_le (h'.trans n.pred_le)]
        
      
    
  · simp only [← not_leₓ] at h
    rw [tsub_eq_zero_iff_le.mpr (Nat.le_pred_of_ltₓ h), eq_zero_of_lt R h]
    simp [← pos_iff_ne_zero.mp (pos_of_gt h)]
    

theorem iterate_derivative_at_0_ne_zero [CharZero R] (n ν : ℕ) (h : ν ≤ n) :
    ((Polynomial.derivative^[ν]) (bernsteinPolynomial R n ν)).eval 0 ≠ 0 := by
  simp only [← Int.coe_nat_eq_zero, ← bernsteinPolynomial.iterate_derivative_at_0, ← Ne.def, ← Nat.cast_eq_zero]
  simp only [pochhammer_eval_cast]
  norm_cast
  apply ne_of_gtₓ
  obtain rfl | h' := Nat.eq_zero_or_posₓ ν
  · simp
    
  · rw [← Nat.succ_pred_eq_of_posₓ h'] at h
    exact pochhammer_pos _ _ (tsub_pos_of_lt (Nat.lt_of_succ_leₓ h))
    

/-!
Rather than redoing the work of evaluating the derivatives at 1,
we use the symmetry of the Bernstein polynomials.
-/


theorem iterate_derivative_at_1_eq_zero_of_lt (n : ℕ) {ν k : ℕ} :
    k < n - ν → ((Polynomial.derivative^[k]) (bernsteinPolynomial R n ν)).eval 1 = 0 := by
  intro w
  rw [flip' _ _ _ (tsub_pos_iff_lt.mp (pos_of_gt w)).le]
  simp [← Polynomial.eval_comp, ← iterate_derivative_at_0_eq_zero_of_lt R n w]

@[simp]
theorem iterate_derivative_at_1 (n ν : ℕ) (h : ν ≤ n) :
    ((Polynomial.derivative^[n - ν]) (bernsteinPolynomial R n ν)).eval 1 =
      -1 ^ (n - ν) * (pochhammer R (n - ν)).eval (ν + 1) :=
  by
  rw [flip' _ _ _ h]
  simp [← Polynomial.eval_comp, ← h]
  obtain rfl | h' := h.eq_or_lt
  · simp
    
  · congr
    norm_cast
    rw [← tsub_add_eq_tsub_tsub, tsub_tsub_cancel_of_le (nat.succ_le_iff.mpr h')]
    

theorem iterate_derivative_at_1_ne_zero [CharZero R] (n ν : ℕ) (h : ν ≤ n) :
    ((Polynomial.derivative^[n - ν]) (bernsteinPolynomial R n ν)).eval 1 ≠ 0 := by
  rw [bernsteinPolynomial.iterate_derivative_at_1 _ _ _ h, Ne.def, neg_one_pow_mul_eq_zero_iff, ← Nat.cast_succₓ, ←
    pochhammer_eval_cast, ← Nat.cast_zeroₓ, Nat.cast_inj]
  exact (pochhammer_pos _ _ (Nat.succ_posₓ ν)).ne'

open Submodule

theorem linear_independent_aux (n k : ℕ) (h : k ≤ n + 1) :
    LinearIndependent ℚ fun ν : Finₓ k => bernsteinPolynomial ℚ n ν := by
  induction' k with k ih
  · apply linear_independent_empty_type
    
  · apply linear_independent_fin_succ'.mpr
    fconstructor
    · exact ih (le_of_ltₓ h)
      
    · -- The actual work!
      -- We show that the (n-k)-th derivative at 1 doesn't vanish,
      -- but vanishes for everything in the span.
      clear ih
      simp only [← Nat.succ_eq_add_one, ← add_le_add_iff_right] at h
      simp only [← Finₓ.coe_last, ← Finₓ.init_def]
      dsimp'
      apply not_mem_span_of_apply_not_mem_span_image (@Polynomial.derivative ℚ _ ^ (n - k))
      simp only [← not_exists, ← not_and, ← Submodule.mem_map, ← Submodule.span_image]
      intro p m
      apply_fun Polynomial.eval (1 : ℚ)
      simp only [← LinearMap.pow_apply]
      -- The right hand side is nonzero,
      -- so it will suffice to show the left hand side is always zero.
      suffices ((Polynomial.derivative^[n - k]) p).eval 1 = 0 by
        rw [this]
        exact (iterate_derivative_at_1_ne_zero ℚ n k h).symm
      apply span_induction m
      · simp
        rintro ⟨a, w⟩
        simp only [← Finₓ.coe_mk]
        rw [iterate_derivative_at_1_eq_zero_of_lt ℚ n ((tsub_lt_tsub_iff_left_of_le h).mpr w)]
        
      · simp
        
      · intro x y hx hy
        simp [← hx, ← hy]
        
      · intro a x h
        simp [← h]
        
      
    

/-- The Bernstein polynomials are linearly independent.

We prove by induction that the collection of `bernstein_polynomial n ν` for `ν = 0, ..., k`
are linearly independent.
The inductive step relies on the observation that the `(n-k)`-th derivative, evaluated at 1,
annihilates `bernstein_polynomial n ν` for `ν < k`, but has a nonzero value at `ν = k`.
-/
theorem linear_independent (n : ℕ) : LinearIndependent ℚ fun ν : Finₓ (n + 1) => bernsteinPolynomial ℚ n ν :=
  linear_independent_aux n (n + 1) le_rfl

theorem sum (n : ℕ) : (∑ ν in Finset.range (n + 1), bernsteinPolynomial R n ν) = 1 :=
  calc
    (∑ ν in Finset.range (n + 1), bernsteinPolynomial R n ν) = (X + (1 - X)) ^ n := by
      rw [add_pow]
      simp only [← bernsteinPolynomial, ← mul_comm, ← mul_assoc, ← mul_left_commₓ]
    _ = 1 := by
      simp
    

open Polynomial

open MvPolynomial

theorem sum_smul (n : ℕ) : (∑ ν in Finset.range (n + 1), ν • bernsteinPolynomial R n ν) = n • X := by
  -- We calculate the `x`-derivative of `(x+y)^n`, evaluated at `y=(1-x)`,
  -- either directly or by using the binomial theorem.
  -- We'll work in `mv_polynomial bool R`.
  let x : MvPolynomial Bool R := MvPolynomial.x tt
  let y : MvPolynomial Bool R := MvPolynomial.x ff
  have pderiv_tt_x : pderiv tt x = 1 := by
    simp [← x]
  have pderiv_tt_y : pderiv tt y = 0 := by
    simp [← pderiv_X, ← y]
  let e : Bool → R[X] := fun i => cond i X (1 - X)
  -- Start with `(x+y)^n = (x+y)^n`,
  -- take the `x`-derivative, evaluate at `x=X, y=1-X`, and multiply by `X`:
  have h : (x + y) ^ n = (x + y) ^ n := rfl
  apply_fun pderiv tt  at h
  apply_fun aeval e  at h
  apply_fun fun p => p * X  at h
  -- On the left hand side we'll use the binomial theorem, then simplify.
  -- We first prepare a tedious rewrite:
  have w :
    ∀ k : ℕ,
      ↑k * Polynomial.x ^ (k - 1) * (1 - Polynomial.x) ^ (n - k) * ↑(n.choose k) * Polynomial.x =
        k • bernsteinPolynomial R n k :=
    by
    rintro (_ | k)
    · simp
      
    · dsimp' [← bernsteinPolynomial]
      simp only [nat_cast_mul, ← Nat.succ_eq_add_one, ← Nat.add_succ_sub_one, ← add_zeroₓ, ← pow_succₓ]
      push_cast
      ring
      
  conv at h =>
    lhs rw [add_pow, (pderiv tt).map_sum, (MvPolynomial.aeval e).map_sum, Finset.sum_mul]-- Step inside the sum:
    apply_congr skip simp [← pderiv_mul, ← pderiv_tt_x, ← pderiv_tt_y, ← e, ← w]
  -- On the right hand side, we'll just simplify.
  conv at h => rhs rw [(pderiv tt).leibniz_pow, (pderiv tt).map_add, pderiv_tt_x, pderiv_tt_y]simp [← e]
  simpa using h

theorem sum_mul_smul (n : ℕ) :
    (∑ ν in Finset.range (n + 1), (ν * (ν - 1)) • bernsteinPolynomial R n ν) = (n * (n - 1)) • X ^ 2 := by
  -- We calculate the second `x`-derivative of `(x+y)^n`, evaluated at `y=(1-x)`,
  -- either directly or by using the binomial theorem.
  -- We'll work in `mv_polynomial bool R`.
  let x : MvPolynomial Bool R := MvPolynomial.x tt
  let y : MvPolynomial Bool R := MvPolynomial.x ff
  have pderiv_tt_x : pderiv tt x = 1 := by
    simp [← x]
  have pderiv_tt_y : pderiv tt y = 0 := by
    simp [← pderiv_X, ← y]
  let e : Bool → R[X] := fun i => cond i X (1 - X)
  -- Start with `(x+y)^n = (x+y)^n`,
  -- take the second `x`-derivative, evaluate at `x=X, y=1-X`, and multiply by `X`:
  have h : (x + y) ^ n = (x + y) ^ n := rfl
  apply_fun pderiv tt  at h
  apply_fun pderiv tt  at h
  apply_fun aeval e  at h
  apply_fun fun p => p * X ^ 2  at h
  -- On the left hand side we'll use the binomial theorem, then simplify.
  -- We first prepare a tedious rewrite:
  have w :
    ∀ k : ℕ,
      ↑k * (↑(k - 1) * Polynomial.x ^ (k - 1 - 1)) * (1 - Polynomial.x) ^ (n - k) * ↑(n.choose k) * Polynomial.x ^ 2 =
        (k * (k - 1)) • bernsteinPolynomial R n k :=
    by
    rintro (_ | k)
    · simp
      
    · rcases k with (_ | k)
      · simp
        
      · dsimp' [← bernsteinPolynomial]
        simp only [nat_cast_mul, ← Nat.succ_eq_add_one, ← Nat.add_succ_sub_one, ← add_zeroₓ, ← pow_succₓ]
        push_cast
        ring
        
      
  conv at h =>
    lhs rw [add_pow, (pderiv tt).map_sum, (pderiv tt).map_sum, (MvPolynomial.aeval e).map_sum,
      Finset.sum_mul]-- Step inside the sum:
    apply_congr skip simp [← pderiv_mul, ← pderiv_tt_x, ← pderiv_tt_y, ← e, ← w]
  -- On the right hand side, we'll just simplify.
  conv at h =>
    rhs simp only [← pderiv_one, ← pderiv_mul, ← (pderiv _).leibniz_pow, ← (pderiv _).map_coe_nat, ←
      (pderiv tt).map_add, ← pderiv_tt_x, ← pderiv_tt_y]simp [← e, ← smul_smul]
  simpa using h

/-- A certain linear combination of the previous three identities,
which we'll want later.
-/
theorem variance (n : ℕ) :
    (∑ ν in Finset.range (n + 1), (n • Polynomial.x - ν) ^ 2 * bernsteinPolynomial R n ν) =
      n • Polynomial.x * (1 - Polynomial.x) :=
  by
  have p :
    ((((Finset.range (n + 1)).Sum fun ν => (ν * (ν - 1)) • bernsteinPolynomial R n ν) +
          (1 - (2 * n) • Polynomial.x) * (Finset.range (n + 1)).Sum fun ν => ν • bernsteinPolynomial R n ν) +
        n ^ 2 • X ^ 2 * (Finset.range (n + 1)).Sum fun ν => bernsteinPolynomial R n ν) =
      _ :=
    rfl
  conv at p =>
    lhs rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ←
      Finset.sum_add_distrib]simp only [nat_cast_mul]simp only [mul_assoc]simp only [add_mulₓ]
  conv at p => rhs rw [Sum, sum_smul, sum_mul_smul, ← nat_cast_mul]
  calc _ = _ := Finset.sum_congr rfl fun k m => _ _ = _ := p _ = _ := _
  · congr 1
    simp' only [nat_cast_mul] with push_cast
    cases k <;>
      · simp
        ring
        
    
  · simp' only [nat_cast_mul] with push_cast
    cases n
    · simp
      
    · simp
      ring
      
    

end bernsteinPolynomial

