/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.Tactic.Abel
import Mathbin.Data.Polynomial.Eval

/-!
# The Pochhammer polynomials

We define and prove some basic relations about
`pochhammer S n : S[X] := X * (X + 1) * ... * (X + n - 1)`
which is also known as the rising factorial. A version of this definition
that is focused on `nat` can be found in `data.nat.factorial` as `nat.asc_factorial`.

## Implementation

As with many other families of polynomials, even though the coefficients are always in `ℕ`,
we define the polynomial with coefficients in any `[semiring S]`.

## TODO

There is lots more in this direction:
* q-factorials, q-binomials, q-Pochhammer.
-/


universe u v

open Polynomial

open Polynomial

section Semiringₓ

variable (S : Type u) [Semiringₓ S]

/-- `pochhammer S n` is the polynomial `X * (X+1) * ... * (X + n - 1)`,
with coefficients in the semiring `S`.
-/
noncomputable def pochhammer : ℕ → S[X]
  | 0 => 1
  | n + 1 => X * (pochhammer n).comp (X + 1)

@[simp]
theorem pochhammer_zero : pochhammer S 0 = 1 :=
  rfl

@[simp]
theorem pochhammer_one : pochhammer S 1 = X := by
  simp [← pochhammer]

theorem pochhammer_succ_left (n : ℕ) : pochhammer S (n + 1) = X * (pochhammer S n).comp (X + 1) := by
  rw [pochhammer]

section

variable {S} {T : Type v} [Semiringₓ T]

@[simp]
theorem pochhammer_map (f : S →+* T) (n : ℕ) : (pochhammer S n).map f = pochhammer T n := by
  induction' n with n ih
  · simp
    
  · simp [← ih, ← pochhammer_succ_left, ← map_comp]
    

end

@[simp, norm_cast]
theorem pochhammer_eval_cast (n k : ℕ) : ((pochhammer ℕ n).eval k : S) = (pochhammer S n).eval k := by
  rw [← pochhammer_map (algebraMap ℕ S), eval_map, ← eq_nat_cast (algebraMap ℕ S), eval₂_at_nat_cast, Nat.cast_id,
    eq_nat_cast]

theorem pochhammer_eval_zero {n : ℕ} : (pochhammer S n).eval 0 = if n = 0 then 1 else 0 := by
  cases n
  · simp
    
  · simp [← X_mul, ← Nat.succ_ne_zero, ← pochhammer_succ_left]
    

theorem pochhammer_zero_eval_zero : (pochhammer S 0).eval 0 = 1 := by
  simp

@[simp]
theorem pochhammer_ne_zero_eval_zero {n : ℕ} (h : n ≠ 0) : (pochhammer S n).eval 0 = 0 := by
  simp [← pochhammer_eval_zero, ← h]

theorem pochhammer_succ_right (n : ℕ) : pochhammer S (n + 1) = pochhammer S n * (X + n) := by
  suffices h : pochhammer ℕ (n + 1) = pochhammer ℕ n * (X + n)
  · apply_fun Polynomial.map (algebraMap ℕ S)  at h
    simpa only [← pochhammer_map, ← Polynomial.map_mul, ← Polynomial.map_add, ← map_X, ← Polynomial.map_nat_cast] using
      h
    
  induction' n with n ih
  · simp
    
  · conv_lhs =>
      rw [pochhammer_succ_left, ih, mul_comp, ← mul_assoc, ← pochhammer_succ_left, add_comp, X_comp, nat_cast_comp,
        add_assocₓ, add_commₓ (1 : ℕ[X]), ← Nat.cast_succₓ]
    

theorem pochhammer_succ_eval {S : Type _} [Semiringₓ S] (n : ℕ) (k : S) :
    (pochhammer S (n + 1)).eval k = (pochhammer S n).eval k * (k + n) := by
  rw [pochhammer_succ_right, mul_addₓ, eval_add, eval_mul_X, ← Nat.cast_comm, ← C_eq_nat_cast, eval_C_mul,
    Nat.cast_comm, ← mul_addₓ]

theorem pochhammer_succ_comp_X_add_one (n : ℕ) :
    (pochhammer S (n + 1)).comp (X + 1) = pochhammer S (n + 1) + (n + 1) • (pochhammer S n).comp (X + 1) := by
  suffices (pochhammer ℕ (n + 1)).comp (X + 1) = pochhammer ℕ (n + 1) + (n + 1) * (pochhammer ℕ n).comp (X + 1) by
    simpa [← map_comp] using congr_arg (Polynomial.map (Nat.castRingHom S)) this
  nth_rw 1[pochhammer_succ_left]
  rw [← add_mulₓ, pochhammer_succ_right ℕ n, mul_comp, mul_comm, add_comp, X_comp, nat_cast_comp, add_commₓ ↑n, ←
    add_assocₓ]

theorem Polynomial.mul_X_add_nat_cast_comp {p q : S[X]} {n : ℕ} : (p * (X + n)).comp q = p.comp q * (q + n) := by
  rw [mul_addₓ, add_comp, mul_X_comp, ← Nat.cast_comm, nat_cast_mul_comp, Nat.cast_comm, mul_addₓ]

theorem pochhammer_mul (n m : ℕ) : pochhammer S n * (pochhammer S m).comp (X + n) = pochhammer S (n + m) := by
  induction' m with m ih
  · simp
    
  · rw [pochhammer_succ_right, Polynomial.mul_X_add_nat_cast_comp, ← mul_assoc, ih, Nat.succ_eq_add_one, ← add_assocₓ,
      pochhammer_succ_right, Nat.cast_addₓ, add_assocₓ]
    

theorem pochhammer_nat_eq_asc_factorial (n : ℕ) : ∀ k, (pochhammer ℕ k).eval (n + 1) = n.ascFactorial k
  | 0 => by
    erw [eval_one] <;> rfl
  | t + 1 => by
    rw [pochhammer_succ_right, eval_mul, pochhammer_nat_eq_asc_factorial t]
    suffices n.asc_factorial t * (n + 1 + t) = n.asc_factorial (t + 1) by
      simpa
    rw [Nat.asc_factorial_succ, add_right_commₓ, mul_comm]

theorem pochhammer_nat_eq_desc_factorial (a b : ℕ) : (pochhammer ℕ b).eval a = (a + b - 1).descFactorial b := by
  cases b
  · rw [Nat.desc_factorial_zero, pochhammer_zero, Polynomial.eval_one]
    
  rw [Nat.add_succ, Nat.succ_sub_succ, tsub_zero]
  cases a
  · rw [pochhammer_ne_zero_eval_zero _ b.succ_ne_zero, zero_addₓ, Nat.desc_factorial_of_lt b.lt_succ_self]
    
  · rw [Nat.succ_add, ← Nat.add_succ, Nat.add_desc_factorial_eq_asc_factorial, pochhammer_nat_eq_asc_factorial]
    

end Semiringₓ

section OrderedSemiring

variable {S : Type _} [OrderedSemiring S] [Nontrivial S]

theorem pochhammer_pos (n : ℕ) (s : S) (h : 0 < s) : 0 < (pochhammer S n).eval s := by
  induction' n with n ih
  · simp only [← Nat.nat_zero_eq_zero, ← pochhammer_zero, ← eval_one]
    exact zero_lt_one
    
  · rw [pochhammer_succ_right, mul_addₓ, eval_add, ← Nat.cast_comm, eval_nat_cast_mul, eval_mul_X, Nat.cast_comm, ←
      mul_addₓ]
    exact mul_pos ih (lt_of_lt_of_leₓ h ((le_add_iff_nonneg_right _).mpr (Nat.cast_nonneg n)))
    

end OrderedSemiring

section Factorial

open Nat

variable (S : Type _) [Semiringₓ S] (r n : ℕ)

@[simp]
theorem pochhammer_eval_one (S : Type _) [Semiringₓ S] (n : ℕ) : (pochhammer S n).eval (1 : S) = (n ! : S) := by
  rw_mod_cast[pochhammer_nat_eq_asc_factorial, Nat.zero_asc_factorial]

theorem factorial_mul_pochhammer (S : Type _) [Semiringₓ S] (r n : ℕ) :
    (r ! : S) * (pochhammer S n).eval (r + 1) = (r + n)! := by
  rw_mod_cast[pochhammer_nat_eq_asc_factorial, Nat.factorial_mul_asc_factorial]

theorem pochhammer_nat_eval_succ (r : ℕ) :
    ∀ n : ℕ, n * (pochhammer ℕ r).eval (n + 1) = (n + r) * (pochhammer ℕ r).eval n
  | 0 => by
    by_cases' h : r = 0
    · simp only [← h, ← zero_mul, ← zero_addₓ]
      
    · simp only [← pochhammer_eval_zero, ← zero_mul, ← if_neg h, ← mul_zero]
      
  | k + 1 => by
    simp only [← pochhammer_nat_eq_asc_factorial, ← Nat.succ_asc_factorial, ← add_right_commₓ]

theorem pochhammer_eval_succ (r n : ℕ) :
    (n : S) * (pochhammer S r).eval (n + 1 : S) = (n + r) * (pochhammer S r).eval n := by
  exact_mod_cast congr_arg Nat.castₓ (pochhammer_nat_eval_succ r n)

end Factorial

