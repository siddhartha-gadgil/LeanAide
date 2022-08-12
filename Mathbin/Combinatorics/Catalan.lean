/-
Copyright (c) 2022 Julian Kuelshammer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julian Kuelshammer
-/
import Mathbin.Data.Nat.Choose.Central
import Mathbin.Algebra.BigOperators.Fin
import Mathbin.Tactic.FieldSimp
import Mathbin.Tactic.LinearCombination

/-!
# Catalan numbers

The Catalan numbers (http://oeis.org/A000108) are probably the most ubiquitous sequence of integers
in mathematics. They enumerate several important objects like binary trees, Dyck paths, and
triangulations of convex polygons.

## Main definitions

* `catalan n`: the `n`th Catalan number, defined recursively as
  `catalan (n + 1) = ∑ i : fin n.succ, catalan i * catalan (n - i)`.

## Main results

* `catalan_eq_central_binom_div `: The explicit formula for the Catalan number using the central
  binomial coefficient, `catalan n = nat.central_binom n / (n + 1)`.

## Implementation details

The proof of `catalan_eq_central_binom_div` follows
https://math.stackexchange.com/questions/3304415/catalan-numbers-algebraic-proof-of-the-recurrence-relation

## TODO

* Prove that the Catalan numbers enumerate many interesting objects.
* Provide the many variants of Catalan numbers, e.g. associated to complex reflection groups,
  Fuss-Catalan, etc.

-/


open BigOperators

open Finset

/-- The recursive definition of the sequence of Catalan numbers:
`catalan (n + 1) = ∑ i : fin n.succ, catalan i * catalan (n - i)` -/
def catalan : ℕ → ℕ
  | 0 => 1
  | n + 1 =>
    ∑ i : Finₓ n.succ,
      have := i.2
      have := Nat.lt_succ_iffₓ.mpr (n.sub_le i)
      catalan i * catalan (n - i)

@[simp]
theorem catalan_zero : catalan 0 = 1 := by
  rw [catalan]

theorem catalan_succ (n : ℕ) : catalan (n + 1) = ∑ i : Finₓ n.succ, catalan i * catalan (n - i) := by
  rw [catalan]

@[simp]
theorem catalan_one : catalan 1 = 1 := by
  simp [← catalan_succ]

/-- A helper sequence that can be used to prove the equality of the recursive and the explicit
definition using a telescoping sum argument. -/
private def gosper_catalan (n j : ℕ) : ℚ :=
  Nat.centralBinom j * Nat.centralBinom (n - j) * (2 * j - n) / (2 * n * (n + 1))

-- ./././Mathport/Syntax/Translate/Basic.lean:646:40: in linear_combination #[[expr «expr - »(«expr * »(«expr * »(«expr * »(«expr * »(«expr * »(«expr * »((2 : exprℚ()), «expr - »(n, i).central_binom), «expr - »(«expr + »(i, 1), «expr - »(n, i))), «expr + »(n, 1)), «expr + »(n, 2)), «expr + »(«expr - »(n, i), 1)), h₁), «expr * »(«expr * »(«expr * »(«expr * »(«expr * »(«expr * »(2, i.central_binom), «expr + »(n, 1)), «expr + »(n, 2)), «expr - »(«expr - »(i, «expr - »(n, i)), 1)), «expr + »(i, 1)), h₂))],
  []]: ./././Mathport/Syntax/Translate/Basic.lean:319:22: unsupported: too many args
private theorem gosper_trick {n i : ℕ} (h : i ≤ n) :
    gosperCatalan (n + 1) (i + 1) - gosperCatalan (n + 1) i =
      Nat.centralBinom i / (i + 1) * Nat.centralBinom (n - i) / (n - i + 1) :=
  by
  have : (n : ℚ) + 1 ≠ 0 := by
    exact_mod_cast n.succ_ne_zero
  have : (n : ℚ) + 1 + 1 ≠ 0 := by
    exact_mod_cast (n + 1).succ_ne_zero
  have : (i : ℚ) + 1 ≠ 0 := by
    exact_mod_cast i.succ_ne_zero
  have : (n : ℚ) - i + 1 ≠ 0 := by
    exact_mod_cast (n - i).succ_ne_zero
  have h₁ : ((i : ℚ) + 1) * (i + 1).centralBinom = 2 * (2 * i + 1) * i.central_binom := by
    exact_mod_cast Nat.succ_mul_central_binom_succ i
  have h₂ : ((n : ℚ) - i + 1) * (n - i + 1).centralBinom = 2 * (2 * (n - i) + 1) * (n - i).centralBinom := by
    exact_mod_cast Nat.succ_mul_central_binom_succ (n - i)
  simp only [← gosper_catalan]
  push_cast
  field_simp
  rw [Nat.succ_subₓ h]
  trace
    "./././Mathport/Syntax/Translate/Basic.lean:646:40: in linear_combination #[[expr «expr - »(«expr * »(«expr * »(«expr * »(«expr * »(«expr * »(«expr * »((2 : exprℚ()), «expr - »(n, i).central_binom), «expr - »(«expr + »(i, 1), «expr - »(n, i))), «expr + »(n, 1)), «expr + »(n, 2)), «expr + »(«expr - »(n, i), 1)), h₁), «expr * »(«expr * »(«expr * »(«expr * »(«expr * »(«expr * »(2, i.central_binom), «expr + »(n, 1)), «expr + »(n, 2)), «expr - »(«expr - »(i, «expr - »(n, i)), 1)), «expr + »(i, 1)), h₂))],\n  []]: ./././Mathport/Syntax/Translate/Basic.lean:319:22: unsupported: too many args"

private theorem gosper_catalan_sub_eq_central_binom_div (n : ℕ) :
    gosperCatalan (n + 1) (n + 1) - gosperCatalan (n + 1) 0 = Nat.centralBinom (n + 1) / (n + 2) := by
  have : (n : ℚ) + 1 ≠ 0 := by
    exact_mod_cast n.succ_ne_zero
  have : (n : ℚ) + 1 + 1 ≠ 0 := by
    exact_mod_cast (n + 1).succ_ne_zero
  have h : (n : ℚ) + 2 ≠ 0 := by
    exact_mod_cast (n + 1).succ_ne_zero
  simp only [← gosper_catalan, ← Nat.sub_zero, ← Nat.central_binom_zero, ← Nat.sub_self]
  field_simp
  ring

theorem catalan_eq_central_binom_div (n : ℕ) : catalan n = n.centralBinom / (n + 1) := by
  suffices (catalan n : ℚ) = Nat.centralBinom n / (n + 1) by
    have h := Nat.succ_dvd_central_binom n
    exact_mod_cast this
  induction' n using Nat.case_strong_induction_onₓ with d hd
  · simp
    
  · simp_rw [catalan_succ, Nat.cast_sum, Nat.cast_mulₓ]
    trans (∑ i : Finₓ d.succ, Nat.centralBinom i / (i + 1) * (Nat.centralBinom (d - i) / (d - i + 1)) : ℚ)
    · refine' sum_congr rfl fun i _ => _
      congr
      · exact_mod_cast hd i i.is_le
        
      · rw_mod_cast[hd (d - i)]
        push_cast
        rw [Nat.cast_sub i.is_le]
        exact tsub_le_self
        
      
    · trans ∑ i : Finₓ d.succ, gosper_catalan (d + 1) (i + 1) - gosper_catalan (d + 1) i
      · refine' sum_congr rfl fun i _ => _
        rw_mod_cast[gosper_trick i.is_le, mul_div]
        
      · rw [← sum_range fun i => gosper_catalan (d + 1) (i + 1) - gosper_catalan (d + 1) i, sum_range_sub,
          Nat.succ_eq_add_one]
        exact_mod_cast gosper_catalan_sub_eq_central_binom_div d
        
      
    

theorem succ_mul_catalan_eq_central_binom (n : ℕ) : (n + 1) * catalan n = n.centralBinom :=
  (Nat.eq_mul_of_div_eq_right n.succ_dvd_central_binom (catalan_eq_central_binom_div n).symm).symm

theorem catalan_two : catalan 2 = 2 := by
  norm_num [← catalan_eq_central_binom_div, ← Nat.centralBinom, ← Nat.choose]

theorem catalan_three : catalan 3 = 5 := by
  norm_num [← catalan_eq_central_binom_div, ← Nat.centralBinom, ← Nat.choose]

