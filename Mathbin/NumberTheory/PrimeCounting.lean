/-
Copyright (c) 2021 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
import Mathbin.Data.Nat.Prime
import Mathbin.Data.Nat.Totient
import Mathbin.Algebra.Periodic
import Mathbin.Data.Finset.LocallyFinite
import Mathbin.Data.Nat.Count
import Mathbin.Data.Nat.Nth

/-!
# The Prime Counting Function

In this file we define the prime counting function: the function on natural numbers that returns
the number of primes less than or equal to its input.

## Main Results

The main definitions for this file are

- `nat.prime_counting`: The prime counting function π
- `nat.prime_counting'`: π(n - 1)

We then prove that these are monotone in `nat.monotone_prime_counting` and
`nat.monotone_prime_counting'`. The last main theorem `nat.prime_counting'_add_le` is an upper
bound on `π'` which arises by observing that all numbers greater than `k` and not coprime to `k`
are not prime, and so only at most `φ(k)/k` fraction of the numbers from `k` to `n` are prime.

## Notation

We use the standard notation `π` to represent the prime counting function (and `π'` to represent
the reindexed version).

-/


namespace Nat

open Finset

/-- A variant of the traditional prime counting function which gives the number of primes
*strictly* less than the input. More convenient for avoiding off-by-one errors.
-/
def primeCounting' : ℕ → ℕ :=
  Nat.count Prime

/-- The prime counting function: Returns the number of primes less than or equal to the input. -/
def primeCounting (n : ℕ) : ℕ :=
  primeCounting' (n + 1)

-- mathport name: «exprπ»
localized [Nat] notation "π" => Nat.primeCounting

-- mathport name: «exprπ'»
localized [Nat] notation "π'" => Nat.primeCounting'

theorem monotone_prime_counting' : Monotone primeCounting' :=
  count_monotone Prime

theorem monotone_prime_counting : Monotone primeCounting := fun a b a_le_b =>
  monotone_prime_counting' (add_le_add_right a_le_b 1)

@[simp]
theorem prime_counting'_nth_eq (n : ℕ) : π' (nth Prime n) = n :=
  count_nth_of_infinite _ infinite_set_of_prime _

@[simp]
theorem prime_nth_prime (n : ℕ) : Prime (nth Prime n) :=
  nth_mem_of_infinite _ infinite_set_of_prime _

/-- A linear upper bound on the size of the `prime_counting'` function -/
theorem prime_counting'_add_le {a k : ℕ} (h0 : 0 < a) (h1 : a < k) (n : ℕ) :
    π' (k + n) ≤ π' k + Nat.totient a * (n / a + 1) :=
  calc
    π' (k + n) ≤ ((range k).filter Prime).card + ((ico k (k + n)).filter Prime).card := by
      rw [prime_counting', count_eq_card_filter_range, range_eq_Ico, ← Ico_union_Ico_eq_Ico (zero_le k) le_self_add,
        filter_union]
      apply card_union_le
    _ ≤ π' k + ((ico k (k + n)).filter Prime).card := by
      rw [prime_counting', count_eq_card_filter_range]
    _ ≤ π' k + ((ico k (k + n)).filter (Coprime a)).card := by
      refine' add_le_add_left (card_le_of_subset _) k.prime_counting'
      simp only [← subset_iff, ← and_imp, ← mem_filter, ← mem_Ico]
      intro p succ_k_le_p p_lt_n p_prime
      constructor
      · exact ⟨succ_k_le_p, p_lt_n⟩
        
      · rw [coprime_comm]
        exact coprime_of_lt_prime h0 (gt_of_ge_of_gtₓ succ_k_le_p h1) p_prime
        
    _ ≤ π' k + totient a * (n / a + 1) := by
      rw [add_le_add_iff_left]
      exact Ico_filter_coprime_le k n h0
    

end Nat

