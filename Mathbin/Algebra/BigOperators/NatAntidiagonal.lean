/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathbin.Data.Finset.NatAntidiagonal
import Mathbin.Algebra.BigOperators.Basic

/-!
# Big operators for `nat_antidiagonal`

This file contains theorems relevant to big operators over `finset.nat.antidiagonal`.
-/


open BigOperators

variable {M N : Type _} [CommMonoidₓ M] [AddCommMonoidₓ N]

namespace Finset

namespace Nat

theorem prod_antidiagonal_succ {n : ℕ} {f : ℕ × ℕ → M} :
    (∏ p in antidiagonal (n + 1), f p) = f (0, n + 1) * ∏ p in antidiagonal n, f (p.1 + 1, p.2) := by
  rw [antidiagonal_succ, prod_cons, prod_map]
  rfl

theorem sum_antidiagonal_succ {n : ℕ} {f : ℕ × ℕ → N} :
    (∑ p in antidiagonal (n + 1), f p) = f (0, n + 1) + ∑ p in antidiagonal n, f (p.1 + 1, p.2) :=
  @prod_antidiagonal_succ (Multiplicative N) _ _ _

@[to_additive]
theorem prod_antidiagonal_swap {n : ℕ} {f : ℕ × ℕ → M} :
    (∏ p in antidiagonal n, f p.swap) = ∏ p in antidiagonal n, f p := by
  nth_rw 1[← map_swap_antidiagonal]
  rw [prod_map]
  rfl

theorem prod_antidiagonal_succ' {n : ℕ} {f : ℕ × ℕ → M} :
    (∏ p in antidiagonal (n + 1), f p) = f (n + 1, 0) * ∏ p in antidiagonal n, f (p.1, p.2 + 1) := by
  rw [← prod_antidiagonal_swap, prod_antidiagonal_succ, ← prod_antidiagonal_swap]
  rfl

theorem sum_antidiagonal_succ' {n : ℕ} {f : ℕ × ℕ → N} :
    (∑ p in antidiagonal (n + 1), f p) = f (n + 1, 0) + ∑ p in antidiagonal n, f (p.1, p.2 + 1) :=
  @prod_antidiagonal_succ' (Multiplicative N) _ _ _

@[to_additive]
theorem prod_antidiagonal_subst {n : ℕ} {f : ℕ × ℕ → ℕ → M} :
    (∏ p in antidiagonal n, f p n) = ∏ p in antidiagonal n, f p (p.1 + p.2) :=
  (prod_congr rfl) fun p hp => by
    rw [nat.mem_antidiagonal.1 hp]

@[to_additive]
theorem prod_antidiagonal_eq_prod_range_succ_mk {M : Type _} [CommMonoidₓ M] (f : ℕ × ℕ → M) (n : ℕ) :
    (∏ ij in Finset.Nat.antidiagonal n, f ij) = ∏ k in range n.succ, f (k, n - k) := by
  convert prod_map _ ⟨fun i => (i, n - i), fun x y h => (Prod.mk.inj h).1⟩ _
  rfl

/-- This lemma matches more generally than `finset.nat.prod_antidiagonal_eq_prod_range_succ_mk` when
using `rw ←`. -/
@[to_additive
      "This lemma matches more generally than\n`finset.nat.sum_antidiagonal_eq_sum_range_succ_mk` when using `rw ←`."]
theorem prod_antidiagonal_eq_prod_range_succ {M : Type _} [CommMonoidₓ M] (f : ℕ → ℕ → M) (n : ℕ) :
    (∏ ij in Finset.Nat.antidiagonal n, f ij.1 ij.2) = ∏ k in range n.succ, f k (n - k) :=
  prod_antidiagonal_eq_prod_range_succ_mk _ _

end Nat

end Finset

