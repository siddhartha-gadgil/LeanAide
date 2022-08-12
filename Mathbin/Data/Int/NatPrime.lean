/-
Copyright (c) 2020 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Lacker, Bryan Gin-ge Chen
-/
import Mathbin.Data.Nat.Prime
import Mathbin.Data.Int.Basic

/-!
# Lemmas about nat.prime using `int`s
-/


open Nat

namespace Int

theorem not_prime_of_int_mul {a b : ℤ} {c : ℕ} (ha : 1 < a.natAbs) (hb : 1 < b.natAbs) (hc : a * b = (c : ℤ)) :
    ¬Nat.Prime c :=
  not_prime_mul' (nat_abs_mul_nat_abs_eq hc) ha hb

end Int

