/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathbin.Algebra.BigOperators.Basic
import Mathbin.Data.Finset.Option

/-!
# Lemmas about products and sums over finite sets in `option α`

In this file we prove formulas for products and sums over `finset.insert_none s` and
`finset.erase_none s`.
-/


open BigOperators

open Function

namespace Finset

variable {α M : Type _} [CommMonoidₓ M]

@[simp, to_additive]
theorem prod_insert_none (f : Option α → M) (s : Finset α) :
    (∏ x in s.insertNone, f x) = f none * ∏ x in s, f (some x) := by
  simp [← insert_none]

@[to_additive]
theorem prod_erase_none (f : α → M) (s : Finset (Option α)) :
    (∏ x in s.eraseNone, f x) = ∏ x in s, Option.elimₓ 1 f x := by
  classical <;>
    calc (∏ x in s.erase_none, f x) = ∏ x in s.erase_none.map embedding.some, Option.elimₓ 1 f x :=
        (prod_map s.erase_none embedding.some <| Option.elimₓ 1 f).symm _ = ∏ x in s.erase none, Option.elimₓ 1 f x :=
        by
        rw [map_some_erase_none]_ = ∏ x in s, Option.elimₓ 1 f x := prod_erase _ rfl

end Finset

