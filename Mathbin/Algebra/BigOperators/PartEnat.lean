/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import Mathbin.Algebra.BigOperators.Basic
import Mathbin.Data.Nat.PartEnat

/-!
# Big operators in `part_enat`

A simple lemma about sums in `part_enat`.
-/


open BigOperators

variable {α : Type _}

namespace Finset

theorem sum_nat_coe_enat (s : Finset α) (f : α → ℕ) : (∑ x in s, (f x : PartEnat)) = (∑ x in s, f x : ℕ) :=
  (PartEnat.coeHom.map_sum _ _).symm

end Finset

