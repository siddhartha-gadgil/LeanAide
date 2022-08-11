/-
Copyright (c) 2021 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import Mathbin.Data.Bool.Basic
import Mathbin.Data.Set.Basic

/-!
# Booleans and set operations

This file contains two trivial lemmas about `bool`, `set.univ`, and `set.range`.
-/


open Set

namespace Bool

@[simp]
theorem univ_eq : (Univ : Set Bool) = {false, true} :=
  (eq_univ_of_forall Bool.dichotomy).symm

@[simp]
theorem range_eq {α : Type _} (f : Bool → α) : Range f = {f false, f true} := by
  rw [← image_univ, univ_eq, image_pair]

end Bool

