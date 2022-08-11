/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.CategoryTheory.Preadditive.Default
import Mathbin.CategoryTheory.SingleObj

/-!
# `single_obj α` is preadditive when `α` is a ring.

-/


namespace CategoryTheory

variable {α : Type _} [Ringₓ α]

instance : Preadditive (SingleObj α) where
  add_comp' := fun _ _ _ f f' g => mul_addₓ g f f'
  comp_add' := fun _ _ _ f g g' => add_mulₓ g g' f

-- TODO define `PreAddCat` (with additive functors as morphisms), and `Ring ⥤ PreAddCat`.
end CategoryTheory

