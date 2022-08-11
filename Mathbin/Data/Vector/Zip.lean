/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.Data.Vector.Basic
import Mathbin.Data.List.Zip

/-!
# The `zip_with` operation on vectors.
-/


namespace Vector

section ZipWith

variable {α β γ : Type _} {n : ℕ} (f : α → β → γ)

/-- Apply the function `f : α → β → γ` to each corresponding pair of elements from two vectors. -/
def zipWith : Vector α n → Vector β n → Vector γ n := fun x y =>
  ⟨List.zipWithₓ f x.1 y.1, by
    simp ⟩

@[simp]
theorem zip_with_to_list (x : Vector α n) (y : Vector β n) :
    (Vector.zipWith f x y).toList = List.zipWithₓ f x.toList y.toList :=
  rfl

@[simp]
theorem zip_with_nth (x : Vector α n) (y : Vector β n) (i) : (Vector.zipWith f x y).nth i = f (x.nth i) (y.nth i) := by
  dsimp' only [← Vector.zipWith, ← Vector.nth]
  cases x
  cases y
  simp only [← List.nth_le_zip_with, ← Subtype.coe_mk]
  congr

@[simp]
theorem zip_with_tail (x : Vector α n) (y : Vector β n) :
    (Vector.zipWith f x y).tail = Vector.zipWith f x.tail y.tail := by
  ext
  simp [← nth_tail]

@[to_additive]
theorem prod_mul_prod_eq_prod_zip_with [CommMonoidₓ α] (x y : Vector α n) :
    x.toList.Prod * y.toList.Prod = (Vector.zipWith (· * ·) x y).toList.Prod :=
  List.prod_mul_prod_eq_prod_zip_with_of_length_eq x.toList y.toList ((to_list_length x).trans (to_list_length y).symm)

end ZipWith

end Vector

