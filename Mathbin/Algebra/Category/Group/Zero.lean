/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.Algebra.Category.Group.Basic
import Mathbin.CategoryTheory.Limits.Shapes.ZeroMorphisms

/-!
# The category of (commutative) (additive) groups has a zero object.

`AddCommGroup` also has zero morphisms. For definitional reasons, we infer this from preadditivity
rather than from the existence of a zero object.
-/


open CategoryTheory

open CategoryTheory.Limits

universe u

namespace Groupₓₓ

@[to_additive]
theorem is_zero_of_subsingleton (G : Groupₓₓ) [Subsingleton G] : IsZero G := by
  refine' ⟨fun X => ⟨⟨⟨1⟩, fun f => _⟩⟩, fun X => ⟨⟨⟨1⟩, fun f => _⟩⟩⟩
  · ext
    have : x = 1 := Subsingleton.elimₓ _ _
    rw [this, map_one, map_one]
    
  · ext
    apply Subsingleton.elimₓ
    

@[to_additive AddGroupₓₓ.has_zero_object]
instance : HasZeroObject Groupₓₓ :=
  ⟨⟨of PUnit, is_zero_of_subsingleton _⟩⟩

end Groupₓₓ

namespace CommGroupₓₓ

@[to_additive]
theorem is_zero_of_subsingleton (G : CommGroupₓₓ) [Subsingleton G] : IsZero G := by
  refine' ⟨fun X => ⟨⟨⟨1⟩, fun f => _⟩⟩, fun X => ⟨⟨⟨1⟩, fun f => _⟩⟩⟩
  · ext
    have : x = 1 := Subsingleton.elimₓ _ _
    rw [this, map_one, map_one]
    
  · ext
    apply Subsingleton.elimₓ
    

@[to_additive AddCommGroupₓₓ.has_zero_object]
instance : HasZeroObject CommGroupₓₓ :=
  ⟨⟨of PUnit, is_zero_of_subsingleton _⟩⟩

end CommGroupₓₓ

