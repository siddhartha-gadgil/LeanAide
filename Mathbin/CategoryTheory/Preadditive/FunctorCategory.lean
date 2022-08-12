/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathbin.CategoryTheory.Preadditive.Default

/-!
# Preadditive structure on functor categories

If `C` and `D` are categories and `D` is preadditive,
then `C ⥤ D` is also preadditive.

-/


open BigOperators

namespace CategoryTheory

open CategoryTheory.Limits Preadditive

variable {C D : Type _} [Category C] [Category D] [Preadditive D]

instance functorCategoryPreadditive : Preadditive (C ⥤ D) where
  homGroup := fun F G =>
    { add := fun α β =>
        { app := fun X => α.app X + β.app X,
          naturality' := by
            intros
            rw [comp_add, add_comp, α.naturality, β.naturality] },
      zero :=
        { app := fun X => 0,
          naturality' := by
            intros
            rw [zero_comp, comp_zero] },
      neg := fun α =>
        { app := fun X => -α.app X,
          naturality' := by
            intros
            rw [comp_neg, neg_comp, α.naturality] },
      sub := fun α β =>
        { app := fun X => α.app X - β.app X,
          naturality' := by
            intros
            rw [comp_sub, sub_comp, α.naturality, β.naturality] },
      add_assoc := by
        intros
        ext
        apply add_assocₓ,
      zero_add := by
        intros
        ext
        apply zero_addₓ,
      add_zero := by
        intros
        ext
        apply add_zeroₓ,
      sub_eq_add_neg := by
        intros
        ext
        apply sub_eq_add_neg,
      add_left_neg := by
        intros
        ext
        apply add_left_negₓ,
      add_comm := by
        intros
        ext
        apply add_commₓ }
  add_comp' := by
    intros
    ext
    apply add_comp
  comp_add' := by
    intros
    ext
    apply comp_add

namespace NatTrans

variable {F G : C ⥤ D}

/-- Application of a natural transformation at a fixed object,
as group homomorphism -/
@[simps]
def appHom (X : C) : (F ⟶ G) →+ (F.obj X ⟶ G.obj X) where
  toFun := fun α => α.app X
  map_zero' := rfl
  map_add' := fun _ _ => rfl

@[simp]
theorem app_zero (X : C) : (0 : F ⟶ G).app X = 0 :=
  rfl

@[simp]
theorem app_add (X : C) (α β : F ⟶ G) : (α + β).app X = α.app X + β.app X :=
  rfl

@[simp]
theorem app_sub (X : C) (α β : F ⟶ G) : (α - β).app X = α.app X - β.app X :=
  rfl

@[simp]
theorem app_neg (X : C) (α : F ⟶ G) : (-α).app X = -α.app X :=
  rfl

@[simp]
theorem app_nsmul (X : C) (α : F ⟶ G) (n : ℕ) : (n • α).app X = n • α.app X :=
  (appHom X).map_nsmul α n

@[simp]
theorem app_zsmul (X : C) (α : F ⟶ G) (n : ℤ) : (n • α).app X = n • α.app X :=
  (appHom X : (F ⟶ G) →+ (F.obj X ⟶ G.obj X)).map_zsmul α n

@[simp]
theorem app_sum {ι : Type _} (s : Finset ι) (X : C) (α : ι → (F ⟶ G)) : (∑ i in s, α i).app X = ∑ i in s, (α i).app X :=
  by
  rw [← app_hom_apply, AddMonoidHom.map_sum]
  rfl

end NatTrans

end CategoryTheory

