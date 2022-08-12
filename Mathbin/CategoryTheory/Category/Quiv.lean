/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.CategoryTheory.Adjunction.Basic
import Mathbin.CategoryTheory.Category.Cat
import Mathbin.CategoryTheory.PathCategory

/-!
# The category of quivers

The category of (bundled) quivers, and the free/forgetful adjunction between `Cat` and `Quiv`.

-/


universe v u

namespace CategoryTheory

/-- Category of quivers. -/
-- intended to be used with explicit universe parameters
@[nolint check_univs]
def Quiv :=
  Bundled Quiver.{v + 1, u}

namespace Quiv

instance : CoeSort Quiv (Type u) where coe := Bundled.α

instance str (C : Quiv.{v, u}) : Quiver.{v + 1, u} C :=
  C.str

/-- Construct a bundled `Quiv` from the underlying type and the typeclass. -/
def of (C : Type u) [Quiver.{v + 1} C] : Quiv.{v, u} :=
  Bundled.of C

instance : Inhabited Quiv :=
  ⟨Quiv.of (Quiver.Empty Pempty)⟩

/-- Category structure on `Quiv` -/
instance category : LargeCategory.{max v u} Quiv.{v, u} where
  Hom := fun C D => Prefunctor C D
  id := fun C => Prefunctor.id C
  comp := fun C D E F G => Prefunctor.comp F G
  id_comp' := fun C D F => by
    cases F <;> rfl
  comp_id' := fun C D F => by
    cases F <;> rfl
  assoc' := by
    intros <;> rfl

/-- The forgetful functor from categories to quivers. -/
@[simps]
def forget : Cat.{v, u} ⥤ Quiv.{v, u} where
  obj := fun C => Quiv.of C
  map := fun C D F => F.toPrefunctor

end Quiv

namespace Cat

/-- The functor sending each quiver to its path category. -/
@[simps]
def free : Quiv.{v, u} ⥤ Cat.{max u v, u} where
  obj := fun V => Cat.of (Paths V)
  map := fun V W F =>
    { obj := fun X => F.obj X, map := fun X Y f => F.mapPath f, map_comp' := fun X Y Z f g => F.map_path_comp f g }
  map_id' := fun V => by
    change (show paths V ⥤ _ from _) = _
    ext
    apply eq_conj_eq_to_hom
    rfl
  map_comp' := fun U V W F G => by
    change (show paths U ⥤ _ from _) = _
    ext
    apply eq_conj_eq_to_hom
    rfl

end Cat

namespace Quiv

/-- Any prefunctor into a category lifts to a functor from the path category. -/
@[simps]
def lift {V : Type u} [Quiver.{v + 1} V] {C : Type u} [Category.{v} C] (F : Prefunctor V C) : Paths V ⥤ C where
  obj := fun X => F.obj X
  map := fun X Y f => composePathₓ (F.mapPath f)

/-- The adjunction between forming the free category on a quiver, and forgetting a category to a quiver.
-/
-- We might construct `of_lift_iso_self : paths.of ⋙ lift F ≅ F`
-- (and then show that `lift F` is initial amongst such functors)
-- but it would require lifting quite a bit of machinery to quivers!
def adj : Cat.free ⊣ Quiv.forget :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun V C =>
        { toFun := fun F => Paths.of.comp F.toPrefunctor, invFun := fun F => lift F,
          left_inv := fun F => by
            ext
            · erw [(eq_conj_eq_to_hom _).symm]
              apply category.id_comp
              
            rfl,
          right_inv := by
            rintro ⟨obj, map⟩
            dsimp' only [← Prefunctor.comp]
            congr
            ext X Y f
            exact category.id_comp _ },
      hom_equiv_naturality_left_symm' := fun V W C f g => by
        change (show paths V ⥤ _ from _) = _
        ext
        apply eq_conj_eq_to_hom
        rfl }

end Quiv

end CategoryTheory

