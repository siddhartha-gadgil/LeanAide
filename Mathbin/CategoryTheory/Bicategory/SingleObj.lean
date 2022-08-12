/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.CategoryTheory.Bicategory.End
import Mathbin.CategoryTheory.Monoidal.Functorial

/-!
# Promoting a monoidal category to a single object bicategory.

A monoidal category can be thought of as a bicategory with a single object.

The objects of the monoidal category become the 1-morphisms,
with composition given by tensor product,
and the morphisms of the monoidal category become the 2-morphisms.

We verify that the endomorphisms of that single object recovers the original monoidal category.

One could go much further: the bicategory of monoidal categories
(equipped with monoidal functors and monoidal natural transformations)
is equivalent to the bicategory consisting of
* single object bicategories,
* pseudofunctors, and
* (oplax) natural transformations `η` such that `η.app punit.star = 𝟙 _`.
-/


namespace CategoryTheory

variable (C : Type _) [Category C] [MonoidalCategory C]

/-- Promote a monoidal category to a bicategory with a single object.
(The objects of the monoidal category become the 1-morphisms,
with composition given by tensor product,
and the morphisms of the monoidal category become the 2-morphisms.)
-/
@[nolint unused_arguments]
def MonoidalSingleObj (C : Type _) [Category C] [MonoidalCategory C] :=
  PUnit deriving Inhabited

open MonoidalCategory

instance : Bicategory (MonoidalSingleObj C) where
  Hom := fun _ _ => C
  id := fun _ => 𝟙_ C
  comp := fun _ _ _ X Y => X ⊗ Y
  whiskerLeft := fun _ _ _ X Y Z f => 𝟙 X ⊗ f
  whiskerRight := fun _ _ _ X Y f Z => f ⊗ 𝟙 Z
  associator := fun _ _ _ _ X Y Z => α_ X Y Z
  leftUnitor := fun _ _ X => λ_ X
  rightUnitor := fun _ _ X => ρ_ X
  comp_whisker_left' := by
    intros
    rw [associator_inv_naturality, iso.hom_inv_id_assoc, tensor_id]
  whisker_assoc' := by
    intros
    rw [associator_inv_naturality, iso.hom_inv_id_assoc]
  whisker_right_comp' := by
    intros
    rw [← tensor_id, associator_naturality, iso.inv_hom_id_assoc]
  id_whisker_left' := by
    intros
    rw [left_unitor_inv_naturality, iso.hom_inv_id_assoc]
  whisker_right_id' := by
    intros
    rw [right_unitor_inv_naturality, iso.hom_inv_id_assoc]
  pentagon' := by
    intros
    rw [pentagon]

namespace MonoidalSingleObj

/-- The unique object in the bicategory obtained by "promoting" a monoidal category. -/
@[nolint unused_arguments]
protected def star : MonoidalSingleObj C :=
  PUnit.unit

/-- The monoidal functor from the endomorphisms of the single object
when we promote a monoidal category to a single object bicategory,
to the original monoidal category.

We subsequently show this is an equivalence.
-/
@[simps]
def endMonoidalStarFunctor : MonoidalFunctor (EndMonoidal (MonoidalSingleObj.star C)) C where
  obj := fun X => X
  map := fun X Y f => f
  ε := 𝟙 _
  μ := fun X Y => 𝟙 _
  μ_natural' := fun X Y X' Y' f g => by
    dsimp'
    simp only [← category.id_comp, ← category.comp_id]
    -- Should we provide further simp lemmas so this goal becomes visible?
    exact (tensor_id_comp_id_tensor _ _).symm

noncomputable section

/-- The equivalence between the endomorphisms of the single object
when we promote a monoidal category to a single object bicategory,
and the original monoidal category.
-/
def endMonoidalStarFunctorIsEquivalence : IsEquivalence (endMonoidalStarFunctor C).toFunctor where
  inverse := { obj := fun X => X, map := fun X Y f => f }
  unitIso :=
    NatIso.ofComponents (fun X => asIso (𝟙 _))
      (by
        tidy)
  counitIso :=
    NatIso.ofComponents (fun X => asIso (𝟙 _))
      (by
        tidy)

end MonoidalSingleObj

end CategoryTheory

