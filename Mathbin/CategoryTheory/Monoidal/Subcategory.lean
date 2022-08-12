/-
Copyright (c) 2022 Antoine Labelle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Labelle
-/
import Mathbin.CategoryTheory.Monoidal.Braided
import Mathbin.CategoryTheory.ConcreteCategory.Basic

/-!
# Full monoidal subcategories

Given a monidal category `C` and a monoidal predicate on `C`, that is a function `P : C → Prop`
closed under `𝟙_` and `⊗`, we can put a monoidal structure on `{X : C // P X}` (the category
structure is defined in `category_theory.full_subcategory`).

When `C` is also braided/symmetric, the full monoidal subcategory also inherits the
braided/symmetric structure.

## TODO
* Add monoidal/braided versions of `category_theory.full_subcategory.lift`
-/


universe u v

namespace CategoryTheory

namespace MonoidalCategory

open Iso

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] (P : C → Prop)

/-- A property `C → Prop` is a monoidal predicate if it is closed under `𝟙_` and `⊗`.
-/
class MonoidalPredicate where
  prop_id' : P (𝟙_ C) := by
    run_tac
      obviously
  prop_tensor' : ∀ {X Y}, P X → P Y → P (X ⊗ Y) := by
    run_tac
      obviously

restate_axiom monoidal_predicate.prop_id'

restate_axiom monoidal_predicate.prop_tensor'

open MonoidalPredicate

variable [MonoidalPredicate P]

/-- When `P` is a monoidal predicate, the full subcategory `{X : C // P X}` inherits the monoidal
structure of `C`
-/
instance fullMonoidalSubcategory : MonoidalCategory { X : C // P X } where
  tensorObj := fun X Y => ⟨X ⊗ Y, prop_tensor X.2 Y.2⟩
  tensorHom := fun X₁ Y₁ X₂ Y₂ f g => by
    change X₁.1 ⊗ X₂.1 ⟶ Y₁.1 ⊗ Y₂.1
    change X₁.1 ⟶ Y₁.1 at f
    change X₂.1 ⟶ Y₂.1 at g
    exact f ⊗ g
  tensorUnit := ⟨𝟙_ C, prop_id⟩
  associator := fun X Y Z =>
    ⟨(α_ X.1 Y.1 Z.1).Hom, (α_ X.1 Y.1 Z.1).inv, hom_inv_id (α_ X.1 Y.1 Z.1), inv_hom_id (α_ X.1 Y.1 Z.1)⟩
  leftUnitor := fun X => ⟨(λ_ X.1).Hom, (λ_ X.1).inv, hom_inv_id (λ_ X.1), inv_hom_id (λ_ X.1)⟩
  rightUnitor := fun X => ⟨(ρ_ X.1).Hom, (ρ_ X.1).inv, hom_inv_id (ρ_ X.1), inv_hom_id (ρ_ X.1)⟩
  tensor_id' := fun X Y => tensor_id X.1 Y.1
  tensor_comp' := fun X₁ Y₁ Z₁ X₂ Y₂ Z₂ f₁ f₂ g₁ g₂ => tensor_comp f₁ f₂ g₁ g₂
  associator_naturality' := fun X₁ X₂ X₃ Y₁ Y₂ Y₃ f₁ f₂ f₃ => associator_naturality f₁ f₂ f₃
  left_unitor_naturality' := fun X Y f => left_unitor_naturality f
  right_unitor_naturality' := fun X Y f => right_unitor_naturality f
  pentagon' := fun W X Y Z => pentagon W.1 X.1 Y.1 Z.1
  triangle' := fun X Y => triangle X.1 Y.1

/-- The forgetful monoidal functor from a full monoidal subcategory into the original category
("forgetting" the condition).
-/
@[simps]
def fullMonoidalSubcategoryInclusion : MonoidalFunctor { X : C // P X } C where
  toFunctor := fullSubcategoryInclusion P
  ε := 𝟙 _
  μ := fun X Y => 𝟙 _

instance fullMonoidalSubcategory.full : Full (fullMonoidalSubcategoryInclusion P).toFunctor :=
  fullSubcategory.full P

instance fullMonoidalSubcategory.faithful : Faithful (fullMonoidalSubcategoryInclusion P).toFunctor :=
  fullSubcategory.faithful P

variable {P} {P' : C → Prop} [MonoidalPredicate P']

/-- An implication of predicates `P → P'` induces a monoidal functor between full monoidal
subcategories. -/
@[simps]
def fullMonoidalSubcategory.map (h : ∀ ⦃X⦄, P X → P' X) : MonoidalFunctor { X : C // P X } { X : C // P' X } where
  toFunctor := fullSubcategory.map h
  ε := 𝟙 _
  μ := fun X Y => 𝟙 _

instance fullMonoidalSubcategory.mapFull (h : ∀ ⦃X⦄, P X → P' X) :
    Full (fullMonoidalSubcategory.map h).toFunctor where preimage := fun X Y f => f

instance fullMonoidalSubcategory.map_faithful (h : ∀ ⦃X⦄, P X → P' X) :
    Faithful (fullMonoidalSubcategory.map h).toFunctor where

section Braided

variable (P) [BraidedCategory C]

/-- The braided structure on `{X : C // P X}` inherited by the braided structure on `C`.
-/
instance fullBraidedSubcategory : BraidedCategory { X : C // P X } :=
  braidedCategoryOfFaithful (fullMonoidalSubcategoryInclusion P)
    (fun X Y => ⟨(β_ X.1 Y.1).Hom, (β_ X.1 Y.1).inv, (β_ X.1 Y.1).hom_inv_id, (β_ X.1 Y.1).inv_hom_id⟩) fun X Y => by
    tidy

/-- The forgetful braided functor from a full braided subcategory into the original category
("forgetting" the condition).
-/
@[simps]
def fullBraidedSubcategoryInclusion : BraidedFunctor { X : C // P X } C where
  toMonoidalFunctor := fullMonoidalSubcategoryInclusion P
  braided' := fun X Y => by
    rw [is_iso.eq_inv_comp]
    tidy

instance fullBraidedSubcategory.full : Full (fullBraidedSubcategoryInclusion P).toFunctor :=
  fullMonoidalSubcategory.full P

instance fullBraidedSubcategory.faithful : Faithful (fullBraidedSubcategoryInclusion P).toFunctor :=
  fullMonoidalSubcategory.faithful P

variable {P}

/-- An implication of predicates `P → P'` induces a braided functor between full braided
subcategories. -/
@[simps]
def fullBraidedSubcategory.map (h : ∀ ⦃X⦄, P X → P' X) : BraidedFunctor { X : C // P X } { X : C // P' X } where
  toMonoidalFunctor := fullMonoidalSubcategory.map h
  braided' := fun X Y => by
    rw [is_iso.eq_inv_comp]
    tidy

instance fullBraidedSubcategory.mapFull (h : ∀ ⦃X⦄, P X → P' X) : Full (fullBraidedSubcategory.map h).toFunctor :=
  fullMonoidalSubcategory.mapFull h

instance fullBraidedSubcategory.map_faithful (h : ∀ ⦃X⦄, P X → P' X) :
    Faithful (fullBraidedSubcategory.map h).toFunctor :=
  fullMonoidalSubcategory.map_faithful h

end Braided

section Symmetric

variable (P) [SymmetricCategory C]

instance fullSymmetricSubcategory : SymmetricCategory { X : C // P X } :=
  symmetricCategoryOfFaithful (fullBraidedSubcategoryInclusion P)

end Symmetric

end MonoidalCategory

end CategoryTheory

