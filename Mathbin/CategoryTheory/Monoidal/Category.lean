/-
Copyright (c) 2018 Michael Jendrusch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jendrusch, Scott Morrison, Bhavik Mehta, Jakob von Raumer
-/
import Mathbin.CategoryTheory.Products.Basic

/-!
# Monoidal categories

A monoidal category is a category equipped with a tensor product, unitors, and an associator.
In the definition, we provide the tensor product as a pair of functions
* `tensor_obj : C → C → C`
* `tensor_hom : (X₁ ⟶ Y₁) → (X₂ ⟶ Y₂) → ((X₁ ⊗ X₂) ⟶ (Y₁ ⊗ Y₂))`
and allow use of the overloaded notation `⊗` for both.
The unitors and associator are provided componentwise.

The tensor product can be expressed as a functor via `tensor : C × C ⥤ C`.
The unitors and associator are gathered together as natural
isomorphisms in `left_unitor_nat_iso`, `right_unitor_nat_iso` and `associator_nat_iso`.

Some consequences of the definition are proved in other files,
e.g. `(λ_ (𝟙_ C)).hom = (ρ_ (𝟙_ C)).hom` in `category_theory.monoidal.unitors_equal`.

## Implementation
Dealing with unitors and associators is painful, and at this stage we do not have a useful
implementation of coherence for monoidal categories.

In an effort to lessen the pain, we put some effort into choosing the right `simp` lemmas.
Generally, the rule is that the component index of a natural transformation "weighs more"
in considering the complexity of an expression than does a structural isomorphism (associator, etc).

As an example when we prove Proposition 2.2.4 of
<http://www-math.mit.edu/~etingof/egnobookfinal.pdf>
we state it as a `@[simp]` lemma as
```
(λ_ (X ⊗ Y)).hom = (α_ (𝟙_ C) X Y).inv ≫ (λ_ X).hom ⊗ (𝟙 Y)
```

This is far from completely effective, but seems to prove a useful principle.

## References
* Tensor categories, Etingof, Gelaki, Nikshych, Ostrik,
  http://www-math.mit.edu/~etingof/egnobookfinal.pdf
* <https://stacks.math.columbia.edu/tag/0FFK>.
-/


open CategoryTheory

universe v u

open CategoryTheory

open CategoryTheory.Category

open CategoryTheory.Iso

namespace CategoryTheory

-- ./././Mathport/Syntax/Translate/Basic.lean:1453:24: unsupported: (notation) in structure
-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `«expr ⊗ »
-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `«expr ⊗ »
-- ./././Mathport/Syntax/Translate/Basic.lean:1453:24: unsupported: (notation) in structure
-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `«expr ⊗' »
-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `«expr ⊗ »
-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `«expr ⊗' »
-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `«expr ⊗' »
-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `«expr ⊗' »
-- ./././Mathport/Syntax/Translate/Basic.lean:1440:30: infer kinds are unsupported in Lean 4: #[`tensorUnit] []
-- ./././Mathport/Syntax/Translate/Basic.lean:1453:24: unsupported: (notation) in structure
-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `«expr ⊗ »
-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `«expr ⊗ »
-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `«expr ⊗ »
-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `«expr ⊗ »
-- ./././Mathport/Syntax/Translate/Basic.lean:1453:24: unsupported: (notation) in structure
-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `«expr ⊗' »
-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `«expr ⊗' »
-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `exprα_
-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `exprα_
-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `«expr ⊗' »
-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `«expr ⊗' »
-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `«expr ⊗ »
-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `«expr𝟙_»
-- ./././Mathport/Syntax/Translate/Basic.lean:1453:24: unsupported: (notation) in structure
-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `«expr ⊗' »
-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `«expr𝟙_»
-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `«exprλ_»
-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `«exprλ_»
-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `«expr ⊗ »
-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `«expr𝟙_»
-- ./././Mathport/Syntax/Translate/Basic.lean:1453:24: unsupported: (notation) in structure
-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `«expr ⊗' »
-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `«expr𝟙_»
-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `exprρ_
-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `exprρ_
-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `«expr ⊗' »
-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `exprα_
-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `exprα_
-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `«expr ⊗ »
-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `«expr ⊗' »
-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `exprα_
-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `exprα_
-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `«expr ⊗ »
-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `exprα_
-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `«expr ⊗ »
-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `exprα_
-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `«expr𝟙_»
-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `«expr ⊗' »
-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `«exprλ_»
-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `«expr ⊗' »
-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `exprρ_
/-- In a monoidal category, we can take the tensor product of objects, `X ⊗ Y` and of morphisms `f ⊗ g`.
Tensor product does not need to be strictly associative on objects, but there is a
specified associator, `α_ X Y Z : (X ⊗ Y) ⊗ Z ≅ X ⊗ (Y ⊗ Z)`. There is a tensor unit `𝟙_ C`,
with specified left and right unitor isomorphisms `λ_ X : 𝟙_ C ⊗ X ≅ X` and `ρ_ X : X ⊗ 𝟙_ C ≅ X`.
These associators and unitors satisfy the pentagon and triangle equations.

See <https://stacks.math.columbia.edu/tag/0FFK>.
-/
class MonoidalCategory (C : Type u) [𝒞 : Category.{v} C] where
  -- curried tensor product of objects:
  tensorObj : C → C → C
  -- This notation is only temporary
  -- curried tensor product of morphisms:
  tensorHom : ∀ {X₁ Y₁ X₂ Y₂ : C}, (X₁ ⟶ Y₁) → (X₂ ⟶ Y₂) → («expr ⊗ » X₁ X₂ ⟶ «expr ⊗ » Y₁ Y₂)
  -- This notation is only temporary
  -- tensor product laws:
  tensor_id' : ∀ X₁ X₂ : C, «expr ⊗' » (𝟙 X₁) (𝟙 X₂) = 𝟙 («expr ⊗ » X₁ X₂) := by
    run_tac
      obviously
  tensor_comp' :
    ∀ {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (g₁ : Y₁ ⟶ Z₁) (g₂ : Y₂ ⟶ Z₂),
      «expr ⊗' » (f₁ ≫ g₁) (f₂ ≫ g₂) = «expr ⊗' » f₁ f₂ ≫ «expr ⊗' » g₁ g₂ := by
    run_tac
      obviously
  -- tensor unit:
  tensorUnit : C
  -- associator:
  associator : ∀ X Y Z : C, «expr ⊗ » («expr ⊗ » X Y) Z ≅ «expr ⊗ » X («expr ⊗ » Y Z)
  associator_naturality' :
    ∀ {X₁ X₂ X₃ Y₁ Y₂ Y₃ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃),
      «expr ⊗' » («expr ⊗' » f₁ f₂) f₃ ≫ ((exprα_) Y₁ Y₂ Y₃).Hom =
        ((exprα_) X₁ X₂ X₃).Hom ≫ «expr ⊗' » f₁ («expr ⊗' » f₂ f₃) := by
    run_tac
      obviously
  -- left unitor:
  leftUnitor : ∀ X : C, «expr ⊗ » («expr𝟙_») X ≅ X
  left_unitor_naturality' :
    ∀ {X Y : C} (f : X ⟶ Y), «expr ⊗' » (𝟙 («expr𝟙_»)) f ≫ ((«exprλ_») Y).Hom = ((«exprλ_») X).Hom ≫ f := by
    run_tac
      obviously
  -- right unitor:
  rightUnitor : ∀ X : C, «expr ⊗ » X («expr𝟙_») ≅ X
  right_unitor_naturality' :
    ∀ {X Y : C} (f : X ⟶ Y), «expr ⊗' » f (𝟙 («expr𝟙_»)) ≫ ((exprρ_) Y).Hom = ((exprρ_) X).Hom ≫ f := by
    run_tac
      obviously
  -- pentagon identity:
  pentagon' :
    ∀ W X Y Z : C,
      «expr ⊗' » ((exprα_) W X Y).Hom (𝟙 Z) ≫
          ((exprα_) W («expr ⊗ » X Y) Z).Hom ≫ «expr ⊗' » (𝟙 W) ((exprα_) X Y Z).Hom =
        ((exprα_) («expr ⊗ » W X) Y Z).Hom ≫ ((exprα_) W X («expr ⊗ » Y Z)).Hom := by
    run_tac
      obviously
  -- triangle identity:
  triangle' :
    ∀ X Y : C,
      ((exprα_) X («expr𝟙_») Y).Hom ≫ «expr ⊗' » (𝟙 X) ((«exprλ_») Y).Hom = «expr ⊗' » ((exprρ_) X).Hom (𝟙 Y) := by
    run_tac
      obviously

restate_axiom monoidal_category.tensor_id'

attribute [simp] monoidal_category.tensor_id

restate_axiom monoidal_category.tensor_comp'

attribute [reassoc] monoidal_category.tensor_comp

-- This would be redundant in the simp set.
attribute [simp] monoidal_category.tensor_comp

restate_axiom monoidal_category.associator_naturality'

attribute [reassoc] monoidal_category.associator_naturality

restate_axiom monoidal_category.left_unitor_naturality'

attribute [reassoc] monoidal_category.left_unitor_naturality

restate_axiom monoidal_category.right_unitor_naturality'

attribute [reassoc] monoidal_category.right_unitor_naturality

restate_axiom monoidal_category.pentagon'

restate_axiom monoidal_category.triangle'

attribute [reassoc] monoidal_category.pentagon

attribute [simp, reassoc] monoidal_category.triangle

open MonoidalCategory

-- mathport name: «expr ⊗ »
infixr:70 " ⊗ " => tensorObj

-- mathport name: «expr ⊗ »
infixr:70 " ⊗ " => tensorHom

-- mathport name: «expr𝟙_»
notation "𝟙_" => tensorUnit

-- mathport name: «exprα_»
notation "α_" => associator

-- mathport name: «exprλ_»
notation "λ_" => leftUnitor

-- mathport name: «exprρ_»
notation "ρ_" => rightUnitor

/-- The tensor product of two isomorphisms is an isomorphism. -/
@[simps]
def tensorIso {C : Type u} {X Y X' Y' : C} [Category.{v} C] [MonoidalCategory.{v} C] (f : X ≅ Y) (g : X' ≅ Y') :
    X ⊗ X' ≅ Y ⊗ Y' where
  Hom := f.Hom ⊗ g.Hom
  inv := f.inv ⊗ g.inv
  hom_inv_id' := by
    rw [← tensor_comp, iso.hom_inv_id, iso.hom_inv_id, ← tensor_id]
  inv_hom_id' := by
    rw [← tensor_comp, iso.inv_hom_id, iso.inv_hom_id, ← tensor_id]

-- mathport name: «expr ⊗ »
infixr:70 " ⊗ " => tensorIso

namespace MonoidalCategory

section

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C]

instance tensor_is_iso {W X Y Z : C} (f : W ⟶ X) [IsIso f] (g : Y ⟶ Z) [IsIso g] : IsIso (f ⊗ g) :=
  IsIso.of_iso (asIso f ⊗ asIso g)

@[simp]
theorem inv_tensor {W X Y Z : C} (f : W ⟶ X) [IsIso f] (g : Y ⟶ Z) [IsIso g] : inv (f ⊗ g) = inv f ⊗ inv g := by
  ext
  simp [tensor_comp]

variable {U V W X Y Z : C}

theorem tensor_dite {P : Prop} [Decidable P] {W X Y Z : C} (f : W ⟶ X) (g : P → (Y ⟶ Z)) (g' : ¬P → (Y ⟶ Z)) :
    (f ⊗ if h : P then g h else g' h) = if h : P then f ⊗ g h else f ⊗ g' h := by
  split_ifs <;> rfl

theorem dite_tensor {P : Prop} [Decidable P] {W X Y Z : C} (f : W ⟶ X) (g : P → (Y ⟶ Z)) (g' : ¬P → (Y ⟶ Z)) :
    (if h : P then g h else g' h) ⊗ f = if h : P then g h ⊗ f else g' h ⊗ f := by
  split_ifs <;> rfl

@[reassoc, simp]
theorem comp_tensor_id (f : W ⟶ X) (g : X ⟶ Y) : f ≫ g ⊗ 𝟙 Z = (f ⊗ 𝟙 Z) ≫ (g ⊗ 𝟙 Z) := by
  rw [← tensor_comp]
  simp

@[reassoc, simp]
theorem id_tensor_comp (f : W ⟶ X) (g : X ⟶ Y) : 𝟙 Z ⊗ f ≫ g = (𝟙 Z ⊗ f) ≫ (𝟙 Z ⊗ g) := by
  rw [← tensor_comp]
  simp

@[simp, reassoc]
theorem id_tensor_comp_tensor_id (f : W ⟶ X) (g : Y ⟶ Z) : (𝟙 Y ⊗ f) ≫ (g ⊗ 𝟙 X) = g ⊗ f := by
  rw [← tensor_comp]
  simp

@[simp, reassoc]
theorem tensor_id_comp_id_tensor (f : W ⟶ X) (g : Y ⟶ Z) : (g ⊗ 𝟙 W) ≫ (𝟙 Z ⊗ f) = g ⊗ f := by
  rw [← tensor_comp]
  simp

@[simp]
theorem right_unitor_conjugation {X Y : C} (f : X ⟶ Y) : f ⊗ 𝟙 (𝟙_ C) = (ρ_ X).Hom ≫ f ≫ (ρ_ Y).inv := by
  rw [← right_unitor_naturality_assoc, iso.hom_inv_id, category.comp_id]

@[simp]
theorem left_unitor_conjugation {X Y : C} (f : X ⟶ Y) : 𝟙 (𝟙_ C) ⊗ f = (λ_ X).Hom ≫ f ≫ (λ_ Y).inv := by
  rw [← left_unitor_naturality_assoc, iso.hom_inv_id, category.comp_id]

@[reassoc]
theorem left_unitor_inv_naturality {X X' : C} (f : X ⟶ X') : f ≫ (λ_ X').inv = (λ_ X).inv ≫ (𝟙 _ ⊗ f) := by
  simp

@[reassoc]
theorem right_unitor_inv_naturality {X X' : C} (f : X ⟶ X') : f ≫ (ρ_ X').inv = (ρ_ X).inv ≫ (f ⊗ 𝟙 _) := by
  simp

theorem tensor_left_iff {X Y : C} (f g : X ⟶ Y) : 𝟙 (𝟙_ C) ⊗ f = 𝟙 (𝟙_ C) ⊗ g ↔ f = g := by
  simp

theorem tensor_right_iff {X Y : C} (f g : X ⟶ Y) : f ⊗ 𝟙 (𝟙_ C) = g ⊗ 𝟙 (𝟙_ C) ↔ f = g := by
  simp

/-! The lemmas in the next section are true by coherence,
but we prove them directly as they are used in proving the coherence theorem. -/


section

@[reassoc]
theorem pentagon_inv (W X Y Z : C) :
    (𝟙 W ⊗ (α_ X Y Z).inv) ≫ (α_ W (X ⊗ Y) Z).inv ≫ ((α_ W X Y).inv ⊗ 𝟙 Z) =
      (α_ W X (Y ⊗ Z)).inv ≫ (α_ (W ⊗ X) Y Z).inv :=
  CategoryTheory.eq_of_inv_eq_inv
    (by
      simp [← pentagon])

@[reassoc, simp]
theorem right_unitor_tensor (X Y : C) : (ρ_ (X ⊗ Y)).Hom = (α_ X Y (𝟙_ C)).Hom ≫ (𝟙 X ⊗ (ρ_ Y).Hom) := by
  rw [← tensor_right_iff, comp_tensor_id, ← cancel_mono (α_ X Y (𝟙_ C)).Hom, assoc, associator_naturality, ←
    triangle_assoc, ← triangle, id_tensor_comp, pentagon_assoc, ← associator_naturality, tensor_id]

@[reassoc, simp]
theorem right_unitor_tensor_inv (X Y : C) : (ρ_ (X ⊗ Y)).inv = (𝟙 X ⊗ (ρ_ Y).inv) ≫ (α_ X Y (𝟙_ C)).inv :=
  eq_of_inv_eq_inv
    (by
      simp )

@[simp, reassoc]
theorem triangle_assoc_comp_right (X Y : C) : (α_ X (𝟙_ C) Y).inv ≫ ((ρ_ X).Hom ⊗ 𝟙 Y) = 𝟙 X ⊗ (λ_ Y).Hom := by
  rw [← triangle, iso.inv_hom_id_assoc]

@[simp, reassoc]
theorem triangle_assoc_comp_left_inv (X Y : C) : (𝟙 X ⊗ (λ_ Y).inv) ≫ (α_ X (𝟙_ C) Y).inv = (ρ_ X).inv ⊗ 𝟙 Y := by
  apply (cancel_mono ((ρ_ X).Hom ⊗ 𝟙 Y)).1
  simp only [← triangle_assoc_comp_right, ← assoc]
  rw [← id_tensor_comp, iso.inv_hom_id, ← comp_tensor_id, iso.inv_hom_id]

end

@[reassoc]
theorem associator_inv_naturality {X Y Z X' Y' Z' : C} (f : X ⟶ X') (g : Y ⟶ Y') (h : Z ⟶ Z') :
    (f ⊗ g ⊗ h) ≫ (α_ X' Y' Z').inv = (α_ X Y Z).inv ≫ ((f ⊗ g) ⊗ h) := by
  rw [comp_inv_eq, assoc, associator_naturality]
  simp

@[reassoc, simp]
theorem associator_conjugation {X X' Y Y' Z Z' : C} (f : X ⟶ X') (g : Y ⟶ Y') (h : Z ⟶ Z') :
    (f ⊗ g) ⊗ h = (α_ X Y Z).Hom ≫ (f ⊗ g ⊗ h) ≫ (α_ X' Y' Z').inv := by
  rw [associator_inv_naturality, hom_inv_id_assoc]

@[reassoc]
theorem associator_inv_conjugation {X X' Y Y' Z Z' : C} (f : X ⟶ X') (g : Y ⟶ Y') (h : Z ⟶ Z') :
    f ⊗ g ⊗ h = (α_ X Y Z).inv ≫ ((f ⊗ g) ⊗ h) ≫ (α_ X' Y' Z').Hom := by
  rw [associator_naturality, inv_hom_id_assoc]

-- TODO these next two lemmas aren't so fundamental, and perhaps could be removed
-- (replacing their usages by their proofs).
@[reassoc]
theorem id_tensor_associator_naturality {X Y Z Z' : C} (h : Z ⟶ Z') :
    (𝟙 (X ⊗ Y) ⊗ h) ≫ (α_ X Y Z').Hom = (α_ X Y Z).Hom ≫ (𝟙 X ⊗ 𝟙 Y ⊗ h) := by
  rw [← tensor_id, associator_naturality]

@[reassoc]
theorem id_tensor_associator_inv_naturality {X Y Z X' : C} (f : X ⟶ X') :
    (f ⊗ 𝟙 (Y ⊗ Z)) ≫ (α_ X' Y Z).inv = (α_ X Y Z).inv ≫ ((f ⊗ 𝟙 Y) ⊗ 𝟙 Z) := by
  rw [← tensor_id, associator_inv_naturality]

@[simp, reassoc]
theorem hom_inv_id_tensor {V W X Y Z : C} (f : V ≅ W) (g : X ⟶ Y) (h : Y ⟶ Z) :
    (f.Hom ⊗ g) ≫ (f.inv ⊗ h) = (𝟙 V ⊗ g) ≫ (𝟙 V ⊗ h) := by
  rw [← tensor_comp, f.hom_inv_id, id_tensor_comp]

@[simp, reassoc]
theorem inv_hom_id_tensor {V W X Y Z : C} (f : V ≅ W) (g : X ⟶ Y) (h : Y ⟶ Z) :
    (f.inv ⊗ g) ≫ (f.Hom ⊗ h) = (𝟙 W ⊗ g) ≫ (𝟙 W ⊗ h) := by
  rw [← tensor_comp, f.inv_hom_id, id_tensor_comp]

@[simp, reassoc]
theorem tensor_hom_inv_id {V W X Y Z : C} (f : V ≅ W) (g : X ⟶ Y) (h : Y ⟶ Z) :
    (g ⊗ f.Hom) ≫ (h ⊗ f.inv) = (g ⊗ 𝟙 V) ≫ (h ⊗ 𝟙 V) := by
  rw [← tensor_comp, f.hom_inv_id, comp_tensor_id]

@[simp, reassoc]
theorem tensor_inv_hom_id {V W X Y Z : C} (f : V ≅ W) (g : X ⟶ Y) (h : Y ⟶ Z) :
    (g ⊗ f.inv) ≫ (h ⊗ f.Hom) = (g ⊗ 𝟙 W) ≫ (h ⊗ 𝟙 W) := by
  rw [← tensor_comp, f.inv_hom_id, comp_tensor_id]

@[simp, reassoc]
theorem hom_inv_id_tensor' {V W X Y Z : C} (f : V ⟶ W) [IsIso f] (g : X ⟶ Y) (h : Y ⟶ Z) :
    (f ⊗ g) ≫ (inv f ⊗ h) = (𝟙 V ⊗ g) ≫ (𝟙 V ⊗ h) := by
  rw [← tensor_comp, is_iso.hom_inv_id, id_tensor_comp]

@[simp, reassoc]
theorem inv_hom_id_tensor' {V W X Y Z : C} (f : V ⟶ W) [IsIso f] (g : X ⟶ Y) (h : Y ⟶ Z) :
    (inv f ⊗ g) ≫ (f ⊗ h) = (𝟙 W ⊗ g) ≫ (𝟙 W ⊗ h) := by
  rw [← tensor_comp, is_iso.inv_hom_id, id_tensor_comp]

@[simp, reassoc]
theorem tensor_hom_inv_id' {V W X Y Z : C} (f : V ⟶ W) [IsIso f] (g : X ⟶ Y) (h : Y ⟶ Z) :
    (g ⊗ f) ≫ (h ⊗ inv f) = (g ⊗ 𝟙 V) ≫ (h ⊗ 𝟙 V) := by
  rw [← tensor_comp, is_iso.hom_inv_id, comp_tensor_id]

@[simp, reassoc]
theorem tensor_inv_hom_id' {V W X Y Z : C} (f : V ⟶ W) [IsIso f] (g : X ⟶ Y) (h : Y ⟶ Z) :
    (g ⊗ inv f) ≫ (h ⊗ f) = (g ⊗ 𝟙 W) ≫ (h ⊗ 𝟙 W) := by
  rw [← tensor_comp, is_iso.inv_hom_id, comp_tensor_id]

end

section

variable (C : Type u) [Category.{v} C] [MonoidalCategory.{v} C]

/-- The tensor product expressed as a functor. -/
@[simps]
def tensor : C × C ⥤ C where
  obj := fun X => X.1 ⊗ X.2
  map := fun {X Y : C × C} (f : X ⟶ Y) => f.1 ⊗ f.2

/-- The left-associated triple tensor product as a functor. -/
def leftAssocTensor : C × C × C ⥤ C where
  obj := fun X => (X.1 ⊗ X.2.1) ⊗ X.2.2
  map := fun {X Y : C × C × C} (f : X ⟶ Y) => (f.1 ⊗ f.2.1) ⊗ f.2.2

@[simp]
theorem left_assoc_tensor_obj (X) : (leftAssocTensor C).obj X = (X.1 ⊗ X.2.1) ⊗ X.2.2 :=
  rfl

@[simp]
theorem left_assoc_tensor_map {X Y} (f : X ⟶ Y) : (leftAssocTensor C).map f = (f.1 ⊗ f.2.1) ⊗ f.2.2 :=
  rfl

/-- The right-associated triple tensor product as a functor. -/
def rightAssocTensor : C × C × C ⥤ C where
  obj := fun X => X.1 ⊗ X.2.1 ⊗ X.2.2
  map := fun {X Y : C × C × C} (f : X ⟶ Y) => f.1 ⊗ f.2.1 ⊗ f.2.2

@[simp]
theorem right_assoc_tensor_obj (X) : (rightAssocTensor C).obj X = X.1 ⊗ X.2.1 ⊗ X.2.2 :=
  rfl

@[simp]
theorem right_assoc_tensor_map {X Y} (f : X ⟶ Y) : (rightAssocTensor C).map f = f.1 ⊗ f.2.1 ⊗ f.2.2 :=
  rfl

/-- The functor `λ X, 𝟙_ C ⊗ X`. -/
def tensorUnitLeft : C ⥤ C where
  obj := fun X => 𝟙_ C ⊗ X
  map := fun {X Y : C} (f : X ⟶ Y) => 𝟙 (𝟙_ C) ⊗ f

/-- The functor `λ X, X ⊗ 𝟙_ C`. -/
def tensorUnitRight : C ⥤ C where
  obj := fun X => X ⊗ 𝟙_ C
  map := fun {X Y : C} (f : X ⟶ Y) => f ⊗ 𝟙 (𝟙_ C)

/-- The associator as a natural isomorphism. -/
-- We can express the associator and the unitors, given componentwise above,
-- as natural isomorphisms.
@[simps]
def associatorNatIso : leftAssocTensor C ≅ rightAssocTensor C :=
  NatIso.ofComponents
    (by
      intros
      apply monoidal_category.associator)
    (by
      intros
      apply monoidal_category.associator_naturality)

/-- The left unitor as a natural isomorphism. -/
@[simps]
def leftUnitorNatIso : tensorUnitLeft C ≅ 𝟭 C :=
  NatIso.ofComponents
    (by
      intros
      apply monoidal_category.left_unitor)
    (by
      intros
      apply monoidal_category.left_unitor_naturality)

/-- The right unitor as a natural isomorphism. -/
@[simps]
def rightUnitorNatIso : tensorUnitRight C ≅ 𝟭 C :=
  NatIso.ofComponents
    (by
      intros
      apply monoidal_category.right_unitor)
    (by
      intros
      apply monoidal_category.right_unitor_naturality)

section

variable {C}

/-- Tensoring on the left with a fixed object, as a functor. -/
@[simps]
def tensorLeft (X : C) : C ⥤ C where
  obj := fun Y => X ⊗ Y
  map := fun Y Y' f => 𝟙 X ⊗ f

/-- Tensoring on the left with `X ⊗ Y` is naturally isomorphic to
tensoring on the left with `Y`, and then again with `X`.
-/
def tensorLeftTensor (X Y : C) : tensorLeft (X ⊗ Y) ≅ tensorLeft Y ⋙ tensorLeft X :=
  NatIso.ofComponents (associator _ _) fun Z Z' f => by
    dsimp'
    rw [← tensor_id]
    apply associator_naturality

@[simp]
theorem tensor_left_tensor_hom_app (X Y Z : C) : (tensorLeftTensor X Y).Hom.app Z = (associator X Y Z).Hom :=
  rfl

@[simp]
theorem tensor_left_tensor_inv_app (X Y Z : C) : (tensorLeftTensor X Y).inv.app Z = (associator X Y Z).inv := by
  simp [← tensor_left_tensor]

/-- Tensoring on the right with a fixed object, as a functor. -/
@[simps]
def tensorRight (X : C) : C ⥤ C where
  obj := fun Y => Y ⊗ X
  map := fun Y Y' f => f ⊗ 𝟙 X

variable (C)

/-- Tensoring on the left, as a functor from `C` into endofunctors of `C`.

TODO: show this is a op-monoidal functor.
-/
@[simps]
def tensoringLeft : C ⥤ C ⥤ C where
  obj := tensorLeft
  map := fun X Y f => { app := fun Z => f ⊗ 𝟙 Z }

instance :
    Faithful (tensoringLeft C) where map_injective' := fun X Y f g h => by
    injections with h
    replace h := congr_fun h (𝟙_ C)
    simpa using h

/-- Tensoring on the right, as a functor from `C` into endofunctors of `C`.

We later show this is a monoidal functor.
-/
@[simps]
def tensoringRight : C ⥤ C ⥤ C where
  obj := tensorRight
  map := fun X Y f => { app := fun Z => 𝟙 Z ⊗ f }

instance :
    Faithful (tensoringRight C) where map_injective' := fun X Y f g h => by
    injections with h
    replace h := congr_fun h (𝟙_ C)
    simpa using h

variable {C}

/-- Tensoring on the right with `X ⊗ Y` is naturally isomorphic to
tensoring on the right with `X`, and then again with `Y`.
-/
def tensorRightTensor (X Y : C) : tensorRight (X ⊗ Y) ≅ tensorRight X ⋙ tensorRight Y :=
  NatIso.ofComponents (fun Z => (associator Z X Y).symm) fun Z Z' f => by
    dsimp'
    rw [← tensor_id]
    apply associator_inv_naturality

@[simp]
theorem tensor_right_tensor_hom_app (X Y Z : C) : (tensorRightTensor X Y).Hom.app Z = (associator Z X Y).inv :=
  rfl

@[simp]
theorem tensor_right_tensor_inv_app (X Y Z : C) : (tensorRightTensor X Y).inv.app Z = (associator Z X Y).Hom := by
  simp [← tensor_right_tensor]

end

end

section

universe v₁ v₂ u₁ u₂

variable (C₁ : Type u₁) [Category.{v₁} C₁] [MonoidalCategory.{v₁} C₁]

variable (C₂ : Type u₂) [Category.{v₂} C₂] [MonoidalCategory.{v₂} C₂]

attribute [local simp] associator_naturality left_unitor_naturality right_unitor_naturality pentagon

@[simps tensorObj tensorHom tensorUnit associator]
instance prodMonoidal : MonoidalCategory (C₁ × C₂) where
  tensorObj := fun X Y => (X.1 ⊗ Y.1, X.2 ⊗ Y.2)
  tensorHom := fun _ _ _ _ f g => (f.1 ⊗ g.1, f.2 ⊗ g.2)
  tensorUnit := (𝟙_ C₁, 𝟙_ C₂)
  associator := fun X Y Z => (α_ X.1 Y.1 Z.1).Prod (α_ X.2 Y.2 Z.2)
  leftUnitor := fun ⟨X₁, X₂⟩ => (λ_ X₁).Prod (λ_ X₂)
  rightUnitor := fun ⟨X₁, X₂⟩ => (ρ_ X₁).Prod (ρ_ X₂)

@[simp]
theorem prod_monoidal_left_unitor_hom_fst (X : C₁ × C₂) : ((λ_ X).Hom : 𝟙_ _ ⊗ X ⟶ X).1 = (λ_ X.1).Hom := by
  cases X
  rfl

@[simp]
theorem prod_monoidal_left_unitor_hom_snd (X : C₁ × C₂) : ((λ_ X).Hom : 𝟙_ _ ⊗ X ⟶ X).2 = (λ_ X.2).Hom := by
  cases X
  rfl

@[simp]
theorem prod_monoidal_left_unitor_inv_fst (X : C₁ × C₂) : ((λ_ X).inv : X ⟶ 𝟙_ _ ⊗ X).1 = (λ_ X.1).inv := by
  cases X
  rfl

@[simp]
theorem prod_monoidal_left_unitor_inv_snd (X : C₁ × C₂) : ((λ_ X).inv : X ⟶ 𝟙_ _ ⊗ X).2 = (λ_ X.2).inv := by
  cases X
  rfl

@[simp]
theorem prod_monoidal_right_unitor_hom_fst (X : C₁ × C₂) : ((ρ_ X).Hom : X ⊗ 𝟙_ _ ⟶ X).1 = (ρ_ X.1).Hom := by
  cases X
  rfl

@[simp]
theorem prod_monoidal_right_unitor_hom_snd (X : C₁ × C₂) : ((ρ_ X).Hom : X ⊗ 𝟙_ _ ⟶ X).2 = (ρ_ X.2).Hom := by
  cases X
  rfl

@[simp]
theorem prod_monoidal_right_unitor_inv_fst (X : C₁ × C₂) : ((ρ_ X).inv : X ⟶ X ⊗ 𝟙_ _).1 = (ρ_ X.1).inv := by
  cases X
  rfl

@[simp]
theorem prod_monoidal_right_unitor_inv_snd (X : C₁ × C₂) : ((ρ_ X).inv : X ⟶ X ⊗ 𝟙_ _).2 = (ρ_ X.2).inv := by
  cases X
  rfl

end

end MonoidalCategory

end CategoryTheory

