/-
Copyright (c) 2021 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathbin.CategoryTheory.Limits.Shapes.WideEqualizers
import Mathbin.CategoryTheory.Limits.Shapes.Products
import Mathbin.CategoryTheory.Limits.Shapes.Terminal

/-!
# Constructions related to weakly initial objects

This file gives constructions related to weakly initial objects, namely:
* If a category has small products and a small weakly initial set of objects, then it has a weakly
  initial object.
* If a category has wide equalizers and a weakly initial object, then it has an initial object.

These are primarily useful to show the General Adjoint Functor Theorem.
-/


universe v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C]

/-- If `C` has (small) products and a small weakly initial set of objects, then it has a weakly initial
object.
-/
theorem has_weakly_initial_of_weakly_initial_set_and_has_products [HasProducts.{v} C] {ι : Type v} {B : ι → C}
    (hB : ∀ A : C, ∃ i, Nonempty (B i ⟶ A)) : ∃ T : C, ∀ X, Nonempty (T ⟶ X) :=
  ⟨∏ B, fun X => ⟨Pi.π _ _ ≫ (hB X).some_spec.some⟩⟩

/-- If `C` has (small) wide equalizers and a weakly initial object, then it has an initial object.

The initial object is constructed as the wide equalizer of all endomorphisms on the given weakly
initial object.
-/
theorem has_initial_of_weakly_initial_and_has_wide_equalizers [HasWideEqualizers.{v} C] {T : C}
    (hT : ∀ X, Nonempty (T ⟶ X)) : HasInitial C := by
  let endos := T ⟶ T
  let i := wide_equalizer.ι (id : endos → endos)
  have : Nonempty endos := ⟨𝟙 _⟩
  have : ∀ X : C, Unique (wide_equalizer (id : endos → endos) ⟶ X) := by
    intro X
    refine' ⟨⟨i ≫ Classical.choice (hT X)⟩, fun a => _⟩
    let E := equalizer a (i ≫ Classical.choice (hT _))
    let e : E ⟶ wide_equalizer id := equalizer.ι _ _
    let h : T ⟶ E := Classical.choice (hT E)
    have : ((i ≫ h) ≫ e) ≫ i = i ≫ 𝟙 _ := by
      rw [category.assoc, category.assoc]
      apply wide_equalizer.condition (id : endos → endos) (h ≫ e ≫ i)
    rw [category.comp_id, cancel_mono_id i] at this
    have : split_epi e := ⟨i ≫ h, this⟩
    rw [← cancel_epi e]
    apply equalizer.condition
  exact has_initial_of_unique (wide_equalizer (id : endos → endos))

end CategoryTheory

