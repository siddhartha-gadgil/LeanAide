/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathbin.Data.List.Chain
import Mathbin.CategoryTheory.Punit
import Mathbin.CategoryTheory.IsConnected
import Mathbin.CategoryTheory.Sigma.Basic
import Mathbin.CategoryTheory.FullSubcategory

/-!
# Connected components of a category

Defines a type `connected_components J` indexing the connected components of a category, and the
full subcategories giving each connected component: `component j : Type u₁`.
We show that each `component j` is in fact connected.

We show every category can be expressed as a disjoint union of its connected components, in
particular `decomposed J` is the category (definitionally) given by the sigma-type of the connected
components of `J`, and it is shown that this is equivalent to `J`.
-/


universe v₁ v₂ v₃ u₁ u₂

noncomputable section

open CategoryTheory.Category

namespace CategoryTheory

attribute [instance] is_connected.is_nonempty

variable {J : Type u₁} [Category.{v₁} J]

variable {C : Type u₂} [Category.{u₁} C]

/-- This type indexes the connected components of the category `J`. -/
def ConnectedComponents (J : Type u₁) [Category.{v₁} J] : Type u₁ :=
  Quotientₓ (Zigzag.setoid J)

instance [Inhabited J] : Inhabited (ConnectedComponents J) :=
  ⟨Quotientₓ.mk' default⟩

/-- Given an index for a connected component, produce the actual component as a full subcategory. -/
def Component (j : ConnectedComponents J) : Type u₁ :=
  { k : J // Quotientₓ.mk' k = j }deriving Category

/-- The inclusion functor from a connected component to the whole category. -/
@[simps (config := { rhsMd := semireducible })]
def Component.ι (j) : Component j ⥤ J :=
  fullSubcategoryInclusion _ deriving Full, Faithful

/-- Each connected component of the category is nonempty. -/
instance (j : ConnectedComponents J) : Nonempty (Component j) := by
  apply Quotientₓ.induction_on' j
  intro k
  refine' ⟨⟨k, rfl⟩⟩

instance (j : ConnectedComponents J) : Inhabited (Component j) :=
  Classical.inhabitedOfNonempty'

/-- Each connected component of the category is connected. -/
instance (j : ConnectedComponents J) : IsConnected (Component j) := by
  -- Show it's connected by constructing a zigzag (in `component j`) between any two objects
  apply is_connected_of_zigzag
  rintro ⟨j₁, hj₁⟩ ⟨j₂, rfl⟩
  -- We know that the underlying objects j₁ j₂ have some zigzag between them in `J`
  have h₁₂ : zigzag j₁ j₂ := Quotientₓ.exact' hj₁
  -- Get an explicit zigzag as a list
  rcases List.exists_chain_of_relation_refl_trans_gen h₁₂ with ⟨l, hl₁, hl₂⟩
  -- Everything which has a zigzag to j₂ can be lifted to the same component as `j₂`.
  let f : ∀ x, zigzag x j₂ → component (Quotientₓ.mk' j₂) := fun x h => ⟨x, Quotientₓ.sound' h⟩
  -- Everything in our chosen zigzag from `j₁` to `j₂` has a zigzag to `j₂`.
  have hf : ∀ a : J, a ∈ l → zigzag a j₂ := by
    intro i hi
    apply List.Chain.induction (fun t => zigzag t j₂) _ hl₁ hl₂ _ _ _ (Or.inr hi)
    · intro j k
      apply Relation.ReflTransGen.head
      
    · apply Relation.ReflTransGen.refl
      
  -- Now lift the zigzag from `j₁` to `j₂` in `J` to the same thing in `component j`.
  refine' ⟨l.pmap f hf, _, _⟩
  · refine' @List.chain_pmap_of_chain _ _ _ f (fun x y _ _ h => _) hl₁ h₁₂ _
    exact zag_of_zag_obj (component.ι _) h
    
  · erw
      [List.last_pmap _ f (j₁ :: l)
        (by
          simpa [← h₁₂] using hf)
        (List.cons_ne_nil _ _)]
    exact Subtype.ext hl₂
    

/-- The disjoint union of `J`s connected components, written explicitly as a sigma-type with the
category structure.
This category is equivalent to `J`.
-/
abbrev Decomposed (J : Type u₁) [Category.{v₁} J] :=
  Σj : ConnectedComponents J, Component j

/-- The inclusion of each component into the decomposed category. This is just `sigma.incl` but having
this abbreviation helps guide typeclass search to get the right category instance on `decomposed J`.
-/
-- This name may cause clashes further down the road, and so might need to be changed.
abbrev inclusion (j : ConnectedComponents J) : Component j ⥤ Decomposed J :=
  Sigma.incl _

/-- The forward direction of the equivalence between the decomposed category and the original. -/
@[simps (config := { rhsMd := semireducible })]
def decomposedTo (J : Type u₁) [Category.{v₁} J] : Decomposed J ⥤ J :=
  Sigma.desc Component.ι

@[simp]
theorem inclusion_comp_decomposed_to (j : ConnectedComponents J) : inclusion j ⋙ decomposedTo J = Component.ι j :=
  rfl

instance : Full (decomposedTo J) where
  Preimage := by
    rintro ⟨j', X, hX⟩ ⟨k', Y, hY⟩ f
    dsimp'  at f
    have : j' = k'
    rw [← hX, ← hY, Quotientₓ.eq']
    exact Relation.ReflTransGen.single (Or.inl ⟨f⟩)
    subst this
    refine' sigma.sigma_hom.mk f
  witness' := by
    rintro ⟨j', X, hX⟩ ⟨_, Y, rfl⟩ f
    have : Quotientₓ.mk' Y = j' := by
      rw [← hX, Quotientₓ.eq']
      exact Relation.ReflTransGen.single (Or.inr ⟨f⟩)
    subst this
    rfl

instance :
    Faithful (decomposedTo J) where map_injective' := by
    rintro ⟨_, j, rfl⟩ ⟨_, k, hY⟩ ⟨_, _, _, f⟩ ⟨_, _, _, g⟩ e
    change f = g at e
    subst e

instance : EssSurj (decomposedTo J) where mem_ess_image := fun j => ⟨⟨_, j, rfl⟩, ⟨Iso.refl _⟩⟩

instance : IsEquivalence (decomposedTo J) :=
  Equivalence.ofFullyFaithfullyEssSurj _

/-- This gives that any category is equivalent to a disjoint union of connected categories. -/
@[simps (config := { rhsMd := semireducible }) Functor]
def decomposedEquiv : Decomposed J ≌ J :=
  (decomposedTo J).asEquivalence

end CategoryTheory

