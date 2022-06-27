import Mathlib.Init.Set
import LeanCodePrompts.Foundations
/-
Some of the basic notation and terminology of set theory, such as unions, intersections, subsets, etc.
This will be useful in providing examples for point-set topology.
-/

namespace Set

variable {α : Type _} (X Y Z : Set α)

/-
The union of sets is commutative.
-/
theorem union_comm : X ∪ Y = Y ∪ X := by 
  apply funext; intro
  apply propext
  apply Iff.intro <;> apply disjunction_commutative

/-
The union of sets is associative.
-/
theorem union_assoc : (X ∪ Y) ∪ Z = X ∪ (Y ∪ Z) := by 
  apply funext; intro
  apply propext
  apply Iff.symm
  apply disjunction_associative

/-
The intersection of sets is commutative.
-/
theorem intersection_comm : X ∩ Y = Y ∩ X := by 
  apply funext; intro
  apply propext
  apply Iff.intro <;> apply conjunction_commutative

/-
The intersection of sets is associative.
-/
theorem intersection_assoc : (X ∩ Y) ∩ Z = X ∩ (Y ∩ Z) := by 
  apply funext; intro
  apply propext
  apply Iff.symm
  apply conjunction_associative

/-
Intersection left-distributes over union.
-/
theorem intersection_left_dist : X ∩ (Y ∪ Z) = (X ∩ Y) ∪ (X ∩ Z) := by 
  apply funext; intro
  apply propext
  apply conjunction_left_distributes

/-
Intersection right-distributes over union.
-/
theorem intersection_right_dist : (X ∪ Y) ∩ Z = (X ∩ Z) ∪ (Y ∩ Z) := by 
  apply funext; intro
  apply propext
  apply conjunction_right_distributes

/-
Union left-distributes over intersection.
-/
theorem union_left_dist : X ∪ (Y ∩ Z) = (X ∪ Y) ∩ (X ∪ Z) := by 
  apply funext; intro
  apply propext
  apply disjunction_left_distributes

/-
Union right-distributes over intersection.
-/
theorem union_right_dist : (X ∩ Y) ∪ Z = (X ∪ Z) ∩ (Y ∪ Z) := by 
  apply funext; intro
  apply propext
  apply disjunction_right_distributes

/-
The union of the empty set with a set is the set itself.
-/
theorem union_empty_left : ∅ ∪ X = X := by 
  apply funext; intro x
  apply propext
  show false ∨ (X x) ↔ (X x)
  simp

/-
The union of a set with the empty set is the set itself.
-/
theorem union_empty_right : X ∪ ∅ = X := by 
  apply funext; intro x
  apply propext
  show (X x) ∨ false ↔ (X x)
  simp

/-
The intersection of the universe with a set is the set itself.
-/
theorem intersection_universe_left : univ ∩ X = X := by 
  apply funext; intro
  apply propext
  apply true_conjunction_left_ident

/-
The intersection of a set with the universe is the set itself.
-/
theorem intersection_universe_right : X ∩ univ = X := by 
  apply funext; intro
  apply propext
  apply true_conjunction_right_ident

/-
The intersection of the empty set with a set is the empty set.
-/
theorem intersection_empty_left : ∅ ∩ X = ∅ := by 
  apply funext; intro x
  apply propext
  show false ∧ (X x) ↔ false
  simp

/-
The intersection of a set with the empty set is the empty set.
-/
theorem intersection_empty_right : X ∩ ∅ = ∅ := by 
  apply funext; intro x
  apply propext
  show (X x) ∧ false ↔ false
  simp

/-
The union of the universe with a set is the universe.
-/
theorem union_universe_left : univ ∪ X = univ := by 
  apply funext; intro
  apply propext
  apply true_disjunction_left_annihilator

/-
The union of a set with the universe is the universe.
-/
theorem union_universe_right : X ∪ univ = univ := by 
  apply funext; intro
  apply propext
  apply true_disjunction_right_annihilator

/-
Union of a set with itself is the set itself.  
-/
theorem union_self : X ∪ X = X := by 
  apply funext; intro
  apply propext
  apply Iff.symm
  apply equivalent_disjunction_self

/-
Intersection of a set with itself is the set itself.
-/
theorem intersection_self : X ∩ X = X := by 
  apply funext; intro
  apply propext
  apply Iff.symm 
  apply equivalent_conjunction_self

/-
Every set contains itself.
-/
theorem subset_self : X ⊆ X := id

/-
The subset relation is transitive.
-/
theorem subset_transitive : X ⊆ Y → Y ⊆ Z → X ⊆ Z := by
  intro hXY hYZ x h
  apply hYZ
  apply hXY
  exact h

/-
Every set is a subset of the universe.
-/
theorem subset_universe : X ⊆ univ := λ _ => trivial

/-
The empty set is a subset of every set.
-/
theorem empty_subset : ∅ ⊆ X := by intro _ h; contradiction 

/-
The empty set contains no elements.
-/
theorem empty_set_no_elem : ∀ {a : α}, ¬(a ∈ (∅ : Set α)) := by 
  intro _ h
  have : false = true := h 
  contradiction

/-
The union of two sets contains the individual sets.
-/
theorem union_subset : X ⊆ (X ∪ Y) ∧ Y ⊆ (X ∪ Y) := ⟨.inl, .inr⟩

/-
The intersection of two sets is contained in the individual sets.
-/
theorem intersection_subset : (X ∩ Y) ⊆ X ∧ (X ∩ Y) ⊆ Y := ⟨And.left, And.right⟩

/-
The intersection of two sets is contained in the union of the two sets.
-/

/-
The pre-image of a set under a function.
-/
def preimage (f : α → β) (X : Set β) : Set α := {a | f a ∈ X}

postfix:max "⁻¹" => preimage

/-
The pre-image of a set under the identity function is the set itself.
-/
theorem preimage_id (X : Set α) : id⁻¹ X = X := rfl 

/-
The image of a set under a function is the set itself.
-/
theorem image_id (X : Set α) : id <$> X = X := by simp 

/-
The pre-image of a set under the composition of two functions is the pre-image of the pre-image.
-/
theorem preimage_comp (f : α → β) (g : β → γ) (X : Set γ) : ((g ∘ f)⁻¹ X) = (f⁻¹ (g⁻¹ X)) := rfl

/-
The image of a set under the composition of two functions is the image of the image.
-/
theorem image_comp (f : α → β) (g : β → γ) (X : Set α) : (g <$> (f <$> X)) = ((g ∘ f) <$> X) := by
  simp only [Functor.map, image]
  ext 
  simp [setOf]
  intro
  apply propext
  apply Iff.intro
  · intro ⟨b, ⟨⟨a, ⟨h₁, h₂⟩⟩, h₃⟩⟩
    exact ⟨a, ⟨h₁, h₂ ▸ h₃⟩⟩
  · intro ⟨a, ⟨h₁, h₂⟩⟩
    exact ⟨f a, ⟨⟨a, ⟨h₁, rfl⟩⟩, h₂⟩⟩

/-
The pre-image of a union of sets is the union of the pre-images.
-/
theorem preimage_union (f : α → β) (S : Set (Set β)) : f⁻¹ (⋃₀ S) = ⋃₀ {f⁻¹ X | X ∈ S} := by
  simp [preimage, Functor.map]
  ext
  intro
  simp [setOf, sUnion]
  apply propext
  apply Iff.intro
  · intro ⟨a, ⟨h₁, h₂⟩⟩
    apply Exists.intro (f⁻¹ a)
    apply And.intro
    · exact ⟨a, ⟨h₁, rfl⟩⟩
    · apply h₂
  · intro ⟨a, ⟨⟨X, ⟨h₁, h₂⟩⟩, h₃⟩⟩
    apply Exists.intro X
    apply And.intro
    · exact h₁
    · revert h₃
      rw [← h₂]
      exact id 

/-
The image of a union of sets is the union of the images.
-/
theorem image_union (f : α → β) (S : Set (Set α)) : (f <$> (⋃₀ S)) = (⋃₀ ((Functor.map f) <$> S)) := by
  simp [image, Functor.map]
  ext
  simp [setOf, sUnion]
  intro
  apply propext
  apply Iff.intro
  · intro ⟨a, ⟨⟨X, ⟨h₁, h₂⟩⟩, h₃⟩⟩
    apply Exists.intro (f <$> X)
    apply And.intro
    · apply Exists.intro X 
      apply And.intro
      · exact h₁
      · simp [Functor.map, image]
        ext 
        intro
        simp [setOf]
    · exact ⟨a, ⟨h₂, h₃⟩⟩ 
  · intro ⟨b, ⟨⟨X, ⟨h₁, h₂⟩⟩, h₃⟩⟩
    rw [← h₂] at h₃
    have ⟨c, ⟨h₄, h₅⟩⟩ := h₃
    apply Exists.intro c
    apply And.intro
    · exact ⟨X, ⟨h₁, h₄⟩⟩
    · exact h₅

end Set