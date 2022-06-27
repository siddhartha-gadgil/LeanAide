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
The pre-image of a set under a function.
-/
def preimage (f : α → β) (X : Set β) : Set α := {a | f a ∈ X}

end Set