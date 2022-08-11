/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.Algebra.Category.Mon.Basic
import Mathbin.CategoryTheory.Limits.HasLimits
import Mathbin.CategoryTheory.Limits.ConcreteCategory

/-!
# The category of monoids has all colimits.

We do this construction knowing nothing about monoids.
In particular, I want to claim that this file could be produced by a python script
that just looks at the output of `#print monoid`:

  -- structure monoid : Type u → Type u
  -- fields:
  -- monoid.mul : Π {α : Type u} [c : monoid α], α → α → α
  -- monoid.mul_assoc : ∀ {α : Type u} [c : monoid α] (a b c_1 : α), a * b * c_1 = a * (b * c_1)
  -- monoid.one : Π (α : Type u) [c : monoid α], α
  -- monoid.one_mul : ∀ {α : Type u} [c : monoid α] (a : α), 1 * a = a
  -- monoid.mul_one : ∀ {α : Type u} [c : monoid α] (a : α), a * 1 = a

and if we'd fed it the output of `#print comm_ring`, this file would instead build
colimits of commutative rings.

A slightly bolder claim is that we could do this with tactics, as well.
-/


universe v

open CategoryTheory

open CategoryTheory.Limits

namespace Mon.Colimits

/-!
We build the colimit of a diagram in `Mon` by constructing the
free monoid on the disjoint union of all the monoids in the diagram,
then taking the quotient by the monoid laws within each monoid,
and the identifications given by the morphisms in the diagram.
-/


variable {J : Type v} [SmallCategory J] (F : J ⥤ Mon.{v})

/-- An inductive type representing all monoid expressions (without relations)
on a collection of types indexed by the objects of `J`.
-/
inductive Prequotient-- There's always `of`

  | of : ∀ (j : J) (x : F.obj j), prequotient-- Then one generator for each operation

  | one : prequotient
  | mul : prequotient → prequotient → prequotient

instance : Inhabited (Prequotient F) :=
  ⟨Prequotient.one⟩

open Prequotient

/-- The relation on `prequotient` saying when two expressions are equal
because of the monoid laws, or
because one element is mapped to another by a morphism in the diagram.
-/
inductive Relation : Prequotient F → Prequotient F → Prop-- Make it an equivalence relation:

  | refl : ∀ x, relation x x
  | symm : ∀ (x y) (h : relation x y), relation y x
  | trans : ∀ (x y z) (h : relation x y) (k : relation y z), relation x z-- There's always a `map` relation

  | map :
    ∀ (j j' : J) (f : j ⟶ j') (x : F.obj j),
      relation (of j' ((F.map f) x)) (of j x)-- Then one relation per operation, describing the interaction with `of`

  | mul : ∀ (j) (x y : F.obj j), relation (of j (x * y)) (mul (of j x) (of j y))
  | one : ∀ j, relation (of j 1) one-- Then one relation per argument of each operation

  | mul_1 : ∀ (x x' y) (r : relation x x'), relation (mul x y) (mul x' y)
  | mul_2 : ∀ (x y y') (r : relation y y'), relation (mul x y) (mul x y')-- And one relation per axiom

  | mul_assoc : ∀ x y z, relation (mul (mul x y) z) (mul x (mul y z))
  | one_mulₓ : ∀ x, relation (mul one x) x
  | mul_oneₓ : ∀ x, relation (mul x one) x

/-- The setoid corresponding to monoid expressions modulo monoid relations and identifications.
-/
def colimitSetoid : Setoidₓ (Prequotient F) where
  R := Relation F
  iseqv := ⟨Relation.refl, Relation.symm, Relation.trans⟩

attribute [instance] colimit_setoid

/-- The underlying type of the colimit of a diagram in `Mon`.
-/
def ColimitType : Type v :=
  Quotientₓ (colimitSetoid F)deriving Inhabited

instance monoidColimitType : Monoidₓ (ColimitType F) where
  mul := by
    fapply @Quot.lift _ _ (colimit_type F → colimit_type F)
    · intro x
      fapply @Quot.lift
      · intro y
        exact Quot.mk _ (mul x y)
        
      · intro y y' r
        apply Quot.sound
        exact relation.mul_2 _ _ _ r
        
      
    · intro x x' r
      funext y
      induction y
      dsimp'
      apply Quot.sound
      · exact relation.mul_1 _ _ _ r
        
      · rfl
        
      
  one := Quot.mk _ one
  mul_assoc := fun x y z => by
    induction x
    induction y
    induction z
    dsimp'
    apply Quot.sound
    apply relation.mul_assoc
    rfl
    rfl
    rfl
  one_mul := fun x => by
    induction x
    dsimp'
    apply Quot.sound
    apply relation.one_mul
    rfl
  mul_one := fun x => by
    induction x
    dsimp'
    apply Quot.sound
    apply relation.mul_one
    rfl

@[simp]
theorem quot_one : Quot.mk Setoidₓ.R one = (1 : ColimitType F) :=
  rfl

@[simp]
theorem quot_mul (x y) : Quot.mk Setoidₓ.R (mul x y) = (Quot.mk Setoidₓ.R x * Quot.mk Setoidₓ.R y : ColimitType F) :=
  rfl

/-- The bundled monoid giving the colimit of a diagram. -/
def colimit : Mon :=
  ⟨ColimitType F, by
    infer_instance⟩

/-- The function from a given monoid in the diagram to the colimit monoid. -/
def coconeFun (j : J) (x : F.obj j) : ColimitType F :=
  Quot.mk _ (of j x)

/-- The monoid homomorphism from a given monoid in the diagram to the colimit monoid. -/
def coconeMorphism (j : J) : F.obj j ⟶ colimit F where
  toFun := coconeFun F j
  map_one' := Quot.sound (Relation.one _)
  map_mul' := fun x y => Quot.sound (Relation.mul _ _ _)

@[simp]
theorem cocone_naturality {j j' : J} (f : j ⟶ j') : F.map f ≫ coconeMorphism F j' = coconeMorphism F j := by
  ext
  apply Quot.sound
  apply Relation.Map

@[simp]
theorem cocone_naturality_components (j j' : J) (f : j ⟶ j') (x : F.obj j) :
    (coconeMorphism F j') (F.map f x) = (coconeMorphism F j) x := by
  rw [← cocone_naturality F f]
  rfl

/-- The cocone over the proposed colimit monoid. -/
def colimitCocone : Cocone F where
  x := colimit F
  ι := { app := coconeMorphism F }

/-- The function from the free monoid on the diagram to the cone point of any other cocone. -/
@[simp]
def descFunLift (s : Cocone F) : Prequotient F → s.x
  | of j x => (s.ι.app j) x
  | one => 1
  | mul x y => desc_fun_lift x * desc_fun_lift y

/-- The function from the colimit monoid to the cone point of any other cocone. -/
def descFun (s : Cocone F) : ColimitType F → s.x := by
  fapply Quot.lift
  · exact desc_fun_lift F s
    
  · intro x y r
    induction r <;>
      try
        dsimp'
    -- refl
    · rfl
      
    -- symm
    · exact r_ih.symm
      
    -- trans
    · exact Eq.trans r_ih_h r_ih_k
      
    -- map
    · simp
      
    -- mul
    · simp
      
    -- one
    · simp
      
    -- mul_1
    · rw [r_ih]
      
    -- mul_2
    · rw [r_ih]
      
    -- mul_assoc
    · rw [mul_assoc]
      
    -- one_mul
    · rw [one_mulₓ]
      
    -- mul_one
    · rw [mul_oneₓ]
      
    

/-- The monoid homomorphism from the colimit monoid to the cone point of any other cocone. -/
def descMorphism (s : Cocone F) : colimit F ⟶ s.x where
  toFun := descFun F s
  map_one' := rfl
  map_mul' := fun x y => by
    induction x <;> induction y <;> rfl

/-- Evidence that the proposed colimit is the colimit. -/
def colimitIsColimit : IsColimit (colimitCocone F) where
  desc := fun s => descMorphism F s
  uniq' := fun s m w => by
    ext
    induction x
    induction x
    · have w' := congr_fun (congr_arg (fun f : F.obj x_j ⟶ s.X => (f : F.obj x_j → s.X)) (w x_j)) x_x
      erw [w']
      rfl
      
    · simp [*]
      
    · simp [*]
      
    rfl

instance has_colimits_Mon :
    HasColimits
      Mon where HasColimitsOfShape := fun J 𝒥 =>
    { HasColimit := fun F => has_colimit.mk { Cocone := colimit_cocone F, IsColimit := colimit_is_colimit F } }

end Mon.Colimits

