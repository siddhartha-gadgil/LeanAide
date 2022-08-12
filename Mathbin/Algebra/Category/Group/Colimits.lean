/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.Algebra.Category.Group.Preadditive
import Mathbin.GroupTheory.QuotientGroup
import Mathbin.CategoryTheory.Limits.ConcreteCategory
import Mathbin.CategoryTheory.Limits.Shapes.Kernels
import Mathbin.CategoryTheory.Limits.Shapes.ConcreteCategory

/-!
# The category of additive commutative groups has all colimits.

This file uses a "pre-automated" approach, just as for `Mon/colimits.lean`.
It is a very uniform approach, that conceivably could be synthesised directly
by a tactic that analyses the shape of `add_comm_group` and `monoid_hom`.

TODO:
In fact, in `AddCommGroup` there is a much nicer model of colimits as quotients
of finitely supported functions, and we really should implement this as well (or instead).
-/


universe u v

open CategoryTheory

open CategoryTheory.Limits

-- [ROBOT VOICE]:
-- You should pretend for now that this file was automatically generated.
-- It follows the same template as colimits in Mon.
namespace AddCommGroupₓₓ.Colimits

/-!
We build the colimit of a diagram in `AddCommGroup` by constructing the
free group on the disjoint union of all the abelian groups in the diagram,
then taking the quotient by the abelian group laws within each abelian group,
and the identifications given by the morphisms in the diagram.
-/


variable {J : Type v} [SmallCategory J] (F : J ⥤ AddCommGroupₓₓ.{v})

/-- An inductive type representing all group expressions (without relations)
on a collection of types indexed by the objects of `J`.
-/
inductive Prequotient-- There's always `of`

  | of : ∀ (j : J) (x : F.obj j), prequotient-- Then one generator for each operation

  | zero : prequotient
  | neg : prequotient → prequotient
  | add : prequotient → prequotient → prequotient

instance : Inhabited (Prequotient F) :=
  ⟨Prequotient.zero⟩

open Prequotient

/-- The relation on `prequotient` saying when two expressions are equal
because of the abelian group laws, or
because one element is mapped to another by a morphism in the diagram.
-/
inductive Relation : Prequotient F → Prequotient F → Prop-- Make it an equivalence relation:

  | refl : ∀ x, relation x x
  | symm : ∀ (x y) (h : relation x y), relation y x
  | trans : ∀ (x y z) (h : relation x y) (k : relation y z), relation x z-- There's always a `map` relation

  | map :
    ∀ (j j' : J) (f : j ⟶ j') (x : F.obj j),
      relation (of j' (F.map f x)) (of j x)-- Then one relation per operation, describing the interaction with `of`

  | zero : ∀ j, relation (of j 0) zero
  | neg : ∀ (j) (x : F.obj j), relation (of j (-x)) (neg (of j x))
  | add :
    ∀ (j) (x y : F.obj j),
      relation (of j (x + y)) (add (of j x) (of j y))-- Then one relation per argument of each operation

  | neg_1 : ∀ (x x') (r : relation x x'), relation (neg x) (neg x')
  | add_1 : ∀ (x x' y) (r : relation x x'), relation (add x y) (add x' y)
  | add_2 : ∀ (x y y') (r : relation y y'), relation (add x y) (add x y')-- And one relation per axiom

  | zero_addₓ : ∀ x, relation (add zero x) x
  | add_zeroₓ : ∀ x, relation (add x zero) x
  | add_left_negₓ : ∀ x, relation (add (neg x) x) zero
  | add_commₓ : ∀ x y, relation (add x y) (add y x)
  | add_assocₓ : ∀ x y z, relation (add (add x y) z) (add x (add y z))

/-- The setoid corresponding to group expressions modulo abelian group relations and identifications.
-/
def colimitSetoid : Setoidₓ (Prequotient F) where
  R := Relation F
  iseqv := ⟨Relation.refl, Relation.symm, Relation.trans⟩

attribute [instance] colimit_setoid

/-- The underlying type of the colimit of a diagram in `AddCommGroup`.
-/
def ColimitType : Type v :=
  Quotientₓ (colimitSetoid F)deriving Inhabited

instance : AddCommGroupₓ (ColimitType F) where
  zero := Quot.mk _ zero
  neg := by
    fapply @Quot.lift
    · intro x
      exact Quot.mk _ (neg x)
      
    · intro x x' r
      apply Quot.sound
      exact relation.neg_1 _ _ r
      
  add := by
    fapply @Quot.lift _ _ (colimit_type F → colimit_type F)
    · intro x
      fapply @Quot.lift
      · intro y
        exact Quot.mk _ (add x y)
        
      · intro y y' r
        apply Quot.sound
        exact relation.add_2 _ _ _ r
        
      
    · intro x x' r
      funext y
      induction y
      dsimp'
      apply Quot.sound
      · exact relation.add_1 _ _ _ r
        
      · rfl
        
      
  zero_add := fun x => by
    induction x
    dsimp'
    apply Quot.sound
    apply relation.zero_add
    rfl
  add_zero := fun x => by
    induction x
    dsimp'
    apply Quot.sound
    apply relation.add_zero
    rfl
  add_left_neg := fun x => by
    induction x
    dsimp'
    apply Quot.sound
    apply relation.add_left_neg
    rfl
  add_comm := fun x y => by
    induction x
    induction y
    dsimp'
    apply Quot.sound
    apply relation.add_comm
    rfl
    rfl
  add_assoc := fun x y z => by
    induction x
    induction y
    induction z
    dsimp'
    apply Quot.sound
    apply relation.add_assoc
    rfl
    rfl
    rfl

@[simp]
theorem quot_zero : Quot.mk Setoidₓ.R zero = (0 : ColimitType F) :=
  rfl

@[simp]
theorem quot_neg (x) : Quot.mk Setoidₓ.R (neg x) = (-Quot.mk Setoidₓ.R x : ColimitType F) :=
  rfl

@[simp]
theorem quot_add (x y) : Quot.mk Setoidₓ.R (add x y) = (Quot.mk Setoidₓ.R x + Quot.mk Setoidₓ.R y : ColimitType F) :=
  rfl

/-- The bundled abelian group giving the colimit of a diagram. -/
def colimit : AddCommGroupₓₓ :=
  AddCommGroupₓₓ.of (ColimitType F)

/-- The function from a given abelian group in the diagram to the colimit abelian group. -/
def coconeFun (j : J) (x : F.obj j) : ColimitType F :=
  Quot.mk _ (of j x)

/-- The group homomorphism from a given abelian group in the diagram to the colimit abelian
group. -/
def coconeMorphism (j : J) : F.obj j ⟶ colimit F where
  toFun := coconeFun F j
  map_zero' := by
    apply Quot.sound <;> apply relation.zero
  map_add' := by
    intros <;> apply Quot.sound <;> apply relation.add

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

/-- The cocone over the proposed colimit abelian group. -/
def colimitCocone : Cocone F where
  x := colimit F
  ι := { app := coconeMorphism F }

/-- The function from the free abelian group on the diagram to the cone point of any other
cocone. -/
@[simp]
def descFunLift (s : Cocone F) : Prequotient F → s.x
  | of j x => (s.ι.app j) x
  | zero => 0
  | neg x => -desc_fun_lift x
  | add x y => desc_fun_lift x + desc_fun_lift y

/-- The function from the colimit abelian group to the cone point of any other cocone. -/
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
      
    -- zero
    · simp
      
    -- neg
    · simp
      
    -- add
    · simp
      
    -- neg_1
    · rw [r_ih]
      
    -- add_1
    · rw [r_ih]
      
    -- add_2
    · rw [r_ih]
      
    -- zero_add
    · rw [zero_addₓ]
      
    -- add_zero
    · rw [add_zeroₓ]
      
    -- add_left_neg
    · rw [add_left_negₓ]
      
    -- add_comm
    · rw [add_commₓ]
      
    -- add_assoc
    · rw [add_assocₓ]
      
    

/-- The group homomorphism from the colimit abelian group to the cone point of any other cocone. -/
def descMorphism (s : Cocone F) : colimit F ⟶ s.x where
  toFun := descFun F s
  map_zero' := rfl
  map_add' := fun x y => by
    induction x <;> induction y <;> rfl

/-- Evidence that the proposed colimit is the colimit. -/
def colimitCoconeIsColimit : IsColimit (colimitCocone F) where
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
      
    · simp [*]
      
    rfl

instance has_colimits_AddCommGroup :
    HasColimits
      AddCommGroupₓₓ where HasColimitsOfShape := fun J 𝒥 =>
    { HasColimit := fun F => has_colimit.mk { Cocone := colimit_cocone F, IsColimit := colimit_cocone_is_colimit F } }

end AddCommGroupₓₓ.Colimits

namespace AddCommGroupₓₓ

open QuotientAddGroup

/-- The categorical cokernel of a morphism in `AddCommGroup`
agrees with the usual group-theoretical quotient.
-/
noncomputable def cokernelIsoQuotient {G H : AddCommGroupₓₓ.{u}} (f : G ⟶ H) :
    cokernel f ≅ AddCommGroupₓₓ.of (H ⧸ AddMonoidHom.range f) where
  Hom :=
    cokernel.desc f (mk' _)
      (by
        ext
        apply Quotientₓ.sound
        apply left_rel_apply.mpr
        fconstructor
        exact -x
        simp only [← add_zeroₓ, ← AddMonoidHom.map_neg])
  inv :=
    QuotientAddGroup.lift _ (cokernel.π f)
      (by
        intro x H_1
        cases H_1
        induction H_1_h
        simp only [← cokernel.condition_apply, ← zero_apply])
  -- obviously can take care of the next goals, but it is really slow
  hom_inv_id' := by
    ext1
    simp only [← coequalizer_as_cokernel, ← category.comp_id, ← cokernel.π_desc_assoc]
    ext1
    rfl
  inv_hom_id' := by
    ext x : 2
    simp only [← colimit.ι_desc_apply, ← id_apply, ← lift_mk, ← mk'_apply, ← cofork.of_π_ι_app, ← comp_apply, ←
      AddMonoidHom.comp_apply]

end AddCommGroupₓₓ

