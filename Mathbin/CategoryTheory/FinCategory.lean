/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.Data.Fintype.Basic
import Mathbin.CategoryTheory.DiscreteCategory
import Mathbin.CategoryTheory.Opposites
import Mathbin.CategoryTheory.Category.Ulift

/-!
# Finite categories

A category is finite in this sense if it has finitely many objects, and finitely many morphisms.

## Implementation
Prior to #14046, `fin_category` required a `decidable_eq` instance on the object and morphism types.
This does not seem to have had any practical payoff (i.e. making some definition constructive)
so we have removed these requirements to avoid
having to supply instances or delay with non-defeq conflicts between instances.
-/


universe w v u

open Classical

noncomputable section

namespace CategoryTheory

instance discreteFintype {α : Type _} [Fintype α] : Fintype (Discrete α) :=
  Fintype.ofEquiv α discreteEquiv.symm

instance discreteHomFintype {α : Type _} (X Y : Discrete α) : Fintype (X ⟶ Y) := by
  apply ULift.fintype

/-- A category with a `fintype` of objects, and a `fintype` for each morphism space. -/
class FinCategory (J : Type v) [SmallCategory J] where
  fintypeObj : Fintype J := by
    run_tac
      tactic.apply_instance
  fintypeHom : ∀ j j' : J, Fintype (j ⟶ j') := by
    run_tac
      tactic.apply_instance

attribute [instance] fin_category.fintype_obj fin_category.fintype_hom

instance finCategoryDiscreteOfFintype (J : Type v) [Fintype J] : FinCategory (Discrete J) where

namespace FinCategory

variable (α : Type _) [Fintype α] [SmallCategory α] [FinCategory α]

/-- A fin_category `α` is equivalent to a category with objects in `Type`. -/
@[nolint unused_arguments]
abbrev ObjAsType : Type :=
  InducedCategory α (Fintype.equivFin α).symm

/-- The constructed category is indeed equivalent to `α`. -/
noncomputable def objAsTypeEquiv : ObjAsType α ≌ α :=
  (inducedFunctor (Fintype.equivFin α).symm).asEquivalence

/-- A fin_category `α` is equivalent to a fin_category with in `Type`. -/
@[nolint unused_arguments]
abbrev AsType : Type :=
  Finₓ (Fintype.card α)

@[simps (config := lemmasOnly) hom id comp]
noncomputable instance categoryAsType : SmallCategory (AsType α) where
  hom := fun i j => Finₓ (Fintype.card (@Quiver.Hom (ObjAsType α) _ i j))
  id := fun i => Fintype.equivFin _ (𝟙 i)
  comp := fun i j k f g => Fintype.equivFin _ ((Fintype.equivFin _).symm f ≫ (Fintype.equivFin _).symm g)

attribute [local simp] category_as_type_hom category_as_type_id category_as_type_comp

/-- The "identity" functor from `as_type α` to `obj_as_type α`. -/
@[simps]
noncomputable def asTypeToObjAsType : AsType α ⥤ ObjAsType α where
  obj := id
  map := fun i j => (Fintype.equivFin _).symm

/-- The "identity" functor from `obj_as_type α` to `as_type α`. -/
@[simps]
noncomputable def objAsTypeToAsType : ObjAsType α ⥤ AsType α where
  obj := id
  map := fun i j => Fintype.equivFin _

/-- The constructed category (`as_type α`) is equivalent to `obj_as_type α`. -/
noncomputable def asTypeEquivObjAsType : AsType α ≌ ObjAsType α :=
  Equivalence.mk (asTypeToObjAsType α) (objAsTypeToAsType α)
    ((NatIso.ofComponents Iso.refl) fun _ _ _ => by
      dsimp'
      simp )
    ((NatIso.ofComponents Iso.refl) fun _ _ _ => by
      dsimp'
      simp )

noncomputable instance asTypeFinCategory : FinCategory (AsType α) where

/-- The constructed category (`as_type α`) is indeed equivalent to `α`. -/
noncomputable def equivAsType : AsType α ≌ α :=
  (asTypeEquivObjAsType α).trans (objAsTypeEquiv α)

end FinCategory

open Opposite

/-- The opposite of a finite category is finite.
-/
instance finCategoryOpposite {J : Type v} [SmallCategory J] [FinCategory J] : FinCategory Jᵒᵖ where
  fintypeObj := Fintype.ofEquiv _ equivToOpposite
  fintypeHom := fun j j' => Fintype.ofEquiv _ (opEquiv j j').symm

/-- Applying `ulift` to morphisms and objects of a category preserves finiteness. -/
instance finCategoryUlift {J : Type v} [SmallCategory J] [FinCategory J] :
    FinCategory.{max w v} (UliftHom.{w, max w v} (ULift.{w, v} J)) where fintypeObj := ULift.fintype J

end CategoryTheory

