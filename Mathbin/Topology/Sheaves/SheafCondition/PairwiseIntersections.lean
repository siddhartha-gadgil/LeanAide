/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.Topology.Sheaves.SheafCondition.Sites
import Mathbin.CategoryTheory.Limits.Preserves.Basic
import Mathbin.CategoryTheory.Category.Pairwise
import Mathbin.CategoryTheory.Limits.Constructions.BinaryProducts

/-!
# Equivalent formulations of the sheaf condition

We give an equivalent formulation of the sheaf condition.

Given any indexed type `ι`, we define `overlap ι`,
a category with objects corresponding to
* individual open sets, `single i`, and
* intersections of pairs of open sets, `pair i j`,
with morphisms from `pair i j` to both `single i` and `single j`.

Any open cover `U : ι → opens X` provides a functor `diagram U : overlap ι ⥤ (opens X)ᵒᵖ`.

There is a canonical cone over this functor, `cone U`, whose cone point is `supr U`,
and in fact this is a limit cone.

A presheaf `F : presheaf C X` is a sheaf precisely if it preserves this limit.
We express this in two equivalent ways, as
* `is_limit (F.map_cone (cone U))`, or
* `preserves_limit (diagram U) F`
-/


noncomputable section

universe v u

open TopologicalSpace

open Top

open Opposite

open CategoryTheory

open CategoryTheory.Limits

namespace Top.Presheaf

variable {X : Top.{v}}

variable {C : Type u} [Category.{v} C]

/-- An alternative formulation of the sheaf condition
(which we prove equivalent to the usual one below as
`is_sheaf_iff_is_sheaf_pairwise_intersections`).

A presheaf is a sheaf if `F` sends the cone `(pairwise.cocone U).op` to a limit cone.
(Recall `pairwise.cocone U` has cone point `supr U`, mapping down to the `U i` and the `U i ⊓ U j`.)
-/
def IsSheafPairwiseIntersections (F : Presheaf C X) : Prop :=
  ∀ ⦃ι : Type v⦄ (U : ι → Opens X), Nonempty (IsLimit (F.mapCone (Pairwise.cocone U).op))

/-- An alternative formulation of the sheaf condition
(which we prove equivalent to the usual one below as
`is_sheaf_iff_is_sheaf_preserves_limit_pairwise_intersections`).

A presheaf is a sheaf if `F` preserves the limit of `pairwise.diagram U`.
(Recall `pairwise.diagram U` is the diagram consisting of the pairwise intersections
`U i ⊓ U j` mapping into the open sets `U i`. This diagram has limit `supr U`.)
-/
def IsSheafPreservesLimitPairwiseIntersections (F : Presheaf C X) : Prop :=
  ∀ ⦃ι : Type v⦄ (U : ι → Opens X), Nonempty (PreservesLimit (Pairwise.diagram U).op F)

/-!
The remainder of this file shows that these conditions are equivalent
to the usual sheaf condition.
-/


variable [HasProducts.{v} C]

namespace SheafConditionPairwiseIntersections

open CategoryTheory.Pairwise CategoryTheory.Pairwise.Hom

open SheafConditionEqualizerProducts

/-- Implementation of `sheaf_condition_pairwise_intersections.cone_equiv`. -/
@[simps]
def coneEquivFunctorObj (F : Presheaf C X) ⦃ι : Type v⦄ (U : ι → Opens ↥X) (c : Limits.Cone ((diagram U).op ⋙ F)) :
    Limits.Cone (SheafConditionEqualizerProducts.diagram F U) where
  x := c.x
  π :=
    { app := fun Z =>
        WalkingParallelPair.casesOn Z (Pi.lift fun i : ι => c.π.app (op (single i)))
          (Pi.lift fun b : ι × ι => c.π.app (op (pair b.1 b.2))),
      naturality' := fun Y Z f => by
        cases Y <;> cases Z <;> cases f
        · ext i
          dsimp'
          simp only [← limit.lift_π, ← category.id_comp, ← fan.mk_π_app, ← CategoryTheory.Functor.map_id, ←
            category.assoc]
          dsimp'
          simp only [← limit.lift_π, ← category.id_comp, ← fan.mk_π_app]
          
        · ext ⟨i, j⟩
          dsimp' [← sheaf_condition_equalizer_products.left_res]
          simp only [← limit.lift_π, ← limit.lift_π_assoc, ← category.id_comp, ← fan.mk_π_app, ← category.assoc]
          have h := c.π.naturality (Quiver.Hom.op (hom.left i j))
          dsimp'  at h
          simpa using h
          
        · ext ⟨i, j⟩
          dsimp' [← sheaf_condition_equalizer_products.right_res]
          simp only [← limit.lift_π, ← limit.lift_π_assoc, ← category.id_comp, ← fan.mk_π_app, ← category.assoc]
          have h := c.π.naturality (Quiver.Hom.op (hom.right i j))
          dsimp'  at h
          simpa using h
          
        · ext i
          dsimp'
          simp only [← limit.lift_π, ← category.id_comp, ← fan.mk_π_app, ← CategoryTheory.Functor.map_id, ←
            category.assoc]
          dsimp'
          simp only [← limit.lift_π, ← category.id_comp, ← fan.mk_π_app]
           }

section

attribute [local tidy] tactic.case_bash

/-- Implementation of `sheaf_condition_pairwise_intersections.cone_equiv`. -/
@[simps]
def coneEquivFunctor (F : Presheaf C X) ⦃ι : Type v⦄ (U : ι → Opens ↥X) :
    Limits.Cone ((diagram U).op ⋙ F) ⥤ Limits.Cone (SheafConditionEqualizerProducts.diagram F U) where
  obj := fun c => coneEquivFunctorObj F U c
  map := fun c c' f =>
    { Hom := f.Hom,
      w' := fun j => by
        cases j <;>
          · ext
            simp only [← limits.fan.mk_π_app, ← limits.cone_morphism.w, ← limits.limit.lift_π, ← category.assoc, ←
              cone_equiv_functor_obj_π_app]
             }

end

/-- Implementation of `sheaf_condition_pairwise_intersections.cone_equiv`. -/
@[simps]
def coneEquivInverseObj (F : Presheaf C X) ⦃ι : Type v⦄ (U : ι → Opens ↥X)
    (c : Limits.Cone (SheafConditionEqualizerProducts.diagram F U)) : Limits.Cone ((diagram U).op ⋙ F) where
  x := c.x
  π :=
    { app := by
        intro x
        induction x using Opposite.rec
        rcases x with (⟨i⟩ | ⟨i, j⟩)
        · exact c.π.app walking_parallel_pair.zero ≫ pi.π _ i
          
        · exact c.π.app walking_parallel_pair.one ≫ pi.π _ (i, j)
          ,
      naturality' := by
        intro x y f
        induction x using Opposite.rec
        induction y using Opposite.rec
        have ef : f = f.unop.op := rfl
        revert ef
        generalize f.unop = f'
        rintro rfl
        rcases x with (⟨i⟩ | ⟨⟩) <;> rcases y with (⟨⟩ | ⟨j, j⟩) <;> rcases f' with ⟨⟩
        · dsimp'
          erw [F.map_id]
          simp
          
        · dsimp'
          simp only [← category.id_comp, ← category.assoc]
          have h := c.π.naturality walking_parallel_pair_hom.left
          dsimp' [← sheaf_condition_equalizer_products.left_res]  at h
          simp only [← category.id_comp] at h
          have h' := h =≫ pi.π _ (i, j)
          rw [h']
          simp only [← category.assoc, ← limit.lift_π, ← fan.mk_π_app]
          rfl
          
        · dsimp'
          simp only [← category.id_comp, ← category.assoc]
          have h := c.π.naturality walking_parallel_pair_hom.right
          dsimp' [← sheaf_condition_equalizer_products.right_res]  at h
          simp only [← category.id_comp] at h
          have h' := h =≫ pi.π _ (j, i)
          rw [h']
          simp
          rfl
          
        · dsimp'
          erw [F.map_id]
          simp
           }

/-- Implementation of `sheaf_condition_pairwise_intersections.cone_equiv`. -/
@[simps]
def coneEquivInverse (F : Presheaf C X) ⦃ι : Type v⦄ (U : ι → Opens ↥X) :
    Limits.Cone (SheafConditionEqualizerProducts.diagram F U) ⥤ Limits.Cone ((diagram U).op ⋙ F) where
  obj := fun c => coneEquivInverseObj F U c
  map := fun c c' f =>
    { Hom := f.Hom,
      w' := by
        intro x
        induction x using Opposite.rec
        rcases x with (⟨i⟩ | ⟨i, j⟩)
        · dsimp'
          dunfold fork.ι
          rw [← f.w walking_parallel_pair.zero, category.assoc]
          
        · dsimp'
          rw [← f.w walking_parallel_pair.one, category.assoc]
           }

/-- Implementation of `sheaf_condition_pairwise_intersections.cone_equiv`. -/
@[simps]
def coneEquivUnitIsoApp (F : Presheaf C X) ⦃ι : Type v⦄ (U : ι → Opens ↥X) (c : Cone ((diagram U).op ⋙ F)) :
    (𝟭 (Cone ((diagram U).op ⋙ F))).obj c ≅ (coneEquivFunctor F U ⋙ coneEquivInverse F U).obj c where
  Hom :=
    { Hom := 𝟙 _,
      w' := fun j => by
        induction j using Opposite.rec
        rcases j with ⟨⟩ <;>
          · dsimp'
            simp only [← limits.fan.mk_π_app, ← category.id_comp, ← limits.limit.lift_π]
             }
  inv :=
    { Hom := 𝟙 _,
      w' := fun j => by
        induction j using Opposite.rec
        rcases j with ⟨⟩ <;>
          · dsimp'
            simp only [← limits.fan.mk_π_app, ← category.id_comp, ← limits.limit.lift_π]
             }
  hom_inv_id' := by
    ext
    simp only [← category.comp_id, ← limits.cone.category_comp_hom, ← limits.cone.category_id_hom]
  inv_hom_id' := by
    ext
    simp only [← category.comp_id, ← limits.cone.category_comp_hom, ← limits.cone.category_id_hom]

/-- Implementation of `sheaf_condition_pairwise_intersections.cone_equiv`. -/
@[simps]
def coneEquivUnitIso (F : Presheaf C X) ⦃ι : Type v⦄ (U : ι → Opens X) :
    𝟭 (Limits.Cone ((diagram U).op ⋙ F)) ≅ coneEquivFunctor F U ⋙ coneEquivInverse F U :=
  NatIso.ofComponents (coneEquivUnitIsoApp F U)
    (by
      tidy)

/-- Implementation of `sheaf_condition_pairwise_intersections.cone_equiv`. -/
@[simps]
def coneEquivCounitIso (F : Presheaf C X) ⦃ι : Type v⦄ (U : ι → Opens X) :
    coneEquivInverse F U ⋙ coneEquivFunctor F U ≅ 𝟭 (Limits.Cone (SheafConditionEqualizerProducts.diagram F U)) :=
  NatIso.ofComponents
    (fun c =>
      { Hom :=
          { Hom := 𝟙 _,
            w' := by
              rintro ⟨_ | _⟩
              · ext ⟨j⟩
                dsimp'
                simp only [← category.id_comp, ← limits.fan.mk_π_app, ← limits.limit.lift_π]
                
              · ext ⟨i, j⟩
                dsimp'
                simp only [← category.id_comp, ← limits.fan.mk_π_app, ← limits.limit.lift_π]
                 },
        inv :=
          { Hom := 𝟙 _,
            w' := by
              rintro ⟨_ | _⟩
              · ext ⟨j⟩
                dsimp'
                simp only [← category.id_comp, ← limits.fan.mk_π_app, ← limits.limit.lift_π]
                
              · ext ⟨i, j⟩
                dsimp'
                simp only [← category.id_comp, ← limits.fan.mk_π_app, ← limits.limit.lift_π]
                 },
        hom_inv_id' := by
          ext
          dsimp'
          simp only [← category.comp_id],
        inv_hom_id' := by
          ext
          dsimp'
          simp only [← category.comp_id] })
    fun c d f => by
    ext
    dsimp'
    simp only [← category.comp_id, ← category.id_comp]

/-- Cones over `diagram U ⋙ F` are the same as a cones over the usual sheaf condition equalizer diagram.
-/
@[simps]
def coneEquiv (F : Presheaf C X) ⦃ι : Type v⦄ (U : ι → Opens X) :
    Limits.Cone ((diagram U).op ⋙ F) ≌ Limits.Cone (SheafConditionEqualizerProducts.diagram F U) where
  Functor := coneEquivFunctor F U
  inverse := coneEquivInverse F U
  unitIso := coneEquivUnitIso F U
  counitIso := coneEquivCounitIso F U

attribute [local reducible] sheaf_condition_equalizer_products.res sheaf_condition_equalizer_products.left_res

/-- If `sheaf_condition_equalizer_products.fork` is an equalizer,
then `F.map_cone (cone U)` is a limit cone.
-/
def isLimitMapConeOfIsLimitSheafConditionFork (F : Presheaf C X) ⦃ι : Type v⦄ (U : ι → Opens X)
    (P : IsLimit (SheafConditionEqualizerProducts.fork F U)) : IsLimit (F.mapCone (cocone U).op) :=
  IsLimit.ofIsoLimit ((IsLimit.ofConeEquiv (coneEquiv F U).symm).symm P)
    { Hom :=
        { Hom := 𝟙 _,
          w' := by
            intro x
            induction x using Opposite.rec
            rcases x with ⟨⟩
            · dsimp'
              simp
              rfl
              
            · dsimp'
              simp only [← limit.lift_π, ← limit.lift_π_assoc, ← category.id_comp, ← fan.mk_π_app, ← category.assoc]
              rw [← F.map_comp]
              rfl
               },
      inv :=
        { Hom := 𝟙 _,
          w' := by
            intro x
            induction x using Opposite.rec
            rcases x with ⟨⟩
            · dsimp'
              simp
              rfl
              
            · dsimp'
              simp only [← limit.lift_π, ← limit.lift_π_assoc, ← category.id_comp, ← fan.mk_π_app, ← category.assoc]
              rw [← F.map_comp]
              rfl
               },
      hom_inv_id' := by
        ext
        dsimp'
        simp only [← category.comp_id],
      inv_hom_id' := by
        ext
        dsimp'
        simp only [← category.comp_id] }

/-- If `F.map_cone (cone U)` is a limit cone,
then `sheaf_condition_equalizer_products.fork` is an equalizer.
-/
def isLimitSheafConditionForkOfIsLimitMapCone (F : Presheaf C X) ⦃ι : Type v⦄ (U : ι → Opens X)
    (Q : IsLimit (F.mapCone (cocone U).op)) : IsLimit (SheafConditionEqualizerProducts.fork F U) :=
  IsLimit.ofIsoLimit ((IsLimit.ofConeEquiv (coneEquiv F U)).symm Q)
    { Hom :=
        { Hom := 𝟙 _,
          w' := by
            rintro ⟨⟩
            · dsimp'
              simp
              rfl
              
            · dsimp'
              ext ⟨i, j⟩
              simp only [← limit.lift_π, ← limit.lift_π_assoc, ← category.id_comp, ← fan.mk_π_app, ← category.assoc]
              rw [← F.map_comp]
              rfl
               },
      inv :=
        { Hom := 𝟙 _,
          w' := by
            rintro ⟨⟩
            · dsimp'
              simp
              rfl
              
            · dsimp'
              ext ⟨i, j⟩
              simp only [← limit.lift_π, ← limit.lift_π_assoc, ← category.id_comp, ← fan.mk_π_app, ← category.assoc]
              rw [← F.map_comp]
              rfl
               },
      hom_inv_id' := by
        ext
        dsimp'
        simp only [← category.comp_id],
      inv_hom_id' := by
        ext
        dsimp'
        simp only [← category.comp_id] }

end SheafConditionPairwiseIntersections

open SheafConditionPairwiseIntersections

/-- The sheaf condition in terms of an equalizer diagram is equivalent
to the reformulation in terms of a limit diagram over `U i` and `U i ⊓ U j`.
-/
theorem is_sheaf_iff_is_sheaf_pairwise_intersections (F : Presheaf C X) : F.IsSheaf ↔ F.IsSheafPairwiseIntersections :=
  Iff.intro (fun h ι U => ⟨isLimitMapConeOfIsLimitSheafConditionFork F U (h U).some⟩) fun h ι U =>
    ⟨isLimitSheafConditionForkOfIsLimitMapCone F U (h U).some⟩

/-- The sheaf condition in terms of an equalizer diagram is equivalent
to the reformulation in terms of the presheaf preserving the limit of the diagram
consisting of the `U i` and `U i ⊓ U j`.
-/
theorem is_sheaf_iff_is_sheaf_preserves_limit_pairwise_intersections (F : Presheaf C X) :
    F.IsSheaf ↔ F.IsSheafPreservesLimitPairwiseIntersections := by
  rw [is_sheaf_iff_is_sheaf_pairwise_intersections]
  constructor
  · intro h ι U
    exact ⟨preserves_limit_of_preserves_limit_cone (pairwise.cocone_is_colimit U).op (h U).some⟩
    
  · intro h ι U
    have := (h U).some
    exact ⟨preserves_limit.preserves (pairwise.cocone_is_colimit U).op⟩
    

end Top.Presheaf

namespace Top.Sheaf

variable {X : Top.{v}} {C : Type u} [Category.{v} C] [HasProducts.{v} C]

variable (F : X.Sheaf C) (U V : Opens X)

open CategoryTheory.Limits

/-- For a sheaf `F`, `F(U ∪ V)` is the pullback of `F(U) ⟶ F(U ∩ V)` and `F(V) ⟶ F(U ∩ V)`.
This is the pullback cone. -/
def interUnionPullbackCone :
    PullbackCone (F.1.map (homOfLe inf_le_left : U ∩ V ⟶ _).op) (F.1.map (homOfLe inf_le_right).op) :=
  PullbackCone.mk (F.1.map (homOfLe le_sup_left).op) (F.1.map (homOfLe le_sup_right).op)
    (by
      rw [← F.1.map_comp, ← F.1.map_comp]
      congr)

@[simp]
theorem inter_union_pullback_cone_X : (interUnionPullbackCone F U V).x = F.1.obj (op <| U ∪ V) :=
  rfl

@[simp]
theorem inter_union_pullback_cone_fst : (interUnionPullbackCone F U V).fst = F.1.map (homOfLe le_sup_left).op :=
  rfl

@[simp]
theorem inter_union_pullback_cone_snd : (interUnionPullbackCone F U V).snd = F.1.map (homOfLe le_sup_right).op :=
  rfl

variable (s : PullbackCone (F.1.map (homOfLe inf_le_left : U ∩ V ⟶ _).op) (F.1.map (homOfLe inf_le_right).op))

/-- (Implementation).
Every cone over `F(U) ⟶ F(U ∩ V)` and `F(V) ⟶ F(U ∩ V)` factors through `F(U ∪ V)`. -/
def interUnionPullbackConeLift : s.x ⟶ F.1.obj (op (U ∪ V)) := by
  let ι : ULift.{v} walking_pair → opens X := fun j => walking_pair.cases_on j.down U V
  have hι : U ∪ V = supr ι := by
    ext
    rw [opens.coe_supr, Set.mem_Union]
    constructor
    · rintro (h | h)
      exacts[⟨⟨walking_pair.left⟩, h⟩, ⟨⟨walking_pair.right⟩, h⟩]
      
    · rintro ⟨⟨_ | _⟩, h⟩
      exacts[Or.inl h, Or.inr h]
      
  refine'
    (F.1.is_sheaf_iff_is_sheaf_pairwise_intersections.mp F.2 ι).some.lift ⟨s.X, { app := _, naturality' := _ }⟩ ≫
      F.1.map (eq_to_hom hι).op
  · apply Opposite.rec
    rintro ((_ | _) | (_ | _))
    exacts[s.fst, s.snd, s.fst ≫ F.1.map (hom_of_le inf_le_left).op, s.snd ≫ F.1.map (hom_of_le inf_le_left).op]
    
  rintro i j f
  induction i using Opposite.rec
  induction j using Opposite.rec
  let g : j ⟶ i := f.unop
  have : f = g.op := rfl
  clear_value g
  subst this
  rcases i with (⟨⟨_ | _⟩⟩ | ⟨⟨_ | _⟩, ⟨_⟩⟩) <;>
    rcases j with (⟨⟨_ | _⟩⟩ | ⟨⟨_ | _⟩, ⟨_⟩⟩) <;>
      rcases g with ⟨⟩ <;>
        dsimp' <;> simp only [← category.id_comp, ← s.condition, ← CategoryTheory.Functor.map_id, ← category.comp_id]
  · rw [← cancel_mono (F.1.map (eq_to_hom <| inf_comm : U ∩ V ⟶ _).op), category.assoc, category.assoc]
    erw [← F.1.map_comp, ← F.1.map_comp]
    convert s.condition.symm
    
  · convert s.condition
    

theorem inter_union_pullback_cone_lift_left :
    interUnionPullbackConeLift F U V s ≫ F.1.map (homOfLe le_sup_left).op = s.fst := by
  erw [category.assoc, ← F.1.map_comp]
  exact
    (F.1.is_sheaf_iff_is_sheaf_pairwise_intersections.mp F.2 _).some.fac _
      (op <| pairwise.single (ULift.up walking_pair.left))

theorem inter_union_pullback_cone_lift_right :
    interUnionPullbackConeLift F U V s ≫ F.1.map (homOfLe le_sup_right).op = s.snd := by
  erw [category.assoc, ← F.1.map_comp]
  exact
    (F.1.is_sheaf_iff_is_sheaf_pairwise_intersections.mp F.2 _).some.fac _
      (op <| pairwise.single (ULift.up walking_pair.right))

/-- For a sheaf `F`, `F(U ∪ V)` is the pullback of `F(U) ⟶ F(U ∩ V)` and `F(V) ⟶ F(U ∩ V)`. -/
def isLimitPullbackCone : IsLimit (interUnionPullbackCone F U V) := by
  let ι : ULift.{v} walking_pair → opens X := fun ⟨j⟩ => walking_pair.cases_on j U V
  have hι : U ∪ V = supr ι := by
    ext
    rw [opens.coe_supr, Set.mem_Union]
    constructor
    · rintro (h | h)
      exacts[⟨⟨walking_pair.left⟩, h⟩, ⟨⟨walking_pair.right⟩, h⟩]
      
    · rintro ⟨⟨_ | _⟩, h⟩
      exacts[Or.inl h, Or.inr h]
      
  apply pullback_cone.is_limit_aux'
  intro s
  use inter_union_pullback_cone_lift F U V s
  refine' ⟨_, _, _⟩
  · apply inter_union_pullback_cone_lift_left
    
  · apply inter_union_pullback_cone_lift_right
    
  · intro m h₁ h₂
    rw [← cancel_mono (F.1.map (eq_to_hom hι.symm).op)]
    apply (F.1.is_sheaf_iff_is_sheaf_pairwise_intersections.mp F.2 ι).some.hom_ext
    apply Opposite.rec
    rintro ((_ | _) | (_ | _)) <;> rw [category.assoc, category.assoc]
    · erw [← F.1.map_comp]
      convert h₁
      apply inter_union_pullback_cone_lift_left
      
    · erw [← F.1.map_comp]
      convert h₂
      apply inter_union_pullback_cone_lift_right
      
    all_goals
      dsimp' only [← functor.op, ← pairwise.cocone_ι_app, ← functor.map_cone_π_app, ← cocone.op, ←
        pairwise.cocone_ι_app_2, ← unop_op, ← op_comp, ← nat_trans.op]
      simp_rw [F.1.map_comp, ← category.assoc]
      congr 1
      simp_rw [category.assoc, ← F.1.map_comp]
    · convert h₁
      apply inter_union_pullback_cone_lift_left
      
    · convert h₂
      apply inter_union_pullback_cone_lift_right
      
    

/-- If `U, V` are disjoint, then `F(U ∪ V) = F(U) × F(V)`. -/
def isProductOfDisjoint (h : U ∩ V = ⊥) :
    IsLimit (BinaryFan.mk (F.1.map (homOfLe le_sup_left : _ ⟶ U⊔V).op) (F.1.map (homOfLe le_sup_right : _ ⟶ U⊔V).op)) :=
  isProductOfIsTerminalIsPullback _ _ _ _ (F.isTerminalOfEqEmpty h) (isLimitPullbackCone F U V)

end Top.Sheaf

