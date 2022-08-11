/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Floris van Doorn
-/
import Mathbin.CategoryTheory.Limits.Shapes.FiniteProducts
import Mathbin.CategoryTheory.DiscreteCategory
import Mathbin.Tactic.EquivRw

/-!
# Limits in `C` give colimits in `Cᵒᵖ`.

We also give special cases for (co)products,
(co)equalizers, and pullbacks / pushouts.

-/


universe v₁ v₂ u₁ u₂

noncomputable section

open CategoryTheory

open CategoryTheory.Functor

open Opposite

namespace CategoryTheory.Limits

variable {C : Type u₁} [Category.{v₁} C]

variable {J : Type u₂} [Category.{v₂} J]

/-- Turn a colimit for `F : J ⥤ C` into a limit for `F.op : Jᵒᵖ ⥤ Cᵒᵖ`. -/
@[simps]
def isLimitCoconeOp (F : J ⥤ C) {c : Cocone F} (hc : IsColimit c) : IsLimit c.op where
  lift := fun s => (hc.desc s.unop).op
  fac' := fun s j =>
    Quiver.Hom.unop_inj
      (by
        simpa)
  uniq' := fun s m w => by
    refine' Quiver.Hom.unop_inj (hc.hom_ext fun j => Quiver.Hom.op_inj _)
    simpa only [← Quiver.Hom.unop_op, ← is_colimit.fac] using w (op j)

/-- Turn a limit for `F : J ⥤ C` into a colimit for `F.op : Jᵒᵖ ⥤ Cᵒᵖ`. -/
@[simps]
def isColimitConeOp (F : J ⥤ C) {c : Cone F} (hc : IsLimit c) : IsColimit c.op where
  desc := fun s => (hc.lift s.unop).op
  fac' := fun s j =>
    Quiver.Hom.unop_inj
      (by
        simpa)
  uniq' := fun s m w => by
    refine' Quiver.Hom.unop_inj (hc.hom_ext fun j => Quiver.Hom.op_inj _)
    simpa only [← Quiver.Hom.unop_op, ← is_limit.fac] using w (op j)

/-- Turn a colimit for `F : J ⥤ Cᵒᵖ` into a limit for `F.left_op : Jᵒᵖ ⥤ C`. -/
@[simps]
def isLimitConeLeftOpOfCocone (F : J ⥤ Cᵒᵖ) {c : Cocone F} (hc : IsColimit c) : IsLimit (coneLeftOpOfCocone c) where
  lift := fun s => (hc.desc (coconeOfConeLeftOp s)).unop
  fac' := fun s j =>
    Quiver.Hom.op_inj <| by
      simpa only [← cone_left_op_of_cocone_π_app, ← op_comp, ← Quiver.Hom.op_unop, ← is_colimit.fac, ←
        cocone_of_cone_left_op_ι_app]
  uniq' := fun s m w => by
    refine' Quiver.Hom.op_inj (hc.hom_ext fun j => Quiver.Hom.unop_inj _)
    simpa only [← Quiver.Hom.op_unop, ← is_colimit.fac, ← cocone_of_cone_left_op_ι_app] using w (op j)

/-- Turn a limit of `F : J ⥤ Cᵒᵖ` into a colimit of `F.left_op : Jᵒᵖ ⥤ C`. -/
@[simps]
def isColimitCoconeLeftOpOfCone (F : J ⥤ Cᵒᵖ) {c : Cone F} (hc : IsLimit c) : IsColimit (coconeLeftOpOfCone c) where
  desc := fun s => (hc.lift (coneOfCoconeLeftOp s)).unop
  fac' := fun s j =>
    Quiver.Hom.op_inj <| by
      simpa only [← cocone_left_op_of_cone_ι_app, ← op_comp, ← Quiver.Hom.op_unop, ← is_limit.fac, ←
        cone_of_cocone_left_op_π_app]
  uniq' := fun s m w => by
    refine' Quiver.Hom.op_inj (hc.hom_ext fun j => Quiver.Hom.unop_inj _)
    simpa only [← Quiver.Hom.op_unop, ← is_limit.fac, ← cone_of_cocone_left_op_π_app] using w (op j)

/-- Turn a colimit for `F : Jᵒᵖ ⥤ C` into a limit for `F.right_op : J ⥤ Cᵒᵖ`. -/
@[simps]
def isLimitConeRightOpOfCocone (F : Jᵒᵖ ⥤ C) {c : Cocone F} (hc : IsColimit c) : IsLimit (coneRightOpOfCocone c) where
  lift := fun s => (hc.desc (coconeOfConeRightOp s)).op
  fac' := fun s j =>
    Quiver.Hom.unop_inj
      (by
        simpa)
  uniq' := fun s m w => by
    refine' Quiver.Hom.unop_inj (hc.hom_ext fun j => Quiver.Hom.op_inj _)
    simpa only [← Quiver.Hom.unop_op, ← is_colimit.fac] using w (unop j)

/-- Turn a limit for `F : Jᵒᵖ ⥤ C` into a colimit for `F.right_op : J ⥤ Cᵒᵖ`. -/
@[simps]
def isColimitCoconeRightOpOfCone (F : Jᵒᵖ ⥤ C) {c : Cone F} (hc : IsLimit c) : IsColimit (coconeRightOpOfCone c) where
  desc := fun s => (hc.lift (coneOfCoconeRightOp s)).op
  fac' := fun s j =>
    Quiver.Hom.unop_inj
      (by
        simpa)
  uniq' := fun s m w => by
    refine' Quiver.Hom.unop_inj (hc.hom_ext fun j => Quiver.Hom.op_inj _)
    simpa only [← Quiver.Hom.unop_op, ← is_limit.fac] using w (unop j)

/-- Turn a colimit for `F : Jᵒᵖ ⥤ Cᵒᵖ` into a limit for `F.unop : J ⥤ C`. -/
@[simps]
def isLimitConeUnopOfCocone (F : Jᵒᵖ ⥤ Cᵒᵖ) {c : Cocone F} (hc : IsColimit c) : IsLimit (coneUnopOfCocone c) where
  lift := fun s => (hc.desc (coconeOfConeUnop s)).unop
  fac' := fun s j =>
    Quiver.Hom.op_inj
      (by
        simpa)
  uniq' := fun s m w => by
    refine' Quiver.Hom.op_inj (hc.hom_ext fun j => Quiver.Hom.unop_inj _)
    simpa only [← Quiver.Hom.op_unop, ← is_colimit.fac] using w (unop j)

/-- Turn a limit of `F : Jᵒᵖ ⥤ Cᵒᵖ` into a colimit of `F.unop : J ⥤ C`. -/
@[simps]
def isColimitCoconeUnopOfCone (F : Jᵒᵖ ⥤ Cᵒᵖ) {c : Cone F} (hc : IsLimit c) : IsColimit (coconeUnopOfCone c) where
  desc := fun s => (hc.lift (coneOfCoconeUnop s)).unop
  fac' := fun s j =>
    Quiver.Hom.op_inj
      (by
        simpa)
  uniq' := fun s m w => by
    refine' Quiver.Hom.op_inj (hc.hom_ext fun j => Quiver.Hom.unop_inj _)
    simpa only [← Quiver.Hom.op_unop, ← is_limit.fac] using w (unop j)

/-- Turn a colimit for `F.op : Jᵒᵖ ⥤ Cᵒᵖ` into a limit for `F : J ⥤ C`. -/
@[simps]
def isLimitCoconeUnop (F : J ⥤ C) {c : Cocone F.op} (hc : IsColimit c) : IsLimit c.unop where
  lift := fun s => (hc.desc s.op).unop
  fac' := fun s j =>
    Quiver.Hom.op_inj
      (by
        simpa)
  uniq' := fun s m w => by
    refine' Quiver.Hom.op_inj (hc.hom_ext fun j => Quiver.Hom.unop_inj _)
    simpa only [← Quiver.Hom.op_unop, ← is_colimit.fac] using w (unop j)

/-- Turn a limit for `F.op : Jᵒᵖ ⥤ Cᵒᵖ` into a colimit for `F : J ⥤ C`. -/
@[simps]
def isColimitConeUnop (F : J ⥤ C) {c : Cone F.op} (hc : IsLimit c) : IsColimit c.unop where
  desc := fun s => (hc.lift s.op).unop
  fac' := fun s j =>
    Quiver.Hom.op_inj
      (by
        simpa)
  uniq' := fun s m w => by
    refine' Quiver.Hom.op_inj (hc.hom_ext fun j => Quiver.Hom.unop_inj _)
    simpa only [← Quiver.Hom.op_unop, ← is_limit.fac] using w (unop j)

/-- Turn a colimit for `F.left_op : Jᵒᵖ ⥤ C` into a limit for `F : J ⥤ Cᵒᵖ`. -/
@[simps]
def isLimitConeOfCoconeLeftOp (F : J ⥤ Cᵒᵖ) {c : Cocone F.leftOp} (hc : IsColimit c) :
    IsLimit (coneOfCoconeLeftOp c) where
  lift := fun s => (hc.desc (coconeLeftOpOfCone s)).op
  fac' := fun s j =>
    Quiver.Hom.unop_inj <| by
      simpa only [← cone_of_cocone_left_op_π_app, ← unop_comp, ← Quiver.Hom.unop_op, ← is_colimit.fac, ←
        cocone_left_op_of_cone_ι_app]
  uniq' := fun s m w => by
    refine' Quiver.Hom.unop_inj (hc.hom_ext fun j => Quiver.Hom.op_inj _)
    simpa only [← Quiver.Hom.unop_op, ← is_colimit.fac, ← cone_of_cocone_left_op_π_app] using w (unop j)

/-- Turn a limit of `F.left_op : Jᵒᵖ ⥤ C` into a colimit of `F : J ⥤ Cᵒᵖ`. -/
@[simps]
def isColimitCoconeOfConeLeftOp (F : J ⥤ Cᵒᵖ) {c : Cone F.leftOp} (hc : IsLimit c) :
    IsColimit (coconeOfConeLeftOp c) where
  desc := fun s => (hc.lift (coneLeftOpOfCocone s)).op
  fac' := fun s j =>
    Quiver.Hom.unop_inj <| by
      simpa only [← cocone_of_cone_left_op_ι_app, ← unop_comp, ← Quiver.Hom.unop_op, ← is_limit.fac, ←
        cone_left_op_of_cocone_π_app]
  uniq' := fun s m w => by
    refine' Quiver.Hom.unop_inj (hc.hom_ext fun j => Quiver.Hom.op_inj _)
    simpa only [← Quiver.Hom.unop_op, ← is_limit.fac, ← cocone_of_cone_left_op_ι_app] using w (unop j)

/-- Turn a colimit for `F.right_op : J ⥤ Cᵒᵖ` into a limit for `F : Jᵒᵖ ⥤ C`. -/
@[simps]
def isLimitConeOfCoconeRightOp (F : Jᵒᵖ ⥤ C) {c : Cocone F.rightOp} (hc : IsColimit c) :
    IsLimit (coneOfCoconeRightOp c) where
  lift := fun s => (hc.desc (coconeRightOpOfCone s)).unop
  fac' := fun s j =>
    Quiver.Hom.op_inj
      (by
        simpa)
  uniq' := fun s m w => by
    refine' Quiver.Hom.op_inj (hc.hom_ext fun j => Quiver.Hom.unop_inj _)
    simpa only [← Quiver.Hom.op_unop, ← is_colimit.fac] using w (op j)

/-- Turn a limit for `F.right_op : J ⥤ Cᵒᵖ` into a limit for `F : Jᵒᵖ ⥤ C`. -/
@[simps]
def isColimitCoconeOfConeRightOp (F : Jᵒᵖ ⥤ C) {c : Cone F.rightOp} (hc : IsLimit c) :
    IsColimit (coconeOfConeRightOp c) where
  desc := fun s => (hc.lift (coneRightOpOfCocone s)).unop
  fac' := fun s j =>
    Quiver.Hom.op_inj
      (by
        simpa)
  uniq' := fun s m w => by
    refine' Quiver.Hom.op_inj (hc.hom_ext fun j => Quiver.Hom.unop_inj _)
    simpa only [← Quiver.Hom.op_unop, ← is_limit.fac] using w (op j)

/-- Turn a colimit for `F.unop : J ⥤ C` into a limit for `F : Jᵒᵖ ⥤ Cᵒᵖ`. -/
@[simps]
def isLimitConeOfCoconeUnop (F : Jᵒᵖ ⥤ Cᵒᵖ) {c : Cocone F.unop} (hc : IsColimit c) : IsLimit (coneOfCoconeUnop c) where
  lift := fun s => (hc.desc (coconeUnopOfCone s)).op
  fac' := fun s j =>
    Quiver.Hom.unop_inj
      (by
        simpa)
  uniq' := fun s m w => by
    refine' Quiver.Hom.unop_inj (hc.hom_ext fun j => Quiver.Hom.op_inj _)
    simpa only [← Quiver.Hom.unop_op, ← is_colimit.fac] using w (op j)

/-- Turn a limit for `F.unop : J ⥤ C` into a colimit for `F : Jᵒᵖ ⥤ Cᵒᵖ`. -/
@[simps]
def isColimitConeOfCoconeUnop (F : Jᵒᵖ ⥤ Cᵒᵖ) {c : Cone F.unop} (hc : IsLimit c) : IsColimit (coconeOfConeUnop c) where
  desc := fun s => (hc.lift (coneUnopOfCocone s)).op
  fac' := fun s j =>
    Quiver.Hom.unop_inj
      (by
        simpa)
  uniq' := fun s m w => by
    refine' Quiver.Hom.unop_inj (hc.hom_ext fun j => Quiver.Hom.op_inj _)
    simpa only [← Quiver.Hom.unop_op, ← is_limit.fac] using w (op j)

/-- If `F.left_op : Jᵒᵖ ⥤ C` has a colimit, we can construct a limit for `F : J ⥤ Cᵒᵖ`.
-/
theorem has_limit_of_has_colimit_left_op (F : J ⥤ Cᵒᵖ) [HasColimit F.leftOp] : HasLimit F :=
  HasLimit.mk
    { Cone := coneOfCoconeLeftOp (Colimit.cocone F.leftOp),
      IsLimit := isLimitConeOfCoconeLeftOp _ (colimit.isColimit _) }

/-- If `C` has colimits of shape `Jᵒᵖ`, we can construct limits in `Cᵒᵖ` of shape `J`.
-/
theorem has_limits_of_shape_op_of_has_colimits_of_shape [HasColimitsOfShape Jᵒᵖ C] : HasLimitsOfShape J Cᵒᵖ :=
  { HasLimit := fun F => has_limit_of_has_colimit_left_op F }

attribute [local instance] has_limits_of_shape_op_of_has_colimits_of_shape

/-- If `C` has colimits, we can construct limits for `Cᵒᵖ`.
-/
theorem has_limits_op_of_has_colimits [HasColimits C] : HasLimits Cᵒᵖ :=
  ⟨inferInstance⟩

/-- If `F.left_op : Jᵒᵖ ⥤ C` has a limit, we can construct a colimit for `F : J ⥤ Cᵒᵖ`.
-/
theorem has_colimit_of_has_limit_left_op (F : J ⥤ Cᵒᵖ) [HasLimit F.leftOp] : HasColimit F :=
  HasColimit.mk
    { Cocone := coconeOfConeLeftOp (Limit.cone F.leftOp), IsColimit := isColimitCoconeOfConeLeftOp _ (limit.isLimit _) }

/-- If `C` has colimits of shape `Jᵒᵖ`, we can construct limits in `Cᵒᵖ` of shape `J`.
-/
theorem has_colimits_of_shape_op_of_has_limits_of_shape [HasLimitsOfShape Jᵒᵖ C] : HasColimitsOfShape J Cᵒᵖ :=
  { HasColimit := fun F => has_colimit_of_has_limit_left_op F }

attribute [local instance] has_colimits_of_shape_op_of_has_limits_of_shape

/-- If `C` has limits, we can construct colimits for `Cᵒᵖ`.
-/
theorem has_colimits_op_of_has_limits [HasLimits C] : HasColimits Cᵒᵖ :=
  ⟨inferInstance⟩

variable (X : Type v₁)

/-- If `C` has products indexed by `X`, then `Cᵒᵖ` has coproducts indexed by `X`.
-/
theorem has_coproducts_opposite [HasProductsOfShape X C] : HasCoproductsOfShape X Cᵒᵖ := by
  have : has_limits_of_shape (discrete X)ᵒᵖ C := has_limits_of_shape_of_equivalence (discrete.opposite X).symm
  infer_instance

/-- If `C` has coproducts indexed by `X`, then `Cᵒᵖ` has products indexed by `X`.
-/
theorem has_products_opposite [HasCoproductsOfShape X C] : HasProductsOfShape X Cᵒᵖ := by
  have : has_colimits_of_shape (discrete X)ᵒᵖ C := has_colimits_of_shape_of_equivalence (discrete.opposite X).symm
  infer_instance

theorem has_finite_coproducts_opposite [HasFiniteProducts C] : HasFiniteCoproducts Cᵒᵖ :=
  { out := fun J 𝒟 => by
      skip
      have : has_limits_of_shape (discrete J)ᵒᵖ C := has_limits_of_shape_of_equivalence (discrete.opposite J).symm
      infer_instance }

theorem has_finite_products_opposite [HasFiniteCoproducts C] : HasFiniteProducts Cᵒᵖ :=
  { out := fun J 𝒟 => by
      skip
      have : has_colimits_of_shape (discrete J)ᵒᵖ C := has_colimits_of_shape_of_equivalence (discrete.opposite J).symm
      infer_instance }

theorem has_equalizers_opposite [HasCoequalizers C] : HasEqualizers Cᵒᵖ := by
  have : has_colimits_of_shape walking_parallel_pairᵒᵖ C :=
    has_colimits_of_shape_of_equivalence walking_parallel_pair_op_equiv
  infer_instance

theorem has_coequalizers_opposite [HasEqualizers C] : HasCoequalizers Cᵒᵖ := by
  have : has_limits_of_shape walking_parallel_pairᵒᵖ C :=
    has_limits_of_shape_of_equivalence walking_parallel_pair_op_equiv
  infer_instance

theorem has_finite_colimits_opposite [HasFiniteLimits C] : HasFiniteColimits Cᵒᵖ :=
  { out := fun J 𝒟 𝒥 => by
      skip
      infer_instance }

theorem has_finite_limits_opposite [HasFiniteColimits C] : HasFiniteLimits Cᵒᵖ :=
  { out := fun J 𝒟 𝒥 => by
      skip
      infer_instance }

theorem has_pullbacks_opposite [HasPushouts C] : HasPullbacks Cᵒᵖ := by
  have : has_colimits_of_shape walking_cospanᵒᵖ C := has_colimits_of_shape_of_equivalence walking_cospan_op_equiv.symm
  apply has_limits_of_shape_op_of_has_colimits_of_shape

theorem has_pushouts_opposite [HasPullbacks C] : HasPushouts Cᵒᵖ := by
  have : has_limits_of_shape walking_spanᵒᵖ C := has_limits_of_shape_of_equivalence walking_span_op_equiv.symm
  apply has_colimits_of_shape_op_of_has_limits_of_shape

/-- The canonical isomorphism relating `span f.op g.op` and `(cospan f g).op` -/
@[simps]
def spanOp {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) : span f.op g.op ≅ walkingCospanOpEquiv.inverse ⋙ (cospan f g).op :=
  NatIso.ofComponents
    (by
      rintro (_ | _ | _) <;> rfl)
    (by
      rintro (_ | _ | _) (_ | _ | _) f <;> cases f <;> tidy)

/-- The canonical isomorphism relating `(cospan f g).op` and `span f.op g.op` -/
@[simps]
def opCospan {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) : (cospan f g).op ≅ walkingCospanOpEquiv.Functor ⋙ span f.op g.op :=
  calc
    (cospan f g).op ≅ 𝟭 _ ⋙ (cospan f g).op := by
      rfl
    _ ≅ (walkingCospanOpEquiv.Functor ⋙ walkingCospanOpEquiv.inverse) ⋙ (cospan f g).op :=
      isoWhiskerRight walkingCospanOpEquiv.unitIso _
    _ ≅ walkingCospanOpEquiv.Functor ⋙ walkingCospanOpEquiv.inverse ⋙ (cospan f g).op := Functor.associator _ _ _
    _ ≅ walkingCospanOpEquiv.Functor ⋙ span f.op g.op := isoWhiskerLeft _ (spanOp f g).symm
    

/-- The canonical isomorphism relating `cospan f.op g.op` and `(span f g).op` -/
@[simps]
def cospanOp {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) : cospan f.op g.op ≅ walkingSpanOpEquiv.inverse ⋙ (span f g).op :=
  NatIso.ofComponents
    (by
      rintro (_ | _ | _) <;> rfl)
    (by
      rintro (_ | _ | _) (_ | _ | _) f <;> cases f <;> tidy)

/-- The canonical isomorphism relating `(span f g).op` and `cospan f.op g.op` -/
@[simps]
def opSpan {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) : (span f g).op ≅ walkingSpanOpEquiv.Functor ⋙ cospan f.op g.op :=
  calc
    (span f g).op ≅ 𝟭 _ ⋙ (span f g).op := by
      rfl
    _ ≅ (walkingSpanOpEquiv.Functor ⋙ walkingSpanOpEquiv.inverse) ⋙ (span f g).op :=
      isoWhiskerRight walkingSpanOpEquiv.unitIso _
    _ ≅ walkingSpanOpEquiv.Functor ⋙ walkingSpanOpEquiv.inverse ⋙ (span f g).op := Functor.associator _ _ _
    _ ≅ walkingSpanOpEquiv.Functor ⋙ cospan f.op g.op := isoWhiskerLeft _ (cospanOp f g).symm
    

namespace PushoutCocone

/-- The obvious map `pushout_cocone f g → pullback_cone f.unop g.unop` -/
@[simps]
def unop {X Y Z : Cᵒᵖ} {f : X ⟶ Y} {g : X ⟶ Z} (c : PushoutCocone f g) : PullbackCone f.unop g.unop :=
  Cocone.unop ((Cocones.precompose (opCospan f.unop g.unop).Hom).obj (Cocone.whisker walkingCospanOpEquiv.Functor c))

@[simp]
theorem unop_fst {X Y Z : Cᵒᵖ} {f : X ⟶ Y} {g : X ⟶ Z} (c : PushoutCocone f g) : c.unop.fst = c.inl.unop := by
  change (_ : limits.cone _).π.app _ = _
  tidy

@[simp]
theorem unop_snd {X Y Z : Cᵒᵖ} {f : X ⟶ Y} {g : X ⟶ Z} (c : PushoutCocone f g) : c.unop.snd = c.inr.unop := by
  change (_ : limits.cone _).π.app _ = _
  tidy

/-- The obvious map `pushout_cocone f.op g.op → pullback_cone f g` -/
@[simps]
def op {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} (c : PushoutCocone f g) : PullbackCone f.op g.op :=
  (Cones.postcompose (cospanOp f g).symm.Hom).obj (Cone.whisker walkingSpanOpEquiv.inverse (Cocone.op c))

@[simp]
theorem op_fst {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} (c : PushoutCocone f g) : c.op.fst = c.inl.op := by
  change (_ : limits.cone _).π.app _ = _
  apply category.comp_id

@[simp]
theorem op_snd {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} (c : PushoutCocone f g) : c.op.snd = c.inr.op := by
  change (_ : limits.cone _).π.app _ = _
  apply category.comp_id

end PushoutCocone

namespace PullbackCone

/-- The obvious map `pullback_cone f g → pushout_cocone f.unop g.unop` -/
@[simps]
def unop {X Y Z : Cᵒᵖ} {f : X ⟶ Z} {g : Y ⟶ Z} (c : PullbackCone f g) : PushoutCocone f.unop g.unop :=
  Cone.unop ((Cones.postcompose (opSpan f.unop g.unop).symm.Hom).obj (Cone.whisker walkingSpanOpEquiv.Functor c))

@[simp]
theorem unop_inl {X Y Z : Cᵒᵖ} {f : X ⟶ Z} {g : Y ⟶ Z} (c : PullbackCone f g) : c.unop.inl = c.fst.unop := by
  change (_ : limits.cocone _).ι.app _ = _
  dsimp' only [← unop, ← op_span]
  simp
  dsimp'
  simp
  dsimp'
  simp

@[simp]
theorem unop_inr {X Y Z : Cᵒᵖ} {f : X ⟶ Z} {g : Y ⟶ Z} (c : PullbackCone f g) : c.unop.inr = c.snd.unop := by
  change (_ : limits.cocone _).ι.app _ = _
  apply Quiver.Hom.op_inj
  dsimp'
  simp
  dsimp'
  simp
  apply category.comp_id

/-- The obvious map `pullback_cone f g → pushout_cocone f.op g.op` -/
@[simps]
def op {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} (c : PullbackCone f g) : PushoutCocone f.op g.op :=
  (Cocones.precompose (spanOp f g).Hom).obj (Cocone.whisker walkingCospanOpEquiv.inverse (Cone.op c))

@[simp]
theorem op_inl {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} (c : PullbackCone f g) : c.op.inl = c.fst.op := by
  change (_ : limits.cocone _).ι.app _ = _
  apply category.id_comp

@[simp]
theorem op_inr {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} (c : PullbackCone f g) : c.op.inr = c.snd.op := by
  change (_ : limits.cocone _).ι.app _ = _
  apply category.id_comp

/-- If `c` is a pullback cone, then `c.op.unop` is isomorphic to `c`. -/
def opUnop {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} (c : PullbackCone f g) : c.op.unop ≅ c :=
  PullbackCone.ext (Iso.refl _)
    (by
      simp )
    (by
      simp )

/-- If `c` is a pullback cone in `Cᵒᵖ`, then `c.unop.op` is isomorphic to `c`. -/
def unopOp {X Y Z : Cᵒᵖ} {f : X ⟶ Z} {g : Y ⟶ Z} (c : PullbackCone f g) : c.unop.op ≅ c :=
  PullbackCone.ext (Iso.refl _)
    (by
      simp )
    (by
      simp )

end PullbackCone

namespace PushoutCocone

/-- If `c` is a pushout cocone, then `c.op.unop` is isomorphic to `c`. -/
def opUnop {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} (c : PushoutCocone f g) : c.op.unop ≅ c :=
  PushoutCocone.ext (Iso.refl _)
    (by
      simp )
    (by
      simp )

/-- If `c` is a pushout cocone in `Cᵒᵖ`, then `c.unop.op` is isomorphic to `c`. -/
def unopOp {X Y Z : Cᵒᵖ} {f : X ⟶ Y} {g : X ⟶ Z} (c : PushoutCocone f g) : c.unop.op ≅ c :=
  PushoutCocone.ext (Iso.refl _)
    (by
      simp )
    (by
      simp )

/-- A pushout cone is a colimit cocone if and only if the corresponding pullback cone
in the opposite category is a limit cone. -/
def isColimitEquivIsLimitOp {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} (c : PushoutCocone f g) : IsColimit c ≃ IsLimit c.op :=
  by
  apply equivOfSubsingletonOfSubsingleton
  · intro h
    equiv_rw is_limit.postcompose_hom_equiv _ _
    equiv_rw(is_limit.whisker_equivalence_equiv walking_span_op_equiv.symm).symm
    exact is_limit_cocone_op _ h
    
  · intro h
    equiv_rw is_colimit.equiv_iso_colimit c.op_unop.symm
    apply is_colimit_cone_unop
    equiv_rw is_limit.postcompose_hom_equiv _ _
    equiv_rw(is_limit.whisker_equivalence_equiv _).symm
    exact h
    

/-- A pushout cone is a colimit cocone in `Cᵒᵖ` if and only if the corresponding pullback cone
in `C` is a limit cone. -/
def isColimitEquivIsLimitUnop {X Y Z : Cᵒᵖ} {f : X ⟶ Y} {g : X ⟶ Z} (c : PushoutCocone f g) :
    IsColimit c ≃ IsLimit c.unop := by
  apply equivOfSubsingletonOfSubsingleton
  · intro h
    apply is_limit_cocone_unop
    equiv_rw is_colimit.precompose_hom_equiv _ _
    equiv_rw(is_colimit.whisker_equivalence_equiv _).symm
    exact h
    
  · intro h
    equiv_rw is_colimit.equiv_iso_colimit c.unop_op.symm
    equiv_rw is_colimit.precompose_hom_equiv _ _
    equiv_rw(is_colimit.whisker_equivalence_equiv walking_cospan_op_equiv.symm).symm
    exact is_colimit_cone_op _ h
    

end PushoutCocone

namespace PullbackCone

/-- A pullback cone is a limit cone if and only if the corresponding pushout cocone
in the opposite category is a colimit cocone. -/
def isLimitEquivIsColimitOp {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} (c : PullbackCone f g) : IsLimit c ≃ IsColimit c.op :=
  (IsLimit.equivIsoLimit c.op_unop).symm.trans c.op.isColimitEquivIsLimitUnop.symm

/-- A pullback cone is a limit cone in `Cᵒᵖ` if and only if the corresponding pushout cocone
in `C` is a colimit cocone. -/
def isLimitEquivIsColimitUnop {X Y Z : Cᵒᵖ} {f : X ⟶ Z} {g : Y ⟶ Z} (c : PullbackCone f g) :
    IsLimit c ≃ IsColimit c.unop :=
  (IsLimit.equivIsoLimit c.unop_op).symm.trans c.unop.isColimitEquivIsLimitOp.symm

end PullbackCone

end CategoryTheory.Limits

