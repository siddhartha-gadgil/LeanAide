/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Thomas Read, Andrew Yang
-/
import Mathbin.CategoryTheory.Adjunction.Basic
import Mathbin.CategoryTheory.Yoneda
import Mathbin.CategoryTheory.Opposites

/-!
# Opposite adjunctions

This file contains constructions to relate adjunctions of functors to adjunctions of their
opposites.
These constructions are used to show uniqueness of adjoints (up to natural isomorphism).

## Tags
adjunction, opposite, uniqueness
-/


open CategoryTheory

universe v₁ v₂ u₁ u₂

-- morphism levels before object levels. See note [category_theory universes].
variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

namespace CategoryTheory.Adjunction

/-- If `G.op` is adjoint to `F.op` then `F` is adjoint to `G`. -/
@[simps]
def adjointOfOpAdjointOp (F : C ⥤ D) (G : D ⥤ C) (h : G.op ⊣ F.op) : F ⊣ G :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y =>
        ((h.homEquiv (Opposite.op Y) (Opposite.op X)).trans (opEquiv _ _)).symm.trans (opEquiv _ _) }

/-- If `G` is adjoint to `F.op` then `F` is adjoint to `G.unop`. -/
def adjointUnopOfAdjointOp (F : C ⥤ D) (G : Dᵒᵖ ⥤ Cᵒᵖ) (h : G ⊣ F.op) : F ⊣ G.unop :=
  adjointOfOpAdjointOp F G.unop (h.ofNatIsoLeft G.opUnopIso.symm)

/-- If `G.op` is adjoint to `F` then `F.unop` is adjoint to `G`. -/
def unopAdjointOfOpAdjoint (F : Cᵒᵖ ⥤ Dᵒᵖ) (G : D ⥤ C) (h : G.op ⊣ F) : F.unop ⊣ G :=
  adjointOfOpAdjointOp _ _ (h.ofNatIsoRight F.opUnopIso.symm)

/-- If `G` is adjoint to `F` then `F.unop` is adjoint to `G.unop`. -/
def unopAdjointUnopOfAdjoint (F : Cᵒᵖ ⥤ Dᵒᵖ) (G : Dᵒᵖ ⥤ Cᵒᵖ) (h : G ⊣ F) : F.unop ⊣ G.unop :=
  adjointUnopOfAdjointOp F.unop G (h.ofNatIsoRight F.opUnopIso.symm)

/-- If `G` is adjoint to `F` then `F.op` is adjoint to `G.op`. -/
@[simps]
def opAdjointOpOfAdjoint (F : C ⥤ D) (G : D ⥤ C) (h : G ⊣ F) : F.op ⊣ G.op :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y => (opEquiv _ Y).trans ((h.homEquiv _ _).symm.trans (opEquiv X (Opposite.op _)).symm) }

/-- If `G` is adjoint to `F.unop` then `F` is adjoint to `G.op`. -/
def adjointOpOfAdjointUnop (F : Cᵒᵖ ⥤ Dᵒᵖ) (G : D ⥤ C) (h : G ⊣ F.unop) : F ⊣ G.op :=
  (opAdjointOpOfAdjoint F.unop _ h).ofNatIsoLeft F.opUnopIso

/-- If `G.unop` is adjoint to `F` then `F.op` is adjoint to `G`. -/
def opAdjointOfUnopAdjoint (F : C ⥤ D) (G : Dᵒᵖ ⥤ Cᵒᵖ) (h : G.unop ⊣ F) : F.op ⊣ G :=
  (opAdjointOpOfAdjoint _ G.unop h).ofNatIsoRight G.opUnopIso

/-- If `G.unop` is adjoint to `F.unop` then `F` is adjoint to `G`. -/
def adjointOfUnopAdjointUnop (F : Cᵒᵖ ⥤ Dᵒᵖ) (G : Dᵒᵖ ⥤ Cᵒᵖ) (h : G.unop ⊣ F.unop) : F ⊣ G :=
  (adjointOpOfAdjointUnop _ _ h).ofNatIsoRight G.opUnopIso

/-- If `F` and `F'` are both adjoint to `G`, there is a natural isomorphism
`F.op ⋙ coyoneda ≅ F'.op ⋙ coyoneda`.
We use this in combination with `fully_faithful_cancel_right` to show left adjoints are unique.
-/
def leftAdjointsCoyonedaEquiv {F F' : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F' ⊣ G) :
    F.op ⋙ coyoneda ≅ F'.op ⋙ coyoneda :=
  NatIso.ofComponents
    (fun X =>
      NatIso.ofComponents (fun Y => ((adj1.homEquiv X.unop Y).trans (adj2.homEquiv X.unop Y).symm).toIso)
        (by
          tidy))
    (by
      tidy)

/-- If `F` and `F'` are both left adjoint to `G`, then they are naturally isomorphic. -/
def leftAdjointUniq {F F' : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F' ⊣ G) : F ≅ F' :=
  NatIso.removeOp (fullyFaithfulCancelRight _ (leftAdjointsCoyonedaEquiv adj2 adj1))

@[simp]
theorem hom_equiv_left_adjoint_uniq_hom_app {F F' : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F' ⊣ G) (x : C) :
    adj1.homEquiv _ _ ((leftAdjointUniq adj1 adj2).Hom.app x) = adj2.Unit.app x := by
  apply (adj1.hom_equiv _ _).symm.Injective
  apply Quiver.Hom.op_inj
  apply coyoneda.map_injective
  swap
  infer_instance
  ext f y
  simpa [← left_adjoint_uniq, ← left_adjoints_coyoneda_equiv]

@[simp, reassoc]
theorem unit_left_adjoint_uniq_hom {F F' : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F' ⊣ G) :
    adj1.Unit ≫ whiskerRight (leftAdjointUniq adj1 adj2).Hom G = adj2.Unit := by
  ext x
  rw [nat_trans.comp_app, ← hom_equiv_left_adjoint_uniq_hom_app adj1 adj2]
  simp [-hom_equiv_left_adjoint_uniq_hom_app, G.map_comp]

@[simp, reassoc]
theorem unit_left_adjoint_uniq_hom_app {F F' : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F' ⊣ G) (x : C) :
    adj1.Unit.app x ≫ G.map ((leftAdjointUniq adj1 adj2).Hom.app x) = adj2.Unit.app x := by
  rw [← unit_left_adjoint_uniq_hom adj1 adj2]
  rfl

@[simp, reassoc]
theorem left_adjoint_uniq_hom_counit {F F' : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F' ⊣ G) :
    whiskerLeft G (leftAdjointUniq adj1 adj2).Hom ≫ adj2.counit = adj1.counit := by
  ext x
  apply Quiver.Hom.op_inj
  apply coyoneda.map_injective
  swap
  infer_instance
  ext y f
  have :
    F.map (adj2.unit.app (G.obj x)) ≫ adj1.counit.app (F'.obj (G.obj x)) ≫ adj2.counit.app x ≫ f =
      adj1.counit.app x ≫ f :=
    by
    erw [← adj1.counit.naturality, ← F.map_comp_assoc]
    simpa
  simpa [← left_adjoint_uniq, ← left_adjoints_coyoneda_equiv] using this

@[simp, reassoc]
theorem left_adjoint_uniq_hom_app_counit {F F' : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F' ⊣ G) (x : D) :
    (leftAdjointUniq adj1 adj2).Hom.app (G.obj x) ≫ adj2.counit.app x = adj1.counit.app x := by
  rw [← left_adjoint_uniq_hom_counit adj1 adj2]
  rfl

@[simp]
theorem left_adjoint_uniq_inv_app {F F' : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F' ⊣ G) (x : C) :
    (leftAdjointUniq adj1 adj2).inv.app x = (leftAdjointUniq adj2 adj1).Hom.app x :=
  rfl

@[simp, reassoc]
theorem left_adjoint_uniq_trans {F F' F'' : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F' ⊣ G) (adj3 : F'' ⊣ G) :
    (leftAdjointUniq adj1 adj2).Hom ≫ (leftAdjointUniq adj2 adj3).Hom = (leftAdjointUniq adj1 adj3).Hom := by
  ext
  apply Quiver.Hom.op_inj
  apply coyoneda.map_injective
  swap
  infer_instance
  ext
  simp [← left_adjoints_coyoneda_equiv, ← left_adjoint_uniq]

@[simp, reassoc]
theorem left_adjoint_uniq_trans_app {F F' F'' : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F' ⊣ G) (adj3 : F'' ⊣ G)
    (x : C) :
    (leftAdjointUniq adj1 adj2).Hom.app x ≫ (leftAdjointUniq adj2 adj3).Hom.app x =
      (leftAdjointUniq adj1 adj3).Hom.app x :=
  by
  rw [← left_adjoint_uniq_trans adj1 adj2 adj3]
  rfl

@[simp]
theorem left_adjoint_uniq_refl {F : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G) : (leftAdjointUniq adj1 adj1).Hom = 𝟙 _ := by
  ext
  apply Quiver.Hom.op_inj
  apply coyoneda.map_injective
  swap
  infer_instance
  ext
  simp [← left_adjoints_coyoneda_equiv, ← left_adjoint_uniq]

/-- If `G` and `G'` are both right adjoint to `F`, then they are naturally isomorphic. -/
def rightAdjointUniq {F : C ⥤ D} {G G' : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F ⊣ G') : G ≅ G' :=
  NatIso.removeOp (leftAdjointUniq (opAdjointOpOfAdjoint _ F adj2) (opAdjointOpOfAdjoint _ _ adj1))

@[simp]
theorem hom_equiv_symm_right_adjoint_uniq_hom_app {F : C ⥤ D} {G G' : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F ⊣ G') (x : D) :
    (adj2.homEquiv _ _).symm ((rightAdjointUniq adj1 adj2).Hom.app x) = adj1.counit.app x := by
  apply Quiver.Hom.op_inj
  convert
    hom_equiv_left_adjoint_uniq_hom_app (op_adjoint_op_of_adjoint _ F adj2) (op_adjoint_op_of_adjoint _ _ adj1)
      (Opposite.op x)
  simpa

@[simp, reassoc]
theorem unit_right_adjoint_uniq_hom_app {F : C ⥤ D} {G G' : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F ⊣ G') (x : C) :
    adj1.Unit.app x ≫ (rightAdjointUniq adj1 adj2).Hom.app (F.obj x) = adj2.Unit.app x := by
  apply Quiver.Hom.op_inj
  convert
    left_adjoint_uniq_hom_app_counit (op_adjoint_op_of_adjoint _ _ adj2) (op_adjoint_op_of_adjoint _ _ adj1)
      (Opposite.op x)
  all_goals
    simpa

@[simp, reassoc]
theorem unit_right_adjoint_uniq_hom {F : C ⥤ D} {G G' : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F ⊣ G') :
    adj1.Unit ≫ whiskerLeft F (rightAdjointUniq adj1 adj2).Hom = adj2.Unit := by
  ext x
  simp

@[simp, reassoc]
theorem right_adjoint_uniq_hom_app_counit {F : C ⥤ D} {G G' : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F ⊣ G') (x : D) :
    F.map ((rightAdjointUniq adj1 adj2).Hom.app x) ≫ adj2.counit.app x = adj1.counit.app x := by
  apply Quiver.Hom.op_inj
  convert
    unit_left_adjoint_uniq_hom_app (op_adjoint_op_of_adjoint _ _ adj2) (op_adjoint_op_of_adjoint _ _ adj1)
      (Opposite.op x)
  all_goals
    simpa

@[simp, reassoc]
theorem right_adjoint_uniq_hom_counit {F : C ⥤ D} {G G' : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F ⊣ G') :
    whiskerRight (rightAdjointUniq adj1 adj2).Hom F ≫ adj2.counit = adj1.counit := by
  ext
  simp

@[simp]
theorem right_adjoint_uniq_inv_app {F : C ⥤ D} {G G' : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F ⊣ G') (x : D) :
    (rightAdjointUniq adj1 adj2).inv.app x = (rightAdjointUniq adj2 adj1).Hom.app x :=
  rfl

@[simp, reassoc]
theorem right_adjoint_uniq_trans_app {F : C ⥤ D} {G G' G'' : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F ⊣ G') (adj3 : F ⊣ G'')
    (x : D) :
    (rightAdjointUniq adj1 adj2).Hom.app x ≫ (rightAdjointUniq adj2 adj3).Hom.app x =
      (rightAdjointUniq adj1 adj3).Hom.app x :=
  by
  apply Quiver.Hom.op_inj
  exact
    left_adjoint_uniq_trans_app (op_adjoint_op_of_adjoint _ _ adj3) (op_adjoint_op_of_adjoint _ _ adj2)
      (op_adjoint_op_of_adjoint _ _ adj1) (Opposite.op x)

@[simp, reassoc]
theorem right_adjoint_uniq_trans {F : C ⥤ D} {G G' G'' : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F ⊣ G') (adj3 : F ⊣ G'') :
    (rightAdjointUniq adj1 adj2).Hom ≫ (rightAdjointUniq adj2 adj3).Hom = (rightAdjointUniq adj1 adj3).Hom := by
  ext
  simp

@[simp]
theorem right_adjoint_uniq_refl {F : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G) : (rightAdjointUniq adj1 adj1).Hom = 𝟙 _ := by
  delta' right_adjoint_uniq
  simp

/-- Given two adjunctions, if the left adjoints are naturally isomorphic, then so are the right
adjoints.
-/
def natIsoOfLeftAdjointNatIso {F F' : C ⥤ D} {G G' : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F' ⊣ G') (l : F ≅ F') : G ≅ G' :=
  rightAdjointUniq adj1 (adj2.ofNatIsoLeft l.symm)

/-- Given two adjunctions, if the right adjoints are naturally isomorphic, then so are the left
adjoints.
-/
def natIsoOfRightAdjointNatIso {F F' : C ⥤ D} {G G' : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F' ⊣ G') (r : G ≅ G') : F ≅ F' :=
  leftAdjointUniq adj1 (adj2.ofNatIsoRight r.symm)

end CategoryTheory.Adjunction

