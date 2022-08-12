/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import Mathbin.AlgebraicTopology.SimplicialObject
import Mathbin.CategoryTheory.Limits.Shapes.WidePullbacks
import Mathbin.CategoryTheory.Arrow

/-!

# The Čech Nerve

This file provides a definition of the Čech nerve associated to an arrow, provided
the base category has the correct wide pullbacks.

Several variants are provided, given `f : arrow C`:
1. `f.cech_nerve` is the Čech nerve, considered as a simplicial object in `C`.
2. `f.augmented_cech_nerve` is the augmented Čech nerve, considered as an
  augmented simplicial object in `C`.
3. `simplicial_object.cech_nerve` and `simplicial_object.augmented_cech_nerve` are
  functorial versions of 1 resp. 2.

-/


open CategoryTheory

open CategoryTheory.Limits

noncomputable section

universe v u

variable {C : Type u} [Category.{v} C]

namespace CategoryTheory.Arrow

variable (f : Arrow C)

variable [∀ n : ℕ, HasWidePullback.{0} f.right (fun i : Finₓ (n + 1) => f.left) fun i => f.Hom]

/-- The Čech nerve associated to an arrow. -/
@[simps]
def cechNerve : SimplicialObject C where
  obj := fun n => widePullback.{0} f.right (fun i : Finₓ (n.unop.len + 1) => f.left) fun i => f.Hom
  map := fun m n g =>
    (widePullback.lift (widePullback.base _) fun i => (widePullback.π fun i => f.Hom) <| g.unop.toOrderHom i) fun j =>
      by
      simp
  map_id' := fun x => by
    ext ⟨⟩
    · simpa
      
    · simp
      
  map_comp' := fun x y z f g => by
    ext ⟨⟩
    · simpa
      
    · simp
      

/-- The morphism between Čech nerves associated to a morphism of arrows. -/
@[simps]
def mapCechNerve {f g : Arrow C} [∀ n : ℕ, HasWidePullback f.right (fun i : Finₓ (n + 1) => f.left) fun i => f.Hom]
    [∀ n : ℕ, HasWidePullback g.right (fun i : Finₓ (n + 1) => g.left) fun i => g.Hom] (F : f ⟶ g) :
    f.cechNerve ⟶ g.cechNerve where
  app := fun n =>
    (widePullback.lift (widePullback.base _ ≫ F.right) fun i => widePullback.π _ i ≫ F.left) fun j => by
      simp
  naturality' := fun x y f => by
    ext ⟨⟩
    · simp
      
    · simp
      

/-- The augmented Čech nerve associated to an arrow. -/
@[simps]
def augmentedCechNerve : SimplicialObject.Augmented C where
  left := f.cechNerve
  right := f.right
  Hom :=
    { app := fun i => widePullback.base _,
      naturality' := fun x y f => by
        dsimp'
        simp }

/-- The morphism between augmented Čech nerve associated to a morphism of arrows. -/
@[simps]
def mapAugmentedCechNerve {f g : Arrow C}
    [∀ n : ℕ, HasWidePullback f.right (fun i : Finₓ (n + 1) => f.left) fun i => f.Hom]
    [∀ n : ℕ, HasWidePullback g.right (fun i : Finₓ (n + 1) => g.left) fun i => g.Hom] (F : f ⟶ g) :
    f.augmentedCechNerve ⟶ g.augmentedCechNerve where
  left := mapCechNerve F
  right := F.right
  w' := by
    ext
    simp

end CategoryTheory.Arrow

namespace CategoryTheory

namespace SimplicialObject

variable [∀ (n : ℕ) (f : Arrow C), HasWidePullback f.right (fun i : Finₓ (n + 1) => f.left) fun i => f.Hom]

/-- The Čech nerve construction, as a functor from `arrow C`. -/
@[simps]
def cechNerve : Arrow C ⥤ SimplicialObject C where
  obj := fun f => f.cechNerve
  map := fun f g F => Arrow.mapCechNerve F
  map_id' := fun i => by
    ext
    · simp
      
    · simp
      
  map_comp' := fun x y z f g => by
    ext
    · simp
      
    · simp
      

/-- The augmented Čech nerve construction, as a functor from `arrow C`. -/
@[simps]
def augmentedCechNerve : Arrow C ⥤ SimplicialObject.Augmented C where
  obj := fun f => f.augmentedCechNerve
  map := fun f g F => Arrow.mapAugmentedCechNerve F
  map_id' := fun x => by
    ext
    · simp
      
    · simp
      
    · rfl
      
  map_comp' := fun x y z f g => by
    ext
    · simp
      
    · simp
      
    · rfl
      

/-- A helper function used in defining the Čech adjunction. -/
@[simps]
def equivalenceRightToLeft (X : SimplicialObject.Augmented C) (F : Arrow C) (G : X ⟶ F.augmentedCechNerve) :
    Augmented.toArrow.obj X ⟶ F where
  left := G.left.app _ ≫ widePullback.π (fun i => F.Hom) 0
  right := G.right
  w' := by
    have := G.w
    apply_fun fun e => e.app (Opposite.op <| SimplexCategory.mk 0)  at this
    simpa using this

/-- A helper function used in defining the Čech adjunction. -/
@[simps]
def equivalenceLeftToRight (X : SimplicialObject.Augmented C) (F : Arrow C) (G : Augmented.toArrow.obj X ⟶ F) :
    X ⟶ F.augmentedCechNerve where
  left :=
    { app := fun x =>
        Limits.widePullback.lift (X.Hom.app _ ≫ G.right)
          (fun i => X.left.map (SimplexCategory.const x.unop i).op ≫ G.left) fun i => by
          dsimp'
          erw [category.assoc, arrow.w, augmented.to_arrow_obj_hom, nat_trans.naturality_assoc, functor.const.obj_map,
            category.id_comp],
      naturality' := by
        intro x y f
        ext
        · dsimp'
          simp only [← wide_pullback.lift_π, ← category.assoc]
          rw [← category.assoc, ← X.left.map_comp]
          rfl
          
        · dsimp'
          simp only [← functor.const.obj_map, ← nat_trans.naturality_assoc, ← wide_pullback.lift_base, ← category.assoc]
          erw [category.id_comp]
           }
  right := G.right
  w' := by
    ext
    dsimp'
    simp

/-- A helper function used in defining the Čech adjunction. -/
@[simps]
def cechNerveEquiv (X : SimplicialObject.Augmented C) (F : Arrow C) :
    (Augmented.toArrow.obj X ⟶ F) ≃ (X ⟶ F.augmentedCechNerve) where
  toFun := equivalenceLeftToRight _ _
  invFun := equivalenceRightToLeft _ _
  left_inv := by
    intro A
    dsimp'
    ext
    · dsimp'
      erw [wide_pullback.lift_π]
      nth_rw 1[← category.id_comp A.left]
      congr 1
      convert X.left.map_id _
      rw [← op_id]
      congr 1
      ext ⟨a, ha⟩
      change a < 1 at ha
      change 0 = a
      linarith
      
    · rfl
      
  right_inv := by
    intro A
    ext _ ⟨j⟩
    · dsimp'
      simp only [← arrow.cech_nerve_map, ← wide_pullback.lift_π, ← nat_trans.naturality_assoc]
      erw [wide_pullback.lift_π]
      rfl
      
    · erw [wide_pullback.lift_base]
      have := A.w
      apply_fun fun e => e.app x  at this
      rw [nat_trans.comp_app] at this
      erw [this]
      rfl
      
    · rfl
      

/-- The augmented Čech nerve construction is right adjoint to the `to_arrow` functor. -/
abbrev cechNerveAdjunction : (Augmented.toArrow : _ ⥤ Arrow C) ⊣ augmented_cech_nerve :=
  Adjunction.mkOfHomEquiv
    { homEquiv := cechNerveEquiv,
      hom_equiv_naturality_left_symm' := fun x y f g h => by
        ext
        · simp
          
        · simp
          ,
      hom_equiv_naturality_right' := fun x y f g h => by
        ext
        · simp
          
        · simp
          
        · rfl
           }

end SimplicialObject

end CategoryTheory

namespace CategoryTheory.Arrow

variable (f : Arrow C)

variable [∀ n : ℕ, HasWidePushout f.left (fun i : Finₓ (n + 1) => f.right) fun i => f.Hom]

/-- The Čech conerve associated to an arrow. -/
@[simps]
def cechConerve : CosimplicialObject C where
  obj := fun n => widePushout f.left (fun i : Finₓ (n.len + 1) => f.right) fun i => f.Hom
  map := fun m n g =>
    (widePushout.desc (widePushout.head _) fun i => (widePushout.ι fun i => f.Hom) <| g.toOrderHom i) fun i => by
      rw [wide_pushout.arrow_ι fun i => f.hom]
  map_id' := fun x => by
    ext ⟨⟩
    · simpa
      
    · simp
      
  map_comp' := fun x y z f g => by
    ext ⟨⟩
    · simpa
      
    · simp
      

/-- The morphism between Čech conerves associated to a morphism of arrows. -/
@[simps]
def mapCechConerve {f g : Arrow C} [∀ n : ℕ, HasWidePushout f.left (fun i : Finₓ (n + 1) => f.right) fun i => f.Hom]
    [∀ n : ℕ, HasWidePushout g.left (fun i : Finₓ (n + 1) => g.right) fun i => g.Hom] (F : f ⟶ g) :
    f.cechConerve ⟶ g.cechConerve where
  app := fun n =>
    (widePushout.desc (F.left ≫ widePushout.head _) fun i => F.right ≫ widePushout.ι _ i) fun i => by
      rw [← arrow.w_assoc F, wide_pushout.arrow_ι fun i => g.hom]
  naturality' := fun x y f => by
    ext
    · simp
      
    · simp
      

/-- The augmented Čech conerve associated to an arrow. -/
@[simps]
def augmentedCechConerve : CosimplicialObject.Augmented C where
  left := f.left
  right := f.cechConerve
  Hom :=
    { app := fun i => widePushout.head _,
      naturality' := fun x y f => by
        dsimp'
        simp }

/-- The morphism between augmented Čech conerves associated to a morphism of arrows. -/
@[simps]
def mapAugmentedCechConerve {f g : Arrow C}
    [∀ n : ℕ, HasWidePushout f.left (fun i : Finₓ (n + 1) => f.right) fun i => f.Hom]
    [∀ n : ℕ, HasWidePushout g.left (fun i : Finₓ (n + 1) => g.right) fun i => g.Hom] (F : f ⟶ g) :
    f.augmentedCechConerve ⟶ g.augmentedCechConerve where
  left := F.left
  right := mapCechConerve F
  w' := by
    ext
    simp

end CategoryTheory.Arrow

namespace CategoryTheory

namespace CosimplicialObject

variable [∀ (n : ℕ) (f : Arrow C), HasWidePushout f.left (fun i : Finₓ (n + 1) => f.right) fun i => f.Hom]

/-- The Čech conerve construction, as a functor from `arrow C`. -/
@[simps]
def cechConerve : Arrow C ⥤ CosimplicialObject C where
  obj := fun f => f.cechConerve
  map := fun f g F => Arrow.mapCechConerve F
  map_id' := fun i => by
    ext
    · dsimp'
      simp
      
    · dsimp'
      simp
      
  map_comp' := fun f g h F G => by
    ext
    · simp
      
    · simp
      

/-- The augmented Čech conerve construction, as a functor from `arrow C`. -/
@[simps]
def augmentedCechConerve : Arrow C ⥤ CosimplicialObject.Augmented C where
  obj := fun f => f.augmentedCechConerve
  map := fun f g F => Arrow.mapAugmentedCechConerve F
  map_id' := fun f => by
    ext
    · rfl
      
    · dsimp'
      simp
      
    · dsimp'
      simp
      
  map_comp' := fun f g h F G => by
    ext
    · rfl
      
    · simp
      
    · simp
      

/-- A helper function used in defining the Čech conerve adjunction. -/
@[simps]
def equivalenceLeftToRight (F : Arrow C) (X : CosimplicialObject.Augmented C) (G : F.augmentedCechConerve ⟶ X) :
    F ⟶ Augmented.toArrow.obj X where
  left := G.left
  right := (widePushout.ι (fun i => F.Hom) 0 ≫ G.right.app (SimplexCategory.mk 0) : _)
  w' := by
    have := G.w
    apply_fun fun e => e.app (SimplexCategory.mk 0)  at this
    simpa only [← CategoryTheory.Functor.id_map, ← augmented.to_arrow_obj_hom, ←
      wide_pushout.arrow_ι_assoc fun i => F.hom]

/-- A helper function used in defining the Čech conerve adjunction. -/
@[simps]
def equivalenceRightToLeft (F : Arrow C) (X : CosimplicialObject.Augmented C) (G : F ⟶ Augmented.toArrow.obj X) :
    F.augmentedCechConerve ⟶ X where
  left := G.left
  right :=
    { app := fun x =>
        Limits.widePushout.desc (G.left ≫ X.Hom.app _) (fun i => G.right ≫ X.right.map (SimplexCategory.const x i))
          (by
            rintro j
            rw [← arrow.w_assoc G]
            have t := X.hom.naturality (x.const j)
            dsimp'  at t⊢
            simp only [← category.id_comp] at t
            rw [← t]),
      naturality' := by
        intro x y f
        ext
        · dsimp'
          simp only [← wide_pushout.ι_desc_assoc, ← wide_pushout.ι_desc]
          rw [category.assoc, ← X.right.map_comp]
          rfl
          
        · dsimp'
          simp only [← functor.const.obj_map, nat_trans.naturality, ← wide_pushout.head_desc_assoc, ←
            wide_pushout.head_desc, ← category.assoc]
          erw [category.id_comp]
           }
  w' := by
    ext
    simp

/-- A helper function used in defining the Čech conerve adjunction. -/
@[simps]
def cechConerveEquiv (F : Arrow C) (X : CosimplicialObject.Augmented C) :
    (F.augmentedCechConerve ⟶ X) ≃ (F ⟶ Augmented.toArrow.obj X) where
  toFun := equivalenceLeftToRight _ _
  invFun := equivalenceRightToLeft _ _
  left_inv := by
    intro A
    dsimp'
    ext _
    · rfl
      
    ext _ ⟨⟩
    -- A bug in the `ext` tactic?
    · dsimp'
      simp only [← arrow.cech_conerve_map, ← wide_pushout.ι_desc, ← category.assoc, nat_trans.naturality, ←
        wide_pushout.ι_desc_assoc]
      rfl
      
    · erw [wide_pushout.head_desc]
      have := A.w
      apply_fun fun e => e.app x  at this
      rw [nat_trans.comp_app] at this
      erw [this]
      rfl
      
  right_inv := by
    intro A
    ext
    · rfl
      
    · dsimp'
      erw [wide_pushout.ι_desc]
      nth_rw 1[← category.comp_id A.right]
      congr 1
      convert X.right.map_id _
      ext ⟨a, ha⟩
      change a < 1 at ha
      change 0 = a
      linarith
      

/-- The augmented Čech conerve construction is left adjoint to the `to_arrow` functor. -/
abbrev cechConerveAdjunction : augmented_cech_conerve ⊣ (Augmented.toArrow : _ ⥤ Arrow C) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := cechConerveEquiv,
      hom_equiv_naturality_left_symm' := fun x y f g h => by
        ext
        · rfl
          
        · simp
          
        · simp
          ,
      hom_equiv_naturality_right' := fun x y f g h => by
        ext
        · simp
          
        · simp
           }

end CosimplicialObject

end CategoryTheory

