/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.CategoryTheory.FullSubcategory
import Mathbin.CategoryTheory.Limits.Shapes.Equalizers
import Mathbin.CategoryTheory.Limits.Shapes.Products
import Mathbin.Topology.Sheaves.Presheaf

/-!
# The sheaf condition in terms of an equalizer of products

Here we set up the machinery for the "usual" definition of the sheaf condition,
e.g. as in https://stacks.math.columbia.edu/tag/0072
in terms of an equalizer diagram where the two objects are
`∏ F.obj (U i)` and `∏ F.obj (U i) ⊓ (U j)`.

-/


universe v' v u

noncomputable section

open CategoryTheory

open CategoryTheory.Limits

open TopologicalSpace

open Opposite

open TopologicalSpace.Opens

namespace Top

variable {C : Type u} [Category.{v} C] [HasProducts.{v} C]

variable {X : Top.{v'}} (F : Presheaf C X) {ι : Type v} (U : ι → Opens X)

namespace Presheaf

namespace SheafConditionEqualizerProducts

/-- The product of the sections of a presheaf over a family of open sets. -/
def piOpens : C :=
  ∏ fun i : ι => F.obj (op (U i))

/-- The product of the sections of a presheaf over the pairwise intersections of
a family of open sets.
-/
def piInters : C :=
  ∏ fun p : ι × ι => F.obj (op (U p.1⊓U p.2))

/-- The morphism `Π F.obj (U i) ⟶ Π F.obj (U i) ⊓ (U j)` whose components
are given by the restriction maps from `U i` to `U i ⊓ U j`.
-/
def leftRes : piOpens F U ⟶ piInters F U :=
  Pi.lift fun p : ι × ι => Pi.π _ p.1 ≫ F.map (inf_le_left (U p.1) (U p.2)).op

/-- The morphism `Π F.obj (U i) ⟶ Π F.obj (U i) ⊓ (U j)` whose components
are given by the restriction maps from `U j` to `U i ⊓ U j`.
-/
def rightRes : piOpens F U ⟶ piInters F U :=
  Pi.lift fun p : ι × ι => Pi.π _ p.2 ≫ F.map (inf_le_right (U p.1) (U p.2)).op

/-- The morphism `F.obj U ⟶ Π F.obj (U i)` whose components
are given by the restriction maps from `U j` to `U i ⊓ U j`.
-/
def res : F.obj (op (supr U)) ⟶ piOpens F U :=
  Pi.lift fun i : ι => F.map (TopologicalSpace.Opens.leSupr U i).op

@[simp, elementwise]
theorem res_π (i : ι) : res F U ≫ limit.π _ ⟨i⟩ = F.map (Opens.leSupr U i).op := by
  rw [res, limit.lift_π, fan.mk_π_app]

@[elementwise]
theorem w : res F U ≫ leftRes F U = res F U ≫ rightRes F U := by
  dsimp' [← res, ← left_res, ← right_res]
  ext
  simp only [← limit.lift_π, ← limit.lift_π_assoc, ← fan.mk_π_app, ← category.assoc]
  rw [← F.map_comp]
  rw [← F.map_comp]
  congr

/-- The equalizer diagram for the sheaf condition.
-/
@[reducible]
def diagram : walking_parallel_pair ⥤ C :=
  parallelPair (leftRes F U) (rightRes F U)

/-- The restriction map `F.obj U ⟶ Π F.obj (U i)` gives a cone over the equalizer diagram
for the sheaf condition. The sheaf condition asserts this cone is a limit cone.
-/
def fork : Fork.{v} (leftRes F U) (rightRes F U) :=
  Fork.ofι _ (w F U)

@[simp]
theorem fork_X : (fork F U).x = F.obj (op (supr U)) :=
  rfl

@[simp]
theorem fork_ι : (fork F U).ι = res F U :=
  rfl

@[simp]
theorem fork_π_app_walking_parallel_pair_zero : (fork F U).π.app WalkingParallelPair.zero = res F U :=
  rfl

@[simp]
theorem fork_π_app_walking_parallel_pair_one : (fork F U).π.app WalkingParallelPair.one = res F U ≫ leftRes F U :=
  rfl

variable {F} {G : Presheaf C X}

/-- Isomorphic presheaves have isomorphic `pi_opens` for any cover `U`. -/
@[simp]
def piOpens.isoOfIso (α : F ≅ G) : piOpens F U ≅ piOpens G U :=
  Pi.mapIso fun X => α.app _

/-- Isomorphic presheaves have isomorphic `pi_inters` for any cover `U`. -/
@[simp]
def piInters.isoOfIso (α : F ≅ G) : piInters F U ≅ piInters G U :=
  Pi.mapIso fun X => α.app _

/-- Isomorphic presheaves have isomorphic sheaf condition diagrams. -/
def diagram.isoOfIso (α : F ≅ G) : diagram F U ≅ diagram G U :=
  NatIso.ofComponents
    (by
      rintro ⟨⟩
      exact pi_opens.iso_of_iso U α
      exact pi_inters.iso_of_iso U α)
    (by
      rintro ⟨⟩ ⟨⟩ ⟨⟩
      · simp
        
      · ext
        simp [← left_res]
        
      · ext
        simp [← right_res]
        
      · simp
        )

/-- If `F G : presheaf C X` are isomorphic presheaves,
then the `fork F U`, the canonical cone of the sheaf condition diagram for `F`,
is isomorphic to `fork F G` postcomposed with the corresponding isomorphism between
sheaf condition diagrams.
-/
def fork.isoOfIso (α : F ≅ G) : fork F U ≅ (Cones.postcompose (diagram.isoOfIso U α).inv).obj (fork G U) := by
  fapply fork.ext
  · apply α.app
    
  · ext
    dunfold fork.ι
    -- Ugh, `simp` can't unfold abbreviations.
    simp [← res, ← diagram.iso_of_iso]
    

section OpenEmbedding

variable {V : Top.{v'}} {j : V ⟶ X} (oe : OpenEmbedding j)

variable (𝒰 : ι → Opens V)

/-- Push forward a cover along an open embedding.
-/
@[simp]
def Cover.ofOpenEmbedding : ι → Opens X := fun i => oe.IsOpenMap.Functor.obj (𝒰 i)

/-- The isomorphism between `pi_opens` corresponding to an open embedding.
-/
@[simp]
def piOpens.isoOfOpenEmbedding : piOpens (oe.IsOpenMap.Functor.op ⋙ F) 𝒰 ≅ piOpens F (Cover.ofOpenEmbedding oe 𝒰) :=
  Pi.mapIso fun X => F.mapIso (Iso.refl _)

/-- The isomorphism between `pi_inters` corresponding to an open embedding.
-/
@[simp]
def piInters.isoOfOpenEmbedding : piInters (oe.IsOpenMap.Functor.op ⋙ F) 𝒰 ≅ piInters F (Cover.ofOpenEmbedding oe 𝒰) :=
  Pi.mapIso fun X =>
    F.mapIso
      (by
        dsimp' [← IsOpenMap.functor]
        exact
          iso.op
            { Hom :=
                hom_of_le
                  (by
                    simp only [← oe.to_embedding.inj, ← Set.image_inter]
                    exact le_rfl),
              inv :=
                hom_of_le
                  (by
                    simp only [← oe.to_embedding.inj, ← Set.image_inter]
                    exact le_rfl) })

/-- The isomorphism of sheaf condition diagrams corresponding to an open embedding. -/
def diagram.isoOfOpenEmbedding : diagram (oe.IsOpenMap.Functor.op ⋙ F) 𝒰 ≅ diagram F (Cover.ofOpenEmbedding oe 𝒰) :=
  NatIso.ofComponents
    (by
      rintro ⟨⟩
      exact pi_opens.iso_of_open_embedding oe 𝒰
      exact pi_inters.iso_of_open_embedding oe 𝒰)
    (by
      rintro ⟨⟩ ⟨⟩ ⟨⟩
      · simp
        
      · ext
        dsimp' [← left_res, ← IsOpenMap.functor]
        simp only [← limit.lift_π, ← cones.postcompose_obj_π, ← iso.op_hom, ← discrete.nat_iso_hom_app, ←
          functor.map_iso_refl, ← functor.map_iso_hom, ← lim_map_π_assoc, ← limit.lift_map, ← fan.mk_π_app, ←
          nat_trans.comp_app, ← category.assoc]
        dsimp'
        rw [category.id_comp, ← F.map_comp]
        rfl
        
      · ext
        dsimp' [← right_res, ← IsOpenMap.functor]
        simp only [← limit.lift_π, ← cones.postcompose_obj_π, ← iso.op_hom, ← discrete.nat_iso_hom_app, ←
          functor.map_iso_refl, ← functor.map_iso_hom, ← lim_map_π_assoc, ← limit.lift_map, ← fan.mk_π_app, ←
          nat_trans.comp_app, ← category.assoc]
        dsimp'
        rw [category.id_comp, ← F.map_comp]
        rfl
        
      · simp
        )

/-- If `F : presheaf C X` is a presheaf, and `oe : U ⟶ X` is an open embedding,
then the sheaf condition fork for a cover `𝒰` in `U` for the composition of `oe` and `F` is
isomorphic to sheaf condition fork for `oe '' 𝒰`, precomposed with the isomorphism
of indexing diagrams `diagram.iso_of_open_embedding`.

We use this to show that the restriction of sheaf along an open embedding is still a sheaf.
-/
def fork.isoOfOpenEmbedding :
    fork (oe.IsOpenMap.Functor.op ⋙ F) 𝒰 ≅
      (Cones.postcompose (diagram.isoOfOpenEmbedding oe 𝒰).inv).obj (fork F (Cover.ofOpenEmbedding oe 𝒰)) :=
  by
  fapply fork.ext
  · dsimp' [← IsOpenMap.functor]
    exact
      F.map_iso
        (iso.op
          { Hom :=
              hom_of_le
                (by
                  simp only [← coe_supr, ← supr_mk, ← le_def, ← Subtype.coe_mk, ← Set.le_eq_subset, ← Set.image_Union]),
            inv :=
              hom_of_le
                (by
                  simp only [← coe_supr, ← supr_mk, ← le_def, ← Subtype.coe_mk, ← Set.le_eq_subset, ←
                    Set.image_Union]) })
    
  · ext ⟨j⟩
    dunfold fork.ι
    -- Ugh, it is unpleasant that we need this.
    simp only [← res, ← diagram.iso_of_open_embedding, ← discrete.nat_iso_inv_app, ← functor.map_iso_inv, ←
      limit.lift_π, ← cones.postcompose_obj_π, ← functor.comp_map, ← fork_π_app_walking_parallel_pair_zero, ←
      pi_opens.iso_of_open_embedding, ← nat_iso.of_components.inv_app, ← functor.map_iso_refl, ← functor.op_map, ←
      limit.lift_map, ← fan.mk_π_app, ← nat_trans.comp_app, ← Quiver.Hom.unop_op, ← category.assoc, ←
      lim_map_eq_lim_map]
    dsimp'
    rw [category.comp_id, ← F.map_comp]
    rfl
    

end OpenEmbedding

end SheafConditionEqualizerProducts

end Presheaf

end Top

