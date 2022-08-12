/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Justus Springer
-/
import Mathbin.Topology.Category.Top.OpenNhds
import Mathbin.Topology.Sheaves.Presheaf
import Mathbin.Topology.Sheaves.SheafCondition.UniqueGluing
import Mathbin.CategoryTheory.Limits.Types
import Mathbin.CategoryTheory.Limits.Preserves.Filtered
import Mathbin.CategoryTheory.Limits.Final
import Mathbin.Topology.Sober
import Mathbin.Tactic.Elementwise
import Mathbin.Algebra.Category.Ring.Default

/-!
# Stalks

For a presheaf `F` on a topological space `X`, valued in some category `C`, the *stalk* of `F`
at the point `x : X` is defined as the colimit of the composition of the inclusion of categories
`(nhds x)ᵒᵖ ⥤ (opens X)ᵒᵖ` and the functor `F : (opens X)ᵒᵖ ⥤ C`.
For an open neighborhood `U` of `x`, we define the map `F.germ x : F.obj (op U) ⟶ F.stalk x` as the
canonical morphism into this colimit.

Taking stalks is functorial: For every point `x : X` we define a functor `stalk_functor C x`,
sending presheaves on `X` to objects of `C`. Furthermore, for a map `f : X ⟶ Y` between
topological spaces, we define `stalk_pushforward` as the induced map on the stalks
`(f _* ℱ).stalk (f x) ⟶ ℱ.stalk x`.

Some lemmas about stalks and germs only hold for certain classes of concrete categories. A basic
property of forgetful functors of categories of algebraic structures (like `Mon`, `CommRing`,...)
is that they preserve filtered colimits. Since stalks are filtered colimits, this ensures that
the stalks of presheaves valued in these categories behave exactly as for `Type`-valued presheaves.
For example, in `germ_exist` we prove that in such a category, every element of the stalk is the
germ of a section.

Furthermore, if we require the forgetful functor to reflect isomorphisms and preserve limits (as
is the case for most algebraic structures), we have access to the unique gluing API and can prove
further properties. Most notably, in `is_iso_iff_stalk_functor_map_iso`, we prove that in such
a category, a morphism of sheaves is an isomorphism if and only if all of its stalk maps are
isomorphisms.

See also the definition of "algebraic structures" in the stacks project:
https://stacks.math.columbia.edu/tag/007L

-/


noncomputable section

universe v u v' u'

open CategoryTheory

open Top

open CategoryTheory.Limits

open TopologicalSpace

open Opposite

variable {C : Type u} [Category.{v} C]

variable [HasColimits.{v} C]

variable {X Y Z : Top.{v}}

namespace Top.Presheaf

variable (C)

/-- Stalks are functorial with respect to morphisms of presheaves over a fixed `X`. -/
def stalkFunctor (x : X) : X.Presheaf C ⥤ C :=
  (whiskeringLeft _ _ C).obj (OpenNhds.inclusion x).op ⋙ colim

variable {C}

/-- The stalk of a presheaf `F` at a point `x` is calculated as the colimit of the functor
nbhds x ⥤ opens F.X ⥤ C
-/
def stalk (ℱ : X.Presheaf C) (x : X) : C :=
  (stalkFunctor C x).obj ℱ

-- -- colimit ((open_nhds.inclusion x).op ⋙ ℱ)
@[simp]
theorem stalk_functor_obj (ℱ : X.Presheaf C) (x : X) : (stalkFunctor C x).obj ℱ = ℱ.stalk x :=
  rfl

/-- The germ of a section of a presheaf over an open at a point of that open.
-/
def germ (F : X.Presheaf C) {U : Opens X} (x : U) : F.obj (op U) ⟶ stalk F x :=
  colimit.ι ((OpenNhds.inclusion x.1).op ⋙ F) (op ⟨U, x.2⟩)

@[simp, elementwise]
theorem germ_res (F : X.Presheaf C) {U V : Opens X} (i : U ⟶ V) (x : U) : F.map i.op ≫ germ F x = germ F (i x : V) :=
  let i' : (⟨U, x.2⟩ : OpenNhds x.1) ⟶ ⟨V, (i x : V).2⟩ := i
  colimit.w ((OpenNhds.inclusion x.1).op ⋙ F) i'.op

/-- A morphism from the stalk of `F` at `x` to some object `Y` is completely determined by its
composition with the `germ` morphisms.
-/
theorem stalk_hom_ext (F : X.Presheaf C) {x} {Y : C} {f₁ f₂ : F.stalk x ⟶ Y}
    (ih : ∀ (U : Opens X) (hxU : x ∈ U), F.germ ⟨x, hxU⟩ ≫ f₁ = F.germ ⟨x, hxU⟩ ≫ f₂) : f₁ = f₂ :=
  colimit.hom_ext fun U => by
    induction U using Opposite.rec
    cases' U with U hxU
    exact ih U hxU

@[simp, reassoc, elementwise]
theorem stalk_functor_map_germ {F G : X.Presheaf C} (U : Opens X) (x : U) (f : F ⟶ G) :
    germ F x ≫ (stalkFunctor C x.1).map f = f.app (op U) ≫ germ G x :=
  colimit.ι_map (whiskerLeft (OpenNhds.inclusion x.1).op f) (op ⟨U, x.2⟩)

variable (C)

/-- For a presheaf `F` on a space `X`, a continuous map `f : X ⟶ Y` induces a morphisms between the
stalk of `f _ * F` at `f x` and the stalk of `F` at `x`.
-/
def stalkPushforward (f : X ⟶ Y) (F : X.Presheaf C) (x : X) : (f _* F).stalk (f x) ⟶ F.stalk x := by
  -- This is a hack; Lean doesn't like to elaborate the term written directly.
  trans
  swap
  exact colimit.pre _ (open_nhds.map f x).op
  exact colim.map (whisker_right (nat_trans.op (open_nhds.inclusion_map_iso f x).inv) F)

@[simp, elementwise, reassoc]
theorem stalk_pushforward_germ (f : X ⟶ Y) (F : X.Presheaf C) (U : Opens Y) (x : (Opens.map f).obj U) :
    (f _* F).germ ⟨f x, x.2⟩ ≫ F.stalkPushforward C f x = F.germ x := by
  rw [stalk_pushforward, germ, colimit.ι_map_assoc, colimit.ι_pre, whisker_right_app]
  erw [CategoryTheory.Functor.map_id, category.id_comp]
  rfl

-- Here are two other potential solutions, suggested by @fpvandoorn at
-- <https://github.com/leanprover-community/mathlib/pull/1018#discussion_r283978240>
-- However, I can't get the subsequent two proofs to work with either one.
-- def stalk_pushforward (f : X ⟶ Y) (ℱ : X.presheaf C) (x : X) :
--   (f _* ℱ).stalk (f x) ⟶ ℱ.stalk x :=
-- colim.map ((functor.associator _ _ _).inv ≫
--   whisker_right (nat_trans.op (open_nhds.inclusion_map_iso f x).inv) ℱ) ≫
-- colimit.pre ((open_nhds.inclusion x).op ⋙ ℱ) (open_nhds.map f x).op
-- def stalk_pushforward (f : X ⟶ Y) (ℱ : X.presheaf C) (x : X) :
--   (f _* ℱ).stalk (f x) ⟶ ℱ.stalk x :=
-- (colim.map (whisker_right (nat_trans.op (open_nhds.inclusion_map_iso f x).inv) ℱ) :
--   colim.obj ((open_nhds.inclusion (f x) ⋙ opens.map f).op ⋙ ℱ) ⟶ _) ≫
-- colimit.pre ((open_nhds.inclusion x).op ⋙ ℱ) (open_nhds.map f x).op
namespace StalkPushforward

attribute [local tidy] tactic.op_induction'

@[simp]
theorem id (ℱ : X.Presheaf C) (x : X) : ℱ.stalkPushforward C (𝟙 X) x = (stalkFunctor C x).map (Pushforward.id ℱ).Hom :=
  by
  dsimp' [← stalk_pushforward, ← stalk_functor]
  ext1
  run_tac
    tactic.op_induction'
  cases j
  cases j_val
  rw [colimit.ι_map_assoc, colimit.ι_map, colimit.ι_pre, whisker_left_app, whisker_right_app, pushforward.id_hom_app,
    eq_to_hom_map, eq_to_hom_refl]
  dsimp'
  -- FIXME A simp lemma which unfortunately doesn't fire:
  erw [CategoryTheory.Functor.map_id]

-- This proof is sadly not at all robust:
-- having to use `erw` at all is a bad sign.
@[simp]
theorem comp (ℱ : X.Presheaf C) (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    ℱ.stalkPushforward C (f ≫ g) x = (f _* ℱ).stalkPushforward C g (f x) ≫ ℱ.stalkPushforward C f x := by
  dsimp' [← stalk_pushforward, ← stalk_functor]
  ext U
  induction U using Opposite.rec
  cases U
  cases U_val
  simp only [← colimit.ι_map_assoc, ← colimit.ι_pre_assoc, ← whisker_right_app, ← category.assoc]
  dsimp'
  -- FIXME: Some of these are simp lemmas, but don't fire successfully:
  erw [CategoryTheory.Functor.map_id, category.id_comp, category.id_comp, category.id_comp, colimit.ι_pre,
    colimit.ι_pre]
  rfl

theorem stalk_pushforward_iso_of_open_embedding {f : X ⟶ Y} (hf : OpenEmbedding f) (F : X.Presheaf C) (x : X) :
    IsIso (F.stalkPushforward _ f x) := by
  have := functor.initial_of_adjunction (hf.is_open_map.adjunction_nhds x)
  convert
    is_iso.of_iso
      ((functor.final.colimit_iso (hf.is_open_map.functor_nhds x).op ((open_nhds.inclusion (f x)).op ⋙ f _* F) :
            _).symm ≪≫
        colim.map_iso _)
  swap
  · fapply nat_iso.of_components
    · intro U
      refine' F.map_iso (eq_to_iso _)
      dsimp' only [← functor.op]
      exact congr_arg op (Subtype.eq <| Set.preimage_image_eq (unop U).1.1 hf.inj)
      
    · intro U V i
      erw [← F.map_comp, ← F.map_comp]
      congr
      
    
  · ext U
    rw [← iso.comp_inv_eq]
    erw [colimit.ι_map_assoc]
    rw [colimit.ι_pre, category.assoc]
    erw [colimit.ι_map_assoc, colimit.ι_pre, ← F.map_comp_assoc]
    apply colimit.w ((open_nhds.inclusion (f x)).op ⋙ f _* F) _
    dsimp' only [← functor.op]
    refine' ((hom_of_le _).op : op (unop U) ⟶ _)
    exact Set.image_preimage_subset _ _
    

end StalkPushforward

section StalkPullback

/-- The morphism `ℱ_{f x} ⟶ (f⁻¹ℱ)ₓ` that factors through `(f_*f⁻¹ℱ)_{f x}`. -/
def stalkPullbackHom (f : X ⟶ Y) (F : Y.Presheaf C) (x : X) : F.stalk (f x) ⟶ (pullbackObj f F).stalk x :=
  (stalkFunctor _ (f x)).map ((pushforwardPullbackAdjunction C f).Unit.app F) ≫ stalkPushforward _ _ _ x

/-- The morphism `(f⁻¹ℱ)(U) ⟶ ℱ_{f(x)}` for some `U ∋ x`. -/
def germToPullbackStalk (f : X ⟶ Y) (F : Y.Presheaf C) (U : Opens X) (x : U) :
    (pullbackObj f F).obj (op U) ⟶ F.stalk (f x) :=
  colimit.desc (Lan.diagram (Opens.map f).op F (op U))
    { x := F.stalk (f x),
      ι :=
        { app := fun V => F.germ ⟨f x, V.Hom.unop.le x.2⟩,
          naturality' := fun _ _ i => by
            erw [category.comp_id]
            exact F.germ_res i.left.unop _ } }

/-- The morphism `(f⁻¹ℱ)ₓ ⟶ ℱ_{f(x)}`. -/
def stalkPullbackInv (f : X ⟶ Y) (F : Y.Presheaf C) (x : X) : (pullbackObj f F).stalk x ⟶ F.stalk (f x) :=
  colimit.desc ((OpenNhds.inclusion x).op ⋙ Presheaf.pullbackObj f F)
    { x := F.stalk (f x),
      ι :=
        { app := fun U => F.germToPullbackStalk _ f (unop U).1 ⟨x, (unop U).2⟩,
          naturality' := fun _ _ _ => by
            erw [colimit.pre_desc, category.comp_id]
            congr } }

/-- The isomorphism `ℱ_{f(x)} ≅ (f⁻¹ℱ)ₓ`. -/
def stalkPullbackIso (f : X ⟶ Y) (F : Y.Presheaf C) (x : X) : F.stalk (f x) ≅ (pullbackObj f F).stalk x where
  Hom := stalkPullbackHom _ _ _ _
  inv := stalkPullbackInv _ _ _ _
  hom_inv_id' := by
    delta' stalk_pullback_hom stalk_pullback_inv stalk_functor presheaf.pullback stalk_pushforward germ_to_pullback_stalk germ
    ext j
    induction j using Opposite.rec
    cases j
    simp only [← TopologicalSpace.OpenNhds.inclusion_map_iso_inv, ← whisker_right_app, ← whisker_left_app, ←
      whiskering_left_obj_map, ← functor.comp_map, ← colimit.ι_map_assoc, ← nat_trans.op_id, ← Lan_obj_map, ←
      pushforward_pullback_adjunction_unit_app_app, ← category.assoc, ← colimit.ι_pre_assoc]
    erw [colimit.ι_desc, colimit.pre_desc, colimit.ι_desc, category.comp_id]
    simpa
  inv_hom_id' := by
    delta' stalk_pullback_hom stalk_pullback_inv stalk_functor presheaf.pullback stalk_pushforward
    ext U j
    induction U using Opposite.rec
    cases U
    cases j
    rcases j_right with ⟨⟨⟩⟩
    erw [colimit.map_desc, colimit.map_desc, colimit.ι_desc_assoc, colimit.ι_desc_assoc, colimit.ι_desc,
      category.comp_id]
    simp only [← cocone.whisker_ι, ← colimit.cocone_ι, ← open_nhds.inclusion_map_iso_inv, ← cocones.precompose_obj_ι, ←
      whisker_right_app, ← whisker_left_app, ← nat_trans.comp_app, ← whiskering_left_obj_map, ← nat_trans.op_id, ←
      Lan_obj_map, ← pushforward_pullback_adjunction_unit_app_app]
    erw [←
      colimit.w _
        (@hom_of_le (open_nhds x) _ ⟨_, U_property⟩ ⟨(opens.map f).obj (unop j_left), j_hom.unop.le U_property⟩
            j_hom.unop.le).op]
    erw [colimit.ι_pre_assoc (Lan.diagram _ F _) (costructured_arrow.map _)]
    erw [colimit.ι_pre_assoc (Lan.diagram _ F _) (costructured_arrow.map _)]
    congr
    simp only [← category.assoc, ← costructured_arrow.map_mk]
    delta' costructured_arrow.mk
    congr

end StalkPullback

section StalkSpecializes

variable {C}

/-- If `x` specializes to `y`, then there is a natural map `F.stalk y ⟶ F.stalk x`. -/
noncomputable def stalkSpecializes (F : X.Presheaf C) {x y : X} (h : x ⤳ y) : F.stalk y ⟶ F.stalk x := by
  refine' colimit.desc _ ⟨_, fun U => _, _⟩
  · exact
      colimit.ι ((open_nhds.inclusion x).op ⋙ F)
        (op ⟨(unop U).1, (specializes_iff_forall_open.mp h _ (unop U).1.2 (unop U).2 : _)⟩)
    
  · intro U V i
    dsimp'
    rw [category.comp_id]
    let U' : open_nhds x := ⟨_, (specializes_iff_forall_open.mp h _ (unop U).1.2 (unop U).2 : _)⟩
    let V' : open_nhds x := ⟨_, (specializes_iff_forall_open.mp h _ (unop V).1.2 (unop V).2 : _)⟩
    exact colimit.w ((open_nhds.inclusion x).op ⋙ F) (show V' ⟶ U' from i.unop).op
    

@[simp, reassoc, elementwise]
theorem germ_stalk_specializes (F : X.Presheaf C) {U : Opens X} {y : U} {x : X} (h : x ⤳ y) :
    F.germ y ≫ F.stalkSpecializes h = F.germ ⟨x, specializes_iff_forall_open.mp h _ U.2 y.Prop⟩ :=
  colimit.ι_desc _ _

@[simp, reassoc, elementwise]
theorem germ_stalk_specializes' (F : X.Presheaf C) {U : Opens X} {x y : X} (h : x ⤳ y) (hy : y ∈ U) :
    F.germ ⟨y, hy⟩ ≫ F.stalkSpecializes h = F.germ ⟨x, specializes_iff_forall_open.mp h _ U.2 hy⟩ :=
  colimit.ι_desc _ _

@[simp, reassoc, elementwise]
theorem stalk_specializes_stalk_functor_map {F G : X.Presheaf C} (f : F ⟶ G) {x y : X} (h : x ⤳ y) :
    F.stalkSpecializes h ≫ (stalkFunctor C x).map f = (stalkFunctor C y).map f ≫ G.stalkSpecializes h := by
  ext
  delta' stalk_functor
  simpa [← stalk_specializes]

@[simp, reassoc, elementwise]
theorem stalk_specializes_stalk_pushforward (f : X ⟶ Y) (F : X.Presheaf C) {x y : X} (h : x ⤳ y) :
    (f _* F).stalkSpecializes (f.map_specializes h) ≫ F.stalkPushforward _ f x =
      F.stalkPushforward _ f y ≫ F.stalkSpecializes h :=
  by
  ext
  delta' stalk_pushforward
  simpa [← stalk_specializes]

end StalkSpecializes

section Concrete

variable {C}

variable [ConcreteCategory.{v} C]

attribute [local instance] concrete_category.has_coe_to_sort concrete_category.has_coe_to_fun

@[ext]
theorem germ_ext (F : X.Presheaf C) {U V : Opens X} {x : X} {hxU : x ∈ U} {hxV : x ∈ V} (W : Opens X) (hxW : x ∈ W)
    (iWU : W ⟶ U) (iWV : W ⟶ V) {sU : F.obj (op U)} {sV : F.obj (op V)} (ih : F.map iWU.op sU = F.map iWV.op sV) :
    F.germ ⟨x, hxU⟩ sU = F.germ ⟨x, hxV⟩ sV := by
  erw [← F.germ_res iWU ⟨x, hxW⟩, ← F.germ_res iWV ⟨x, hxW⟩, comp_apply, comp_apply, ih]

variable [PreservesFilteredColimits (forget C)]

/-- For presheaves valued in a concrete category whose forgetful functor preserves filtered colimits,
every element of the stalk is the germ of a section.
-/
theorem germ_exist (F : X.Presheaf C) (x : X) (t : stalk F x) :
    ∃ (U : Opens X)(m : x ∈ U)(s : F.obj (op U)), F.germ ⟨x, m⟩ s = t := by
  obtain ⟨U, s, e⟩ := Types.jointly_surjective.{v, v} _ (is_colimit_of_preserves (forget C) (colimit.is_colimit _)) t
  revert s e
  rw [show U = op (unop U) from rfl]
  generalize unop U = V
  clear U
  cases' V with V m
  intro s e
  exact ⟨V, m, s, e⟩

theorem germ_eq (F : X.Presheaf C) {U V : Opens X} (x : X) (mU : x ∈ U) (mV : x ∈ V) (s : F.obj (op U))
    (t : F.obj (op V)) (h : germ F ⟨x, mU⟩ s = germ F ⟨x, mV⟩ t) :
    ∃ (W : Opens X)(m : x ∈ W)(iU : W ⟶ U)(iV : W ⟶ V), F.map iU.op s = F.map iV.op t := by
  obtain ⟨W, iU, iV, e⟩ :=
    (Types.FilteredColimit.is_colimit_eq_iff.{v, v} _
          (is_colimit_of_preserves _ (colimit.is_colimit ((open_nhds.inclusion x).op ⋙ F)))).mp
      h
  exact ⟨(unop W).1, (unop W).2, iU.unop, iV.unop, e⟩

theorem stalk_functor_map_injective_of_app_injective {F G : Presheaf C X} (f : F ⟶ G)
    (h : ∀ U : Opens X, Function.Injective (f.app (op U))) (x : X) : Function.Injective ((stalkFunctor C x).map f) :=
  fun s t hst => by
  rcases germ_exist F x s with ⟨U₁, hxU₁, s, rfl⟩
  rcases germ_exist F x t with ⟨U₂, hxU₂, t, rfl⟩
  simp only [← stalk_functor_map_germ_apply _ ⟨x, _⟩] at hst
  obtain ⟨W, hxW, iWU₁, iWU₂, heq⟩ := G.germ_eq x hxU₁ hxU₂ _ _ hst
  rw [← comp_apply, ← comp_apply, ← f.naturality, ← f.naturality, comp_apply, comp_apply] at heq
  replace heq := h W HEq
  convert congr_arg (F.germ ⟨x, hxW⟩) HEq
  exacts[(F.germ_res_apply iWU₁ ⟨x, hxW⟩ s).symm, (F.germ_res_apply iWU₂ ⟨x, hxW⟩ t).symm]

variable [HasLimits C] [PreservesLimits (forget C)] [ReflectsIsomorphisms (forget C)]

/-- Let `F` be a sheaf valued in a concrete category, whose forgetful functor reflects isomorphisms,
preserves limits and filtered colimits. Then two sections who agree on every stalk must be equal.
-/
theorem section_ext (F : Sheaf C X) (U : Opens X) (s t : F.1.obj (op U)) (h : ∀ x : U, F.1.germ x s = F.1.germ x t) :
    s = t := by
  -- We use `germ_eq` and the axiom of choice, to pick for every point `x` a neighbourhood
  -- `V x`, such that the restrictions of `s` and `t` to `V x` coincide.
  choose V m i₁ i₂ heq using fun x : U => F.1.germ_eq x.1 x.2 x.2 s t (h x)
  -- Since `F` is a sheaf, we can prove the equality locally, if we can show that these
  -- neighborhoods form a cover of `U`.
  apply F.eq_of_locally_eq' V U i₁
  · intro x hxU
    rw [opens.mem_coe, opens.mem_supr]
    exact ⟨⟨x, hxU⟩, m ⟨x, hxU⟩⟩
    
  · intro x
    rw [HEq, Subsingleton.elimₓ (i₁ x) (i₂ x)]
    

/-
Note that the analogous statement for surjectivity is false: Surjectivity on stalks does not
imply surjectivity of the components of a sheaf morphism. However it does imply that the morphism
is an epi, but this fact is not yet formalized.
-/
theorem app_injective_of_stalk_functor_map_injective {F : Sheaf C X} {G : Presheaf C X} (f : F.1 ⟶ G) (U : Opens X)
    (h : ∀ x : U, Function.Injective ((stalkFunctor C x.val).map f)) : Function.Injective (f.app (op U)) :=
  fun s t hst =>
  (section_ext F _ _ _) fun x =>
    h x <| by
      rw [stalk_functor_map_germ_apply, stalk_functor_map_germ_apply, hst]

theorem app_injective_iff_stalk_functor_map_injective {F : Sheaf C X} {G : Presheaf C X} (f : F.1 ⟶ G) :
    (∀ x : X, Function.Injective ((stalkFunctor C x).map f)) ↔ ∀ U : Opens X, Function.Injective (f.app (op U)) :=
  ⟨fun h U => app_injective_of_stalk_functor_map_injective f U fun x => h x.1,
    stalk_functor_map_injective_of_app_injective f⟩

/-- For surjectivity, we are given an arbitrary section `t` and need to find a preimage for it.
We claim that it suffices to find preimages *locally*. That is, for each `x : U` we construct
a neighborhood `V ≤ U` and a section `s : F.obj (op V))` such that `f.app (op V) s` and `t`
agree on `V`. -/
theorem app_surjective_of_injective_of_locally_surjective {F G : Sheaf C X} (f : F ⟶ G) (U : Opens X)
    (hinj : ∀ x : U, Function.Injective ((stalkFunctor C x.1).map f))
    (hsurj :
      ∀ (t) (x : U), ∃ (V : Opens X)(m : x.1 ∈ V)(iVU : V ⟶ U)(s : F.1.obj (op V)), f.app (op V) s = G.1.map iVU.op t) :
    Function.Surjective (f.app (op U)) := by
  intro t
  -- We use the axiom of choice to pick around each point `x` an open neighborhood `V` and a
  -- preimage under `f` on `V`.
  choose V mV iVU sf heq using hsurj t
  -- These neighborhoods clearly cover all of `U`.
  have V_cover : U ≤ supr V := by
    intro x hxU
    rw [opens.mem_coe, opens.mem_supr]
    exact ⟨⟨x, hxU⟩, mV ⟨x, hxU⟩⟩
  -- Since `F` is a sheaf, we can glue all the local preimages together to get a global preimage.
  obtain ⟨s, s_spec, -⟩ := F.exists_unique_gluing' V U iVU V_cover sf _
  · use s
    apply G.eq_of_locally_eq' V U iVU V_cover
    intro x
    rw [← comp_apply, ← f.naturality, comp_apply, s_spec, HEq]
    
  · intro x y
    -- What's left to show here is that the secions `sf` are compatible, i.e. they agree on
    -- the intersections `V x ⊓ V y`. We prove this by showing that all germs are equal.
    apply section_ext
    intro z
    -- Here, we need to use injectivity of the stalk maps.
    apply hinj ⟨z, (iVU x).le ((inf_le_left : V x⊓V y ≤ V x) z.2)⟩
    dsimp' only
    erw [stalk_functor_map_germ_apply, stalk_functor_map_germ_apply]
    simp_rw [← comp_apply, f.naturality, comp_apply, HEq, ← comp_apply, ← G.1.map_comp]
    rfl
    

theorem app_surjective_of_stalk_functor_map_bijective {F G : Sheaf C X} (f : F ⟶ G) (U : Opens X)
    (h : ∀ x : U, Function.Bijective ((stalkFunctor C x.val).map f)) : Function.Surjective (f.app (op U)) := by
  refine' app_surjective_of_injective_of_locally_surjective f U (fun x => (h x).1) fun t x => _
  -- Now we need to prove our initial claim: That we can find preimages of `t` locally.
  -- Since `f` is surjective on stalks, we can find a preimage `s₀` of the germ of `t` at `x`
  obtain ⟨s₀, hs₀⟩ := (h x).2 (G.1.germ x t)
  -- ... and this preimage must come from some section `s₁` defined on some open neighborhood `V₁`
  obtain ⟨V₁, hxV₁, s₁, hs₁⟩ := F.1.germ_exist x.1 s₀
  subst hs₁
  rename' hs₀ => hs₁
  erw [stalk_functor_map_germ_apply V₁ ⟨x.1, hxV₁⟩ f s₁] at hs₁
  -- Now, the germ of `f.app (op V₁) s₁` equals the germ of `t`, hence they must coincide on
  -- some open neighborhood `V₂`.
  obtain ⟨V₂, hxV₂, iV₂V₁, iV₂U, heq⟩ := G.1.germ_eq x.1 hxV₁ x.2 _ _ hs₁
  -- The restriction of `s₁` to that neighborhood is our desired local preimage.
  use V₂, hxV₂, iV₂U, F.1.map iV₂V₁.op s₁
  rw [← comp_apply, f.naturality, comp_apply, HEq]

theorem app_bijective_of_stalk_functor_map_bijective {F G : Sheaf C X} (f : F ⟶ G) (U : Opens X)
    (h : ∀ x : U, Function.Bijective ((stalkFunctor C x.val).map f)) : Function.Bijective (f.app (op U)) :=
  ⟨app_injective_of_stalk_functor_map_injective f U fun x => (h x).1,
    app_surjective_of_stalk_functor_map_bijective f U h⟩

theorem app_is_iso_of_stalk_functor_map_iso {F G : Sheaf C X} (f : F ⟶ G) (U : Opens X)
    [∀ x : U, IsIso ((stalkFunctor C x.val).map f)] : IsIso (f.app (op U)) := by
  -- Since the forgetful functor of `C` reflects isomorphisms, it suffices to see that the
  -- underlying map between types is an isomorphism, i.e. bijective.
  suffices is_iso ((forget C).map (f.app (op U))) by
    exact is_iso_of_reflects_iso (f.app (op U)) (forget C)
  rw [is_iso_iff_bijective]
  apply app_bijective_of_stalk_functor_map_bijective
  intro x
  apply (is_iso_iff_bijective _).mp
  exact functor.map_is_iso (forget C) ((stalk_functor C x.1).map f)

/-- Let `F` and `G` be sheaves valued in a concrete category, whose forgetful functor reflects
isomorphisms, preserves limits and filtered colimits. Then if the stalk maps of a morphism
`f : F ⟶ G` are all isomorphisms, `f` must be an isomorphism.
-/
-- Making this an instance would cause a loop in typeclass resolution with `functor.map_is_iso`
theorem is_iso_of_stalk_functor_map_iso {F G : Sheaf C X} (f : F ⟶ G) [∀ x : X, IsIso ((stalkFunctor C x).map f)] :
    IsIso f := by
  -- Since the inclusion functor from sheaves to presheaves is fully faithful, it suffices to
  -- show that `f`, as a morphism between _presheaves_, is an isomorphism.
  suffices is_iso ((sheaf.forget C X).map f) by
    exact is_iso_of_fully_faithful (sheaf.forget C X) f
  -- We show that all components of `f` are isomorphisms.
  suffices ∀ U : (opens X)ᵒᵖ, is_iso (f.app U) by
    exact @nat_iso.is_iso_of_is_iso_app _ _ _ _ F.1 G.1 f this
  intro U
  induction U using Opposite.rec
  apply app_is_iso_of_stalk_functor_map_iso

/-- Let `F` and `G` be sheaves valued in a concrete category, whose forgetful functor reflects
isomorphisms, preserves limits and filtered colimits. Then a morphism `f : F ⟶ G` is an
isomorphism if and only if all of its stalk maps are isomorphisms.
-/
theorem is_iso_iff_stalk_functor_map_iso {F G : Sheaf C X} (f : F ⟶ G) :
    IsIso f ↔ ∀ x : X, IsIso ((stalkFunctor C x).map f) := by
  constructor
  · intro h x
    skip
    exact @functor.map_is_iso _ _ _ _ _ _ (stalk_functor C x) f ((sheaf.forget C X).map_is_iso f)
    
  · intro h
    exact is_iso_of_stalk_functor_map_iso f
    

end Concrete

instance (F : X.Presheaf CommRingₓₓ) {U : Opens X} (x : U) : Algebra (F.obj <| op U) (F.stalk x) :=
  (F.germ x).toAlgebra

@[simp]
theorem stalk_open_algebra_map {X : Top} (F : X.Presheaf CommRingₓₓ) {U : Opens X} (x : U) :
    algebraMap (F.obj <| op U) (F.stalk x) = F.germ x :=
  rfl

end Top.Presheaf

