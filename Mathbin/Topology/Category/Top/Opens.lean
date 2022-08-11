/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.CategoryTheory.Category.Preorder
import Mathbin.CategoryTheory.EqToHom
import Mathbin.Topology.Category.Top.EpiMono
import Mathbin.Topology.Sets.Opens

/-!
# The category of open sets in a topological space.

We define `to_Top : opens X ⥤ Top` and
`map (f : X ⟶ Y) : opens Y ⥤ opens X`, given by taking preimages of open sets.

Unfortunately `opens` isn't (usefully) a functor `Top ⥤ Cat`.
(One can in fact define such a functor,
but using it results in unresolvable `eq.rec` terms in goals.)

Really it's a 2-functor from (spaces, continuous functions, equalities)
to (categories, functors, natural isomorphisms).
We don't attempt to set up the full theory here, but do provide the natural isomorphisms
`map_id : map (𝟙 X) ≅ 𝟭 (opens X)` and
`map_comp : map (f ≫ g) ≅ map g ⋙ map f`.

Beyond that, there's a collection of simp lemmas for working with these constructions.
-/


open CategoryTheory

open TopologicalSpace

open Opposite

universe u

namespace TopologicalSpace.Opens

variable {X Y Z : Top.{u}}

/-!
Since `opens X` has a partial order, it automatically receives a `category` instance.
Unfortunately, because we do not allow morphisms in `Prop`,
the morphisms `U ⟶ V` are not just proofs `U ≤ V`, but rather
`ulift (plift (U ≤ V))`.
-/


instance opensHomHasCoeToFun {U V : Opens X} : CoeFun (U ⟶ V) fun f => U → V :=
  ⟨fun f x => ⟨x, f.le x.2⟩⟩

/-!
We now construct as morphisms various inclusions of open sets.
-/


/-- The inclusion `U ⊓ V ⟶ U` as a morphism in the category of open sets.
-/
-- This is tedious, but necessary because we decided not to allow Prop as morphisms in a category...
def infLeLeft (U V : Opens X) : U⊓V ⟶ U :=
  inf_le_left.Hom

/-- The inclusion `U ⊓ V ⟶ V` as a morphism in the category of open sets.
-/
def infLeRight (U V : Opens X) : U⊓V ⟶ V :=
  inf_le_right.Hom

/-- The inclusion `U i ⟶ supr U` as a morphism in the category of open sets.
-/
def leSupr {ι : Type _} (U : ι → Opens X) (i : ι) : U i ⟶ supr U :=
  (le_supr U i).Hom

/-- The inclusion `⊥ ⟶ U` as a morphism in the category of open sets.
-/
def botLe (U : Opens X) : ⊥ ⟶ U :=
  bot_le.Hom

/-- The inclusion `U ⟶ ⊤` as a morphism in the category of open sets.
-/
def leTop (U : Opens X) : U ⟶ ⊤ :=
  le_top.Hom

-- We do not mark this as a simp lemma because it breaks open `x`.
-- Nevertheless, it is useful in `sheaf_of_functions`.
theorem inf_le_left_apply (U V : Opens X) (x) : (infLeLeft U V) x = ⟨x.1, (@inf_le_left _ _ U V : _ ≤ _) x.2⟩ :=
  rfl

@[simp]
theorem inf_le_left_apply_mk (U V : Opens X) (x) (m) : (infLeLeft U V) ⟨x, m⟩ = ⟨x, (@inf_le_left _ _ U V : _ ≤ _) m⟩ :=
  rfl

@[simp]
theorem le_supr_apply_mk {ι : Type _} (U : ι → Opens X) (i : ι) (x) (m) :
    (leSupr U i) ⟨x, m⟩ = ⟨x, (le_supr U i : _) m⟩ :=
  rfl

/-- The functor from open sets in `X` to `Top`,
realising each open set as a topological space itself.
-/
def toTop (X : Top.{u}) : Opens X ⥤ Top where
  obj := fun U => ⟨U.val, inferInstance⟩
  map := fun U V i =>
    ⟨fun x => ⟨x.1, i.le x.2⟩, (Embedding.continuous_iff embedding_subtype_coe).2 continuous_induced_dom⟩

@[simp]
theorem to_Top_map (X : Top.{u}) {U V : Opens X} {f : U ⟶ V} {x} {h} : ((toTop X).map f) ⟨x, h⟩ = ⟨x, f.le h⟩ :=
  rfl

/-- The inclusion map from an open subset to the whole space, as a morphism in `Top`.
-/
@[simps]
def inclusion {X : Top.{u}} (U : Opens X) : (toTop X).obj U ⟶ X where
  toFun := _
  continuous_to_fun := continuous_subtype_coe

theorem open_embedding {X : Top.{u}} (U : Opens X) : OpenEmbedding (inclusion U) :=
  IsOpen.open_embedding_subtype_coe U.2

/-- The inclusion of the top open subset (i.e. the whole space) is an isomorphism.
-/
def inclusionTopIso (X : Top.{u}) : (toTop X).obj ⊤ ≅ X where
  Hom := inclusion ⊤
  inv := ⟨fun x => ⟨x, trivialₓ⟩, continuous_def.2 fun U ⟨S, hS, hSU⟩ => hSU ▸ hS⟩

/-- `opens.map f` gives the functor from open sets in Y to open set in X,
    given by taking preimages under f. -/
def map (f : X ⟶ Y) : Opens Y ⥤ Opens X where
  obj := fun U => ⟨f ⁻¹' U.val, U.property.preimage f.Continuous⟩
  map := fun U V i => ⟨⟨fun x h => i.le h⟩⟩

@[simp]
theorem map_obj (f : X ⟶ Y) (U) (p) : (map f).obj ⟨U, p⟩ = ⟨f ⁻¹' U, p.preimage f.Continuous⟩ :=
  rfl

@[simp]
theorem map_id_obj (U : Opens X) : (map (𝟙 X)).obj U = U :=
  let ⟨_, _⟩ := U
  rfl

@[simp]
theorem map_id_obj' (U) (p) : (map (𝟙 X)).obj ⟨U, p⟩ = ⟨U, p⟩ :=
  rfl

@[simp]
theorem map_id_obj_unop (U : (Opens X)ᵒᵖ) : (map (𝟙 X)).obj (unop U) = unop U :=
  let ⟨_, _⟩ := U.unop
  rfl

@[simp]
theorem op_map_id_obj (U : (Opens X)ᵒᵖ) : (map (𝟙 X)).op.obj U = U := by
  simp

/-- The inclusion `U ⟶ (map f).obj ⊤` as a morphism in the category of open sets.
-/
def leMapTop (f : X ⟶ Y) (U : Opens X) : U ⟶ (map f).obj ⊤ :=
  leTop U

@[simp]
theorem map_comp_obj (f : X ⟶ Y) (g : Y ⟶ Z) (U) : (map (f ≫ g)).obj U = (map f).obj ((map g).obj U) :=
  rfl

@[simp]
theorem map_comp_obj' (f : X ⟶ Y) (g : Y ⟶ Z) (U) (p) : (map (f ≫ g)).obj ⟨U, p⟩ = (map f).obj ((map g).obj ⟨U, p⟩) :=
  rfl

@[simp]
theorem map_comp_map (f : X ⟶ Y) (g : Y ⟶ Z) {U V} (i : U ⟶ V) : (map (f ≫ g)).map i = (map f).map ((map g).map i) :=
  rfl

@[simp]
theorem map_comp_obj_unop (f : X ⟶ Y) (g : Y ⟶ Z) (U) :
    (map (f ≫ g)).obj (unop U) = (map f).obj ((map g).obj (unop U)) :=
  rfl

@[simp]
theorem op_map_comp_obj (f : X ⟶ Y) (g : Y ⟶ Z) (U) : (map (f ≫ g)).op.obj U = (map f).op.obj ((map g).op.obj U) :=
  rfl

theorem map_supr (f : X ⟶ Y) {ι : Type _} (U : ι → Opens Y) : (map f).obj (supr U) = supr ((map f).obj ∘ U) := by
  apply Subtype.eq
  rw [supr_def, supr_def, map_obj]
  dsimp'
  rw [Set.preimage_Union]
  rfl

section

variable (X)

/-- The functor `opens X ⥤ opens X` given by taking preimages under the identity function
is naturally isomorphic to the identity functor.
-/
@[simps]
def mapId : map (𝟙 X) ≅ 𝟭 (Opens X) where
  Hom := { app := fun U => eqToHom (map_id_obj U) }
  inv := { app := fun U => eqToHom (map_id_obj U).symm }

theorem map_id_eq : map (𝟙 X) = 𝟭 (Opens X) := by
  unfold map
  congr
  ext
  rfl
  ext

end

/-- The natural isomorphism between taking preimages under `f ≫ g`, and the composite
of taking preimages under `g`, then preimages under `f`.
-/
@[simps]
def mapComp (f : X ⟶ Y) (g : Y ⟶ Z) : map (f ≫ g) ≅ map g ⋙ map f where
  Hom := { app := fun U => eqToHom (map_comp_obj f g U) }
  inv := { app := fun U => eqToHom (map_comp_obj f g U).symm }

theorem map_comp_eq (f : X ⟶ Y) (g : Y ⟶ Z) : map (f ≫ g) = map g ⋙ map f :=
  rfl

/-- If two continuous maps `f g : X ⟶ Y` are equal,
then the functors `opens Y ⥤ opens X` they induce are isomorphic.
-/
-- We could make `f g` implicit here, but it's nice to be able to see when
-- they are the identity (often!)
def mapIso (f g : X ⟶ Y) (h : f = g) : map f ≅ map g :=
  NatIso.ofComponents (fun U => eqToIso (congr_fun (congr_arg Functor.obj (congr_arg map h)) U))
    (by
      run_tac
        obviously)

theorem map_eq (f g : X ⟶ Y) (h : f = g) : map f = map g := by
  unfold map
  congr
  ext
  rw [h]
  rw [h]
  assumption'

@[simp]
theorem map_iso_refl (f : X ⟶ Y) (h) : mapIso f f h = Iso.refl (map _) :=
  rfl

@[simp]
theorem map_iso_hom_app (f g : X ⟶ Y) (h : f = g) (U : Opens Y) :
    (mapIso f g h).Hom.app U = eqToHom (congr_fun (congr_arg Functor.obj (congr_arg map h)) U) :=
  rfl

@[simp]
theorem map_iso_inv_app (f g : X ⟶ Y) (h : f = g) (U : Opens Y) :
    (mapIso f g h).inv.app U = eqToHom (congr_fun (congr_arg Functor.obj (congr_arg map h.symm)) U) :=
  rfl

/-- A homeomorphism of spaces gives an equivalence of categories of open sets. -/
@[simps]
def mapMapIso {X Y : Top.{u}} (H : X ≅ Y) : Opens Y ≌ Opens X where
  Functor := map H.Hom
  inverse := map H.inv
  unitIso :=
    NatIso.ofComponents
      (fun U =>
        eqToIso
          (by
            simp [← map, ← Set.preimage_preimage]))
      (by
        intro _ _ _
        simp )
  counitIso :=
    NatIso.ofComponents
      (fun U =>
        eqToIso
          (by
            simp [← map, ← Set.preimage_preimage]))
      (by
        intro _ _ _
        simp )

end TopologicalSpace.Opens

/-- An open map `f : X ⟶ Y` induces a functor `opens X ⥤ opens Y`.
-/
@[simps]
def IsOpenMap.functor {X Y : Top} {f : X ⟶ Y} (hf : IsOpenMap f) : Opens X ⥤ Opens Y where
  obj := fun U => ⟨f '' U, hf U U.2⟩
  map := fun U V h => ⟨⟨Set.image_subset _ h.down.down⟩⟩

/-- An open map `f : X ⟶ Y` induces an adjunction between `opens X` and `opens Y`.
-/
def IsOpenMap.adjunction {X Y : Top} {f : X ⟶ Y} (hf : IsOpenMap f) :
    Adjunction hf.Functor (TopologicalSpace.Opens.map f) :=
  Adjunction.mkOfUnitCounit
    { Unit := { app := fun U => hom_of_le fun x hxU => ⟨x, hxU, rfl⟩ },
      counit := { app := fun V => hom_of_le fun y ⟨x, hfxV, hxy⟩ => hxy ▸ hfxV } }

instance IsOpenMap.functorFullOfMono {X Y : Top} {f : X ⟶ Y} (hf : IsOpenMap f) [H : Mono f] :
    Full hf.Functor where preimage := fun U V i =>
    homOfLe fun x hx => by
      obtain ⟨y, hy, eq⟩ := i.le ⟨x, hx, rfl⟩
      exact (Top.mono_iff_injective f).mp H Eq ▸ hy

instance IsOpenMap.functor_faithful {X Y : Top} {f : X ⟶ Y} (hf : IsOpenMap f) : Faithful hf.Functor where

namespace TopologicalSpace.Opens

open TopologicalSpace

@[simp]
theorem open_embedding_obj_top {X : Top} (U : Opens X) : U.OpenEmbedding.IsOpenMap.Functor.obj ⊤ = U := by
  ext1
  exact set.image_univ.trans Subtype.range_coe

@[simp]
theorem inclusion_map_eq_top {X : Top} (U : Opens X) : (Opens.map U.inclusion).obj U = ⊤ := by
  ext1
  exact Subtype.coe_preimage_self _

@[simp]
theorem adjunction_counit_app_self {X : Top} (U : Opens X) :
    U.OpenEmbedding.IsOpenMap.Adjunction.counit.app U =
      eqToHom
        (by
          simp ) :=
  by
  ext

theorem inclusion_top_functor (X : Top) : (@Opens.open_embedding X ⊤).IsOpenMap.Functor = map (inclusionTopIso X).inv :=
  by
  apply functor.hext
  intro
  abstract obj_eq 
    ext
    exact ⟨fun ⟨⟨_, _⟩, h, rfl⟩ => h, fun h => ⟨⟨x, trivialₓ⟩, h, rfl⟩⟩
  intros
  apply Subsingleton.helimₓ
  congr 1
  iterate 2 
    apply inclusion_top_functor.obj_eq

end TopologicalSpace.Opens

