/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton, Mario Carneiro, Scott Morrison, Floris van Doorn
-/
import Mathbin.CategoryTheory.Adjunction.Basic
import Mathbin.CategoryTheory.Limits.Cones

/-!
# Limits and colimits

We set up the general theory of limits and colimits in a category.
In this introduction we only describe the setup for limits;
it is repeated, with slightly different names, for colimits.

The main structures defined in this file is
* `is_limit c`, for `c : cone F`, `F : J ⥤ C`, expressing that `c` is a limit cone,

See also `category_theory.limits.has_limits` which further builds:
* `limit_cone F`, which consists of a choice of cone for `F` and the fact it is a limit cone, and
* `has_limit F`, asserting the mere existence of some limit cone for `F`.

## Implementation
At present we simply say everything twice, in order to handle both limits and colimits.
It would be highly desirable to have some automation support,
e.g. a `@[dualize]` attribute that behaves similarly to `@[to_additive]`.

## References
* [Stacks: Limits and colimits](https://stacks.math.columbia.edu/tag/002D)

-/


noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Functor Opposite

namespace CategoryTheory.Limits

-- declare the `v`'s first; see `category_theory.category` for an explanation
universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {J : Type u₁} [Category.{v₁} J] {K : Type u₂} [Category.{v₂} K]

variable {C : Type u₃} [Category.{v₃} C]

variable {F : J ⥤ C}

/-- A cone `t` on `F` is a limit cone if each cone on `F` admits a unique
cone morphism to `t`.

See <https://stacks.math.columbia.edu/tag/002E>.
  -/
@[nolint has_inhabited_instance]
structure IsLimit (t : Cone F) where
  lift : ∀ s : Cone F, s.x ⟶ t.x
  fac' : ∀ (s : Cone F) (j : J), lift s ≫ t.π.app j = s.π.app j := by
    run_tac
      obviously
  uniq' : ∀ (s : Cone F) (m : s.x ⟶ t.x) (w : ∀ j : J, m ≫ t.π.app j = s.π.app j), m = lift s := by
    run_tac
      obviously

restate_axiom is_limit.fac'

attribute [simp, reassoc] is_limit.fac

restate_axiom is_limit.uniq'

namespace IsLimit

instance subsingleton {t : Cone F} : Subsingleton (IsLimit t) :=
  ⟨by
    intro P Q <;> cases P <;> cases Q <;> congr <;> ext <;> solve_by_elim⟩

/-- Given a natural transformation `α : F ⟶ G`, we give a morphism from the cone point
of any cone over `F` to the cone point of a limit cone over `G`. -/
def map {F G : J ⥤ C} (s : Cone F) {t : Cone G} (P : IsLimit t) (α : F ⟶ G) : s.x ⟶ t.x :=
  P.lift ((Cones.postcompose α).obj s)

@[simp, reassoc]
theorem map_π {F G : J ⥤ C} (c : Cone F) {d : Cone G} (hd : IsLimit d) (α : F ⟶ G) (j : J) :
    hd.map c α ≫ d.π.app j = c.π.app j ≫ α.app j :=
  fac _ _ _

theorem lift_self {c : Cone F} (t : IsLimit c) : t.lift c = 𝟙 c.x :=
  (t.uniq _ _ fun j => id_comp _).symm

/-- The universal morphism from any other cone to a limit cone. -/
-- Repackaging the definition in terms of cone morphisms.
@[simps]
def liftConeMorphism {t : Cone F} (h : IsLimit t) (s : Cone F) : s ⟶ t where Hom := h.lift s

theorem uniq_cone_morphism {s t : Cone F} (h : IsLimit t) {f f' : s ⟶ t} : f = f' :=
  have : ∀ {g : s ⟶ t}, g = h.liftConeMorphism s := by
    intro g <;> ext <;> exact h.uniq _ _ g.w
  this.trans this.symm

/-- Restating the definition of a limit cone in terms of the ∃! operator. -/
theorem exists_unique {t : Cone F} (h : IsLimit t) (s : Cone F) : ∃! l : s.x ⟶ t.x, ∀ j, l ≫ t.π.app j = s.π.app j :=
  ⟨h.lift s, h.fac s, h.uniq s⟩

/-- Noncomputably make a colimit cocone from the existence of unique factorizations. -/
def ofExistsUnique {t : Cone F} (ht : ∀ s : Cone F, ∃! l : s.x ⟶ t.x, ∀ j, l ≫ t.π.app j = s.π.app j) : IsLimit t := by
  choose s hs hs' using ht
  exact ⟨s, hs, hs'⟩

/-- Alternative constructor for `is_limit`,
providing a morphism of cones rather than a morphism between the cone points
and separately the factorisation condition.
-/
@[simps]
def mkConeMorphism {t : Cone F} (lift : ∀ s : Cone F, s ⟶ t) (uniq' : ∀ (s : Cone F) (m : s ⟶ t), m = lift s) :
    IsLimit t where
  lift := fun s => (lift s).Hom
  uniq' := fun s m w =>
    have : ConeMorphism.mk m w = lift s := by
      apply uniq'
    congr_arg ConeMorphism.hom this

/-- Limit cones on `F` are unique up to isomorphism. -/
@[simps]
def uniqueUpToIso {s t : Cone F} (P : IsLimit s) (Q : IsLimit t) : s ≅ t where
  Hom := Q.liftConeMorphism s
  inv := P.liftConeMorphism t
  hom_inv_id' := P.uniq_cone_morphism
  inv_hom_id' := Q.uniq_cone_morphism

/-- Any cone morphism between limit cones is an isomorphism. -/
theorem hom_is_iso {s t : Cone F} (P : IsLimit s) (Q : IsLimit t) (f : s ⟶ t) : IsIso f :=
  ⟨⟨P.liftConeMorphism t, ⟨P.uniq_cone_morphism, Q.uniq_cone_morphism⟩⟩⟩

/-- Limits of `F` are unique up to isomorphism. -/
def conePointUniqueUpToIso {s t : Cone F} (P : IsLimit s) (Q : IsLimit t) : s.x ≅ t.x :=
  (Cones.forget F).mapIso (uniqueUpToIso P Q)

@[simp, reassoc]
theorem cone_point_unique_up_to_iso_hom_comp {s t : Cone F} (P : IsLimit s) (Q : IsLimit t) (j : J) :
    (conePointUniqueUpToIso P Q).Hom ≫ t.π.app j = s.π.app j :=
  (uniqueUpToIso P Q).Hom.w _

@[simp, reassoc]
theorem cone_point_unique_up_to_iso_inv_comp {s t : Cone F} (P : IsLimit s) (Q : IsLimit t) (j : J) :
    (conePointUniqueUpToIso P Q).inv ≫ s.π.app j = t.π.app j :=
  (uniqueUpToIso P Q).inv.w _

@[simp, reassoc]
theorem lift_comp_cone_point_unique_up_to_iso_hom {r s t : Cone F} (P : IsLimit s) (Q : IsLimit t) :
    P.lift r ≫ (conePointUniqueUpToIso P Q).Hom = Q.lift r :=
  Q.uniq _ _
    (by
      simp )

@[simp, reassoc]
theorem lift_comp_cone_point_unique_up_to_iso_inv {r s t : Cone F} (P : IsLimit s) (Q : IsLimit t) :
    Q.lift r ≫ (conePointUniqueUpToIso P Q).inv = P.lift r :=
  P.uniq _ _
    (by
      simp )

/-- Transport evidence that a cone is a limit cone across an isomorphism of cones. -/
def ofIsoLimit {r t : Cone F} (P : IsLimit r) (i : r ≅ t) : IsLimit t :=
  IsLimit.mkConeMorphism (fun s => P.liftConeMorphism s ≫ i.Hom) fun s m => by
    rw [← i.comp_inv_eq] <;> apply P.uniq_cone_morphism

@[simp]
theorem of_iso_limit_lift {r t : Cone F} (P : IsLimit r) (i : r ≅ t) (s) :
    (P.ofIsoLimit i).lift s = P.lift s ≫ i.Hom.Hom :=
  rfl

/-- Isomorphism of cones preserves whether or not they are limiting cones. -/
def equivIsoLimit {r t : Cone F} (i : r ≅ t) : IsLimit r ≃ IsLimit t where
  toFun := fun h => h.ofIsoLimit i
  invFun := fun h => h.ofIsoLimit i.symm
  left_inv := by
    tidy
  right_inv := by
    tidy

@[simp]
theorem equiv_iso_limit_apply {r t : Cone F} (i : r ≅ t) (P : IsLimit r) : equivIsoLimit i P = P.ofIsoLimit i :=
  rfl

@[simp]
theorem equiv_iso_limit_symm_apply {r t : Cone F} (i : r ≅ t) (P : IsLimit t) :
    (equivIsoLimit i).symm P = P.ofIsoLimit i.symm :=
  rfl

/-- If the canonical morphism from a cone point to a limiting cone point is an iso, then the
first cone was limiting also.
-/
def ofPointIso {r t : Cone F} (P : IsLimit r) [i : IsIso (P.lift t)] : IsLimit t :=
  ofIsoLimit P
    (by
      have : is_iso (P.lift_cone_morphism t).Hom := i
      have : is_iso (P.lift_cone_morphism t) := cones.cone_iso_of_hom_iso _
      symm
      apply as_iso (P.lift_cone_morphism t))

variable {t : Cone F}

theorem hom_lift (h : IsLimit t) {W : C} (m : W ⟶ t.x) :
    m = h.lift { x := W, π := { app := fun b => m ≫ t.π.app b } } :=
  h.uniq { x := W, π := { app := fun b => m ≫ t.π.app b } } m fun b => rfl

/-- Two morphisms into a limit are equal if their compositions with
  each cone morphism are equal. -/
theorem hom_ext (h : IsLimit t) {W : C} {f f' : W ⟶ t.x} (w : ∀ j, f ≫ t.π.app j = f' ≫ t.π.app j) : f = f' := by
  rw [h.hom_lift f, h.hom_lift f'] <;> congr <;> exact funext w

/-- Given a right adjoint functor between categories of cones,
the image of a limit cone is a limit cone.
-/
def ofRightAdjoint {D : Type u₄} [Category.{v₄} D] {G : K ⥤ D} (h : Cone G ⥤ Cone F) [IsRightAdjoint h] {c : Cone G}
    (t : IsLimit c) : IsLimit (h.obj c) :=
  mkConeMorphism (fun s => (Adjunction.ofRightAdjoint h).homEquiv s c (t.liftConeMorphism _)) fun s m =>
    (Adjunction.eq_hom_equiv_apply _ _ _).2 t.uniq_cone_morphism

/-- Given two functors which have equivalent categories of cones, we can transport a limiting cone
across the equivalence.
-/
def ofConeEquiv {D : Type u₄} [Category.{v₄} D] {G : K ⥤ D} (h : Cone G ≌ Cone F) {c : Cone G} :
    IsLimit (h.Functor.obj c) ≃ IsLimit c where
  toFun := fun P => ofIsoLimit (ofRightAdjoint h.inverse P) (h.unitIso.symm.app c)
  invFun := ofRightAdjoint h.Functor
  left_inv := by
    tidy
  right_inv := by
    tidy

@[simp]
theorem of_cone_equiv_apply_desc {D : Type u₄} [Category.{v₄} D] {G : K ⥤ D} (h : Cone G ≌ Cone F) {c : Cone G}
    (P : IsLimit (h.Functor.obj c)) (s) :
    (ofConeEquiv h P).lift s =
      ((h.unitIso.Hom.app s).Hom ≫ (h.Functor.inv.map (P.liftConeMorphism (h.Functor.obj s))).Hom) ≫
        (h.unitIso.inv.app c).Hom :=
  rfl

@[simp]
theorem of_cone_equiv_symm_apply_desc {D : Type u₄} [Category.{v₄} D] {G : K ⥤ D} (h : Cone G ≌ Cone F) {c : Cone G}
    (P : IsLimit c) (s) :
    ((ofConeEquiv h).symm P).lift s =
      (h.counitIso.inv.app s).Hom ≫ (h.Functor.map (P.liftConeMorphism (h.inverse.obj s))).Hom :=
  rfl

/-- A cone postcomposed with a natural isomorphism is a limit cone if and only if the original cone is.
-/
def postcomposeHomEquiv {F G : J ⥤ C} (α : F ≅ G) (c : Cone F) :
    IsLimit ((Cones.postcompose α.Hom).obj c) ≃ IsLimit c :=
  ofConeEquiv (Cones.postcomposeEquivalence α)

/-- A cone postcomposed with the inverse of a natural isomorphism is a limit cone if and only if
the original cone is.
-/
def postcomposeInvEquiv {F G : J ⥤ C} (α : F ≅ G) (c : Cone G) :
    IsLimit ((Cones.postcompose α.inv).obj c) ≃ IsLimit c :=
  postcomposeHomEquiv α.symm c

/-- Constructing an equivalence `is_limit c ≃ is_limit d` from a natural isomorphism
between the underlying functors, and then an isomorphism between `c` transported along this and `d`.
-/
def equivOfNatIsoOfIso {F G : J ⥤ C} (α : F ≅ G) (c : Cone F) (d : Cone G) (w : (Cones.postcompose α.Hom).obj c ≅ d) :
    IsLimit c ≃ IsLimit d :=
  (postcomposeHomEquiv α _).symm.trans (equivIsoLimit w)

/-- The cone points of two limit cones for naturally isomorphic functors
are themselves isomorphic.
-/
@[simps]
def conePointsIsoOfNatIso {F G : J ⥤ C} {s : Cone F} {t : Cone G} (P : IsLimit s) (Q : IsLimit t) (w : F ≅ G) :
    s.x ≅ t.x where
  Hom := Q.map s w.Hom
  inv := P.map t w.inv
  hom_inv_id' :=
    P.hom_ext
      (by
        tidy)
  inv_hom_id' :=
    Q.hom_ext
      (by
        tidy)

@[reassoc]
theorem cone_points_iso_of_nat_iso_hom_comp {F G : J ⥤ C} {s : Cone F} {t : Cone G} (P : IsLimit s) (Q : IsLimit t)
    (w : F ≅ G) (j : J) : (conePointsIsoOfNatIso P Q w).Hom ≫ t.π.app j = s.π.app j ≫ w.Hom.app j := by
  simp

@[reassoc]
theorem cone_points_iso_of_nat_iso_inv_comp {F G : J ⥤ C} {s : Cone F} {t : Cone G} (P : IsLimit s) (Q : IsLimit t)
    (w : F ≅ G) (j : J) : (conePointsIsoOfNatIso P Q w).inv ≫ s.π.app j = t.π.app j ≫ w.inv.app j := by
  simp

@[reassoc]
theorem lift_comp_cone_points_iso_of_nat_iso_hom {F G : J ⥤ C} {r s : Cone F} {t : Cone G} (P : IsLimit s)
    (Q : IsLimit t) (w : F ≅ G) : P.lift r ≫ (conePointsIsoOfNatIso P Q w).Hom = Q.map r w.Hom :=
  Q.hom_ext
    (by
      simp )

@[reassoc]
theorem lift_comp_cone_points_iso_of_nat_iso_inv {F G : J ⥤ C} {r s : Cone G} {t : Cone F} (P : IsLimit t)
    (Q : IsLimit s) (w : F ≅ G) : Q.lift r ≫ (conePointsIsoOfNatIso P Q w).inv = P.map r w.inv :=
  P.hom_ext
    (by
      simp )

section Equivalenceₓ

open CategoryTheory.Equivalence

/-- If `s : cone F` is a limit cone, so is `s` whiskered by an equivalence `e`.
-/
def whiskerEquivalence {s : Cone F} (P : IsLimit s) (e : K ≌ J) : IsLimit (s.whisker e.Functor) :=
  ofRightAdjoint (Cones.whiskeringEquivalence e).Functor P

/-- If `s : cone F` whiskered by an equivalence `e` is a limit cone, so is `s`.
-/
def ofWhiskerEquivalence {s : Cone F} (e : K ≌ J) (P : IsLimit (s.whisker e.Functor)) : IsLimit s :=
  equivIsoLimit ((Cones.whiskeringEquivalence e).unitIso.app s).symm
    (ofRightAdjoint (Cones.whiskeringEquivalence e).inverse P : _)

/-- Given an equivalence of diagrams `e`, `s` is a limit cone iff `s.whisker e.functor` is.
-/
def whiskerEquivalenceEquiv {s : Cone F} (e : K ≌ J) : IsLimit s ≃ IsLimit (s.whisker e.Functor) :=
  ⟨fun h => h.whiskerEquivalence e, ofWhiskerEquivalence e, by
    tidy, by
    tidy⟩

/-- We can prove two cone points `(s : cone F).X` and `(t.cone G).X` are isomorphic if
* both cones are limit cones
* their indexing categories are equivalent via some `e : J ≌ K`,
* the triangle of functors commutes up to a natural isomorphism: `e.functor ⋙ G ≅ F`.

This is the most general form of uniqueness of cone points,
allowing relabelling of both the indexing category (up to equivalence)
and the functor (up to natural isomorphism).
-/
@[simps]
def conePointsIsoOfEquivalence {F : J ⥤ C} {s : Cone F} {G : K ⥤ C} {t : Cone G} (P : IsLimit s) (Q : IsLimit t)
    (e : J ≌ K) (w : e.Functor ⋙ G ≅ F) : s.x ≅ t.x :=
  let w' : e.inverse ⋙ F ≅ G := (isoWhiskerLeft e.inverse w).symm ≪≫ invFunIdAssoc e G
  { Hom := Q.lift ((Cones.equivalenceOfReindexing e.symm w').Functor.obj s),
    inv := P.lift ((Cones.equivalenceOfReindexing e w).Functor.obj t),
    hom_inv_id' := by
      apply hom_ext P
      intro j
      dsimp'
      simp only [← limits.cone.whisker_π, ← limits.cones.postcompose_obj_π, ← fac, ← whisker_left_app, ← assoc, ←
        id_comp, ← inv_fun_id_assoc_hom_app, ← fac_assoc, ← nat_trans.comp_app]
      rw [counit_app_functor, ← functor.comp_map, w.hom.naturality]
      simp ,
    inv_hom_id' := by
      apply hom_ext Q
      tidy }

end Equivalenceₓ

/-- The universal property of a limit cone: a map `W ⟶ X` is the same as
  a cone on `F` with vertex `W`. -/
def homIso (h : IsLimit t) (W : C) : ULift.{u₁} (W ⟶ t.x : Type v₃) ≅ (const J).obj W ⟶ F where
  Hom := fun f => (t.extend f.down).π
  inv := fun π => ⟨h.lift { x := W, π }⟩
  hom_inv_id' := by
    ext f <;> apply h.hom_ext <;> intro j <;> simp <;> dsimp' <;> rfl

@[simp]
theorem hom_iso_hom (h : IsLimit t) {W : C} (f : ULift.{u₁} (W ⟶ t.x)) :
    (IsLimit.homIso h W).Hom f = (t.extend f.down).π :=
  rfl

/-- The limit of `F` represents the functor taking `W` to
  the set of cones on `F` with vertex `W`. -/
def natIso (h : IsLimit t) : yoneda.obj t.x ⋙ ulift_functor.{u₁} ≅ F.cones :=
  NatIso.ofComponents (fun W => IsLimit.homIso h (unop W))
    (by
      tidy)

/-- Another, more explicit, formulation of the universal property of a limit cone.
See also `hom_iso`.
-/
def homIso' (h : IsLimit t) (W : C) :
    ULift.{u₁} (W ⟶ t.x : Type v₃) ≅ { p : ∀ j, W ⟶ F.obj j // ∀ {j j'} (f : j ⟶ j'), p j ≫ F.map f = p j' } :=
  h.homIso W ≪≫
    { Hom := fun π =>
        ⟨fun j => π.app j, fun j j' f => by
          convert ← (π.naturality f).symm <;> apply id_comp⟩,
      inv := fun p =>
        { app := fun j => p.1 j,
          naturality' := fun j j' f => by
            dsimp'
            rw [id_comp]
            exact (p.2 f).symm } }

/-- If G : C → D is a faithful functor which sends t to a limit cone,
  then it suffices to check that the induced maps for the image of t
  can be lifted to maps of C. -/
def ofFaithful {t : Cone F} {D : Type u₄} [Category.{v₄} D] (G : C ⥤ D) [Faithful G] (ht : IsLimit (G.mapCone t))
    (lift : ∀ s : Cone F, s.x ⟶ t.x) (h : ∀ s, G.map (lift s) = ht.lift (G.mapCone s)) : IsLimit t :=
  { lift,
    fac' := fun s j => by
      apply G.map_injective <;> rw [G.map_comp, h] <;> apply ht.fac,
    uniq' := fun s m w => by
      apply G.map_injective
      rw [h]
      refine' ht.uniq (G.map_cone s) _ fun j => _
      convert ← congr_arg (fun f => G.map f) (w j)
      apply G.map_comp }

/-- If `F` and `G` are naturally isomorphic, then `F.map_cone c` being a limit implies
`G.map_cone c` is also a limit.
-/
def mapConeEquiv {D : Type u₄} [Category.{v₄} D] {K : J ⥤ C} {F G : C ⥤ D} (h : F ≅ G) {c : Cone K}
    (t : IsLimit (F.mapCone c)) : IsLimit (G.mapCone c) := by
  apply postcompose_inv_equiv (iso_whisker_left K h : _) (G.map_cone c) _
  apply t.of_iso_limit (postcompose_whisker_left_map_cone h.symm c).symm

/-- A cone is a limit cone exactly if
there is a unique cone morphism from any other cone.
-/
def isoUniqueConeMorphism {t : Cone F} : IsLimit t ≅ ∀ s, Unique (s ⟶ t) where
  Hom := fun h s => { default := h.liftConeMorphism s, uniq := fun _ => h.uniq_cone_morphism }
  inv := fun h =>
    { lift := fun s => (h s).default.Hom, uniq' := fun s f w => congr_arg ConeMorphism.hom ((h s).uniq ⟨f, w⟩) }

namespace OfNatIso

variable {X : C} (h : yoneda.obj X ⋙ ulift_functor.{u₁} ≅ F.cones)

/-- If `F.cones` is represented by `X`, each morphism `f : Y ⟶ X` gives a cone with cone point
`Y`. -/
def coneOfHom {Y : C} (f : Y ⟶ X) : Cone F where
  x := Y
  π := h.Hom.app (op Y) ⟨f⟩

/-- If `F.cones` is represented by `X`, each cone `s` gives a morphism `s.X ⟶ X`. -/
def homOfCone (s : Cone F) : s.x ⟶ X :=
  (h.inv.app (op s.x) s.π).down

@[simp]
theorem cone_of_hom_of_cone (s : Cone F) : coneOfHom h (homOfCone h s) = s := by
  dsimp' [← cone_of_hom, ← hom_of_cone]
  cases s
  congr
  dsimp'
  convert congr_fun (congr_fun (congr_arg nat_trans.app h.inv_hom_id) (op s_X)) s_π
  exact ULift.up_down _

@[simp]
theorem hom_of_cone_of_hom {Y : C} (f : Y ⟶ X) : homOfCone h (coneOfHom h f) = f :=
  congr_arg ULift.down (congr_fun (congr_fun (congr_arg NatTrans.app h.hom_inv_id) (op Y)) ⟨f⟩ : _)

/-- If `F.cones` is represented by `X`, the cone corresponding to the identity morphism on `X`
will be a limit cone. -/
def limitCone : Cone F :=
  coneOfHom h (𝟙 X)

/-- If `F.cones` is represented by `X`, the cone corresponding to a morphism `f : Y ⟶ X` is
the limit cone extended by `f`. -/
theorem cone_of_hom_fac {Y : C} (f : Y ⟶ X) : coneOfHom h f = (limitCone h).extend f := by
  dsimp' [← cone_of_hom, ← limit_cone, ← cone.extend]
  congr with j
  have t := congr_fun (h.hom.naturality f.op) ⟨𝟙 X⟩
  dsimp'  at t
  simp only [← comp_id] at t
  rw [congr_fun (congr_arg nat_trans.app t) j]
  rfl

/-- If `F.cones` is represented by `X`, any cone is the extension of the limit cone by the
corresponding morphism. -/
theorem cone_fac (s : Cone F) : (limitCone h).extend (homOfCone h s) = s := by
  rw [← cone_of_hom_of_cone h s]
  conv_lhs => simp only [← hom_of_cone_of_hom]
  apply (cone_of_hom_fac _ _).symm

end OfNatIso

section

open OfNatIso

/-- If `F.cones` is representable, then the cone corresponding to the identity morphism on
the representing object is a limit cone.
-/
def ofNatIso {X : C} (h : yoneda.obj X ⋙ ulift_functor.{u₁} ≅ F.cones) : IsLimit (limitCone h) where
  lift := fun s => homOfCone h s
  fac' := fun s j => by
    have h := cone_fac h s
    cases s
    injection h with h₁ h₂
    simp only [← heq_iff_eq] at h₂
    conv_rhs => rw [← h₂]
    rfl
  uniq' := fun s m w => by
    rw [← hom_of_cone_of_hom h m]
    congr
    rw [cone_of_hom_fac]
    dsimp' [← cone.extend]
    cases s
    congr with j
    exact w j

end

end IsLimit

/-- A cocone `t` on `F` is a colimit cocone if each cocone on `F` admits a unique
cocone morphism from `t`.

See <https://stacks.math.columbia.edu/tag/002F>.
-/
@[nolint has_inhabited_instance]
structure IsColimit (t : Cocone F) where
  desc : ∀ s : Cocone F, t.x ⟶ s.x
  fac' : ∀ (s : Cocone F) (j : J), t.ι.app j ≫ desc s = s.ι.app j := by
    run_tac
      obviously
  uniq' : ∀ (s : Cocone F) (m : t.x ⟶ s.x) (w : ∀ j : J, t.ι.app j ≫ m = s.ι.app j), m = desc s := by
    run_tac
      obviously

restate_axiom is_colimit.fac'

attribute [simp, reassoc] is_colimit.fac

restate_axiom is_colimit.uniq'

namespace IsColimit

instance subsingleton {t : Cocone F} : Subsingleton (IsColimit t) :=
  ⟨by
    intro P Q <;> cases P <;> cases Q <;> congr <;> ext <;> solve_by_elim⟩

/-- Given a natural transformation `α : F ⟶ G`, we give a morphism from the cocone point
of a colimit cocone over `F` to the cocone point of any cocone over `G`. -/
def map {F G : J ⥤ C} {s : Cocone F} (P : IsColimit s) (t : Cocone G) (α : F ⟶ G) : s.x ⟶ t.x :=
  P.desc ((Cocones.precompose α).obj t)

@[simp, reassoc]
theorem ι_map {F G : J ⥤ C} {c : Cocone F} (hc : IsColimit c) (d : Cocone G) (α : F ⟶ G) (j : J) :
    c.ι.app j ≫ IsColimit.map hc d α = α.app j ≫ d.ι.app j :=
  fac _ _ _

@[simp]
theorem desc_self {t : Cocone F} (h : IsColimit t) : h.desc t = 𝟙 t.x :=
  (h.uniq _ _ fun j => comp_id _).symm

/-- The universal morphism from a colimit cocone to any other cocone. -/
-- Repackaging the definition in terms of cocone morphisms.
@[simps]
def descCoconeMorphism {t : Cocone F} (h : IsColimit t) (s : Cocone F) : t ⟶ s where Hom := h.desc s

theorem uniq_cocone_morphism {s t : Cocone F} (h : IsColimit t) {f f' : t ⟶ s} : f = f' :=
  have : ∀ {g : t ⟶ s}, g = h.descCoconeMorphism s := by
    intro g <;> ext <;> exact h.uniq _ _ g.w
  this.trans this.symm

/-- Restating the definition of a colimit cocone in terms of the ∃! operator. -/
theorem exists_unique {t : Cocone F} (h : IsColimit t) (s : Cocone F) :
    ∃! d : t.x ⟶ s.x, ∀ j, t.ι.app j ≫ d = s.ι.app j :=
  ⟨h.desc s, h.fac s, h.uniq s⟩

/-- Noncomputably make a colimit cocone from the existence of unique factorizations. -/
def ofExistsUnique {t : Cocone F} (ht : ∀ s : Cocone F, ∃! d : t.x ⟶ s.x, ∀ j, t.ι.app j ≫ d = s.ι.app j) :
    IsColimit t := by
  choose s hs hs' using ht
  exact ⟨s, hs, hs'⟩

/-- Alternative constructor for `is_colimit`,
providing a morphism of cocones rather than a morphism between the cocone points
and separately the factorisation condition.
-/
@[simps]
def mkCoconeMorphism {t : Cocone F} (desc : ∀ s : Cocone F, t ⟶ s) (uniq' : ∀ (s : Cocone F) (m : t ⟶ s), m = desc s) :
    IsColimit t where
  desc := fun s => (desc s).Hom
  uniq' := fun s m w =>
    have : CoconeMorphism.mk m w = desc s := by
      apply uniq'
    congr_arg CoconeMorphism.hom this

/-- Colimit cocones on `F` are unique up to isomorphism. -/
@[simps]
def uniqueUpToIso {s t : Cocone F} (P : IsColimit s) (Q : IsColimit t) : s ≅ t where
  Hom := P.descCoconeMorphism t
  inv := Q.descCoconeMorphism s
  hom_inv_id' := P.uniq_cocone_morphism
  inv_hom_id' := Q.uniq_cocone_morphism

/-- Any cocone morphism between colimit cocones is an isomorphism. -/
theorem hom_is_iso {s t : Cocone F} (P : IsColimit s) (Q : IsColimit t) (f : s ⟶ t) : IsIso f :=
  ⟨⟨Q.descCoconeMorphism s, ⟨P.uniq_cocone_morphism, Q.uniq_cocone_morphism⟩⟩⟩

/-- Colimits of `F` are unique up to isomorphism. -/
def coconePointUniqueUpToIso {s t : Cocone F} (P : IsColimit s) (Q : IsColimit t) : s.x ≅ t.x :=
  (Cocones.forget F).mapIso (uniqueUpToIso P Q)

@[simp, reassoc]
theorem comp_cocone_point_unique_up_to_iso_hom {s t : Cocone F} (P : IsColimit s) (Q : IsColimit t) (j : J) :
    s.ι.app j ≫ (coconePointUniqueUpToIso P Q).Hom = t.ι.app j :=
  (uniqueUpToIso P Q).Hom.w _

@[simp, reassoc]
theorem comp_cocone_point_unique_up_to_iso_inv {s t : Cocone F} (P : IsColimit s) (Q : IsColimit t) (j : J) :
    t.ι.app j ≫ (coconePointUniqueUpToIso P Q).inv = s.ι.app j :=
  (uniqueUpToIso P Q).inv.w _

@[simp, reassoc]
theorem cocone_point_unique_up_to_iso_hom_desc {r s t : Cocone F} (P : IsColimit s) (Q : IsColimit t) :
    (coconePointUniqueUpToIso P Q).Hom ≫ Q.desc r = P.desc r :=
  P.uniq _ _
    (by
      simp )

@[simp, reassoc]
theorem cocone_point_unique_up_to_iso_inv_desc {r s t : Cocone F} (P : IsColimit s) (Q : IsColimit t) :
    (coconePointUniqueUpToIso P Q).inv ≫ P.desc r = Q.desc r :=
  Q.uniq _ _
    (by
      simp )

/-- Transport evidence that a cocone is a colimit cocone across an isomorphism of cocones. -/
def ofIsoColimit {r t : Cocone F} (P : IsColimit r) (i : r ≅ t) : IsColimit t :=
  IsColimit.mkCoconeMorphism (fun s => i.inv ≫ P.descCoconeMorphism s) fun s m => by
    rw [i.eq_inv_comp] <;> apply P.uniq_cocone_morphism

@[simp]
theorem of_iso_colimit_desc {r t : Cocone F} (P : IsColimit r) (i : r ≅ t) (s) :
    (P.ofIsoColimit i).desc s = i.inv.Hom ≫ P.desc s :=
  rfl

/-- Isomorphism of cocones preserves whether or not they are colimiting cocones. -/
def equivIsoColimit {r t : Cocone F} (i : r ≅ t) : IsColimit r ≃ IsColimit t where
  toFun := fun h => h.ofIsoColimit i
  invFun := fun h => h.ofIsoColimit i.symm
  left_inv := by
    tidy
  right_inv := by
    tidy

@[simp]
theorem equiv_iso_colimit_apply {r t : Cocone F} (i : r ≅ t) (P : IsColimit r) :
    equivIsoColimit i P = P.ofIsoColimit i :=
  rfl

@[simp]
theorem equiv_iso_colimit_symm_apply {r t : Cocone F} (i : r ≅ t) (P : IsColimit t) :
    (equivIsoColimit i).symm P = P.ofIsoColimit i.symm :=
  rfl

/-- If the canonical morphism to a cocone point from a colimiting cocone point is an iso, then the
first cocone was colimiting also.
-/
def ofPointIso {r t : Cocone F} (P : IsColimit r) [i : IsIso (P.desc t)] : IsColimit t :=
  ofIsoColimit P
    (by
      have : is_iso (P.desc_cocone_morphism t).Hom := i
      have : is_iso (P.desc_cocone_morphism t) := cocones.cocone_iso_of_hom_iso _
      apply as_iso (P.desc_cocone_morphism t))

variable {t : Cocone F}

theorem hom_desc (h : IsColimit t) {W : C} (m : t.x ⟶ W) :
    m =
      h.desc
        { x := W,
          ι :=
            { app := fun b => t.ι.app b ≫ m,
              naturality' := by
                intros <;> erw [← assoc, t.ι.naturality, comp_id, comp_id] } } :=
  h.uniq { x := W, ι := { app := fun b => t.ι.app b ≫ m, naturality' := _ } } m fun b => rfl

/-- Two morphisms out of a colimit are equal if their compositions with
  each cocone morphism are equal. -/
theorem hom_ext (h : IsColimit t) {W : C} {f f' : t.x ⟶ W} (w : ∀ j, t.ι.app j ≫ f = t.ι.app j ≫ f') : f = f' := by
  rw [h.hom_desc f, h.hom_desc f'] <;> congr <;> exact funext w

/-- Given a left adjoint functor between categories of cocones,
the image of a colimit cocone is a colimit cocone.
-/
def ofLeftAdjoint {D : Type u₄} [Category.{v₄} D] {G : K ⥤ D} (h : Cocone G ⥤ Cocone F) [IsLeftAdjoint h] {c : Cocone G}
    (t : IsColimit c) : IsColimit (h.obj c) :=
  mkCoconeMorphism (fun s => ((Adjunction.ofLeftAdjoint h).homEquiv c s).symm (t.descCoconeMorphism _)) fun s m =>
    (Adjunction.hom_equiv_apply_eq _ _ _).1 t.uniq_cocone_morphism

/-- Given two functors which have equivalent categories of cocones,
we can transport a colimiting cocone across the equivalence.
-/
def ofCoconeEquiv {D : Type u₄} [Category.{v₄} D] {G : K ⥤ D} (h : Cocone G ≌ Cocone F) {c : Cocone G} :
    IsColimit (h.Functor.obj c) ≃ IsColimit c where
  toFun := fun P => ofIsoColimit (ofLeftAdjoint h.inverse P) (h.unitIso.symm.app c)
  invFun := ofLeftAdjoint h.Functor
  left_inv := by
    tidy
  right_inv := by
    tidy

@[simp]
theorem of_cocone_equiv_apply_desc {D : Type u₄} [Category.{v₄} D] {G : K ⥤ D} (h : Cocone G ≌ Cocone F) {c : Cocone G}
    (P : IsColimit (h.Functor.obj c)) (s) :
    (ofCoconeEquiv h P).desc s =
      (h.Unit.app c).Hom ≫ (h.inverse.map (P.descCoconeMorphism (h.Functor.obj s))).Hom ≫ (h.unitInv.app s).Hom :=
  rfl

@[simp]
theorem of_cocone_equiv_symm_apply_desc {D : Type u₄} [Category.{v₄} D] {G : K ⥤ D} (h : Cocone G ≌ Cocone F)
    {c : Cocone G} (P : IsColimit c) (s) :
    ((ofCoconeEquiv h).symm P).desc s =
      (h.Functor.map (P.descCoconeMorphism (h.inverse.obj s))).Hom ≫ (h.counit.app s).Hom :=
  rfl

/-- A cocone precomposed with a natural isomorphism is a colimit cocone
if and only if the original cocone is.
-/
def precomposeHomEquiv {F G : J ⥤ C} (α : F ≅ G) (c : Cocone G) :
    IsColimit ((Cocones.precompose α.Hom).obj c) ≃ IsColimit c :=
  ofCoconeEquiv (Cocones.precomposeEquivalence α)

/-- A cocone precomposed with the inverse of a natural isomorphism is a colimit cocone
if and only if the original cocone is.
-/
def precomposeInvEquiv {F G : J ⥤ C} (α : F ≅ G) (c : Cocone F) :
    IsColimit ((Cocones.precompose α.inv).obj c) ≃ IsColimit c :=
  precomposeHomEquiv α.symm c

/-- Constructing an equivalence `is_colimit c ≃ is_colimit d` from a natural isomorphism
between the underlying functors, and then an isomorphism between `c` transported along this and `d`.
-/
def equivOfNatIsoOfIso {F G : J ⥤ C} (α : F ≅ G) (c : Cocone F) (d : Cocone G)
    (w : (Cocones.precompose α.inv).obj c ≅ d) : IsColimit c ≃ IsColimit d :=
  (precomposeInvEquiv α _).symm.trans (equivIsoColimit w)

/-- The cocone points of two colimit cocones for naturally isomorphic functors
are themselves isomorphic.
-/
@[simps]
def coconePointsIsoOfNatIso {F G : J ⥤ C} {s : Cocone F} {t : Cocone G} (P : IsColimit s) (Q : IsColimit t)
    (w : F ≅ G) : s.x ≅ t.x where
  Hom := P.map t w.Hom
  inv := Q.map s w.inv
  hom_inv_id' :=
    P.hom_ext
      (by
        tidy)
  inv_hom_id' :=
    Q.hom_ext
      (by
        tidy)

@[reassoc]
theorem comp_cocone_points_iso_of_nat_iso_hom {F G : J ⥤ C} {s : Cocone F} {t : Cocone G} (P : IsColimit s)
    (Q : IsColimit t) (w : F ≅ G) (j : J) : s.ι.app j ≫ (coconePointsIsoOfNatIso P Q w).Hom = w.Hom.app j ≫ t.ι.app j :=
  by
  simp

@[reassoc]
theorem comp_cocone_points_iso_of_nat_iso_inv {F G : J ⥤ C} {s : Cocone F} {t : Cocone G} (P : IsColimit s)
    (Q : IsColimit t) (w : F ≅ G) (j : J) : t.ι.app j ≫ (coconePointsIsoOfNatIso P Q w).inv = w.inv.app j ≫ s.ι.app j :=
  by
  simp

@[reassoc]
theorem cocone_points_iso_of_nat_iso_hom_desc {F G : J ⥤ C} {s : Cocone F} {r t : Cocone G} (P : IsColimit s)
    (Q : IsColimit t) (w : F ≅ G) : (coconePointsIsoOfNatIso P Q w).Hom ≫ Q.desc r = P.map _ w.Hom :=
  P.hom_ext
    (by
      simp )

@[reassoc]
theorem cocone_points_iso_of_nat_iso_inv_desc {F G : J ⥤ C} {s : Cocone G} {r t : Cocone F} (P : IsColimit t)
    (Q : IsColimit s) (w : F ≅ G) : (coconePointsIsoOfNatIso P Q w).inv ≫ P.desc r = Q.map _ w.inv :=
  Q.hom_ext
    (by
      simp )

section Equivalenceₓ

open CategoryTheory.Equivalence

/-- If `s : cocone F` is a colimit cocone, so is `s` whiskered by an equivalence `e`.
-/
def whiskerEquivalence {s : Cocone F} (P : IsColimit s) (e : K ≌ J) : IsColimit (s.whisker e.Functor) :=
  ofLeftAdjoint (Cocones.whiskeringEquivalence e).Functor P

/-- If `s : cocone F` whiskered by an equivalence `e` is a colimit cocone, so is `s`.
-/
def ofWhiskerEquivalence {s : Cocone F} (e : K ≌ J) (P : IsColimit (s.whisker e.Functor)) : IsColimit s :=
  equivIsoColimit ((Cocones.whiskeringEquivalence e).unitIso.app s).symm
    (ofLeftAdjoint (Cocones.whiskeringEquivalence e).inverse P : _)

/-- Given an equivalence of diagrams `e`, `s` is a colimit cocone iff `s.whisker e.functor` is.
-/
def whiskerEquivalenceEquiv {s : Cocone F} (e : K ≌ J) : IsColimit s ≃ IsColimit (s.whisker e.Functor) :=
  ⟨fun h => h.whiskerEquivalence e, ofWhiskerEquivalence e, by
    tidy, by
    tidy⟩

/-- We can prove two cocone points `(s : cocone F).X` and `(t.cocone G).X` are isomorphic if
* both cocones are colimit cocones
* their indexing categories are equivalent via some `e : J ≌ K`,
* the triangle of functors commutes up to a natural isomorphism: `e.functor ⋙ G ≅ F`.

This is the most general form of uniqueness of cocone points,
allowing relabelling of both the indexing category (up to equivalence)
and the functor (up to natural isomorphism).
-/
@[simps]
def coconePointsIsoOfEquivalence {F : J ⥤ C} {s : Cocone F} {G : K ⥤ C} {t : Cocone G} (P : IsColimit s)
    (Q : IsColimit t) (e : J ≌ K) (w : e.Functor ⋙ G ≅ F) : s.x ≅ t.x :=
  let w' : e.inverse ⋙ F ≅ G := (isoWhiskerLeft e.inverse w).symm ≪≫ invFunIdAssoc e G
  { Hom := P.desc ((Cocones.equivalenceOfReindexing e w).Functor.obj t),
    inv := Q.desc ((Cocones.equivalenceOfReindexing e.symm w').Functor.obj s),
    hom_inv_id' := by
      apply hom_ext P
      intro j
      dsimp'
      simp only [← limits.cocone.whisker_ι, ← fac, ← inv_fun_id_assoc_inv_app, ← whisker_left_app, ← assoc, ← comp_id, ←
        limits.cocones.precompose_obj_ι, ← fac_assoc, ← nat_trans.comp_app]
      rw [counit_inv_app_functor, ← functor.comp_map, ← w.inv.naturality_assoc]
      dsimp'
      simp ,
    inv_hom_id' := by
      apply hom_ext Q
      tidy }

end Equivalenceₓ

/-- The universal property of a colimit cocone: a map `X ⟶ W` is the same as
  a cocone on `F` with vertex `W`. -/
def homIso (h : IsColimit t) (W : C) : ULift.{u₁} (t.x ⟶ W : Type v₃) ≅ F ⟶ (const J).obj W where
  Hom := fun f => (t.extend f.down).ι
  inv := fun ι => ⟨h.desc { x := W, ι }⟩
  hom_inv_id' := by
    ext f <;> apply h.hom_ext <;> intro j <;> simp <;> dsimp' <;> rfl

@[simp]
theorem hom_iso_hom (h : IsColimit t) {W : C} (f : ULift (t.x ⟶ W)) :
    (IsColimit.homIso h W).Hom f = (t.extend f.down).ι :=
  rfl

/-- The colimit of `F` represents the functor taking `W` to
  the set of cocones on `F` with vertex `W`. -/
def natIso (h : IsColimit t) : coyoneda.obj (op t.x) ⋙ ulift_functor.{u₁} ≅ F.cocones :=
  NatIso.ofComponents (IsColimit.homIso h)
    (by
      intros <;> ext <;> dsimp' <;> rw [← assoc] <;> rfl)

/-- Another, more explicit, formulation of the universal property of a colimit cocone.
See also `hom_iso`.
-/
def homIso' (h : IsColimit t) (W : C) :
    ULift.{u₁} (t.x ⟶ W : Type v₃) ≅ { p : ∀ j, F.obj j ⟶ W // ∀ {j j' : J} (f : j ⟶ j'), F.map f ≫ p j' = p j } :=
  h.homIso W ≪≫
    { Hom := fun ι =>
        ⟨fun j => ι.app j, fun j j' f => by
          convert ← ι.naturality f <;> apply comp_id⟩,
      inv := fun p =>
        { app := fun j => p.1 j,
          naturality' := fun j j' f => by
            dsimp'
            rw [comp_id]
            exact p.2 f } }

/-- If G : C → D is a faithful functor which sends t to a colimit cocone,
  then it suffices to check that the induced maps for the image of t
  can be lifted to maps of C. -/
def ofFaithful {t : Cocone F} {D : Type u₄} [Category.{v₄} D] (G : C ⥤ D) [Faithful G] (ht : IsColimit (G.mapCocone t))
    (desc : ∀ s : Cocone F, t.x ⟶ s.x) (h : ∀ s, G.map (desc s) = ht.desc (G.mapCocone s)) : IsColimit t :=
  { desc,
    fac' := fun s j => by
      apply G.map_injective <;> rw [G.map_comp, h] <;> apply ht.fac,
    uniq' := fun s m w => by
      apply G.map_injective
      rw [h]
      refine' ht.uniq (G.map_cocone s) _ fun j => _
      convert ← congr_arg (fun f => G.map f) (w j)
      apply G.map_comp }

/-- If `F` and `G` are naturally isomorphic, then `F.map_cone c` being a colimit implies
`G.map_cone c` is also a colimit.
-/
def mapCoconeEquiv {D : Type u₄} [Category.{v₄} D] {K : J ⥤ C} {F G : C ⥤ D} (h : F ≅ G) {c : Cocone K}
    (t : IsColimit (F.mapCocone c)) : IsColimit (G.mapCocone c) := by
  apply is_colimit.of_iso_colimit _ (precompose_whisker_left_map_cocone h c)
  apply (precompose_inv_equiv (iso_whisker_left K h : _) _).symm t

/-- A cocone is a colimit cocone exactly if
there is a unique cocone morphism from any other cocone.
-/
def isoUniqueCoconeMorphism {t : Cocone F} : IsColimit t ≅ ∀ s, Unique (t ⟶ s) where
  Hom := fun h s => { default := h.descCoconeMorphism s, uniq := fun _ => h.uniq_cocone_morphism }
  inv := fun h =>
    { desc := fun s => (h s).default.Hom, uniq' := fun s f w => congr_arg CoconeMorphism.hom ((h s).uniq ⟨f, w⟩) }

namespace OfNatIso

variable {X : C} (h : coyoneda.obj (op X) ⋙ ulift_functor.{u₁} ≅ F.cocones)

/-- If `F.cocones` is corepresented by `X`, each morphism `f : X ⟶ Y` gives a cocone with cone
point `Y`. -/
def coconeOfHom {Y : C} (f : X ⟶ Y) : Cocone F where
  x := Y
  ι := h.Hom.app Y ⟨f⟩

/-- If `F.cocones` is corepresented by `X`, each cocone `s` gives a morphism `X ⟶ s.X`. -/
def homOfCocone (s : Cocone F) : X ⟶ s.x :=
  (h.inv.app s.x s.ι).down

@[simp]
theorem cocone_of_hom_of_cocone (s : Cocone F) : coconeOfHom h (homOfCocone h s) = s := by
  dsimp' [← cocone_of_hom, ← hom_of_cocone]
  cases s
  congr
  dsimp'
  convert congr_fun (congr_fun (congr_arg nat_trans.app h.inv_hom_id) s_X) s_ι
  exact ULift.up_down _

@[simp]
theorem hom_of_cocone_of_hom {Y : C} (f : X ⟶ Y) : homOfCocone h (coconeOfHom h f) = f :=
  congr_arg ULift.down (congr_fun (congr_fun (congr_arg NatTrans.app h.hom_inv_id) Y) ⟨f⟩ : _)

/-- If `F.cocones` is corepresented by `X`, the cocone corresponding to the identity morphism on `X`
will be a colimit cocone. -/
def colimitCocone : Cocone F :=
  coconeOfHom h (𝟙 X)

/-- If `F.cocones` is corepresented by `X`, the cocone corresponding to a morphism `f : Y ⟶ X` is
the colimit cocone extended by `f`. -/
theorem cocone_of_hom_fac {Y : C} (f : X ⟶ Y) : coconeOfHom h f = (colimitCocone h).extend f := by
  dsimp' [← cocone_of_hom, ← colimit_cocone, ← cocone.extend]
  congr with j
  have t := congr_fun (h.hom.naturality f) ⟨𝟙 X⟩
  dsimp'  at t
  simp only [← id_comp] at t
  rw [congr_fun (congr_arg nat_trans.app t) j]
  rfl

/-- If `F.cocones` is corepresented by `X`, any cocone is the extension of the colimit cocone by the
corresponding morphism. -/
theorem cocone_fac (s : Cocone F) : (colimitCocone h).extend (homOfCocone h s) = s := by
  rw [← cocone_of_hom_of_cocone h s]
  conv_lhs => simp only [← hom_of_cocone_of_hom]
  apply (cocone_of_hom_fac _ _).symm

end OfNatIso

section

open OfNatIso

/-- If `F.cocones` is corepresentable, then the cocone corresponding to the identity morphism on
the representing object is a colimit cocone.
-/
def ofNatIso {X : C} (h : coyoneda.obj (op X) ⋙ ulift_functor.{u₁} ≅ F.cocones) : IsColimit (colimitCocone h) where
  desc := fun s => homOfCocone h s
  fac' := fun s j => by
    have h := cocone_fac h s
    cases s
    injection h with h₁ h₂
    simp only [← heq_iff_eq] at h₂
    conv_rhs => rw [← h₂]
    rfl
  uniq' := fun s m w => by
    rw [← hom_of_cocone_of_hom h m]
    congr
    rw [cocone_of_hom_fac]
    dsimp' [← cocone.extend]
    cases s
    congr with j
    exact w j

end

end IsColimit

end CategoryTheory.Limits

