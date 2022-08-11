/-
Copyright (c) 2021 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
import Mathbin.AlgebraicGeometry.Scheme
import Mathbin.CategoryTheory.Adjunction.Limits
import Mathbin.CategoryTheory.Adjunction.Reflective

/-!
# Adjunction between `Γ` and `Spec`

We define the adjunction `Γ_Spec.adjunction : Γ ⊣ Spec` by defining the unit (`to_Γ_Spec`,
in multiple steps in this file) and counit (done in Spec.lean) and checking that they satisfy
the left and right triangle identities. The constructions and proofs make use of
maps and lemmas defined and proved in structure_sheaf.lean extensively.

Notice that since the adjunction is between contravariant functors, you get to choose
one of the two categories to have arrows reversed, and it is equally valid to present
the adjunction as `Spec ⊣ Γ` (`Spec.to_LocallyRingedSpace.right_op ⊣ Γ`), in which
case the unit and the counit would switch to each other.

## Main definition

* `algebraic_geometry.identity_to_Γ_Spec` : The natural transformation `𝟭 _ ⟶ Γ ⋙ Spec`.
* `algebraic_geometry.Γ_Spec.LocallyRingedSpace_adjunction` : The adjunction `Γ ⊣ Spec` from
  `CommRingᵒᵖ` to `LocallyRingedSpace`.
* `algebraic_geometry.Γ_Spec.adjunction` : The adjunction `Γ ⊣ Spec` from
  `CommRingᵒᵖ` to `Scheme`.

-/


noncomputable section

universe u

open PrimeSpectrum

namespace AlgebraicGeometry

open Opposite

open CategoryTheory

open StructureSheaf

open Spec (structureSheaf)

open TopologicalSpace

open AlgebraicGeometry.LocallyRingedSpace

open Top.Presheaf

open Top.Presheaf.SheafCondition

namespace LocallyRingedSpace

variable (X : LocallyRingedSpace.{u})

/-- The map from the global sections to a stalk. -/
def ΓToStalk (x : X) : Γ.obj (op X) ⟶ X.Presheaf.stalk x :=
  X.Presheaf.germ (⟨x, trivialₓ⟩ : (⊤ : Opens X))

/-- The canonical map from the underlying set to the prime spectrum of `Γ(X)`. -/
def toΓSpecFun : X → PrimeSpectrum (Γ.obj (op X)) := fun x =>
  comap (X.ΓToStalk x) (LocalRing.closedPoint (X.Presheaf.stalk x))

theorem not_mem_prime_iff_unit_in_stalk (r : Γ.obj (op X)) (x : X) :
    r ∉ (X.toΓSpecFun x).asIdeal ↔ IsUnit (X.ΓToStalk x r) := by
  erw [LocalRing.mem_maximal_ideal, not_not]

/-- The preimage of a basic open in `Spec Γ(X)` under the unit is the basic
open in `X` defined by the same element (they are equal as sets). -/
theorem to_Γ_Spec_preim_basic_open_eq (r : Γ.obj (op X)) :
    X.toΓSpecFun ⁻¹' (basicOpen r).1 = (X.toRingedSpace.basicOpen r).1 := by
  ext
  erw [X.to_RingedSpace.mem_top_basic_open]
  apply not_mem_prime_iff_unit_in_stalk

/-- `to_Γ_Spec_fun` is continuous. -/
theorem to_Γ_Spec_continuous : Continuous X.toΓSpecFun := by
  apply is_topological_basis_basic_opens.continuous
  rintro _ ⟨r, rfl⟩
  erw [X.to_Γ_Spec_preim_basic_open_eq r]
  exact (X.to_RingedSpace.basic_open r).2

/-- The canonical (bundled) continuous map from the underlying topological
space of `X` to the prime spectrum of its global sections. -/
@[simps]
def toΓSpecBase : X.toTop ⟶ Spec.topObj (Γ.obj (op X)) where
  toFun := X.toΓSpecFun
  continuous_to_fun := X.to_Γ_Spec_continuous

variable (r : Γ.obj (op X))

/-- The preimage in `X` of a basic open in `Spec Γ(X)` (as an open set). -/
abbrev toΓSpecMapBasicOpen : Opens X :=
  (Opens.map X.toΓSpecBase).obj (basicOpen r)

/-- The preimage is the basic open in `X` defined by the same element `r`. -/
theorem to_Γ_Spec_map_basic_open_eq : X.toΓSpecMapBasicOpen r = X.toRingedSpace.basicOpen r :=
  Subtype.eq (X.to_Γ_Spec_preim_basic_open_eq r)

/-- The map from the global sections `Γ(X)` to the sections on the (preimage of) a basic open. -/
abbrev toToΓSpecMapBasicOpen : X.Presheaf.obj (op ⊤) ⟶ X.Presheaf.obj (op <| X.toΓSpecMapBasicOpen r) :=
  X.Presheaf.map (X.toΓSpecMapBasicOpen r).le_top.op

/-- `r` is a unit as a section on the basic open defined by `r`. -/
theorem is_unit_res_to_Γ_Spec_map_basic_open : IsUnit (X.toToΓSpecMapBasicOpen r r) := by
  convert
    (X.presheaf.map <| (eq_to_hom <| X.to_Γ_Spec_map_basic_open_eq r).op).is_unit_map
      (X.to_RingedSpace.is_unit_res_basic_open r)
  rw [← comp_apply]
  erw [← functor.map_comp]
  congr

/-- Define the sheaf hom on individual basic opens for the unit. -/
def toΓSpecCApp :
    (structure_sheaf <| Γ.obj <| op X).val.obj (op <| basicOpen r) ⟶ X.Presheaf.obj (op <| X.toΓSpecMapBasicOpen r) :=
  IsLocalization.Away.lift r (is_unit_res_to_Γ_Spec_map_basic_open _ r)

/-- Characterization of the sheaf hom on basic opens,
    direction ← (next lemma) is used at various places, but → is not used in this file. -/
theorem to_Γ_Spec_c_app_iff
    (f :
      (structure_sheaf <| Γ.obj <| op X).val.obj (op <| basicOpen r) ⟶ X.Presheaf.obj (op <| X.toΓSpecMapBasicOpen r)) :
    toOpen _ (basicOpen r) ≫ f = X.toToΓSpecMapBasicOpen r ↔ f = X.toΓSpecCApp r := by
  rw [← IsLocalization.Away.AwayMap.lift_comp r (X.is_unit_res_to_Γ_Spec_map_basic_open r)]
  pick_goal 5
  exact is_localization.to_basic_open _ r
  constructor
  · intro h
    refine' IsLocalization.ring_hom_ext _ _
    pick_goal 5
    exact is_localization.to_basic_open _ r
    exact h
    
  apply congr_arg

theorem to_Γ_Spec_c_app_spec : toOpen _ (basicOpen r) ≫ X.toΓSpecCApp r = X.toToΓSpecMapBasicOpen r :=
  (X.to_Γ_Spec_c_app_iff r _).2 rfl

/-- The sheaf hom on all basic opens, commuting with restrictions. -/
def toΓSpecCBasicOpens :
    (inducedFunctor basicOpen).op ⋙ (structureSheaf (Γ.obj (op X))).1 ⟶
      (inducedFunctor basicOpen).op ⋙ ((Top.Sheaf.pushforward X.toΓSpecBase).obj X.𝒪).1 where
  app := fun r => X.toΓSpecCApp r.unop
  naturality' := fun r s f => by
    apply (structure_sheaf.to_basic_open_epi (Γ.obj (op X)) r.unop).1
    simp only [category.assoc]
    erw [X.to_Γ_Spec_c_app_spec r.unop]
    convert X.to_Γ_Spec_c_app_spec s.unop
    symm
    apply X.presheaf.map_comp

/-- The canonical morphism of sheafed spaces from `X` to the spectrum of its global sections. -/
@[simps]
def toΓSpecSheafedSpace : X.toSheafedSpace ⟶ Spec.toSheafedSpace.obj (op (Γ.obj (op X))) where
  base := X.toΓSpecBase
  c := Top.Sheaf.restrictHomEquivHom (structureSheaf (Γ.obj (op X))).1 _ is_basis_basic_opens X.toΓSpecCBasicOpens

theorem to_Γ_Spec_SheafedSpace_app_eq : X.toΓSpecSheafedSpace.c.app (op (basicOpen r)) = X.toΓSpecCApp r :=
  Top.Sheaf.extend_hom_app _ _ _ _ _

theorem to_Γ_Spec_SheafedSpace_app_spec (r : Γ.obj (op X)) :
    toOpen _ (basicOpen r) ≫ X.toΓSpecSheafedSpace.c.app (op (basicOpen r)) = X.toToΓSpecMapBasicOpen r :=
  (X.to_Γ_Spec_SheafedSpace_app_eq r).symm ▸ X.to_Γ_Spec_c_app_spec r

/-- The map on stalks induced by the unit commutes with maps from `Γ(X)` to
    stalks (in `Spec Γ(X)` and in `X`). -/
theorem to_stalk_stalk_map_to_Γ_Spec (x : X) :
    toStalk _ _ ≫ PresheafedSpace.stalkMap X.toΓSpecSheafedSpace x = X.ΓToStalk x := by
  rw [PresheafedSpace.stalk_map]
  erw [←
    to_open_germ _ (basic_open (1 : Γ.obj (op X)))
      ⟨X.to_Γ_Spec_fun x, by
        rw [basic_open_one] <;> trivial⟩]
  rw [← category.assoc, category.assoc (to_open _ _)]
  erw [stalk_functor_map_germ]
  rw [← category.assoc (to_open _ _), X.to_Γ_Spec_SheafedSpace_app_spec 1]
  unfold Γ_to_stalk
  rw [← stalk_pushforward_germ _ X.to_Γ_Spec_base X.presheaf ⊤]
  congr 1
  change (X.to_Γ_Spec_base _* X.presheaf).map le_top.hom.op ≫ _ = _
  apply germ_res

/-- The canonical morphism from `X` to the spectrum of its global sections. -/
@[simps coeBase]
def toΓSpec : X ⟶ Spec.locallyRingedSpaceObj (Γ.obj (op X)) where
  val := X.toΓSpecSheafedSpace
  property := by
    intro x
    let p : PrimeSpectrum (Γ.obj (op X)) := X.to_Γ_Spec_fun x
    constructor
    -- show stalk map is local hom ↓
    let S := (structure_sheaf _).val.stalk p
    rintro (t : S) ht
    obtain ⟨⟨r, s⟩, he⟩ := IsLocalization.surj p.as_ideal.prime_compl t
    dsimp'  at he
    apply is_unit_of_mul_is_unit_left
    rw [he]
    refine' IsLocalization.map_units S (⟨r, _⟩ : p.as_ideal.prime_compl)
    apply (not_mem_prime_iff_unit_in_stalk _ _ _).mpr
    rw [← to_stalk_stalk_map_to_Γ_Spec, comp_apply]
    erw [← he]
    rw [RingHom.map_mul]
    exact ht.mul ((IsLocalization.map_units S s : _).map (PresheafedSpace.stalk_map X.to_Γ_Spec_SheafedSpace x))

theorem comp_ring_hom_ext {X : LocallyRingedSpace} {R : CommRingₓₓ} {f : R ⟶ Γ.obj (op X)}
    {β : X ⟶ Spec.locallyRingedSpaceObj R} (w : X.toΓSpec.1.base ≫ (Spec.locallyRingedSpaceMap f).1.base = β.1.base)
    (h :
      ∀ r : R,
        f ≫ X.Presheaf.map (homOfLe le_top : (Opens.map β.1.base).obj (basicOpen r) ⟶ _).op =
          toOpen R (basicOpen r) ≫ β.1.c.app (op (basicOpen r))) :
    X.toΓSpec ≫ Spec.locallyRingedSpaceMap f = β := by
  ext1
  apply Spec.basic_open_hom_ext
  · intro r _
    rw [LocallyRingedSpace.comp_val_c_app]
    erw [to_open_comp_comap_assoc]
    rw [category.assoc]
    erw [to_Γ_Spec_SheafedSpace_app_spec, ← X.presheaf.map_comp]
    convert h r
    
  exact w

/-- `to_Spec_Γ _` is an isomorphism so these are mutually two-sided inverses. -/
theorem Γ_Spec_left_triangle : toSpecΓ (Γ.obj (op X)) ≫ X.toΓSpec.1.c.app (op ⊤) = 𝟙 _ := by
  unfold to_Spec_Γ
  rw [← to_open_res _ (basic_open (1 : Γ.obj (op X))) ⊤ (eq_to_hom basic_open_one.symm)]
  erw [category.assoc]
  rw [nat_trans.naturality, ← category.assoc]
  erw [X.to_Γ_Spec_SheafedSpace_app_spec 1, ← functor.map_comp]
  convert eq_to_hom_map X.presheaf _
  rfl

end LocallyRingedSpace

/-- The unit as a natural transformation. -/
def identityToΓSpec : 𝟭 LocallyRingedSpace.{u} ⟶ Γ.rightOp ⋙ Spec.to_LocallyRingedSpace where
  app := LocallyRingedSpace.toΓSpec
  naturality' := fun X Y f => by
    symm
    apply LocallyRingedSpace.comp_ring_hom_ext
    · ext1 x
      dsimp' [← Spec.Top_map, ← LocallyRingedSpace.to_Γ_Spec_fun]
      rw [← Subtype.val_eq_coe, ← LocalRing.comap_closed_point (PresheafedSpace.stalk_map _ x), ←
        PrimeSpectrum.comap_comp_apply, ← PrimeSpectrum.comap_comp_apply]
      congr 2
      exact (PresheafedSpace.stalk_map_germ f.1 ⊤ ⟨x, trivialₓ⟩).symm
      infer_instance
      
    · intro r
      rw [LocallyRingedSpace.comp_val_c_app, ← category.assoc]
      erw [Y.to_Γ_Spec_SheafedSpace_app_spec, f.1.c.naturality]
      rfl
      

namespace ΓSpec

theorem left_triangle (X : LocallyRingedSpace) :
    specΓIdentity.inv.app (Γ.obj (op X)) ≫ (identityToΓSpec.app X).val.c.app (op ⊤) = 𝟙 _ :=
  X.Γ_Spec_left_triangle

/-- `Spec_Γ_identity` is iso so these are mutually two-sided inverses. -/
theorem right_triangle (R : CommRingₓₓ) :
    identityToΓSpec.app (Spec.toLocallyRingedSpace.obj <| op R) ≫
        Spec.toLocallyRingedSpace.map (specΓIdentity.inv.app R).op =
      𝟙 _ :=
  by
  apply LocallyRingedSpace.comp_ring_hom_ext
  · ext (p : PrimeSpectrum R) x
    erw [← IsLocalization.AtPrime.to_map_mem_maximal_iff ((structure_sheaf R).val.stalk p) p.as_ideal x]
    rfl
    
  · intro r
    apply to_open_res
    

/-- The adjunction `Γ ⊣ Spec` from `CommRingᵒᵖ` to `LocallyRingedSpace`. -/
-- Removing this makes the following definition time out.
@[simps Unit counit]
def locallyRingedSpaceAdjunction : Γ.rightOp ⊣ Spec.to_LocallyRingedSpace :=
  Adjunction.mkOfUnitCounit
    { Unit := identityToΓSpec, counit := (NatIso.op specΓIdentity).inv,
      left_triangle' := by
        ext X
        erw [category.id_comp]
        exact congr_arg Quiver.Hom.op (left_triangle X),
      right_triangle' := by
        ext1
        ext1 R
        erw [category.id_comp]
        exact right_triangle R.unop }

attribute [local semireducible] Spec.to_LocallyRingedSpace

/-- The adjunction `Γ ⊣ Spec` from `CommRingᵒᵖ` to `Scheme`. -/
def adjunction : Scheme.Γ.rightOp ⊣ Scheme.Spec :=
  locallyRingedSpaceAdjunction.restrictFullyFaithful Scheme.forgetToLocallyRingedSpace (𝟭 _)
    (NatIso.ofComponents (fun X => Iso.refl _) fun _ _ f => by
      simpa)
    (NatIso.ofComponents (fun X => Iso.refl _) fun _ _ f => by
      simpa)

theorem adjunction_hom_equiv_apply {X : Scheme} {R : CommRingₓₓᵒᵖ} (f : (op <| Scheme.Γ.obj <| op X) ⟶ R) :
    ΓSpec.adjunction.homEquiv X R f = locallyRingedSpaceAdjunction.homEquiv X.1 R f := by
  dsimp' [← adjunction, ← adjunction.restrict_fully_faithful]
  simp

theorem adjunction_hom_equiv (X : Scheme) (R : CommRingₓₓᵒᵖ) :
    ΓSpec.adjunction.homEquiv X R = locallyRingedSpaceAdjunction.homEquiv X.1 R :=
  Equivₓ.ext fun f => adjunction_hom_equiv_apply f

theorem adjunction_hom_equiv_symm_apply {X : Scheme} {R : CommRingₓₓᵒᵖ} (f : X ⟶ Scheme.spec.obj R) :
    (ΓSpec.adjunction.homEquiv X R).symm f = (locallyRingedSpaceAdjunction.homEquiv X.1 R).symm f := by
  congr 2
  exact adjunction_hom_equiv _ _

@[simp]
theorem adjunction_counit_app {R : CommRingₓₓᵒᵖ} :
    ΓSpec.adjunction.counit.app R = locallyRingedSpaceAdjunction.counit.app R := by
  rw [← adjunction.hom_equiv_symm_id, ← adjunction.hom_equiv_symm_id, adjunction_hom_equiv_symm_apply]
  rfl

@[simp]
theorem adjunction_unit_app {X : Scheme} : ΓSpec.adjunction.Unit.app X = locallyRingedSpaceAdjunction.Unit.app X.1 := by
  rw [← adjunction.hom_equiv_id, ← adjunction.hom_equiv_id, adjunction_hom_equiv_apply]
  rfl

attribute [local semireducible] LocallyRingedSpace_adjunction Γ_Spec.adjunction

instance is_iso_LocallyRingedSpace_adjunction_counit : IsIso locallyRingedSpaceAdjunction.counit :=
  IsIso.of_iso_inv _

instance is_iso_adjunction_counit : IsIso ΓSpec.adjunction.counit := by
  apply nat_iso.is_iso_of_is_iso_app with { instances := false }
  intro R
  rw [adjunction_counit_app]
  infer_instance

-- This is just
-- `(Γ_Spec.adjunction.unit.app X).1.c.app (op ⊤) = Spec_Γ_identity.hom.app (X.presheaf.obj (op ⊤))`
-- But lean times out when trying to unify the types of the two sides.
theorem adjunction_unit_app_app_top (X : Scheme) :
    @Eq
      ((Scheme.spec.obj (op <| X.Presheaf.obj (op ⊤))).Presheaf.obj (op ⊤) ⟶
        ((ΓSpec.adjunction.Unit.app X).1.base _* X.Presheaf).obj (op ⊤))
      ((ΓSpec.adjunction.Unit.app X).val.c.app (op ⊤)) (specΓIdentity.Hom.app (X.Presheaf.obj (op ⊤))) :=
  by
  have := congr_app Γ_Spec.adjunction.left_triangle X
  dsimp'  at this
  rw [← is_iso.eq_comp_inv] at this
  simp only [← Γ_Spec.LocallyRingedSpace_adjunction_counit, ← nat_trans.op_app, ← category.id_comp, ←
    Γ_Spec.adjunction_counit_app] at this
  rw [← op_inv, nat_iso.inv_inv_app, quiver.hom.op_inj.eq_iff] at this
  exact this

end ΓSpec

/-! Immediate consequences of the adjunction. -/


/-- Spec preserves limits. -/
instance : Limits.PreservesLimits Spec.toLocallyRingedSpace :=
  ΓSpec.locallyRingedSpaceAdjunction.rightAdjointPreservesLimits

instance Spec.preservesLimits : Limits.preservesLimits Scheme.spec :=
  ΓSpec.adjunction.rightAdjointPreservesLimits

/-- Spec is a full functor. -/
instance : Full Spec.toLocallyRingedSpace :=
  rFullOfCounitIsIso ΓSpec.locallyRingedSpaceAdjunction

instance Spec.full : Full Scheme.spec :=
  rFullOfCounitIsIso ΓSpec.adjunction

/-- Spec is a faithful functor. -/
instance : Faithful Spec.toLocallyRingedSpace :=
  R_faithful_of_counit_is_iso ΓSpec.locallyRingedSpaceAdjunction

instance Spec.faithful : Faithful Scheme.spec :=
  R_faithful_of_counit_is_iso ΓSpec.adjunction

instance : IsRightAdjoint Spec.toLocallyRingedSpace :=
  ⟨_, ΓSpec.locallyRingedSpaceAdjunction⟩

instance : IsRightAdjoint Scheme.spec :=
  ⟨_, ΓSpec.adjunction⟩

instance : Reflective Spec.toLocallyRingedSpace :=
  ⟨⟩

instance Spec.reflective : Reflective Scheme.spec :=
  ⟨⟩

end AlgebraicGeometry

