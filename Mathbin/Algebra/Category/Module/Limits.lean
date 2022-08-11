/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.Algebra.Category.Module.Basic
import Mathbin.Algebra.Category.Group.Limits
import Mathbin.Algebra.DirectLimit

/-!
# The category of R-modules has all limits

Further, these limits are preserved by the forgetful functor --- that is,
the underlying types are just the limits in the category of types.
-/


open CategoryTheory

open CategoryTheory.Limits

universe v w u

-- `u` is determined by the ring, so can come last
noncomputable section

namespace ModuleCat

variable {R : Type u} [Ringₓ R]

variable {J : Type v} [SmallCategory J]

instance addCommGroupObj (F : J ⥤ ModuleCat.{max v w} R) (j) : AddCommGroupₓ ((F ⋙ forget (ModuleCat R)).obj j) := by
  change AddCommGroupₓ (F.obj j)
  infer_instance

instance moduleObj (F : J ⥤ ModuleCat.{max v w} R) (j) : Module R ((F ⋙ forget (ModuleCat R)).obj j) := by
  change Module R (F.obj j)
  infer_instance

/-- The flat sections of a functor into `Module R` form a submodule of all sections.
-/
def sectionsSubmodule (F : J ⥤ ModuleCat.{max v w} R) : Submodule R (∀ j, F.obj j) :=
  { AddGroupₓₓ.sectionsAddSubgroup
      (F ⋙ forget₂ (ModuleCat R) AddCommGroupₓₓ.{max v w} ⋙ forget₂ AddCommGroupₓₓ AddGroupₓₓ.{max v w}) with
    Carrier := (F ⋙ forget (ModuleCat R)).sections,
    smul_mem' := fun r s sh j j' f => by
      simp only [← forget_map_eq_coe, ← functor.comp_map, ← Pi.smul_apply, ← LinearMap.map_smul]
      dsimp' [← functor.sections]  at sh
      rw [sh f] }

-- Adding the following instance speeds up `limit_module` noticeably,
-- by preventing a bad unfold of `limit_add_comm_group`.
instance limitAddCommMonoid (F : J ⥤ ModuleCat R) :
    AddCommMonoidₓ (Types.limitCone (F ⋙ forget (ModuleCat.{max v w} R))).x :=
  show AddCommMonoidₓ (sectionsSubmodule F) by
    infer_instance

instance limitAddCommGroup (F : J ⥤ ModuleCat R) :
    AddCommGroupₓ (Types.limitCone (F ⋙ forget (ModuleCat.{max v w} R))).x :=
  show AddCommGroupₓ (sectionsSubmodule F) by
    infer_instance

instance limitModule (F : J ⥤ ModuleCat R) : Module R (Types.limitCone (F ⋙ forget (ModuleCat.{max v w} R))).x :=
  show Module R (sectionsSubmodule F) by
    infer_instance

/-- `limit.π (F ⋙ forget Ring) j` as a `ring_hom`. -/
def limitπLinearMap (F : J ⥤ ModuleCat R) (j) :
    (Types.limitCone (F ⋙ forget (ModuleCat.{max v w} R))).x →ₗ[R] (F ⋙ forget (ModuleCat R)).obj j where
  toFun := (Types.limitCone (F ⋙ forget (ModuleCat R))).π.app j
  map_smul' := fun x y => rfl
  map_add' := fun x y => rfl

namespace HasLimits

/-- Construction of a limit cone in `Module R`.
(Internal use only; use the limits API.)
-/
-- The next two definitions are used in the construction of `has_limits (Module R)`.
-- After that, the limits should be constructed using the generic limits API,
-- e.g. `limit F`, `limit.cone F`, and `limit.is_limit F`.
def limitCone (F : J ⥤ ModuleCat.{max v w} R) : Cone F where
  x := ModuleCat.of R (Types.limitCone (F ⋙ forget _)).x
  π :=
    { app := limitπLinearMap F,
      naturality' := fun j j' f => LinearMap.coe_injective ((Types.limitCone (F ⋙ forget _)).π.naturality f) }

/-- Witness that the limit cone in `Module R` is a limit cone.
(Internal use only; use the limits API.)
-/
def limitConeIsLimit (F : J ⥤ ModuleCat.{max v w} R) : IsLimit (limitCone F) := by
  refine'
      is_limit.of_faithful (forget (ModuleCat R)) (types.limit_cone_is_limit _) (fun s => ⟨_, _, _⟩) fun s => rfl <;>
    intros <;>
      ext j <;>
        simp only [← Subtype.coe_mk, ← functor.map_cone_π_app, ← forget_map_eq_coe, ← LinearMap.map_add, ←
            LinearMap.map_smul] <;>
          rfl

end HasLimits

open HasLimits

-- ./././Mathport/Syntax/Translate/Basic.lean:1389:38: unsupported irreducible non-definition
/-- The category of R-modules has all limits. -/
irreducible_def has_limits_of_size : HasLimitsOfSize.{v, v} (ModuleCat.{max v w} R) :=
  { HasLimitsOfShape := fun J 𝒥 =>
      { HasLimit := fun F => has_limit.mk { Cone := limit_cone F, IsLimit := limit_cone_is_limit F } } }

instance has_limits : HasLimits (ModuleCat.{w} R) :=
  ModuleCat.has_limits_of_size.{w, w, u}

/-- An auxiliary declaration to speed up typechecking.
-/
def forget₂AddCommGroupPreservesLimitsAux (F : J ⥤ ModuleCat.{max v w} R) :
    IsLimit ((forget₂ (ModuleCat R) AddCommGroupₓₓ).mapCone (limitCone F)) :=
  AddCommGroupₓₓ.limitConeIsLimit (F ⋙ forget₂ (ModuleCat R) AddCommGroupₓₓ.{max v w})

/-- The forgetful functor from R-modules to abelian groups preserves all limits.
-/
instance forget₂AddCommGroupPreservesLimitsOfSize :
    PreservesLimitsOfSize.{v, v}
      (forget₂ (ModuleCat R)
        AddCommGroupₓₓ.{max v
            w}) where PreservesLimitsOfShape := fun J 𝒥 =>
    { PreservesLimit := fun F =>
        preserves_limit_of_preserves_limit_cone (limit_cone_is_limit F) (forget₂_AddCommGroup_preserves_limits_aux F) }

instance forget₂AddCommGroupPreservesLimits : PreservesLimits (forget₂ (ModuleCat R) AddCommGroupₓₓ.{w}) :=
  ModuleCat.forget₂AddCommGroupPreservesLimitsOfSize.{w, w}

/-- The forgetful functor from R-modules to types preserves all limits.
-/
instance forgetPreservesLimitsOfSize :
    PreservesLimitsOfSize.{v, v}
      (forget
        (ModuleCat.{max v w}
          R)) where PreservesLimitsOfShape := fun J 𝒥 =>
    { PreservesLimit := fun F =>
        preserves_limit_of_preserves_limit_cone (limit_cone_is_limit F) (types.limit_cone_is_limit (F ⋙ forget _)) }

instance forgetPreservesLimits : PreservesLimits (forget (ModuleCat.{w} R)) :=
  ModuleCat.forgetPreservesLimitsOfSize.{w, w}

section DirectLimit

open Module

variable {ι : Type v}

variable [dec_ι : DecidableEq ι] [Preorderₓ ι]

variable (G : ι → Type v)

variable [∀ i, AddCommGroupₓ (G i)] [∀ i, Module R (G i)]

variable (f : ∀ i j, i ≤ j → G i →ₗ[R] G j) [DirectedSystem G fun i j h => f i j h]

/-- The diagram (in the sense of `category_theory`)
 of an unbundled `direct_limit` of modules. -/
@[simps]
def directLimitDiagram : ι ⥤ ModuleCat R where
  obj := fun i => ModuleCat.of R (G i)
  map := fun i j hij => f i j hij.le
  map_id' := fun i => by
    apply LinearMap.ext
    intro x
    apply Module.DirectedSystem.map_self
  map_comp' := fun i j k hij hjk => by
    apply LinearMap.ext
    intro x
    symm
    apply Module.DirectedSystem.map_map

variable [DecidableEq ι]

/-- The `cocone` on `direct_limit_diagram` corresponding to
the unbundled `direct_limit` of modules.

In `direct_limit_is_colimit` we show that it is a colimit cocone. -/
@[simps]
def directLimitCocone : Cocone (directLimitDiagram G f) where
  x := ModuleCat.of R <| DirectLimit G f
  ι :=
    { app := Module.DirectLimit.of R ι G f,
      naturality' := fun i j hij => by
        apply LinearMap.ext
        intro x
        exact direct_limit.of_f }

/-- The unbundled `direct_limit` of modules is a colimit
in the sense of `category_theory`. -/
@[simps]
def directLimitIsColimit [Nonempty ι] [IsDirected ι (· ≤ ·)] : IsColimit (directLimitCocone G f) where
  desc := fun s =>
    (DirectLimit.lift R ι G f s.ι.app) fun i j h x => by
      rw [← s.w (hom_of_le h)]
      rfl
  fac' := fun s i => by
    apply LinearMap.ext
    intro x
    dsimp'
    exact direct_limit.lift_of s.ι.app _ x
  uniq' := fun s m h => by
    have : s.ι.app = fun i => LinearMap.comp m (direct_limit.of R ι (fun i => G i) (fun i j H => f i j H) i) := by
      funext i
      rw [← h]
      rfl
    apply LinearMap.ext
    intro x
    simp only [← this]
    apply Module.DirectLimit.lift_unique

end DirectLimit

end ModuleCat

