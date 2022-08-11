/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaniel Thomas, Jeremy Avigad, Johannes Hölzl, Mario Carneiro, Anne Baanen,
  Frédéric Dupuis, Heather Macbeth
-/
import Mathbin.Algebra.Hom.Group
import Mathbin.Algebra.Hom.GroupAction
import Mathbin.Algebra.Module.Basic
import Mathbin.Algebra.Module.Pi
import Mathbin.Algebra.Ring.CompTypeclasses
import Mathbin.Algebra.Star.Basic

/-!
# (Semi)linear maps

In this file we define

* `linear_map σ M M₂`, `M →ₛₗ[σ] M₂` : a semilinear map between two `module`s. Here,
  `σ` is a `ring_hom` from `R` to `R₂` and an `f : M →ₛₗ[σ] M₂` satisfies
  `f (c • x) = (σ c) • (f x)`. We recover plain linear maps by choosing `σ` to be `ring_hom.id R`.
  This is denoted by `M →ₗ[R] M₂`. We also add the notation `M →ₗ⋆[R] M₂` for star-linear maps.

* `is_linear_map R f` : predicate saying that `f : M → M₂` is a linear map. (Note that this
  was not generalized to semilinear maps.)

We then provide `linear_map` with the following instances:

* `linear_map.add_comm_monoid` and `linear_map.add_comm_group`: the elementwise addition structures
  corresponding to addition in the codomain
* `linear_map.distrib_mul_action` and `linear_map.module`: the elementwise scalar action structures
  corresponding to applying the action in the codomain.
* `module.End.semiring` and `module.End.ring`: the (semi)ring of endomorphisms formed by taking the
  additive structure above with composition as multiplication.

## Implementation notes

To ensure that composition works smoothly for semilinear maps, we use the typeclasses
`ring_hom_comp_triple`, `ring_hom_inv_pair` and `ring_hom_surjective` from
`algebra/ring/comp_typeclasses`.

## Notation

* Throughout the file, we denote regular linear maps by `fₗ`, `gₗ`, etc, and semilinear maps
  by `f`, `g`, etc.

## TODO

* Parts of this file have not yet been generalized to semilinear maps (i.e. `compatible_smul`)

## Tags

linear map
-/


open Function

open BigOperators

universe u u' v w x y z

variable {R : Type _} {R₁ : Type _} {R₂ : Type _} {R₃ : Type _}

variable {k : Type _} {S : Type _} {S₃ : Type _} {T : Type _}

variable {M : Type _} {M₁ : Type _} {M₂ : Type _} {M₃ : Type _}

variable {N₁ : Type _} {N₂ : Type _} {N₃ : Type _} {ι : Type _}

/-- A map `f` between modules over a semiring is linear if it satisfies the two properties
`f (x + y) = f x + f y` and `f (c • x) = c • f x`. The predicate `is_linear_map R f` asserts this
property. A bundled version is available with `linear_map`, and should be favored over
`is_linear_map` most of the time. -/
structure IsLinearMap (R : Type u) {M : Type v} {M₂ : Type w} [Semiringₓ R] [AddCommMonoidₓ M] [AddCommMonoidₓ M₂]
  [Module R M] [Module R M₂] (f : M → M₂) : Prop where
  map_add : ∀ x y, f (x + y) = f x + f y
  map_smul : ∀ (c : R) (x), f (c • x) = c • f x

section

/-- A map `f` between an `R`-module and an `S`-module over a ring homomorphism `σ : R →+* S`
is semilinear if it satisfies the two properties `f (x + y) = f x + f y` and
`f (c • x) = (σ c) • f x`. Elements of `linear_map σ M M₂` (available under the notation
`M →ₛₗ[σ] M₂`) are bundled versions of such maps. For plain linear maps (i.e. for which
`σ = ring_hom.id R`), the notation `M →ₗ[R] M₂` is available. An unbundled version of plain linear
maps is available with the predicate `is_linear_map`, but it should be avoided most of the time. -/
structure LinearMap {R : Type _} {S : Type _} [Semiringₓ R] [Semiringₓ S] (σ : R →+* S) (M : Type _) (M₂ : Type _)
  [AddCommMonoidₓ M] [AddCommMonoidₓ M₂] [Module R M] [Module S M₂] extends AddHom M M₂ where
  map_smul' : ∀ (r : R) (x : M), to_fun (r • x) = σ r • to_fun x

/-- The `add_hom` underlying a `linear_map`. -/
add_decl_doc LinearMap.toAddHom

-- mathport name: «expr →ₛₗ[ ] »
notation:25 M " →ₛₗ[" σ:25 "] " M₂:0 => LinearMap σ M M₂

-- mathport name: «expr →ₗ[ ] »
notation:25 M " →ₗ[" R:25 "] " M₂:0 => LinearMap (RingHom.id R) M M₂

-- mathport name: «expr →ₗ⋆[ ] »
notation:25 M " →ₗ⋆[" R:25 "] " M₂:0 => LinearMap (starRingEnd R) M M₂

/-- `semilinear_map_class F σ M M₂` asserts `F` is a type of bundled `σ`-semilinear maps `M → M₂`.

See also `linear_map_class F R M M₂` for the case where `σ` is the identity map on `R`.

A map `f` between an `R`-module and an `S`-module over a ring homomorphism `σ : R →+* S`
is semilinear if it satisfies the two properties `f (x + y) = f x + f y` and
`f (c • x) = (σ c) • f x`. -/
class SemilinearMapClass (F : Type _) {R S : outParam (Type _)} [Semiringₓ R] [Semiringₓ S] (σ : outParam <| R →+* S)
  (M M₂ : outParam (Type _)) [AddCommMonoidₓ M] [AddCommMonoidₓ M₂] [Module R M] [Module S M₂] extends
  AddHomClass F M M₂ where
  map_smulₛₗ : ∀ (f : F) (r : R) (x : M), f (r • x) = σ r • f x

end

-- `σ` becomes a metavariable but that's fine because it's an `out_param`
attribute [nolint dangerous_instance] SemilinearMapClass.toAddHomClass

export SemilinearMapClass (map_smulₛₗ)

attribute [simp] map_smulₛₗ

/-- `linear_map_class F R M M₂` asserts `F` is a type of bundled `R`-linear maps `M → M₂`.

This is an abbreviation for `semilinear_map_class F (ring_hom.id R) M M₂`.
-/
abbrev LinearMapClass (F : Type _) (R M M₂ : outParam (Type _)) [Semiringₓ R] [AddCommMonoidₓ M] [AddCommMonoidₓ M₂]
    [Module R M] [Module R M₂] :=
  SemilinearMapClass F (RingHom.id R) M M₂

namespace SemilinearMapClass

variable (F : Type _)

variable [Semiringₓ R] [Semiringₓ S]

variable [AddCommMonoidₓ M] [AddCommMonoidₓ M₁] [AddCommMonoidₓ M₂] [AddCommMonoidₓ M₃]

variable [AddCommMonoidₓ N₁] [AddCommMonoidₓ N₂] [AddCommMonoidₓ N₃]

variable [Module R M] [Module R M₂] [Module S M₃]

variable {σ : R →+* S}

-- `σ` is an `out_param` so it's not dangerous
@[nolint dangerous_instance]
instance (priority := 100) [SemilinearMapClass F σ M M₃] : AddMonoidHomClass F M M₃ :=
  { SemilinearMapClass.toAddHomClass F σ M M₃ with coe := fun f => (f : M → M₃),
    map_zero := fun f =>
      show f 0 = 0 by
        rw [← zero_smul R (0 : M), map_smulₛₗ]
        simp }

-- `R` is an `out_param` so it's not dangerous
@[nolint dangerous_instance]
instance (priority := 100) [LinearMapClass F R M M₂] : DistribMulActionHomClass F R M M₂ :=
  { SemilinearMapClass.addMonoidHomClass F with coe := fun f => (f : M → M₂),
    map_smul := fun f c x => by
      rw [map_smulₛₗ, RingHom.id_apply] }

variable {F} (f : F) [i : SemilinearMapClass F σ M M₃]

include i

theorem map_smul_inv {σ' : S →+* R} [RingHomInvPair σ σ'] (c : S) (x : M) : c • f x = f (σ' c • x) := by
  simp

end SemilinearMapClass

namespace LinearMap

section AddCommMonoidₓ

variable [Semiringₓ R] [Semiringₓ S]

section

variable [AddCommMonoidₓ M] [AddCommMonoidₓ M₁] [AddCommMonoidₓ M₂] [AddCommMonoidₓ M₃]

variable [AddCommMonoidₓ N₁] [AddCommMonoidₓ N₂] [AddCommMonoidₓ N₃]

variable [Module R M] [Module R M₂] [Module S M₃]

variable {σ : R →+* S}

instance : SemilinearMapClass (M →ₛₗ[σ] M₃) σ M M₃ where
  coe := LinearMap.toFun
  coe_injective' := fun f g h => by
    cases f <;> cases g <;> congr
  map_add := LinearMap.map_add'
  map_smulₛₗ := LinearMap.map_smul'

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly.
-/
instance : CoeFun (M →ₛₗ[σ] M₃) fun _ => M → M₃ :=
  ⟨fun f => f⟩

/-- The `distrib_mul_action_hom` underlying a `linear_map`. -/
def toDistribMulActionHom (f : M →ₗ[R] M₂) : DistribMulActionHom R M M₂ :=
  { f with map_zero' := show f 0 = 0 from map_zero f }

@[simp]
theorem to_fun_eq_coe {f : M →ₛₗ[σ] M₃} : f.toFun = (f : M → M₃) :=
  rfl

@[ext]
theorem ext {f g : M →ₛₗ[σ] M₃} (h : ∀ x, f x = g x) : f = g :=
  FunLike.ext f g h

/-- Copy of a `linear_map` with a new `to_fun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (f : M →ₛₗ[σ] M₃) (f' : M → M₃) (h : f' = ⇑f) : M →ₛₗ[σ] M₃ where
  toFun := f'
  map_add' := h.symm ▸ f.map_add'
  map_smul' := h.symm ▸ f.map_smul'

/-- See Note [custom simps projection]. -/
protected def Simps.apply {R S : Type _} [Semiringₓ R] [Semiringₓ S] (σ : R →+* S) (M M₃ : Type _) [AddCommMonoidₓ M]
    [AddCommMonoidₓ M₃] [Module R M] [Module S M₃] (f : M →ₛₗ[σ] M₃) : M → M₃ :=
  f

initialize_simps_projections LinearMap (toFun → apply)

@[simp]
theorem coe_mk {σ : R →+* S} (f : M → M₃) (h₁ h₂) : ((LinearMap.mk f h₁ h₂ : M →ₛₗ[σ] M₃) : M → M₃) = f :=
  rfl

/-- Identity map as a `linear_map` -/
def id : M →ₗ[R] M :=
  { DistribMulActionHom.id R with toFun := id }

theorem id_apply (x : M) : @id R M _ _ _ x = x :=
  rfl

@[simp, norm_cast]
theorem id_coe : ((LinearMap.id : M →ₗ[R] M) : M → M) = _root_.id :=
  rfl

end

section

variable [AddCommMonoidₓ M] [AddCommMonoidₓ M₁] [AddCommMonoidₓ M₂] [AddCommMonoidₓ M₃]

variable [AddCommMonoidₓ N₁] [AddCommMonoidₓ N₂] [AddCommMonoidₓ N₃]

variable [Module R M] [Module R M₂] [Module S M₃]

variable (σ : R →+* S)

variable (fₗ gₗ : M →ₗ[R] M₂) (f g : M →ₛₗ[σ] M₃)

theorem is_linear : IsLinearMap R fₗ :=
  ⟨fₗ.map_add', fₗ.map_smul'⟩

variable {fₗ gₗ f g σ}

theorem coe_injective : @Injective (M →ₛₗ[σ] M₃) (M → M₃) coeFn :=
  FunLike.coe_injective

protected theorem congr_arg {x x' : M} : x = x' → f x = f x' :=
  FunLike.congr_arg f

/-- If two linear maps are equal, they are equal at each point. -/
protected theorem congr_fun (h : f = g) (x : M) : f x = g x :=
  FunLike.congr_fun h x

theorem ext_iff : f = g ↔ ∀ x, f x = g x :=
  FunLike.ext_iff

@[simp]
theorem mk_coe (f : M →ₛₗ[σ] M₃) (h₁ h₂) : (LinearMap.mk f h₁ h₂ : M →ₛₗ[σ] M₃) = f :=
  ext fun _ => rfl

variable (fₗ gₗ f g)

protected theorem map_add (x y : M) : f (x + y) = f x + f y :=
  map_add f x y

protected theorem map_zero : f 0 = 0 :=
  map_zero f

-- TODO: `simp` isn't picking up `map_smulₛₗ` for `linear_map`s without specifying `map_smulₛₗ f`
@[simp]
protected theorem map_smulₛₗ (c : R) (x : M) : f (c • x) = σ c • f x :=
  map_smulₛₗ f c x

protected theorem map_smul (c : R) (x : M) : fₗ (c • x) = c • fₗ x :=
  map_smul fₗ c x

protected theorem map_smul_inv {σ' : S →+* R} [RingHomInvPair σ σ'] (c : S) (x : M) : c • f x = f (σ' c • x) := by
  simp

-- TODO: generalize to `zero_hom_class`
@[simp]
theorem map_eq_zero_iff (h : Function.Injective f) {x : M} : f x = 0 ↔ x = 0 :=
  ⟨fun w => by
    apply h
    simp [← w], fun w => by
    subst w
    simp ⟩

section Pointwise

open Pointwise

variable (M M₃ σ) {F : Type _} (h : F)

@[simp]
theorem _root_.image_smul_setₛₗ [SemilinearMapClass F σ M M₃] (c : R) (s : Set M) : h '' (c • s) = σ c • h '' s := by
  apply Set.Subset.antisymm
  · rintro x ⟨y, ⟨z, zs, rfl⟩, rfl⟩
    exact ⟨h z, Set.mem_image_of_mem _ zs, (map_smulₛₗ _ _ _).symm⟩
    
  · rintro x ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    exact (Set.mem_image _ _ _).2 ⟨c • z, Set.smul_mem_smul_set hz, map_smulₛₗ _ _ _⟩
    

theorem _root_.preimage_smul_setₛₗ [SemilinearMapClass F σ M M₃] {c : R} (hc : IsUnit c) (s : Set M₃) :
    h ⁻¹' (σ c • s) = c • h ⁻¹' s := by
  apply Set.Subset.antisymm
  · rintro x ⟨y, ys, hy⟩
    refine' ⟨(hc.unit.inv : R) • x, _, _⟩
    · simp only [hy, ← smul_smul, ← Set.mem_preimage, ← Units.inv_eq_coe_inv, ← map_smulₛₗ h, map_mul, ←
        IsUnit.coe_inv_mul, ← one_smul, ← map_one, ← ys]
      
    · simp only [← smul_smul, ← IsUnit.mul_coe_inv, ← one_smul, ← Units.inv_eq_coe_inv]
      
    
  · rintro x ⟨y, hy, rfl⟩
    refine'
      ⟨h y, hy, by
        simp only [← RingHom.id_apply, ← map_smulₛₗ h]⟩
    

variable (R M₂)

theorem _root_.image_smul_set [LinearMapClass F R M M₂] (c : R) (s : Set M) : h '' (c • s) = c • h '' s :=
  image_smul_setₛₗ _ _ _ h c s

theorem _root_.preimage_smul_set [LinearMapClass F R M M₂] {c : R} (hc : IsUnit c) (s : Set M₂) :
    h ⁻¹' (c • s) = c • h ⁻¹' s :=
  preimage_smul_setₛₗ _ _ _ h hc s

end Pointwise

variable (M M₂)

/-- A typeclass for `has_smul` structures which can be moved through a `linear_map`.
This typeclass is generated automatically from a `is_scalar_tower` instance, but exists so that
we can also add an instance for `add_comm_group.int_module`, allowing `z •` to be moved even if
`R` does not support negation.
-/
class CompatibleSmul (R S : Type _) [Semiringₓ S] [HasSmul R M] [Module S M] [HasSmul R M₂] [Module S M₂] where
  map_smul : ∀ (fₗ : M →ₗ[S] M₂) (c : R) (x : M), fₗ (c • x) = c • fₗ x

variable {M M₂}

instance (priority := 100) IsScalarTower.compatibleSmul {R S : Type _} [Semiringₓ S] [HasSmul R S] [HasSmul R M]
    [Module S M] [IsScalarTower R S M] [HasSmul R M₂] [Module S M₂] [IsScalarTower R S M₂] : CompatibleSmul M M₂ R S :=
  ⟨fun fₗ c x => by
    rw [← smul_one_smul S c x, ← smul_one_smul S c (fₗ x), map_smul]⟩

@[simp]
theorem map_smul_of_tower {R S : Type _} [Semiringₓ S] [HasSmul R M] [Module S M] [HasSmul R M₂] [Module S M₂]
    [CompatibleSmul M M₂ R S] (fₗ : M →ₗ[S] M₂) (c : R) (x : M) : fₗ (c • x) = c • fₗ x :=
  CompatibleSmul.map_smul fₗ c x

/-- convert a linear map to an additive map -/
def toAddMonoidHom : M →+ M₃ where
  toFun := f
  map_zero' := f.map_zero
  map_add' := f.map_add

@[simp]
theorem to_add_monoid_hom_coe : ⇑f.toAddMonoidHom = f :=
  rfl

section RestrictScalars

variable (R) [Module S M] [Module S M₂] [CompatibleSmul M M₂ R S]

/-- If `M` and `M₂` are both `R`-modules and `S`-modules and `R`-module structures
are defined by an action of `R` on `S` (formally, we have two scalar towers), then any `S`-linear
map from `M` to `M₂` is `R`-linear.

See also `linear_map.map_smul_of_tower`. -/
def restrictScalars (fₗ : M →ₗ[S] M₂) : M →ₗ[R] M₂ where
  toFun := fₗ
  map_add' := fₗ.map_add
  map_smul' := fₗ.map_smul_of_tower

@[simp]
theorem coe_restrict_scalars (fₗ : M →ₗ[S] M₂) : ⇑(restrictScalars R fₗ) = fₗ :=
  rfl

theorem restrict_scalars_apply (fₗ : M →ₗ[S] M₂) (x) : restrictScalars R fₗ x = fₗ x :=
  rfl

theorem restrict_scalars_injective : Function.Injective (restrictScalars R : (M →ₗ[S] M₂) → M →ₗ[R] M₂) :=
  fun fₗ gₗ h => ext (LinearMap.congr_fun h : _)

@[simp]
theorem restrict_scalars_inj (fₗ gₗ : M →ₗ[S] M₂) : fₗ.restrictScalars R = gₗ.restrictScalars R ↔ fₗ = gₗ :=
  (restrict_scalars_injective R).eq_iff

end RestrictScalars

variable {R}

@[simp]
theorem map_sum {ι} {t : Finset ι} {g : ι → M} : f (∑ i in t, g i) = ∑ i in t, f (g i) :=
  f.toAddMonoidHom.map_sum _ _

theorem to_add_monoid_hom_injective : Function.Injective (toAddMonoidHom : (M →ₛₗ[σ] M₃) → M →+ M₃) := fun f g h =>
  ext <| AddMonoidHom.congr_fun h

/-- If two `σ`-linear maps from `R` are equal on `1`, then they are equal. -/
@[ext]
theorem ext_ring {f g : R →ₛₗ[σ] M₃} (h : f 1 = g 1) : f = g :=
  ext fun x => by
    rw [← mul_oneₓ x, ← smul_eq_mul, f.map_smulₛₗ, g.map_smulₛₗ, h]

theorem ext_ring_iff {σ : R →+* R} {f g : R →ₛₗ[σ] M} : f = g ↔ f 1 = g 1 :=
  ⟨fun h => h ▸ rfl, ext_ring⟩

@[ext]
theorem ext_ring_op {σ : Rᵐᵒᵖ →+* S} {f g : R →ₛₗ[σ] M₃} (h : f 1 = g 1) : f = g :=
  ext fun x => by
    rw [← one_mulₓ x, ← op_smul_eq_mul, f.map_smulₛₗ, g.map_smulₛₗ, h]

end

/-- Interpret a `ring_hom` `f` as an `f`-semilinear map. -/
@[simps]
def _root_.ring_hom.to_semilinear_map (f : R →+* S) : R →ₛₗ[f] S :=
  { f with toFun := f, map_smul' := f.map_mul }

section

variable [Semiringₓ R₁] [Semiringₓ R₂] [Semiringₓ R₃]

variable [AddCommMonoidₓ M] [AddCommMonoidₓ M₁] [AddCommMonoidₓ M₂] [AddCommMonoidₓ M₃]

variable {module_M₁ : Module R₁ M₁} {module_M₂ : Module R₂ M₂} {module_M₃ : Module R₃ M₃}

variable {σ₁₂ : R₁ →+* R₂} {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R₁ →+* R₃}

variable [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]

variable (f : M₂ →ₛₗ[σ₂₃] M₃) (g : M₁ →ₛₗ[σ₁₂] M₂)

include module_M₁ module_M₂ module_M₃

/-- Composition of two linear maps is a linear map -/
def comp : M₁ →ₛₗ[σ₁₃] M₃ where
  toFun := f ∘ g
  map_add' := by
    simp only [← map_add, ← forall_const, ← eq_self_iff_true, ← comp_app]
  map_smul' := fun r x => by
    rw [comp_app, map_smulₛₗ, map_smulₛₗ, RingHomCompTriple.comp_apply]

omit module_M₁ module_M₂ module_M₃

-- mathport name: «expr ∘ₗ »
infixr:80 " ∘ₗ " =>
  @LinearMap.comp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (RingHom.id _) (RingHom.id _) (RingHom.id _) RingHomCompTriple.ids

include σ₁₃

theorem comp_apply (x : M₁) : f.comp g x = f (g x) :=
  rfl

omit σ₁₃

include σ₁₃

@[simp, norm_cast]
theorem coe_comp : (f.comp g : M₁ → M₃) = f ∘ g :=
  rfl

omit σ₁₃

@[simp]
theorem comp_id : f.comp id = f :=
  LinearMap.ext fun x => rfl

@[simp]
theorem id_comp : id.comp f = f :=
  LinearMap.ext fun x => rfl

variable {f g} {f' : M₂ →ₛₗ[σ₂₃] M₃} {g' : M₁ →ₛₗ[σ₁₂] M₂}

include σ₁₃

theorem cancel_right (hg : Function.Surjective g) : f.comp g = f'.comp g ↔ f = f' :=
  ⟨fun h => ext <| hg.forall.2 (ext_iff.1 h), fun h => h ▸ rfl⟩

theorem cancel_left (hf : Function.Injective f) : f.comp g = f.comp g' ↔ g = g' :=
  ⟨fun h =>
    ext fun x =>
      hf <| by
        rw [← comp_apply, h, comp_apply],
    fun h => h ▸ rfl⟩

omit σ₁₃

end

variable [AddCommMonoidₓ M] [AddCommMonoidₓ M₁] [AddCommMonoidₓ M₂] [AddCommMonoidₓ M₃]

/-- If a function `g` is a left and right inverse of a linear map `f`, then `g` is linear itself. -/
def inverse [Module R M] [Module S M₂] {σ : R →+* S} {σ' : S →+* R} [RingHomInvPair σ σ'] (f : M →ₛₗ[σ] M₂) (g : M₂ → M)
    (h₁ : LeftInverse g f) (h₂ : RightInverse g f) : M₂ →ₛₗ[σ'] M := by
  dsimp' [← left_inverse, ← Function.RightInverse]  at h₁ h₂ <;>
    exact
      { toFun := g,
        map_add' := fun x y => by
          rw [← h₁ (g (x + y)), ← h₁ (g x + g y)] <;> simp [← h₂],
        map_smul' := fun a b => by
          rw [← h₁ (g (a • b)), ← h₁ (σ' a • g b)]
          simp [← h₂] }

end AddCommMonoidₓ

section AddCommGroupₓ

variable [Semiringₓ R] [Semiringₓ S] [AddCommGroupₓ M] [AddCommGroupₓ M₂]

variable {module_M : Module R M} {module_M₂ : Module S M₂} {σ : R →+* S}

variable (f : M →ₛₗ[σ] M₂)

protected theorem map_neg (x : M) : f (-x) = -f x :=
  map_neg f x

protected theorem map_sub (x y : M) : f (x - y) = f x - f y :=
  map_sub f x y

instance CompatibleSmul.intModule {S : Type _} [Semiringₓ S] [Module S M] [Module S M₂] : CompatibleSmul M M₂ ℤ S :=
  ⟨fun fₗ c x => by
    induction c using Int.induction_on
    case hz =>
      simp
    case hp n ih =>
      simp [← add_smul, ← ih]
    case hn n ih =>
      simp [← sub_smul, ← ih]⟩

instance CompatibleSmul.units {R S : Type _} [Monoidₓ R] [MulAction R M] [MulAction R M₂] [Semiringₓ S] [Module S M]
    [Module S M₂] [CompatibleSmul M M₂ R S] : CompatibleSmul M M₂ Rˣ S :=
  ⟨fun fₗ c x => (CompatibleSmul.map_smul fₗ (c : R) x : _)⟩

end AddCommGroupₓ

end LinearMap

namespace Module

/-- `g : R →+* S` is `R`-linear when the module structure on `S` is `module.comp_hom S g` . -/
@[simps]
def compHom.toLinearMap {R S : Type _} [Semiringₓ R] [Semiringₓ S] (g : R →+* S) :
    have := comp_hom S g
    R →ₗ[R] S where
  toFun := (g : R → S)
  map_add' := g.map_add
  map_smul' := g.map_mul

end Module

namespace DistribMulActionHom

variable [Semiringₓ R] [AddCommMonoidₓ M] [AddCommMonoidₓ M₂] [Module R M] [Module R M₂]

/-- A `distrib_mul_action_hom` between two modules is a linear map. -/
def toLinearMap (fₗ : M →+[R] M₂) : M →ₗ[R] M₂ :=
  { fₗ with }

instance : Coe (M →+[R] M₂) (M →ₗ[R] M₂) :=
  ⟨toLinearMap⟩

@[simp]
theorem to_linear_map_eq_coe (f : M →+[R] M₂) : f.toLinearMap = ↑f :=
  rfl

@[simp, norm_cast]
theorem coe_to_linear_map (f : M →+[R] M₂) : ((f : M →ₗ[R] M₂) : M → M₂) = f :=
  rfl

theorem to_linear_map_injective {f g : M →+[R] M₂} (h : (f : M →ₗ[R] M₂) = (g : M →ₗ[R] M₂)) : f = g := by
  ext m
  exact LinearMap.congr_fun h m

end DistribMulActionHom

namespace IsLinearMap

section AddCommMonoidₓ

variable [Semiringₓ R] [AddCommMonoidₓ M] [AddCommMonoidₓ M₂]

variable [Module R M] [Module R M₂]

include R

/-- Convert an `is_linear_map` predicate to a `linear_map` -/
def mk' (f : M → M₂) (H : IsLinearMap R f) : M →ₗ[R] M₂ where
  toFun := f
  map_add' := H.1
  map_smul' := H.2

@[simp]
theorem mk'_apply {f : M → M₂} (H : IsLinearMap R f) (x : M) : mk' f H x = f x :=
  rfl

theorem is_linear_map_smul {R M : Type _} [CommSemiringₓ R] [AddCommMonoidₓ M] [Module R M] (c : R) :
    IsLinearMap R fun z : M => c • z := by
  refine' IsLinearMap.mk (smul_add c) _
  intro _ _
  simp only [← smul_smul, ← mul_comm]

theorem is_linear_map_smul' {R M : Type _} [Semiringₓ R] [AddCommMonoidₓ M] [Module R M] (a : M) :
    IsLinearMap R fun c : R => c • a :=
  IsLinearMap.mk (fun x y => add_smul x y a) fun x y => mul_smul x y a

variable {f : M → M₂} (lin : IsLinearMap R f)

include M M₂ lin

theorem map_zero : f (0 : M) = (0 : M₂) :=
  (lin.mk' f).map_zero

end AddCommMonoidₓ

section AddCommGroupₓ

variable [Semiringₓ R] [AddCommGroupₓ M] [AddCommGroupₓ M₂]

variable [Module R M] [Module R M₂]

include R

theorem is_linear_map_neg : IsLinearMap R fun z : M => -z :=
  IsLinearMap.mk neg_add fun x y => (smul_neg x y).symm

variable {f : M → M₂} (lin : IsLinearMap R f)

include M M₂ lin

theorem map_neg (x : M) : f (-x) = -f x :=
  (lin.mk' f).map_neg x

theorem map_sub (x y) : f (x - y) = f x - f y :=
  (lin.mk' f).map_sub x y

end AddCommGroupₓ

end IsLinearMap

/-- Linear endomorphisms of a module, with associated ring structure
`module.End.semiring` and algebra structure `module.End.algebra`. -/
abbrev Module.End (R : Type u) (M : Type v) [Semiringₓ R] [AddCommMonoidₓ M] [Module R M] :=
  M →ₗ[R] M

/-- Reinterpret an additive homomorphism as a `ℕ`-linear map. -/
def AddMonoidHom.toNatLinearMap [AddCommMonoidₓ M] [AddCommMonoidₓ M₂] (f : M →+ M₂) : M →ₗ[ℕ] M₂ where
  toFun := f
  map_add' := f.map_add
  map_smul' := map_nsmul f

theorem AddMonoidHom.to_nat_linear_map_injective [AddCommMonoidₓ M] [AddCommMonoidₓ M₂] :
    Function.Injective (@AddMonoidHom.toNatLinearMap M M₂ _ _) := by
  intro f g h
  ext
  exact LinearMap.congr_fun h x

/-- Reinterpret an additive homomorphism as a `ℤ`-linear map. -/
def AddMonoidHom.toIntLinearMap [AddCommGroupₓ M] [AddCommGroupₓ M₂] (f : M →+ M₂) : M →ₗ[ℤ] M₂ where
  toFun := f
  map_add' := f.map_add
  map_smul' := map_zsmul f

theorem AddMonoidHom.to_int_linear_map_injective [AddCommGroupₓ M] [AddCommGroupₓ M₂] :
    Function.Injective (@AddMonoidHom.toIntLinearMap M M₂ _ _) := by
  intro f g h
  ext
  exact LinearMap.congr_fun h x

@[simp]
theorem AddMonoidHom.coe_to_int_linear_map [AddCommGroupₓ M] [AddCommGroupₓ M₂] (f : M →+ M₂) : ⇑f.toIntLinearMap = f :=
  rfl

/-- Reinterpret an additive homomorphism as a `ℚ`-linear map. -/
def AddMonoidHom.toRatLinearMap [AddCommGroupₓ M] [Module ℚ M] [AddCommGroupₓ M₂] [Module ℚ M₂] (f : M →+ M₂) :
    M →ₗ[ℚ] M₂ :=
  { f with map_smul' := map_rat_smul f }

theorem AddMonoidHom.to_rat_linear_map_injective [AddCommGroupₓ M] [Module ℚ M] [AddCommGroupₓ M₂] [Module ℚ M₂] :
    Function.Injective (@AddMonoidHom.toRatLinearMap M M₂ _ _ _ _) := by
  intro f g h
  ext
  exact LinearMap.congr_fun h x

@[simp]
theorem AddMonoidHom.coe_to_rat_linear_map [AddCommGroupₓ M] [Module ℚ M] [AddCommGroupₓ M₂] [Module ℚ M₂]
    (f : M →+ M₂) : ⇑f.toRatLinearMap = f :=
  rfl

namespace LinearMap

section HasSmul

variable [Semiringₓ R] [Semiringₓ R₂] [Semiringₓ R₃]

variable [AddCommMonoidₓ M] [AddCommMonoidₓ M₂] [AddCommMonoidₓ M₃]

variable [Module R M] [Module R₂ M₂] [Module R₃ M₃]

variable {σ₁₂ : R →+* R₂} {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R →+* R₃} [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]

variable [Monoidₓ S] [DistribMulAction S M₂] [SmulCommClass R₂ S M₂]

variable [Monoidₓ S₃] [DistribMulAction S₃ M₃] [SmulCommClass R₃ S₃ M₃]

variable [Monoidₓ T] [DistribMulAction T M₂] [SmulCommClass R₂ T M₂]

instance : HasSmul S (M →ₛₗ[σ₁₂] M₂) :=
  ⟨fun a f =>
    { toFun := a • f,
      map_add' := fun x y => by
        simp only [← Pi.smul_apply, ← f.map_add, ← smul_add],
      map_smul' := fun c x => by
        simp [← Pi.smul_apply, ← smul_comm (σ₁₂ c)] }⟩

@[simp]
theorem smul_apply (a : S) (f : M →ₛₗ[σ₁₂] M₂) (x : M) : (a • f) x = a • f x :=
  rfl

theorem coe_smul (a : S) (f : M →ₛₗ[σ₁₂] M₂) : ⇑(a • f) = a • f :=
  rfl

instance [SmulCommClass S T M₂] : SmulCommClass S T (M →ₛₗ[σ₁₂] M₂) :=
  ⟨fun a b f => ext fun x => smul_comm _ _ _⟩

-- example application of this instance: if S -> T -> R are homomorphisms of commutative rings and
-- M and M₂ are R-modules then the S-module and T-module structures on Hom_R(M,M₂) are compatible.
instance [HasSmul S T] [IsScalarTower S T M₂] :
    IsScalarTower S T (M →ₛₗ[σ₁₂] M₂) where smul_assoc := fun _ _ _ => ext fun _ => smul_assoc _ _ _

instance [DistribMulAction Sᵐᵒᵖ M₂] [SmulCommClass R₂ Sᵐᵒᵖ M₂] [IsCentralScalar S M₂] :
    IsCentralScalar S (M →ₛₗ[σ₁₂] M₂) where op_smul_eq_smul := fun a b => ext fun x => op_smul_eq_smul _ _

end HasSmul

/-! ### Arithmetic on the codomain -/


section Arithmetic

variable [Semiringₓ R₁] [Semiringₓ R₂] [Semiringₓ R₃]

variable [AddCommMonoidₓ M] [AddCommMonoidₓ M₂] [AddCommMonoidₓ M₃]

variable [AddCommGroupₓ N₁] [AddCommGroupₓ N₂] [AddCommGroupₓ N₃]

variable [Module R₁ M] [Module R₂ M₂] [Module R₃ M₃]

variable [Module R₁ N₁] [Module R₂ N₂] [Module R₃ N₃]

variable {σ₁₂ : R₁ →+* R₂} {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R₁ →+* R₃} [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]

/-- The constant 0 map is linear. -/
instance : Zero (M →ₛₗ[σ₁₂] M₂) :=
  ⟨{ toFun := 0,
      map_add' := by
        simp ,
      map_smul' := by
        simp }⟩

@[simp]
theorem zero_apply (x : M) : (0 : M →ₛₗ[σ₁₂] M₂) x = 0 :=
  rfl

@[simp]
theorem comp_zero (g : M₂ →ₛₗ[σ₂₃] M₃) : (g.comp (0 : M →ₛₗ[σ₁₂] M₂) : M →ₛₗ[σ₁₃] M₃) = 0 :=
  ext fun c => by
    rw [comp_apply, zero_apply, zero_apply, g.map_zero]

@[simp]
theorem zero_comp (f : M →ₛₗ[σ₁₂] M₂) : ((0 : M₂ →ₛₗ[σ₂₃] M₃).comp f : M →ₛₗ[σ₁₃] M₃) = 0 :=
  rfl

instance : Inhabited (M →ₛₗ[σ₁₂] M₂) :=
  ⟨0⟩

@[simp]
theorem default_def : (default : M →ₛₗ[σ₁₂] M₂) = 0 :=
  rfl

/-- The sum of two linear maps is linear. -/
instance : Add (M →ₛₗ[σ₁₂] M₂) :=
  ⟨fun f g =>
    { toFun := f + g,
      map_add' := by
        simp [← add_commₓ, ← add_left_commₓ],
      map_smul' := by
        simp [← smul_add] }⟩

@[simp]
theorem add_apply (f g : M →ₛₗ[σ₁₂] M₂) (x : M) : (f + g) x = f x + g x :=
  rfl

theorem add_comp (f : M →ₛₗ[σ₁₂] M₂) (g h : M₂ →ₛₗ[σ₂₃] M₃) : ((h + g).comp f : M →ₛₗ[σ₁₃] M₃) = h.comp f + g.comp f :=
  rfl

theorem comp_add (f g : M →ₛₗ[σ₁₂] M₂) (h : M₂ →ₛₗ[σ₂₃] M₃) : (h.comp (f + g) : M →ₛₗ[σ₁₃] M₃) = h.comp f + h.comp g :=
  ext fun _ => h.map_add _ _

/-- The type of linear maps is an additive monoid. -/
instance : AddCommMonoidₓ (M →ₛₗ[σ₁₂] M₂) :=
  FunLike.coe_injective.AddCommMonoid _ rfl (fun _ _ => rfl) fun _ _ => rfl

/-- The negation of a linear map is linear. -/
instance : Neg (M →ₛₗ[σ₁₂] N₂) :=
  ⟨fun f =>
    { toFun := -f,
      map_add' := by
        simp [← add_commₓ],
      map_smul' := by
        simp }⟩

@[simp]
theorem neg_apply (f : M →ₛₗ[σ₁₂] N₂) (x : M) : (-f) x = -f x :=
  rfl

include σ₁₃

@[simp]
theorem neg_comp (f : M →ₛₗ[σ₁₂] M₂) (g : M₂ →ₛₗ[σ₂₃] N₃) : (-g).comp f = -g.comp f :=
  rfl

@[simp]
theorem comp_neg (f : M →ₛₗ[σ₁₂] N₂) (g : N₂ →ₛₗ[σ₂₃] N₃) : g.comp (-f) = -g.comp f :=
  ext fun _ => g.map_neg _

omit σ₁₃

/-- The negation of a linear map is linear. -/
instance : Sub (M →ₛₗ[σ₁₂] N₂) :=
  ⟨fun f g =>
    { toFun := f - g,
      map_add' := fun x y => by
        simp only [← Pi.sub_apply, ← map_add, ← add_sub_add_comm],
      map_smul' := fun r x => by
        simp [← Pi.sub_apply, ← map_smul, ← smul_sub] }⟩

@[simp]
theorem sub_apply (f g : M →ₛₗ[σ₁₂] N₂) (x : M) : (f - g) x = f x - g x :=
  rfl

include σ₁₃

theorem sub_comp (f : M →ₛₗ[σ₁₂] M₂) (g h : M₂ →ₛₗ[σ₂₃] N₃) : (g - h).comp f = g.comp f - h.comp f :=
  rfl

theorem comp_sub (f g : M →ₛₗ[σ₁₂] N₂) (h : N₂ →ₛₗ[σ₂₃] N₃) : h.comp (g - f) = h.comp g - h.comp f :=
  ext fun _ => h.map_sub _ _

omit σ₁₃

/-- The type of linear maps is an additive group. -/
instance : AddCommGroupₓ (M →ₛₗ[σ₁₂] N₂) :=
  FunLike.coe_injective.AddCommGroup _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ =>
    rfl

end Arithmetic

section Actions

variable [Semiringₓ R] [Semiringₓ R₂] [Semiringₓ R₃]

variable [AddCommMonoidₓ M] [AddCommMonoidₓ M₂] [AddCommMonoidₓ M₃]

variable [Module R M] [Module R₂ M₂] [Module R₃ M₃]

variable {σ₁₂ : R →+* R₂} {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R →+* R₃} [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]

section HasSmul

variable [Monoidₓ S] [DistribMulAction S M₂] [SmulCommClass R₂ S M₂]

variable [Monoidₓ S₃] [DistribMulAction S₃ M₃] [SmulCommClass R₃ S₃ M₃]

variable [Monoidₓ T] [DistribMulAction T M₂] [SmulCommClass R₂ T M₂]

instance : DistribMulAction S (M →ₛₗ[σ₁₂] M₂) where
  one_smul := fun f => ext fun _ => one_smul _ _
  mul_smul := fun c c' f => ext fun _ => mul_smul _ _ _
  smul_add := fun c f g => ext fun x => smul_add _ _ _
  smul_zero := fun c => ext fun x => smul_zero _

include σ₁₃

theorem smul_comp (a : S₃) (g : M₂ →ₛₗ[σ₂₃] M₃) (f : M →ₛₗ[σ₁₂] M₂) : (a • g).comp f = a • g.comp f :=
  rfl

omit σ₁₃

-- TODO: generalize this to semilinear maps
theorem comp_smul [Module R M₂] [Module R M₃] [SmulCommClass R S M₂] [DistribMulAction S M₃] [SmulCommClass R S M₃]
    [CompatibleSmul M₃ M₂ S R] (g : M₃ →ₗ[R] M₂) (a : S) (f : M →ₗ[R] M₃) : g.comp (a • f) = a • g.comp f :=
  ext fun x => g.map_smul_of_tower _ _

end HasSmul

section Module

variable [Semiringₓ S] [Module S M₂] [SmulCommClass R₂ S M₂]

instance : Module S (M →ₛₗ[σ₁₂] M₂) where
  add_smul := fun a b f => ext fun x => add_smul _ _ _
  zero_smul := fun f => ext fun x => zero_smul _ _

instance [NoZeroSmulDivisors S M₂] : NoZeroSmulDivisors S (M →ₛₗ[σ₁₂] M₂) :=
  coe_injective.NoZeroSmulDivisors _ rfl coe_smul

end Module

end Actions

/-!
### Monoid structure of endomorphisms

Lemmas about `pow` such as `linear_map.pow_apply` appear in later files.
-/


section Endomorphisms

variable [Semiringₓ R] [AddCommMonoidₓ M] [AddCommGroupₓ N₁] [Module R M] [Module R N₁]

instance : One (Module.End R M) :=
  ⟨LinearMap.id⟩

instance : Mul (Module.End R M) :=
  ⟨LinearMap.comp⟩

theorem one_eq_id : (1 : Module.End R M) = id :=
  rfl

theorem mul_eq_comp (f g : Module.End R M) : f * g = f.comp g :=
  rfl

@[simp]
theorem one_apply (x : M) : (1 : Module.End R M) x = x :=
  rfl

@[simp]
theorem mul_apply (f g : Module.End R M) (x : M) : (f * g) x = f (g x) :=
  rfl

theorem coe_one : ⇑(1 : Module.End R M) = _root_.id :=
  rfl

theorem coe_mul (f g : Module.End R M) : ⇑(f * g) = f ∘ g :=
  rfl

instance _root_.module.End.monoid : Monoidₓ (Module.End R M) where
  mul := (· * ·)
  one := (1 : M →ₗ[R] M)
  mul_assoc := fun f g h => LinearMap.ext fun x => rfl
  mul_one := comp_id
  one_mul := id_comp

instance _root_.module.End.semiring : Semiringₓ (Module.End R M) :=
  { AddMonoidWithOneₓ.unary, Module.End.monoid, LinearMap.addCommMonoid with mul := (· * ·), one := (1 : M →ₗ[R] M),
    zero := 0, add := (· + ·), mul_zero := comp_zero, zero_mul := zero_comp,
    left_distrib := fun f g h => comp_add _ _ _, right_distrib := fun f g h => add_comp _ _ _ }

instance _root_.module.End.ring : Ringₓ (Module.End R N₁) :=
  { Module.End.semiring, LinearMap.addCommGroup with }

section

variable [Monoidₓ S] [DistribMulAction S M] [SmulCommClass R S M]

instance _root_.module.End.is_scalar_tower : IsScalarTower S (Module.End R M) (Module.End R M) :=
  ⟨smul_comp⟩

instance _root_.module.End.smul_comm_class [HasSmul S R] [IsScalarTower S R M] :
    SmulCommClass S (Module.End R M) (Module.End R M) :=
  ⟨fun s _ _ => (comp_smul _ s _).symm⟩

instance _root_.module.End.smul_comm_class' [HasSmul S R] [IsScalarTower S R M] :
    SmulCommClass (Module.End R M) S (Module.End R M) :=
  SmulCommClass.symm _ _ _

end

/-! ### Action by a module endomorphism. -/


/-- The tautological action by `module.End R M` (aka `M →ₗ[R] M`) on `M`.

This generalizes `function.End.apply_mul_action`. -/
instance applyModule : Module (Module.End R M) M where
  smul := (· <| ·)
  smul_zero := LinearMap.map_zero
  smul_add := LinearMap.map_add
  add_smul := LinearMap.add_apply
  zero_smul := (LinearMap.zero_apply : ∀ m, (0 : M →ₗ[R] M) m = 0)
  one_smul := fun _ => rfl
  mul_smul := fun _ _ _ => rfl

@[simp]
protected theorem smul_def (f : Module.End R M) (a : M) : f • a = f a :=
  rfl

/-- `linear_map.apply_module` is faithful. -/
instance apply_has_faithful_smul : HasFaithfulSmul (Module.End R M) M :=
  ⟨fun _ _ => LinearMap.ext⟩

instance apply_smul_comm_class :
    SmulCommClass R (Module.End R M) M where smul_comm := fun r e m => (e.map_smul r m).symm

instance apply_smul_comm_class' : SmulCommClass (Module.End R M) R M where smul_comm := LinearMap.map_smul

instance apply_is_scalar_tower {R M : Type _} [CommSemiringₓ R] [AddCommMonoidₓ M] [Module R M] :
    IsScalarTower R (Module.End R M) M :=
  ⟨fun t f m => rfl⟩

end Endomorphisms

end LinearMap

/-! ### Actions as module endomorphisms -/


namespace DistribMulAction

variable (R M) [Semiringₓ R] [AddCommMonoidₓ M] [Module R M]

variable [Monoidₓ S] [DistribMulAction S M] [SmulCommClass S R M]

/-- Each element of the monoid defines a linear map.

This is a stronger version of `distrib_mul_action.to_add_monoid_hom`. -/
@[simps]
def toLinearMap (s : S) : M →ₗ[R] M where
  toFun := HasSmul.smul s
  map_add' := smul_add s
  map_smul' := fun a b => smul_comm _ _ _

/-- Each element of the monoid defines a module endomorphism.

This is a stronger version of `distrib_mul_action.to_add_monoid_End`. -/
@[simps]
def toModuleEnd : S →* Module.End R M where
  toFun := toLinearMap R M
  map_one' := LinearMap.ext <| one_smul _
  map_mul' := fun a b => LinearMap.ext <| mul_smul _ _

end DistribMulAction

namespace Module

variable (R M) [Semiringₓ R] [AddCommMonoidₓ M] [Module R M]

variable [Semiringₓ S] [Module S M] [SmulCommClass S R M]

/-- Each element of the monoid defines a module endomorphism.

This is a stronger version of `distrib_mul_action.to_module_End`. -/
@[simps]
def toModuleEnd : S →+* Module.End R M :=
  { DistribMulAction.toModuleEnd R M with toFun := DistribMulAction.toLinearMap R M,
    map_zero' := LinearMap.ext <| zero_smul _, map_add' := fun f g => LinearMap.ext <| add_smul _ _ }

/-- The canonical (semi)ring isomorphism from `Rᵐᵒᵖ` to `module.End R R` induced by the right
multiplication. -/
@[simps]
def moduleEndSelf : Rᵐᵒᵖ ≃+* Module.End R R :=
  { Module.toModuleEnd R R with toFun := DistribMulAction.toLinearMap R R, invFun := fun f => MulOpposite.op (f 1),
    left_inv := mul_oneₓ, right_inv := fun f => LinearMap.ext_ring <| one_mulₓ _ }

/-- The canonical (semi)ring isomorphism from `R` to `module.End Rᵐᵒᵖ R` induced by the left
multiplication. -/
@[simps]
def moduleEndSelfOp : R ≃+* Module.End Rᵐᵒᵖ R :=
  { Module.toModuleEnd _ _ with toFun := DistribMulAction.toLinearMap _ _, invFun := fun f => f 1, left_inv := mul_oneₓ,
    right_inv := fun f => LinearMap.ext_ring_op <| mul_oneₓ _ }

end Module

