/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaniel Thomas, Jeremy Avigad, Johannes Hölzl, Mario Carneiro, Anne Baanen,
  Frédéric Dupuis, Heather Macbeth
-/
import Mathbin.Algebra.Module.LinearMap

/-!
# (Semi)linear equivalences

In this file we define

* `linear_equiv σ M M₂`, `M ≃ₛₗ[σ] M₂`: an invertible semilinear map. Here, `σ` is a `ring_hom`
  from `R` to `R₂` and an `e : M ≃ₛₗ[σ] M₂` satisfies `e (c • x) = (σ c) • (e x)`. The plain
  linear version, with `σ` being `ring_hom.id R`, is denoted by `M ≃ₗ[R] M₂`, and the
  star-linear version (with `σ` being `star_ring_end`) is denoted by `M ≃ₗ⋆[R] M₂`.

## Implementation notes

To ensure that composition works smoothly for semilinear equivalences, we use the typeclasses
`ring_hom_comp_triple`, `ring_hom_inv_pair` and `ring_hom_surjective` from
`algebra/ring/comp_typeclasses`.

The group structure on automorphisms, `linear_equiv.automorphism_group`, is provided elsewhere.

## TODO

* Parts of this file have not yet been generalized to semilinear maps

## Tags

linear equiv, linear equivalences, linear isomorphism, linear isomorphic
-/


open Function

open BigOperators

universe u u' v w x y z

variable {R : Type _} {R₁ : Type _} {R₂ : Type _} {R₃ : Type _}

variable {k : Type _} {S : Type _} {M : Type _} {M₁ : Type _} {M₂ : Type _} {M₃ : Type _}

variable {N₁ : Type _} {N₂ : Type _} {N₃ : Type _} {N₄ : Type _} {ι : Type _}

section

/-- A linear equivalence is an invertible linear map. -/
@[nolint has_inhabited_instance]
structure LinearEquiv {R : Type _} {S : Type _} [Semiringₓ R] [Semiringₓ S] (σ : R →+* S) {σ' : S →+* R}
  [RingHomInvPair σ σ'] [RingHomInvPair σ' σ] (M : Type _) (M₂ : Type _) [AddCommMonoidₓ M] [AddCommMonoidₓ M₂]
  [Module R M] [Module S M₂] extends LinearMap σ M M₂, M ≃+ M₂

end

attribute [nolint doc_blame] LinearEquiv.toLinearMap

attribute [nolint doc_blame] LinearEquiv.toAddEquiv

-- mathport name: «expr ≃ₛₗ[ ] »
notation:50 M " ≃ₛₗ[" σ "] " M₂ => LinearEquiv σ M M₂

-- mathport name: «expr ≃ₗ[ ] »
notation:50 M " ≃ₗ[" R "] " M₂ => LinearEquiv (RingHom.id R) M M₂

-- mathport name: «expr ≃ₗ⋆[ ] »
notation:50 M " ≃ₗ⋆[" R "] " M₂ => LinearEquiv (starRingEnd R) M M₂

namespace LinearEquiv

section AddCommMonoidₓ

variable {M₄ : Type _}

variable [Semiringₓ R] [Semiringₓ S]

section

variable [AddCommMonoidₓ M] [AddCommMonoidₓ M₁] [AddCommMonoidₓ M₂]

variable [Module R M] [Module S M₂] {σ : R →+* S} {σ' : S →+* R}

variable [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]

include R

include σ'

instance : Coe (M ≃ₛₗ[σ] M₂) (M →ₛₗ[σ] M₂) :=
  ⟨toLinearMap⟩

-- see Note [function coercion]
instance : CoeFun (M ≃ₛₗ[σ] M₂) fun _ => M → M₂ :=
  ⟨toFun⟩

@[simp]
theorem coe_mk {to_fun inv_fun map_add map_smul left_inv right_inv} :
    ⇑(⟨to_fun, map_add, map_smul, inv_fun, left_inv, right_inv⟩ : M ≃ₛₗ[σ] M₂) = to_fun :=
  rfl

-- This exists for compatibility, previously `≃ₗ[R]` extended `≃` instead of `≃+`.
@[nolint doc_blame]
def toEquiv : (M ≃ₛₗ[σ] M₂) → M ≃ M₂ := fun f => f.toAddEquiv.toEquiv

theorem to_equiv_injective : Function.Injective (toEquiv : (M ≃ₛₗ[σ] M₂) → M ≃ M₂) :=
  fun ⟨_, _, _, _, _, _⟩ ⟨_, _, _, _, _, _⟩ h => LinearEquiv.mk.inj_eq.mpr (Equivₓ.mk.inj h)

@[simp]
theorem to_equiv_inj {e₁ e₂ : M ≃ₛₗ[σ] M₂} : e₁.toEquiv = e₂.toEquiv ↔ e₁ = e₂ :=
  to_equiv_injective.eq_iff

theorem to_linear_map_injective : Injective (coe : (M ≃ₛₗ[σ] M₂) → M →ₛₗ[σ] M₂) := fun e₁ e₂ H =>
  to_equiv_injective <| Equivₓ.ext <| LinearMap.congr_fun H

@[simp, norm_cast]
theorem to_linear_map_inj {e₁ e₂ : M ≃ₛₗ[σ] M₂} : (e₁ : M →ₛₗ[σ] M₂) = e₂ ↔ e₁ = e₂ :=
  to_linear_map_injective.eq_iff

instance : SemilinearMapClass (M ≃ₛₗ[σ] M₂) σ M M₂ where
  coe := LinearEquiv.toFun
  coe_injective' := fun f g h => to_linear_map_injective (FunLike.coe_injective h)
  map_add := map_add'
  map_smulₛₗ := map_smul'

theorem coe_injective : @Injective (M ≃ₛₗ[σ] M₂) (M → M₂) coeFn :=
  FunLike.coe_injective

end

section

variable [Semiringₓ R₁] [Semiringₓ R₂] [Semiringₓ R₃]

variable [AddCommMonoidₓ M] [AddCommMonoidₓ M₁] [AddCommMonoidₓ M₂]

variable [AddCommMonoidₓ M₃] [AddCommMonoidₓ M₄]

variable [AddCommMonoidₓ N₁] [AddCommMonoidₓ N₂]

variable {module_M : Module R M} {module_S_M₂ : Module S M₂} {σ : R →+* S} {σ' : S →+* R}

variable {re₁ : RingHomInvPair σ σ'} {re₂ : RingHomInvPair σ' σ}

variable (e e' : M ≃ₛₗ[σ] M₂)

theorem to_linear_map_eq_coe : e.toLinearMap = (e : M →ₛₗ[σ] M₂) :=
  rfl

@[simp, norm_cast]
theorem coe_coe : ⇑(e : M →ₛₗ[σ] M₂) = e :=
  rfl

@[simp]
theorem coe_to_equiv : ⇑e.toEquiv = e :=
  rfl

@[simp]
theorem coe_to_linear_map : ⇑e.toLinearMap = e :=
  rfl

@[simp]
theorem to_fun_eq_coe : e.toFun = e :=
  rfl

section

variable {e e'}

@[ext]
theorem ext (h : ∀ x, e x = e' x) : e = e' :=
  FunLike.ext _ _ h

theorem ext_iff : e = e' ↔ ∀ x, e x = e' x :=
  FunLike.ext_iff

protected theorem congr_arg {x x'} : x = x' → e x = e x' :=
  FunLike.congr_arg e

protected theorem congr_fun (h : e = e') (x : M) : e x = e' x :=
  FunLike.congr_fun h x

end

section

variable (M R)

/-- The identity map is a linear equivalence. -/
@[refl]
def refl [Module R M] : M ≃ₗ[R] M :=
  { LinearMap.id, Equivₓ.refl M with }

end

@[simp]
theorem refl_apply [Module R M] (x : M) : refl R M x = x :=
  rfl

include module_M module_S_M₂ re₁ re₂

/-- Linear equivalences are symmetric. -/
@[symm]
def symm (e : M ≃ₛₗ[σ] M₂) : M₂ ≃ₛₗ[σ'] M :=
  { e.toLinearMap.inverse e.invFun e.left_inv e.right_inv, e.toEquiv.symm with
    toFun := e.toLinearMap.inverse e.invFun e.left_inv e.right_inv, invFun := e.toEquiv.symm.invFun,
    map_smul' := fun r x => by
      rw [map_smulₛₗ] }

omit module_M module_S_M₂ re₁ re₂

/-- See Note [custom simps projection] -/
def Simps.symmApply {R : Type _} {S : Type _} [Semiringₓ R] [Semiringₓ S] {σ : R →+* S} {σ' : S →+* R}
    [RingHomInvPair σ σ'] [RingHomInvPair σ' σ] {M : Type _} {M₂ : Type _} [AddCommMonoidₓ M] [AddCommMonoidₓ M₂]
    [Module R M] [Module S M₂] (e : M ≃ₛₗ[σ] M₂) : M₂ → M :=
  e.symm

initialize_simps_projections LinearEquiv (toFun → apply, invFun → symmApply)

include σ'

@[simp]
theorem inv_fun_eq_symm : e.invFun = e.symm :=
  rfl

omit σ'

@[simp]
theorem coe_to_equiv_symm : ⇑e.toEquiv.symm = e.symm :=
  rfl

variable {module_M₁ : Module R₁ M₁} {module_M₂ : Module R₂ M₂} {module_M₃ : Module R₃ M₃}

variable {module_N₁ : Module R₁ N₁} {module_N₂ : Module R₁ N₂}

variable {σ₁₂ : R₁ →+* R₂} {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R₁ →+* R₃}

variable {σ₂₁ : R₂ →+* R₁} {σ₃₂ : R₃ →+* R₂} {σ₃₁ : R₃ →+* R₁}

variable [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]

variable [RingHomCompTriple σ₃₂ σ₂₁ σ₃₁]

variable {re₁₂ : RingHomInvPair σ₁₂ σ₂₁} {re₂₃ : RingHomInvPair σ₂₃ σ₃₂}

variable [RingHomInvPair σ₁₃ σ₃₁] {re₂₁ : RingHomInvPair σ₂₁ σ₁₂}

variable {re₃₂ : RingHomInvPair σ₃₂ σ₂₃} [RingHomInvPair σ₃₁ σ₁₃]

variable (e₁₂ : M₁ ≃ₛₗ[σ₁₂] M₂) (e₂₃ : M₂ ≃ₛₗ[σ₂₃] M₃)

include σ₃₁

/-- Linear equivalences are transitive. -/
-- Note: The linter thinks the `ring_hom_comp_triple` argument is doubled -- it is not.
@[trans, nolint unused_arguments]
def trans : M₁ ≃ₛₗ[σ₁₃] M₃ :=
  { e₂₃.toLinearMap.comp e₁₂.toLinearMap, e₁₂.toEquiv.trans e₂₃.toEquiv with }

omit σ₃₁

-- mathport name: «expr ≪≫ₗ »
infixl:80 " ≪≫ₗ " =>
  @LinearEquiv.trans _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (RingHom.id _) (RingHom.id _) (RingHom.id _) (RingHom.id _)
    (RingHom.id _) (RingHom.id _) RingHomCompTriple.ids RingHomCompTriple.ids RingHomInvPair.ids RingHomInvPair.ids
    RingHomInvPair.ids RingHomInvPair.ids RingHomInvPair.ids RingHomInvPair.ids

variable {e₁₂} {e₂₃}

@[simp]
theorem coe_to_add_equiv : ⇑e.toAddEquiv = e :=
  rfl

/-- The two paths coercion can take to an `add_monoid_hom` are equivalent -/
theorem to_add_monoid_hom_commutes : e.toLinearMap.toAddMonoidHom = e.toAddEquiv.toAddMonoidHom :=
  rfl

include σ₃₁

@[simp]
theorem trans_apply (c : M₁) : (e₁₂.trans e₂₃ : M₁ ≃ₛₗ[σ₁₃] M₃) c = e₂₃ (e₁₂ c) :=
  rfl

omit σ₃₁

include σ'

@[simp]
theorem apply_symm_apply (c : M₂) : e (e.symm c) = c :=
  e.right_inv c

@[simp]
theorem symm_apply_apply (b : M) : e.symm (e b) = b :=
  e.left_inv b

omit σ'

include σ₃₁ σ₂₁ σ₃₂

@[simp]
theorem trans_symm : (e₁₂.trans e₂₃ : M₁ ≃ₛₗ[σ₁₃] M₃).symm = e₂₃.symm.trans e₁₂.symm :=
  rfl

theorem symm_trans_apply (c : M₃) : (e₁₂.trans e₂₃ : M₁ ≃ₛₗ[σ₁₃] M₃).symm c = e₁₂.symm (e₂₃.symm c) :=
  rfl

omit σ₃₁ σ₂₁ σ₃₂

@[simp]
theorem trans_refl : e.trans (refl S M₂) = e :=
  to_equiv_injective e.toEquiv.trans_refl

@[simp]
theorem refl_trans : (refl R M).trans e = e :=
  to_equiv_injective e.toEquiv.refl_trans

include σ'

theorem symm_apply_eq {x y} : e.symm x = y ↔ x = e y :=
  e.toEquiv.symm_apply_eq

theorem eq_symm_apply {x y} : y = e.symm x ↔ e y = x :=
  e.toEquiv.eq_symm_apply

omit σ'

theorem eq_comp_symm {α : Type _} (f : M₂ → α) (g : M₁ → α) : f = g ∘ e₁₂.symm ↔ f ∘ e₁₂ = g :=
  e₁₂.toEquiv.eq_comp_symm f g

theorem comp_symm_eq {α : Type _} (f : M₂ → α) (g : M₁ → α) : g ∘ e₁₂.symm = f ↔ g = f ∘ e₁₂ :=
  e₁₂.toEquiv.comp_symm_eq f g

theorem eq_symm_comp {α : Type _} (f : α → M₁) (g : α → M₂) : f = e₁₂.symm ∘ g ↔ e₁₂ ∘ f = g :=
  e₁₂.toEquiv.eq_symm_comp f g

theorem symm_comp_eq {α : Type _} (f : α → M₁) (g : α → M₂) : e₁₂.symm ∘ g = f ↔ g = e₁₂ ∘ f :=
  e₁₂.toEquiv.symm_comp_eq f g

variable [RingHomCompTriple σ₂₁ σ₁₃ σ₂₃] [RingHomCompTriple σ₃₁ σ₁₂ σ₃₂]

include module_M₃

theorem eq_comp_to_linear_map_symm (f : M₂ →ₛₗ[σ₂₃] M₃) (g : M₁ →ₛₗ[σ₁₃] M₃) :
    f = g.comp e₁₂.symm.toLinearMap ↔ f.comp e₁₂.toLinearMap = g := by
  constructor <;> intro H <;> ext
  · simp [← H, ← e₁₂.to_equiv.eq_comp_symm f g]
    
  · simp [H, e₁₂.to_equiv.eq_comp_symm f g]
    

theorem comp_to_linear_map_symm_eq (f : M₂ →ₛₗ[σ₂₃] M₃) (g : M₁ →ₛₗ[σ₁₃] M₃) :
    g.comp e₁₂.symm.toLinearMap = f ↔ g = f.comp e₁₂.toLinearMap := by
  constructor <;> intro H <;> ext
  · simp [H, e₁₂.to_equiv.comp_symm_eq f g]
    
  · simp [← H, ← e₁₂.to_equiv.comp_symm_eq f g]
    

theorem eq_to_linear_map_symm_comp (f : M₃ →ₛₗ[σ₃₁] M₁) (g : M₃ →ₛₗ[σ₃₂] M₂) :
    f = e₁₂.symm.toLinearMap.comp g ↔ e₁₂.toLinearMap.comp f = g := by
  constructor <;> intro H <;> ext
  · simp [← H, ← e₁₂.to_equiv.eq_symm_comp f g]
    
  · simp [H, e₁₂.to_equiv.eq_symm_comp f g]
    

theorem to_linear_map_symm_comp_eq (f : M₃ →ₛₗ[σ₃₁] M₁) (g : M₃ →ₛₗ[σ₃₂] M₂) :
    e₁₂.symm.toLinearMap.comp g = f ↔ g = e₁₂.toLinearMap.comp f := by
  constructor <;> intro H <;> ext
  · simp [H, e₁₂.to_equiv.symm_comp_eq f g]
    
  · simp [← H, ← e₁₂.to_equiv.symm_comp_eq f g]
    

omit module_M₃

@[simp]
theorem refl_symm [Module R M] : (refl R M).symm = LinearEquiv.refl R M :=
  rfl

@[simp]
theorem self_trans_symm [Module R M] [Module R M₂] (f : M ≃ₗ[R] M₂) : f.trans f.symm = LinearEquiv.refl R M := by
  ext x
  simp

@[simp]
theorem symm_trans_self [Module R M] [Module R M₂] (f : M ≃ₗ[R] M₂) : f.symm.trans f = LinearEquiv.refl R M₂ := by
  ext x
  simp

@[simp, norm_cast]
theorem refl_to_linear_map [Module R M] : (LinearEquiv.refl R M : M →ₗ[R] M) = LinearMap.id :=
  rfl

@[simp, norm_cast]
theorem comp_coe [Module R M] [Module R M₂] [Module R M₃] (f : M ≃ₗ[R] M₂) (f' : M₂ ≃ₗ[R] M₃) :
    (f' : M₂ →ₗ[R] M₃).comp (f : M →ₗ[R] M₂) = (f.trans f' : M ≃ₗ[R] M₃) :=
  rfl

@[simp]
theorem mk_coe (h₁ h₂ f h₃ h₄) : (LinearEquiv.mk e h₁ h₂ f h₃ h₄ : M ≃ₛₗ[σ] M₂) = e :=
  ext fun _ => rfl

protected theorem map_add (a b : M) : e (a + b) = e a + e b :=
  map_add e a b

protected theorem map_zero : e 0 = 0 :=
  map_zero e

-- TODO: `simp` isn't picking up `map_smulₛₗ` for `linear_equiv`s without specifying `map_smulₛₗ f`
@[simp]
protected theorem map_smulₛₗ (c : R) (x : M) : e (c • x) = σ c • e x :=
  e.map_smul' c x

include module_N₁ module_N₂

theorem map_smul (e : N₁ ≃ₗ[R₁] N₂) (c : R₁) (x : N₁) : e (c • x) = c • e x :=
  map_smulₛₗ e c x

omit module_N₁ module_N₂

@[simp]
theorem map_sum {s : Finset ι} (u : ι → M) : e (∑ i in s, u i) = ∑ i in s, e (u i) :=
  e.toLinearMap.map_sum

@[simp]
theorem map_eq_zero_iff {x : M} : e x = 0 ↔ x = 0 :=
  e.toAddEquiv.map_eq_zero_iff

theorem map_ne_zero_iff {x : M} : e x ≠ 0 ↔ x ≠ 0 :=
  e.toAddEquiv.map_ne_zero_iff

include module_M module_S_M₂ re₁ re₂

@[simp]
theorem symm_symm (e : M ≃ₛₗ[σ] M₂) : e.symm.symm = e := by
  cases e
  rfl

omit module_M module_S_M₂ re₁ re₂

theorem symm_bijective [Module R M] [Module S M₂] [RingHomInvPair σ' σ] [RingHomInvPair σ σ'] :
    Function.Bijective (symm : (M ≃ₛₗ[σ] M₂) → M₂ ≃ₛₗ[σ'] M) :=
  Equivₓ.bijective ⟨(symm : (M ≃ₛₗ[σ] M₂) → M₂ ≃ₛₗ[σ'] M), (symm : (M₂ ≃ₛₗ[σ'] M) → M ≃ₛₗ[σ] M₂), symm_symm, symm_symm⟩

@[simp]
theorem mk_coe' (f h₁ h₂ h₃ h₄) : (LinearEquiv.mk f h₁ h₂ (⇑e) h₃ h₄ : M₂ ≃ₛₗ[σ'] M) = e.symm :=
  symm_bijective.Injective <| ext fun x => rfl

@[simp]
theorem symm_mk (f h₁ h₂ h₃ h₄) :
    (⟨e, h₁, h₂, f, h₃, h₄⟩ : M ≃ₛₗ[σ] M₂).symm =
      { (⟨e, h₁, h₂, f, h₃, h₄⟩ : M ≃ₛₗ[σ] M₂).symm with toFun := f, invFun := e } :=
  rfl

@[simp]
theorem coe_symm_mk [Module R M] [Module R M₂] {to_fun inv_fun map_add map_smul left_inv right_inv} :
    ⇑(⟨to_fun, map_add, map_smul, inv_fun, left_inv, right_inv⟩ : M ≃ₗ[R] M₂).symm = inv_fun :=
  rfl

protected theorem bijective : Function.Bijective e :=
  e.toEquiv.Bijective

protected theorem injective : Function.Injective e :=
  e.toEquiv.Injective

protected theorem surjective : Function.Surjective e :=
  e.toEquiv.Surjective

protected theorem image_eq_preimage (s : Set M) : e '' s = e.symm ⁻¹' s :=
  e.toEquiv.image_eq_preimage s

protected theorem image_symm_eq_preimage (s : Set M₂) : e.symm '' s = e ⁻¹' s :=
  e.toEquiv.symm.image_eq_preimage s

end

/-- Interpret a `ring_equiv` `f` as an `f`-semilinear equiv. -/
@[simps]
def _root_.ring_equiv.to_semilinear_equiv (f : R ≃+* S) : by
    have := RingHomInvPair.of_ring_equiv f <;>
      have := RingHomInvPair.symm (↑f : R →+* S) (f.symm : S →+* R) <;> exact R ≃ₛₗ[(↑f : R →+* S)] S :=
  { f with toFun := f, map_smul' := f.map_mul }

variable [Semiringₓ R₁] [Semiringₓ R₂] [Semiringₓ R₃]

variable [AddCommMonoidₓ M] [AddCommMonoidₓ M₁] [AddCommMonoidₓ M₂]

/-- An involutive linear map is a linear equivalence. -/
def ofInvolutive {σ σ' : R →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ] {module_M : Module R M} (f : M →ₛₗ[σ] M)
    (hf : Involutive f) : M ≃ₛₗ[σ] M :=
  { f, hf.toPerm f with }

@[simp]
theorem coe_of_involutive {σ σ' : R →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ] {module_M : Module R M}
    (f : M →ₛₗ[σ] M) (hf : Involutive f) : ⇑(ofInvolutive f hf) = f :=
  rfl

section RestrictScalars

variable (R) [Module R M] [Module R M₂] [Module S M] [Module S M₂] [LinearMap.CompatibleSmul M M₂ R S]

/-- If `M` and `M₂` are both `R`-semimodules and `S`-semimodules and `R`-semimodule structures
are defined by an action of `R` on `S` (formally, we have two scalar towers), then any `S`-linear
equivalence from `M` to `M₂` is also an `R`-linear equivalence.

See also `linear_map.restrict_scalars`. -/
@[simps]
def restrictScalars (f : M ≃ₗ[S] M₂) : M ≃ₗ[R] M₂ :=
  { f.toLinearMap.restrictScalars R with toFun := f, invFun := f.symm, left_inv := f.left_inv,
    right_inv := f.right_inv }

theorem restrict_scalars_injective : Function.Injective (restrictScalars R : (M ≃ₗ[S] M₂) → M ≃ₗ[R] M₂) := fun f g h =>
  ext (LinearEquiv.congr_fun h : _)

@[simp]
theorem restrict_scalars_inj (f g : M ≃ₗ[S] M₂) : f.restrictScalars R = g.restrictScalars R ↔ f = g :=
  (restrict_scalars_injective R).eq_iff

end RestrictScalars

section Automorphisms

variable [Module R M]

instance automorphismGroup : Groupₓ (M ≃ₗ[R] M) where
  mul := fun f g => g.trans f
  one := LinearEquiv.refl R M
  inv := fun f => f.symm
  mul_assoc := fun f g h => rfl
  mul_one := fun f => ext fun x => rfl
  one_mul := fun f => ext fun x => rfl
  mul_left_inv := fun f => ext <| f.left_inv

/-- Restriction from `R`-linear automorphisms of `M` to `R`-linear endomorphisms of `M`,
promoted to a monoid hom. -/
@[simps]
def automorphismGroup.toLinearMapMonoidHom : (M ≃ₗ[R] M) →* M →ₗ[R] M where
  toFun := coe
  map_one' := rfl
  map_mul' := fun _ _ => rfl

/-- The tautological action by `M ≃ₗ[R] M` on `M`.

This generalizes `function.End.apply_mul_action`. -/
instance applyDistribMulAction : DistribMulAction (M ≃ₗ[R] M) M where
  smul := (· <| ·)
  smul_zero := LinearEquiv.map_zero
  smul_add := LinearEquiv.map_add
  one_smul := fun _ => rfl
  mul_smul := fun _ _ _ => rfl

@[simp]
protected theorem smul_def (f : M ≃ₗ[R] M) (a : M) : f • a = f a :=
  rfl

/-- `linear_equiv.apply_distrib_mul_action` is faithful. -/
instance apply_has_faithful_smul : HasFaithfulSmul (M ≃ₗ[R] M) M :=
  ⟨fun _ _ => LinearEquiv.ext⟩

instance apply_smul_comm_class : SmulCommClass R (M ≃ₗ[R] M) M where smul_comm := fun r e m => (e.map_smul r m).symm

instance apply_smul_comm_class' : SmulCommClass (M ≃ₗ[R] M) R M where smul_comm := LinearEquiv.map_smul

end Automorphisms

end AddCommMonoidₓ

end LinearEquiv

namespace Module

/-- `g : R ≃+* S` is `R`-linear when the module structure on `S` is `module.comp_hom S g` . -/
@[simps]
def compHom.toLinearEquiv {R S : Type _} [Semiringₓ R] [Semiringₓ S] (g : R ≃+* S) :
    have := comp_hom S (↑g : R →+* S)
    R ≃ₗ[R] S :=
  { g with toFun := (g : R → S), invFun := (g.symm : S → R), map_smul' := g.map_mul }

end Module

namespace DistribMulAction

variable (R M) [Semiringₓ R] [AddCommMonoidₓ M] [Module R M]

variable [Groupₓ S] [DistribMulAction S M] [SmulCommClass S R M]

/-- Each element of the group defines a linear equivalence.

This is a stronger version of `distrib_mul_action.to_add_equiv`. -/
@[simps]
def toLinearEquiv (s : S) : M ≃ₗ[R] M :=
  { toAddEquiv M s, toLinearMap R M s with }

/-- Each element of the group defines a module automorphism.

This is a stronger version of `distrib_mul_action.to_add_aut`. -/
@[simps]
def toModuleAut : S →* M ≃ₗ[R] M where
  toFun := toLinearEquiv R M
  map_one' := LinearEquiv.ext <| one_smul _
  map_mul' := fun a b => LinearEquiv.ext <| mul_smul _ _

end DistribMulAction

namespace AddEquiv

section AddCommMonoidₓ

variable [Semiringₓ R] [AddCommMonoidₓ M] [AddCommMonoidₓ M₂] [AddCommMonoidₓ M₃]

variable [Module R M] [Module R M₂]

variable (e : M ≃+ M₂)

/-- An additive equivalence whose underlying function preserves `smul` is a linear equivalence. -/
def toLinearEquiv (h : ∀ (c : R) (x), e (c • x) = c • e x) : M ≃ₗ[R] M₂ :=
  { e with map_smul' := h }

@[simp]
theorem coe_to_linear_equiv (h : ∀ (c : R) (x), e (c • x) = c • e x) : ⇑(e.toLinearEquiv h) = e :=
  rfl

@[simp]
theorem coe_to_linear_equiv_symm (h : ∀ (c : R) (x), e (c • x) = c • e x) : ⇑(e.toLinearEquiv h).symm = e.symm :=
  rfl

/-- An additive equivalence between commutative additive monoids is a linear equivalence between
ℕ-modules -/
def toNatLinearEquiv : M ≃ₗ[ℕ] M₂ :=
  e.toLinearEquiv fun c a => by
    erw [e.to_add_monoid_hom.map_nsmul]
    rfl

@[simp]
theorem coe_to_nat_linear_equiv : ⇑e.toNatLinearEquiv = e :=
  rfl

@[simp]
theorem to_nat_linear_equiv_to_add_equiv : e.toNatLinearEquiv.toAddEquiv = e := by
  ext
  rfl

@[simp]
theorem _root_.linear_equiv.to_add_equiv_to_nat_linear_equiv (e : M ≃ₗ[ℕ] M₂) : e.toAddEquiv.toNatLinearEquiv = e :=
  FunLike.coe_injective rfl

@[simp]
theorem to_nat_linear_equiv_symm : e.toNatLinearEquiv.symm = e.symm.toNatLinearEquiv :=
  rfl

@[simp]
theorem to_nat_linear_equiv_refl : (AddEquiv.refl M).toNatLinearEquiv = LinearEquiv.refl ℕ M :=
  rfl

@[simp]
theorem to_nat_linear_equiv_trans (e₂ : M₂ ≃+ M₃) :
    e.toNatLinearEquiv.trans e₂.toNatLinearEquiv = (e.trans e₂).toNatLinearEquiv :=
  rfl

end AddCommMonoidₓ

section AddCommGroupₓ

variable [AddCommGroupₓ M] [AddCommGroupₓ M₂] [AddCommGroupₓ M₃]

variable (e : M ≃+ M₂)

/-- An additive equivalence between commutative additive groups is a linear
equivalence between ℤ-modules -/
def toIntLinearEquiv : M ≃ₗ[ℤ] M₂ :=
  e.toLinearEquiv fun c a => e.toAddMonoidHom.map_zsmul a c

@[simp]
theorem coe_to_int_linear_equiv : ⇑e.toIntLinearEquiv = e :=
  rfl

@[simp]
theorem to_int_linear_equiv_to_add_equiv : e.toIntLinearEquiv.toAddEquiv = e := by
  ext
  rfl

@[simp]
theorem _root_.linear_equiv.to_add_equiv_to_int_linear_equiv (e : M ≃ₗ[ℤ] M₂) : e.toAddEquiv.toIntLinearEquiv = e :=
  FunLike.coe_injective rfl

@[simp]
theorem to_int_linear_equiv_symm : e.toIntLinearEquiv.symm = e.symm.toIntLinearEquiv :=
  rfl

@[simp]
theorem to_int_linear_equiv_refl : (AddEquiv.refl M).toIntLinearEquiv = LinearEquiv.refl ℤ M :=
  rfl

@[simp]
theorem to_int_linear_equiv_trans (e₂ : M₂ ≃+ M₃) :
    e.toIntLinearEquiv.trans e₂.toIntLinearEquiv = (e.trans e₂).toIntLinearEquiv :=
  rfl

end AddCommGroupₓ

end AddEquiv

