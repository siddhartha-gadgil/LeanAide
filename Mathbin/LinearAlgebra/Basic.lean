/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Kevin Buzzard, Yury Kudryashov, Frédéric Dupuis,
  Heather Macbeth
-/
import Mathbin.Algebra.BigOperators.Pi
import Mathbin.Algebra.Module.Hom
import Mathbin.Algebra.Module.Prod
import Mathbin.Algebra.Module.Submodule.Lattice
import Mathbin.Data.Dfinsupp.Basic
import Mathbin.Data.Finsupp.Basic
import Mathbin.Order.CompactlyGenerated

/-!
# Linear algebra

This file defines the basics of linear algebra. It sets up the "categorical/lattice structure" of
modules over a ring, submodules, and linear maps.

Many of the relevant definitions, including `module`, `submodule`, and `linear_map`, are found in
`src/algebra/module`.

## Main definitions

* Many constructors for (semi)linear maps
* The kernel `ker` and range `range` of a linear map are submodules of the domain and codomain
  respectively.
* The general linear group is defined to be the group of invertible linear maps from `M` to itself.

See `linear_algebra.span` for the span of a set (as a submodule),
and `linear_algebra.quotient` for quotients by submodules.

## Main theorems

See `linear_algebra.isomorphisms` for Noether's three isomorphism theorems for modules.

## Notations

* We continue to use the notations `M →ₛₗ[σ] M₂` and `M →ₗ[R] M₂` for the type of semilinear
  (resp. linear) maps from `M` to `M₂` over the ring homomorphism `σ` (resp. over the ring `R`).

## Implementation notes

We note that, when constructing linear maps, it is convenient to use operations defined on bundled
maps (`linear_map.prod`, `linear_map.coprod`, arithmetic operations like `+`) instead of defining a
function and proving it is linear.

## TODO

* Parts of this file have not yet been generalized to semilinear maps

## Tags
linear algebra, vector space, module

-/


open Function

open BigOperators Pointwise

variable {R : Type _} {R₁ : Type _} {R₂ : Type _} {R₃ : Type _} {R₄ : Type _}

variable {S : Type _}

variable {K : Type _} {K₂ : Type _}

variable {M : Type _} {M' : Type _} {M₁ : Type _} {M₂ : Type _} {M₃ : Type _} {M₄ : Type _}

variable {N : Type _} {N₂ : Type _}

variable {ι : Type _}

variable {V : Type _} {V₂ : Type _}

namespace Finsupp

theorem smul_sum {α : Type _} {β : Type _} {R : Type _} {M : Type _} [Zero β] [Monoidₓ R] [AddCommMonoidₓ M]
    [DistribMulAction R M] {v : α →₀ β} {c : R} {h : α → β → M} : c • v.Sum h = v.Sum fun a b => c • h a b :=
  Finset.smul_sum

@[simp]
theorem sum_smul_index_linear_map' {α : Type _} {R : Type _} {M : Type _} {M₂ : Type _} [Semiringₓ R] [AddCommMonoidₓ M]
    [Module R M] [AddCommMonoidₓ M₂] [Module R M₂] {v : α →₀ M} {c : R} {h : α → M →ₗ[R] M₂} :
    ((c • v).Sum fun a => h a) = c • v.Sum fun a => h a := by
  rw [Finsupp.sum_smul_index', Finsupp.smul_sum]
  · simp only [← map_smul]
    
  · intro i
    exact (h i).map_zero
    

variable (α : Type _) [Fintype α]

variable (R M) [AddCommMonoidₓ M] [Semiringₓ R] [Module R M]

/-- Given `fintype α`, `linear_equiv_fun_on_fintype R` is the natural `R`-linear equivalence between
`α →₀ β` and `α → β`. -/
@[simps apply]
noncomputable def linearEquivFunOnFintype : (α →₀ M) ≃ₗ[R] α → M :=
  { equivFunOnFintype with toFun := coeFn,
    map_add' := fun f g => by
      ext
      rfl,
    map_smul' := fun c f => by
      ext
      rfl }

@[simp]
theorem linear_equiv_fun_on_fintype_single [DecidableEq α] (x : α) (m : M) :
    (linearEquivFunOnFintype R M α) (single x m) = Pi.single x m := by
  ext a
  change (equiv_fun_on_fintype (single x m)) a = _
  convert _root_.congr_fun (equiv_fun_on_fintype_single x m) a

@[simp]
theorem linear_equiv_fun_on_fintype_symm_single [DecidableEq α] (x : α) (m : M) :
    (linearEquivFunOnFintype R M α).symm (Pi.single x m) = single x m := by
  ext a
  change (equiv_fun_on_fintype.symm (Pi.single x m)) a = _
  convert congr_fun (equiv_fun_on_fintype_symm_single x m) a

@[simp]
theorem linear_equiv_fun_on_fintype_symm_coe (f : α →₀ M) : (linearEquivFunOnFintype R M α).symm f = f := by
  ext
  simp [← linear_equiv_fun_on_fintype]

end Finsupp

/-- decomposing `x : ι → R` as a sum along the canonical basis -/
theorem pi_eq_sum_univ {ι : Type _} [Fintype ι] [DecidableEq ι] {R : Type _} [Semiringₓ R] (x : ι → R) :
    x = ∑ i, x i • fun j => if i = j then 1 else 0 := by
  ext
  simp

/-! ### Properties of linear maps -/


namespace LinearMap

section AddCommMonoidₓ

variable [Semiringₓ R] [Semiringₓ R₂] [Semiringₓ R₃] [Semiringₓ R₄]

variable [AddCommMonoidₓ M] [AddCommMonoidₓ M₁] [AddCommMonoidₓ M₂]

variable [AddCommMonoidₓ M₃] [AddCommMonoidₓ M₄]

variable [Module R M] [Module R M₁] [Module R₂ M₂] [Module R₃ M₃] [Module R₄ M₄]

variable {σ₁₂ : R →+* R₂} {σ₂₃ : R₂ →+* R₃} {σ₃₄ : R₃ →+* R₄}

variable {σ₁₃ : R →+* R₃} {σ₂₄ : R₂ →+* R₄} {σ₁₄ : R →+* R₄}

variable [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [RingHomCompTriple σ₂₃ σ₃₄ σ₂₄]

variable [RingHomCompTriple σ₁₃ σ₃₄ σ₁₄] [RingHomCompTriple σ₁₂ σ₂₄ σ₁₄]

variable (f : M →ₛₗ[σ₁₂] M₂) (g : M₂ →ₛₗ[σ₂₃] M₃)

include R R₂

theorem comp_assoc (h : M₃ →ₛₗ[σ₃₄] M₄) :
    ((h.comp g : M₂ →ₛₗ[σ₂₄] M₄).comp f : M →ₛₗ[σ₁₄] M₄) = h.comp (g.comp f : M →ₛₗ[σ₁₃] M₃) :=
  rfl

omit R R₂

/-- The restriction of a linear map `f : M → M₂` to a submodule `p ⊆ M` gives a linear map
`p → M₂`. -/
def domRestrict (f : M →ₛₗ[σ₁₂] M₂) (p : Submodule R M) : p →ₛₗ[σ₁₂] M₂ :=
  f.comp p.Subtype

@[simp]
theorem dom_restrict_apply (f : M →ₛₗ[σ₁₂] M₂) (p : Submodule R M) (x : p) : f.domRestrict p x = f x :=
  rfl

/-- A linear map `f : M₂ → M` whose values lie in a submodule `p ⊆ M` can be restricted to a
linear map M₂ → p. -/
def codRestrict (p : Submodule R₂ M₂) (f : M →ₛₗ[σ₁₂] M₂) (h : ∀ c, f c ∈ p) : M →ₛₗ[σ₁₂] p := by
  refine' { toFun := fun c => ⟨f c, h c⟩.. } <;> intros <;> apply SetCoe.ext <;> simp

@[simp]
theorem cod_restrict_apply (p : Submodule R₂ M₂) (f : M →ₛₗ[σ₁₂] M₂) {h} (x : M) : (codRestrict p f h x : M₂) = f x :=
  rfl

@[simp]
theorem comp_cod_restrict (p : Submodule R₃ M₃) (h : ∀ b, g b ∈ p) :
    ((codRestrict p g h).comp f : M →ₛₗ[σ₁₃] p) = codRestrict p (g.comp f) fun b => h _ :=
  ext fun b => rfl

@[simp]
theorem subtype_comp_cod_restrict (p : Submodule R₂ M₂) (h : ∀ b, f b ∈ p) : p.Subtype.comp (codRestrict p f h) = f :=
  ext fun b => rfl

/-- Restrict domain and codomain of an endomorphism. -/
def restrict (f : M →ₗ[R] M) {p : Submodule R M} (hf : ∀, ∀ x ∈ p, ∀, f x ∈ p) : p →ₗ[R] p :=
  (f.domRestrict p).codRestrict p <| SetLike.forall.2 hf

theorem restrict_apply {f : M →ₗ[R] M} {p : Submodule R M} (hf : ∀, ∀ x ∈ p, ∀, f x ∈ p) (x : p) :
    f.restrict hf x = ⟨f x, hf x.1 x.2⟩ :=
  rfl

theorem subtype_comp_restrict {f : M →ₗ[R] M} {p : Submodule R M} (hf : ∀, ∀ x ∈ p, ∀, f x ∈ p) :
    p.Subtype.comp (f.restrict hf) = f.domRestrict p :=
  rfl

theorem restrict_eq_cod_restrict_dom_restrict {f : M →ₗ[R] M} {p : Submodule R M} (hf : ∀, ∀ x ∈ p, ∀, f x ∈ p) :
    f.restrict hf = (f.domRestrict p).codRestrict p fun x => hf x.1 x.2 :=
  rfl

theorem restrict_eq_dom_restrict_cod_restrict {f : M →ₗ[R] M} {p : Submodule R M} (hf : ∀ x, f x ∈ p) :
    (f.restrict fun x _ => hf x) = (f.codRestrict p hf).domRestrict p :=
  rfl

instance uniqueOfLeft [Subsingleton M] : Unique (M →ₛₗ[σ₁₂] M₂) :=
  { LinearMap.inhabited with
    uniq := fun f =>
      ext fun x => by
        rw [Subsingleton.elimₓ x 0, map_zero, map_zero] }

instance uniqueOfRight [Subsingleton M₂] : Unique (M →ₛₗ[σ₁₂] M₂) :=
  coe_injective.unique

/-- Evaluation of a `σ₁₂`-linear map at a fixed `a`, as an `add_monoid_hom`. -/
def evalAddMonoidHom (a : M) : (M →ₛₗ[σ₁₂] M₂) →+ M₂ where
  toFun := fun f => f a
  map_add' := fun f g => LinearMap.add_apply f g a
  map_zero' := rfl

/-- `linear_map.to_add_monoid_hom` promoted to an `add_monoid_hom` -/
def toAddMonoidHom' : (M →ₛₗ[σ₁₂] M₂) →+ M →+ M₂ where
  toFun := toAddMonoidHom
  map_zero' := by
    ext <;> rfl
  map_add' := by
    intros <;> ext <;> rfl

theorem sum_apply (t : Finset ι) (f : ι → M →ₛₗ[σ₁₂] M₂) (b : M) : (∑ d in t, f d) b = ∑ d in t, f d b :=
  AddMonoidHom.map_sum ((AddMonoidHom.eval b).comp toAddMonoidHom') f _

section SmulRight

variable [Semiringₓ S] [Module R S] [Module S M] [IsScalarTower R S M]

/-- When `f` is an `R`-linear map taking values in `S`, then `λb, f b • x` is an `R`-linear map. -/
def smulRight (f : M₁ →ₗ[R] S) (x : M) : M₁ →ₗ[R] M where
  toFun := fun b => f b • x
  map_add' := fun x y => by
    rw [f.map_add, add_smul]
  map_smul' := fun b y => by
    dsimp' <;> rw [map_smul, smul_assoc]

@[simp]
theorem coe_smul_right (f : M₁ →ₗ[R] S) (x : M) : (smulRight f x : M₁ → M) = fun c => f c • x :=
  rfl

theorem smul_right_apply (f : M₁ →ₗ[R] S) (x : M) (c : M₁) : smulRight f x c = f c • x :=
  rfl

end SmulRight

instance [Nontrivial M] : Nontrivial (Module.End R M) := by
  obtain ⟨m, ne⟩ := (nontrivial_iff_exists_ne (0 : M)).mp inferInstance
  exact nontrivial_of_ne 1 0 fun p => Ne (LinearMap.congr_fun p m)

@[simp, norm_cast]
theorem coe_fn_sum {ι : Type _} (t : Finset ι) (f : ι → M →ₛₗ[σ₁₂] M₂) : ⇑(∑ i in t, f i) = ∑ i in t, (f i : M → M₂) :=
  AddMonoidHom.map_sum ⟨@toFun R R₂ _ _ σ₁₂ M M₂ _ _ _ _, rfl, fun x y => rfl⟩ _ _

@[simp]
theorem pow_apply (f : M →ₗ[R] M) (n : ℕ) (m : M) : (f ^ n) m = (f^[n]) m := by
  induction' n with n ih
  · rfl
    
  · simp only [← Function.comp_app, ← Function.iterate_succ, ← LinearMap.mul_apply, ← pow_succₓ, ← ih]
    exact (Function.Commute.iterate_self _ _ m).symm
    

theorem pow_map_zero_of_le {f : Module.End R M} {m : M} {k l : ℕ} (hk : k ≤ l) (hm : (f ^ k) m = 0) : (f ^ l) m = 0 :=
  by
  rw [← tsub_add_cancel_of_le hk, pow_addₓ, mul_apply, hm, map_zero]

theorem commute_pow_left_of_commute {f : M →ₛₗ[σ₁₂] M₂} {g : Module.End R M} {g₂ : Module.End R₂ M₂}
    (h : g₂.comp f = f.comp g) (k : ℕ) : (g₂ ^ k).comp f = f.comp (g ^ k) := by
  induction' k with k ih
  · simpa only [← pow_zeroₓ]
    
  · rw [pow_succₓ, pow_succₓ, LinearMap.mul_eq_comp, LinearMap.comp_assoc, ih, ← LinearMap.comp_assoc, h,
      LinearMap.comp_assoc, LinearMap.mul_eq_comp]
    

theorem submodule_pow_eq_zero_of_pow_eq_zero {N : Submodule R M} {g : Module.End R N} {G : Module.End R M}
    (h : G.comp N.Subtype = N.Subtype.comp g) {k : ℕ} (hG : G ^ k = 0) : g ^ k = 0 := by
  ext m
  have hg : N.subtype.comp (g ^ k) m = 0 := by
    rw [← commute_pow_left_of_commute h, hG, zero_comp, zero_apply]
  simp only [← Submodule.subtype_apply, ← comp_app, ← Submodule.coe_eq_zero, ← coe_comp] at hg
  rw [hg, LinearMap.zero_apply]

theorem coe_pow (f : M →ₗ[R] M) (n : ℕ) : ⇑(f ^ n) = f^[n] := by
  ext m
  apply pow_apply

@[simp]
theorem id_pow (n : ℕ) : (id : M →ₗ[R] M) ^ n = id :=
  one_pow n

section

variable {f' : M →ₗ[R] M}

theorem iterate_succ (n : ℕ) : f' ^ (n + 1) = comp (f' ^ n) f' := by
  rw [pow_succ'ₓ, mul_eq_comp]

theorem iterate_surjective (h : Surjective f') : ∀ n : ℕ, Surjective ⇑(f' ^ n)
  | 0 => surjective_id
  | n + 1 => by
    rw [iterate_succ]
    exact surjective.comp (iterate_surjective n) h

theorem iterate_injective (h : Injective f') : ∀ n : ℕ, Injective ⇑(f' ^ n)
  | 0 => injective_id
  | n + 1 => by
    rw [iterate_succ]
    exact injective.comp (iterate_injective n) h

theorem iterate_bijective (h : Bijective f') : ∀ n : ℕ, Bijective ⇑(f' ^ n)
  | 0 => bijective_id
  | n + 1 => by
    rw [iterate_succ]
    exact bijective.comp (iterate_bijective n) h

theorem injective_of_iterate_injective {n : ℕ} (hn : n ≠ 0) (h : Injective ⇑(f' ^ n)) : Injective f' := by
  rw [← Nat.succ_pred_eq_of_posₓ (pos_iff_ne_zero.mpr hn), iterate_succ, coe_comp] at h
  exact injective.of_comp h

theorem surjective_of_iterate_surjective {n : ℕ} (hn : n ≠ 0) (h : Surjective ⇑(f' ^ n)) : Surjective f' := by
  rw [← Nat.succ_pred_eq_of_posₓ (pos_iff_ne_zero.mpr hn), Nat.succ_eq_add_one, add_commₓ, pow_addₓ] at h
  exact surjective.of_comp h

theorem pow_apply_mem_of_forall_mem {p : Submodule R M} (n : ℕ) (h : ∀, ∀ x ∈ p, ∀, f' x ∈ p) (x : M) (hx : x ∈ p) :
    (f' ^ n) x ∈ p := by
  induction' n with n ih generalizing x
  · simpa
    
  simpa only [← iterate_succ, ← coe_comp, ← Function.comp_app, ← restrict_apply] using ih _ (h _ hx)

theorem pow_restrict {p : Submodule R M} (n : ℕ) (h : ∀, ∀ x ∈ p, ∀, f' x ∈ p) (h' := pow_apply_mem_of_forall_mem n h) :
    f'.restrict h ^ n = (f' ^ n).restrict h' := by
  induction' n with n ih <;> ext
  · simp [← restrict_apply]
    
  · simp [← restrict_apply, ← LinearMap.iterate_succ, -LinearMap.pow_apply, ← ih]
    

end

/-- A linear map `f` applied to `x : ι → R` can be computed using the image under `f` of elements
of the canonical basis. -/
theorem pi_apply_eq_sum_univ [Fintype ι] [DecidableEq ι] (f : (ι → R) →ₗ[R] M) (x : ι → R) :
    f x = ∑ i, x i • f fun j => if i = j then 1 else 0 := by
  conv_lhs => rw [pi_eq_sum_univ x, f.map_sum]
  apply Finset.sum_congr rfl fun l hl => _
  rw [map_smul]

end AddCommMonoidₓ

section Module

variable [Semiringₓ R] [Semiringₓ S] [AddCommMonoidₓ M] [AddCommMonoidₓ M₂] [AddCommMonoidₓ M₃] [Module R M]
  [Module R M₂] [Module R M₃] [Module S M₂] [Module S M₃] [SmulCommClass R S M₂] [SmulCommClass R S M₃] (f : M →ₗ[R] M₂)

variable (S)

/-- Applying a linear map at `v : M`, seen as `S`-linear map from `M →ₗ[R] M₂` to `M₂`.

 See `linear_map.applyₗ` for a version where `S = R`. -/
@[simps]
def applyₗ' : M →+ (M →ₗ[R] M₂) →ₗ[S] M₂ where
  toFun := fun v =>
    { toFun := fun f => f v, map_add' := fun f g => f.add_apply g v, map_smul' := fun x f => f.smul_apply x v }
  map_zero' := LinearMap.ext fun f => f.map_zero
  map_add' := fun x y => LinearMap.ext fun f => f.map_add _ _

section

variable (R M)

/-- The equivalence between R-linear maps from `R` to `M`, and points of `M` itself.
This says that the forgetful functor from `R`-modules to types is representable, by `R`.

This as an `S`-linear equivalence, under the assumption that `S` acts on `M` commuting with `R`.
When `R` is commutative, we can take this to be the usual action with `S = R`.
Otherwise, `S = ℕ` shows that the equivalence is additive.
See note [bundled maps over different rings].
-/
@[simps]
def ringLmapEquivSelf [Module S M] [SmulCommClass R S M] : (R →ₗ[R] M) ≃ₗ[S] M :=
  { applyₗ' S (1 : R) with toFun := fun f => f 1, invFun := smulRight (1 : R →ₗ[R] R),
    left_inv := fun f => by
      ext
      simp ,
    right_inv := fun x => by
      simp }

end

end Module

section CommSemiringₓ

variable [CommSemiringₓ R] [AddCommMonoidₓ M] [AddCommMonoidₓ M₂] [AddCommMonoidₓ M₃]

variable [Module R M] [Module R M₂] [Module R M₃]

variable (f g : M →ₗ[R] M₂)

include R

/-- Composition by `f : M₂ → M₃` is a linear map from the space of linear maps `M → M₂`
to the space of linear maps `M₂ → M₃`. -/
def compRight (f : M₂ →ₗ[R] M₃) : (M →ₗ[R] M₂) →ₗ[R] M →ₗ[R] M₃ where
  toFun := f.comp
  map_add' := fun _ _ => LinearMap.ext fun _ => map_add f _ _
  map_smul' := fun _ _ => LinearMap.ext fun _ => map_smul f _ _

@[simp]
theorem comp_right_apply (f : M₂ →ₗ[R] M₃) (g : M →ₗ[R] M₂) : compRight f g = f.comp g :=
  rfl

/-- Applying a linear map at `v : M`, seen as a linear map from `M →ₗ[R] M₂` to `M₂`.
See also `linear_map.applyₗ'` for a version that works with two different semirings.

This is the `linear_map` version of `add_monoid_hom.eval`. -/
@[simps]
def applyₗ : M →ₗ[R] (M →ₗ[R] M₂) →ₗ[R] M₂ :=
  { applyₗ' R with toFun := fun v => { applyₗ' R v with toFun := fun f => f v },
    map_smul' := fun x y => LinearMap.ext fun f => map_smul f _ _ }

/-- Alternative version of `dom_restrict` as a linear map. -/
def domRestrict' (p : Submodule R M) : (M →ₗ[R] M₂) →ₗ[R] p →ₗ[R] M₂ where
  toFun := fun φ => φ.domRestrict p
  map_add' := by
    simp [← LinearMap.ext_iff]
  map_smul' := by
    simp [← LinearMap.ext_iff]

@[simp]
theorem dom_restrict'_apply (f : M →ₗ[R] M₂) (p : Submodule R M) (x : p) : domRestrict' p f x = f x :=
  rfl

/-- The family of linear maps `M₂ → M` parameterised by `f ∈ M₂ → R`, `x ∈ M`, is linear in `f`, `x`.
-/
def smulRightₗ : (M₂ →ₗ[R] R) →ₗ[R] M →ₗ[R] M₂ →ₗ[R] M where
  toFun := fun f =>
    { toFun := LinearMap.smulRight f,
      map_add' := fun m m' => by
        ext
        apply smul_add,
      map_smul' := fun c m => by
        ext
        apply smul_comm }
  map_add' := fun f f' => by
    ext
    apply add_smul
  map_smul' := fun c f => by
    ext
    apply mul_smul

@[simp]
theorem smul_rightₗ_apply (f : M₂ →ₗ[R] R) (x : M) (c : M₂) :
    (smulRightₗ : (M₂ →ₗ[R] R) →ₗ[R] M →ₗ[R] M₂ →ₗ[R] M) f x c = f c • x :=
  rfl

end CommSemiringₓ

end LinearMap

/-- The `R`-linear equivalence between additive morphisms `A →+ B` and `ℕ`-linear morphisms `A →ₗ[ℕ] B`.
-/
@[simps]
def addMonoidHomLequivNat {A B : Type _} (R : Type _) [Semiringₓ R] [AddCommMonoidₓ A] [AddCommMonoidₓ B] [Module R B] :
    (A →+ B) ≃ₗ[R] A →ₗ[ℕ] B where
  toFun := AddMonoidHom.toNatLinearMap
  invFun := LinearMap.toAddMonoidHom
  map_add' := by
    intros
    ext
    rfl
  map_smul' := by
    intros
    ext
    rfl
  left_inv := by
    intro f
    ext
    rfl
  right_inv := by
    intro f
    ext
    rfl

/-- The `R`-linear equivalence between additive morphisms `A →+ B` and `ℤ`-linear morphisms `A →ₗ[ℤ] B`.
-/
@[simps]
def addMonoidHomLequivInt {A B : Type _} (R : Type _) [Semiringₓ R] [AddCommGroupₓ A] [AddCommGroupₓ B] [Module R B] :
    (A →+ B) ≃ₗ[R] A →ₗ[ℤ] B where
  toFun := AddMonoidHom.toIntLinearMap
  invFun := LinearMap.toAddMonoidHom
  map_add' := by
    intros
    ext
    rfl
  map_smul' := by
    intros
    ext
    rfl
  left_inv := by
    intro f
    ext
    rfl
  right_inv := by
    intro f
    ext
    rfl

/-! ### Properties of submodules -/


namespace Submodule

section AddCommMonoidₓ

variable [Semiringₓ R] [Semiringₓ R₂] [Semiringₓ R₃]

variable [AddCommMonoidₓ M] [AddCommMonoidₓ M₂] [AddCommMonoidₓ M₃] [AddCommMonoidₓ M']

variable [Module R M] [Module R M'] [Module R₂ M₂] [Module R₃ M₃]

variable {σ₁₂ : R →+* R₂} {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R →+* R₃}

variable {σ₂₁ : R₂ →+* R}

variable [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]

variable [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]

variable (p p' : Submodule R M) (q q' : Submodule R₂ M₂)

variable (q₁ q₁' : Submodule R M')

variable {r : R} {x y : M}

open Set

variable {p p'}

/-- If two submodules `p` and `p'` satisfy `p ⊆ p'`, then `of_le p p'` is the linear map version of
this inclusion. -/
def ofLe (h : p ≤ p') : p →ₗ[R] p' :=
  (p.Subtype.codRestrict p') fun ⟨x, hx⟩ => h hx

@[simp]
theorem coe_of_le (h : p ≤ p') (x : p) : (ofLe h x : M) = x :=
  rfl

theorem of_le_apply (h : p ≤ p') (x : p) : ofLe h x = ⟨x, h x.2⟩ :=
  rfl

theorem of_le_injective (h : p ≤ p') : Function.Injective (ofLe h) := fun x y h =>
  Subtype.val_injective (Subtype.mk.injₓ h)

variable (p p')

theorem subtype_comp_of_le (p q : Submodule R M) (h : p ≤ q) : q.Subtype.comp (ofLe h) = p.Subtype := by
  ext ⟨b, hb⟩
  rfl

variable (R)

@[simp]
theorem subsingleton_iff : Subsingleton (Submodule R M) ↔ Subsingleton M :=
  have h : Subsingleton (Submodule R M) ↔ Subsingleton (AddSubmonoid M) := by
    rw [← subsingleton_iff_bot_eq_top, ← subsingleton_iff_bot_eq_top]
    convert to_add_submonoid_eq.symm <;> rfl
  h.trans AddSubmonoid.subsingleton_iff

@[simp]
theorem nontrivial_iff : Nontrivial (Submodule R M) ↔ Nontrivial M :=
  not_iff_not.mp
    ((not_nontrivial_iff_subsingleton.trans <| subsingleton_iff R).trans not_nontrivial_iff_subsingleton.symm)

variable {R}

instance [Subsingleton M] : Unique (Submodule R M) :=
  ⟨⟨⊥⟩, fun a => @Subsingleton.elimₓ _ ((subsingleton_iff R).mpr ‹_›) a _⟩

instance unique' [Subsingleton R] : Unique (Submodule R M) := by
  have := Module.subsingleton R M <;> infer_instance

instance [Nontrivial M] : Nontrivial (Submodule R M) :=
  (nontrivial_iff R).mpr ‹_›

theorem mem_right_iff_eq_zero_of_disjoint {p p' : Submodule R M} (h : Disjoint p p') {x : p} : (x : M) ∈ p' ↔ x = 0 :=
  ⟨fun hx => coe_eq_zero.1 <| disjoint_def.1 h x x.2 hx, fun h => h.symm ▸ p'.zero_mem⟩

theorem mem_left_iff_eq_zero_of_disjoint {p p' : Submodule R M} (h : Disjoint p p') {x : p'} : (x : M) ∈ p ↔ x = 0 :=
  ⟨fun hx => coe_eq_zero.1 <| disjoint_def.1 h x hx x.2, fun h => h.symm ▸ p.zero_mem⟩

section

variable [RingHomSurjective σ₁₂]

/-- The pushforward of a submodule `p ⊆ M` by `f : M → M₂` -/
def map (f : M →ₛₗ[σ₁₂] M₂) (p : Submodule R M) : Submodule R₂ M₂ :=
  { p.toAddSubmonoid.map f.toAddMonoidHom with Carrier := f '' p,
    smul_mem' := by
      rintro c x ⟨y, hy, rfl⟩
      obtain ⟨a, rfl⟩ := σ₁₂.is_surjective c
      exact ⟨_, p.smul_mem a hy, map_smulₛₗ f _ _⟩ }

@[simp]
theorem map_coe (f : M →ₛₗ[σ₁₂] M₂) (p : Submodule R M) : (map f p : Set M₂) = f '' p :=
  rfl

theorem map_to_add_submonoid (f : M →ₛₗ[σ₁₂] M₂) (p : Submodule R M) :
    (p.map f).toAddSubmonoid = p.toAddSubmonoid.map (f : M →+ M₂) :=
  SetLike.coe_injective rfl

theorem map_to_add_submonoid' (f : M →ₛₗ[σ₁₂] M₂) (p : Submodule R M) :
    (p.map f).toAddSubmonoid = p.toAddSubmonoid.map f :=
  SetLike.coe_injective rfl

@[simp]
theorem mem_map {f : M →ₛₗ[σ₁₂] M₂} {p : Submodule R M} {x : M₂} : x ∈ map f p ↔ ∃ y, y ∈ p ∧ f y = x :=
  Iff.rfl

theorem mem_map_of_mem {f : M →ₛₗ[σ₁₂] M₂} {p : Submodule R M} {r} (h : r ∈ p) : f r ∈ map f p :=
  Set.mem_image_of_mem _ h

theorem apply_coe_mem_map (f : M →ₛₗ[σ₁₂] M₂) {p : Submodule R M} (r : p) : f r ∈ map f p :=
  mem_map_of_mem r.Prop

@[simp]
theorem map_id : map (LinearMap.id : M →ₗ[R] M) p = p :=
  Submodule.ext fun a => by
    simp

theorem map_comp [RingHomSurjective σ₂₃] [RingHomSurjective σ₁₃] (f : M →ₛₗ[σ₁₂] M₂) (g : M₂ →ₛₗ[σ₂₃] M₃)
    (p : Submodule R M) : map (g.comp f : M →ₛₗ[σ₁₃] M₃) p = map g (map f p) :=
  SetLike.coe_injective <| by
    simp [← map_coe] <;> rw [← image_comp]

theorem map_mono {f : M →ₛₗ[σ₁₂] M₂} {p p' : Submodule R M} : p ≤ p' → map f p ≤ map f p' :=
  image_subset _

@[simp]
theorem map_zero : map (0 : M →ₛₗ[σ₁₂] M₂) p = ⊥ :=
  have : ∃ x : M, x ∈ p := ⟨0, p.zero_mem⟩
  ext <| by
    simp [← this, ← eq_comm]

theorem map_add_le (f g : M →ₛₗ[σ₁₂] M₂) : map (f + g) p ≤ map f p⊔map g p := by
  rintro x ⟨m, hm, rfl⟩
  exact add_mem_sup (mem_map_of_mem hm) (mem_map_of_mem hm)

theorem range_map_nonempty (N : Submodule R M) :
    (Set.Range (fun ϕ => Submodule.map ϕ N : (M →ₛₗ[σ₁₂] M₂) → Submodule R₂ M₂)).Nonempty :=
  ⟨_, Set.mem_range.mpr ⟨0, rfl⟩⟩

end

include σ₂₁

/-- The pushforward of a submodule by an injective linear map is
linearly equivalent to the original submodule. See also `linear_equiv.submodule_map` for a
computable version when `f` has an explicit inverse. -/
noncomputable def equivMapOfInjective (f : M →ₛₗ[σ₁₂] M₂) (i : Injective f) (p : Submodule R M) : p ≃ₛₗ[σ₁₂] p.map f :=
  { Equivₓ.Set.image f p i with
    map_add' := by
      intros
      simp
      rfl,
    map_smul' := by
      intros
      simp
      rfl }

@[simp]
theorem coe_equiv_map_of_injective_apply (f : M →ₛₗ[σ₁₂] M₂) (i : Injective f) (p : Submodule R M) (x : p) :
    (equivMapOfInjective f i p x : M₂) = f x :=
  rfl

omit σ₂₁

/-- The pullback of a submodule `p ⊆ M₂` along `f : M → M₂` -/
def comap (f : M →ₛₗ[σ₁₂] M₂) (p : Submodule R₂ M₂) : Submodule R M :=
  { p.toAddSubmonoid.comap f.toAddMonoidHom with Carrier := f ⁻¹' p,
    smul_mem' := fun a x h => by
      simp [← p.smul_mem _ h] }

@[simp]
theorem comap_coe (f : M →ₛₗ[σ₁₂] M₂) (p : Submodule R₂ M₂) : (comap f p : Set M) = f ⁻¹' p :=
  rfl

@[simp]
theorem mem_comap {f : M →ₛₗ[σ₁₂] M₂} {p : Submodule R₂ M₂} : x ∈ comap f p ↔ f x ∈ p :=
  Iff.rfl

@[simp]
theorem comap_id : comap LinearMap.id p = p :=
  SetLike.coe_injective rfl

theorem comap_comp (f : M →ₛₗ[σ₁₂] M₂) (g : M₂ →ₛₗ[σ₂₃] M₃) (p : Submodule R₃ M₃) :
    comap (g.comp f : M →ₛₗ[σ₁₃] M₃) p = comap f (comap g p) :=
  rfl

theorem comap_mono {f : M →ₛₗ[σ₁₂] M₂} {q q' : Submodule R₂ M₂} : q ≤ q' → comap f q ≤ comap f q' :=
  preimage_mono

theorem le_comap_pow_of_le_comap (p : Submodule R M) {f : M →ₗ[R] M} (h : p ≤ p.comap f) (k : ℕ) :
    p ≤ p.comap (f ^ k) := by
  induction' k with k ih
  · simp [← LinearMap.one_eq_id]
    
  · simp [← LinearMap.iterate_succ, ← comap_comp, ← h.trans (comap_mono ih)]
    

section

variable [RingHomSurjective σ₁₂]

theorem map_le_iff_le_comap {f : M →ₛₗ[σ₁₂] M₂} {p : Submodule R M} {q : Submodule R₂ M₂} :
    map f p ≤ q ↔ p ≤ comap f q :=
  image_subset_iff

theorem gc_map_comap (f : M →ₛₗ[σ₁₂] M₂) : GaloisConnection (map f) (comap f)
  | p, q => map_le_iff_le_comap

@[simp]
theorem map_bot (f : M →ₛₗ[σ₁₂] M₂) : map f ⊥ = ⊥ :=
  (gc_map_comap f).l_bot

@[simp]
theorem map_sup (f : M →ₛₗ[σ₁₂] M₂) : map f (p⊔p') = map f p⊔map f p' :=
  (gc_map_comap f).l_sup

@[simp]
theorem map_supr {ι : Sort _} (f : M →ₛₗ[σ₁₂] M₂) (p : ι → Submodule R M) : map f (⨆ i, p i) = ⨆ i, map f (p i) :=
  (gc_map_comap f).l_supr

end

@[simp]
theorem comap_top (f : M →ₛₗ[σ₁₂] M₂) : comap f ⊤ = ⊤ :=
  rfl

@[simp]
theorem comap_inf (f : M →ₛₗ[σ₁₂] M₂) : comap f (q⊓q') = comap f q⊓comap f q' :=
  rfl

@[simp]
theorem comap_infi [RingHomSurjective σ₁₂] {ι : Sort _} (f : M →ₛₗ[σ₁₂] M₂) (p : ι → Submodule R₂ M₂) :
    comap f (⨅ i, p i) = ⨅ i, comap f (p i) :=
  (gc_map_comap f).u_infi

@[simp]
theorem comap_zero : comap (0 : M →ₛₗ[σ₁₂] M₂) q = ⊤ :=
  ext <| by
    simp

theorem map_comap_le [RingHomSurjective σ₁₂] (f : M →ₛₗ[σ₁₂] M₂) (q : Submodule R₂ M₂) : map f (comap f q) ≤ q :=
  (gc_map_comap f).l_u_le _

theorem le_comap_map [RingHomSurjective σ₁₂] (f : M →ₛₗ[σ₁₂] M₂) (p : Submodule R M) : p ≤ comap f (map f p) :=
  (gc_map_comap f).le_u_l _

section GaloisInsertion

variable {f : M →ₛₗ[σ₁₂] M₂} (hf : Surjective f)

variable [RingHomSurjective σ₁₂]

include hf

/-- `map f` and `comap f` form a `galois_insertion` when `f` is surjective. -/
def giMapComap : GaloisInsertion (map f) (comap f) :=
  (gc_map_comap f).toGaloisInsertion fun S x hx => by
    rcases hf x with ⟨y, rfl⟩
    simp only [← mem_map, ← mem_comap]
    exact ⟨y, hx, rfl⟩

theorem map_comap_eq_of_surjective (p : Submodule R₂ M₂) : (p.comap f).map f = p :=
  (giMapComap hf).l_u_eq _

theorem map_surjective_of_surjective : Function.Surjective (map f) :=
  (giMapComap hf).l_surjective

theorem comap_injective_of_surjective : Function.Injective (comap f) :=
  (giMapComap hf).u_injective

theorem map_sup_comap_of_surjective (p q : Submodule R₂ M₂) : (p.comap f⊔q.comap f).map f = p⊔q :=
  (giMapComap hf).l_sup_u _ _

theorem map_supr_comap_of_sujective {ι : Sort _} (S : ι → Submodule R₂ M₂) : (⨆ i, (S i).comap f).map f = supr S :=
  (giMapComap hf).l_supr_u _

theorem map_inf_comap_of_surjective (p q : Submodule R₂ M₂) : (p.comap f⊓q.comap f).map f = p⊓q :=
  (giMapComap hf).l_inf_u _ _

theorem map_infi_comap_of_surjective {ι : Sort _} (S : ι → Submodule R₂ M₂) : (⨅ i, (S i).comap f).map f = infi S :=
  (giMapComap hf).l_infi_u _

theorem comap_le_comap_iff_of_surjective (p q : Submodule R₂ M₂) : p.comap f ≤ q.comap f ↔ p ≤ q :=
  (giMapComap hf).u_le_u_iff

theorem comap_strict_mono_of_surjective : StrictMono (comap f) :=
  (giMapComap hf).strict_mono_u

end GaloisInsertion

section GaloisCoinsertion

variable [RingHomSurjective σ₁₂] {f : M →ₛₗ[σ₁₂] M₂} (hf : Injective f)

include hf

/-- `map f` and `comap f` form a `galois_coinsertion` when `f` is injective. -/
def gciMapComap : GaloisCoinsertion (map f) (comap f) :=
  (gc_map_comap f).toGaloisCoinsertion fun S x => by
    simp [← mem_comap, ← mem_map, ← hf.eq_iff]

theorem comap_map_eq_of_injective (p : Submodule R M) : (p.map f).comap f = p :=
  (gciMapComap hf).u_l_eq _

theorem comap_surjective_of_injective : Function.Surjective (comap f) :=
  (gciMapComap hf).u_surjective

theorem map_injective_of_injective : Function.Injective (map f) :=
  (gciMapComap hf).l_injective

theorem comap_inf_map_of_injective (p q : Submodule R M) : (p.map f⊓q.map f).comap f = p⊓q :=
  (gciMapComap hf).u_inf_l _ _

theorem comap_infi_map_of_injective {ι : Sort _} (S : ι → Submodule R M) : (⨅ i, (S i).map f).comap f = infi S :=
  (gciMapComap hf).u_infi_l _

theorem comap_sup_map_of_injective (p q : Submodule R M) : (p.map f⊔q.map f).comap f = p⊔q :=
  (gciMapComap hf).u_sup_l _ _

theorem comap_supr_map_of_injective {ι : Sort _} (S : ι → Submodule R M) : (⨆ i, (S i).map f).comap f = supr S :=
  (gciMapComap hf).u_supr_l _

theorem map_le_map_iff_of_injective (p q : Submodule R M) : p.map f ≤ q.map f ↔ p ≤ q :=
  (gciMapComap hf).l_le_l_iff

theorem map_strict_mono_of_injective : StrictMono (map f) :=
  (gciMapComap hf).strict_mono_l

end GaloisCoinsertion

--TODO(Mario): is there a way to prove this from order properties?
theorem map_inf_eq_map_inf_comap [RingHomSurjective σ₁₂] {f : M →ₛₗ[σ₁₂] M₂} {p : Submodule R M}
    {p' : Submodule R₂ M₂} : map f p⊓p' = map f (p⊓comap f p') :=
  le_antisymmₓ
    (by
      rintro _ ⟨⟨x, h₁, rfl⟩, h₂⟩ <;> exact ⟨_, ⟨h₁, h₂⟩, rfl⟩)
    (le_inf (map_mono inf_le_left) (map_le_iff_le_comap.2 inf_le_right))

theorem map_comap_subtype : map p.Subtype (comap p.Subtype p') = p⊓p' :=
  ext fun x =>
    ⟨by
      rintro ⟨⟨_, h₁⟩, h₂, rfl⟩ <;> exact ⟨h₁, h₂⟩, fun ⟨h₁, h₂⟩ => ⟨⟨_, h₁⟩, h₂, rfl⟩⟩

theorem eq_zero_of_bot_submodule : ∀ b : (⊥ : Submodule R M), b = 0
  | ⟨b', hb⟩ => Subtype.eq <| show b' = 0 from (mem_bot R).1 hb

/-- The infimum of a family of invariant submodule of an endomorphism is also an invariant
submodule. -/
theorem _root_.linear_map.infi_invariant {σ : R →+* R} [RingHomSurjective σ] {ι : Sort _} (f : M →ₛₗ[σ] M)
    {p : ι → Submodule R M} (hf : ∀ i, ∀, ∀ v ∈ p i, ∀, f v ∈ p i) : ∀, ∀ v ∈ infi p, ∀, f v ∈ infi p := by
  have : ∀ i, (p i).map f ≤ p i := by
    rintro i - ⟨v, hv, rfl⟩
    exact hf i v hv
  suffices (infi p).map f ≤ infi p by
    exact fun v hv => this ⟨v, hv, rfl⟩
  exact le_infi fun i => (Submodule.map_mono (infi_le p i)).trans (this i)

end AddCommMonoidₓ

section AddCommGroupₓ

variable [Ringₓ R] [AddCommGroupₓ M] [Module R M] (p : Submodule R M)

variable [AddCommGroupₓ M₂] [Module R M₂]

@[simp]
theorem neg_coe : -(p : Set M) = p :=
  Set.ext fun x => p.neg_mem_iff

@[simp]
protected theorem map_neg (f : M →ₗ[R] M₂) : map (-f) p = map f p :=
  ext fun y =>
    ⟨fun ⟨x, hx, hy⟩ => hy ▸ ⟨-x, show -x ∈ p from neg_mem hx, map_neg f x⟩, fun ⟨x, hx, hy⟩ =>
      hy ▸ ⟨-x, show -x ∈ p from neg_mem hx, (map_neg (-f) _).trans (neg_negₓ (f x))⟩⟩

end AddCommGroupₓ

end Submodule

namespace Submodule

variable [Field K]

variable [AddCommGroupₓ V] [Module K V]

variable [AddCommGroupₓ V₂] [Module K V₂]

theorem comap_smul (f : V →ₗ[K] V₂) (p : Submodule K V₂) (a : K) (h : a ≠ 0) : p.comap (a • f) = p.comap f := by
  ext b <;> simp only [← Submodule.mem_comap, ← p.smul_mem_iff h, ← LinearMap.smul_apply]

theorem map_smul (f : V →ₗ[K] V₂) (p : Submodule K V) (a : K) (h : a ≠ 0) : p.map (a • f) = p.map f :=
  le_antisymmₓ
    (by
      rw [map_le_iff_le_comap, comap_smul f _ a h, ← map_le_iff_le_comap]
      exact le_rfl)
    (by
      rw [map_le_iff_le_comap, ← comap_smul f _ a h, ← map_le_iff_le_comap]
      exact le_rfl)

theorem comap_smul' (f : V →ₗ[K] V₂) (p : Submodule K V₂) (a : K) : p.comap (a • f) = ⨅ h : a ≠ 0, p.comap f := by
  classical <;> by_cases' a = 0 <;> simp [← h, ← comap_smul]

theorem map_smul' (f : V →ₗ[K] V₂) (p : Submodule K V) (a : K) : p.map (a • f) = ⨆ h : a ≠ 0, p.map f := by
  classical <;> by_cases' a = 0 <;> simp [← h, ← map_smul]

end Submodule

/-! ### Properties of linear maps -/


namespace LinearMap

section AddCommMonoidₓ

variable [Semiringₓ R] [Semiringₓ R₂] [Semiringₓ R₃]

variable [AddCommMonoidₓ M] [AddCommMonoidₓ M₂] [AddCommMonoidₓ M₃]

variable {σ₁₂ : R →+* R₂} {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R →+* R₃}

variable [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]

variable [Module R M] [Module R₂ M₂] [Module R₃ M₃]

include R

open Submodule

section Finsupp

variable {γ : Type _} [Zero γ]

@[simp]
theorem map_finsupp_sum (f : M →ₛₗ[σ₁₂] M₂) {t : ι →₀ γ} {g : ι → γ → M} : f (t.Sum g) = t.Sum fun i d => f (g i d) :=
  f.map_sum

theorem coe_finsupp_sum (t : ι →₀ γ) (g : ι → γ → M →ₛₗ[σ₁₂] M₂) : ⇑(t.Sum g) = t.Sum fun i d => g i d :=
  coe_fn_sum _ _

@[simp]
theorem finsupp_sum_apply (t : ι →₀ γ) (g : ι → γ → M →ₛₗ[σ₁₂] M₂) (b : M) : (t.Sum g) b = t.Sum fun i d => g i d b :=
  sum_apply _ _ _

end Finsupp

section Dfinsupp

open Dfinsupp

variable {γ : ι → Type _} [DecidableEq ι]

section Sum

variable [∀ i, Zero (γ i)] [∀ (i) (x : γ i), Decidable (x ≠ 0)]

@[simp]
theorem map_dfinsupp_sum (f : M →ₛₗ[σ₁₂] M₂) {t : Π₀ i, γ i} {g : ∀ i, γ i → M} :
    f (t.Sum g) = t.Sum fun i d => f (g i d) :=
  f.map_sum

theorem coe_dfinsupp_sum (t : Π₀ i, γ i) (g : ∀ i, γ i → M →ₛₗ[σ₁₂] M₂) : ⇑(t.Sum g) = t.Sum fun i d => g i d :=
  coe_fn_sum _ _

@[simp]
theorem dfinsupp_sum_apply (t : Π₀ i, γ i) (g : ∀ i, γ i → M →ₛₗ[σ₁₂] M₂) (b : M) :
    (t.Sum g) b = t.Sum fun i d => g i d b :=
  sum_apply _ _ _

end Sum

section SumAddHom

variable [∀ i, AddZeroClassₓ (γ i)]

@[simp]
theorem map_dfinsupp_sum_add_hom (f : M →ₛₗ[σ₁₂] M₂) {t : Π₀ i, γ i} {g : ∀ i, γ i →+ M} :
    f (sumAddHom g t) = sumAddHom (fun i => f.toAddMonoidHom.comp (g i)) t :=
  f.toAddMonoidHom.map_dfinsupp_sum_add_hom _ _

end SumAddHom

end Dfinsupp

variable {σ₂₁ : R₂ →+* R} {τ₁₂ : R →+* R₂} {τ₂₃ : R₂ →+* R₃} {τ₁₃ : R →+* R₃}

variable [RingHomCompTriple τ₁₂ τ₂₃ τ₁₃]

theorem map_cod_restrict [RingHomSurjective σ₂₁] (p : Submodule R M) (f : M₂ →ₛₗ[σ₂₁] M) (h p') :
    Submodule.map (codRestrict p f h) p' = comap p.Subtype (p'.map f) :=
  Submodule.ext fun ⟨x, hx⟩ => by
    simp [← Subtype.ext_iff_val]

theorem comap_cod_restrict (p : Submodule R M) (f : M₂ →ₛₗ[σ₂₁] M) (hf p') :
    Submodule.comap (codRestrict p f hf) p' = Submodule.comap f (map p.Subtype p') :=
  Submodule.ext fun x =>
    ⟨fun h => ⟨⟨_, hf x⟩, h, rfl⟩, by
      rintro ⟨⟨_, _⟩, h, ⟨⟩⟩ <;> exact h⟩

section

/-- The range of a linear map `f : M → M₂` is a submodule of `M₂`.
See Note [range copy pattern]. -/
def range [RingHomSurjective τ₁₂] (f : M →ₛₗ[τ₁₂] M₂) : Submodule R₂ M₂ :=
  (map f ⊤).copy (Set.Range f) Set.image_univ.symm

theorem range_coe [RingHomSurjective τ₁₂] (f : M →ₛₗ[τ₁₂] M₂) : (range f : Set M₂) = Set.Range f :=
  rfl

theorem range_to_add_submonoid [RingHomSurjective τ₁₂] (f : M →ₛₗ[τ₁₂] M₂) :
    f.range.toAddSubmonoid = f.toAddMonoidHom.mrange :=
  rfl

@[simp]
theorem mem_range [RingHomSurjective τ₁₂] {f : M →ₛₗ[τ₁₂] M₂} {x} : x ∈ range f ↔ ∃ y, f y = x :=
  Iff.rfl

theorem range_eq_map [RingHomSurjective τ₁₂] (f : M →ₛₗ[τ₁₂] M₂) : f.range = map f ⊤ := by
  ext
  simp

theorem mem_range_self [RingHomSurjective τ₁₂] (f : M →ₛₗ[τ₁₂] M₂) (x : M) : f x ∈ f.range :=
  ⟨x, rfl⟩

@[simp]
theorem range_id : range (LinearMap.id : M →ₗ[R] M) = ⊤ :=
  SetLike.coe_injective Set.range_id

theorem range_comp [RingHomSurjective τ₁₂] [RingHomSurjective τ₂₃] [RingHomSurjective τ₁₃] (f : M →ₛₗ[τ₁₂] M₂)
    (g : M₂ →ₛₗ[τ₂₃] M₃) : range (g.comp f : M →ₛₗ[τ₁₃] M₃) = map g (range f) :=
  SetLike.coe_injective (Set.range_comp g f)

theorem range_comp_le_range [RingHomSurjective τ₂₃] [RingHomSurjective τ₁₃] (f : M →ₛₗ[τ₁₂] M₂) (g : M₂ →ₛₗ[τ₂₃] M₃) :
    range (g.comp f : M →ₛₗ[τ₁₃] M₃) ≤ range g :=
  SetLike.coe_mono (Set.range_comp_subset_range f g)

theorem range_eq_top [RingHomSurjective τ₁₂] {f : M →ₛₗ[τ₁₂] M₂} : range f = ⊤ ↔ Surjective f := by
  rw [SetLike.ext'_iff, range_coe, top_coe, Set.range_iff_surjective]

theorem range_le_iff_comap [RingHomSurjective τ₁₂] {f : M →ₛₗ[τ₁₂] M₂} {p : Submodule R₂ M₂} :
    range f ≤ p ↔ comap f p = ⊤ := by
  rw [range_eq_map, map_le_iff_le_comap, eq_top_iff]

theorem map_le_range [RingHomSurjective τ₁₂] {f : M →ₛₗ[τ₁₂] M₂} {p : Submodule R M} : map f p ≤ range f :=
  SetLike.coe_mono (Set.image_subset_range f p)

@[simp]
theorem range_neg {R : Type _} {R₂ : Type _} {M : Type _} {M₂ : Type _} [Semiringₓ R] [Ringₓ R₂] [AddCommMonoidₓ M]
    [AddCommGroupₓ M₂] [Module R M] [Module R₂ M₂] {τ₁₂ : R →+* R₂} [RingHomSurjective τ₁₂] (f : M →ₛₗ[τ₁₂] M₂) :
    (-f).range = f.range := by
  change ((-LinearMap.id : M₂ →ₗ[R₂] M₂).comp f).range = _
  rw [range_comp, Submodule.map_neg, Submodule.map_id]

end

/-- The decreasing sequence of submodules consisting of the ranges of the iterates of a linear map.
-/
@[simps]
def iterateRange (f : M →ₗ[R] M) : ℕ →o (Submodule R M)ᵒᵈ :=
  ⟨fun n => (f ^ n).range, fun n m w x h => by
    obtain ⟨c, rfl⟩ := le_iff_exists_add.mp w
    rw [LinearMap.mem_range] at h
    obtain ⟨m, rfl⟩ := h
    rw [LinearMap.mem_range]
    use (f ^ c) m
    rw [pow_addₓ, LinearMap.mul_apply]⟩

/-- Restrict the codomain of a linear map `f` to `f.range`.

This is the bundled version of `set.range_factorization`. -/
@[reducible]
def rangeRestrict [RingHomSurjective τ₁₂] (f : M →ₛₗ[τ₁₂] M₂) : M →ₛₗ[τ₁₂] f.range :=
  f.codRestrict f.range f.mem_range_self

/-- The range of a linear map is finite if the domain is finite.
Note: this instance can form a diamond with `subtype.fintype` in the
  presence of `fintype M₂`. -/
instance fintypeRange [Fintype M] [DecidableEq M₂] [RingHomSurjective τ₁₂] (f : M →ₛₗ[τ₁₂] M₂) : Fintype (range f) :=
  Set.fintypeRange f

/-- The kernel of a linear map `f : M → M₂` is defined to be `comap f ⊥`. This is equivalent to the
set of `x : M` such that `f x = 0`. The kernel is a submodule of `M`. -/
def ker (f : M →ₛₗ[τ₁₂] M₂) : Submodule R M :=
  comap f ⊥

@[simp]
theorem mem_ker {f : M →ₛₗ[τ₁₂] M₂} {y} : y ∈ ker f ↔ f y = 0 :=
  mem_bot R₂

@[simp]
theorem ker_id : ker (LinearMap.id : M →ₗ[R] M) = ⊥ :=
  rfl

@[simp]
theorem map_coe_ker (f : M →ₛₗ[τ₁₂] M₂) (x : ker f) : f x = 0 :=
  mem_ker.1 x.2

theorem ker_to_add_submonoid (f : M →ₛₗ[τ₁₂] M₂) : f.ker.toAddSubmonoid = f.toAddMonoidHom.mker :=
  rfl

theorem comp_ker_subtype (f : M →ₛₗ[τ₁₂] M₂) : f.comp f.ker.Subtype = 0 :=
  LinearMap.ext fun x =>
    suffices f x = 0 by
      simp [← this]
    mem_ker.1 x.2

theorem ker_comp (f : M →ₛₗ[τ₁₂] M₂) (g : M₂ →ₛₗ[τ₂₃] M₃) : ker (g.comp f : M →ₛₗ[τ₁₃] M₃) = comap f (ker g) :=
  rfl

theorem ker_le_ker_comp (f : M →ₛₗ[τ₁₂] M₂) (g : M₂ →ₛₗ[τ₂₃] M₃) : ker f ≤ ker (g.comp f : M →ₛₗ[τ₁₃] M₃) := by
  rw [ker_comp] <;> exact comap_mono bot_le

theorem disjoint_ker {f : M →ₛₗ[τ₁₂] M₂} {p : Submodule R M} : Disjoint p (ker f) ↔ ∀, ∀ x ∈ p, ∀, f x = 0 → x = 0 := by
  simp [← disjoint_def]

theorem ker_eq_bot' {f : M →ₛₗ[τ₁₂] M₂} : ker f = ⊥ ↔ ∀ m, f m = 0 → m = 0 := by
  simpa [← Disjoint] using @disjoint_ker _ _ _ _ _ _ _ _ _ _ _ f ⊤

theorem ker_eq_bot_of_inverse {τ₂₁ : R₂ →+* R} [RingHomInvPair τ₁₂ τ₂₁] {f : M →ₛₗ[τ₁₂] M₂} {g : M₂ →ₛₗ[τ₂₁] M}
    (h : (g.comp f : M →ₗ[R] M) = id) : ker f = ⊥ :=
  ker_eq_bot'.2 fun m hm => by
    rw [← id_apply m, ← h, comp_apply, hm, g.map_zero]

theorem le_ker_iff_map [RingHomSurjective τ₁₂] {f : M →ₛₗ[τ₁₂] M₂} {p : Submodule R M} : p ≤ ker f ↔ map f p = ⊥ := by
  rw [ker, eq_bot_iff, map_le_iff_le_comap]

theorem ker_cod_restrict {τ₂₁ : R₂ →+* R} (p : Submodule R M) (f : M₂ →ₛₗ[τ₂₁] M) (hf) :
    ker (codRestrict p f hf) = ker f := by
  rw [ker, comap_cod_restrict, map_bot] <;> rfl

theorem range_cod_restrict {τ₂₁ : R₂ →+* R} [RingHomSurjective τ₂₁] (p : Submodule R M) (f : M₂ →ₛₗ[τ₂₁] M) (hf) :
    range (codRestrict p f hf) = comap p.Subtype f.range := by
  simpa only [← range_eq_map] using map_cod_restrict _ _ _ _

theorem ker_restrict {p : Submodule R M} {f : M →ₗ[R] M} (hf : ∀ x : M, x ∈ p → f x ∈ p) :
    ker (f.restrict hf) = (f.domRestrict p).ker := by
  rw [restrict_eq_cod_restrict_dom_restrict, ker_cod_restrict]

theorem _root_.submodule.map_comap_eq [RingHomSurjective τ₁₂] (f : M →ₛₗ[τ₁₂] M₂) (q : Submodule R₂ M₂) :
    map f (comap f q) = range f⊓q :=
  le_antisymmₓ (le_inf map_le_range (map_comap_le _ _)) <| by
    rintro _ ⟨⟨x, _, rfl⟩, hx⟩ <;> exact ⟨x, hx, rfl⟩

theorem _root_.submodule.map_comap_eq_self [RingHomSurjective τ₁₂] {f : M →ₛₗ[τ₁₂] M₂} {q : Submodule R₂ M₂}
    (h : q ≤ range f) : map f (comap f q) = q := by
  rwa [Submodule.map_comap_eq, inf_eq_right]

@[simp]
theorem ker_zero : ker (0 : M →ₛₗ[τ₁₂] M₂) = ⊤ :=
  eq_top_iff'.2 fun x => by
    simp

@[simp]
theorem range_zero [RingHomSurjective τ₁₂] : range (0 : M →ₛₗ[τ₁₂] M₂) = ⊥ := by
  simpa only [← range_eq_map] using Submodule.map_zero _

theorem ker_eq_top {f : M →ₛₗ[τ₁₂] M₂} : ker f = ⊤ ↔ f = 0 :=
  ⟨fun h => ext fun x => mem_ker.1 <| h.symm ▸ trivialₓ, fun h => h.symm ▸ ker_zero⟩

section

variable [RingHomSurjective τ₁₂]

theorem range_le_bot_iff (f : M →ₛₗ[τ₁₂] M₂) : range f ≤ ⊥ ↔ f = 0 := by
  rw [range_le_iff_comap] <;> exact ker_eq_top

theorem range_eq_bot {f : M →ₛₗ[τ₁₂] M₂} : range f = ⊥ ↔ f = 0 := by
  rw [← range_le_bot_iff, le_bot_iff]

theorem range_le_ker_iff {f : M →ₛₗ[τ₁₂] M₂} {g : M₂ →ₛₗ[τ₂₃] M₃} : range f ≤ ker g ↔ (g.comp f : M →ₛₗ[τ₁₃] M₃) = 0 :=
  ⟨fun h => ker_eq_top.1 <| eq_top_iff'.2 fun x => h <| ⟨_, rfl⟩, fun h x hx =>
    mem_ker.2 <|
      (Exists.elim hx) fun y hy => by
        rw [← hy, ← comp_apply, h, zero_apply]⟩

theorem comap_le_comap_iff {f : M →ₛₗ[τ₁₂] M₂} (hf : range f = ⊤) {p p'} : comap f p ≤ comap f p' ↔ p ≤ p' :=
  ⟨fun H x hx => by
    rcases range_eq_top.1 hf x with ⟨y, hy, rfl⟩ <;> exact H hx, comap_mono⟩

theorem comap_injective {f : M →ₛₗ[τ₁₂] M₂} (hf : range f = ⊤) : Injective (comap f) := fun p p' h =>
  le_antisymmₓ ((comap_le_comap_iff hf).1 (le_of_eqₓ h)) ((comap_le_comap_iff hf).1 (ge_of_eq h))

end

theorem ker_eq_bot_of_injective {f : M →ₛₗ[τ₁₂] M₂} (hf : Injective f) : ker f = ⊥ := by
  have : Disjoint ⊤ f.ker := by
    rw [disjoint_ker, ← map_zero f]
    exact fun x hx H => hf H
  simpa [← Disjoint]

/-- The increasing sequence of submodules consisting of the kernels of the iterates of a linear map.
-/
@[simps]
def iterateKer (f : M →ₗ[R] M) : ℕ →o Submodule R M :=
  ⟨fun n => (f ^ n).ker, fun n m w x h => by
    obtain ⟨c, rfl⟩ := le_iff_exists_add.mp w
    rw [LinearMap.mem_ker] at h
    rw [LinearMap.mem_ker, add_commₓ, pow_addₓ, LinearMap.mul_apply, h, LinearMap.map_zero]⟩

end AddCommMonoidₓ

section Ringₓ

variable [Ringₓ R] [Ringₓ R₂] [Ringₓ R₃]

variable [AddCommGroupₓ M] [AddCommGroupₓ M₂] [AddCommGroupₓ M₃]

variable [Module R M] [Module R₂ M₂] [Module R₃ M₃]

variable {τ₁₂ : R →+* R₂} {τ₂₃ : R₂ →+* R₃} {τ₁₃ : R →+* R₃}

variable [RingHomCompTriple τ₁₂ τ₂₃ τ₁₃]

variable {f : M →ₛₗ[τ₁₂] M₂}

include R

open Submodule

theorem range_to_add_subgroup [RingHomSurjective τ₁₂] (f : M →ₛₗ[τ₁₂] M₂) :
    f.range.toAddSubgroup = f.toAddMonoidHom.range :=
  rfl

theorem ker_to_add_subgroup (f : M →ₛₗ[τ₁₂] M₂) : f.ker.toAddSubgroup = f.toAddMonoidHom.ker :=
  rfl

theorem sub_mem_ker_iff {x y} : x - y ∈ f.ker ↔ f x = f y := by
  rw [mem_ker, map_sub, sub_eq_zero]

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (x y «expr ∈ » p)
theorem disjoint_ker' {p : Submodule R M} : Disjoint p (ker f) ↔ ∀ (x y) (_ : x ∈ p) (_ : y ∈ p), f x = f y → x = y :=
  disjoint_ker.trans
    ⟨fun H x hx y hy h =>
      eq_of_sub_eq_zero <|
        H _ (sub_mem hx hy)
          (by
            simp [← h]),
      fun H x h₁ h₂ =>
      H x h₁ 0 (zero_mem _)
        (by
          simpa using h₂)⟩

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (x y «expr ∈ » s)
theorem inj_of_disjoint_ker {p : Submodule R M} {s : Set M} (h : s ⊆ p) (hd : Disjoint p (ker f)) :
    ∀ (x y) (_ : x ∈ s) (_ : y ∈ s), f x = f y → x = y := fun x hx y hy => disjoint_ker'.1 hd _ (h hx) _ (h hy)

theorem ker_eq_bot : ker f = ⊥ ↔ Injective f := by
  simpa [← Disjoint] using @disjoint_ker' _ _ _ _ _ _ _ _ _ _ _ f ⊤

theorem ker_le_iff [RingHomSurjective τ₁₂] {p : Submodule R M} : ker f ≤ p ↔ ∃ y ∈ range f, f ⁻¹' {y} ⊆ p := by
  constructor
  · intro h
    use 0
    rw [← SetLike.mem_coe, f.range_coe]
    exact ⟨⟨0, map_zero f⟩, h⟩
    
  · rintro ⟨y, h₁, h₂⟩
    rw [SetLike.le_def]
    intro z hz
    simp only [← mem_ker, ← SetLike.mem_coe] at hz
    rw [← SetLike.mem_coe, f.range_coe, Set.mem_range] at h₁
    obtain ⟨x, hx⟩ := h₁
    have hx' : x ∈ p := h₂ hx
    have hxz : z + x ∈ p := by
      apply h₂
      simp [← hx, ← hz]
    suffices z + x - x ∈ p by
      simpa only [← this, ← add_sub_cancel]
    exact p.sub_mem hxz hx'
    

end Ringₓ

section Field

variable [Field K] [Field K₂]

variable [AddCommGroupₓ V] [Module K V]

variable [AddCommGroupₓ V₂] [Module K V₂]

theorem ker_smul (f : V →ₗ[K] V₂) (a : K) (h : a ≠ 0) : ker (a • f) = ker f :=
  Submodule.comap_smul f _ a h

theorem ker_smul' (f : V →ₗ[K] V₂) (a : K) : ker (a • f) = ⨅ h : a ≠ 0, ker f :=
  Submodule.comap_smul' f _ a

theorem range_smul (f : V →ₗ[K] V₂) (a : K) (h : a ≠ 0) : range (a • f) = range f := by
  simpa only [← range_eq_map] using Submodule.map_smul f _ a h

theorem range_smul' (f : V →ₗ[K] V₂) (a : K) : range (a • f) = ⨆ h : a ≠ 0, range f := by
  simpa only [← range_eq_map] using Submodule.map_smul' f _ a

end Field

end LinearMap

namespace IsLinearMap

theorem is_linear_map_add [Semiringₓ R] [AddCommMonoidₓ M] [Module R M] : IsLinearMap R fun x : M × M => x.1 + x.2 := by
  apply IsLinearMap.mk
  · intro x y
    simp
    cc
    
  · intro x y
    simp [← smul_add]
    

theorem is_linear_map_sub {R M : Type _} [Semiringₓ R] [AddCommGroupₓ M] [Module R M] :
    IsLinearMap R fun x : M × M => x.1 - x.2 := by
  apply IsLinearMap.mk
  · intro x y
    simp [← add_commₓ, ← add_left_commₓ, ← sub_eq_add_neg]
    
  · intro x y
    simp [← smul_sub]
    

end IsLinearMap

namespace Submodule

section AddCommMonoidₓ

variable [Semiringₓ R] [Semiringₓ R₂] [AddCommMonoidₓ M] [AddCommMonoidₓ M₂]

variable [Module R M] [Module R₂ M₂]

variable (p p' : Submodule R M) (q : Submodule R₂ M₂)

variable {τ₁₂ : R →+* R₂}

open LinearMap

@[simp]
theorem map_top [RingHomSurjective τ₁₂] (f : M →ₛₗ[τ₁₂] M₂) : map f ⊤ = range f :=
  f.range_eq_map.symm

@[simp]
theorem comap_bot (f : M →ₛₗ[τ₁₂] M₂) : comap f ⊥ = ker f :=
  rfl

@[simp]
theorem ker_subtype : p.Subtype.ker = ⊥ :=
  ker_eq_bot_of_injective fun x y => Subtype.ext_val

@[simp]
theorem range_subtype : p.Subtype.range = p := by
  simpa using map_comap_subtype p ⊤

theorem map_subtype_le (p' : Submodule R p) : map p.Subtype p' ≤ p := by
  simpa using (map_le_range : map p.subtype p' ≤ p.subtype.range)

/-- Under the canonical linear map from a submodule `p` to the ambient space `M`, the image of the
maximal submodule of `p` is just `p `. -/
@[simp]
theorem map_subtype_top : map p.Subtype (⊤ : Submodule R p) = p := by
  simp

@[simp]
theorem comap_subtype_eq_top {p p' : Submodule R M} : comap p.Subtype p' = ⊤ ↔ p ≤ p' :=
  eq_top_iff.trans <|
    map_le_iff_le_comap.symm.trans <| by
      rw [map_subtype_top]

@[simp]
theorem comap_subtype_self : comap p.Subtype p = ⊤ :=
  comap_subtype_eq_top.2 le_rfl

@[simp]
theorem ker_of_le (p p' : Submodule R M) (h : p ≤ p') : (ofLe h).ker = ⊥ := by
  rw [of_le, ker_cod_restrict, ker_subtype]

theorem range_of_le (p q : Submodule R M) (h : p ≤ q) : (ofLe h).range = comap q.Subtype p := by
  rw [← map_top, of_le, LinearMap.map_cod_restrict, map_top, range_subtype]

@[simp]
theorem map_subtype_range_of_le {p p' : Submodule R M} (h : p ≤ p') : map p'.Subtype (ofLe h).range = p := by
  simp [← range_of_le, ← map_comap_eq, ← h]

theorem disjoint_iff_comap_eq_bot {p q : Submodule R M} : Disjoint p q ↔ comap p.Subtype q = ⊥ := by
  rw [← (map_injective_of_injective (show injective p.subtype from Subtype.coe_injective)).eq_iff, map_comap_subtype,
    map_bot, disjoint_iff]

/-- If `N ⊆ M` then submodules of `N` are the same as submodules of `M` contained in `N` -/
def MapSubtype.relIso : Submodule R p ≃o { p' : Submodule R M // p' ≤ p } where
  toFun := fun p' => ⟨map p.Subtype p', map_subtype_le p _⟩
  invFun := fun q => comap p.Subtype q
  left_inv := fun p' => comap_map_eq_of_injective Subtype.coe_injective p'
  right_inv := fun ⟨q, hq⟩ =>
    Subtype.ext_val <| by
      simp [← map_comap_subtype p, ← inf_of_le_right hq]
  map_rel_iff' := fun p₁ p₂ =>
    Subtype.coe_le_coe.symm.trans
      (by
        dsimp'
        rw [map_le_iff_le_comap, comap_map_eq_of_injective (show injective p.subtype from Subtype.coe_injective) p₂])

/-- If `p ⊆ M` is a submodule, the ordering of submodules of `p` is embedded in the ordering of
submodules of `M`. -/
def MapSubtype.orderEmbedding : Submodule R p ↪o Submodule R M :=
  (RelIso.toRelEmbedding <| MapSubtype.relIso p).trans (Subtype.relEmbedding _ _)

@[simp]
theorem map_subtype_embedding_eq (p' : Submodule R p) : MapSubtype.orderEmbedding p p' = map p.Subtype p' :=
  rfl

end AddCommMonoidₓ

end Submodule

namespace LinearMap

section Semiringₓ

variable [Semiringₓ R] [Semiringₓ R₂] [Semiringₓ R₃]

variable [AddCommMonoidₓ M] [AddCommMonoidₓ M₂] [AddCommMonoidₓ M₃]

variable [Module R M] [Module R₂ M₂] [Module R₃ M₃]

variable {τ₁₂ : R →+* R₂} {τ₂₃ : R₂ →+* R₃} {τ₁₃ : R →+* R₃}

variable [RingHomCompTriple τ₁₂ τ₂₃ τ₁₃]

/-- A monomorphism is injective. -/
theorem ker_eq_bot_of_cancel {f : M →ₛₗ[τ₁₂] M₂} (h : ∀ u v : f.ker →ₗ[R] M, f.comp u = f.comp v → u = v) : f.ker = ⊥ :=
  by
  have h₁ : f.comp (0 : f.ker →ₗ[R] M) = 0 := comp_zero _
  rw [← Submodule.range_subtype f.ker, ← h 0 f.ker.subtype (Eq.trans h₁ (comp_ker_subtype f).symm)]
  exact range_zero

theorem range_comp_of_range_eq_top [RingHomSurjective τ₁₂] [RingHomSurjective τ₂₃] [RingHomSurjective τ₁₃]
    {f : M →ₛₗ[τ₁₂] M₂} (g : M₂ →ₛₗ[τ₂₃] M₃) (hf : range f = ⊤) : range (g.comp f : M →ₛₗ[τ₁₃] M₃) = range g := by
  rw [range_comp, hf, Submodule.map_top]

theorem ker_comp_of_ker_eq_bot (f : M →ₛₗ[τ₁₂] M₂) {g : M₂ →ₛₗ[τ₂₃] M₃} (hg : ker g = ⊥) :
    ker (g.comp f : M →ₛₗ[τ₁₃] M₃) = ker f := by
  rw [ker_comp, hg, Submodule.comap_bot]

section Image

/-- If `O` is a submodule of `M`, and `Φ : O →ₗ M'` is a linear map,
then `(ϕ : O →ₗ M').submodule_image N` is `ϕ(N)` as a submodule of `M'` -/
def submoduleImage {M' : Type _} [AddCommMonoidₓ M'] [Module R M'] {O : Submodule R M} (ϕ : O →ₗ[R] M')
    (N : Submodule R M) : Submodule R M' :=
  (N.comap O.Subtype).map ϕ

@[simp]
theorem mem_submodule_image {M' : Type _} [AddCommMonoidₓ M'] [Module R M'] {O : Submodule R M} {ϕ : O →ₗ[R] M'}
    {N : Submodule R M} {x : M'} : x ∈ ϕ.submoduleImage N ↔ ∃ (y : _)(yO : y ∈ O)(yN : y ∈ N), ϕ ⟨y, yO⟩ = x := by
  refine' submodule.mem_map.trans ⟨_, _⟩ <;> simp_rw [Submodule.mem_comap]
  · rintro ⟨⟨y, yO⟩, yN : y ∈ N, h⟩
    exact ⟨y, yO, yN, h⟩
    
  · rintro ⟨y, yO, yN, h⟩
    exact ⟨⟨y, yO⟩, yN, h⟩
    

theorem mem_submodule_image_of_le {M' : Type _} [AddCommMonoidₓ M'] [Module R M'] {O : Submodule R M} {ϕ : O →ₗ[R] M'}
    {N : Submodule R M} (hNO : N ≤ O) {x : M'} : x ∈ ϕ.submoduleImage N ↔ ∃ (y : _)(yN : y ∈ N), ϕ ⟨y, hNO yN⟩ = x := by
  refine' mem_submodule_image.trans ⟨_, _⟩
  · rintro ⟨y, yO, yN, h⟩
    exact ⟨y, yN, h⟩
    
  · rintro ⟨y, yN, h⟩
    exact ⟨y, hNO yN, yN, h⟩
    

theorem submodule_image_apply_of_le {M' : Type _} [AddCommGroupₓ M'] [Module R M'] {O : Submodule R M} (ϕ : O →ₗ[R] M')
    (N : Submodule R M) (hNO : N ≤ O) : ϕ.submoduleImage N = (ϕ.comp (Submodule.ofLe hNO)).range := by
  rw [submodule_image, range_comp, Submodule.range_of_le]

end Image

end Semiringₓ

end LinearMap

@[simp]
theorem LinearMap.range_range_restrict [Semiringₓ R] [AddCommMonoidₓ M] [AddCommMonoidₓ M₂] [Module R M] [Module R M₂]
    (f : M →ₗ[R] M₂) : f.range_restrict.range = ⊤ := by
  simp [← f.range_cod_restrict _]

/-! ### Linear equivalences -/


namespace LinearEquiv

section AddCommMonoidₓ

section Subsingleton

variable [Semiringₓ R] [Semiringₓ R₂] [Semiringₓ R₃] [Semiringₓ R₄]

variable [AddCommMonoidₓ M] [AddCommMonoidₓ M₂] [AddCommMonoidₓ M₃] [AddCommMonoidₓ M₄]

variable [Module R M] [Module R₂ M₂]

variable [Subsingleton M] [Subsingleton M₂]

variable {σ₁₂ : R →+* R₂} {σ₂₁ : R₂ →+* R}

variable [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]

include σ₂₁

/-- Between two zero modules, the zero map is an equivalence. -/
instance : Zero (M ≃ₛₗ[σ₁₂] M₂) :=
  ⟨{ (0 : M →ₛₗ[σ₁₂] M₂) with toFun := 0, invFun := 0, right_inv := fun x => Subsingleton.elimₓ _ _,
      left_inv := fun x => Subsingleton.elimₓ _ _ }⟩

omit σ₂₁

-- Even though these are implied by `subsingleton.elim` via the `unique` instance below, they're
-- nice to have as `rfl`-lemmas for `dsimp`.
include σ₂₁

@[simp]
theorem zero_symm : (0 : M ≃ₛₗ[σ₁₂] M₂).symm = 0 :=
  rfl

@[simp]
theorem coe_zero : ⇑(0 : M ≃ₛₗ[σ₁₂] M₂) = 0 :=
  rfl

theorem zero_apply (x : M) : (0 : M ≃ₛₗ[σ₁₂] M₂) x = 0 :=
  rfl

/-- Between two zero modules, the zero map is the only equivalence. -/
instance : Unique (M ≃ₛₗ[σ₁₂] M₂) where
  uniq := fun f => to_linear_map_injective (Subsingleton.elimₓ _ _)
  default := 0

omit σ₂₁

end Subsingleton

section

variable [Semiringₓ R] [Semiringₓ R₂] [Semiringₓ R₃] [Semiringₓ R₄]

variable [AddCommMonoidₓ M] [AddCommMonoidₓ M₂] [AddCommMonoidₓ M₃] [AddCommMonoidₓ M₄]

variable {module_M : Module R M} {module_M₂ : Module R₂ M₂}

variable {σ₁₂ : R →+* R₂} {σ₂₁ : R₂ →+* R}

variable {re₁₂ : RingHomInvPair σ₁₂ σ₂₁} {re₂₁ : RingHomInvPair σ₂₁ σ₁₂}

variable (e e' : M ≃ₛₗ[σ₁₂] M₂)

theorem map_eq_comap {p : Submodule R M} :
    (p.map (e : M →ₛₗ[σ₁₂] M₂) : Submodule R₂ M₂) = p.comap (e.symm : M₂ →ₛₗ[σ₂₁] M) :=
  SetLike.coe_injective <| by
    simp [← e.image_eq_preimage]

/-- A linear equivalence of two modules restricts to a linear equivalence from any submodule
`p` of the domain onto the image of that submodule.

This is the linear version of `add_equiv.submonoid_map` and `add_equiv.subgroup_map`.

This is `linear_equiv.of_submodule'` but with `map` on the right instead of `comap` on the left. -/
def submoduleMap (p : Submodule R M) : p ≃ₛₗ[σ₁₂] ↥(p.map (e : M →ₛₗ[σ₁₂] M₂) : Submodule R₂ M₂) :=
  { ((e : M →ₛₗ[σ₁₂] M₂).domRestrict p).codRestrict (p.map (e : M →ₛₗ[σ₁₂] M₂)) fun x =>
      ⟨x, by
        simp only [← LinearMap.dom_restrict_apply, ← eq_self_iff_true, ← and_trueₓ, ← SetLike.coe_mem, ←
          SetLike.mem_coe]⟩ with
    invFun := fun y =>
      ⟨(e.symm : M₂ →ₛₗ[σ₂₁] M) y, by
        rcases y with ⟨y', hy⟩
        rw [Submodule.mem_map] at hy
        rcases hy with ⟨x, hx, hxy⟩
        subst hxy
        simp only [← symm_apply_apply, ← Submodule.coe_mk, ← coe_coe, ← hx]⟩,
    left_inv := fun x => by
      simp only [← LinearMap.dom_restrict_apply, ← LinearMap.cod_restrict_apply, ← LinearMap.to_fun_eq_coe, ←
        LinearEquiv.coe_coe, ← LinearEquiv.symm_apply_apply, ← SetLike.eta],
    right_inv := fun y => by
      apply SetCoe.ext
      simp only [← LinearMap.dom_restrict_apply, ← LinearMap.cod_restrict_apply, ← LinearMap.to_fun_eq_coe, ←
        LinearEquiv.coe_coe, ← SetLike.coe_mk, ← LinearEquiv.apply_symm_apply] }

include σ₂₁

@[simp]
theorem submodule_map_apply (p : Submodule R M) (x : p) : ↑(e.submoduleMap p x) = e x :=
  rfl

@[simp]
theorem submodule_map_symm_apply (p : Submodule R M) (x : (p.map (e : M →ₛₗ[σ₁₂] M₂) : Submodule R₂ M₂)) :
    ↑((e.submoduleMap p).symm x) = e.symm x :=
  rfl

omit σ₂₁

end

section Finsupp

variable {γ : Type _}

variable [Semiringₓ R] [Semiringₓ R₂]

variable [AddCommMonoidₓ M] [AddCommMonoidₓ M₂]

variable [Module R M] [Module R₂ M₂] [Zero γ]

variable {τ₁₂ : R →+* R₂} {τ₂₁ : R₂ →+* R}

variable [RingHomInvPair τ₁₂ τ₂₁] [RingHomInvPair τ₂₁ τ₁₂]

include τ₂₁

@[simp]
theorem map_finsupp_sum (f : M ≃ₛₗ[τ₁₂] M₂) {t : ι →₀ γ} {g : ι → γ → M} : f (t.Sum g) = t.Sum fun i d => f (g i d) :=
  f.map_sum _

omit τ₂₁

end Finsupp

section Dfinsupp

open Dfinsupp

variable [Semiringₓ R] [Semiringₓ R₂]

variable [AddCommMonoidₓ M] [AddCommMonoidₓ M₂]

variable [Module R M] [Module R₂ M₂]

variable {τ₁₂ : R →+* R₂} {τ₂₁ : R₂ →+* R}

variable [RingHomInvPair τ₁₂ τ₂₁] [RingHomInvPair τ₂₁ τ₁₂]

variable {γ : ι → Type _} [DecidableEq ι]

include τ₂₁

@[simp]
theorem map_dfinsupp_sum [∀ i, Zero (γ i)] [∀ (i) (x : γ i), Decidable (x ≠ 0)] (f : M ≃ₛₗ[τ₁₂] M₂) (t : Π₀ i, γ i)
    (g : ∀ i, γ i → M) : f (t.Sum g) = t.Sum fun i d => f (g i d) :=
  f.map_sum _

@[simp]
theorem map_dfinsupp_sum_add_hom [∀ i, AddZeroClassₓ (γ i)] (f : M ≃ₛₗ[τ₁₂] M₂) (t : Π₀ i, γ i) (g : ∀ i, γ i →+ M) :
    f (sumAddHom g t) = sumAddHom (fun i => f.toAddEquiv.toAddMonoidHom.comp (g i)) t :=
  f.toAddEquiv.map_dfinsupp_sum_add_hom _ _

end Dfinsupp

section Uncurry

variable [Semiringₓ R] [Semiringₓ R₂] [Semiringₓ R₃] [Semiringₓ R₄]

variable [AddCommMonoidₓ M] [AddCommMonoidₓ M₂] [AddCommMonoidₓ M₃] [AddCommMonoidₓ M₄]

variable (V V₂ R)

/-- Linear equivalence between a curried and uncurried function.
  Differs from `tensor_product.curry`. -/
protected def curry : (V × V₂ → R) ≃ₗ[R] V → V₂ → R :=
  { Equivₓ.curry _ _ _ with
    map_add' := fun _ _ => by
      ext
      rfl,
    map_smul' := fun _ _ => by
      ext
      rfl }

@[simp]
theorem coe_curry : ⇑(LinearEquiv.curry R V V₂) = curry :=
  rfl

@[simp]
theorem coe_curry_symm : ⇑(LinearEquiv.curry R V V₂).symm = uncurry :=
  rfl

end Uncurry

section

variable [Semiringₓ R] [Semiringₓ R₂] [Semiringₓ R₃] [Semiringₓ R₄]

variable [AddCommMonoidₓ M] [AddCommMonoidₓ M₂] [AddCommMonoidₓ M₃] [AddCommMonoidₓ M₄]

variable {module_M : Module R M} {module_M₂ : Module R₂ M₂} {module_M₃ : Module R₃ M₃}

variable {σ₁₂ : R →+* R₂} {σ₂₁ : R₂ →+* R}

variable {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R →+* R₃} [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]

variable {σ₃₂ : R₃ →+* R₂}

variable {re₁₂ : RingHomInvPair σ₁₂ σ₂₁} {re₂₁ : RingHomInvPair σ₂₁ σ₁₂}

variable {re₂₃ : RingHomInvPair σ₂₃ σ₃₂} {re₃₂ : RingHomInvPair σ₃₂ σ₂₃}

variable (f : M →ₛₗ[σ₁₂] M₂) (g : M₂ →ₛₗ[σ₂₁] M) (e : M ≃ₛₗ[σ₁₂] M₂) (h : M₂ →ₛₗ[σ₂₃] M₃)

variable (e'' : M₂ ≃ₛₗ[σ₂₃] M₃)

variable (p q : Submodule R M)

/-- Linear equivalence between two equal submodules. -/
def ofEq (h : p = q) : p ≃ₗ[R] q :=
  { Equivₓ.Set.ofEq (congr_arg _ h) with map_smul' := fun _ _ => rfl, map_add' := fun _ _ => rfl }

variable {p q}

@[simp]
theorem coe_of_eq_apply (h : p = q) (x : p) : (ofEq p q h x : M) = x :=
  rfl

@[simp]
theorem of_eq_symm (h : p = q) : (ofEq p q h).symm = ofEq q p h.symm :=
  rfl

include σ₂₁

/-- A linear equivalence which maps a submodule of one module onto another, restricts to a linear
equivalence of the two submodules. -/
def ofSubmodules (p : Submodule R M) (q : Submodule R₂ M₂) (h : p.map (e : M →ₛₗ[σ₁₂] M₂) = q) : p ≃ₛₗ[σ₁₂] q :=
  (e.submoduleMap p).trans (LinearEquiv.ofEq _ _ h)

@[simp]
theorem of_submodules_apply {p : Submodule R M} {q : Submodule R₂ M₂} (h : p.map ↑e = q) (x : p) :
    ↑(e.ofSubmodules p q h x) = e x :=
  rfl

@[simp]
theorem of_submodules_symm_apply {p : Submodule R M} {q : Submodule R₂ M₂} (h : p.map ↑e = q) (x : q) :
    ↑((e.ofSubmodules p q h).symm x) = e.symm x :=
  rfl

include re₁₂ re₂₁

/-- A linear equivalence of two modules restricts to a linear equivalence from the preimage of any
submodule to that submodule.

This is `linear_equiv.of_submodule` but with `comap` on the left instead of `map` on the right. -/
def ofSubmodule' [Module R M] [Module R₂ M₂] (f : M ≃ₛₗ[σ₁₂] M₂) (U : Submodule R₂ M₂) :
    U.comap (f : M →ₛₗ[σ₁₂] M₂) ≃ₛₗ[σ₁₂] U :=
  (f.symm.ofSubmodules _ _ f.symm.map_eq_comap).symm

theorem of_submodule'_to_linear_map [Module R M] [Module R₂ M₂] (f : M ≃ₛₗ[σ₁₂] M₂) (U : Submodule R₂ M₂) :
    (f.ofSubmodule' U).toLinearMap = (f.toLinearMap.domRestrict _).codRestrict _ Subtype.prop := by
  ext
  rfl

@[simp]
theorem of_submodule'_apply [Module R M] [Module R₂ M₂] (f : M ≃ₛₗ[σ₁₂] M₂) (U : Submodule R₂ M₂)
    (x : U.comap (f : M →ₛₗ[σ₁₂] M₂)) : (f.ofSubmodule' U x : M₂) = f (x : M) :=
  rfl

@[simp]
theorem of_submodule'_symm_apply [Module R M] [Module R₂ M₂] (f : M ≃ₛₗ[σ₁₂] M₂) (U : Submodule R₂ M₂) (x : U) :
    ((f.ofSubmodule' U).symm x : M) = f.symm (x : M₂) :=
  rfl

variable (p)

omit σ₂₁ re₁₂ re₂₁

/-- The top submodule of `M` is linearly equivalent to `M`. -/
def ofTop (h : p = ⊤) : p ≃ₗ[R] M :=
  { p.Subtype with invFun := fun x => ⟨x, h.symm ▸ trivialₓ⟩, left_inv := fun ⟨x, h⟩ => rfl, right_inv := fun x => rfl }

@[simp]
theorem of_top_apply {h} (x : p) : ofTop p h x = x :=
  rfl

@[simp]
theorem coe_of_top_symm_apply {h} (x : M) : ((ofTop p h).symm x : M) = x :=
  rfl

theorem of_top_symm_apply {h} (x : M) : (ofTop p h).symm x = ⟨x, h.symm ▸ trivialₓ⟩ :=
  rfl

include σ₂₁ re₁₂ re₂₁

/-- If a linear map has an inverse, it is a linear equivalence. -/
def ofLinear (h₁ : f.comp g = LinearMap.id) (h₂ : g.comp f = LinearMap.id) : M ≃ₛₗ[σ₁₂] M₂ :=
  { f with invFun := g, left_inv := LinearMap.ext_iff.1 h₂, right_inv := LinearMap.ext_iff.1 h₁ }

omit σ₂₁ re₁₂ re₂₁

include σ₂₁ re₁₂ re₂₁

@[simp]
theorem of_linear_apply {h₁ h₂} (x : M) : ofLinear f g h₁ h₂ x = f x :=
  rfl

omit σ₂₁ re₁₂ re₂₁

include σ₂₁ re₁₂ re₂₁

@[simp]
theorem of_linear_symm_apply {h₁ h₂} (x : M₂) : (ofLinear f g h₁ h₂).symm x = g x :=
  rfl

omit σ₂₁ re₁₂ re₂₁

@[simp]
protected theorem range : (e : M →ₛₗ[σ₁₂] M₂).range = ⊤ :=
  LinearMap.range_eq_top.2 e.toEquiv.Surjective

include σ₂₁ re₁₂ re₂₁

theorem eq_bot_of_equiv [Module R₂ M₂] (e : p ≃ₛₗ[σ₁₂] (⊥ : Submodule R₂ M₂)) : p = ⊥ := by
  refine' bot_unique (SetLike.le_def.2 fun b hb => (Submodule.mem_bot R).2 _)
  rw [← p.mk_eq_zero hb, ← e.map_eq_zero_iff]
  apply Submodule.eq_zero_of_bot_submodule

omit σ₂₁ re₁₂ re₂₁

@[simp]
protected theorem ker : (e : M →ₛₗ[σ₁₂] M₂).ker = ⊥ :=
  LinearMap.ker_eq_bot_of_injective e.toEquiv.Injective

@[simp]
theorem range_comp [RingHomSurjective σ₁₂] [RingHomSurjective σ₂₃] [RingHomSurjective σ₁₃] :
    (h.comp (e : M →ₛₗ[σ₁₂] M₂) : M →ₛₗ[σ₁₃] M₃).range = h.range :=
  LinearMap.range_comp_of_range_eq_top _ e.range

include module_M

@[simp]
theorem ker_comp (l : M →ₛₗ[σ₁₂] M₂) : (((e'' : M₂ →ₛₗ[σ₂₃] M₃).comp l : M →ₛₗ[σ₁₃] M₃) : M →ₛₗ[σ₁₃] M₃).ker = l.ker :=
  LinearMap.ker_comp_of_ker_eq_bot _ e''.ker

omit module_M

variable {f g}

include σ₂₁

/-- An linear map `f : M →ₗ[R] M₂` with a left-inverse `g : M₂ →ₗ[R] M` defines a linear
equivalence between `M` and `f.range`.

This is a computable alternative to `linear_equiv.of_injective`, and a bidirectional version of
`linear_map.range_restrict`. -/
def ofLeftInverse [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂] {g : M₂ → M} (h : Function.LeftInverse g f) :
    M ≃ₛₗ[σ₁₂] f.range :=
  { f.range_restrict with toFun := f.range_restrict, invFun := g ∘ f.range.Subtype, left_inv := h,
    right_inv := fun x =>
      Subtype.ext <|
        let ⟨x', hx'⟩ := LinearMap.mem_range.mp x.Prop
        show f (g x) = x by
          rw [← hx', h x'] }

omit σ₂₁

@[simp]
theorem of_left_inverse_apply [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂] (h : Function.LeftInverse g f) (x : M) :
    ↑(ofLeftInverse h x) = f x :=
  rfl

include σ₂₁

@[simp]
theorem of_left_inverse_symm_apply [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂] (h : Function.LeftInverse g f)
    (x : f.range) : (ofLeftInverse h).symm x = g x :=
  rfl

omit σ₂₁

variable (f)

/-- An `injective` linear map `f : M →ₗ[R] M₂` defines a linear equivalence
between `M` and `f.range`. See also `linear_map.of_left_inverse`. -/
noncomputable def ofInjective [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂] (h : Injective f) :
    M ≃ₛₗ[σ₁₂] f.range :=
  of_left_inverse <| Classical.some_spec h.HasLeftInverse

@[simp]
theorem of_injective_apply [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂] {h : Injective f} (x : M) :
    ↑(ofInjective f h x) = f x :=
  rfl

/-- A bijective linear map is a linear equivalence. -/
noncomputable def ofBijective [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂] (hf₁ : Injective f)
    (hf₂ : Surjective f) : M ≃ₛₗ[σ₁₂] M₂ :=
  (ofInjective f hf₁).trans (ofTop _ <| LinearMap.range_eq_top.2 hf₂)

@[simp]
theorem of_bijective_apply [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂] {hf₁ hf₂} (x : M) :
    ofBijective f hf₁ hf₂ x = f x :=
  rfl

end

end AddCommMonoidₓ

section AddCommGroupₓ

variable [Semiringₓ R] [Semiringₓ R₂] [Semiringₓ R₃] [Semiringₓ R₄]

variable [AddCommGroupₓ M] [AddCommGroupₓ M₂] [AddCommGroupₓ M₃] [AddCommGroupₓ M₄]

variable {module_M : Module R M} {module_M₂ : Module R₂ M₂}

variable {module_M₃ : Module R₃ M₃} {module_M₄ : Module R₄ M₄}

variable {σ₁₂ : R →+* R₂} {σ₃₄ : R₃ →+* R₄}

variable {σ₂₁ : R₂ →+* R} {σ₄₃ : R₄ →+* R₃}

variable {re₁₂ : RingHomInvPair σ₁₂ σ₂₁} {re₂₁ : RingHomInvPair σ₂₁ σ₁₂}

variable {re₃₄ : RingHomInvPair σ₃₄ σ₄₃} {re₄₃ : RingHomInvPair σ₄₃ σ₃₄}

variable (e e₁ : M ≃ₛₗ[σ₁₂] M₂) (e₂ : M₃ ≃ₛₗ[σ₃₄] M₄)

@[simp]
theorem map_neg (a : M) : e (-a) = -e a :=
  e.toLinearMap.map_neg a

@[simp]
theorem map_sub (a b : M) : e (a - b) = e a - e b :=
  e.toLinearMap.map_sub a b

end AddCommGroupₓ

section Neg

variable (R) [Semiringₓ R] [AddCommGroupₓ M] [Module R M]

/-- `x ↦ -x` as a `linear_equiv` -/
def neg : M ≃ₗ[R] M :=
  { Equivₓ.neg M, (-LinearMap.id : M →ₗ[R] M) with }

variable {R}

@[simp]
theorem coe_neg : ⇑(neg R : M ≃ₗ[R] M) = -id :=
  rfl

theorem neg_apply (x : M) : neg R x = -x := by
  simp

@[simp]
theorem symm_neg : (neg R : M ≃ₗ[R] M).symm = neg R :=
  rfl

end Neg

section CommSemiringₓ

variable [CommSemiringₓ R] [AddCommMonoidₓ M] [AddCommMonoidₓ M₂] [AddCommMonoidₓ M₃]

variable [Module R M] [Module R M₂] [Module R M₃]

open _Root_.LinearMap

/-- Multiplying by a unit `a` of the ring `R` is a linear equivalence. -/
def smulOfUnit (a : Rˣ) : M ≃ₗ[R] M :=
  DistribMulAction.toLinearEquiv R M a

/-- A linear isomorphism between the domains and codomains of two spaces of linear maps gives a
linear isomorphism between the two function spaces. -/
def arrowCongr {R M₁ M₂ M₂₁ M₂₂ : Sort _} [CommSemiringₓ R] [AddCommMonoidₓ M₁] [AddCommMonoidₓ M₂] [AddCommMonoidₓ M₂₁]
    [AddCommMonoidₓ M₂₂] [Module R M₁] [Module R M₂] [Module R M₂₁] [Module R M₂₂] (e₁ : M₁ ≃ₗ[R] M₂)
    (e₂ : M₂₁ ≃ₗ[R] M₂₂) : (M₁ →ₗ[R] M₂₁) ≃ₗ[R] M₂ →ₗ[R] M₂₂ where
  toFun := fun f : M₁ →ₗ[R] M₂₁ => (e₂ : M₂₁ →ₗ[R] M₂₂).comp <| f.comp (e₁.symm : M₂ →ₗ[R] M₁)
  invFun := fun f => (e₂.symm : M₂₂ →ₗ[R] M₂₁).comp <| f.comp (e₁ : M₁ →ₗ[R] M₂)
  left_inv := fun f => by
    ext x
    simp only [← symm_apply_apply, ← comp_app, ← coe_comp, ← coe_coe]
  right_inv := fun f => by
    ext x
    simp only [← comp_app, ← apply_symm_apply, ← coe_comp, ← coe_coe]
  map_add' := fun f g => by
    ext x
    simp only [← map_add, ← add_apply, ← comp_app, ← coe_comp, ← coe_coe]
  map_smul' := fun c f => by
    ext x
    simp only [← smul_apply, ← comp_app, ← coe_comp, ← map_smulₛₗ e₂, ← coe_coe]

@[simp]
theorem arrow_congr_apply {R M₁ M₂ M₂₁ M₂₂ : Sort _} [CommSemiringₓ R] [AddCommMonoidₓ M₁] [AddCommMonoidₓ M₂]
    [AddCommMonoidₓ M₂₁] [AddCommMonoidₓ M₂₂] [Module R M₁] [Module R M₂] [Module R M₂₁] [Module R M₂₂]
    (e₁ : M₁ ≃ₗ[R] M₂) (e₂ : M₂₁ ≃ₗ[R] M₂₂) (f : M₁ →ₗ[R] M₂₁) (x : M₂) : arrowCongr e₁ e₂ f x = e₂ (f (e₁.symm x)) :=
  rfl

@[simp]
theorem arrow_congr_symm_apply {R M₁ M₂ M₂₁ M₂₂ : Sort _} [CommSemiringₓ R] [AddCommMonoidₓ M₁] [AddCommMonoidₓ M₂]
    [AddCommMonoidₓ M₂₁] [AddCommMonoidₓ M₂₂] [Module R M₁] [Module R M₂] [Module R M₂₁] [Module R M₂₂]
    (e₁ : M₁ ≃ₗ[R] M₂) (e₂ : M₂₁ ≃ₗ[R] M₂₂) (f : M₂ →ₗ[R] M₂₂) (x : M₁) :
    (arrowCongr e₁ e₂).symm f x = e₂.symm (f (e₁ x)) :=
  rfl

theorem arrow_congr_comp {N N₂ N₃ : Sort _} [AddCommMonoidₓ N] [AddCommMonoidₓ N₂] [AddCommMonoidₓ N₃] [Module R N]
    [Module R N₂] [Module R N₃] (e₁ : M ≃ₗ[R] N) (e₂ : M₂ ≃ₗ[R] N₂) (e₃ : M₃ ≃ₗ[R] N₃) (f : M →ₗ[R] M₂)
    (g : M₂ →ₗ[R] M₃) : arrowCongr e₁ e₃ (g.comp f) = (arrowCongr e₂ e₃ g).comp (arrowCongr e₁ e₂ f) := by
  ext
  simp only [← symm_apply_apply, ← arrow_congr_apply, ← LinearMap.comp_apply]

theorem arrow_congr_trans {M₁ M₂ M₃ N₁ N₂ N₃ : Sort _} [AddCommMonoidₓ M₁] [Module R M₁] [AddCommMonoidₓ M₂]
    [Module R M₂] [AddCommMonoidₓ M₃] [Module R M₃] [AddCommMonoidₓ N₁] [Module R N₁] [AddCommMonoidₓ N₂] [Module R N₂]
    [AddCommMonoidₓ N₃] [Module R N₃] (e₁ : M₁ ≃ₗ[R] M₂) (e₂ : N₁ ≃ₗ[R] N₂) (e₃ : M₂ ≃ₗ[R] M₃) (e₄ : N₂ ≃ₗ[R] N₃) :
    (arrowCongr e₁ e₂).trans (arrowCongr e₃ e₄) = arrowCongr (e₁.trans e₃) (e₂.trans e₄) :=
  rfl

/-- If `M₂` and `M₃` are linearly isomorphic then the two spaces of linear maps from `M` into `M₂`
and `M` into `M₃` are linearly isomorphic. -/
def congrRight (f : M₂ ≃ₗ[R] M₃) : (M →ₗ[R] M₂) ≃ₗ[R] M →ₗ[R] M₃ :=
  arrowCongr (LinearEquiv.refl R M) f

/-- If `M` and `M₂` are linearly isomorphic then the two spaces of linear maps from `M` and `M₂` to
themselves are linearly isomorphic. -/
def conj (e : M ≃ₗ[R] M₂) : Module.End R M ≃ₗ[R] Module.End R M₂ :=
  arrowCongr e e

theorem conj_apply (e : M ≃ₗ[R] M₂) (f : Module.End R M) :
    e.conj f = ((↑e : M →ₗ[R] M₂).comp f).comp (e.symm : M₂ →ₗ[R] M) :=
  rfl

theorem symm_conj_apply (e : M ≃ₗ[R] M₂) (f : Module.End R M₂) :
    e.symm.conj f = ((↑e.symm : M₂ →ₗ[R] M).comp f).comp (e : M →ₗ[R] M₂) :=
  rfl

theorem conj_comp (e : M ≃ₗ[R] M₂) (f g : Module.End R M) : e.conj (g.comp f) = (e.conj g).comp (e.conj f) :=
  arrow_congr_comp e e e f g

theorem conj_trans (e₁ : M ≃ₗ[R] M₂) (e₂ : M₂ ≃ₗ[R] M₃) : e₁.conj.trans e₂.conj = (e₁.trans e₂).conj := by
  ext f x
  rfl

@[simp]
theorem conj_id (e : M ≃ₗ[R] M₂) : e.conj LinearMap.id = LinearMap.id := by
  ext
  simp [← conj_apply]

end CommSemiringₓ

section Field

variable [Field K] [AddCommGroupₓ M] [AddCommGroupₓ M₂] [AddCommGroupₓ M₃]

variable [Module K M] [Module K M₂] [Module K M₃]

variable (K) (M)

open _Root_.LinearMap

/-- Multiplying by a nonzero element `a` of the field `K` is a linear equivalence. -/
@[simps]
def smulOfNeZero (a : K) (ha : a ≠ 0) : M ≃ₗ[K] M :=
  smul_of_unit <| Units.mk0 a ha

end Field

end LinearEquiv

namespace Submodule

section Module

variable [Semiringₓ R] [AddCommMonoidₓ M] [Module R M]

/-- Given `p` a submodule of the module `M` and `q` a submodule of `p`, `p.equiv_subtype_map q`
is the natural `linear_equiv` between `q` and `q.map p.subtype`. -/
def equivSubtypeMap (p : Submodule R M) (q : Submodule R p) : q ≃ₗ[R] q.map p.Subtype :=
  { (p.Subtype.domRestrict q).codRestrict _
      (by
        rintro ⟨x, hx⟩
        refine' ⟨x, hx, rfl⟩) with
    invFun := by
      rintro ⟨x, hx⟩
      refine' ⟨⟨x, _⟩, _⟩ <;> rcases hx with ⟨⟨_, h⟩, _, rfl⟩ <;> assumption,
    left_inv := fun ⟨⟨_, _⟩, _⟩ => rfl, right_inv := fun ⟨x, ⟨_, h⟩, _, rfl⟩ => rfl }

@[simp]
theorem equiv_subtype_map_apply {p : Submodule R M} {q : Submodule R p} (x : q) :
    (p.equivSubtypeMap q x : M) = p.Subtype.domRestrict q x :=
  rfl

@[simp]
theorem equiv_subtype_map_symm_apply {p : Submodule R M} {q : Submodule R p} (x : q.map p.Subtype) :
    ((p.equivSubtypeMap q).symm x : M) = x := by
  cases x
  rfl

/-- If `s ≤ t`, then we can view `s` as a submodule of `t` by taking the comap
of `t.subtype`. -/
@[simps]
def comapSubtypeEquivOfLe {p q : Submodule R M} (hpq : p ≤ q) : comap q.Subtype p ≃ₗ[R] p where
  toFun := fun x => ⟨x, x.2⟩
  invFun := fun x => ⟨⟨x, hpq x.2⟩, x.2⟩
  left_inv := fun x => by
    simp only [← coe_mk, ← SetLike.eta, ← coe_coe]
  right_inv := fun x => by
    simp only [← Subtype.coe_mk, ← SetLike.eta, ← coe_coe]
  map_add' := fun x y => rfl
  map_smul' := fun c x => rfl

end Module

end Submodule

namespace Submodule

variable [CommSemiringₓ R] [CommSemiringₓ R₂]

variable [AddCommMonoidₓ M] [AddCommMonoidₓ M₂] [Module R M] [Module R₂ M₂]

variable [AddCommMonoidₓ N] [AddCommMonoidₓ N₂] [Module R N] [Module R N₂]

variable {τ₁₂ : R →+* R₂} {τ₂₁ : R₂ →+* R}

variable [RingHomInvPair τ₁₂ τ₂₁] [RingHomInvPair τ₂₁ τ₁₂]

variable (p : Submodule R M) (q : Submodule R₂ M₂)

variable (pₗ : Submodule R N) (qₗ : Submodule R N₂)

include τ₂₁

@[simp]
theorem mem_map_equiv {e : M ≃ₛₗ[τ₁₂] M₂} {x : M₂} : x ∈ p.map (e : M →ₛₗ[τ₁₂] M₂) ↔ e.symm x ∈ p := by
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, hx⟩
    simp [hx, ← hy]
    
  · intro hx
    refine'
      ⟨e.symm x, hx, by
        simp ⟩
    

omit τ₂₁

theorem map_equiv_eq_comap_symm (e : M ≃ₛₗ[τ₁₂] M₂) (K : Submodule R M) :
    K.map (e : M →ₛₗ[τ₁₂] M₂) = K.comap (e.symm : M₂ →ₛₗ[τ₂₁] M) :=
  Submodule.ext fun _ => by
    rw [mem_map_equiv, mem_comap, LinearEquiv.coe_coe]

theorem comap_equiv_eq_map_symm (e : M ≃ₛₗ[τ₁₂] M₂) (K : Submodule R₂ M₂) :
    K.comap (e : M →ₛₗ[τ₁₂] M₂) = K.map (e.symm : M₂ →ₛₗ[τ₂₁] M) :=
  (map_equiv_eq_comap_symm e.symm K).symm

theorem comap_le_comap_smul (fₗ : N →ₗ[R] N₂) (c : R) : comap fₗ qₗ ≤ comap (c • fₗ) qₗ := by
  rw [SetLike.le_def]
  intro m h
  change c • fₗ m ∈ qₗ
  change fₗ m ∈ qₗ at h
  apply qₗ.smul_mem _ h

theorem inf_comap_le_comap_add (f₁ f₂ : M →ₛₗ[τ₁₂] M₂) : comap f₁ q⊓comap f₂ q ≤ comap (f₁ + f₂) q := by
  rw [SetLike.le_def]
  intro m h
  change f₁ m + f₂ m ∈ q
  change f₁ m ∈ q ∧ f₂ m ∈ q at h
  apply q.add_mem h.1 h.2

/-- Given modules `M`, `M₂` over a commutative ring, together with submodules `p ⊆ M`, `q ⊆ M₂`,
the set of maps $\{f ∈ Hom(M, M₂) | f(p) ⊆ q \}$ is a submodule of `Hom(M, M₂)`. -/
def compatibleMaps : Submodule R (N →ₗ[R] N₂) where
  Carrier := { fₗ | pₗ ≤ comap fₗ qₗ }
  zero_mem' := by
    change pₗ ≤ comap 0 qₗ
    rw [comap_zero]
    refine' le_top
  add_mem' := fun f₁ f₂ h₁ h₂ => by
    apply le_transₓ _ (inf_comap_le_comap_add qₗ f₁ f₂)
    rw [le_inf_iff]
    exact ⟨h₁, h₂⟩
  smul_mem' := fun c fₗ h => le_transₓ h (comap_le_comap_smul qₗ fₗ c)

end Submodule

namespace Equivₓ

variable [Semiringₓ R] [AddCommMonoidₓ M] [Module R M] [AddCommMonoidₓ M₂] [Module R M₂]

/-- An equivalence whose underlying function is linear is a linear equivalence. -/
def toLinearEquiv (e : M ≃ M₂) (h : IsLinearMap R (e : M → M₂)) : M ≃ₗ[R] M₂ :=
  { e, h.mk' e with }

end Equivₓ

section FunLeft

variable (R M) [Semiringₓ R] [AddCommMonoidₓ M] [Module R M]

variable {m n p : Type _}

namespace LinearMap

/-- Given an `R`-module `M` and a function `m → n` between arbitrary types,
construct a linear map `(n → M) →ₗ[R] (m → M)` -/
def funLeft (f : m → n) : (n → M) →ₗ[R] m → M where
  toFun := (· ∘ f)
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl

@[simp]
theorem fun_left_apply (f : m → n) (g : n → M) (i : m) : funLeft R M f g i = g (f i) :=
  rfl

@[simp]
theorem fun_left_id (g : n → M) : funLeft R M id g = g :=
  rfl

theorem fun_left_comp (f₁ : n → p) (f₂ : m → n) : funLeft R M (f₁ ∘ f₂) = (funLeft R M f₂).comp (funLeft R M f₁) :=
  rfl

theorem fun_left_surjective_of_injective (f : m → n) (hf : Injective f) : Surjective (funLeft R M f) := by
  classical
  intro g
  refine' ⟨fun x => if h : ∃ y, f y = x then g h.some else 0, _⟩
  · ext
    dsimp' only [← fun_left_apply]
    split_ifs with w
    · congr
      exact hf w.some_spec
      
    · simpa only [← not_true, ← exists_apply_eq_applyₓ] using w
      
    

theorem fun_left_injective_of_surjective (f : m → n) (hf : Surjective f) : Injective (funLeft R M f) := by
  obtain ⟨g, hg⟩ := hf.has_right_inverse
  suffices left_inverse (fun_left R M g) (fun_left R M f) by
    exact this.injective
  intro x
  rw [← LinearMap.comp_apply, ← fun_left_comp, hg.id, fun_left_id]

end LinearMap

namespace LinearEquiv

open _Root_.LinearMap

/-- Given an `R`-module `M` and an equivalence `m ≃ n` between arbitrary types,
construct a linear equivalence `(n → M) ≃ₗ[R] (m → M)` -/
def funCongrLeft (e : m ≃ n) : (n → M) ≃ₗ[R] m → M :=
  LinearEquiv.ofLinear (funLeft R M e) (funLeft R M e.symm)
    (LinearMap.ext fun x =>
      funext fun i => by
        rw [id_apply, ← fun_left_comp, Equivₓ.symm_comp_self, fun_left_id])
    (LinearMap.ext fun x =>
      funext fun i => by
        rw [id_apply, ← fun_left_comp, Equivₓ.self_comp_symm, fun_left_id])

@[simp]
theorem fun_congr_left_apply (e : m ≃ n) (x : n → M) : funCongrLeft R M e x = funLeft R M e x :=
  rfl

@[simp]
theorem fun_congr_left_id : funCongrLeft R M (Equivₓ.refl n) = LinearEquiv.refl R (n → M) :=
  rfl

@[simp]
theorem fun_congr_left_comp (e₁ : m ≃ n) (e₂ : n ≃ p) :
    funCongrLeft R M (Equivₓ.trans e₁ e₂) = LinearEquiv.trans (funCongrLeft R M e₂) (funCongrLeft R M e₁) :=
  rfl

@[simp]
theorem fun_congr_left_symm (e : m ≃ n) : (funCongrLeft R M e).symm = funCongrLeft R M e.symm :=
  rfl

end LinearEquiv

end FunLeft

namespace LinearMap

variable [Semiringₓ R] [AddCommMonoidₓ M] [Module R M]

variable (R M)

/-- The group of invertible linear maps from `M` to itself -/
@[reducible]
def GeneralLinearGroup :=
  (M →ₗ[R] M)ˣ

namespace GeneralLinearGroup

variable {R M}

instance : CoeFun (GeneralLinearGroup R M) fun _ => M → M := by
  infer_instance

/-- An invertible linear map `f` determines an equivalence from `M` to itself. -/
def toLinearEquiv (f : GeneralLinearGroup R M) : M ≃ₗ[R] M :=
  { f.val with invFun := f.inv.toFun,
    left_inv := fun m =>
      show (f.inv * f.val) m = m by
        erw [f.inv_val] <;> simp ,
    right_inv := fun m =>
      show (f.val * f.inv) m = m by
        erw [f.val_inv] <;> simp }

/-- An equivalence from `M` to itself determines an invertible linear map. -/
def ofLinearEquiv (f : M ≃ₗ[R] M) : GeneralLinearGroup R M where
  val := f
  inv := (f.symm : M →ₗ[R] M)
  val_inv := LinearMap.ext fun _ => f.apply_symm_apply _
  inv_val := LinearMap.ext fun _ => f.symm_apply_apply _

variable (R M)

/-- The general linear group on `R` and `M` is multiplicatively equivalent to the type of linear
equivalences between `M` and itself. -/
def generalLinearEquiv : GeneralLinearGroup R M ≃* M ≃ₗ[R] M where
  toFun := toLinearEquiv
  invFun := ofLinearEquiv
  left_inv := fun f => by
    ext
    rfl
  right_inv := fun f => by
    ext
    rfl
  map_mul' := fun x y => by
    ext
    rfl

@[simp]
theorem general_linear_equiv_to_linear_map (f : GeneralLinearGroup R M) : (generalLinearEquiv R M f : M →ₗ[R] M) = f :=
  by
  ext
  rfl

@[simp]
theorem coe_fn_general_linear_equiv (f : GeneralLinearGroup R M) : ⇑(generalLinearEquiv R M f) = (f : M → M) :=
  rfl

end GeneralLinearGroup

end LinearMap

