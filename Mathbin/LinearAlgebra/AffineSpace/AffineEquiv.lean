/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import Mathbin.LinearAlgebra.AffineSpace.AffineMap
import Mathbin.Algebra.Invertible

/-!
# Affine equivalences

In this file we define `affine_equiv k P₁ P₂` (notation: `P₁ ≃ᵃ[k] P₂`) to be the type of affine
equivalences between `P₁` and `P₂, i.e., equivalences such that both forward and inverse maps are
affine maps.

We define the following equivalences:

* `affine_equiv.refl k P`: the identity map as an `affine_equiv`;

* `e.symm`: the inverse map of an `affine_equiv` as an `affine_equiv`;

* `e.trans e'`: composition of two `affine_equiv`s; note that the order follows `mathlib`'s
  `category_theory` convention (apply `e`, then `e'`), not the convention used in function
  composition and compositions of bundled morphisms.

We equip `affine_equiv k P P` with a `group` structure with multiplication corresponding to
composition in `affine_equiv.group`.

## Tags

affine space, affine equivalence
-/


open Function Set

open Affine

/-- An affine equivalence is an equivalence between affine spaces such that both forward
and inverse maps are affine.

We define it using an `equiv` for the map and a `linear_equiv` for the linear part in order
to allow affine equivalences with good definitional equalities. -/
@[nolint has_inhabited_instance]
structure AffineEquiv (k P₁ P₂ : Type _) {V₁ V₂ : Type _} [Ringₓ k] [AddCommGroupₓ V₁] [Module k V₁] [AddTorsor V₁ P₁]
  [AddCommGroupₓ V₂] [Module k V₂] [AddTorsor V₂ P₂] extends P₁ ≃ P₂ where
  linear : V₁ ≃ₗ[k] V₂
  map_vadd' : ∀ (p : P₁) (v : V₁), to_equiv (v +ᵥ p) = linear v +ᵥ to_equiv p

-- mathport name: «expr ≃ᵃ[ ] »
notation:25 P₁ " ≃ᵃ[" k:25 "] " P₂:0 => AffineEquiv k P₁ P₂

variable {k P₁ P₂ P₃ P₄ V₁ V₂ V₃ V₄ : Type _} [Ringₓ k] [AddCommGroupₓ V₁] [Module k V₁] [AddTorsor V₁ P₁]
  [AddCommGroupₓ V₂] [Module k V₂] [AddTorsor V₂ P₂] [AddCommGroupₓ V₃] [Module k V₃] [AddTorsor V₃ P₃]
  [AddCommGroupₓ V₄] [Module k V₄] [AddTorsor V₄ P₄]

namespace AffineEquiv

include V₁ V₂

instance : CoeFun (P₁ ≃ᵃ[k] P₂) fun _ => P₁ → P₂ :=
  ⟨fun e => e.toFun⟩

instance : Coe (P₁ ≃ᵃ[k] P₂) (P₁ ≃ P₂) :=
  ⟨AffineEquiv.toEquiv⟩

variable {k P₁}

@[simp]
theorem map_vadd (e : P₁ ≃ᵃ[k] P₂) (p : P₁) (v : V₁) : e (v +ᵥ p) = e.linear v +ᵥ e p :=
  e.map_vadd' p v

@[simp]
theorem coe_to_equiv (e : P₁ ≃ᵃ[k] P₂) : ⇑e.toEquiv = e :=
  rfl

/-- Reinterpret an `affine_equiv` as an `affine_map`. -/
def toAffineMap (e : P₁ ≃ᵃ[k] P₂) : P₁ →ᵃ[k] P₂ :=
  { e with toFun := e }

instance : Coe (P₁ ≃ᵃ[k] P₂) (P₁ →ᵃ[k] P₂) :=
  ⟨toAffineMap⟩

@[simp]
theorem coe_to_affine_map (e : P₁ ≃ᵃ[k] P₂) : (e.toAffineMap : P₁ → P₂) = (e : P₁ → P₂) :=
  rfl

@[simp]
theorem to_affine_map_mk (f : P₁ ≃ P₂) (f' : V₁ ≃ₗ[k] V₂) (h) : toAffineMap (mk f f' h) = ⟨f, f', h⟩ :=
  rfl

@[norm_cast, simp]
theorem coe_coe (e : P₁ ≃ᵃ[k] P₂) : ((e : P₁ →ᵃ[k] P₂) : P₁ → P₂) = e :=
  rfl

@[simp]
theorem linear_to_affine_map (e : P₁ ≃ᵃ[k] P₂) : e.toAffineMap.linear = e.linear :=
  rfl

theorem to_affine_map_injective : Injective (toAffineMap : (P₁ ≃ᵃ[k] P₂) → P₁ →ᵃ[k] P₂) := by
  rintro ⟨e, el, h⟩ ⟨e', el', h'⟩ H
  simp only [← to_affine_map_mk, ← Equivₓ.coe_inj, ← LinearEquiv.to_linear_map_inj] at H
  congr
  exacts[H.1, H.2]

@[simp]
theorem to_affine_map_inj {e e' : P₁ ≃ᵃ[k] P₂} : e.toAffineMap = e'.toAffineMap ↔ e = e' :=
  to_affine_map_injective.eq_iff

@[ext]
theorem ext {e e' : P₁ ≃ᵃ[k] P₂} (h : ∀ x, e x = e' x) : e = e' :=
  to_affine_map_injective <| AffineMap.ext h

theorem coe_fn_injective : @Injective (P₁ ≃ᵃ[k] P₂) (P₁ → P₂) coeFn := fun e e' H => ext <| congr_fun H

@[simp, norm_cast]
theorem coe_fn_inj {e e' : P₁ ≃ᵃ[k] P₂} : (e : P₁ → P₂) = e' ↔ e = e' :=
  coe_fn_injective.eq_iff

theorem to_equiv_injective : Injective (toEquiv : (P₁ ≃ᵃ[k] P₂) → P₁ ≃ P₂) := fun e e' H => ext <| Equivₓ.ext_iff.1 H

@[simp]
theorem to_equiv_inj {e e' : P₁ ≃ᵃ[k] P₂} : e.toEquiv = e'.toEquiv ↔ e = e' :=
  to_equiv_injective.eq_iff

@[simp]
theorem coe_mk (e : P₁ ≃ P₂) (e' : V₁ ≃ₗ[k] V₂) (h) : ((⟨e, e', h⟩ : P₁ ≃ᵃ[k] P₂) : P₁ → P₂) = e :=
  rfl

/-- Construct an affine equivalence by verifying the relation between the map and its linear part at
one base point. Namely, this function takes a map `e : P₁ → P₂`, a linear equivalence
`e' : V₁ ≃ₗ[k] V₂`, and a point `p` such that for any other point `p'` we have
`e p' = e' (p' -ᵥ p) +ᵥ e p`. -/
def mk' (e : P₁ → P₂) (e' : V₁ ≃ₗ[k] V₂) (p : P₁) (h : ∀ p' : P₁, e p' = e' (p' -ᵥ p) +ᵥ e p) : P₁ ≃ᵃ[k] P₂ where
  toFun := e
  invFun := fun q' : P₂ => e'.symm (q' -ᵥ e p) +ᵥ p
  left_inv := fun p' => by
    simp [← h p']
  right_inv := fun q' => by
    simp [← h (e'.symm (q' -ᵥ e p) +ᵥ p)]
  linear := e'
  map_vadd' := fun p' v => by
    simp [← h p', ← h (v +ᵥ p'), ← vadd_vsub_assoc, ← vadd_vadd]

@[simp]
theorem coe_mk' (e : P₁ ≃ P₂) (e' : V₁ ≃ₗ[k] V₂) (p h) : ⇑(mk' e e' p h) = e :=
  rfl

@[simp]
theorem linear_mk' (e : P₁ ≃ P₂) (e' : V₁ ≃ₗ[k] V₂) (p h) : (mk' e e' p h).linear = e' :=
  rfl

/-- Inverse of an affine equivalence as an affine equivalence. -/
@[symm]
def symm (e : P₁ ≃ᵃ[k] P₂) : P₂ ≃ᵃ[k] P₁ where
  toEquiv := e.toEquiv.symm
  linear := e.linear.symm
  map_vadd' := fun v p =>
    e.toEquiv.symm.apply_eq_iff_eq_symm_apply.2 <| by
      simpa using (e.to_equiv.apply_symm_apply v).symm

@[simp]
theorem symm_to_equiv (e : P₁ ≃ᵃ[k] P₂) : e.toEquiv.symm = e.symm.toEquiv :=
  rfl

@[simp]
theorem symm_linear (e : P₁ ≃ᵃ[k] P₂) : e.linear.symm = e.symm.linear :=
  rfl

/-- See Note [custom simps projection] -/
def Simps.apply (e : P₁ ≃ᵃ[k] P₂) : P₁ → P₂ :=
  e

/-- See Note [custom simps projection] -/
def Simps.symmApply (e : P₁ ≃ᵃ[k] P₂) : P₂ → P₁ :=
  e.symm

initialize_simps_projections AffineEquiv (to_equiv_to_fun → apply, to_equiv_inv_fun → symmApply, linear →
  linear as_prefix, -toEquiv)

protected theorem bijective (e : P₁ ≃ᵃ[k] P₂) : Bijective e :=
  e.toEquiv.Bijective

protected theorem surjective (e : P₁ ≃ᵃ[k] P₂) : Surjective e :=
  e.toEquiv.Surjective

protected theorem injective (e : P₁ ≃ᵃ[k] P₂) : Injective e :=
  e.toEquiv.Injective

@[simp]
theorem range_eq (e : P₁ ≃ᵃ[k] P₂) : Range e = univ :=
  e.Surjective.range_eq

@[simp]
theorem apply_symm_apply (e : P₁ ≃ᵃ[k] P₂) (p : P₂) : e (e.symm p) = p :=
  e.toEquiv.apply_symm_apply p

@[simp]
theorem symm_apply_apply (e : P₁ ≃ᵃ[k] P₂) (p : P₁) : e.symm (e p) = p :=
  e.toEquiv.symm_apply_apply p

theorem apply_eq_iff_eq_symm_apply (e : P₁ ≃ᵃ[k] P₂) {p₁ p₂} : e p₁ = p₂ ↔ p₁ = e.symm p₂ :=
  e.toEquiv.apply_eq_iff_eq_symm_apply

@[simp]
theorem apply_eq_iff_eq (e : P₁ ≃ᵃ[k] P₂) {p₁ p₂ : P₁} : e p₁ = e p₂ ↔ p₁ = p₂ :=
  e.toEquiv.apply_eq_iff_eq

variable (k P₁)

omit V₂

/-- Identity map as an `affine_equiv`. -/
@[refl]
def refl : P₁ ≃ᵃ[k] P₁ where
  toEquiv := Equivₓ.refl P₁
  linear := LinearEquiv.refl k V₁
  map_vadd' := fun _ _ => rfl

@[simp]
theorem coe_refl : ⇑(refl k P₁) = id :=
  rfl

@[simp]
theorem coe_refl_to_affine_map : ↑(refl k P₁) = AffineMap.id k P₁ :=
  rfl

@[simp]
theorem refl_apply (x : P₁) : refl k P₁ x = x :=
  rfl

@[simp]
theorem to_equiv_refl : (refl k P₁).toEquiv = Equivₓ.refl P₁ :=
  rfl

@[simp]
theorem linear_refl : (refl k P₁).linear = LinearEquiv.refl k V₁ :=
  rfl

@[simp]
theorem symm_refl : (refl k P₁).symm = refl k P₁ :=
  rfl

variable {k P₁}

include V₂ V₃

/-- Composition of two `affine_equiv`alences, applied left to right. -/
@[trans]
def trans (e : P₁ ≃ᵃ[k] P₂) (e' : P₂ ≃ᵃ[k] P₃) : P₁ ≃ᵃ[k] P₃ where
  toEquiv := e.toEquiv.trans e'.toEquiv
  linear := e.linear.trans e'.linear
  map_vadd' := fun p v => by
    simp only [← LinearEquiv.trans_apply, ← coe_to_equiv, ← (· ∘ ·), ← Equivₓ.coe_trans, ← map_vadd]

@[simp]
theorem coe_trans (e : P₁ ≃ᵃ[k] P₂) (e' : P₂ ≃ᵃ[k] P₃) : ⇑(e.trans e') = e' ∘ e :=
  rfl

@[simp]
theorem trans_apply (e : P₁ ≃ᵃ[k] P₂) (e' : P₂ ≃ᵃ[k] P₃) (p : P₁) : e.trans e' p = e' (e p) :=
  rfl

include V₄

theorem trans_assoc (e₁ : P₁ ≃ᵃ[k] P₂) (e₂ : P₂ ≃ᵃ[k] P₃) (e₃ : P₃ ≃ᵃ[k] P₄) :
    (e₁.trans e₂).trans e₃ = e₁.trans (e₂.trans e₃) :=
  ext fun _ => rfl

omit V₃ V₄

@[simp]
theorem trans_refl (e : P₁ ≃ᵃ[k] P₂) : e.trans (refl k P₂) = e :=
  ext fun _ => rfl

@[simp]
theorem refl_trans (e : P₁ ≃ᵃ[k] P₂) : (refl k P₁).trans e = e :=
  ext fun _ => rfl

@[simp]
theorem self_trans_symm (e : P₁ ≃ᵃ[k] P₂) : e.trans e.symm = refl k P₁ :=
  ext e.symm_apply_apply

@[simp]
theorem symm_trans_self (e : P₁ ≃ᵃ[k] P₂) : e.symm.trans e = refl k P₂ :=
  ext e.apply_symm_apply

@[simp]
theorem apply_line_map (e : P₁ ≃ᵃ[k] P₂) (a b : P₁) (c : k) :
    e (AffineMap.lineMap a b c) = AffineMap.lineMap (e a) (e b) c :=
  e.toAffineMap.apply_line_map a b c

omit V₂

instance : Groupₓ (P₁ ≃ᵃ[k] P₁) where
  one := refl k P₁
  mul := fun e e' => e'.trans e
  inv := symm
  mul_assoc := fun e₁ e₂ e₃ => trans_assoc _ _ _
  one_mul := trans_refl
  mul_one := refl_trans
  mul_left_inv := self_trans_symm

theorem one_def : (1 : P₁ ≃ᵃ[k] P₁) = refl k P₁ :=
  rfl

@[simp]
theorem coe_one : ⇑(1 : P₁ ≃ᵃ[k] P₁) = id :=
  rfl

theorem mul_def (e e' : P₁ ≃ᵃ[k] P₁) : e * e' = e'.trans e :=
  rfl

@[simp]
theorem coe_mul (e e' : P₁ ≃ᵃ[k] P₁) : ⇑(e * e') = e ∘ e' :=
  rfl

theorem inv_def (e : P₁ ≃ᵃ[k] P₁) : e⁻¹ = e.symm :=
  rfl

/-- `affine_equiv.linear` on automorphisms is a `monoid_hom`. -/
@[simps]
def linearHom : (P₁ ≃ᵃ[k] P₁) →* V₁ ≃ₗ[k] V₁ where
  toFun := linear
  map_one' := rfl
  map_mul' := fun _ _ => rfl

/-- The group of `affine_equiv`s are equivalent to the group of units of `affine_map`.

This is the affine version of `linear_map.general_linear_group.general_linear_equiv`. -/
@[simps]
def equivUnitsAffineMap : (P₁ ≃ᵃ[k] P₁) ≃* (P₁ →ᵃ[k] P₁)ˣ where
  toFun := fun e => ⟨e, e.symm, congr_arg coe e.symm_trans_self, congr_arg coe e.self_trans_symm⟩
  invFun := fun u =>
    { toFun := (u : P₁ →ᵃ[k] P₁), invFun := (↑u⁻¹ : P₁ →ᵃ[k] P₁), left_inv := AffineMap.congr_fun u.inv_mul,
      right_inv := AffineMap.congr_fun u.mul_inv,
      linear := LinearMap.GeneralLinearGroup.generalLinearEquiv _ _ <| Units.map AffineMap.linearHom u,
      map_vadd' := fun _ _ => (u : P₁ →ᵃ[k] P₁).map_vadd _ _ }
  left_inv := fun e => AffineEquiv.ext fun x => rfl
  right_inv := fun u => Units.ext <| AffineMap.ext fun x => rfl
  map_mul' := fun e₁ e₂ => rfl

variable (k)

/-- The map `v ↦ v +ᵥ b` as an affine equivalence between a module `V` and an affine space `P` with
tangent space `V`. -/
@[simps]
def vaddConst (b : P₁) : V₁ ≃ᵃ[k] P₁ where
  toEquiv := Equivₓ.vaddConst b
  linear := LinearEquiv.refl _ _
  map_vadd' := fun p v => add_vadd _ _ _

/-- `p' ↦ p -ᵥ p'` as an equivalence. -/
def constVsub (p : P₁) : P₁ ≃ᵃ[k] V₁ where
  toEquiv := Equivₓ.constVsub p
  linear := LinearEquiv.neg k
  map_vadd' := fun p' v => by
    simp [← vsub_vadd_eq_vsub_sub, ← neg_add_eq_sub]

@[simp]
theorem coe_const_vsub (p : P₁) : ⇑(constVsub k p) = (· -ᵥ ·) p :=
  rfl

@[simp]
theorem coe_const_vsub_symm (p : P₁) : ⇑(constVsub k p).symm = fun v => -v +ᵥ p :=
  rfl

variable (P₁)

/-- The map `p ↦ v +ᵥ p` as an affine automorphism of an affine space.

Note that there is no need for an `affine_map.const_vadd` as it is always an equivalence.
This is roughly to `distrib_mul_action.to_linear_equiv` as `+ᵥ` is to `•`. -/
@[simps apply linear]
def constVadd (v : V₁) : P₁ ≃ᵃ[k] P₁ where
  toEquiv := Equivₓ.constVadd P₁ v
  linear := LinearEquiv.refl _ _
  map_vadd' := fun p w => vadd_comm _ _ _

@[simp]
theorem const_vadd_zero : constVadd k P₁ 0 = AffineEquiv.refl _ _ :=
  ext <| zero_vadd _

@[simp]
theorem const_vadd_add (v w : V₁) : constVadd k P₁ (v + w) = (constVadd k P₁ w).trans (constVadd k P₁ v) :=
  ext <| add_vadd _ _

@[simp]
theorem const_vadd_symm (v : V₁) : (constVadd k P₁ v).symm = constVadd k P₁ (-v) :=
  ext fun _ => rfl

/-- A more bundled version of `affine_equiv.const_vadd`. -/
@[simps]
def constVaddHom : Multiplicative V₁ →* P₁ ≃ᵃ[k] P₁ where
  toFun := fun v => constVadd k P₁ v.toAdd
  map_one' := const_vadd_zero _ _
  map_mul' := const_vadd_add _ _

theorem const_vadd_nsmul (n : ℕ) (v : V₁) : constVadd k P₁ (n • v) = constVadd k P₁ v ^ n :=
  (constVaddHom k P₁).map_pow _ _

theorem const_vadd_zsmul (z : ℤ) (v : V₁) : constVadd k P₁ (z • v) = constVadd k P₁ v ^ z :=
  (constVaddHom k P₁).map_zpow _ _

section Homothety

omit V₁

variable {R V P : Type _} [CommRingₓ R] [AddCommGroupₓ V] [Module R V] [affine_space V P]

include V

/-- Fixing a point in affine space, homothety about this point gives a group homomorphism from (the
centre of) the units of the scalars into the group of affine equivalences. -/
def homothetyUnitsMulHom (p : P) : Rˣ →* P ≃ᵃ[R] P :=
  equivUnitsAffineMap.symm.toMonoidHom.comp <| Units.map (AffineMap.homothetyHom p)

@[simp]
theorem coe_homothety_units_mul_hom_apply (p : P) (t : Rˣ) :
    (homothetyUnitsMulHom p t : P → P) = AffineMap.homothety p (t : R) :=
  rfl

@[simp]
theorem coe_homothety_units_mul_hom_apply_symm (p : P) (t : Rˣ) :
    ((homothetyUnitsMulHom p t).symm : P → P) = AffineMap.homothety p (↑t⁻¹ : R) :=
  rfl

@[simp]
theorem coe_homothety_units_mul_hom_eq_homothety_hom_coe (p : P) :
    (coe : (P ≃ᵃ[R] P) → P →ᵃ[R] P) ∘ homothetyUnitsMulHom p = AffineMap.homothetyHom p ∘ (coe : Rˣ → R) :=
  funext fun _ => rfl

end Homothety

variable {P₁}

open Function

/-- Point reflection in `x` as a permutation. -/
def pointReflection (x : P₁) : P₁ ≃ᵃ[k] P₁ :=
  (constVsub k x).trans (vaddConst k x)

theorem point_reflection_apply (x y : P₁) : pointReflection k x y = x -ᵥ y +ᵥ x :=
  rfl

@[simp]
theorem point_reflection_symm (x : P₁) : (pointReflection k x).symm = pointReflection k x :=
  to_equiv_injective <| Equivₓ.point_reflection_symm x

@[simp]
theorem to_equiv_point_reflection (x : P₁) : (pointReflection k x).toEquiv = Equivₓ.pointReflection x :=
  rfl

@[simp]
theorem point_reflection_self (x : P₁) : pointReflection k x x = x :=
  vsub_vadd _ _

theorem point_reflection_involutive (x : P₁) : Involutive (pointReflection k x : P₁ → P₁) :=
  Equivₓ.point_reflection_involutive x

/-- `x` is the only fixed point of `point_reflection x`. This lemma requires
`x + x = y + y ↔ x = y`. There is no typeclass to use here, so we add it as an explicit argument. -/
theorem point_reflection_fixed_iff_of_injective_bit0 {x y : P₁} (h : Injective (bit0 : V₁ → V₁)) :
    pointReflection k x y = y ↔ y = x :=
  Equivₓ.point_reflection_fixed_iff_of_injective_bit0 h

theorem injective_point_reflection_left_of_injective_bit0 (h : Injective (bit0 : V₁ → V₁)) (y : P₁) :
    Injective fun x : P₁ => pointReflection k x y :=
  Equivₓ.injective_point_reflection_left_of_injective_bit0 h y

theorem injective_point_reflection_left_of_module [Invertible (2 : k)] :
    ∀ y, Injective fun x : P₁ => pointReflection k x y :=
  (injective_point_reflection_left_of_injective_bit0 k) fun x y h => by
    rwa [bit0, bit0, ← two_smul k x, ← two_smul k y, (is_unit_of_invertible (2 : k)).smul_left_cancel] at h

theorem point_reflection_fixed_iff_of_module [Invertible (2 : k)] {x y : P₁} : pointReflection k x y = y ↔ y = x :=
  ((injective_point_reflection_left_of_module k y).eq_iff' (point_reflection_self k y)).trans eq_comm

end AffineEquiv

namespace LinearEquiv

/-- Interpret a linear equivalence between modules as an affine equivalence. -/
def toAffineEquiv (e : V₁ ≃ₗ[k] V₂) : V₁ ≃ᵃ[k] V₂ where
  toEquiv := e.toEquiv
  linear := e
  map_vadd' := fun p v => e.map_add v p

@[simp]
theorem coe_to_affine_equiv (e : V₁ ≃ₗ[k] V₂) : ⇑e.toAffineEquiv = e :=
  rfl

end LinearEquiv

namespace AffineMap

open AffineEquiv

include V₁

theorem line_map_vadd (v v' : V₁) (p : P₁) (c : k) : lineMap v v' c +ᵥ p = lineMap (v +ᵥ p) (v' +ᵥ p) c :=
  (vaddConst k p).apply_line_map v v' c

theorem line_map_vsub (p₁ p₂ p₃ : P₁) (c : k) : lineMap p₁ p₂ c -ᵥ p₃ = lineMap (p₁ -ᵥ p₃) (p₂ -ᵥ p₃) c :=
  (vaddConst k p₃).symm.apply_line_map p₁ p₂ c

theorem vsub_line_map (p₁ p₂ p₃ : P₁) (c : k) : p₁ -ᵥ lineMap p₂ p₃ c = lineMap (p₁ -ᵥ p₂) (p₁ -ᵥ p₃) c :=
  (constVsub k p₁).apply_line_map p₂ p₃ c

theorem vadd_line_map (v : V₁) (p₁ p₂ : P₁) (c : k) : v +ᵥ lineMap p₁ p₂ c = lineMap (v +ᵥ p₁) (v +ᵥ p₂) c :=
  (constVadd k P₁ v).apply_line_map p₁ p₂ c

variable {R' : Type _} [CommRingₓ R'] [Module R' V₁]

theorem homothety_neg_one_apply (c p : P₁) : homothety c (-1 : R') p = pointReflection R' c p := by
  simp [← homothety_apply, ← point_reflection_apply]

end AffineMap

