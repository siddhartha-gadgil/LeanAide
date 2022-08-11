/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathbin.Algebra.Algebra.Basic
import Mathbin.Topology.LocallyConstant.Basic

/-!
# Algebraic structure on locally constant functions

This file puts algebraic structure (`add_group`, etc)
on the type of locally constant functions.

-/


namespace LocallyConstant

variable {X Y : Type _} [TopologicalSpace X]

@[to_additive]
instance [One Y] : One (LocallyConstant X Y) where one := const X 1

@[simp, to_additive]
theorem coe_one [One Y] : ⇑(1 : LocallyConstant X Y) = (1 : X → Y) :=
  rfl

@[to_additive]
theorem one_apply [One Y] (x : X) : (1 : LocallyConstant X Y) x = 1 :=
  rfl

@[to_additive]
instance [Inv Y] : Inv (LocallyConstant X Y) where inv := fun f => ⟨f⁻¹, f.IsLocallyConstant.inv⟩

@[simp, to_additive]
theorem coe_inv [Inv Y] (f : LocallyConstant X Y) : ⇑f⁻¹ = f⁻¹ :=
  rfl

@[to_additive]
theorem inv_apply [Inv Y] (f : LocallyConstant X Y) (x : X) : f⁻¹ x = (f x)⁻¹ :=
  rfl

@[to_additive]
instance [Mul Y] :
    Mul (LocallyConstant X Y) where mul := fun f g => ⟨f * g, f.IsLocallyConstant.mul g.IsLocallyConstant⟩

@[simp, to_additive]
theorem coe_mul [Mul Y] (f g : LocallyConstant X Y) : ⇑(f * g) = f * g :=
  rfl

@[to_additive]
theorem mul_apply [Mul Y] (f g : LocallyConstant X Y) (x : X) : (f * g) x = f x * g x :=
  rfl

@[to_additive]
instance [MulOneClassₓ Y] : MulOneClassₓ (LocallyConstant X Y) :=
  { LocallyConstant.hasOne, LocallyConstant.hasMul with
    one_mul := by
      intros
      ext
      simp only [← mul_apply, ← one_apply, ← one_mulₓ],
    mul_one := by
      intros
      ext
      simp only [← mul_apply, ← one_apply, ← mul_oneₓ] }

/-- `coe_fn` is a `monoid_hom`. -/
@[to_additive "`coe_fn` is an `add_monoid_hom`.", simps]
def coeFnMonoidHom [MulOneClassₓ Y] : LocallyConstant X Y →* X → Y where
  toFun := coeFn
  map_one' := rfl
  map_mul' := fun _ _ => rfl

/-- The constant-function embedding, as a multiplicative monoid hom. -/
@[to_additive "The constant-function embedding, as an additive monoid hom.", simps]
def constMonoidHom [MulOneClassₓ Y] : Y →* LocallyConstant X Y where
  toFun := const X
  map_one' := rfl
  map_mul' := fun _ _ => rfl

instance [MulZeroClassₓ Y] : MulZeroClassₓ (LocallyConstant X Y) :=
  { LocallyConstant.hasZero, LocallyConstant.hasMul with
    zero_mul := by
      intros
      ext
      simp only [← mul_apply, ← zero_apply, ← zero_mul],
    mul_zero := by
      intros
      ext
      simp only [← mul_apply, ← zero_apply, ← mul_zero] }

instance [MulZeroOneClassₓ Y] : MulZeroOneClassₓ (LocallyConstant X Y) :=
  { LocallyConstant.mulZeroClass, LocallyConstant.mulOneClass with }

section CharFn

variable (Y) [MulZeroOneClassₓ Y] {U V : Set X}

/-- Characteristic functions are locally constant functions taking `x : X` to `1` if `x ∈ U`,
  where `U` is a clopen set, and `0` otherwise. -/
noncomputable def charFn (hU : IsClopen U) : LocallyConstant X Y :=
  indicator 1 hU

theorem coe_char_fn (hU : IsClopen U) : (charFn Y hU : X → Y) = Set.indicatorₓ U 1 :=
  rfl

theorem char_fn_eq_one [Nontrivial Y] (x : X) (hU : IsClopen U) : charFn Y hU x = (1 : Y) ↔ x ∈ U :=
  Set.indicator_eq_one_iff_mem _

theorem char_fn_eq_zero [Nontrivial Y] (x : X) (hU : IsClopen U) : charFn Y hU x = (0 : Y) ↔ x ∉ U :=
  Set.indicator_eq_zero_iff_not_mem _

theorem char_fn_inj [Nontrivial Y] (hU : IsClopen U) (hV : IsClopen V) (h : charFn Y hU = charFn Y hV) : U = V :=
  Set.indicator_one_inj Y <| coe_inj.mpr h

end CharFn

@[to_additive]
instance [Div Y] :
    Div (LocallyConstant X Y) where div := fun f g => ⟨f / g, f.IsLocallyConstant.div g.IsLocallyConstant⟩

@[to_additive]
theorem coe_div [Div Y] (f g : LocallyConstant X Y) : ⇑(f / g) = f / g :=
  rfl

@[to_additive]
theorem div_apply [Div Y] (f g : LocallyConstant X Y) (x : X) : (f / g) x = f x / g x :=
  rfl

@[to_additive]
instance [Semigroupₓ Y] : Semigroupₓ (LocallyConstant X Y) :=
  { LocallyConstant.hasMul with
    mul_assoc := by
      intros
      ext
      simp only [← mul_apply, ← mul_assoc] }

instance [SemigroupWithZeroₓ Y] : SemigroupWithZeroₓ (LocallyConstant X Y) :=
  { LocallyConstant.mulZeroClass, LocallyConstant.semigroup with }

@[to_additive]
instance [CommSemigroupₓ Y] : CommSemigroupₓ (LocallyConstant X Y) :=
  { LocallyConstant.semigroup with
    mul_comm := by
      intros
      ext
      simp only [← mul_apply, ← mul_comm] }

@[to_additive]
instance [Monoidₓ Y] : Monoidₓ (LocallyConstant X Y) :=
  { LocallyConstant.semigroup, LocallyConstant.mulOneClass with mul := (· * ·) }

instance [AddMonoidWithOneₓ Y] : AddMonoidWithOneₓ (LocallyConstant X Y) :=
  { LocallyConstant.addMonoid, LocallyConstant.hasOne with natCast := fun n => const X n,
    nat_cast_zero := by
      ext <;> simp [← Nat.castₓ],
    nat_cast_succ := fun _ => by
      ext <;> simp [← Nat.castₓ] }

@[to_additive]
instance [CommMonoidₓ Y] : CommMonoidₓ (LocallyConstant X Y) :=
  { LocallyConstant.commSemigroup, LocallyConstant.monoid with }

@[to_additive]
instance [Groupₓ Y] : Groupₓ (LocallyConstant X Y) :=
  { LocallyConstant.monoid, LocallyConstant.hasInv, LocallyConstant.hasDiv with
    mul_left_inv := by
      intros
      ext
      simp only [← mul_apply, ← inv_apply, ← one_apply, ← mul_left_invₓ],
    div_eq_mul_inv := by
      intros
      ext
      simp only [← mul_apply, ← inv_apply, ← div_apply, ← div_eq_mul_inv] }

@[to_additive]
instance [CommGroupₓ Y] : CommGroupₓ (LocallyConstant X Y) :=
  { LocallyConstant.commMonoid, LocallyConstant.group with }

instance [Distribₓ Y] : Distribₓ (LocallyConstant X Y) :=
  { LocallyConstant.hasAdd, LocallyConstant.hasMul with
    left_distrib := by
      intros
      ext
      simp only [← mul_apply, ← add_apply, ← mul_addₓ],
    right_distrib := by
      intros
      ext
      simp only [← mul_apply, ← add_apply, ← add_mulₓ] }

instance [NonUnitalNonAssocSemiringₓ Y] : NonUnitalNonAssocSemiringₓ (LocallyConstant X Y) :=
  { LocallyConstant.addCommMonoid, LocallyConstant.hasMul, LocallyConstant.distrib, LocallyConstant.mulZeroClass with }

instance [NonUnitalSemiringₓ Y] : NonUnitalSemiringₓ (LocallyConstant X Y) :=
  { LocallyConstant.semigroup, LocallyConstant.nonUnitalNonAssocSemiring with }

instance [NonAssocSemiringₓ Y] : NonAssocSemiringₓ (LocallyConstant X Y) :=
  { LocallyConstant.mulOneClass, LocallyConstant.addMonoidWithOne, LocallyConstant.nonUnitalNonAssocSemiring with }

/-- The constant-function embedding, as a ring hom.  -/
@[simps]
def constRingHom [NonAssocSemiringₓ Y] : Y →+* LocallyConstant X Y :=
  { constMonoidHom, constAddMonoidHom with toFun := const X }

instance [Semiringₓ Y] : Semiringₓ (LocallyConstant X Y) :=
  { LocallyConstant.nonAssocSemiring, LocallyConstant.monoid with }

instance [NonUnitalCommSemiring Y] : NonUnitalCommSemiring (LocallyConstant X Y) :=
  { LocallyConstant.nonUnitalSemiring, LocallyConstant.commSemigroup with }

instance [CommSemiringₓ Y] : CommSemiringₓ (LocallyConstant X Y) :=
  { LocallyConstant.semiring, LocallyConstant.commMonoid with }

instance [NonUnitalNonAssocRing Y] : NonUnitalNonAssocRing (LocallyConstant X Y) :=
  { LocallyConstant.addCommGroup, LocallyConstant.hasMul, LocallyConstant.distrib, LocallyConstant.mulZeroClass with }

instance [NonUnitalRing Y] : NonUnitalRing (LocallyConstant X Y) :=
  { LocallyConstant.semigroup, LocallyConstant.nonUnitalNonAssocRing with }

instance [NonAssocRing Y] : NonAssocRing (LocallyConstant X Y) :=
  { LocallyConstant.mulOneClass, LocallyConstant.nonUnitalNonAssocRing with }

instance [Ringₓ Y] : Ringₓ (LocallyConstant X Y) :=
  { LocallyConstant.semiring, LocallyConstant.addCommGroup with }

instance [NonUnitalCommRing Y] : NonUnitalCommRing (LocallyConstant X Y) :=
  { LocallyConstant.nonUnitalCommSemiring, LocallyConstant.nonUnitalRing with }

instance [CommRingₓ Y] : CommRingₓ (LocallyConstant X Y) :=
  { LocallyConstant.commSemiring, LocallyConstant.ring with }

variable {R : Type _}

instance [HasSmul R Y] :
    HasSmul R
      (LocallyConstant X
        Y) where smul := fun r f =>
    { toFun := r • f, IsLocallyConstant := ((is_locally_constant f).comp ((· • ·) r) : _) }

@[simp]
theorem coe_smul [HasSmul R Y] (r : R) (f : LocallyConstant X Y) : ⇑(r • f) = r • f :=
  rfl

theorem smul_apply [HasSmul R Y] (r : R) (f : LocallyConstant X Y) (x : X) : (r • f) x = r • f x :=
  rfl

instance [Monoidₓ R] [MulAction R Y] : MulAction R (LocallyConstant X Y) :=
  Function.Injective.mulAction _ coe_injective fun _ _ => rfl

instance [Monoidₓ R] [AddMonoidₓ Y] [DistribMulAction R Y] : DistribMulAction R (LocallyConstant X Y) :=
  Function.Injective.distribMulAction coeFnAddMonoidHom coe_injective fun _ _ => rfl

instance [Semiringₓ R] [AddCommMonoidₓ Y] [Module R Y] : Module R (LocallyConstant X Y) :=
  Function.Injective.module R coeFnAddMonoidHom coe_injective fun _ _ => rfl

section Algebra

variable [CommSemiringₓ R] [Semiringₓ Y] [Algebra R Y]

instance : Algebra R (LocallyConstant X Y) where
  toRingHom := constRingHom.comp <| algebraMap R Y
  commutes' := by
    intros
    ext
    exact Algebra.commutes' _ _
  smul_def' := by
    intros
    ext
    exact Algebra.smul_def' _ _

@[simp]
theorem coe_algebra_map (r : R) : ⇑(algebraMap R (LocallyConstant X Y) r) = algebraMap R (X → Y) r :=
  rfl

end Algebra

end LocallyConstant

