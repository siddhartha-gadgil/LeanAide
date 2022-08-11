/-
Copyright (c) 2021 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
import Mathbin.Algebra.Star.Basic
import Mathbin.GroupTheory.Subgroup.Basic

/-!
# Self-adjoint, skew-adjoint and normal elements of a star additive group

This file defines `self_adjoint R` (resp. `skew_adjoint R`), where `R` is a star additive group,
as the additive subgroup containing the elements that satisfy `star x = x` (resp. `star x = -x`).
This includes, for instance, (skew-)Hermitian operators on Hilbert spaces.

We also define `is_star_normal R`, a `Prop` that states that an element `x` satisfies
`star x * x = x * star x`.

## Implementation notes

* When `R` is a `star_module R₂ R`, then `self_adjoint R` has a natural
  `module (self_adjoint R₂) (self_adjoint R)` structure. However, doing this literally would be
  undesirable since in the main case of interest (`R₂ = ℂ`) we want `module ℝ (self_adjoint R)`
  and not `module (self_adjoint ℂ) (self_adjoint R)`. We solve this issue by adding the typeclass
  `[has_trivial_star R₃]`, of which `ℝ` is an instance (registered in `data/real/basic`), and then
  add a `[module R₃ (self_adjoint R)]` instance whenever we have
  `[module R₃ R] [has_trivial_star R₃]`. (Another approach would have been to define
  `[star_invariant_scalars R₃ R]` to express the fact that `star (x • v) = x • star v`, but
  this typeclass would have the disadvantage of taking two type arguments.)

## TODO

* Define `λ z x, z * x * star z` (i.e. conjugation by `z`) as a monoid action of `R` on `R`
  (similar to the existing `conj_act` for groups), and then state the fact that `self_adjoint R` is
  invariant under it.

-/


variable (R : Type _) {A : Type _}

/-- The self-adjoint elements of a star additive group, as an additive subgroup. -/
def selfAdjoint [AddGroupₓ R] [StarAddMonoid R] : AddSubgroup R where
  Carrier := { x | star x = x }
  zero_mem' := star_zero R
  add_mem' := fun x y (hx : star x = x) (hy : star y = y) =>
    show star (x + y) = x + y by
      simp only [← star_add x y, ← hx, ← hy]
  neg_mem' := fun x (hx : star x = x) =>
    show star (-x) = -x by
      simp only [← hx, ← star_neg]

/-- The skew-adjoint elements of a star additive group, as an additive subgroup. -/
def skewAdjoint [AddCommGroupₓ R] [StarAddMonoid R] : AddSubgroup R where
  Carrier := { x | star x = -x }
  zero_mem' :=
    show star (0 : R) = -0 by
      simp only [← star_zero, ← neg_zero]
  add_mem' := fun x y (hx : star x = -x) (hy : star y = -y) =>
    show star (x + y) = -(x + y) by
      rw [star_add x y, hx, hy, neg_add]
  neg_mem' := fun x (hx : star x = -x) =>
    show star (-x) = - -x by
      simp only [← hx, ← star_neg]

variable {R}

/-- An element of a star monoid is normal if it commutes with its adjoint. -/
class IsStarNormal [Mul R] [HasStar R] (x : R) : Prop where
  star_comm_self : Commute (star x) x

export IsStarNormal (star_comm_self)

theorem star_comm_self' [Mul R] [HasStar R] (x : R) [IsStarNormal x] : star x * x = x * star x :=
  IsStarNormal.star_comm_self

namespace selfAdjoint

section AddGroupₓ

variable [AddGroupₓ R] [StarAddMonoid R]

theorem mem_iff {x : R} : x ∈ selfAdjoint R ↔ star x = x := by
  rw [← AddSubgroup.mem_carrier]
  exact Iff.rfl

@[simp, norm_cast]
theorem star_coe_eq {x : selfAdjoint R} : star (x : R) = x :=
  x.Prop

instance : Inhabited (selfAdjoint R) :=
  ⟨0⟩

theorem bit0_mem {x : R} (hx : x ∈ selfAdjoint R) : bit0 x ∈ selfAdjoint R := by
  simp only [← mem_iff, ← star_bit0, ← mem_iff.mp hx]

end AddGroupₓ

section Ringₓ

variable [Ringₓ R] [StarRing R]

instance : One (selfAdjoint R) :=
  ⟨⟨1, by
      rw [mem_iff, star_one]⟩⟩

@[simp, norm_cast]
theorem coe_one : ↑(1 : selfAdjoint R) = (1 : R) :=
  rfl

instance [Nontrivial R] : Nontrivial (selfAdjoint R) :=
  ⟨⟨0, 1, Subtype.ne_of_val_ne zero_ne_one⟩⟩

theorem one_mem : (1 : R) ∈ selfAdjoint R := by
  simp only [← mem_iff, ← star_one]

instance : HasNatCast (selfAdjoint R) :=
  ⟨fun n =>
    ⟨n, by
      induction n <;> simp [← zero_mem, ← add_mem, ← one_mem, *]⟩⟩

instance : HasIntCast (selfAdjoint R) :=
  ⟨fun n =>
    ⟨n, by
      cases n <;> simp [← add_mem, ← one_mem, ← show ↑n ∈ selfAdjoint R from (n : selfAdjoint R).2]⟩⟩

theorem bit1_mem {x : R} (hx : x ∈ selfAdjoint R) : bit1 x ∈ selfAdjoint R := by
  simp only [← mem_iff, ← star_bit1, ← mem_iff.mp hx]

theorem conjugate {x : R} (hx : x ∈ selfAdjoint R) (z : R) : z * x * star z ∈ selfAdjoint R := by
  simp only [← mem_iff, ← star_mul, ← star_star, ← mem_iff.mp hx, ← mul_assoc]

theorem conjugate' {x : R} (hx : x ∈ selfAdjoint R) (z : R) : star z * x * z ∈ selfAdjoint R := by
  simp only [← mem_iff, ← star_mul, ← star_star, ← mem_iff.mp hx, ← mul_assoc]

theorem is_star_normal_of_mem {x : R} (hx : x ∈ selfAdjoint R) : IsStarNormal x :=
  ⟨by
    simp only [← mem_iff] at hx
    simp only [← hx]⟩

instance (x : selfAdjoint R) : IsStarNormal (x : R) :=
  is_star_normal_of_mem (SetLike.coe_mem _)

instance : Pow (selfAdjoint R) ℕ :=
  ⟨fun x n =>
    ⟨(x : R) ^ n, by
      simp only [← mem_iff, ← star_pow, ← star_coe_eq]⟩⟩

@[simp, norm_cast]
theorem coe_pow (x : selfAdjoint R) (n : ℕ) : ↑(x ^ n) = (x : R) ^ n :=
  rfl

end Ringₓ

section CommRingₓ

variable [CommRingₓ R] [StarRing R]

instance : Mul (selfAdjoint R) :=
  ⟨fun x y =>
    ⟨(x : R) * y, by
      simp only [← mem_iff, ← star_mul', ← star_coe_eq]⟩⟩

@[simp, norm_cast]
theorem coe_mul (x y : selfAdjoint R) : ↑(x * y) = (x : R) * y :=
  rfl

instance : CommRingₓ (selfAdjoint R) :=
  Function.Injective.commRing _ Subtype.coe_injective (selfAdjoint R).coe_zero coe_one (selfAdjoint R).coe_add coe_mul
    (selfAdjoint R).coeNeg (selfAdjoint R).coe_sub (selfAdjoint R).coe_nsmul (selfAdjoint R).coe_zsmul coe_pow
    (fun _ => rfl) fun _ => rfl

end CommRingₓ

section Field

variable [Field R] [StarRing R]

instance :
    Inv (selfAdjoint R) where inv := fun x =>
    ⟨x.val⁻¹, by
      simp only [← mem_iff, ← star_inv', ← star_coe_eq, ← Subtype.val_eq_coe]⟩

@[simp, norm_cast]
theorem coe_inv (x : selfAdjoint R) : ↑x⁻¹ = (x : R)⁻¹ :=
  rfl

instance :
    Div (selfAdjoint R) where div := fun x y =>
    ⟨x / y, by
      simp only [← mem_iff, ← star_div', ← star_coe_eq, ← Subtype.val_eq_coe]⟩

@[simp, norm_cast]
theorem coe_div (x y : selfAdjoint R) : ↑(x / y) = (x / y : R) :=
  rfl

instance :
    Pow (selfAdjoint R) ℤ where pow := fun x z =>
    ⟨x ^ z, by
      simp only [← mem_iff, ← star_zpow₀, ← star_coe_eq, ← Subtype.val_eq_coe]⟩

@[simp, norm_cast]
theorem coe_zpow (x : selfAdjoint R) (z : ℤ) : ↑(x ^ z) = (x : R) ^ z :=
  rfl

instance : Field (selfAdjoint R) :=
  Function.Injective.field _ Subtype.coe_injective (selfAdjoint R).coe_zero coe_one (selfAdjoint R).coe_add coe_mul
    (selfAdjoint R).coeNeg (selfAdjoint R).coe_sub coe_inv coe_div (selfAdjoint R).coe_nsmul (selfAdjoint R).coe_zsmul
    coe_pow coe_zpow (fun _ => rfl) fun _ => rfl

end Field

section HasSmul

variable [HasStar R] [HasTrivialStar R] [AddGroupₓ A] [StarAddMonoid A]

theorem smul_mem [HasSmul R A] [StarModule R A] (r : R) {x : A} (h : x ∈ selfAdjoint A) : r • x ∈ selfAdjoint A := by
  rw [mem_iff, star_smul, star_trivial, mem_iff.mp h]

instance [HasSmul R A] [StarModule R A] : HasSmul R (selfAdjoint A) :=
  ⟨fun r x => ⟨r • x, smul_mem r x.Prop⟩⟩

@[simp, norm_cast]
theorem coe_smul [HasSmul R A] [StarModule R A] (r : R) (x : selfAdjoint A) : ↑(r • x) = r • (x : A) :=
  rfl

instance [Monoidₓ R] [MulAction R A] [StarModule R A] : MulAction R (selfAdjoint A) :=
  Function.Injective.mulAction coe Subtype.coe_injective coe_smul

instance [Monoidₓ R] [DistribMulAction R A] [StarModule R A] : DistribMulAction R (selfAdjoint A) :=
  Function.Injective.distribMulAction (selfAdjoint A).Subtype Subtype.coe_injective coe_smul

end HasSmul

section Module

variable [HasStar R] [HasTrivialStar R] [AddCommGroupₓ A] [StarAddMonoid A]

instance [Semiringₓ R] [Module R A] [StarModule R A] : Module R (selfAdjoint A) :=
  Function.Injective.module R (selfAdjoint A).Subtype Subtype.coe_injective coe_smul

end Module

end selfAdjoint

namespace skewAdjoint

section AddGroupₓ

variable [AddCommGroupₓ R] [StarAddMonoid R]

theorem mem_iff {x : R} : x ∈ skewAdjoint R ↔ star x = -x := by
  rw [← AddSubgroup.mem_carrier]
  exact Iff.rfl

@[simp, norm_cast]
theorem star_coe_eq {x : skewAdjoint R} : star (x : R) = -x :=
  x.Prop

instance : Inhabited (skewAdjoint R) :=
  ⟨0⟩

theorem bit0_mem {x : R} (hx : x ∈ skewAdjoint R) : bit0 x ∈ skewAdjoint R := by
  rw [mem_iff, star_bit0, mem_iff.mp hx, bit0, bit0, neg_add]

end AddGroupₓ

section Ringₓ

variable [Ringₓ R] [StarRing R]

theorem conjugate {x : R} (hx : x ∈ skewAdjoint R) (z : R) : z * x * star z ∈ skewAdjoint R := by
  simp only [← mem_iff, ← star_mul, ← star_star, ← mem_iff.mp hx, ← neg_mul, ← mul_neg, ← mul_assoc]

theorem conjugate' {x : R} (hx : x ∈ skewAdjoint R) (z : R) : star z * x * z ∈ skewAdjoint R := by
  simp only [← mem_iff, ← star_mul, ← star_star, ← mem_iff.mp hx, ← neg_mul, ← mul_neg, ← mul_assoc]

theorem is_star_normal_of_mem {x : R} (hx : x ∈ skewAdjoint R) : IsStarNormal x :=
  ⟨by
    simp only [← mem_iff] at hx
    simp only [← hx, ← Commute.neg_left]⟩

instance (x : skewAdjoint R) : IsStarNormal (x : R) :=
  is_star_normal_of_mem (SetLike.coe_mem _)

end Ringₓ

section HasSmul

variable [HasStar R] [HasTrivialStar R] [AddCommGroupₓ A] [StarAddMonoid A]

theorem smul_mem [Monoidₓ R] [DistribMulAction R A] [StarModule R A] (r : R) {x : A} (h : x ∈ skewAdjoint A) :
    r • x ∈ skewAdjoint A := by
  rw [mem_iff, star_smul, star_trivial, mem_iff.mp h, smul_neg r]

instance [Monoidₓ R] [DistribMulAction R A] [StarModule R A] : HasSmul R (skewAdjoint A) :=
  ⟨fun r x => ⟨r • x, smul_mem r x.Prop⟩⟩

@[simp, norm_cast]
theorem coe_smul [Monoidₓ R] [DistribMulAction R A] [StarModule R A] (r : R) (x : skewAdjoint A) :
    ↑(r • x) = r • (x : A) :=
  rfl

instance [Monoidₓ R] [DistribMulAction R A] [StarModule R A] : DistribMulAction R (skewAdjoint A) :=
  Function.Injective.distribMulAction (skewAdjoint A).Subtype Subtype.coe_injective coe_smul

instance [Semiringₓ R] [Module R A] [StarModule R A] : Module R (skewAdjoint A) :=
  Function.Injective.module R (skewAdjoint A).Subtype Subtype.coe_injective coe_smul

end HasSmul

end skewAdjoint

instance is_star_normal_zero [Semiringₓ R] [StarRing R] : IsStarNormal (0 : R) :=
  ⟨by
    simp only [← star_comm_self, ← star_zero]⟩

instance is_star_normal_one [Monoidₓ R] [StarSemigroup R] : IsStarNormal (1 : R) :=
  ⟨by
    simp only [← star_comm_self, ← star_one]⟩

instance is_star_normal_star_self [Monoidₓ R] [StarSemigroup R] {x : R} [IsStarNormal x] : IsStarNormal (star x) :=
  ⟨show star (star x) * star x = star x * star (star x) by
      rw [star_star, star_comm_self']⟩

-- see Note [lower instance priority]
instance (priority := 100) HasTrivialStar.is_star_normal [Monoidₓ R] [StarSemigroup R] [HasTrivialStar R] {x : R} :
    IsStarNormal x :=
  ⟨by
    rw [star_trivial]⟩

-- see Note [lower instance priority]
instance (priority := 100) CommMonoidₓ.is_star_normal [CommMonoidₓ R] [StarSemigroup R] {x : R} : IsStarNormal x :=
  ⟨mul_comm _ _⟩

