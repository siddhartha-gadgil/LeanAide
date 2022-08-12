/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import Mathbin.Algebra.Algebra.Basic
import Mathbin.LinearAlgebra.Prod
import Mathbin.Algebra.Hom.NonUnitalAlg

/-!
# Unitization of a non-unital algebra

Given a non-unital `R`-algebra `A` (given via the type classes
`[non_unital_ring A] [module R A] [smul_comm_class R A A] [is_scalar_tower R A A]`) we construct
the minimal unital `R`-algebra containing `A` as an ideal. This object `algebra.unitization R A` is
a type synonym for `R × A` on which we place a different multiplicative structure, namely,
`(r₁, a₁) * (r₂, a₂) = (r₁ * r₂, r₁ • a₂ + r₂ • a₁ + a₁ * a₂)` where the multiplicative identity
is `(1, 0)`.

Note, when `A` is a *unital* `R`-algebra, then `unitization R A` constructs a new multiplicative
identity different from the old one, and so in general `unitization R A` and `A` will not be
isomorphic even in the unital case. This approach actually has nice functorial properties.

There is a natural coercion from `A` to `unitization R A` given by `λ a, (0, a)`, the image
of which is a proper ideal (TODO), and when `R` is a field this ideal is maximal. Moreover,
this ideal is always an essential ideal (it has nontrivial intersection with every other nontrivial
ideal).

Every non-unital algebra homomorphism from `A` into a *unital* `R`-algebra `B` has a unique
extension to a (unital) algebra homomorphism from `unitization R A` to `B`.

## Main definitions

* `unitization R A`: the unitization of a non-unital `R`-algebra `A`.
* `unitization.algebra`: the unitization of `A` as a (unital) `R`-algebra.
* `unitization.coe_non_unital_alg_hom`: coercion as a non-unital algebra homomorphism.
* `non_unital_alg_hom.to_alg_hom φ`: the extension of a non-unital algebra homomorphism `φ : A → B`
  into a unital `R`-algebra `B` to an algebra homomorphism `unitization R A →ₐ[R] B`.

## Main results

* `non_unital_alg_hom.to_alg_hom_unique`: the extension is unique

## TODO

* prove the unitization operation is a functor between the appropriate categories
* prove the image of the coercion is an essential ideal, maximal if scalars are a field.
-/


/-- The minimal unitization of a non-unital `R`-algebra `A`. This is just a type synonym for
`R × A`.-/
def Unitization (R A : Type _) :=
  R × A

namespace Unitization

section Basic

variable {R A : Type _}

/-- The canonical inclusion `R → unitization R A`. -/
def inl [Zero A] (r : R) : Unitization R A :=
  (r, 0)

/-- The canonical inclusion `A → unitization R A`. -/
instance [Zero R] : CoeTₓ A (Unitization R A) where coe := fun a => (0, a)

/-- The canonical projection `unitization R A → R`. -/
def fst (x : Unitization R A) : R :=
  x.1

/-- The canonical projection `unitization R A → A`. -/
def snd (x : Unitization R A) : A :=
  x.2

@[ext]
theorem ext {x y : Unitization R A} (h1 : x.fst = y.fst) (h2 : x.snd = y.snd) : x = y :=
  Prod.extₓ h1 h2

section

variable (A)

@[simp]
theorem fst_inl [Zero A] (r : R) : (inl r : Unitization R A).fst = r :=
  rfl

@[simp]
theorem snd_inl [Zero A] (r : R) : (inl r : Unitization R A).snd = 0 :=
  rfl

end

section

variable (R)

@[simp]
theorem fst_coe [Zero R] (a : A) : (a : Unitization R A).fst = 0 :=
  rfl

@[simp]
theorem snd_coe [Zero R] (a : A) : (a : Unitization R A).snd = a :=
  rfl

end

theorem inl_injective [Zero A] : Function.Injective (inl : R → Unitization R A) :=
  Function.LeftInverse.injective <| fst_inl _

theorem coe_injective [Zero R] : Function.Injective (coe : A → Unitization R A) :=
  Function.LeftInverse.injective <| snd_coe _

end Basic

/-! ### Structures inherited from `prod`

Additive operators and scalar multiplication operate elementwise. -/


section Additive

variable {T : Type _} {S : Type _} {R : Type _} {A : Type _}

instance [Inhabited R] [Inhabited A] : Inhabited (Unitization R A) :=
  Prod.inhabited

instance [Zero R] [Zero A] : Zero (Unitization R A) :=
  Prod.hasZero

instance [Add R] [Add A] : Add (Unitization R A) :=
  Prod.hasAdd

instance [Neg R] [Neg A] : Neg (Unitization R A) :=
  Prod.hasNeg

instance [AddSemigroupₓ R] [AddSemigroupₓ A] : AddSemigroupₓ (Unitization R A) :=
  Prod.addSemigroup

instance [AddZeroClassₓ R] [AddZeroClassₓ A] : AddZeroClassₓ (Unitization R A) :=
  Prod.addZeroClass

instance [AddMonoidₓ R] [AddMonoidₓ A] : AddMonoidₓ (Unitization R A) :=
  Prod.addMonoid

instance [AddGroupₓ R] [AddGroupₓ A] : AddGroupₓ (Unitization R A) :=
  Prod.addGroup

instance [AddCommSemigroupₓ R] [AddCommSemigroupₓ A] : AddCommSemigroupₓ (Unitization R A) :=
  Prod.addCommSemigroup

instance [AddCommMonoidₓ R] [AddCommMonoidₓ A] : AddCommMonoidₓ (Unitization R A) :=
  Prod.addCommMonoid

instance [AddCommGroupₓ R] [AddCommGroupₓ A] : AddCommGroupₓ (Unitization R A) :=
  Prod.addCommGroup

instance [HasSmul S R] [HasSmul S A] : HasSmul S (Unitization R A) :=
  Prod.hasSmul

instance [HasSmul T R] [HasSmul T A] [HasSmul S R] [HasSmul S A] [HasSmul T S] [IsScalarTower T S R]
    [IsScalarTower T S A] : IsScalarTower T S (Unitization R A) :=
  Prod.is_scalar_tower

instance [HasSmul T R] [HasSmul T A] [HasSmul S R] [HasSmul S A] [SmulCommClass T S R] [SmulCommClass T S A] :
    SmulCommClass T S (Unitization R A) :=
  Prod.smul_comm_class

instance [HasSmul S R] [HasSmul S A] [HasSmul Sᵐᵒᵖ R] [HasSmul Sᵐᵒᵖ A] [IsCentralScalar S R] [IsCentralScalar S A] :
    IsCentralScalar S (Unitization R A) :=
  Prod.is_central_scalar

instance [Monoidₓ S] [MulAction S R] [MulAction S A] : MulAction S (Unitization R A) :=
  Prod.mulAction

instance [Monoidₓ S] [AddMonoidₓ R] [AddMonoidₓ A] [DistribMulAction S R] [DistribMulAction S A] :
    DistribMulAction S (Unitization R A) :=
  Prod.distribMulAction

instance [Semiringₓ S] [AddCommMonoidₓ R] [AddCommMonoidₓ A] [Module S R] [Module S A] : Module S (Unitization R A) :=
  Prod.module

@[simp]
theorem fst_zero [Zero R] [Zero A] : (0 : Unitization R A).fst = 0 :=
  rfl

@[simp]
theorem snd_zero [Zero R] [Zero A] : (0 : Unitization R A).snd = 0 :=
  rfl

@[simp]
theorem fst_add [Add R] [Add A] (x₁ x₂ : Unitization R A) : (x₁ + x₂).fst = x₁.fst + x₂.fst :=
  rfl

@[simp]
theorem snd_add [Add R] [Add A] (x₁ x₂ : Unitization R A) : (x₁ + x₂).snd = x₁.snd + x₂.snd :=
  rfl

@[simp]
theorem fst_neg [Neg R] [Neg A] (x : Unitization R A) : (-x).fst = -x.fst :=
  rfl

@[simp]
theorem snd_neg [Neg R] [Neg A] (x : Unitization R A) : (-x).snd = -x.snd :=
  rfl

@[simp]
theorem fst_smul [HasSmul S R] [HasSmul S A] (s : S) (x : Unitization R A) : (s • x).fst = s • x.fst :=
  rfl

@[simp]
theorem snd_smul [HasSmul S R] [HasSmul S A] (s : S) (x : Unitization R A) : (s • x).snd = s • x.snd :=
  rfl

section

variable (A)

@[simp]
theorem inl_zero [Zero R] [Zero A] : (inl 0 : Unitization R A) = 0 :=
  rfl

@[simp]
theorem inl_add [Add R] [AddZeroClassₓ A] (r₁ r₂ : R) : (inl (r₁ + r₂) : Unitization R A) = inl r₁ + inl r₂ :=
  ext rfl (add_zeroₓ 0).symm

@[simp]
theorem inl_neg [Neg R] [AddGroupₓ A] (r : R) : (inl (-r) : Unitization R A) = -inl r :=
  ext rfl neg_zero.symm

@[simp]
theorem inl_smul [Monoidₓ S] [AddMonoidₓ A] [HasSmul S R] [DistribMulAction S A] (s : S) (r : R) :
    (inl (s • r) : Unitization R A) = s • inl r :=
  ext rfl (smul_zero s).symm

end

section

variable (R)

@[simp]
theorem coe_zero [Zero R] [Zero A] : ↑(0 : A) = (0 : Unitization R A) :=
  rfl

@[simp]
theorem coe_add [AddZeroClassₓ R] [Add A] (m₁ m₂ : A) : (↑(m₁ + m₂) : Unitization R A) = m₁ + m₂ :=
  ext (add_zeroₓ 0).symm rfl

@[simp]
theorem coe_neg [AddGroupₓ R] [Neg A] (m : A) : (↑(-m) : Unitization R A) = -m :=
  ext neg_zero.symm rfl

@[simp]
theorem coe_smul [Zero R] [Zero S] [SmulWithZero S R] [HasSmul S A] (r : S) (m : A) :
    (↑(r • m) : Unitization R A) = r • m :=
  ext (smul_zero' _ _).symm rfl

end

theorem inl_fst_add_coe_snd_eq [AddZeroClassₓ R] [AddZeroClassₓ A] (x : Unitization R A) : inl x.fst + ↑x.snd = x :=
  ext (add_zeroₓ x.1) (zero_addₓ x.2)

/-- To show a property hold on all `unitization R A` it suffices to show it holds
on terms of the form `inl r + a`.

This can be used as `induction x using unitization.ind`. -/
theorem ind {R A} [AddZeroClassₓ R] [AddZeroClassₓ A] {P : Unitization R A → Prop}
    (h : ∀ (r : R) (a : A), P (inl r + a)) (x) : P x :=
  inl_fst_add_coe_snd_eq x ▸ h x.1 x.2

/-- This cannot be marked `@[ext]` as it ends up being used instead of `linear_map.prod_ext` when
working with `R × A`. -/
theorem linear_map_ext {N} [Semiringₓ S] [AddCommMonoidₓ R] [AddCommMonoidₓ A] [AddCommMonoidₓ N] [Module S R]
    [Module S A] [Module S N] ⦃f g : Unitization R A →ₗ[S] N⦄ (hl : ∀ r, f (inl r) = g (inl r))
    (hr : ∀ a : A, f a = g a) : f = g :=
  LinearMap.prod_ext (LinearMap.ext hl) (LinearMap.ext hr)

variable (R A)

/-- The canonical `R`-linear inclusion `A → unitization R A`. -/
@[simps apply]
def coeHom [Semiringₓ R] [AddCommMonoidₓ A] [Module R A] : A →ₗ[R] Unitization R A :=
  { LinearMap.inr R R A with toFun := coe }

/-- The canonical `R`-linear projection `unitization R A → A`. -/
@[simps apply]
def sndHom [Semiringₓ R] [AddCommMonoidₓ A] [Module R A] : Unitization R A →ₗ[R] A :=
  { LinearMap.snd _ _ _ with toFun := snd }

end Additive

/-! ### Multiplicative structure -/


section Mul

variable {R A : Type _}

instance [One R] [Zero A] : One (Unitization R A) :=
  ⟨(1, 0)⟩

instance [Mul R] [Add A] [Mul A] [HasSmul R A] : Mul (Unitization R A) :=
  ⟨fun x y => (x.1 * y.1, x.1 • y.2 + y.1 • x.2 + x.2 * y.2)⟩

@[simp]
theorem fst_one [One R] [Zero A] : (1 : Unitization R A).fst = 1 :=
  rfl

@[simp]
theorem snd_one [One R] [Zero A] : (1 : Unitization R A).snd = 0 :=
  rfl

@[simp]
theorem fst_mul [Mul R] [Add A] [Mul A] [HasSmul R A] (x₁ x₂ : Unitization R A) : (x₁ * x₂).fst = x₁.fst * x₂.fst :=
  rfl

@[simp]
theorem snd_mul [Mul R] [Add A] [Mul A] [HasSmul R A] (x₁ x₂ : Unitization R A) :
    (x₁ * x₂).snd = x₁.fst • x₂.snd + x₂.fst • x₁.snd + x₁.snd * x₂.snd :=
  rfl

section

variable (A)

@[simp]
theorem inl_one [One R] [Zero A] : (inl 1 : Unitization R A) = 1 :=
  rfl

@[simp]
theorem inl_mul [Monoidₓ R] [NonUnitalNonAssocSemiringₓ A] [DistribMulAction R A] (r₁ r₂ : R) :
    (inl (r₁ * r₂) : Unitization R A) = inl r₁ * inl r₂ :=
  ext rfl <|
    show (0 : A) = r₁ • (0 : A) + r₂ • 0 + 0 * 0 by
      simp only [← smul_zero, ← add_zeroₓ, ← mul_zero]

theorem inl_mul_inl [Monoidₓ R] [NonUnitalNonAssocSemiringₓ A] [DistribMulAction R A] (r₁ r₂ : R) :
    (inl r₁ * inl r₂ : Unitization R A) = inl (r₁ * r₂) :=
  (inl_mul A r₁ r₂).symm

end

section

variable (R)

@[simp]
theorem coe_mul [Semiringₓ R] [AddCommMonoidₓ A] [Mul A] [SmulWithZero R A] (a₁ a₂ : A) :
    (↑(a₁ * a₂) : Unitization R A) = a₁ * a₂ :=
  ext (mul_zero _).symm <|
    show a₁ * a₂ = (0 : R) • a₂ + (0 : R) • a₁ + a₁ * a₂ by
      simp only [← zero_smul, ← zero_addₓ]

end

theorem inl_mul_coe [Semiringₓ R] [NonUnitalNonAssocSemiringₓ A] [DistribMulAction R A] (r : R) (a : A) :
    (inl r * a : Unitization R A) = ↑(r • a) :=
  ext (mul_zero r) <|
    show r • a + (0 : R) • 0 + 0 * a = r • a by
      rw [smul_zero, add_zeroₓ, zero_mul, add_zeroₓ]

theorem coe_mul_inl [Semiringₓ R] [NonUnitalNonAssocSemiringₓ A] [DistribMulAction R A] (r : R) (a : A) :
    (a * inl r : Unitization R A) = ↑(r • a) :=
  ext (zero_mul r) <|
    show (0 : R) • 0 + r • a + a * 0 = r • a by
      rw [smul_zero, zero_addₓ, mul_zero, add_zeroₓ]

instance mulOneClass [Monoidₓ R] [NonUnitalNonAssocSemiringₓ A] [DistribMulAction R A] :
    MulOneClassₓ (Unitization R A) :=
  { Unitization.hasOne, Unitization.hasMul with
    one_mul := fun x =>
      ext (one_mulₓ x.1) <|
        show (1 : R) • x.2 + x.1 • 0 + 0 * x.2 = x.2 by
          rw [one_smul, smul_zero, add_zeroₓ, zero_mul, add_zeroₓ],
    mul_one := fun x =>
      ext (mul_oneₓ x.1) <|
        show (x.1 • 0 : A) + (1 : R) • x.2 + x.2 * 0 = x.2 by
          rw [smul_zero, zero_addₓ, one_smul, mul_zero, add_zeroₓ] }

instance [Semiringₓ R] [NonUnitalNonAssocSemiringₓ A] [Module R A] : NonAssocSemiringₓ (Unitization R A) :=
  { Unitization.mulOneClass, Unitization.addCommMonoid with
    zero_mul := fun x =>
      ext (zero_mul x.1) <|
        show (0 : R) • x.2 + x.1 • 0 + 0 * x.2 = 0 by
          rw [zero_smul, zero_addₓ, smul_zero, zero_mul, add_zeroₓ],
    mul_zero := fun x =>
      ext (mul_zero x.1) <|
        show (x.1 • 0 : A) + (0 : R) • x.2 + x.2 * 0 = 0 by
          rw [smul_zero, zero_addₓ, zero_smul, mul_zero, add_zeroₓ],
    left_distrib := fun x₁ x₂ x₃ =>
      ext (mul_addₓ x₁.1 x₂.1 x₃.1) <|
        show
          x₁.1 • (x₂.2 + x₃.2) + (x₂.1 + x₃.1) • x₁.2 + x₁.2 * (x₂.2 + x₃.2) =
            x₁.1 • x₂.2 + x₂.1 • x₁.2 + x₁.2 * x₂.2 + (x₁.1 • x₃.2 + x₃.1 • x₁.2 + x₁.2 * x₃.2)
          by
          simp only [← smul_add, ← add_smul, ← mul_addₓ]
          abel,
    right_distrib := fun x₁ x₂ x₃ =>
      ext (add_mulₓ x₁.1 x₂.1 x₃.1) <|
        show
          (x₁.1 + x₂.1) • x₃.2 + x₃.1 • (x₁.2 + x₂.2) + (x₁.2 + x₂.2) * x₃.2 =
            x₁.1 • x₃.2 + x₃.1 • x₁.2 + x₁.2 * x₃.2 + (x₂.1 • x₃.2 + x₃.1 • x₂.2 + x₂.2 * x₃.2)
          by
          simp only [← add_smul, ← smul_add, ← add_mulₓ]
          abel }

instance [CommMonoidₓ R] [NonUnitalSemiringₓ A] [DistribMulAction R A] [IsScalarTower R A A] [SmulCommClass R A A] :
    Monoidₓ (Unitization R A) :=
  { Unitization.mulOneClass with
    mul_assoc := fun x y z =>
      ext (mul_assoc x.1 y.1 z.1) <|
        show
          (x.1 * y.1) • z.2 + z.1 • (x.1 • y.2 + y.1 • x.2 + x.2 * y.2) + (x.1 • y.2 + y.1 • x.2 + x.2 * y.2) * z.2 =
            x.1 • (y.1 • z.2 + z.1 • y.2 + y.2 * z.2) + (y.1 * z.1) • x.2 + x.2 * (y.1 • z.2 + z.1 • y.2 + y.2 * z.2)
          by
          simp only [← smul_add, ← mul_addₓ, ← add_mulₓ, ← smul_smul, ← smul_mul_assoc, ← mul_smul_comm, ← mul_assoc]
          nth_rw 1[mul_comm]
          nth_rw 2[mul_comm]
          abel }

-- This should work for `non_unital_comm_semiring`s, but we don't seem to have those
instance [CommMonoidₓ R] [CommSemiringₓ A] [DistribMulAction R A] [IsScalarTower R A A] [SmulCommClass R A A] :
    CommMonoidₓ (Unitization R A) :=
  { Unitization.monoid with
    mul_comm := fun x₁ x₂ =>
      ext (mul_comm x₁.1 x₂.1) <|
        show x₁.1 • x₂.2 + x₂.1 • x₁.2 + x₁.2 * x₂.2 = x₂.1 • x₁.2 + x₁.1 • x₂.2 + x₂.2 * x₁.2 by
          rw [add_commₓ (x₁.1 • x₂.2), mul_comm] }

instance [CommSemiringₓ R] [NonUnitalSemiringₓ A] [Module R A] [IsScalarTower R A A] [SmulCommClass R A A] :
    Semiringₓ (Unitization R A) :=
  { Unitization.monoid, Unitization.nonAssocSemiring with }

-- This should work for `non_unital_comm_semiring`s, but we don't seem to have those
instance [CommSemiringₓ R] [CommSemiringₓ A] [Module R A] [IsScalarTower R A A] [SmulCommClass R A A] :
    CommSemiringₓ (Unitization R A) :=
  { Unitization.commMonoid, Unitization.nonAssocSemiring with }

variable (R A)

/-- The canonical inclusion of rings `R →+* unitization R A`. -/
@[simps apply]
def inlRingHom [Semiringₓ R] [NonUnitalSemiringₓ A] [Module R A] : R →+* Unitization R A where
  toFun := inl
  map_one' := inl_one A
  map_mul' := inl_mul A
  map_zero' := inl_zero A
  map_add' := inl_add A

end Mul

/-! ### Star structure -/


section Star

variable {R A : Type _}

instance [HasStar R] [HasStar A] : HasStar (Unitization R A) :=
  ⟨fun ra => (star ra.fst, star ra.snd)⟩

@[simp]
theorem fst_star [HasStar R] [HasStar A] (x : Unitization R A) : (star x).fst = star x.fst :=
  rfl

@[simp]
theorem snd_star [HasStar R] [HasStar A] (x : Unitization R A) : (star x).snd = star x.snd :=
  rfl

@[simp]
theorem inl_star [HasStar R] [AddMonoidₓ A] [StarAddMonoid A] (r : R) : inl (star r) = star (inl r : Unitization R A) :=
  ext rfl
    (by
      simp only [← snd_star, ← star_zero, ← snd_inl])

@[simp]
theorem coe_star [AddMonoidₓ R] [StarAddMonoid R] [HasStar A] (a : A) : ↑(star a) = star (a : Unitization R A) :=
  ext
    (by
      simp only [← fst_star, ← star_zero, ← fst_coe])
    rfl

instance [AddMonoidₓ R] [AddMonoidₓ A] [StarAddMonoid R] [StarAddMonoid A] : StarAddMonoid (Unitization R A) where
  star_involutive := fun x => ext (star_star x.fst) (star_star x.snd)
  star_add := fun x y => ext (star_add x.fst y.fst) (star_add x.snd y.snd)

instance [CommSemiringₓ R] [StarRing R] [AddCommMonoidₓ A] [StarAddMonoid A] [Module R A] [StarModule R A] :
    StarModule R (Unitization R A) where star_smul := fun r x =>
    ext
      (by
        simp )
      (by
        simp )

instance [CommSemiringₓ R] [StarRing R] [NonUnitalSemiringₓ A] [StarRing A] [Module R A] [IsScalarTower R A A]
    [SmulCommClass R A A] [StarModule R A] : StarRing (Unitization R A) :=
  { Unitization.starAddMonoid with
    star_mul := fun x y =>
      ext
        (by
          simp [← star_mul])
        (by
          simp [← star_mul, ← add_commₓ (star x.fst • star y.snd)]) }

end Star

/-! ### Algebra structure -/


section Algebra

variable (S R A : Type _) [CommSemiringₓ S] [CommSemiringₓ R] [NonUnitalSemiringₓ A] [Module R A] [IsScalarTower R A A]
  [SmulCommClass R A A] [Algebra S R] [DistribMulAction S A] [IsScalarTower S R A]

instance algebra : Algebra S (Unitization R A) :=
  { (Unitization.inlRingHom R A).comp (algebraMap S R) with
    commutes' := fun r x => by
      induction x using Unitization.ind
      simp only [← mul_addₓ, ← add_mulₓ, ← RingHom.to_fun_eq_coe, ← RingHom.coe_comp, ← Function.comp_app, ←
        inl_ring_hom_apply, ← inl_mul_inl]
      rw [inl_mul_coe, coe_mul_inl, mul_comm],
    smul_def' := fun s x => by
      induction x using Unitization.ind
      simp only [← mul_addₓ, ← smul_add, ← RingHom.to_fun_eq_coe, ← RingHom.coe_comp, ← Function.comp_app, ←
        inl_ring_hom_apply, ← Algebra.algebra_map_eq_smul_one]
      rw [inl_mul_inl, inl_mul_coe, smul_one_mul, inl_smul, coe_smul, smul_one_smul] }

theorem algebra_map_eq_inl_comp : ⇑(algebraMap S (Unitization R A)) = inl ∘ algebraMap S R :=
  rfl

theorem algebra_map_eq_inl_ring_hom_comp : algebraMap S (Unitization R A) = (inlRingHom R A).comp (algebraMap S R) :=
  rfl

theorem algebra_map_eq_inl : ⇑(algebraMap R (Unitization R A)) = inl :=
  rfl

theorem algebra_map_eq_inl_hom : algebraMap R (Unitization R A) = inlRingHom R A :=
  rfl

/-- The canonical `R`-algebra projection `unitization R A → R`. -/
@[simps]
def fstHom : Unitization R A →ₐ[R] R where
  toFun := fst
  map_one' := fst_one
  map_mul' := fst_mul
  map_zero' := fst_zero
  map_add' := fst_add
  commutes' := fst_inl A

end Algebra

section coe

/-- The coercion from a non-unital `R`-algebra `A` to its unitization `unitization R A`
realized as a non-unital algebra homomorphism. -/
@[simps]
def coeNonUnitalAlgHom (R A : Type _) [CommSemiringₓ R] [NonUnitalSemiringₓ A] [Module R A] :
    A →ₙₐ[R] Unitization R A where
  toFun := coe
  map_smul' := coe_smul R
  map_zero' := coe_zero R
  map_add' := coe_add R
  map_mul' := coe_mul R

end coe

section AlgHom

variable {S R A : Type _} [CommSemiringₓ S] [CommSemiringₓ R] [NonUnitalSemiringₓ A] [Module R A] [SmulCommClass R A A]
  [IsScalarTower R A A] {B : Type _} [Semiringₓ B] [Algebra S B] [Algebra S R] [DistribMulAction S A]
  [IsScalarTower S R A] {C : Type _} [Ringₓ C] [Algebra R C]

theorem alg_hom_ext {φ ψ : Unitization R A →ₐ[S] B} (h : ∀ a : A, φ a = ψ a)
    (h' : ∀ r, φ (algebraMap R (Unitization R A) r) = ψ (algebraMap R (Unitization R A) r)) : φ = ψ := by
  ext
  induction x using Unitization.ind
  simp only [← map_add, algebra_map_eq_inl, ← h, ← h']

/-- See note [partially-applied ext lemmas] -/
@[ext]
theorem alg_hom_ext' {φ ψ : Unitization R A →ₐ[R] C}
    (h : φ.toNonUnitalAlgHom.comp (coeNonUnitalAlgHom R A) = ψ.toNonUnitalAlgHom.comp (coeNonUnitalAlgHom R A)) :
    φ = ψ :=
  alg_hom_ext (NonUnitalAlgHom.congr_fun h)
    (by
      simp [← AlgHom.commutes])

/-- Non-unital algebra homomorphisms from `A` into a unital `R`-algebra `C` lift uniquely to
`unitization R A →ₐ[R] C`. This is the universal property of the unitization. -/
@[simps apply_apply]
def lift : (A →ₙₐ[R] C) ≃ (Unitization R A →ₐ[R] C) where
  toFun := fun φ =>
    { toFun := fun x => algebraMap R C x.fst + φ x.snd,
      map_one' := by
        simp only [← fst_one, ← map_one, ← snd_one, ← φ.map_zero, ← add_zeroₓ],
      map_mul' := fun x y => by
        induction x using Unitization.ind
        induction y using Unitization.ind
        simp only [← mul_addₓ, ← add_mulₓ, ← coe_mul, ← fst_add, ← fst_mul, ← fst_inl, ← fst_coe, ← mul_zero, ←
          add_zeroₓ, ← zero_mul, ← map_mul, ← snd_add, ← snd_mul, ← snd_inl, ← smul_zero, ← snd_coe, ← zero_addₓ, ←
          φ.map_add, ← φ.map_smul, ← φ.map_mul, ← zero_smul, ← zero_addₓ]
        rw [← Algebra.commutes _ (φ x_a)]
        simp only [← Algebra.algebra_map_eq_smul_one, ← smul_one_mul, ← add_assocₓ],
      map_zero' := by
        simp only [← fst_zero, ← map_zero, ← snd_zero, ← φ.map_zero, ← add_zeroₓ],
      map_add' := fun x y => by
        induction x using Unitization.ind
        induction y using Unitization.ind
        simp only [← fst_add, ← fst_inl, ← fst_coe, ← add_zeroₓ, ← map_add, ← snd_add, ← snd_inl, ← snd_coe, ←
          zero_addₓ, ← φ.map_add]
        rw [add_add_add_commₓ],
      commutes' := fun r => by
        simp only [← algebra_map_eq_inl, ← fst_inl, ← snd_inl, ← φ.map_zero, ← add_zeroₓ] }
  invFun := fun φ => φ.toNonUnitalAlgHom.comp (coeNonUnitalAlgHom R A)
  left_inv := fun φ => by
    ext
    simp
  right_inv := fun φ =>
    Unitization.alg_hom_ext'
      (by
        ext
        simp )

theorem lift_symm_apply (φ : Unitization R A →ₐ[R] C) (a : A) : Unitization.lift.symm φ a = φ a :=
  rfl

end AlgHom

end Unitization

