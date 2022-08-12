/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathbin.Algebra.Algebra.Basic
import Mathbin.SetTheory.Cardinal.Ordinal
import Mathbin.Tactic.RingExp

/-!
# Quaternions

In this file we define quaternions `ℍ[R]` over a commutative ring `R`, and define some
algebraic structures on `ℍ[R]`.

## Main definitions

* `quaternion_algebra R a b`, `ℍ[R, a, b]` :
  [quaternion algebra](https://en.wikipedia.org/wiki/Quaternion_algebra) with coefficients `a`, `b`
* `quaternion R`, `ℍ[R]` : the space of quaternions, a.k.a. `quaternion_algebra R (-1) (-1)`;
* `quaternion.norm_sq` : square of the norm of a quaternion;
* `quaternion.conj` : conjugate of a quaternion;

We also define the following algebraic structures on `ℍ[R]`:

* `ring ℍ[R, a, b]` and `algebra R ℍ[R, a, b]` : for any commutative ring `R`;
* `ring ℍ[R]` and `algebra R ℍ[R]` : for any commutative ring `R`;
* `domain ℍ[R]` : for a linear ordered commutative ring `R`;
* `division_algebra ℍ[R]` : for a linear ordered field `R`.

## Notation

The following notation is available with `open_locale quaternion`.

* `ℍ[R, c₁, c₂]` : `quaternion_algebra R  c₁ c₂`
* `ℍ[R]` : quaternions over `R`.

## Implementation notes

We define quaternions over any ring `R`, not just `ℝ` to be able to deal with, e.g., integer
or rational quaternions without using real numbers. In particular, all definitions in this file
are computable.

## Tags

quaternion
-/


-- ./././Mathport/Syntax/Translate/Basic.lean:1474:34: infer kinds are unsupported in Lean 4: mk {}
/-- Quaternion algebra over a type with fixed coefficients $a=i^2$ and $b=j^2$.
Implemented as a structure with four fields: `re`, `im_i`, `im_j`, and `im_k`. -/
@[nolint unused_arguments, ext]
structure QuaternionAlgebra (R : Type _) (a b : R) where mk ::
  re : R
  imI : R
  imJ : R
  imK : R

-- mathport name: «exprℍ[ , , ]»
localized [Quaternion] notation "ℍ[" R "," a "," b "]" => QuaternionAlgebra R a b

namespace QuaternionAlgebra

/-- The equivalence between a quaternion algebra over R and R × R × R × R. -/
@[simps]
def equivProd {R : Type _} (c₁ c₂ : R) : ℍ[R,c₁,c₂] ≃ R × R × R × R where
  toFun := fun a => ⟨a.1, a.2, a.3, a.4⟩
  invFun := fun a => ⟨a.1, a.2.1, a.2.2.1, a.2.2.2⟩
  left_inv := fun ⟨a₁, a₂, a₃, a₄⟩ => rfl
  right_inv := fun ⟨a₁, a₂, a₃, a₄⟩ => rfl

@[simp]
theorem mk.eta {R : Type _} {c₁ c₂} : ∀ a : ℍ[R,c₁,c₂], mk a.1 a.2 a.3 a.4 = a
  | ⟨a₁, a₂, a₃, a₄⟩ => rfl

variable {R : Type _} [CommRingₓ R] {c₁ c₂ : R} (r x y z : R) (a b c : ℍ[R,c₁,c₂])

instance : CoeTₓ R ℍ[R,c₁,c₂] :=
  ⟨fun x => ⟨x, 0, 0, 0⟩⟩

@[simp]
theorem coe_re : (x : ℍ[R,c₁,c₂]).re = x :=
  rfl

@[simp]
theorem coe_im_i : (x : ℍ[R,c₁,c₂]).imI = 0 :=
  rfl

@[simp]
theorem coe_im_j : (x : ℍ[R,c₁,c₂]).imJ = 0 :=
  rfl

@[simp]
theorem coe_im_k : (x : ℍ[R,c₁,c₂]).imK = 0 :=
  rfl

theorem coe_injective : Function.Injective (coe : R → ℍ[R,c₁,c₂]) := fun x y h => congr_arg re h

@[simp]
theorem coe_inj {x y : R} : (x : ℍ[R,c₁,c₂]) = y ↔ x = y :=
  coe_injective.eq_iff

@[simps]
instance : Zero ℍ[R,c₁,c₂] :=
  ⟨⟨0, 0, 0, 0⟩⟩

@[simp, norm_cast]
theorem coe_zero : ((0 : R) : ℍ[R,c₁,c₂]) = 0 :=
  rfl

instance : Inhabited ℍ[R,c₁,c₂] :=
  ⟨0⟩

@[simps]
instance : One ℍ[R,c₁,c₂] :=
  ⟨⟨1, 0, 0, 0⟩⟩

@[simp, norm_cast]
theorem coe_one : ((1 : R) : ℍ[R,c₁,c₂]) = 1 :=
  rfl

@[simps]
instance : Add ℍ[R,c₁,c₂] :=
  ⟨fun a b => ⟨a.1 + b.1, a.2 + b.2, a.3 + b.3, a.4 + b.4⟩⟩

@[simp]
theorem mk_add_mk (a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ : R) :
    (mk a₁ a₂ a₃ a₄ : ℍ[R,c₁,c₂]) + mk b₁ b₂ b₃ b₄ = mk (a₁ + b₁) (a₂ + b₂) (a₃ + b₃) (a₄ + b₄) :=
  rfl

@[norm_cast, simp]
theorem coe_add : ((x + y : R) : ℍ[R,c₁,c₂]) = x + y := by
  ext <;> simp

@[simps]
instance : Neg ℍ[R,c₁,c₂] :=
  ⟨fun a => ⟨-a.1, -a.2, -a.3, -a.4⟩⟩

@[simp]
theorem neg_mk (a₁ a₂ a₃ a₄ : R) : -(mk a₁ a₂ a₃ a₄ : ℍ[R,c₁,c₂]) = ⟨-a₁, -a₂, -a₃, -a₄⟩ :=
  rfl

@[norm_cast, simp]
theorem coe_neg : ((-x : R) : ℍ[R,c₁,c₂]) = -x := by
  ext <;> simp

@[simps]
instance : Sub ℍ[R,c₁,c₂] :=
  ⟨fun a b => ⟨a.1 - b.1, a.2 - b.2, a.3 - b.3, a.4 - b.4⟩⟩

@[simp]
theorem mk_sub_mk (a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ : R) :
    (mk a₁ a₂ a₃ a₄ : ℍ[R,c₁,c₂]) - mk b₁ b₂ b₃ b₄ = mk (a₁ - b₁) (a₂ - b₂) (a₃ - b₃) (a₄ - b₄) :=
  rfl

/-- Multiplication is given by

* `1 * x = x * 1 = x`;
* `i * i = c₁`;
* `j * j = c₂`;
* `i * j = k`, `j * i = -k`;
* `k * k = -c₁ * c₂`;
* `i * k = c₁ * j`, `k * i = `-c₁ * j`;
* `j * k = -c₂ * i`, `k * j = c₂ * i`.  -/
@[simps]
instance : Mul ℍ[R,c₁,c₂] :=
  ⟨fun a b =>
    ⟨a.1 * b.1 + c₁ * a.2 * b.2 + c₂ * a.3 * b.3 - c₁ * c₂ * a.4 * b.4,
      a.1 * b.2 + a.2 * b.1 - c₂ * a.3 * b.4 + c₂ * a.4 * b.3, a.1 * b.3 + c₁ * a.2 * b.4 + a.3 * b.1 - c₁ * a.4 * b.2,
      a.1 * b.4 + a.2 * b.3 - a.3 * b.2 + a.4 * b.1⟩⟩

@[simp]
theorem mk_mul_mk (a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ : R) :
    (mk a₁ a₂ a₃ a₄ : ℍ[R,c₁,c₂]) * mk b₁ b₂ b₃ b₄ =
      ⟨a₁ * b₁ + c₁ * a₂ * b₂ + c₂ * a₃ * b₃ - c₁ * c₂ * a₄ * b₄, a₁ * b₂ + a₂ * b₁ - c₂ * a₃ * b₄ + c₂ * a₄ * b₃,
        a₁ * b₃ + c₁ * a₂ * b₄ + a₃ * b₁ - c₁ * a₄ * b₂, a₁ * b₄ + a₂ * b₃ - a₃ * b₂ + a₄ * b₁⟩ :=
  rfl

instance : AddCommGroupₓ ℍ[R,c₁,c₂] := by
  refine_struct
      { add := (· + ·), neg := Neg.neg, sub := Sub.sub, zero := (0 : ℍ[R,c₁,c₂]),
        zsmul := @zsmulRec _ ⟨(0 : ℍ[R,c₁,c₂])⟩ ⟨(· + ·)⟩ ⟨Neg.neg⟩,
        nsmul := @nsmulRec _ ⟨(0 : ℍ[R,c₁,c₂])⟩ ⟨(· + ·)⟩ } <;>
    intros <;>
      try
          rfl <;>
        ext <;> simp <;> ring_exp

instance : AddGroupWithOneₓ ℍ[R,c₁,c₂] :=
  { QuaternionAlgebra.addCommGroup with natCast := fun n => ((n : R) : ℍ[R,c₁,c₂]),
    nat_cast_zero := by
      simp ,
    nat_cast_succ := by
      simp ,
    intCast := fun n => ((n : R) : ℍ[R,c₁,c₂]), int_cast_of_nat := fun _ => congr_arg coe (Int.cast_of_nat _),
    int_cast_neg_succ_of_nat := fun n =>
      show ↑↑_ = -↑↑_ by
        rw [Int.cast_neg, Int.cast_coe_nat, coe_neg],
    one := 1 }

instance : Ringₓ ℍ[R,c₁,c₂] := by
  refine_struct
      { QuaternionAlgebra.addGroupWithOne, QuaternionAlgebra.addCommGroup with add := (· + ·), mul := (· * ·), one := 1,
        npow := @npowRec _ ⟨(1 : ℍ[R,c₁,c₂])⟩ ⟨(· * ·)⟩ } <;>
    intros <;>
      try
          rfl <;>
        ext <;> simp <;> ring_exp

instance : Algebra R ℍ[R,c₁,c₂] where
  smul := fun r a => ⟨r * a.1, r * a.2, r * a.3, r * a.4⟩
  toFun := coe
  map_one' := rfl
  map_zero' := rfl
  map_mul' := fun x y => by
    ext <;> simp
  map_add' := fun x y => by
    ext <;> simp
  smul_def' := fun r x => by
    ext <;> simp
  commutes' := fun r x => by
    ext <;> simp [← mul_comm]

@[simp]
theorem smul_re : (r • a).re = r • a.re :=
  rfl

@[simp]
theorem smul_im_i : (r • a).imI = r • a.imI :=
  rfl

@[simp]
theorem smul_im_j : (r • a).imJ = r • a.imJ :=
  rfl

@[simp]
theorem smul_im_k : (r • a).imK = r • a.imK :=
  rfl

@[simp]
theorem smul_mk (re im_i im_j im_k : R) :
    r • (⟨re, im_i, im_j, im_k⟩ : ℍ[R,c₁,c₂]) = ⟨r • re, r • im_i, r • im_j, r • im_k⟩ :=
  rfl

theorem algebra_map_eq (r : R) : algebraMap R ℍ[R,c₁,c₂] r = ⟨r, 0, 0, 0⟩ :=
  rfl

section

variable (R c₁ c₂)

/-- `quaternion_algebra.re` as a `linear_map`-/
@[simps]
def reLm : ℍ[R,c₁,c₂] →ₗ[R] R where
  toFun := re
  map_add' := fun x y => rfl
  map_smul' := fun r x => rfl

/-- `quaternion_algebra.im_i` as a `linear_map`-/
@[simps]
def imILm : ℍ[R,c₁,c₂] →ₗ[R] R where
  toFun := imI
  map_add' := fun x y => rfl
  map_smul' := fun r x => rfl

/-- `quaternion_algebra.im_j` as a `linear_map`-/
@[simps]
def imJLm : ℍ[R,c₁,c₂] →ₗ[R] R where
  toFun := imJ
  map_add' := fun x y => rfl
  map_smul' := fun r x => rfl

/-- `quaternion_algebra.im_k` as a `linear_map`-/
@[simps]
def imKLm : ℍ[R,c₁,c₂] →ₗ[R] R where
  toFun := imK
  map_add' := fun x y => rfl
  map_smul' := fun r x => rfl

end

@[norm_cast, simp]
theorem coe_sub : ((x - y : R) : ℍ[R,c₁,c₂]) = x - y :=
  (algebraMap R ℍ[R,c₁,c₂]).map_sub x y

@[norm_cast, simp]
theorem coe_mul : ((x * y : R) : ℍ[R,c₁,c₂]) = x * y :=
  (algebraMap R ℍ[R,c₁,c₂]).map_mul x y

theorem coe_commutes : ↑r * a = a * r :=
  Algebra.commutes r a

theorem coe_commute : Commute (↑r) a :=
  coe_commutes r a

theorem coe_mul_eq_smul : ↑r * a = r • a :=
  (Algebra.smul_def r a).symm

theorem mul_coe_eq_smul : a * r = r • a := by
  rw [← coe_commutes, coe_mul_eq_smul]

@[norm_cast, simp]
theorem coe_algebra_map : ⇑(algebraMap R ℍ[R,c₁,c₂]) = coe :=
  rfl

theorem smul_coe : x • (y : ℍ[R,c₁,c₂]) = ↑(x * y) := by
  rw [coe_mul, coe_mul_eq_smul]

/-- Quaternion conjugate. -/
def conj : ℍ[R,c₁,c₂] ≃ₗ[R] ℍ[R,c₁,c₂] :=
  (LinearEquiv.ofInvolutive
      { toFun := fun a => ⟨a.1, -a.2, -a.3, -a.4⟩,
        map_add' := fun a b => by
          ext <;> simp [← neg_add],
        map_smul' := fun r a => by
          ext <;> simp })
    fun a => by
    simp

@[simp]
theorem re_conj : (conj a).re = a.re :=
  rfl

@[simp]
theorem im_i_conj : (conj a).imI = -a.imI :=
  rfl

@[simp]
theorem im_j_conj : (conj a).imJ = -a.imJ :=
  rfl

@[simp]
theorem im_k_conj : (conj a).imK = -a.imK :=
  rfl

@[simp]
theorem conj_mk (a₁ a₂ a₃ a₄ : R) : conj (mk a₁ a₂ a₃ a₄ : ℍ[R,c₁,c₂]) = ⟨a₁, -a₂, -a₃, -a₄⟩ :=
  rfl

@[simp]
theorem conj_conj : a.conj.conj = a :=
  ext _ _ rfl (neg_negₓ _) (neg_negₓ _) (neg_negₓ _)

theorem conj_add : (a + b).conj = a.conj + b.conj :=
  conj.map_add a b

@[simp]
theorem conj_mul : (a * b).conj = b.conj * a.conj := by
  ext <;> simp <;> ring_exp

theorem conj_conj_mul : (a.conj * b).conj = b.conj * a := by
  rw [conj_mul, conj_conj]

theorem conj_mul_conj : (a * b.conj).conj = b * a.conj := by
  rw [conj_mul, conj_conj]

theorem self_add_conj' : a + a.conj = ↑(2 * a.re) := by
  ext <;> simp [← two_mul]

theorem self_add_conj : a + a.conj = 2 * a.re := by
  simp only [← self_add_conj', ← two_mul, ← coe_add]

theorem conj_add_self' : a.conj + a = ↑(2 * a.re) := by
  rw [add_commₓ, self_add_conj']

theorem conj_add_self : a.conj + a = 2 * a.re := by
  rw [add_commₓ, self_add_conj]

theorem conj_eq_two_re_sub : a.conj = ↑(2 * a.re) - a :=
  eq_sub_iff_add_eq.2 a.conj_add_self'

theorem commute_conj_self : Commute a.conj a := by
  rw [a.conj_eq_two_re_sub]
  exact (coe_commute (2 * a.re) a).subLeft (Commute.refl a)

theorem commute_self_conj : Commute a a.conj :=
  a.commute_conj_self.symm

theorem commute_conj_conj {a b : ℍ[R,c₁,c₂]} (h : Commute a b) : Commute a.conj b.conj :=
  calc
    a.conj * b.conj = (b * a).conj := (conj_mul b a).symm
    _ = (a * b).conj := by
      rw [h.eq]
    _ = b.conj * a.conj := conj_mul a b
    

@[simp]
theorem conj_coe : conj (x : ℍ[R,c₁,c₂]) = x := by
  ext <;> simp

theorem conj_smul : conj (r • a) = r • conj a :=
  conj.map_smul r a

@[simp]
theorem conj_one : conj (1 : ℍ[R,c₁,c₂]) = 1 :=
  conj_coe 1

theorem eq_re_of_eq_coe {a : ℍ[R,c₁,c₂]} {x : R} (h : a = x) : a = a.re := by
  rw [h, coe_re]

theorem eq_re_iff_mem_range_coe {a : ℍ[R,c₁,c₂]} : a = a.re ↔ a ∈ Set.Range (coe : R → ℍ[R,c₁,c₂]) :=
  ⟨fun h => ⟨a.re, h.symm⟩, fun ⟨x, h⟩ => eq_re_of_eq_coe h.symm⟩

@[simp]
theorem conj_fixed {R : Type _} [CommRingₓ R] [NoZeroDivisors R] [CharZero R] {c₁ c₂ : R} {a : ℍ[R,c₁,c₂]} :
    conj a = a ↔ a = a.re := by
  simp [← ext_iff, ← neg_eq_iff_add_eq_zero, ← add_self_eq_zero]

-- Can't use `rw ← conj_fixed` in the proof without additional assumptions
theorem conj_mul_eq_coe : conj a * a = (conj a * a).re := by
  ext <;> simp <;> ring_exp

theorem mul_conj_eq_coe : a * conj a = (a * conj a).re := by
  rw [a.commute_self_conj.eq]
  exact a.conj_mul_eq_coe

theorem conj_zero : conj (0 : ℍ[R,c₁,c₂]) = 0 :=
  conj.map_zero

theorem conj_neg : (-a).conj = -a.conj :=
  (conj : ℍ[R,c₁,c₂] ≃ₗ[R] _).map_neg a

theorem conj_sub : (a - b).conj = a.conj - b.conj :=
  (conj : ℍ[R,c₁,c₂] ≃ₗ[R] _).map_sub a b

instance : StarRing ℍ[R,c₁,c₂] where
  star := conj
  star_involutive := conj_conj
  star_add := conj_add
  star_mul := conj_mul

@[simp]
theorem star_def (a : ℍ[R,c₁,c₂]) : star a = conj a :=
  rfl

open MulOpposite

/-- Quaternion conjugate as an `alg_equiv` to the opposite ring. -/
def conjAe : ℍ[R,c₁,c₂] ≃ₐ[R] ℍ[R,c₁,c₂]ᵐᵒᵖ :=
  { conj.toAddEquiv.trans opAddEquiv with toFun := op ∘ conj, invFun := conj ∘ unop,
    map_mul' := fun x y => by
      simp ,
    commutes' := fun r => by
      simp }

@[simp]
theorem coe_conj_ae : ⇑(conjAe : ℍ[R,c₁,c₂] ≃ₐ[R] _) = op ∘ conj :=
  rfl

end QuaternionAlgebra

/-- Space of quaternions over a type. Implemented as a structure with four fields:
`re`, `im_i`, `im_j`, and `im_k`. -/
def Quaternion (R : Type _) [One R] [Neg R] :=
  QuaternionAlgebra R (-1) (-1)

-- mathport name: «exprℍ[ ]»
localized [Quaternion] notation "ℍ[" R "]" => Quaternion R

/-- The equivalence between the quaternions over R and R × R × R × R. -/
def Quaternion.equivProd (R : Type _) [One R] [Neg R] : ℍ[R] ≃ R × R × R × R :=
  QuaternionAlgebra.equivProd _ _

namespace Quaternion

variable {R : Type _} [CommRingₓ R] (r x y z : R) (a b c : ℍ[R])

export QuaternionAlgebra (re imI imJ imK)

instance : CoeTₓ R ℍ[R] :=
  QuaternionAlgebra.hasCoeT

instance : Ringₓ ℍ[R] :=
  QuaternionAlgebra.ring

instance : Inhabited ℍ[R] :=
  QuaternionAlgebra.inhabited

instance : Algebra R ℍ[R] :=
  QuaternionAlgebra.algebra

instance : StarRing ℍ[R] :=
  QuaternionAlgebra.starRing

@[ext]
theorem ext : a.re = b.re → a.imI = b.imI → a.imJ = b.imJ → a.imK = b.imK → a = b :=
  QuaternionAlgebra.ext a b

theorem ext_iff {a b : ℍ[R]} : a = b ↔ a.re = b.re ∧ a.imI = b.imI ∧ a.imJ = b.imJ ∧ a.imK = b.imK :=
  QuaternionAlgebra.ext_iff a b

@[simp, norm_cast]
theorem coe_re : (x : ℍ[R]).re = x :=
  rfl

@[simp, norm_cast]
theorem coe_im_i : (x : ℍ[R]).imI = 0 :=
  rfl

@[simp, norm_cast]
theorem coe_im_j : (x : ℍ[R]).imJ = 0 :=
  rfl

@[simp, norm_cast]
theorem coe_im_k : (x : ℍ[R]).imK = 0 :=
  rfl

@[simp]
theorem zero_re : (0 : ℍ[R]).re = 0 :=
  rfl

@[simp]
theorem zero_im_i : (0 : ℍ[R]).imI = 0 :=
  rfl

@[simp]
theorem zero_im_j : (0 : ℍ[R]).imJ = 0 :=
  rfl

@[simp]
theorem zero_im_k : (0 : ℍ[R]).imK = 0 :=
  rfl

@[simp, norm_cast]
theorem coe_zero : ((0 : R) : ℍ[R]) = 0 :=
  rfl

@[simp]
theorem one_re : (1 : ℍ[R]).re = 1 :=
  rfl

@[simp]
theorem one_im_i : (1 : ℍ[R]).imI = 0 :=
  rfl

@[simp]
theorem one_im_j : (1 : ℍ[R]).imJ = 0 :=
  rfl

@[simp]
theorem one_im_k : (1 : ℍ[R]).imK = 0 :=
  rfl

@[simp, norm_cast]
theorem coe_one : ((1 : R) : ℍ[R]) = 1 :=
  rfl

@[simp]
theorem add_re : (a + b).re = a.re + b.re :=
  rfl

@[simp]
theorem add_im_i : (a + b).imI = a.imI + b.imI :=
  rfl

@[simp]
theorem add_im_j : (a + b).imJ = a.imJ + b.imJ :=
  rfl

@[simp]
theorem add_im_k : (a + b).imK = a.imK + b.imK :=
  rfl

@[simp, norm_cast]
theorem coe_add : ((x + y : R) : ℍ[R]) = x + y :=
  QuaternionAlgebra.coe_add x y

@[simp]
theorem neg_re : (-a).re = -a.re :=
  rfl

@[simp]
theorem neg_im_i : (-a).imI = -a.imI :=
  rfl

@[simp]
theorem neg_im_j : (-a).imJ = -a.imJ :=
  rfl

@[simp]
theorem neg_im_k : (-a).imK = -a.imK :=
  rfl

@[simp, norm_cast]
theorem coe_neg : ((-x : R) : ℍ[R]) = -x :=
  QuaternionAlgebra.coe_neg x

@[simp]
theorem sub_re : (a - b).re = a.re - b.re :=
  rfl

@[simp]
theorem sub_im_i : (a - b).imI = a.imI - b.imI :=
  rfl

@[simp]
theorem sub_im_j : (a - b).imJ = a.imJ - b.imJ :=
  rfl

@[simp]
theorem sub_im_k : (a - b).imK = a.imK - b.imK :=
  rfl

@[simp, norm_cast]
theorem coe_sub : ((x - y : R) : ℍ[R]) = x - y :=
  QuaternionAlgebra.coe_sub x y

@[simp]
theorem mul_re : (a * b).re = a.re * b.re - a.imI * b.imI - a.imJ * b.imJ - a.imK * b.imK :=
  (QuaternionAlgebra.has_mul_mul_re a b).trans <| by
    simp only [← one_mulₓ, ← neg_mul, ← sub_eq_add_neg, ← neg_negₓ]

@[simp]
theorem mul_im_i : (a * b).imI = a.re * b.imI + a.imI * b.re + a.imJ * b.imK - a.imK * b.imJ :=
  (QuaternionAlgebra.has_mul_mul_im_i a b).trans <| by
    simp only [← one_mulₓ, ← neg_mul, ← sub_eq_add_neg, ← neg_negₓ]

@[simp]
theorem mul_im_j : (a * b).imJ = a.re * b.imJ - a.imI * b.imK + a.imJ * b.re + a.imK * b.imI :=
  (QuaternionAlgebra.has_mul_mul_im_j a b).trans <| by
    simp only [← one_mulₓ, ← neg_mul, ← sub_eq_add_neg, ← neg_negₓ]

@[simp]
theorem mul_im_k : (a * b).imK = a.re * b.imK + a.imI * b.imJ - a.imJ * b.imI + a.imK * b.re :=
  (QuaternionAlgebra.has_mul_mul_im_k a b).trans <| by
    simp only [← one_mulₓ, ← neg_mul, ← sub_eq_add_neg, ← neg_negₓ]

@[simp, norm_cast]
theorem coe_mul : ((x * y : R) : ℍ[R]) = x * y :=
  QuaternionAlgebra.coe_mul x y

theorem coe_injective : Function.Injective (coe : R → ℍ[R]) :=
  QuaternionAlgebra.coe_injective

@[simp]
theorem coe_inj {x y : R} : (x : ℍ[R]) = y ↔ x = y :=
  coe_injective.eq_iff

@[simp]
theorem smul_re : (r • a).re = r • a.re :=
  rfl

@[simp]
theorem smul_im_i : (r • a).imI = r • a.imI :=
  rfl

@[simp]
theorem smul_im_j : (r • a).imJ = r • a.imJ :=
  rfl

@[simp]
theorem smul_im_k : (r • a).imK = r • a.imK :=
  rfl

theorem coe_commutes : ↑r * a = a * r :=
  QuaternionAlgebra.coe_commutes r a

theorem coe_commute : Commute (↑r) a :=
  QuaternionAlgebra.coe_commute r a

theorem coe_mul_eq_smul : ↑r * a = r • a :=
  QuaternionAlgebra.coe_mul_eq_smul r a

theorem mul_coe_eq_smul : a * r = r • a :=
  QuaternionAlgebra.mul_coe_eq_smul r a

@[simp]
theorem algebra_map_def : ⇑(algebraMap R ℍ[R]) = coe :=
  rfl

theorem smul_coe : x • (y : ℍ[R]) = ↑(x * y) :=
  QuaternionAlgebra.smul_coe x y

/-- Quaternion conjugate. -/
def conj : ℍ[R] ≃ₗ[R] ℍ[R] :=
  QuaternionAlgebra.conj

@[simp]
theorem conj_re : a.conj.re = a.re :=
  rfl

@[simp]
theorem conj_im_i : a.conj.imI = -a.imI :=
  rfl

@[simp]
theorem conj_im_j : a.conj.imJ = -a.imJ :=
  rfl

@[simp]
theorem conj_im_k : a.conj.imK = -a.imK :=
  rfl

@[simp]
theorem conj_conj : a.conj.conj = a :=
  a.conj_conj

@[simp]
theorem conj_add : (a + b).conj = a.conj + b.conj :=
  a.conj_add b

@[simp]
theorem conj_mul : (a * b).conj = b.conj * a.conj :=
  a.conj_mul b

theorem conj_conj_mul : (a.conj * b).conj = b.conj * a :=
  a.conj_conj_mul b

theorem conj_mul_conj : (a * b.conj).conj = b * a.conj :=
  a.conj_mul_conj b

theorem self_add_conj' : a + a.conj = ↑(2 * a.re) :=
  a.self_add_conj'

theorem self_add_conj : a + a.conj = 2 * a.re :=
  a.self_add_conj

theorem conj_add_self' : a.conj + a = ↑(2 * a.re) :=
  a.conj_add_self'

theorem conj_add_self : a.conj + a = 2 * a.re :=
  a.conj_add_self

theorem conj_eq_two_re_sub : a.conj = ↑(2 * a.re) - a :=
  a.conj_eq_two_re_sub

theorem commute_conj_self : Commute a.conj a :=
  a.commute_conj_self

theorem commute_self_conj : Commute a a.conj :=
  a.commute_self_conj

theorem commute_conj_conj {a b : ℍ[R]} (h : Commute a b) : Commute a.conj b.conj :=
  QuaternionAlgebra.commute_conj_conj h

alias commute_conj_conj ← commute.quaternion_conj

@[simp]
theorem conj_coe : conj (x : ℍ[R]) = x :=
  QuaternionAlgebra.conj_coe x

@[simp]
theorem conj_smul : conj (r • a) = r • conj a :=
  a.conj_smul r

@[simp]
theorem conj_one : conj (1 : ℍ[R]) = 1 :=
  conj_coe 1

theorem eq_re_of_eq_coe {a : ℍ[R]} {x : R} (h : a = x) : a = a.re :=
  QuaternionAlgebra.eq_re_of_eq_coe h

theorem eq_re_iff_mem_range_coe {a : ℍ[R]} : a = a.re ↔ a ∈ Set.Range (coe : R → ℍ[R]) :=
  QuaternionAlgebra.eq_re_iff_mem_range_coe

@[simp]
theorem conj_fixed {R : Type _} [CommRingₓ R] [NoZeroDivisors R] [CharZero R] {a : ℍ[R]} : conj a = a ↔ a = a.re :=
  QuaternionAlgebra.conj_fixed

theorem conj_mul_eq_coe : conj a * a = (conj a * a).re :=
  a.conj_mul_eq_coe

theorem mul_conj_eq_coe : a * conj a = (a * conj a).re :=
  a.mul_conj_eq_coe

@[simp]
theorem conj_zero : conj (0 : ℍ[R]) = 0 :=
  QuaternionAlgebra.conj_zero

@[simp]
theorem conj_neg : (-a).conj = -a.conj :=
  a.conj_neg

@[simp]
theorem conj_sub : (a - b).conj = a.conj - b.conj :=
  a.conj_sub b

open MulOpposite

/-- Quaternion conjugate as an `alg_equiv` to the opposite ring. -/
def conjAe : ℍ[R] ≃ₐ[R] ℍ[R]ᵐᵒᵖ :=
  QuaternionAlgebra.conjAe

@[simp]
theorem coe_conj_ae : ⇑(conjAe : ℍ[R] ≃ₐ[R] ℍ[R]ᵐᵒᵖ) = op ∘ conj :=
  rfl

/-- Square of the norm. -/
def normSq : ℍ[R] →*₀ R where
  toFun := fun a => (a * a.conj).re
  map_zero' := by
    rw [conj_zero, zero_mul, zero_re]
  map_one' := by
    rw [conj_one, one_mulₓ, one_re]
  map_mul' := fun x y =>
    coe_injective <| by
      conv_lhs =>
        rw [← mul_conj_eq_coe, conj_mul, mul_assoc, ← mul_assoc y, y.mul_conj_eq_coe, coe_commutes, ← mul_assoc,
          x.mul_conj_eq_coe, ← coe_mul]

theorem norm_sq_def : normSq a = (a * a.conj).re :=
  rfl

theorem norm_sq_def' : normSq a = a.1 ^ 2 + a.2 ^ 2 + a.3 ^ 2 + a.4 ^ 2 := by
  simp only [← norm_sq_def, ← sq, ← mul_neg, ← sub_neg_eq_add, ← mul_re, ← conj_re, ← conj_im_i, ← conj_im_j, ←
    conj_im_k]

theorem norm_sq_coe : normSq (x : ℍ[R]) = x ^ 2 := by
  rw [norm_sq_def, conj_coe, ← coe_mul, coe_re, sq]

@[simp]
theorem norm_sq_neg : normSq (-a) = normSq a := by
  simp only [← norm_sq_def, ← conj_neg, ← neg_mul_neg]

theorem self_mul_conj : a * a.conj = normSq a := by
  rw [mul_conj_eq_coe, norm_sq_def]

theorem conj_mul_self : a.conj * a = normSq a := by
  rw [← a.commute_self_conj.eq, self_mul_conj]

theorem coe_norm_sq_add : (normSq (a + b) : ℍ[R]) = normSq a + a * b.conj + b * a.conj + normSq b := by
  simp [self_mul_conj, ← mul_addₓ, ← add_mulₓ, ← add_assocₓ]

end Quaternion

namespace Quaternion

variable {R : Type _}

section LinearOrderedCommRing

variable [LinearOrderedCommRing R] {a : ℍ[R]}

-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:63:9: parse error
@[simp]
theorem norm_sq_eq_zero : normSq a = 0 ↔ a = 0 := by
  refine' ⟨fun h => _, fun h => h.symm ▸ norm_sq.map_zero⟩
  rw [norm_sq_def', add_eq_zero_iff', add_eq_zero_iff', add_eq_zero_iff'] at h
  exact ext a 0 (pow_eq_zero h.1.1.1) (pow_eq_zero h.1.1.2) (pow_eq_zero h.1.2) (pow_eq_zero h.2)
  all_goals
    apply_rules [sq_nonneg, add_nonneg]

theorem norm_sq_ne_zero : normSq a ≠ 0 ↔ a ≠ 0 :=
  not_congr norm_sq_eq_zero

-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:63:9: parse error
@[simp]
theorem norm_sq_nonneg : 0 ≤ normSq a := by
  rw [norm_sq_def']
  apply_rules [sq_nonneg, add_nonneg]

@[simp]
theorem norm_sq_le_zero : normSq a ≤ 0 ↔ a = 0 := by
  simpa only [← le_antisymm_iffₓ, ← norm_sq_nonneg, ← and_trueₓ] using @norm_sq_eq_zero _ _ a

instance : Nontrivial ℍ[R] where exists_pair_ne := ⟨0, 1, mt (congr_arg re) zero_ne_one⟩

instance : IsDomain ℍ[R] :=
  { Quaternion.nontrivial with
    eq_zero_or_eq_zero_of_mul_eq_zero := fun a b hab =>
      have : normSq a * normSq b = 0 := by
        rwa [← norm_sq.map_mul, norm_sq_eq_zero]
      (eq_zero_or_eq_zero_of_mul_eq_zero this).imp norm_sq_eq_zero.1 norm_sq_eq_zero.1 }

end LinearOrderedCommRing

section Field

variable [LinearOrderedField R] (a b : ℍ[R])

@[simps (config := { attrs := [] })]
instance : Inv ℍ[R] :=
  ⟨fun a => (normSq a)⁻¹ • a.conj⟩

instance : DivisionRing ℍ[R] :=
  { Quaternion.nontrivial, Quaternion.ring with inv := Inv.inv,
    inv_zero := by
      rw [has_inv_inv, conj_zero, smul_zero],
    mul_inv_cancel := fun a ha => by
      rw [has_inv_inv, Algebra.mul_smul_comm, self_mul_conj, smul_coe, inv_mul_cancel (norm_sq_ne_zero.2 ha), coe_one] }

@[simp]
theorem norm_sq_inv : normSq a⁻¹ = (normSq a)⁻¹ :=
  MonoidWithZeroHom.map_inv normSq _

@[simp]
theorem norm_sq_div : normSq (a / b) = normSq a / normSq b :=
  MonoidWithZeroHom.map_div normSq a b

end Field

end Quaternion

namespace Cardinal

open Cardinal Quaternion

section QuaternionAlgebra

variable {R : Type _} (c₁ c₂ : R)

private theorem pow_four [Infinite R] : # R ^ 4 = # R :=
  power_nat_eq (aleph_0_le_mk R) <| by
    simp

/-- The cardinality of a quaternion algebra, as a type. -/
theorem mk_quaternion_algebra : # ℍ[R,c₁,c₂] = # R ^ 4 := by
  rw [mk_congr (QuaternionAlgebra.equivProd c₁ c₂)]
  simp only [← mk_prod, ← lift_id]
  ring

@[simp]
theorem mk_quaternion_algebra_of_infinite [Infinite R] : # ℍ[R,c₁,c₂] = # R := by
  rw [mk_quaternion_algebra, pow_four]

/-- The cardinality of a quaternion algebra, as a set. -/
theorem mk_univ_quaternion_algebra : # (Set.Univ : Set ℍ[R,c₁,c₂]) = # R ^ 4 := by
  rw [mk_univ, mk_quaternion_algebra]

@[simp]
theorem mk_univ_quaternion_algebra_of_infinite [Infinite R] : # (Set.Univ : Set ℍ[R,c₁,c₂]) = # R := by
  rw [mk_univ_quaternion_algebra, pow_four]

end QuaternionAlgebra

section Quaternion

variable (R : Type _) [One R] [Neg R]

/-- The cardinality of the quaternions, as a type. -/
@[simp]
theorem mk_quaternion : # ℍ[R] = # R ^ 4 :=
  mk_quaternion_algebra _ _

@[simp]
theorem mk_quaternion_of_infinite [Infinite R] : # ℍ[R] = # R := by
  rw [mk_quaternion, pow_four]

/-- The cardinality of the quaternions, as a set. -/
@[simp]
theorem mk_univ_quaternion : # (Set.Univ : Set ℍ[R]) = # R ^ 4 :=
  mk_univ_quaternion_algebra _ _

@[simp]
theorem mk_univ_quaternion_of_infinite [Infinite R] : # (Set.Univ : Set ℍ[R]) = # R := by
  rw [mk_univ_quaternion, pow_four]

end Quaternion

end Cardinal

