/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import Mathbin.LinearAlgebra.Matrix.Adjugate
import Mathbin.LinearAlgebra.Matrix.ToLin

/-!
# The Special Linear group $SL(n, R)$

This file defines the elements of the Special Linear group `special_linear_group n R`, consisting
of all square `R`-matrices with determinant `1` on the fintype `n` by `n`.  In addition, we define
the group structure on `special_linear_group n R` and the embedding into the general linear group
`general_linear_group R (n → R)`.

## Main definitions

 * `matrix.special_linear_group` is the type of matrices with determinant 1
 * `matrix.special_linear_group.group` gives the group structure (under multiplication)
 * `matrix.special_linear_group.to_GL` is the embedding `SLₙ(R) → GLₙ(R)`

## Notation

For `m : ℕ`, we introduce the notation `SL(m,R)` for the special linear group on the fintype
`n = fin m`, in the locale `matrix_groups`.

## Implementation notes
The inverse operation in the `special_linear_group` is defined to be the adjugate
matrix, so that `special_linear_group n R` has a group structure for all `comm_ring R`.

We define the elements of `special_linear_group` to be matrices, since we need to
compute their determinant. This is in contrast with `general_linear_group R M`,
which consists of invertible `R`-linear maps on `M`.

We provide `matrix.special_linear_group.has_coe_to_fun` for convenience, but do not state any
lemmas about it, and use `matrix.special_linear_group.coe_fn_eq_coe` to eliminate it `⇑` in favor
of a regular `↑` coercion.

## References

 * https://en.wikipedia.org/wiki/Special_linear_group

## Tags

matrix group, group, matrix inverse
-/


namespace Matrix

universe u v

open Matrix

open LinearMap

section

variable (n : Type u) [DecidableEq n] [Fintype n] (R : Type v) [CommRingₓ R]

/-- `special_linear_group n R` is the group of `n` by `n` `R`-matrices with determinant equal to 1.
-/
def SpecialLinearGroup :=
  { A : Matrix n n R // A.det = 1 }

end

-- mathport name: «exprSL( , )»
localized [MatrixGroups] notation "SL(" n "," R ")" => Matrix.SpecialLinearGroup (Finₓ n) R

namespace SpecialLinearGroup

variable {n : Type u} [DecidableEq n] [Fintype n] {R : Type v} [CommRingₓ R]

instance hasCoeToMatrix : Coe (SpecialLinearGroup n R) (Matrix n n R) :=
  ⟨fun A => A.val⟩

-- mathport name: «expr↑ₘ »
/- In this file, Lean often has a hard time working out the values of `n` and `R` for an expression
like `det ↑A`. Rather than writing `(A : matrix n n R)` everywhere in this file which is annoyingly
verbose, or `A.val` which is not the simp-normal form for subtypes, we create a local notation
`↑ₘA`. This notation references the local `n` and `R` variables, so is not valid as a global
notation. -/
local prefix:1024 "↑ₘ" => @coe _ (Matrix n n R) _

theorem ext_iff (A B : SpecialLinearGroup n R) : A = B ↔ ∀ i j, ↑ₘA i j = ↑ₘB i j :=
  Subtype.ext_iff.trans Matrix.ext_iff.symm

@[ext]
theorem ext (A B : SpecialLinearGroup n R) : (∀ i j, ↑ₘA i j = ↑ₘB i j) → A = B :=
  (SpecialLinearGroup.ext_iff A B).mpr

instance hasInv : Inv (SpecialLinearGroup n R) :=
  ⟨fun A =>
    ⟨adjugate A, by
      rw [det_adjugate, A.prop, one_pow]⟩⟩

instance hasMul : Mul (SpecialLinearGroup n R) :=
  ⟨fun A B =>
    ⟨A.1 ⬝ B.1, by
      erw [det_mul, A.2, B.2, one_mulₓ]⟩⟩

instance hasOne : One (SpecialLinearGroup n R) :=
  ⟨⟨1, det_one⟩⟩

instance :
    Pow (SpecialLinearGroup n R) ℕ where pow := fun x n => ⟨x ^ n, (det_pow _ _).trans <| x.Prop.symm ▸ one_pow _⟩

instance : Inhabited (SpecialLinearGroup n R) :=
  ⟨1⟩

section CoeLemmas

variable (A B : SpecialLinearGroup n R)

@[simp]
theorem coe_mk (A : Matrix n n R) (h : det A = 1) : ↑(⟨A, h⟩ : SpecialLinearGroup n R) = A :=
  rfl

@[simp]
theorem coe_inv : ↑ₘA⁻¹ = adjugate A :=
  rfl

@[simp]
theorem coe_mul : ↑ₘ(A * B) = ↑ₘA ⬝ ↑ₘB :=
  rfl

@[simp]
theorem coe_one : ↑ₘ(1 : SpecialLinearGroup n R) = (1 : Matrix n n R) :=
  rfl

@[simp]
theorem det_coe : det ↑ₘA = 1 :=
  A.2

@[simp]
theorem coe_pow (m : ℕ) : ↑ₘ(A ^ m) = ↑ₘA ^ m :=
  rfl

theorem det_ne_zero [Nontrivial R] (g : SpecialLinearGroup n R) : det ↑ₘg ≠ 0 := by
  rw [g.det_coe]
  norm_num

theorem row_ne_zero [Nontrivial R] (g : SpecialLinearGroup n R) (i : n) : ↑ₘg i ≠ 0 := fun h =>
  g.det_ne_zero <|
    det_eq_zero_of_row_eq_zero i <| by
      simp [← h]

end CoeLemmas

instance : Monoidₓ (SpecialLinearGroup n R) :=
  Function.Injective.monoid coe Subtype.coe_injective coe_one coe_mul coe_pow

instance : Groupₓ (SpecialLinearGroup n R) :=
  { SpecialLinearGroup.monoid, SpecialLinearGroup.hasInv with
    mul_left_inv := fun A => by
      ext1
      simp [← adjugate_mul] }

/-- A version of `matrix.to_lin' A` that produces linear equivalences. -/
def toLin' : SpecialLinearGroup n R →* (n → R) ≃ₗ[R] n → R where
  toFun := fun A =>
    LinearEquiv.ofLinear (Matrix.toLin' ↑ₘA) (Matrix.toLin' ↑ₘA⁻¹)
      (by
        rw [← to_lin'_mul, ← coe_mul, mul_right_invₓ, coe_one, to_lin'_one])
      (by
        rw [← to_lin'_mul, ← coe_mul, mul_left_invₓ, coe_one, to_lin'_one])
  map_one' := LinearEquiv.to_linear_map_injective Matrix.to_lin'_one
  map_mul' := fun A B => LinearEquiv.to_linear_map_injective <| Matrix.to_lin'_mul A B

theorem to_lin'_apply (A : SpecialLinearGroup n R) (v : n → R) :
    SpecialLinearGroup.toLin' A v = Matrix.toLin' (↑ₘA) v :=
  rfl

theorem to_lin'_to_linear_map (A : SpecialLinearGroup n R) : ↑(SpecialLinearGroup.toLin' A) = Matrix.toLin' ↑ₘA :=
  rfl

theorem to_lin'_symm_apply (A : SpecialLinearGroup n R) (v : n → R) : A.toLin'.symm v = Matrix.toLin' (↑ₘA⁻¹) v :=
  rfl

theorem to_lin'_symm_to_linear_map (A : SpecialLinearGroup n R) : ↑A.toLin'.symm = Matrix.toLin' ↑ₘA⁻¹ :=
  rfl

theorem to_lin'_injective : Function.Injective ⇑(toLin' : SpecialLinearGroup n R →* (n → R) ≃ₗ[R] n → R) := fun A B h =>
  Subtype.coe_injective <| Matrix.toLin'.Injective <| LinearEquiv.to_linear_map_injective.eq_iff.mpr h

/-- `to_GL` is the map from the special linear group to the general linear group -/
def toGL : SpecialLinearGroup n R →* GeneralLinearGroup R (n → R) :=
  (GeneralLinearGroup.generalLinearEquiv _ _).symm.toMonoidHom.comp toLin'

theorem coe_to_GL (A : SpecialLinearGroup n R) : ↑A.toGL = A.toLin'.toLinearMap :=
  rfl

variable {S : Type _} [CommRingₓ S]

/-- A ring homomorphism from `R` to `S` induces a group homomorphism from
`special_linear_group n R` to `special_linear_group n S`. -/
@[simps]
def map (f : R →+* S) : SpecialLinearGroup n R →* SpecialLinearGroup n S where
  toFun := fun g =>
    ⟨f.mapMatrix ↑g, by
      rw [← f.map_det]
      simp [← g.2]⟩
  map_one' := Subtype.ext <| f.mapMatrix.map_one
  map_mul' := fun x y => Subtype.ext <| f.mapMatrix.map_mul x y

section cast

/-- Coercion of SL `n` `ℤ` to SL `n` `R` for a commutative ring `R`. -/
instance : Coe (SpecialLinearGroup n ℤ) (SpecialLinearGroup n R) :=
  ⟨fun x => map (Int.castRingHom R) x⟩

@[simp]
theorem coe_matrix_coe (g : SpecialLinearGroup n ℤ) :
    ↑(g : SpecialLinearGroup n R) = (↑g : Matrix n n ℤ).map (Int.castRingHom R) :=
  map_apply_coe (Int.castRingHom R) g

end cast

section Neg

variable [Fact (Even (Fintype.card n))]

/-- Formal operation of negation on special linear group on even cardinality `n` given by negating
each element. -/
instance : Neg (SpecialLinearGroup n R) :=
  ⟨fun g =>
    ⟨-g, by
      simpa [← (Fact.out <| Even <| Fintype.card n).neg_one_pow, ← g.det_coe] using det_smul (↑ₘg) (-1)⟩⟩

@[simp]
theorem coe_neg (g : SpecialLinearGroup n R) : ↑(-g) = -(g : Matrix n n R) :=
  rfl

instance : HasDistribNeg (SpecialLinearGroup n R) :=
  Function.Injective.hasDistribNeg _ Subtype.coe_injective coe_neg coe_mul

@[simp]
theorem coe_int_neg (g : SpecialLinearGroup n ℤ) : ↑(-g) = (-↑g : SpecialLinearGroup n R) :=
  Subtype.ext <| (@RingHom.mapMatrix n _ _ _ _ _ _ (Int.castRingHom R)).map_neg ↑g

end Neg

-- this section should be last to ensure we do not use it in lemmas
section CoeFnInstance

/-- This instance is here for convenience, but is not the simp-normal form. -/
instance : CoeFun (SpecialLinearGroup n R) fun _ => n → n → R where coe := fun A => A.val

@[simp]
theorem coe_fn_eq_coe (s : SpecialLinearGroup n R) : ⇑s = ↑ₘs :=
  rfl

end CoeFnInstance

end SpecialLinearGroup

end Matrix

