/-
Copyright (c) 2018 Andreas Swerdlow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andreas Swerdlow, Kexing Ying
-/
import Mathbin.LinearAlgebra.Dual
import Mathbin.LinearAlgebra.Matrix.ToLin
import Mathbin.LinearAlgebra.TensorProduct

/-!
# Bilinear form

This file defines a bilinear form over a module. Basic ideas
such as orthogonality are also introduced, as well as reflexivive,
symmetric, non-degenerate and alternating bilinear forms. Adjoints of
linear maps with respect to a bilinear form are also introduced.

A bilinear form on an R-(semi)module M, is a function from M x M to R,
that is linear in both arguments. Comments will typically abbreviate
"(semi)module" as just "module", but the definitions should be as general as
possible.

The result that there exists an orthogonal basis with respect to a symmetric,
nondegenerate bilinear form can be found in `quadratic_form.lean` with
`exists_orthogonal_basis`.

## Notations

Given any term B of type bilin_form, due to a coercion, can use
the notation B x y to refer to the function field, ie. B x y = B.bilin x y.

In this file we use the following type variables:
 - `M`, `M'`, ... are modules over the semiring `R`,
 - `M₁`, `M₁'`, ... are modules over the ring `R₁`,
 - `M₂`, `M₂'`, ... are modules over the commutative semiring `R₂`,
 - `M₃`, `M₃'`, ... are modules over the commutative ring `R₃`,
 - `V`, ... is a vector space over the field `K`.

## References

* <https://en.wikipedia.org/wiki/Bilinear_form>

## Tags

Bilinear form,
-/


open BigOperators

universe u v w

/-- `bilin_form R M` is the type of `R`-bilinear functions `M → M → R`. -/
structure BilinForm (R : Type _) (M : Type _) [Semiringₓ R] [AddCommMonoidₓ M] [Module R M] where
  bilin : M → M → R
  bilin_add_left : ∀ x y z : M, bilin (x + y) z = bilin x z + bilin y z
  bilin_smul_left : ∀ (a : R) (x y : M), bilin (a • x) y = a * bilin x y
  bilin_add_right : ∀ x y z : M, bilin x (y + z) = bilin x y + bilin x z
  bilin_smul_right : ∀ (a : R) (x y : M), bilin x (a • y) = a * bilin x y

variable {R : Type _} {M : Type _} [Semiringₓ R] [AddCommMonoidₓ M] [Module R M]

variable {R₁ : Type _} {M₁ : Type _} [Ringₓ R₁] [AddCommGroupₓ M₁] [Module R₁ M₁]

variable {R₂ : Type _} {M₂ : Type _} [CommSemiringₓ R₂] [AddCommMonoidₓ M₂] [Module R₂ M₂]

variable {R₃ : Type _} {M₃ : Type _} [CommRingₓ R₃] [AddCommGroupₓ M₃] [Module R₃ M₃]

variable {V : Type _} {K : Type _} [Field K] [AddCommGroupₓ V] [Module K V]

variable {B : BilinForm R M} {B₁ : BilinForm R₁ M₁} {B₂ : BilinForm R₂ M₂}

namespace BilinForm

instance : CoeFun (BilinForm R M) fun _ => M → M → R :=
  ⟨bilin⟩

initialize_simps_projections BilinForm (bilin → apply)

@[simp]
theorem coe_fn_mk (f : M → M → R) (h₁ h₂ h₃ h₄) : (BilinForm.mk f h₁ h₂ h₃ h₄ : M → M → R) = f :=
  rfl

theorem coe_fn_congr : ∀ {x x' y y' : M}, x = x' → y = y' → B x y = B x' y'
  | _, _, _, _, rfl, rfl => rfl

@[simp]
theorem add_left (x y z : M) : B (x + y) z = B x z + B y z :=
  bilin_add_left B x y z

@[simp]
theorem smul_left (a : R) (x y : M) : B (a • x) y = a * B x y :=
  bilin_smul_left B a x y

@[simp]
theorem add_right (x y z : M) : B x (y + z) = B x y + B x z :=
  bilin_add_right B x y z

@[simp]
theorem smul_right (a : R) (x y : M) : B x (a • y) = a * B x y :=
  bilin_smul_right B a x y

@[simp]
theorem zero_left (x : M) : B 0 x = 0 := by
  rw [← @zero_smul R _ _ _ _ (0 : M), smul_left, zero_mul]

@[simp]
theorem zero_right (x : M) : B x 0 = 0 := by
  rw [← @zero_smul _ _ _ _ _ (0 : M), smul_right, zero_mul]

@[simp]
theorem neg_left (x y : M₁) : B₁ (-x) y = -B₁ x y := by
  rw [← @neg_one_smul R₁ _ _, smul_left, neg_one_mul]

@[simp]
theorem neg_right (x y : M₁) : B₁ x (-y) = -B₁ x y := by
  rw [← @neg_one_smul R₁ _ _, smul_right, neg_one_mul]

@[simp]
theorem sub_left (x y z : M₁) : B₁ (x - y) z = B₁ x z - B₁ y z := by
  rw [sub_eq_add_neg, sub_eq_add_neg, add_left, neg_left]

@[simp]
theorem sub_right (x y z : M₁) : B₁ x (y - z) = B₁ x y - B₁ x z := by
  rw [sub_eq_add_neg, sub_eq_add_neg, add_right, neg_right]

variable {D : BilinForm R M} {D₁ : BilinForm R₁ M₁}

-- TODO: instantiate `fun_like`
theorem coe_injective : Function.Injective (coeFn : BilinForm R M → M → M → R) := fun B D h => by
  cases B
  cases D
  congr

@[ext]
theorem ext (H : ∀ x y : M, B x y = D x y) : B = D :=
  coe_injective <| by
    funext
    exact H _ _

theorem congr_fun (h : B = D) (x y : M) : B x y = D x y :=
  h ▸ rfl

theorem ext_iff : B = D ↔ ∀ x y, B x y = D x y :=
  ⟨congr_fun, ext⟩

instance :
    Zero
      (BilinForm R
        M) where zero :=
    { bilin := fun x y => 0, bilin_add_left := fun x y z => (add_zeroₓ 0).symm,
      bilin_smul_left := fun a x y => (mul_zero a).symm, bilin_add_right := fun x y z => (zero_addₓ 0).symm,
      bilin_smul_right := fun a x y => (mul_zero a).symm }

@[simp]
theorem coe_zero : ⇑(0 : BilinForm R M) = 0 :=
  rfl

@[simp]
theorem zero_apply (x y : M) : (0 : BilinForm R M) x y = 0 :=
  rfl

variable (B D B₁ D₁)

instance :
    Add (BilinForm R M) where add := fun B D =>
    { bilin := fun x y => B x y + D x y,
      bilin_add_left := fun x y z => by
        rw [add_left, add_left, add_add_add_commₓ],
      bilin_smul_left := fun a x y => by
        rw [smul_left, smul_left, mul_addₓ],
      bilin_add_right := fun x y z => by
        rw [add_right, add_right, add_add_add_commₓ],
      bilin_smul_right := fun a x y => by
        rw [smul_right, smul_right, mul_addₓ] }

@[simp]
theorem coe_add : ⇑(B + D) = B + D :=
  rfl

@[simp]
theorem add_apply (x y : M) : (B + D) x y = B x y + D x y :=
  rfl

/-- `bilin_form R M` inherits the scalar action by `α` on `R` if this is compatible with
multiplication.

When `R` itself is commutative, this provides an `R`-action via `algebra.id`. -/
instance {α} [Monoidₓ α] [DistribMulAction α R] [SmulCommClass α R R] :
    HasSmul α
      (BilinForm R M) where smul := fun c B =>
    { bilin := fun x y => c • B x y,
      bilin_add_left := fun x y z => by
        rw [add_left, smul_add],
      bilin_smul_left := fun a x y => by
        rw [smul_left, ← mul_smul_comm],
      bilin_add_right := fun x y z => by
        rw [add_right, smul_add],
      bilin_smul_right := fun a x y => by
        rw [smul_right, ← mul_smul_comm] }

@[simp]
theorem coe_smul {α} [Monoidₓ α] [DistribMulAction α R] [SmulCommClass α R R] (a : α) (B : BilinForm R M) :
    ⇑(a • B) = a • B :=
  rfl

@[simp]
theorem smul_apply {α} [Monoidₓ α] [DistribMulAction α R] [SmulCommClass α R R] (a : α) (B : BilinForm R M) (x y : M) :
    (a • B) x y = a • B x y :=
  rfl

instance : AddCommMonoidₓ (BilinForm R M) :=
  Function.Injective.addCommMonoid _ coe_injective coe_zero coe_add fun n x => coe_smul _ _

instance :
    Neg (BilinForm R₁ M₁) where neg := fun B =>
    { bilin := fun x y => -B x y,
      bilin_add_left := fun x y z => by
        rw [add_left, neg_add],
      bilin_smul_left := fun a x y => by
        rw [smul_left, mul_neg],
      bilin_add_right := fun x y z => by
        rw [add_right, neg_add],
      bilin_smul_right := fun a x y => by
        rw [smul_right, mul_neg] }

@[simp]
theorem coe_neg : ⇑(-B₁) = -B₁ :=
  rfl

@[simp]
theorem neg_apply (x y : M₁) : (-B₁) x y = -B₁ x y :=
  rfl

instance :
    Sub (BilinForm R₁ M₁) where sub := fun B D =>
    { bilin := fun x y => B x y - D x y,
      bilin_add_left := fun x y z => by
        rw [add_left, add_left, add_sub_add_comm],
      bilin_smul_left := fun a x y => by
        rw [smul_left, smul_left, mul_sub],
      bilin_add_right := fun x y z => by
        rw [add_right, add_right, add_sub_add_comm],
      bilin_smul_right := fun a x y => by
        rw [smul_right, smul_right, mul_sub] }

@[simp]
theorem coe_sub : ⇑(B₁ - D₁) = B₁ - D₁ :=
  rfl

@[simp]
theorem sub_apply (x y : M₁) : (B₁ - D₁) x y = B₁ x y - D₁ x y :=
  rfl

instance : AddCommGroupₓ (BilinForm R₁ M₁) :=
  Function.Injective.addCommGroup _ coe_injective coe_zero coe_add coe_neg coe_sub (fun n x => coe_smul _ _) fun n x =>
    coe_smul _ _

instance : Inhabited (BilinForm R M) :=
  ⟨0⟩

/-- `coe_fn` as an `add_monoid_hom` -/
def coeFnAddMonoidHom : BilinForm R M →+ M → M → R where
  toFun := coeFn
  map_zero' := coe_zero
  map_add' := coe_add

instance {α} [Monoidₓ α] [DistribMulAction α R] [SmulCommClass α R R] : DistribMulAction α (BilinForm R M) :=
  Function.Injective.distribMulAction coeFnAddMonoidHom coe_injective coe_smul

instance {α} [Semiringₓ α] [Module α R] [SmulCommClass α R R] : Module α (BilinForm R M) :=
  Function.Injective.module _ coeFnAddMonoidHom coe_injective coe_smul

section flip

variable (R₂)

/-- Auxiliary construction for the flip of a bilinear form, obtained by exchanging the left and
right arguments. This version is a `linear_map`; it is later upgraded to a `linear_equiv`
in `flip_hom`. -/
def flipHomAux [Algebra R₂ R] : BilinForm R M →ₗ[R₂] BilinForm R M where
  toFun := fun A =>
    { bilin := fun i j => A j i, bilin_add_left := fun x y z => A.bilin_add_right z x y,
      bilin_smul_left := fun a x y => A.bilin_smul_right a y x, bilin_add_right := fun x y z => A.bilin_add_left y z x,
      bilin_smul_right := fun a x y => A.bilin_smul_left a y x }
  map_add' := fun A₁ A₂ => by
    ext
    simp
  map_smul' := fun c A => by
    ext
    simp

variable {R₂}

theorem flip_flip_aux [Algebra R₂ R] (A : BilinForm R M) : (flipHomAux R₂) (flipHomAux R₂ A) = A := by
  ext A x y
  simp [← flip_hom_aux]

variable (R₂)

/-- The flip of a bilinear form, obtained by exchanging the left and right arguments. This is a
less structured version of the equiv which applies to general (noncommutative) rings `R` with a
distinguished commutative subring `R₂`; over a commutative ring use `flip`. -/
def flipHom [Algebra R₂ R] : BilinForm R M ≃ₗ[R₂] BilinForm R M :=
  { flipHomAux R₂ with invFun := flipHomAux R₂, left_inv := flip_flip_aux, right_inv := flip_flip_aux }

variable {R₂}

@[simp]
theorem flip_apply [Algebra R₂ R] (A : BilinForm R M) (x y : M) : flipHom R₂ A x y = A y x :=
  rfl

theorem flip_flip [Algebra R₂ R] : (flipHom R₂).trans (flipHom R₂) = LinearEquiv.refl R₂ (BilinForm R M) := by
  ext A x y
  simp

/-- The flip of a bilinear form over a ring, obtained by exchanging the left and right arguments,
here considered as an `ℕ`-linear equivalence, i.e. an additive equivalence. -/
abbrev flip' : BilinForm R M ≃ₗ[ℕ] BilinForm R M :=
  flipHom ℕ

/-- The `flip` of a bilinear form over a commutative ring, obtained by exchanging the left and
right arguments. -/
abbrev flip : BilinForm R₂ M₂ ≃ₗ[R₂] BilinForm R₂ M₂ :=
  flipHom R₂

end flip

section ToLin'

variable [Algebra R₂ R] [Module R₂ M] [IsScalarTower R₂ R M]

/-- Auxiliary definition to define `to_lin_hom`; see below. -/
def toLinHomAux₁ (A : BilinForm R M) (x : M) : M →ₗ[R] R where
  toFun := fun y => A x y
  map_add' := A.bilin_add_right x
  map_smul' := fun c => A.bilin_smul_right c x

/-- Auxiliary definition to define `to_lin_hom`; see below. -/
def toLinHomAux₂ (A : BilinForm R M) : M →ₗ[R₂] M →ₗ[R] R where
  toFun := toLinHomAux₁ A
  map_add' := fun x₁ x₂ =>
    LinearMap.ext fun x => by
      simp only [← to_lin_hom_aux₁, ← LinearMap.coe_mk, ← LinearMap.add_apply, ← add_left]
  map_smul' := fun c x =>
    LinearMap.ext <| by
      dsimp' [← to_lin_hom_aux₁]
      intros
      simp only [algebra_map_smul R c x, ← Algebra.smul_def, ← LinearMap.coe_mk, ← LinearMap.smul_apply, ← smul_left]

variable (R₂)

/-- The linear map obtained from a `bilin_form` by fixing the left co-ordinate and evaluating in
the right.
This is the most general version of the construction; it is `R₂`-linear for some distinguished
commutative subsemiring `R₂` of the scalar ring.  Over a semiring with no particular distinguished
such subsemiring, use `to_lin'`, which is `ℕ`-linear.  Over a commutative semiring, use `to_lin`,
which is linear. -/
def toLinHom : BilinForm R M →ₗ[R₂] M →ₗ[R₂] M →ₗ[R] R where
  toFun := toLinHomAux₂
  map_add' := fun A₁ A₂ =>
    LinearMap.ext fun x => by
      dsimp' only [← to_lin_hom_aux₁, ← to_lin_hom_aux₂]
      apply LinearMap.ext
      intro y
      simp only [← to_lin_hom_aux₂, ← to_lin_hom_aux₁, ← LinearMap.coe_mk, ← LinearMap.add_apply, ← add_apply]
  map_smul' := fun c A => by
    dsimp' [← to_lin_hom_aux₁, ← to_lin_hom_aux₂]
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    simp only [← to_lin_hom_aux₂, ← to_lin_hom_aux₁, ← LinearMap.coe_mk, ← LinearMap.smul_apply, ← smul_apply]

variable {R₂}

@[simp]
theorem to_lin'_apply (A : BilinForm R M) (x : M) : ⇑(toLinHom R₂ A x) = A x :=
  rfl

/-- The linear map obtained from a `bilin_form` by fixing the left co-ordinate and evaluating in
the right.
Over a commutative semiring, use `to_lin`, which is linear rather than `ℕ`-linear. -/
abbrev toLin' : BilinForm R M →ₗ[ℕ] M →ₗ[ℕ] M →ₗ[R] R :=
  toLinHom ℕ

@[simp]
theorem sum_left {α} (t : Finset α) (g : α → M) (w : M) : B (∑ i in t, g i) w = ∑ i in t, B (g i) w :=
  (BilinForm.toLin' B).map_sum₂ t g w

@[simp]
theorem sum_right {α} (t : Finset α) (w : M) (g : α → M) : B w (∑ i in t, g i) = ∑ i in t, B w (g i) :=
  (BilinForm.toLin' B w).map_sum

variable (R₂)

/-- The linear map obtained from a `bilin_form` by fixing the right co-ordinate and evaluating in
the left.
This is the most general version of the construction; it is `R₂`-linear for some distinguished
commutative subsemiring `R₂` of the scalar ring.  Over semiring with no particular distinguished
such subsemiring, use `to_lin'_flip`, which is `ℕ`-linear.  Over a commutative semiring, use
`to_lin_flip`, which is linear. -/
def toLinHomFlip : BilinForm R M →ₗ[R₂] M →ₗ[R₂] M →ₗ[R] R :=
  (toLinHom R₂).comp (flipHom R₂).toLinearMap

variable {R₂}

@[simp]
theorem to_lin'_flip_apply (A : BilinForm R M) (x : M) : ⇑(toLinHomFlip R₂ A x) = fun y => A y x :=
  rfl

/-- The linear map obtained from a `bilin_form` by fixing the right co-ordinate and evaluating in
the left.
Over a commutative semiring, use `to_lin_flip`, which is linear rather than `ℕ`-linear. -/
abbrev toLin'Flip : BilinForm R M →ₗ[ℕ] M →ₗ[ℕ] M →ₗ[R] R :=
  toLinHomFlip ℕ

end ToLin'

end BilinForm

section EquivLin

/-- A map with two arguments that is linear in both is a bilinear form.

This is an auxiliary definition for the full linear equivalence `linear_map.to_bilin`.
-/
def LinearMap.toBilinAux (f : M₂ →ₗ[R₂] M₂ →ₗ[R₂] R₂) : BilinForm R₂ M₂ where
  bilin := fun x y => f x y
  bilin_add_left := fun x y z => (LinearMap.map_add f x y).symm ▸ LinearMap.add_apply (f x) (f y) z
  bilin_smul_left := fun a x y => by
    rw [LinearMap.map_smul, LinearMap.smul_apply, smul_eq_mul]
  bilin_add_right := fun x y z => LinearMap.map_add (f x) y z
  bilin_smul_right := fun a x y => LinearMap.map_smul (f x) a y

/-- Bilinear forms are linearly equivalent to maps with two arguments that are linear in both. -/
def BilinForm.toLin : BilinForm R₂ M₂ ≃ₗ[R₂] M₂ →ₗ[R₂] M₂ →ₗ[R₂] R₂ :=
  { BilinForm.toLinHom R₂ with invFun := LinearMap.toBilinAux,
    left_inv := fun B => by
      ext
      simp [← LinearMap.toBilinAux],
    right_inv := fun B => by
      ext
      simp [← LinearMap.toBilinAux] }

/-- A map with two arguments that is linear in both is linearly equivalent to bilinear form. -/
def LinearMap.toBilin : (M₂ →ₗ[R₂] M₂ →ₗ[R₂] R₂) ≃ₗ[R₂] BilinForm R₂ M₂ :=
  BilinForm.toLin.symm

@[simp]
theorem LinearMap.to_bilin_aux_eq (f : M₂ →ₗ[R₂] M₂ →ₗ[R₂] R₂) : LinearMap.toBilinAux f = LinearMap.toBilin f :=
  rfl

@[simp]
theorem LinearMap.to_bilin_symm : (LinearMap.toBilin.symm : BilinForm R₂ M₂ ≃ₗ[R₂] _) = BilinForm.toLin :=
  rfl

@[simp]
theorem BilinForm.to_lin_symm : (BilinForm.toLin.symm : _ ≃ₗ[R₂] BilinForm R₂ M₂) = LinearMap.toBilin :=
  LinearMap.toBilin.symm_symm

@[simp, norm_cast]
theorem BilinForm.to_lin_apply (x : M₂) : ⇑(BilinForm.toLin B₂ x) = B₂ x :=
  rfl

end EquivLin

namespace LinearMap

variable {R' : Type} [CommSemiringₓ R'] [Algebra R' R] [Module R' M] [IsScalarTower R' R M]

/-- Apply a linear map on the output of a bilinear form. -/
@[simps]
def compBilinForm (f : R →ₗ[R'] R') (B : BilinForm R M) : BilinForm R' M where
  bilin := fun x y => f (B x y)
  bilin_add_left := fun x y z => by
    rw [BilinForm.add_left, map_add]
  bilin_smul_left := fun r x y => by
    rw [← smul_one_smul R r (_ : M), BilinForm.smul_left, smul_one_mul r (_ : R), map_smul, smul_eq_mul]
  bilin_add_right := fun x y z => by
    rw [BilinForm.add_right, map_add]
  bilin_smul_right := fun r x y => by
    rw [← smul_one_smul R r (_ : M), BilinForm.smul_right, smul_one_mul r (_ : R), map_smul, smul_eq_mul]

end LinearMap

namespace BilinForm

section Comp

variable {M' : Type w} [AddCommMonoidₓ M'] [Module R M']

/-- Apply a linear map on the left and right argument of a bilinear form. -/
def comp (B : BilinForm R M') (l r : M →ₗ[R] M') : BilinForm R M where
  bilin := fun x y => B (l x) (r y)
  bilin_add_left := fun x y z => by
    rw [LinearMap.map_add, add_left]
  bilin_smul_left := fun x y z => by
    rw [LinearMap.map_smul, smul_left]
  bilin_add_right := fun x y z => by
    rw [LinearMap.map_add, add_right]
  bilin_smul_right := fun x y z => by
    rw [LinearMap.map_smul, smul_right]

/-- Apply a linear map to the left argument of a bilinear form. -/
def compLeft (B : BilinForm R M) (f : M →ₗ[R] M) : BilinForm R M :=
  B.comp f LinearMap.id

/-- Apply a linear map to the right argument of a bilinear form. -/
def compRight (B : BilinForm R M) (f : M →ₗ[R] M) : BilinForm R M :=
  B.comp LinearMap.id f

theorem comp_comp {M'' : Type _} [AddCommMonoidₓ M''] [Module R M''] (B : BilinForm R M'') (l r : M →ₗ[R] M')
    (l' r' : M' →ₗ[R] M'') : (B.comp l' r').comp l r = B.comp (l'.comp l) (r'.comp r) :=
  rfl

@[simp]
theorem comp_left_comp_right (B : BilinForm R M) (l r : M →ₗ[R] M) : (B.compLeft l).compRight r = B.comp l r :=
  rfl

@[simp]
theorem comp_right_comp_left (B : BilinForm R M) (l r : M →ₗ[R] M) : (B.compRight r).compLeft l = B.comp l r :=
  rfl

@[simp]
theorem comp_apply (B : BilinForm R M') (l r : M →ₗ[R] M') (v w) : B.comp l r v w = B (l v) (r w) :=
  rfl

@[simp]
theorem comp_left_apply (B : BilinForm R M) (f : M →ₗ[R] M) (v w) : B.compLeft f v w = B (f v) w :=
  rfl

@[simp]
theorem comp_right_apply (B : BilinForm R M) (f : M →ₗ[R] M) (v w) : B.compRight f v w = B v (f w) :=
  rfl

@[simp]
theorem comp_id_left (B : BilinForm R M) (r : M →ₗ[R] M) : B.comp LinearMap.id r = B.compRight r := by
  ext
  rfl

@[simp]
theorem comp_id_right (B : BilinForm R M) (l : M →ₗ[R] M) : B.comp l LinearMap.id = B.compLeft l := by
  ext
  rfl

@[simp]
theorem comp_left_id (B : BilinForm R M) : B.compLeft LinearMap.id = B := by
  ext
  rfl

@[simp]
theorem comp_right_id (B : BilinForm R M) : B.compRight LinearMap.id = B := by
  ext
  rfl

-- Shortcut for `comp_id_{left,right}` followed by `comp_{right,left}_id`,
-- has to be declared after the former two to get the right priority
@[simp]
theorem comp_id_id (B : BilinForm R M) : B.comp LinearMap.id LinearMap.id = B := by
  ext
  rfl

theorem comp_inj (B₁ B₂ : BilinForm R M') {l r : M →ₗ[R] M'} (hₗ : Function.Surjective l) (hᵣ : Function.Surjective r) :
    B₁.comp l r = B₂.comp l r ↔ B₁ = B₂ := by
  constructor <;> intro h
  · -- B₁.comp l r = B₂.comp l r → B₁ = B₂
    ext
    cases' hₗ x with x' hx
    subst hx
    cases' hᵣ y with y' hy
    subst hy
    rw [← comp_apply, ← comp_apply, h]
    
  · -- B₁ = B₂ → B₁.comp l r = B₂.comp l r
    subst h
    

end Comp

variable {M₂' M₂'' : Type _}

variable [AddCommMonoidₓ M₂'] [AddCommMonoidₓ M₂''] [Module R₂ M₂'] [Module R₂ M₂'']

section congr

/-- Apply a linear equivalence on the arguments of a bilinear form. -/
def congr (e : M₂ ≃ₗ[R₂] M₂') : BilinForm R₂ M₂ ≃ₗ[R₂] BilinForm R₂ M₂' where
  toFun := fun B => B.comp e.symm e.symm
  invFun := fun B => B.comp e e
  left_inv := fun B =>
    ext fun x y => by
      simp only [← comp_apply, ← LinearEquiv.coe_coe, ← e.symm_apply_apply]
  right_inv := fun B =>
    ext fun x y => by
      simp only [← comp_apply, ← LinearEquiv.coe_coe, ← e.apply_symm_apply]
  map_add' := fun B B' =>
    ext fun x y => by
      simp only [← comp_apply, ← add_apply]
  map_smul' := fun B B' =>
    ext fun x y => by
      simp [← comp_apply, ← smul_apply]

@[simp]
theorem congr_apply (e : M₂ ≃ₗ[R₂] M₂') (B : BilinForm R₂ M₂) (x y : M₂') : congr e B x y = B (e.symm x) (e.symm y) :=
  rfl

@[simp]
theorem congr_symm (e : M₂ ≃ₗ[R₂] M₂') : (congr e).symm = congr e.symm := by
  ext B x y
  simp only [← congr_apply, ← LinearEquiv.symm_symm]
  rfl

@[simp]
theorem congr_refl : congr (LinearEquiv.refl R₂ M₂) = LinearEquiv.refl R₂ _ :=
  LinearEquiv.ext fun B => ext fun x y => rfl

theorem congr_trans (e : M₂ ≃ₗ[R₂] M₂') (f : M₂' ≃ₗ[R₂] M₂'') : (congr e).trans (congr f) = congr (e.trans f) :=
  rfl

theorem congr_congr (e : M₂' ≃ₗ[R₂] M₂'') (f : M₂ ≃ₗ[R₂] M₂') (B : BilinForm R₂ M₂) :
    congr e (congr f B) = congr (f.trans e) B :=
  rfl

theorem congr_comp (e : M₂ ≃ₗ[R₂] M₂') (B : BilinForm R₂ M₂) (l r : M₂'' →ₗ[R₂] M₂') :
    (congr e B).comp l r =
      B.comp (LinearMap.comp (e.symm : M₂' →ₗ[R₂] M₂) l) (LinearMap.comp (e.symm : M₂' →ₗ[R₂] M₂) r) :=
  rfl

theorem comp_congr (e : M₂' ≃ₗ[R₂] M₂'') (B : BilinForm R₂ M₂) (l r : M₂' →ₗ[R₂] M₂) :
    congr e (B.comp l r) = B.comp (l.comp (e.symm : M₂'' →ₗ[R₂] M₂')) (r.comp (e.symm : M₂'' →ₗ[R₂] M₂')) :=
  rfl

end congr

section LinMulLin

/-- `lin_mul_lin f g` is the bilinear form mapping `x` and `y` to `f x * g y` -/
def linMulLin (f g : M₂ →ₗ[R₂] R₂) : BilinForm R₂ M₂ where
  bilin := fun x y => f x * g y
  bilin_add_left := fun x y z => by
    rw [LinearMap.map_add, add_mulₓ]
  bilin_smul_left := fun x y z => by
    rw [LinearMap.map_smul, smul_eq_mul, mul_assoc]
  bilin_add_right := fun x y z => by
    rw [LinearMap.map_add, mul_addₓ]
  bilin_smul_right := fun x y z => by
    rw [LinearMap.map_smul, smul_eq_mul, mul_left_commₓ]

variable {f g : M₂ →ₗ[R₂] R₂}

@[simp]
theorem lin_mul_lin_apply (x y) : linMulLin f g x y = f x * g y :=
  rfl

@[simp]
theorem lin_mul_lin_comp (l r : M₂' →ₗ[R₂] M₂) : (linMulLin f g).comp l r = linMulLin (f.comp l) (g.comp r) :=
  rfl

@[simp]
theorem lin_mul_lin_comp_left (l : M₂ →ₗ[R₂] M₂) : (linMulLin f g).compLeft l = linMulLin (f.comp l) g :=
  rfl

@[simp]
theorem lin_mul_lin_comp_right (r : M₂ →ₗ[R₂] M₂) : (linMulLin f g).compRight r = linMulLin f (g.comp r) :=
  rfl

end LinMulLin

/-- The proposition that two elements of a bilinear form space are orthogonal. For orthogonality
of an indexed set of elements, use `bilin_form.is_Ortho`. -/
def IsOrtho (B : BilinForm R M) (x y : M) : Prop :=
  B x y = 0

theorem is_ortho_def {B : BilinForm R M} {x y : M} : B.IsOrtho x y ↔ B x y = 0 :=
  Iff.rfl

theorem is_ortho_zero_left (x : M) : IsOrtho B (0 : M) x :=
  zero_left x

theorem is_ortho_zero_right (x : M) : IsOrtho B x (0 : M) :=
  zero_right x

theorem ne_zero_of_not_is_ortho_self {B : BilinForm K V} (x : V) (hx₁ : ¬B.IsOrtho x x) : x ≠ 0 := fun hx₂ =>
  hx₁ (hx₂.symm ▸ is_ortho_zero_left _)

/-- A set of vectors `v` is orthogonal with respect to some bilinear form `B` if and only
if for all `i ≠ j`, `B (v i) (v j) = 0`. For orthogonality between two elements, use
`bilin_form.is_ortho` -/
def IsOrthoₓ {n : Type w} (B : BilinForm R M) (v : n → M) : Prop :=
  Pairwise (B.IsOrtho on v)

theorem is_Ortho_def {n : Type w} {B : BilinForm R M} {v : n → M} :
    B.IsOrtho v ↔ ∀ i j : n, i ≠ j → B (v i) (v j) = 0 :=
  Iff.rfl

section

variable {R₄ M₄ : Type _} [Ringₓ R₄] [IsDomain R₄]

variable [AddCommGroupₓ M₄] [Module R₄ M₄] {G : BilinForm R₄ M₄}

@[simp]
theorem is_ortho_smul_left {x y : M₄} {a : R₄} (ha : a ≠ 0) : IsOrtho G (a • x) y ↔ IsOrtho G x y := by
  dunfold is_ortho
  constructor <;> intro H
  · rw [smul_left, mul_eq_zero] at H
    cases H
    · trivial
      
    · exact H
      
    
  · rw [smul_left, H, mul_zero]
    

@[simp]
theorem is_ortho_smul_right {x y : M₄} {a : R₄} (ha : a ≠ 0) : IsOrtho G x (a • y) ↔ IsOrtho G x y := by
  dunfold is_ortho
  constructor <;> intro H
  · rw [smul_right, mul_eq_zero] at H
    cases H
    · trivial
      
    · exact H
      
    
  · rw [smul_right, H, mul_zero]
    

/-- A set of orthogonal vectors `v` with respect to some bilinear form `B` is linearly independent
  if for all `i`, `B (v i) (v i) ≠ 0`. -/
theorem linear_independent_of_is_Ortho {n : Type w} {B : BilinForm K V} {v : n → V} (hv₁ : B.IsOrtho v)
    (hv₂ : ∀ i, ¬B.IsOrtho (v i) (v i)) : LinearIndependent K v := by
  classical
  rw [linear_independent_iff']
  intro s w hs i hi
  have : B (s.sum fun i : n => w i • v i) (v i) = 0 := by
    rw [hs, zero_left]
  have hsum : (s.sum fun j : n => w j * B (v j) (v i)) = w i * B (v i) (v i) := by
    apply Finset.sum_eq_single_of_mem i hi
    intro j hj hij
    rw [is_Ortho_def.1 hv₁ _ _ hij, mul_zero]
  simp_rw [sum_left, smul_left, hsum] at this
  exact eq_zero_of_ne_zero_of_mul_right_eq_zero (hv₂ i) this

end

section Basis

variable {F₂ : BilinForm R₂ M₂}

variable {ι : Type _} (b : Basis ι R₂ M₂)

/-- Two bilinear forms are equal when they are equal on all basis vectors. -/
theorem ext_basis (h : ∀ i j, B₂ (b i) (b j) = F₂ (b i) (b j)) : B₂ = F₂ :=
  toLin.Injective <| b.ext fun i => b.ext fun j => h i j

/-- Write out `B x y` as a sum over `B (b i) (b j)` if `b` is a basis. -/
theorem sum_repr_mul_repr_mul (x y : M₂) :
    ((b.repr x).Sum fun i xi => (b.repr y).Sum fun j yj => xi • yj • B₂ (b i) (b j)) = B₂ x y := by
  conv_rhs => rw [← b.total_repr x, ← b.total_repr y]
  simp_rw [Finsupp.total_apply, Finsupp.sum, sum_left, sum_right, smul_left, smul_right, smul_eq_mul]

end Basis

/-- The proposition that a bilinear form is reflexive -/
def IsRefl (B : BilinForm R M) : Prop :=
  ∀ x y : M, B x y = 0 → B y x = 0

namespace IsRefl

variable (H : B.IsRefl)

theorem eq_zero : ∀ {x y : M}, B x y = 0 → B y x = 0 := fun x y => H x y

theorem ortho_comm {x y : M} : IsOrtho B x y ↔ IsOrtho B y x :=
  ⟨eq_zero H, eq_zero H⟩

end IsRefl

/-- The proposition that a bilinear form is symmetric -/
def IsSymm (B : BilinForm R M) : Prop :=
  ∀ x y : M, B x y = B y x

namespace IsSymm

variable (H : B.IsSymm)

protected theorem eq (x y : M) : B x y = B y x :=
  H x y

theorem is_refl : B.IsRefl := fun x y H1 => H x y ▸ H1

theorem ortho_comm {x y : M} : IsOrtho B x y ↔ IsOrtho B y x :=
  H.IsRefl.ortho_comm

end IsSymm

theorem is_symm_iff_flip' [Algebra R₂ R] : B.IsSymm ↔ flipHom R₂ B = B := by
  constructor
  · intro h
    ext x y
    exact h y x
    
  · intro h x y
    conv_lhs => rw [← h]
    simp
    

/-- The proposition that a bilinear form is alternating -/
def IsAlt (B : BilinForm R M) : Prop :=
  ∀ x : M, B x x = 0

namespace IsAlt

theorem self_eq_zero (H : B.IsAlt) (x : M) : B x x = 0 :=
  H x

theorem neg (H : B₁.IsAlt) (x y : M₁) : -B₁ x y = B₁ y x := by
  have H1 : B₁ (x + y) (x + y) = 0 := self_eq_zero H (x + y)
  rw [add_left, add_right, add_right, self_eq_zero H, self_eq_zero H, Ringₓ.zero_add, Ringₓ.add_zero,
    add_eq_zero_iff_neg_eq] at H1
  exact H1

theorem is_refl (H : B₁.IsAlt) : B₁.IsRefl := by
  intro x y h
  rw [← neg H, h, neg_zero]

theorem ortho_comm (H : B₁.IsAlt) {x y : M₁} : IsOrtho B₁ x y ↔ IsOrtho B₁ y x :=
  H.IsRefl.ortho_comm

end IsAlt

section LinearAdjoints

variable (B) (F : BilinForm R M)

variable {M' : Type _} [AddCommMonoidₓ M'] [Module R M']

variable (B' : BilinForm R M') (f f' : M →ₗ[R] M') (g g' : M' →ₗ[R] M)

/-- Given a pair of modules equipped with bilinear forms, this is the condition for a pair of
maps between them to be mutually adjoint. -/
def IsAdjointPair :=
  ∀ ⦃x y⦄, B' (f x) y = B x (g y)

variable {B B' B₂ f f' g g'}

theorem IsAdjointPair.eq (h : IsAdjointPair B B' f g) : ∀ {x y}, B' (f x) y = B x (g y) :=
  h

theorem is_adjoint_pair_iff_comp_left_eq_comp_right (f g : Module.End R M) :
    IsAdjointPair B F f g ↔ F.compLeft f = B.compRight g := by
  constructor <;> intro h
  · ext x y
    rw [comp_left_apply, comp_right_apply]
    apply h
    
  · intro x y
    rw [← comp_left_apply, ← comp_right_apply]
    rw [h]
    

theorem is_adjoint_pair_zero : IsAdjointPair B B' 0 0 := fun x y => by
  simp only [← BilinForm.zero_left, ← BilinForm.zero_right, ← LinearMap.zero_apply]

theorem is_adjoint_pair_id : IsAdjointPair B B 1 1 := fun x y => rfl

theorem IsAdjointPair.add (h : IsAdjointPair B B' f g) (h' : IsAdjointPair B B' f' g') :
    IsAdjointPair B B' (f + f') (g + g') := fun x y => by
  rw [LinearMap.add_apply, LinearMap.add_apply, add_left, add_right, h, h']

variable {M₁' : Type _} [AddCommGroupₓ M₁'] [Module R₁ M₁']

variable {B₁' : BilinForm R₁ M₁'} {f₁ f₁' : M₁ →ₗ[R₁] M₁'} {g₁ g₁' : M₁' →ₗ[R₁] M₁}

theorem IsAdjointPair.sub (h : IsAdjointPair B₁ B₁' f₁ g₁) (h' : IsAdjointPair B₁ B₁' f₁' g₁') :
    IsAdjointPair B₁ B₁' (f₁ - f₁') (g₁ - g₁') := fun x y => by
  rw [LinearMap.sub_apply, LinearMap.sub_apply, sub_left, sub_right, h, h']

variable {B₂' : BilinForm R₂ M₂'} {f₂ f₂' : M₂ →ₗ[R₂] M₂'} {g₂ g₂' : M₂' →ₗ[R₂] M₂}

theorem IsAdjointPair.smul (c : R₂) (h : IsAdjointPair B₂ B₂' f₂ g₂) : IsAdjointPair B₂ B₂' (c • f₂) (c • g₂) :=
  fun x y => by
  rw [LinearMap.smul_apply, LinearMap.smul_apply, smul_left, smul_right, h]

variable {M'' : Type _} [AddCommMonoidₓ M''] [Module R M'']

variable (B'' : BilinForm R M'')

theorem IsAdjointPair.comp {f' : M' →ₗ[R] M''} {g' : M'' →ₗ[R] M'} (h : IsAdjointPair B B' f g)
    (h' : IsAdjointPair B' B'' f' g') : IsAdjointPair B B'' (f'.comp f) (g.comp g') := fun x y => by
  rw [LinearMap.comp_apply, LinearMap.comp_apply, h', h]

theorem IsAdjointPair.mul {f g f' g' : Module.End R M} (h : IsAdjointPair B B f g) (h' : IsAdjointPair B B f' g') :
    IsAdjointPair B B (f * f') (g' * g) := fun x y => by
  rw [LinearMap.mul_apply, LinearMap.mul_apply, h, h']

variable (B B' B₁ B₂) (F₂ : BilinForm R₂ M₂)

/-- The condition for an endomorphism to be "self-adjoint" with respect to a pair of bilinear forms
on the underlying module. In the case that these two forms are identical, this is the usual concept
of self adjointness. In the case that one of the forms is the negation of the other, this is the
usual concept of skew adjointness. -/
def IsPairSelfAdjoint (f : Module.End R M) :=
  IsAdjointPair B F f f

/-- The set of pair-self-adjoint endomorphisms are a submodule of the type of all endomorphisms. -/
def isPairSelfAdjointSubmodule : Submodule R₂ (Module.End R₂ M₂) where
  Carrier := { f | IsPairSelfAdjoint B₂ F₂ f }
  zero_mem' := is_adjoint_pair_zero
  add_mem' := fun f g hf hg => hf.add hg
  smul_mem' := fun c f h => h.smul c

@[simp]
theorem mem_is_pair_self_adjoint_submodule (f : Module.End R₂ M₂) :
    f ∈ isPairSelfAdjointSubmodule B₂ F₂ ↔ IsPairSelfAdjoint B₂ F₂ f := by
  rfl

theorem is_pair_self_adjoint_equiv (e : M₂' ≃ₗ[R₂] M₂) (f : Module.End R₂ M₂) :
    IsPairSelfAdjoint B₂ F₂ f ↔ IsPairSelfAdjoint (B₂.comp ↑e ↑e) (F₂.comp ↑e ↑e) (e.symm.conj f) := by
  have hₗ : (F₂.comp ↑e ↑e).compLeft (e.symm.conj f) = (F₂.comp_left f).comp ↑e ↑e := by
    ext
    simp [← LinearEquiv.symm_conj_apply]
  have hᵣ : (B₂.comp ↑e ↑e).compRight (e.symm.conj f) = (B₂.comp_right f).comp ↑e ↑e := by
    ext
    simp [← LinearEquiv.conj_apply]
  have he : Function.Surjective (⇑(↑e : M₂' →ₗ[R₂] M₂) : M₂' → M₂) := e.surjective
  show BilinForm.IsAdjointPair _ _ _ _ ↔ BilinForm.IsAdjointPair _ _ _ _
  rw [is_adjoint_pair_iff_comp_left_eq_comp_right, is_adjoint_pair_iff_comp_left_eq_comp_right, hᵣ, hₗ,
    comp_inj _ _ he he]

/-- An endomorphism of a module is self-adjoint with respect to a bilinear form if it serves as an
adjoint for itself. -/
def IsSelfAdjoint (f : Module.End R M) :=
  IsAdjointPair B B f f

/-- An endomorphism of a module is skew-adjoint with respect to a bilinear form if its negation
serves as an adjoint. -/
def IsSkewAdjoint (f : Module.End R₁ M₁) :=
  IsAdjointPair B₁ B₁ f (-f)

theorem is_skew_adjoint_iff_neg_self_adjoint (f : Module.End R₁ M₁) : B₁.IsSkewAdjoint f ↔ IsAdjointPair (-B₁) B₁ f f :=
  show (∀ x y, B₁ (f x) y = B₁ x ((-f) y)) ↔ ∀ x y, B₁ (f x) y = (-B₁) x (f y) by
    simp only [← LinearMap.neg_apply, ← BilinForm.neg_apply, ← BilinForm.neg_right]

/-- The set of self-adjoint endomorphisms of a module with bilinear form is a submodule. (In fact
it is a Jordan subalgebra.) -/
def selfAdjointSubmodule :=
  isPairSelfAdjointSubmodule B₂ B₂

@[simp]
theorem mem_self_adjoint_submodule (f : Module.End R₂ M₂) : f ∈ B₂.selfAdjointSubmodule ↔ B₂.IsSelfAdjoint f :=
  Iff.rfl

variable (B₃ : BilinForm R₃ M₃)

/-- The set of skew-adjoint endomorphisms of a module with bilinear form is a submodule. (In fact
it is a Lie subalgebra.) -/
def skewAdjointSubmodule :=
  isPairSelfAdjointSubmodule (-B₃) B₃

@[simp]
theorem mem_skew_adjoint_submodule (f : Module.End R₃ M₃) : f ∈ B₃.skewAdjointSubmodule ↔ B₃.IsSkewAdjoint f := by
  rw [is_skew_adjoint_iff_neg_self_adjoint]
  exact Iff.rfl

end LinearAdjoints

end BilinForm

namespace BilinForm

section Orthogonal

/-- The orthogonal complement of a submodule `N` with respect to some bilinear form is the set of
elements `x` which are orthogonal to all elements of `N`; i.e., for all `y` in `N`, `B x y = 0`.

Note that for general (neither symmetric nor antisymmetric) bilinear forms this definition has a
chirality; in addition to this "left" orthogonal complement one could define a "right" orthogonal
complement for which, for all `y` in `N`, `B y x = 0`.  This variant definition is not currently
provided in mathlib. -/
def orthogonal (B : BilinForm R M) (N : Submodule R M) : Submodule R M where
  Carrier := { m | ∀, ∀ n ∈ N, ∀, IsOrtho B n m }
  zero_mem' := fun x _ => is_ortho_zero_right x
  add_mem' := fun x y hx hy n hn => by
    rw [is_ortho, add_right, show B n x = 0 from hx n hn, show B n y = 0 from hy n hn, zero_addₓ]
  smul_mem' := fun c x hx n hn => by
    rw [is_ortho, smul_right, show B n x = 0 from hx n hn, mul_zero]

variable {N L : Submodule R M}

@[simp]
theorem mem_orthogonal_iff {N : Submodule R M} {m : M} : m ∈ B.orthogonal N ↔ ∀, ∀ n ∈ N, ∀, IsOrtho B n m :=
  Iff.rfl

theorem orthogonal_le (h : N ≤ L) : B.orthogonal L ≤ B.orthogonal N := fun _ hn l hl => hn l (h hl)

theorem le_orthogonal_orthogonal (b : B.IsRefl) : N ≤ B.orthogonal (B.orthogonal N) := fun n hn m hm => b _ _ (hm n hn)

-- ↓ This lemma only applies in fields as we require `a * b = 0 → a = 0 ∨ b = 0`
theorem span_singleton_inf_orthogonal_eq_bot {B : BilinForm K V} {x : V} (hx : ¬B.IsOrtho x x) :
    (K∙x)⊓B.orthogonal (K∙x) = ⊥ := by
  rw [← Finset.coe_singleton]
  refine' eq_bot_iff.2 fun y h => _
  rcases mem_span_finset.1 h.1 with ⟨μ, rfl⟩
  have := h.2 x _
  · rw [Finset.sum_singleton] at this⊢
    suffices hμzero : μ x = 0
    · rw [hμzero, zero_smul, Submodule.mem_bot]
      
    change B x (μ x • x) = 0 at this
    rw [smul_right] at this
    exact Or.elim (zero_eq_mul.mp this.symm) id fun hfalse => False.elim <| hx hfalse
    
  · rw [Submodule.mem_span] <;> exact fun _ hp => hp <| Finset.mem_singleton_self _
    

-- ↓ This lemma only applies in fields since we use the `mul_eq_zero`
theorem orthogonal_span_singleton_eq_to_lin_ker {B : BilinForm K V} (x : V) :
    B.orthogonal (K∙x) = (BilinForm.toLin B x).ker := by
  ext y
  simp_rw [mem_orthogonal_iff, LinearMap.mem_ker, Submodule.mem_span_singleton]
  constructor
  · exact fun h => h x ⟨1, one_smul _ _⟩
    
  · rintro h _ ⟨z, rfl⟩
    rw [is_ortho, smul_left, mul_eq_zero]
    exact Or.intro_rightₓ _ h
    

theorem span_singleton_sup_orthogonal_eq_top {B : BilinForm K V} {x : V} (hx : ¬B.IsOrtho x x) :
    (K∙x)⊔B.orthogonal (K∙x) = ⊤ := by
  rw [orthogonal_span_singleton_eq_to_lin_ker]
  exact LinearMap.span_singleton_sup_ker_eq_top _ hx

/-- Given a bilinear form `B` and some `x` such that `B x x ≠ 0`, the span of the singleton of `x`
  is complement to its orthogonal complement. -/
theorem is_compl_span_singleton_orthogonal {B : BilinForm K V} {x : V} (hx : ¬B.IsOrtho x x) :
    IsCompl (K∙x) (B.orthogonal <| K∙x) :=
  { Disjoint := eq_bot_iff.1 <| span_singleton_inf_orthogonal_eq_bot hx,
    Codisjoint := eq_top_iff.1 <| span_singleton_sup_orthogonal_eq_top hx }

end Orthogonal

/-- The restriction of a bilinear form on a submodule. -/
@[simps apply]
def restrict (B : BilinForm R M) (W : Submodule R M) : BilinForm R W where
  bilin := fun a b => B a b
  bilin_add_left := fun _ _ _ => add_left _ _ _
  bilin_smul_left := fun _ _ _ => smul_left _ _ _
  bilin_add_right := fun _ _ _ => add_right _ _ _
  bilin_smul_right := fun _ _ _ => smul_right _ _ _

/-- The restriction of a symmetric bilinear form on a submodule is also symmetric. -/
theorem restrict_symm (B : BilinForm R M) (b : B.IsSymm) (W : Submodule R M) : (B.restrict W).IsSymm := fun x y => b x y

/-- A nondegenerate bilinear form is a bilinear form such that the only element that is orthogonal
to every other element is `0`; i.e., for all nonzero `m` in `M`, there exists `n` in `M` with
`B m n ≠ 0`.

Note that for general (neither symmetric nor antisymmetric) bilinear forms this definition has a
chirality; in addition to this "left" nondegeneracy condition one could define a "right"
nondegeneracy condition that in the situation described, `B n m ≠ 0`.  This variant definition is
not currently provided in mathlib. In finite dimension either definition implies the other. -/
def Nondegenerate (B : BilinForm R M) : Prop :=
  ∀ m : M, (∀ n : M, B m n = 0) → m = 0

section

variable (R M)

/-- In a non-trivial module, zero is not non-degenerate. -/
theorem not_nondegenerate_zero [Nontrivial M] : ¬(0 : BilinForm R M).Nondegenerate :=
  let ⟨m, hm⟩ := exists_ne (0 : M)
  fun h => hm ((h m) fun n => rfl)

end

variable {M₂' : Type _}

variable [AddCommMonoidₓ M₂'] [Module R₂ M₂']

theorem Nondegenerate.ne_zero [Nontrivial M] {B : BilinForm R M} (h : B.Nondegenerate) : B ≠ 0 := fun h0 =>
  not_nondegenerate_zero R M <| h0 ▸ h

theorem Nondegenerate.congr {B : BilinForm R₂ M₂} (e : M₂ ≃ₗ[R₂] M₂') (h : B.Nondegenerate) :
    (congr e B).Nondegenerate := fun m hm =>
  e.symm.map_eq_zero_iff.1 <| (h (e.symm m)) fun n => (congr_arg _ (e.symm_apply_apply n).symm).trans (hm (e n))

@[simp]
theorem nondegenerate_congr_iff {B : BilinForm R₂ M₂} (e : M₂ ≃ₗ[R₂] M₂') :
    (congr e B).Nondegenerate ↔ B.Nondegenerate :=
  ⟨fun h => by
    convert h.congr e.symm
    rw [congr_congr, e.self_trans_symm, congr_refl, LinearEquiv.refl_apply], Nondegenerate.congr e⟩

/-- A bilinear form is nondegenerate if and only if it has a trivial kernel. -/
theorem nondegenerate_iff_ker_eq_bot {B : BilinForm R₂ M₂} : B.Nondegenerate ↔ B.toLin.ker = ⊥ := by
  rw [LinearMap.ker_eq_bot']
  constructor <;> intro h
  · refine' fun m hm => h _ fun x => _
    rw [← to_lin_apply, hm]
    rfl
    
  · intro m hm
    apply h
    ext x
    exact hm x
    

theorem Nondegenerate.ker_eq_bot {B : BilinForm R₂ M₂} (h : B.Nondegenerate) : B.toLin.ker = ⊥ :=
  nondegenerate_iff_ker_eq_bot.mp h

/-- The restriction of a reflexive bilinear form `B` onto a submodule `W` is
nondegenerate if `disjoint W (B.orthogonal W)`. -/
theorem nondegenerate_restrict_of_disjoint_orthogonal (B : BilinForm R₁ M₁) (b : B.IsRefl) {W : Submodule R₁ M₁}
    (hW : Disjoint W (B.orthogonal W)) : (B.restrict W).Nondegenerate := by
  rintro ⟨x, hx⟩ b₁
  rw [Submodule.mk_eq_zero, ← Submodule.mem_bot R₁]
  refine' hW ⟨hx, fun y hy => _⟩
  specialize b₁ ⟨y, hy⟩
  rw [restrict_apply, Submodule.coe_mk, Submodule.coe_mk] at b₁
  exact is_ortho_def.mpr (b x y b₁)

/-- An orthogonal basis with respect to a nondegenerate bilinear form has no self-orthogonal
elements. -/
theorem IsOrthoₓ.not_is_ortho_basis_self_of_nondegenerate {n : Type w} [Nontrivial R] {B : BilinForm R M}
    {v : Basis n R M} (h : B.IsOrtho v) (hB : B.Nondegenerate) (i : n) : ¬B.IsOrtho (v i) (v i) := by
  intro ho
  refine' v.ne_zero i ((hB (v i)) fun m => _)
  obtain ⟨vi, rfl⟩ := v.repr.symm.surjective m
  rw [Basis.repr_symm_apply, Finsupp.total_apply, Finsupp.sum, sum_right]
  apply Finset.sum_eq_zero
  rintro j -
  rw [smul_right]
  convert mul_zero _ using 2
  obtain rfl | hij := eq_or_ne i j
  · exact ho
    
  · exact h i j hij
    

/-- Given an orthogonal basis with respect to a bilinear form, the bilinear form is nondegenerate
iff the basis has no elements which are self-orthogonal. -/
theorem IsOrthoₓ.nondegenerate_iff_not_is_ortho_basis_self {n : Type w} [Nontrivial R] [NoZeroDivisors R]
    (B : BilinForm R M) (v : Basis n R M) (hO : B.IsOrtho v) : B.Nondegenerate ↔ ∀ i, ¬B.IsOrtho (v i) (v i) := by
  refine' ⟨hO.not_is_ortho_basis_self_of_nondegenerate, fun ho m hB => _⟩
  obtain ⟨vi, rfl⟩ := v.repr.symm.surjective m
  rw [LinearEquiv.map_eq_zero_iff]
  ext i
  rw [Finsupp.zero_apply]
  specialize hB (v i)
  simp_rw [Basis.repr_symm_apply, Finsupp.total_apply, Finsupp.sum, sum_left, smul_left] at hB
  rw [Finset.sum_eq_single i] at hB
  · exact eq_zero_of_ne_zero_of_mul_right_eq_zero (ho i) hB
    
  · intro j hj hij
    convert mul_zero _ using 2
    exact hO j i hij
    
  · intro hi
    convert zero_mul _ using 2
    exact finsupp.not_mem_support_iff.mp hi
    

section

theorem to_lin_restrict_ker_eq_inf_orthogonal (B : BilinForm K V) (W : Subspace K V) (b : B.IsRefl) :
    (B.toLin.domRestrict W).ker.map W.Subtype = (W⊓B.orthogonal ⊤ : Subspace K V) := by
  ext x
  constructor <;> intro hx
  · rcases hx with ⟨⟨x, hx⟩, hker, rfl⟩
    erw [LinearMap.mem_ker] at hker
    constructor
    · simp [← hx]
      
    · intro y _
      rw [is_ortho, b]
      change (B.to_lin.dom_restrict W) ⟨x, hx⟩ y = 0
      rw [hker]
      rfl
      
    
  · simp_rw [Submodule.mem_map, LinearMap.mem_ker]
    refine' ⟨⟨x, hx.1⟩, _, rfl⟩
    ext y
    change B x y = 0
    rw [b]
    exact hx.2 _ Submodule.mem_top
    

theorem to_lin_restrict_range_dual_annihilator_comap_eq_orthogonal (B : BilinForm K V) (W : Subspace K V) :
    (B.toLin.domRestrict W).range.dualAnnihilatorComap = B.orthogonal W := by
  ext x
  constructor <;> rw [mem_orthogonal_iff] <;> intro hx
  · intro y hy
    rw [Submodule.mem_dual_annihilator_comap_iff] at hx
    refine' hx (B.to_lin.dom_restrict W ⟨y, hy⟩) ⟨⟨y, hy⟩, rfl⟩
    
  · rw [Submodule.mem_dual_annihilator_comap_iff]
    rintro _ ⟨⟨w, hw⟩, rfl⟩
    exact hx w hw
    

variable [FiniteDimensional K V]

open FiniteDimensional

theorem finrank_add_finrank_orthogonal {B : BilinForm K V} {W : Subspace K V} (b₁ : B.IsRefl) :
    finrank K W + finrank K (B.orthogonal W) = finrank K V + finrank K (W⊓B.orthogonal ⊤ : Subspace K V) := by
  rw [← to_lin_restrict_ker_eq_inf_orthogonal _ _ b₁, ← to_lin_restrict_range_dual_annihilator_comap_eq_orthogonal _ _,
    finrank_map_subtype_eq]
  conv_rhs =>
    rw [← @Subspace.finrank_add_finrank_dual_annihilator_comap_eq K V _ _ _ _ (B.to_lin.dom_restrict W).range,
      add_commₓ, ← add_assocₓ, add_commₓ (finrank K ↥(B.to_lin.dom_restrict W).ker),
      LinearMap.finrank_range_add_finrank_ker]

/-- A subspace is complement to its orthogonal complement with respect to some
reflexive bilinear form if that bilinear form restricted on to the subspace is nondegenerate. -/
theorem restrict_nondegenerate_of_is_compl_orthogonal {B : BilinForm K V} {W : Subspace K V} (b₁ : B.IsRefl)
    (b₂ : (B.restrict W).Nondegenerate) : IsCompl W (B.orthogonal W) := by
  have : W⊓B.orthogonal W = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hx₁, hx₂⟩ := Submodule.mem_inf.1 hx
    refine' Subtype.mk_eq_mk.1 (b₂ ⟨x, hx₁⟩ _)
    rintro ⟨n, hn⟩
    rw [restrict_apply, Submodule.coe_mk, Submodule.coe_mk, b₁]
    exact hx₂ n hn
  refine' IsCompl.of_eq this (eq_top_of_finrank_eq <| (Submodule.finrank_le _).antisymm _)
  conv_rhs => rw [← add_zeroₓ (finrank K _)]
  rw [← finrank_bot K V, ← this, Submodule.dim_sup_add_dim_inf_eq, finrank_add_finrank_orthogonal b₁]
  exact le_self_add

/-- A subspace is complement to its orthogonal complement with respect to some reflexive bilinear
form if and only if that bilinear form restricted on to the subspace is nondegenerate. -/
theorem restrict_nondegenerate_iff_is_compl_orthogonal {B : BilinForm K V} {W : Subspace K V} (b₁ : B.IsRefl) :
    (B.restrict W).Nondegenerate ↔ IsCompl W (B.orthogonal W) :=
  ⟨fun b₂ => restrict_nondegenerate_of_is_compl_orthogonal b₁ b₂, fun h =>
    B.nondegenerate_restrict_of_disjoint_orthogonal b₁ h.1⟩

/-- Given a nondegenerate bilinear form `B` on a finite-dimensional vector space, `B.to_dual` is
the linear equivalence between a vector space and its dual with the underlying linear map
`B.to_lin`. -/
noncomputable def toDual (B : BilinForm K V) (b : B.Nondegenerate) : V ≃ₗ[K] Module.Dual K V :=
  B.toLin.linearEquivOfInjective (LinearMap.ker_eq_bot.mp <| b.ker_eq_bot) Subspace.dual_finrank_eq.symm

theorem to_dual_def {B : BilinForm K V} (b : B.Nondegenerate) {m n : V} : B.toDual b m n = B m n :=
  rfl

section DualBasis

variable {ι : Type _} [DecidableEq ι] [Fintype ι]

/-- The `B`-dual basis `B.dual_basis hB b` to a finite basis `b` satisfies
`B (B.dual_basis hB b i) (b j) = B (b i) (B.dual_basis hB b j) = if i = j then 1 else 0`,
where `B` is a nondegenerate (symmetric) bilinear form and `b` is a finite basis. -/
noncomputable def dualBasis (B : BilinForm K V) (hB : B.Nondegenerate) (b : Basis ι K V) : Basis ι K V :=
  b.dualBasis.map (B.toDual hB).symm

@[simp]
theorem dual_basis_repr_apply (B : BilinForm K V) (hB : B.Nondegenerate) (b : Basis ι K V) (x i) :
    (B.dualBasis hB b).repr x i = B x (b i) := by
  rw [dual_basis, Basis.map_repr, LinearEquiv.symm_symm, LinearEquiv.trans_apply, Basis.dual_basis_repr, to_dual_def]

theorem apply_dual_basis_left (B : BilinForm K V) (hB : B.Nondegenerate) (b : Basis ι K V) (i j) :
    B (B.dualBasis hB b i) (b j) = if j = i then 1 else 0 := by
  rw [dual_basis, Basis.map_apply, Basis.coe_dual_basis, ← to_dual_def hB, LinearEquiv.apply_symm_apply,
    Basis.coord_apply, Basis.repr_self, Finsupp.single_apply]

theorem apply_dual_basis_right (B : BilinForm K V) (hB : B.Nondegenerate) (sym : B.IsSymm) (b : Basis ι K V) (i j) :
    B (b i) (B.dualBasis hB b j) = if i = j then 1 else 0 := by
  rw [Sym, apply_dual_basis_left]

end DualBasis

end

/-! We note that we cannot use `bilin_form.restrict_nondegenerate_iff_is_compl_orthogonal` for the
lemma below since the below lemma does not require `V` to be finite dimensional. However,
`bilin_form.restrict_nondegenerate_iff_is_compl_orthogonal` does not require `B` to be nondegenerate
on the whole space. -/


/-- The restriction of a reflexive, non-degenerate bilinear form on the orthogonal complement of
the span of a singleton is also non-degenerate. -/
theorem restrict_orthogonal_span_singleton_nondegenerate (B : BilinForm K V) (b₁ : B.Nondegenerate) (b₂ : B.IsRefl)
    {x : V} (hx : ¬B.IsOrtho x x) : nondegenerate <| B.restrict <| B.orthogonal (K∙x) := by
  refine' fun m hm => Submodule.coe_eq_zero.1 (b₁ m.1 fun n => _)
  have : n ∈ (K∙x)⊔B.orthogonal (K∙x) := (span_singleton_sup_orthogonal_eq_top hx).symm ▸ Submodule.mem_top
  rcases Submodule.mem_sup.1 this with ⟨y, hy, z, hz, rfl⟩
  specialize hm ⟨z, hz⟩
  rw [restrict] at hm
  erw [add_right,
    show B m.1 y = 0 by
      rw [b₂] <;> exact m.2 y hy,
    hm, add_zeroₓ]

section LinearAdjoints

theorem comp_left_injective (B : BilinForm R₁ M₁) (b : B.Nondegenerate) : Function.Injective B.compLeft := fun φ ψ h =>
  by
  ext w
  refine' eq_of_sub_eq_zero (b _ _)
  intro v
  rw [sub_left, ← comp_left_apply, ← comp_left_apply, ← h, sub_self]

theorem is_adjoint_pair_unique_of_nondegenerate (B : BilinForm R₁ M₁) (b : B.Nondegenerate) (φ ψ₁ ψ₂ : M₁ →ₗ[R₁] M₁)
    (hψ₁ : IsAdjointPair B B ψ₁ φ) (hψ₂ : IsAdjointPair B B ψ₂ φ) : ψ₁ = ψ₂ :=
  B.comp_left_injective b <|
    ext fun v w => by
      rw [comp_left_apply, comp_left_apply, hψ₁, hψ₂]

variable [FiniteDimensional K V]

/-- Given bilinear forms `B₁, B₂` where `B₂` is nondegenerate, `symm_comp_of_nondegenerate`
is the linear map `B₂.to_lin⁻¹ ∘ B₁.to_lin`. -/
noncomputable def symmCompOfNondegenerate (B₁ B₂ : BilinForm K V) (b₂ : B₂.Nondegenerate) : V →ₗ[K] V :=
  (B₂.toDual b₂).symm.toLinearMap.comp B₁.toLin

theorem comp_symm_comp_of_nondegenerate_apply (B₁ : BilinForm K V) {B₂ : BilinForm K V} (b₂ : B₂.Nondegenerate)
    (v : V) : toLin B₂ (B₁.symmCompOfNondegenerate B₂ b₂ v) = toLin B₁ v := by
  erw [symm_comp_of_nondegenerate, LinearEquiv.apply_symm_apply (B₂.to_dual b₂) _]

@[simp]
theorem symm_comp_of_nondegenerate_left_apply (B₁ : BilinForm K V) {B₂ : BilinForm K V} (b₂ : B₂.Nondegenerate)
    (v w : V) : B₂ (symmCompOfNondegenerate B₁ B₂ b₂ w) v = B₁ w v := by
  conv_lhs => rw [← BilinForm.to_lin_apply, comp_symm_comp_of_nondegenerate_apply]
  rfl

/-- Given the nondegenerate bilinear form `B` and the linear map `φ`,
`left_adjoint_of_nondegenerate` provides the left adjoint of `φ` with respect to `B`.
The lemma proving this property is `bilin_form.is_adjoint_pair_left_adjoint_of_nondegenerate`. -/
noncomputable def leftAdjointOfNondegenerate (B : BilinForm K V) (b : B.Nondegenerate) (φ : V →ₗ[K] V) : V →ₗ[K] V :=
  symmCompOfNondegenerate (B.compRight φ) B b

theorem is_adjoint_pair_left_adjoint_of_nondegenerate (B : BilinForm K V) (b : B.Nondegenerate) (φ : V →ₗ[K] V) :
    IsAdjointPair B B (B.leftAdjointOfNondegenerate b φ) φ := fun x y =>
  (B.compRight φ).symm_comp_of_nondegenerate_left_apply b y x

/-- Given the nondegenerate bilinear form `B`, the linear map `φ` has a unique left adjoint given by
`bilin_form.left_adjoint_of_nondegenerate`. -/
theorem is_adjoint_pair_iff_eq_of_nondegenerate (B : BilinForm K V) (b : B.Nondegenerate) (ψ φ : V →ₗ[K] V) :
    IsAdjointPair B B ψ φ ↔ ψ = B.leftAdjointOfNondegenerate b φ :=
  ⟨fun h => B.is_adjoint_pair_unique_of_nondegenerate b φ ψ _ h (is_adjoint_pair_left_adjoint_of_nondegenerate _ _ _),
    fun h => h.symm ▸ is_adjoint_pair_left_adjoint_of_nondegenerate _ _ _⟩

end LinearAdjoints

end BilinForm

