/-
Copyright (c) 2020 Alexander Bentkamp, Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp, Sébastien Gouëzel, Eric Wieser
-/
import Mathbin.Algebra.Order.Smul
import Mathbin.Data.Complex.Basic
import Mathbin.Data.Fin.VecNotation
import Mathbin.FieldTheory.Tower

/-!
# Complex number as a vector space over `ℝ`

This file contains the following instances:
* Any `•`-structure (`has_smul`, `mul_action`, `distrib_mul_action`, `module`, `algebra`) on
  `ℝ` imbues a corresponding structure on `ℂ`. This includes the statement that `ℂ` is an `ℝ`
  algebra.
* any complex vector space is a real vector space;
* any finite dimensional complex vector space is a finite dimensional real vector space;
* the space of `ℝ`-linear maps from a real vector space to a complex vector space is a complex
  vector space.

It also defines bundled versions of four standard maps (respectively, the real part, the imaginary
part, the embedding of `ℝ` in `ℂ`, and the complex conjugate):

* `complex.re_lm` (`ℝ`-linear map);
* `complex.im_lm` (`ℝ`-linear map);
* `complex.of_real_am` (`ℝ`-algebra (homo)morphism);
* `complex.conj_ae` (`ℝ`-algebra equivalence).

It also provides a universal property of the complex numbers `complex.lift`, which constructs a
`ℂ →ₐ[ℝ] A` into any `ℝ`-algebra `A` given a square root of `-1`.

-/


namespace Complex

open ComplexConjugate

variable {R : Type _} {S : Type _}

section

variable [HasSmul R ℝ]

/- The useless `0` multiplication in `smul` is to make sure that
`restrict_scalars.module ℝ ℂ ℂ = complex.module` definitionally. -/
instance : HasSmul R ℂ where smul := fun r x => ⟨r • x.re - 0 * x.im, r • x.im + 0 * x.re⟩

theorem smul_re (r : R) (z : ℂ) : (r • z).re = r • z.re := by
  simp [← (· • ·)]

theorem smul_im (r : R) (z : ℂ) : (r • z).im = r • z.im := by
  simp [← (· • ·)]

@[simp]
theorem real_smul {x : ℝ} {z : ℂ} : x • z = x * z :=
  rfl

end

instance [HasSmul R ℝ] [HasSmul S ℝ] [SmulCommClass R S ℝ] :
    SmulCommClass R S ℂ where smul_comm := fun r s x => by
    ext <;> simp [← smul_re, ← smul_im, ← smul_comm]

instance [HasSmul R S] [HasSmul R ℝ] [HasSmul S ℝ] [IsScalarTower R S ℝ] :
    IsScalarTower R S ℂ where smul_assoc := fun r s x => by
    ext <;> simp [← smul_re, ← smul_im, ← smul_assoc]

instance [HasSmul R ℝ] [HasSmul Rᵐᵒᵖ ℝ] [IsCentralScalar R ℝ] :
    IsCentralScalar R ℂ where op_smul_eq_smul := fun r x => by
    ext <;> simp [← smul_re, ← smul_im, ← op_smul_eq_smul]

instance [Monoidₓ R] [MulAction R ℝ] : MulAction R ℂ where
  one_smul := fun x => by
    ext <;> simp [← smul_re, ← smul_im, ← one_smul]
  mul_smul := fun r s x => by
    ext <;> simp [← smul_re, ← smul_im, ← mul_smul]

instance [Semiringₓ R] [DistribMulAction R ℝ] : DistribMulAction R ℂ where
  smul_add := fun r x y => by
    ext <;> simp [← smul_re, ← smul_im, ← smul_add]
  smul_zero := fun r => by
    ext <;> simp [← smul_re, ← smul_im, ← smul_zero]

instance [Semiringₓ R] [Module R ℝ] : Module R ℂ where
  add_smul := fun r s x => by
    ext <;> simp [← smul_re, ← smul_im, ← add_smul]
  zero_smul := fun r => by
    ext <;> simp [← smul_re, ← smul_im, ← zero_smul]

instance [CommSemiringₓ R] [Algebra R ℝ] : Algebra R ℂ :=
  { Complex.ofReal.comp (algebraMap R ℝ) with smul := (· • ·),
    smul_def' := fun r x => by
      ext <;> simp [← smul_re, ← smul_im, ← Algebra.smul_def],
    commutes' := fun r ⟨xr, xi⟩ => by
      ext <;> simp [← smul_re, ← smul_im, ← Algebra.commutes] }

instance : StarModule ℝ ℂ :=
  ⟨fun r x => by
    simp only [← star_def, ← star_trivial, ← real_smul, ← map_mul, ← conj_of_real]⟩

@[simp]
theorem coe_algebra_map : (algebraMap ℝ ℂ : ℝ → ℂ) = coe :=
  rfl

section

variable {A : Type _} [Semiringₓ A] [Algebra ℝ A]

/-- We need this lemma since `complex.coe_algebra_map` diverts the simp-normal form away from
`alg_hom.commutes`. -/
@[simp]
theorem _root_.alg_hom.map_coe_real_complex (f : ℂ →ₐ[ℝ] A) (x : ℝ) : f x = algebraMap ℝ A x :=
  f.commutes x

/-- Two `ℝ`-algebra homomorphisms from ℂ are equal if they agree on `complex.I`. -/
@[ext]
theorem alg_hom_ext ⦃f g : ℂ →ₐ[ℝ] A⦄ (h : f i = g i) : f = g := by
  ext ⟨x, y⟩
  simp only [← mk_eq_add_mul_I, ← AlgHom.map_add, ← AlgHom.map_coe_real_complex, ← AlgHom.map_mul, ← h]

end

section

open ComplexOrder

protected theorem ordered_smul : OrderedSmul ℝ ℂ :=
  OrderedSmul.mk' fun a b r hab hr =>
    ⟨by
      simp [← hr, ← hab.1.le], by
      simp [← hab.2]⟩

localized [ComplexOrder] attribute [instance] Complex.ordered_smul

end

open Submodule FiniteDimensional

-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:30:4: unsupported: too many args: fin_cases ... #[[]]
/-- `ℂ` has a basis over `ℝ` given by `1` and `I`. -/
noncomputable def basisOneI : Basis (Finₓ 2) ℝ ℂ :=
  Basis.ofEquivFun
    { toFun := fun z => ![z.re, z.im], invFun := fun c => c 0 + c 1 • I,
      left_inv := fun z => by
        simp ,
      right_inv := fun c => by
        ext i
        fin_cases i <;> simp ,
      map_add' := fun z z' => by
        simp ,-- why does `simp` not know how to apply `smul_cons`, which is a `@[simp]` lemma, here?
      map_smul' := fun c z => by
        simp [← Matrix.smul_cons c z.re, ← Matrix.smul_cons c z.im] }

@[simp]
theorem coe_basis_one_I_repr (z : ℂ) : ⇑(basisOneI.repr z) = ![z.re, z.im] :=
  rfl

-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:30:4: unsupported: too many args: fin_cases ... #[[]]
-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:30:4: unsupported: too many args: fin_cases ... #[[]]
@[simp]
theorem coe_basis_one_I : ⇑basis_one_I = ![1, i] :=
  funext fun i =>
    Basis.apply_eq_iff.mpr <|
      Finsupp.ext fun j => by
        fin_cases i <;>
          fin_cases j <;>
            simp only [← coe_basis_one_I_repr, ← Finsupp.single_eq_same, ← Finsupp.single_eq_of_ne, ←
              Matrix.cons_val_zero, ← Matrix.cons_val_one, ← Matrix.head_cons, ← Nat.one_ne_zero, ←
              Finₓ.one_eq_zero_iff, ← Finₓ.zero_eq_one_iff, ← Ne.def, ← not_false_iff, ← one_re, ← one_im, ← I_re, ←
              I_im]

instance : FiniteDimensional ℝ ℂ :=
  of_fintype_basis basisOneI

@[simp]
theorem finrank_real_complex : FiniteDimensional.finrank ℝ ℂ = 2 := by
  rw [finrank_eq_card_basis basis_one_I, Fintype.card_fin]

@[simp]
theorem dim_real_complex : Module.rank ℝ ℂ = 2 := by
  simp [finrank_eq_dim, ← finrank_real_complex]

theorem dim_real_complex'.{u} : Cardinal.lift.{u} (Module.rank ℝ ℂ) = 2 := by
  simp [finrank_eq_dim, ← finrank_real_complex, ← bit0]

/-- `fact` version of the dimension of `ℂ` over `ℝ`, locally useful in the definition of the
circle. -/
theorem finrank_real_complex_fact : Fact (finrank ℝ ℂ = 2) :=
  ⟨finrank_real_complex⟩

end Complex

/- Register as an instance (with low priority) the fact that a complex vector space is also a real
vector space. -/
instance (priority := 900) Module.complexToReal (E : Type _) [AddCommGroupₓ E] [Module ℂ E] : Module ℝ E :=
  RestrictScalars.module ℝ ℂ E

instance Module.real_complex_tower (E : Type _) [AddCommGroupₓ E] [Module ℂ E] : IsScalarTower ℝ ℂ E :=
  RestrictScalars.is_scalar_tower ℝ ℂ E

@[simp, norm_cast]
theorem Complex.coe_smul {E : Type _} [AddCommGroupₓ E] [Module ℂ E] (x : ℝ) (y : E) : (x : ℂ) • y = x • y :=
  rfl

instance (priority := 100) FiniteDimensional.complex_to_real (E : Type _) [AddCommGroupₓ E] [Module ℂ E]
    [FiniteDimensional ℂ E] : FiniteDimensional ℝ E :=
  FiniteDimensional.trans ℝ ℂ E

theorem dim_real_of_complex (E : Type _) [AddCommGroupₓ E] [Module ℂ E] : Module.rank ℝ E = 2 * Module.rank ℂ E :=
  Cardinal.lift_inj.1 <| by
    rw [← dim_mul_dim' ℝ ℂ E, Complex.dim_real_complex]
    simp [← bit0]

theorem finrank_real_of_complex (E : Type _) [AddCommGroupₓ E] [Module ℂ E] :
    FiniteDimensional.finrank ℝ E = 2 * FiniteDimensional.finrank ℂ E := by
  rw [← FiniteDimensional.finrank_mul_finrank ℝ ℂ E, Complex.finrank_real_complex]

instance (priority := 900) StarModule.complex_to_real {E : Type _} [AddCommGroupₓ E] [HasStar E] [Module ℂ E]
    [StarModule ℂ E] : StarModule ℝ E :=
  ⟨fun r a => by
    rw [star_trivial r, restrict_scalars_smul_def, restrict_scalars_smul_def, star_smul, Complex.coe_algebra_map,
      Complex.star_def, Complex.conj_of_real]⟩

namespace Complex

open ComplexConjugate

/-- Linear map version of the real part function, from `ℂ` to `ℝ`. -/
def reLm : ℂ →ₗ[ℝ] ℝ where
  toFun := fun x => x.re
  map_add' := add_re
  map_smul' := by
    simp

@[simp]
theorem re_lm_coe : ⇑re_lm = re :=
  rfl

/-- Linear map version of the imaginary part function, from `ℂ` to `ℝ`. -/
def imLm : ℂ →ₗ[ℝ] ℝ where
  toFun := fun x => x.im
  map_add' := add_im
  map_smul' := by
    simp

@[simp]
theorem im_lm_coe : ⇑im_lm = im :=
  rfl

/-- `ℝ`-algebra morphism version of the canonical embedding of `ℝ` in `ℂ`. -/
def ofRealAm : ℝ →ₐ[ℝ] ℂ :=
  Algebra.ofId ℝ ℂ

@[simp]
theorem of_real_am_coe : ⇑of_real_am = coe :=
  rfl

/-- `ℝ`-algebra isomorphism version of the complex conjugation function from `ℂ` to `ℂ` -/
def conjAe : ℂ ≃ₐ[ℝ] ℂ :=
  { conj with invFun := conj, left_inv := star_star, right_inv := star_star, commutes' := conj_of_real }

@[simp]
theorem conj_ae_coe : ⇑conj_ae = conj :=
  rfl

-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:30:4: unsupported: too many args: fin_cases ... #[[]]
-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:30:4: unsupported: too many args: fin_cases ... #[[]]
-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `«expr!![ »
-- ./././Mathport/Syntax/Translate/Basic.lean:1144:14: unsupported user notation matrix.notation
/-- The matrix representation of `conj_ae`. -/
@[simp]
theorem to_matrix_conj_ae :
    LinearMap.toMatrix basisOneI basisOneI conjAe.toLinearMap =
      «expr!![ » "./././Mathport/Syntax/Translate/Basic.lean:1144:14: unsupported user notation matrix.notation" :=
  by
  ext i j
  simp [← LinearMap.to_matrix_apply]
  fin_cases i <;> fin_cases j <;> simp

section lift

variable {A : Type _} [Ringₓ A] [Algebra ℝ A]

/-- There is an alg_hom from `ℂ` to any `ℝ`-algebra with an element that squares to `-1`.

See `complex.lift` for this as an equiv. -/
def liftAux (I' : A) (hf : I' * I' = -1) : ℂ →ₐ[ℝ] A :=
  AlgHom.ofLinearMap ((Algebra.ofId ℝ A).toLinearMap.comp reLm + (LinearMap.toSpanSingleton _ _ I').comp imLm)
    (show algebraMap ℝ A 1 + (0 : ℝ) • I' = 1 by
      rw [RingHom.map_one, zero_smul, add_zeroₓ])
    fun ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ =>
    show
      algebraMap ℝ A (x₁ * x₂ - y₁ * y₂) + (x₁ * y₂ + y₁ * x₂) • I' =
        (algebraMap ℝ A x₁ + y₁ • I') * (algebraMap ℝ A x₂ + y₂ • I')
      by
      rw [add_mulₓ, mul_addₓ, mul_addₓ, add_commₓ _ (y₁ • I' * y₂ • I'), add_add_add_commₓ]
      congr 1
      -- equate "real" and "imaginary" parts
      · rw [smul_mul_smul, hf, smul_neg, ← Algebra.algebra_map_eq_smul_one, ← sub_eq_add_neg, ← RingHom.map_mul, ←
          RingHom.map_sub]
        
      · rw [Algebra.smul_def, Algebra.smul_def, Algebra.smul_def, ← Algebra.right_comm _ x₂, ← mul_assoc, ← add_mulₓ, ←
          RingHom.map_mul, ← RingHom.map_mul, ← RingHom.map_add]
        

@[simp]
theorem lift_aux_apply (I' : A) (hI') (z : ℂ) : liftAux I' hI' z = algebraMap ℝ A z.re + z.im • I' :=
  rfl

theorem lift_aux_apply_I (I' : A) (hI') : liftAux I' hI' i = I' := by
  simp

/-- A universal property of the complex numbers, providing a unique `ℂ →ₐ[ℝ] A` for every element
of `A` which squares to `-1`.

This can be used to embed the complex numbers in the `quaternion`s.

This isomorphism is named to match the very similar `zsqrtd.lift`. -/
@[simps (config := { simpRhs := true })]
def lift : { I' : A // I' * I' = -1 } ≃ (ℂ →ₐ[ℝ] A) where
  toFun := fun I' => liftAux I' I'.Prop
  invFun := fun F =>
    ⟨F i, by
      rw [← F.map_mul, I_mul_I, AlgHom.map_neg, AlgHom.map_one]⟩
  left_inv := fun I' => Subtype.ext <| lift_aux_apply_I I' I'.Prop
  right_inv := fun F => alg_hom_ext <| lift_aux_apply_I _ _

-- When applied to `complex.I` itself, `lift` is the identity.
@[simp]
theorem lift_aux_I : liftAux i I_mul_I = AlgHom.id ℝ ℂ :=
  alg_hom_ext <| lift_aux_apply_I _ _

-- When applied to `-complex.I`, `lift` is conjugation, `conj`.
@[simp]
theorem lift_aux_neg_I : liftAux (-I) ((neg_mul_neg _ _).trans I_mul_I) = conj_ae :=
  alg_hom_ext <| (lift_aux_apply_I _ _).trans conj_I.symm

end lift

end Complex

