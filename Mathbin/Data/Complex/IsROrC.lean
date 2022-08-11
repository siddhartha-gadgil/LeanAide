/-
Copyright (c) 2020 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
import Mathbin.Data.Real.Sqrt
import Mathbin.FieldTheory.Tower
import Mathbin.Analysis.NormedSpace.FiniteDimension
import Mathbin.Analysis.NormedSpace.Star.Basic

/-!
# `is_R_or_C`: a typeclass for ℝ or ℂ

This file defines the typeclass `is_R_or_C` intended to have only two instances:
ℝ and ℂ. It is meant for definitions and theorems which hold for both the real and the complex case,
and in particular when the real case follows directly from the complex case by setting `re` to `id`,
`im` to zero and so on. Its API follows closely that of ℂ.

Applications include defining inner products and Hilbert spaces for both the real and
complex case. One typically produces the definitions and proof for an arbitrary field of this
typeclass, which basically amounts to doing the complex case, and the two cases then fall out
immediately from the two instances of the class.

The instance for `ℝ` is registered in this file.
The instance for `ℂ` is declared in `analysis.complex.basic`.

## Implementation notes

The coercion from reals into an `is_R_or_C` field is done by registering `algebra_map ℝ K` as
a `has_coe_t`. For this to work, we must proceed carefully to avoid problems involving circular
coercions in the case `K=ℝ`; in particular, we cannot use the plain `has_coe` and must set
priorities carefully. This problem was already solved for `ℕ`, and we copy the solution detailed
in `data/nat/cast`. See also Note [coercion into rings] for more details.

In addition, several lemmas need to be set at priority 900 to make sure that they do not override
their counterparts in `complex.lean` (which causes linter errors).
-/


open BigOperators

section

-- mathport name: «expr𝓚»
local notation "𝓚" => algebraMap ℝ _

open ComplexConjugate

/-- This typeclass captures properties shared by ℝ and ℂ, with an API that closely matches that of ℂ.
-/
class IsROrC (K : Type _) extends NondiscreteNormedField K, StarRing K, NormedAlgebra ℝ K, CompleteSpace K where
  re : K →+ ℝ
  im : K →+ ℝ
  i : K
  -- Meant to be set to 0 for K=ℝ
  I_re_ax : re I = 0
  I_mul_I_ax : I = 0 ∨ I * I = -1
  re_add_im_ax : ∀ z : K, 𝓚 (re z) + 𝓚 (im z) * I = z
  of_real_re_ax : ∀ r : ℝ, re (𝓚 r) = r
  of_real_im_ax : ∀ r : ℝ, im (𝓚 r) = 0
  mul_re_ax : ∀ z w : K, re (z * w) = re z * re w - im z * im w
  mul_im_ax : ∀ z w : K, im (z * w) = re z * im w + im z * re w
  conj_re_ax : ∀ z : K, re (conj z) = re z
  conj_im_ax : ∀ z : K, im (conj z) = -im z
  conj_I_ax : conj I = -I
  norm_sq_eq_def_ax : ∀ z : K, ∥z∥ ^ 2 = re z * re z + im z * im z
  mul_im_I_ax : ∀ z : K, im z * im I = im z
  inv_def_ax : ∀ z : K, z⁻¹ = conj z * 𝓚 (∥z∥ ^ 2)⁻¹
  div_I_ax : ∀ z : K, z / I = -(z * I)

end

mk_simp_attribute is_R_or_C_simps := "Simp attribute for lemmas about `is_R_or_C`"

variable {K : Type _} [IsROrC K]

namespace IsROrC

open ComplexConjugate

/- The priority must be set at 900 to ensure that coercions are tried in the right order.
See Note [coercion into rings], or `data/nat/cast.lean` for more details. -/
noncomputable instance (priority := 900) algebraMapCoe : CoeTₓ ℝ K :=
  ⟨algebraMap ℝ K⟩

theorem of_real_alg (x : ℝ) : (x : K) = x • (1 : K) :=
  Algebra.algebra_map_eq_smul_one x

theorem algebra_map_eq_of_real : ⇑(algebraMap ℝ K) = coe :=
  rfl

@[simp, is_R_or_C_simps]
theorem re_add_im (z : K) : (re z : K) + im z * I = z :=
  IsROrC.re_add_im_ax z

@[simp, norm_cast, is_R_or_C_simps]
theorem of_real_re : ∀ r : ℝ, re (r : K) = r :=
  IsROrC.of_real_re_ax

@[simp, norm_cast, is_R_or_C_simps]
theorem of_real_im : ∀ r : ℝ, im (r : K) = 0 :=
  IsROrC.of_real_im_ax

@[simp, is_R_or_C_simps]
theorem mul_re : ∀ z w : K, re (z * w) = re z * re w - im z * im w :=
  IsROrC.mul_re_ax

@[simp, is_R_or_C_simps]
theorem mul_im : ∀ z w : K, im (z * w) = re z * im w + im z * re w :=
  IsROrC.mul_im_ax

theorem inv_def (z : K) : z⁻¹ = conj z * ((∥z∥ ^ 2)⁻¹ : ℝ) :=
  IsROrC.inv_def_ax z

theorem ext_iff : ∀ {z w : K}, z = w ↔ re z = re w ∧ im z = im w := fun z w =>
  { mp := by
      rintro rfl
      cc,
    mpr := by
      rintro ⟨h₁, h₂⟩
      rw [← re_add_im z, ← re_add_im w, h₁, h₂] }

theorem ext : ∀ {z w : K}, re z = re w → im z = im w → z = w := by
  simp_rw [ext_iff]
  cc

@[simp, norm_cast, is_R_or_C_simps]
theorem of_real_zero : ((0 : ℝ) : K) = 0 := by
  rw [of_real_alg, zero_smul]

@[simp, is_R_or_C_simps]
theorem zero_re' : re (0 : K) = (0 : ℝ) :=
  re.map_zero

@[simp, norm_cast, is_R_or_C_simps]
theorem of_real_one : ((1 : ℝ) : K) = 1 := by
  rw [of_real_alg, one_smul]

@[simp, is_R_or_C_simps]
theorem one_re : re (1 : K) = 1 := by
  rw [← of_real_one, of_real_re]

@[simp, is_R_or_C_simps]
theorem one_im : im (1 : K) = 0 := by
  rw [← of_real_one, of_real_im]

@[simp, norm_cast]
theorem of_real_inj {z w : ℝ} : (z : K) = (w : K) ↔ z = w :=
  { mp := fun h => by
      convert congr_arg re h <;> simp only [← of_real_re],
    mpr := fun h => by
      rw [h] }

@[simp, is_R_or_C_simps]
theorem bit0_re (z : K) : re (bit0 z) = bit0 (re z) := by
  simp only [← bit0, ← map_add]

@[simp, is_R_or_C_simps]
theorem bit1_re (z : K) : re (bit1 z) = bit1 (re z) := by
  simp only [← bit1, ← AddMonoidHom.map_add, ← bit0_re, ← add_right_injₓ, ← one_re]

@[simp, is_R_or_C_simps]
theorem bit0_im (z : K) : im (bit0 z) = bit0 (im z) := by
  simp only [← bit0, ← map_add]

@[simp, is_R_or_C_simps]
theorem bit1_im (z : K) : im (bit1 z) = bit0 (im z) := by
  simp only [← bit1, ← add_right_eq_selfₓ, ← AddMonoidHom.map_add, ← bit0_im, ← one_im]

@[simp, is_R_or_C_simps]
theorem of_real_eq_zero {z : ℝ} : (z : K) = 0 ↔ z = 0 := by
  rw [← of_real_zero] <;> exact of_real_inj

@[simp, is_R_or_C_simps, norm_cast]
theorem of_real_add ⦃r s : ℝ⦄ : ((r + s : ℝ) : K) = r + s := by
  apply (@IsROrC.ext_iff K _ ((r + s : ℝ) : K) (r + s)).mpr
  simp

@[simp, is_R_or_C_simps, norm_cast]
theorem of_real_bit0 (r : ℝ) : ((bit0 r : ℝ) : K) = bit0 (r : K) :=
  ext_iff.2 <| by
    simp [← bit0]

@[simp, is_R_or_C_simps, norm_cast]
theorem of_real_bit1 (r : ℝ) : ((bit1 r : ℝ) : K) = bit1 (r : K) :=
  ext_iff.2 <| by
    simp [← bit1]

-- Note: This can be proven by `norm_num` once K is proven to be of characteristic zero below.
theorem two_ne_zero : (2 : K) ≠ 0 := by
  intro h
  rw
    [show (2 : K) = ((2 : ℝ) : K) by
      norm_num,
    ← of_real_zero, of_real_inj] at h
  linarith

@[simp, norm_cast, is_R_or_C_simps]
theorem of_real_neg (r : ℝ) : ((-r : ℝ) : K) = -r :=
  ext_iff.2 <| by
    simp

@[simp, norm_cast, is_R_or_C_simps]
theorem of_real_mul (r s : ℝ) : ((r * s : ℝ) : K) = r * s :=
  ext_iff.2 <| by
    simp' with is_R_or_C_simps

@[simp, norm_cast, is_R_or_C_simps]
theorem of_real_smul (r x : ℝ) : r • (x : K) = (r : K) * (x : K) := by
  simp_rw [← smul_eq_mul, of_real_alg r]
  simp only [← Algebra.id.smul_eq_mul, ← one_mulₓ, ← Algebra.smul_mul_assoc]

@[is_R_or_C_simps]
theorem of_real_mul_re (r : ℝ) (z : K) : re (↑r * z) = r * re z := by
  simp only [← mul_re, ← of_real_im, ← zero_mul, ← of_real_re, ← sub_zero]

@[is_R_or_C_simps]
theorem of_real_mul_im (r : ℝ) (z : K) : im (↑r * z) = r * im z := by
  simp only [← add_zeroₓ, ← of_real_im, ← zero_mul, ← of_real_re, ← mul_im]

@[is_R_or_C_simps]
theorem smul_re : ∀ (r : ℝ) (z : K), re (r • z) = r * re z := fun r z => by
  rw [Algebra.smul_def]
  apply of_real_mul_re

@[is_R_or_C_simps]
theorem smul_im : ∀ (r : ℝ) (z : K), im (r • z) = r * im z := fun r z => by
  rw [Algebra.smul_def]
  apply of_real_mul_im

/-! ### The imaginary unit, `I` -/


/-- The imaginary unit. -/
@[simp, is_R_or_C_simps]
theorem I_re : re (i : K) = 0 :=
  I_re_ax

@[simp, is_R_or_C_simps]
theorem I_im (z : K) : im z * im (i : K) = im z :=
  mul_im_I_ax z

@[simp, is_R_or_C_simps]
theorem I_im' (z : K) : im (i : K) * im z = im z := by
  rw [mul_comm, I_im _]

@[simp, is_R_or_C_simps]
theorem I_mul_re (z : K) : re (I * z) = -im z := by
  simp only [← I_re, ← zero_sub, ← I_im', ← zero_mul, ← mul_re]

theorem I_mul_I : (i : K) = 0 ∨ (i : K) * I = -1 :=
  I_mul_I_ax

@[simp, is_R_or_C_simps]
theorem conj_re (z : K) : re (conj z) = re z :=
  IsROrC.conj_re_ax z

@[simp, is_R_or_C_simps]
theorem conj_im (z : K) : im (conj z) = -im z :=
  IsROrC.conj_im_ax z

@[simp, is_R_or_C_simps]
theorem conj_I : conj (i : K) = -I :=
  IsROrC.conj_I_ax

@[simp, is_R_or_C_simps]
theorem conj_of_real (r : ℝ) : conj (r : K) = (r : K) := by
  rw [ext_iff]
  simp only [← of_real_im, ← conj_im, ← eq_self_iff_true, ← conj_re, ← and_selfₓ, ← neg_zero]

@[simp, is_R_or_C_simps]
theorem conj_bit0 (z : K) : conj (bit0 z) = bit0 (conj z) := by
  simp only [← bit0, ← RingHom.map_add, ← eq_self_iff_true]

@[simp, is_R_or_C_simps]
theorem conj_bit1 (z : K) : conj (bit1 z) = bit1 (conj z) := by
  simp only [← bit0, ← ext_iff, ← bit1_re, ← conj_im, ← eq_self_iff_true, ← conj_re, ← neg_add_rev, ← and_selfₓ, ←
    bit1_im]

@[simp, is_R_or_C_simps]
theorem conj_neg_I : conj (-I) = (i : K) := by
  simp only [← conj_I, ← RingHom.map_neg, ← eq_self_iff_true, ← neg_negₓ]

theorem conj_eq_re_sub_im (z : K) : conj z = re z - im z * I := by
  rw [ext_iff]
  simp only [← add_zeroₓ, ← I_re, ← of_real_im, ← I_im, ← zero_sub, ← zero_mul, ← conj_im, ← of_real_re, ←
    eq_self_iff_true, ← sub_zero, ← conj_re, ← mul_im, ← neg_inj, ← and_selfₓ, ← mul_re, ← mul_zero, ← map_sub]

@[is_R_or_C_simps]
theorem conj_smul (r : ℝ) (z : K) : conj (r • z) = r • conj z := by
  simp_rw [conj_eq_re_sub_im]
  simp only [← smul_re, ← smul_im, ← of_real_mul]
  rw [smul_sub]
  simp_rw [of_real_alg]
  simp only [← one_mulₓ, ← Algebra.smul_mul_assoc]

theorem eq_conj_iff_real {z : K} : conj z = z ↔ ∃ r : ℝ, z = (r : K) := by
  constructor
  · intro h
    suffices im z = 0 by
      use re z
      rw [← add_zeroₓ (coe _)]
      convert (re_add_im z).symm
      simp [← this]
    contrapose! h
    rw [← re_add_im z]
    simp only [← conj_of_real, ← RingHom.map_add, ← RingHom.map_mul, ← conj_I_ax]
    rw [add_left_cancel_iffₓ, ext_iff]
    simpa [← neg_eq_iff_add_eq_zero, ← add_self_eq_zero]
    
  · rintro ⟨r, rfl⟩
    apply conj_of_real
    

@[simp]
theorem star_def : (HasStar.star : K → K) = conj :=
  rfl

variable (K)

/-- Conjugation as a ring equivalence. This is used to convert the inner product into a
sesquilinear product. -/
abbrev conjToRingEquiv : K ≃+* Kᵐᵒᵖ :=
  starRingEquiv

variable {K}

theorem eq_conj_iff_re {z : K} : conj z = z ↔ (re z : K) = z :=
  eq_conj_iff_real.trans
    ⟨by
      rintro ⟨r, rfl⟩ <;> simp , fun h => ⟨_, h.symm⟩⟩

/-- The norm squared function. -/
def normSq : K →*₀ ℝ where
  toFun := fun z => re z * re z + im z * im z
  map_zero' := by
    simp only [← add_zeroₓ, ← mul_zero, ← map_zero]
  map_one' := by
    simp only [← one_im, ← add_zeroₓ, ← mul_oneₓ, ← one_re, ← mul_zero]
  map_mul' := fun z w => by
    simp only [← mul_im, ← mul_re]
    ring

theorem norm_sq_eq_def {z : K} : ∥z∥ ^ 2 = re z * re z + im z * im z :=
  norm_sq_eq_def_ax z

theorem norm_sq_eq_def' (z : K) : normSq z = ∥z∥ ^ 2 := by
  rw [norm_sq_eq_def]
  rfl

@[simp, is_R_or_C_simps]
theorem norm_sq_of_real (r : ℝ) : ∥(r : K)∥ ^ 2 = r * r := by
  simp' only [← norm_sq_eq_def, ← add_zeroₓ, ← mul_zero] with is_R_or_C_simps

@[is_R_or_C_simps]
theorem norm_sq_zero : normSq (0 : K) = 0 :=
  normSq.map_zero

@[is_R_or_C_simps]
theorem norm_sq_one : normSq (1 : K) = 1 :=
  normSq.map_one

theorem norm_sq_nonneg (z : K) : 0 ≤ normSq z :=
  add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)

@[simp, is_R_or_C_simps]
theorem norm_sq_eq_zero {z : K} : normSq z = 0 ↔ z = 0 := by
  rw [norm_sq_eq_def']
  simp [← sq]

@[simp, is_R_or_C_simps]
theorem norm_sq_pos {z : K} : 0 < normSq z ↔ z ≠ 0 := by
  rw [lt_iff_le_and_ne, Ne, eq_comm] <;> simp [← norm_sq_nonneg]

@[simp, is_R_or_C_simps]
theorem norm_sq_neg (z : K) : normSq (-z) = normSq z := by
  simp only [← norm_sq_eq_def', ← norm_neg]

@[simp, is_R_or_C_simps]
theorem norm_sq_conj (z : K) : normSq (conj z) = normSq z := by
  simp' only [← norm_sq, ← neg_mul, ← MonoidWithZeroHom.coe_mk, ← mul_neg, ← neg_negₓ] with is_R_or_C_simps

@[simp, is_R_or_C_simps]
theorem norm_sq_mul (z w : K) : normSq (z * w) = normSq z * normSq w :=
  normSq.map_mul z w

theorem norm_sq_add (z w : K) : normSq (z + w) = normSq z + normSq w + 2 * re (z * conj w) := by
  simp' only [← norm_sq, ← map_add, ← MonoidWithZeroHom.coe_mk, ← mul_neg, ← sub_neg_eq_add] with is_R_or_C_simps
  ring

theorem re_sq_le_norm_sq (z : K) : re z * re z ≤ normSq z :=
  le_add_of_nonneg_right (mul_self_nonneg _)

theorem im_sq_le_norm_sq (z : K) : im z * im z ≤ normSq z :=
  le_add_of_nonneg_left (mul_self_nonneg _)

theorem mul_conj (z : K) : z * conj z = (normSq z : K) := by
  simp' only [← map_add, ← add_zeroₓ, ← ext_iff, ← MonoidWithZeroHom.coe_mk, ← add_left_injₓ, ← mul_eq_mul_left_iff, ←
    zero_mul, ← add_commₓ, ← true_orₓ, ← eq_self_iff_true, ← mul_neg, ← add_right_negₓ, ← zero_addₓ, ← norm_sq, ←
    mul_comm, ← and_selfₓ, ← neg_negₓ, ← mul_zero, ← sub_eq_neg_add, ← neg_zero] with is_R_or_C_simps

theorem add_conj (z : K) : z + conj z = 2 * re z := by
  simp only [← ext_iff, ← two_mul, ← map_add, ← add_zeroₓ, ← of_real_im, ← conj_im, ← of_real_re, ← eq_self_iff_true, ←
    add_right_negₓ, ← conj_re, ← and_selfₓ]

/-- The pseudo-coercion `of_real` as a `ring_hom`. -/
noncomputable def ofRealHom : ℝ →+* K :=
  algebraMap ℝ K

/-- The coercion from reals as a `ring_hom`. -/
noncomputable def coeHom : ℝ →+* K :=
  ⟨coe, of_real_one, of_real_mul, of_real_zero, of_real_add⟩

@[simp, norm_cast, is_R_or_C_simps]
theorem of_real_sub (r s : ℝ) : ((r - s : ℝ) : K) = r - s :=
  ext_iff.2 <| by
    simp only [← of_real_im, ← of_real_re, ← eq_self_iff_true, ← sub_zero, ← and_selfₓ, ← map_sub]

@[simp, norm_cast, is_R_or_C_simps]
theorem of_real_pow (r : ℝ) (n : ℕ) : ((r ^ n : ℝ) : K) = r ^ n := by
  induction n
  · simp only [← of_real_one, ← pow_zeroₓ]
    
  · simp only [*, ← of_real_mul, ← pow_succₓ]
    

theorem sub_conj (z : K) : z - conj z = 2 * im z * I := by
  simp' only [← ext_iff, ← two_mul, ← sub_eq_add_neg, ← add_mulₓ, ← map_add, ← add_zeroₓ, ← add_left_injₓ, ← zero_mul, ←
    map_add_neg, ← eq_self_iff_true, ← add_right_negₓ, ← and_selfₓ, ← neg_negₓ, ← mul_zero, ← neg_zero] with
    is_R_or_C_simps

theorem norm_sq_sub (z w : K) : normSq (z - w) = normSq z + normSq w - 2 * re (z * conj w) := by
  simp only [← norm_sq_add, ← sub_eq_add_neg, ← RingEquiv.map_neg, ← mul_neg, ← norm_sq_neg, ← map_neg]

theorem sqrt_norm_sq_eq_norm {z : K} : Real.sqrt (normSq z) = ∥z∥ := by
  have h₂ : ∥z∥ = Real.sqrt (∥z∥ ^ 2) := (Real.sqrt_sq (norm_nonneg z)).symm
  rw [h₂]
  exact congr_arg Real.sqrt (norm_sq_eq_def' z)

/-! ### Inversion -/


@[simp, is_R_or_C_simps]
theorem inv_re (z : K) : re z⁻¹ = re z / normSq z := by
  simp' only [← inv_def, ← norm_sq_eq_def, ← norm_sq, ← division_def, ← MonoidWithZeroHom.coe_mk, ← sub_zero, ←
    mul_zero] with is_R_or_C_simps

@[simp, is_R_or_C_simps]
theorem inv_im (z : K) : im z⁻¹ = im (-z) / normSq z := by
  simp' only [← inv_def, ← norm_sq_eq_def, ← norm_sq, ← division_def, ← of_real_im, ← MonoidWithZeroHom.coe_mk, ←
    of_real_re, ← zero_addₓ, ← map_neg, ← mul_zero] with is_R_or_C_simps

@[simp, norm_cast, is_R_or_C_simps]
theorem of_real_inv (r : ℝ) : ((r⁻¹ : ℝ) : K) = r⁻¹ := by
  rw [ext_iff]
  by_cases' r = 0
  · simp only [← h, ← of_real_zero, ← inv_zero, ← and_selfₓ, ← map_zero]
    
  · simp' only with is_R_or_C_simps
    field_simp [← h, ← norm_sq]
    

protected theorem inv_zero : (0⁻¹ : K) = 0 := by
  rw [← of_real_zero, ← of_real_inv, inv_zero]

protected theorem mul_inv_cancel {z : K} (h : z ≠ 0) : z * z⁻¹ = 1 := by
  rw [inv_def, ← mul_assoc, mul_conj, ← of_real_mul, ← norm_sq_eq_def', mul_inv_cancel (mt norm_sq_eq_zero.1 h),
    of_real_one]

theorem div_re (z w : K) : re (z / w) = re z * re w / normSq w + im z * im w / normSq w := by
  simp' only [← div_eq_mul_inv, ← mul_assoc, ← sub_eq_add_neg, ← neg_mul, ← mul_neg, ← neg_negₓ, ← map_neg] with
    is_R_or_C_simps

theorem div_im (z w : K) : im (z / w) = im z * re w / normSq w - re z * im w / normSq w := by
  simp' only [← div_eq_mul_inv, ← mul_assoc, ← sub_eq_add_neg, ← add_commₓ, ← neg_mul, ← mul_neg, ← map_neg] with
    is_R_or_C_simps

@[simp, is_R_or_C_simps]
theorem conj_inv (x : K) : conj x⁻¹ = (conj x)⁻¹ :=
  star_inv' _

@[simp, norm_cast, is_R_or_C_simps]
theorem of_real_div (r s : ℝ) : ((r / s : ℝ) : K) = r / s :=
  (@IsROrC.coeHom K _).map_div r s

theorem div_re_of_real {z : K} {r : ℝ} : re (z / r) = re z / r := by
  by_cases' h : r = 0
  · simp only [← h, ← of_real_zero, ← div_zero, ← zero_re']
    
  · change r ≠ 0 at h
    rw [div_eq_mul_inv, ← of_real_inv, div_eq_mul_inv]
    simp only [← one_div, ← of_real_im, ← of_real_re, ← sub_zero, ← mul_re, ← mul_zero]
    

@[simp, norm_cast, is_R_or_C_simps]
theorem of_real_zpow (r : ℝ) (n : ℤ) : ((r ^ n : ℝ) : K) = r ^ n :=
  (@IsROrC.coeHom K _).map_zpow r n

theorem I_mul_I_of_nonzero : (i : K) ≠ 0 → (i : K) * I = -1 := by
  have := I_mul_I_ax
  tauto

@[simp, is_R_or_C_simps]
theorem div_I (z : K) : z / I = -(z * I) := by
  by_cases' h : (I : K) = 0
  · simp [← h]
    
  · field_simp [← mul_assoc, ← I_mul_I_of_nonzero h]
    

@[simp, is_R_or_C_simps]
theorem inv_I : (i : K)⁻¹ = -I := by
  field_simp

@[simp, is_R_or_C_simps]
theorem norm_sq_inv (z : K) : normSq z⁻¹ = (normSq z)⁻¹ :=
  (@normSq K _).map_inv z

@[simp, is_R_or_C_simps]
theorem norm_sq_div (z w : K) : normSq (z / w) = normSq z / normSq w :=
  (@normSq K _).map_div z w

@[is_R_or_C_simps]
theorem norm_conj {z : K} : ∥conj z∥ = ∥z∥ := by
  simp only [sqrt_norm_sq_eq_norm, ← norm_sq_conj]

instance (priority := 100) :
    CstarRing K where norm_star_mul_self := fun x => (norm_mul _ _).trans <| congr_arg (· * ∥x∥) norm_conj

/-! ### Cast lemmas -/


@[simp, is_R_or_C_simps, norm_cast]
theorem of_real_nat_cast (n : ℕ) : ((n : ℝ) : K) = n :=
  show (algebraMap ℝ K) n = n from map_nat_cast ofRealHom n

--of_real_hom.map_nat_cast n
--@[simp, norm_cast, priority 900] theorem of_real_nat_cast (n : ℕ) : ((n : ℝ) : K) = n :=
@[simp, is_R_or_C_simps, norm_cast]
theorem nat_cast_re (n : ℕ) : re (n : K) = n := by
  rw [← of_real_nat_cast, of_real_re]

@[simp, is_R_or_C_simps, norm_cast]
theorem nat_cast_im (n : ℕ) : im (n : K) = 0 := by
  rw [← of_real_nat_cast, of_real_im]

@[simp, is_R_or_C_simps, norm_cast]
theorem of_real_int_cast (n : ℤ) : ((n : ℝ) : K) = n :=
  ofRealHom.map_int_cast n

@[simp, is_R_or_C_simps, norm_cast]
theorem int_cast_re (n : ℤ) : re (n : K) = n := by
  rw [← of_real_int_cast, of_real_re]

@[simp, is_R_or_C_simps, norm_cast]
theorem int_cast_im (n : ℤ) : im (n : K) = 0 := by
  rw [← of_real_int_cast, of_real_im]

@[simp, is_R_or_C_simps, norm_cast]
theorem of_real_rat_cast (n : ℚ) : ((n : ℝ) : K) = n :=
  map_rat_cast (@IsROrC.ofRealHom K _) n

@[simp, is_R_or_C_simps, norm_cast]
theorem rat_cast_re (q : ℚ) : re (q : K) = q := by
  rw [← of_real_rat_cast, of_real_re]

@[simp, is_R_or_C_simps, norm_cast]
theorem rat_cast_im (q : ℚ) : im (q : K) = 0 := by
  rw [← of_real_rat_cast, of_real_im]

/-! ### Characteristic zero -/


/-- ℝ and ℂ are both of characteristic zero.  -/
-- see Note [lower instance priority]
instance (priority := 100) char_zero_R_or_C : CharZero K :=
  char_zero_of_inj_zero fun n h => by
    rwa [← of_real_nat_cast, of_real_eq_zero, Nat.cast_eq_zero] at h

theorem re_eq_add_conj (z : K) : ↑(re z) = (z + conj z) / 2 := by
  rw [add_conj, mul_div_cancel_left (re z : K) two_ne_zero']

theorem im_eq_conj_sub (z : K) : ↑(im z) = I * (conj z - z) / 2 := by
  rw [← neg_inj, ← of_real_neg, ← I_mul_re, re_eq_add_conj]
  simp only [← mul_addₓ, ← sub_eq_add_neg, ← neg_div', ← neg_mul, ← conj_I, ← mul_neg, ← neg_add_rev, ← neg_negₓ, ←
    RingHom.map_mul]

/-! ### Absolute value -/


/-- The complex absolute value function, defined as the square root of the norm squared. -/
@[pp_nodot]
noncomputable def abs (z : K) : ℝ :=
  (normSq z).sqrt

-- mathport name: «exprabs'»
local notation "abs'" => HasAbs.abs

-- mathport name: «exprabsK»
local notation "absK" => @abs K _

@[simp, norm_cast]
theorem abs_of_real (r : ℝ) : absK r = abs' r := by
  simp only [← abs, ← norm_sq, ← Real.sqrt_mul_self_eq_abs, ← add_zeroₓ, ← of_real_im, ← MonoidWithZeroHom.coe_mk, ←
    of_real_re, ← mul_zero]

theorem norm_eq_abs (z : K) : ∥z∥ = absK z := by
  simp only [← abs, ← norm_sq_eq_def', ← norm_nonneg, ← Real.sqrt_sq]

@[is_R_or_C_simps, norm_cast]
theorem norm_of_real (z : ℝ) : ∥(z : K)∥ = ∥z∥ := by
  rw [IsROrC.norm_eq_abs, IsROrC.abs_of_real, Real.norm_eq_abs]

theorem abs_of_nonneg {r : ℝ} (h : 0 ≤ r) : absK r = r :=
  (abs_of_real _).trans (abs_of_nonneg h)

theorem norm_of_nonneg {r : ℝ} (r_nn : 0 ≤ r) : ∥(r : K)∥ = r := by
  rw [norm_of_real]
  exact abs_eq_self.mpr r_nn

theorem abs_of_nat (n : ℕ) : absK n = n := by
  rw [← of_real_nat_cast]
  exact abs_of_nonneg (Nat.cast_nonneg n)

theorem mul_self_abs (z : K) : abs z * abs z = normSq z :=
  Real.mul_self_sqrt (norm_sq_nonneg _)

@[simp, is_R_or_C_simps]
theorem abs_zero : absK 0 = 0 := by
  simp only [← abs, ← Real.sqrt_zero, ← map_zero]

@[simp, is_R_or_C_simps]
theorem abs_one : absK 1 = 1 := by
  simp only [← abs, ← map_one, ← Real.sqrt_one]

@[simp, is_R_or_C_simps]
theorem abs_two : absK 2 = 2 :=
  calc
    absK 2 = absK (2 : ℝ) := by
      rw [of_real_bit0, of_real_one]
    _ = (2 : ℝ) :=
      abs_of_nonneg
        (by
          norm_num)
    

theorem abs_nonneg (z : K) : 0 ≤ absK z :=
  Real.sqrt_nonneg _

@[simp, is_R_or_C_simps]
theorem abs_eq_zero {z : K} : absK z = 0 ↔ z = 0 :=
  (Real.sqrt_eq_zero <| norm_sq_nonneg _).trans norm_sq_eq_zero

theorem abs_ne_zero {z : K} : abs z ≠ 0 ↔ z ≠ 0 :=
  not_congr abs_eq_zero

@[simp, is_R_or_C_simps]
theorem abs_conj (z : K) : abs (conj z) = abs z := by
  simp only [← abs, ← norm_sq_conj]

@[simp, is_R_or_C_simps]
theorem abs_mul (z w : K) : abs (z * w) = abs z * abs w := by
  rw [abs, norm_sq_mul, Real.sqrt_mul (norm_sq_nonneg _)] <;> rfl

theorem abs_re_le_abs (z : K) : abs' (re z) ≤ abs z := by
  rw [mul_self_le_mul_self_iff (_root_.abs_nonneg (re z)) (abs_nonneg _), abs_mul_abs_self, mul_self_abs] <;>
    apply re_sq_le_norm_sq

theorem abs_im_le_abs (z : K) : abs' (im z) ≤ abs z := by
  rw [mul_self_le_mul_self_iff (_root_.abs_nonneg (im z)) (abs_nonneg _), abs_mul_abs_self, mul_self_abs] <;>
    apply im_sq_le_norm_sq

theorem norm_re_le_norm (z : K) : ∥re z∥ ≤ ∥z∥ := by
  rw [IsROrC.norm_eq_abs, Real.norm_eq_abs]
  exact IsROrC.abs_re_le_abs _

theorem norm_im_le_norm (z : K) : ∥im z∥ ≤ ∥z∥ := by
  rw [IsROrC.norm_eq_abs, Real.norm_eq_abs]
  exact IsROrC.abs_im_le_abs _

theorem re_le_abs (z : K) : re z ≤ abs z :=
  (abs_le.1 (abs_re_le_abs _)).2

theorem im_le_abs (z : K) : im z ≤ abs z :=
  (abs_le.1 (abs_im_le_abs _)).2

theorem im_eq_zero_of_le {a : K} (h : abs a ≤ re a) : im a = 0 := by
  rw [← zero_eq_mul_self]
  have : re a * re a = re a * re a + im a * im a := by
    convert IsROrC.mul_self_abs a <;> linarith [re_le_abs a]
  linarith

theorem re_eq_self_of_le {a : K} (h : abs a ≤ re a) : (re a : K) = a := by
  rw [← re_add_im a]
  simp' only [← im_eq_zero_of_le h, ← add_zeroₓ, ← zero_mul] with is_R_or_C_simps

theorem abs_add (z w : K) : abs (z + w) ≤ abs z + abs w :=
  (mul_self_le_mul_self_iff (abs_nonneg _) (add_nonneg (abs_nonneg _) (abs_nonneg _))).2 <| by
    rw [mul_self_abs, add_mul_self_eq, mul_self_abs, mul_self_abs, add_right_commₓ, norm_sq_add, add_le_add_iff_left,
      mul_assoc, mul_le_mul_left (@zero_lt_two ℝ _ _)]
    simpa [-mul_re] with is_R_or_C_simps using re_le_abs (z * conj w)

instance : IsAbsoluteValue absK where
  abv_nonneg := abs_nonneg
  abv_eq_zero := fun _ => abs_eq_zero
  abv_add := abs_add
  abv_mul := abs_mul

open IsAbsoluteValue

@[simp, is_R_or_C_simps]
theorem abs_abs (z : K) : abs' (abs z) = abs z :=
  abs_of_nonneg (abs_nonneg _)

@[simp, is_R_or_C_simps]
theorem abs_pos {z : K} : 0 < abs z ↔ z ≠ 0 :=
  abv_pos abs

@[simp, is_R_or_C_simps]
theorem abs_neg : ∀ z : K, abs (-z) = abs z :=
  abv_neg abs

theorem abs_sub : ∀ z w : K, abs (z - w) = abs (w - z) :=
  abv_sub abs

theorem abs_sub_le : ∀ a b c : K, abs (a - c) ≤ abs (a - b) + abs (b - c) :=
  abv_sub_le abs

@[simp, is_R_or_C_simps]
theorem abs_inv : ∀ z : K, abs z⁻¹ = (abs z)⁻¹ :=
  abv_inv abs

@[simp, is_R_or_C_simps]
theorem abs_div : ∀ z w : K, abs (z / w) = abs z / abs w :=
  abv_div abs

theorem abs_abs_sub_le_abs_sub : ∀ z w : K, abs' (abs z - abs w) ≤ abs (z - w) :=
  abs_abv_sub_le_abv_sub abs

theorem abs_re_div_abs_le_one (z : K) : abs' (re z / abs z) ≤ 1 := by
  by_cases' hz : z = 0
  · simp [← hz, ← zero_le_one]
    
  · simp_rw [_root_.abs_div, abs_abs, div_le_iff (abs_pos.2 hz), one_mulₓ, abs_re_le_abs]
    

theorem abs_im_div_abs_le_one (z : K) : abs' (im z / abs z) ≤ 1 := by
  by_cases' hz : z = 0
  · simp [← hz, ← zero_le_one]
    
  · simp_rw [_root_.abs_div, abs_abs, div_le_iff (abs_pos.2 hz), one_mulₓ, abs_im_le_abs]
    

@[simp, is_R_or_C_simps, norm_cast]
theorem abs_cast_nat (n : ℕ) : abs (n : K) = n := by
  rw [← of_real_nat_cast, abs_of_nonneg (Nat.cast_nonneg n)]

theorem norm_sq_eq_abs (x : K) : normSq x = abs x ^ 2 := by
  rw [abs, sq, Real.mul_self_sqrt (norm_sq_nonneg _)]

theorem re_eq_abs_of_mul_conj (x : K) : re (x * conj x) = abs (x * conj x) := by
  rw [mul_conj, of_real_re, abs_of_real, norm_sq_eq_abs, sq, _root_.abs_mul, abs_abs]

theorem abs_sq_re_add_conj (x : K) : abs (x + conj x) ^ 2 = re (x + conj x) ^ 2 := by
  simp' only [← sq, norm_sq_eq_abs, ← norm_sq, ← map_add, ← add_zeroₓ, ← MonoidWithZeroHom.coe_mk, ← add_right_negₓ, ←
    mul_zero] with is_R_or_C_simps

theorem abs_sq_re_add_conj' (x : K) : abs (conj x + x) ^ 2 = re (conj x + x) ^ 2 := by
  simp' only [← sq, norm_sq_eq_abs, ← norm_sq, ← map_add, ← add_zeroₓ, ← MonoidWithZeroHom.coe_mk, ← add_left_negₓ, ←
    mul_zero] with is_R_or_C_simps

theorem conj_mul_eq_norm_sq_left (x : K) : conj x * x = (normSq x : K) := by
  rw [ext_iff]
  refine'
    ⟨by
      simp' only [← norm_sq, ← neg_mul, ← MonoidWithZeroHom.coe_mk, ← sub_neg_eq_add, ← map_add, ← sub_zero, ←
        mul_zero] with is_R_or_C_simps,
      _⟩
  simp' only [← mul_comm, ← mul_neg, ← add_left_negₓ] with is_R_or_C_simps

/-! ### Cauchy sequences -/


theorem is_cau_seq_re (f : CauSeq K abs) : IsCauSeq abs' fun n => re (f n) := fun ε ε0 =>
  (f.cauchy ε0).imp fun i H j ij =>
    lt_of_le_of_ltₓ
      (by
        simpa using abs_re_le_abs (f j - f i))
      (H _ ij)

theorem is_cau_seq_im (f : CauSeq K abs) : IsCauSeq abs' fun n => im (f n) := fun ε ε0 =>
  (f.cauchy ε0).imp fun i H j ij =>
    lt_of_le_of_ltₓ
      (by
        simpa using abs_im_le_abs (f j - f i))
      (H _ ij)

/-- The real part of a K Cauchy sequence, as a real Cauchy sequence. -/
noncomputable def cauSeqRe (f : CauSeq K abs) : CauSeq ℝ abs' :=
  ⟨_, is_cau_seq_re f⟩

/-- The imaginary part of a K Cauchy sequence, as a real Cauchy sequence. -/
noncomputable def cauSeqIm (f : CauSeq K abs) : CauSeq ℝ abs' :=
  ⟨_, is_cau_seq_im f⟩

theorem is_cau_seq_abs {f : ℕ → K} (hf : IsCauSeq abs f) : IsCauSeq abs' (abs ∘ f) := fun ε ε0 =>
  let ⟨i, hi⟩ := hf ε ε0
  ⟨i, fun j hj => lt_of_le_of_ltₓ (abs_abs_sub_le_abs_sub _ _) (hi j hj)⟩

@[simp, is_R_or_C_simps, norm_cast]
theorem of_real_prod {α : Type _} (s : Finset α) (f : α → ℝ) : ((∏ i in s, f i : ℝ) : K) = ∏ i in s, (f i : K) :=
  RingHom.map_prod _ _ _

@[simp, is_R_or_C_simps, norm_cast]
theorem of_real_sum {α : Type _} (s : Finset α) (f : α → ℝ) : ((∑ i in s, f i : ℝ) : K) = ∑ i in s, (f i : K) :=
  RingHom.map_sum _ _ _

@[simp, is_R_or_C_simps, norm_cast]
theorem of_real_finsupp_sum {α M : Type _} [Zero M] (f : α →₀ M) (g : α → M → ℝ) :
    ((f.Sum fun a b => g a b : ℝ) : K) = f.Sum fun a b => (g a b : K) :=
  RingHom.map_finsupp_sum _ f g

@[simp, is_R_or_C_simps, norm_cast]
theorem of_real_finsupp_prod {α M : Type _} [Zero M] (f : α →₀ M) (g : α → M → ℝ) :
    ((f.Prod fun a b => g a b : ℝ) : K) = f.Prod fun a b => (g a b : K) :=
  RingHom.map_finsupp_prod _ f g

end IsROrC

namespace Polynomial

open Polynomial

theorem of_real_eval (p : ℝ[X]) (x : ℝ) : (p.eval x : K) = aeval (↑x) p :=
  (@aeval_algebra_map_apply ℝ K _ _ _ x p).symm

end Polynomial

namespace FiniteDimensional

open Classical

open IsROrC

library_note "is_R_or_C instance"/--
This instance generates a type-class problem with a metavariable `?m` that should satisfy
`is_R_or_C ?m`. Since this can only be satisfied by `ℝ` or `ℂ`, this does not cause problems. -/


/-- An `is_R_or_C` field is finite-dimensional over `ℝ`, since it is spanned by `{1, I}`. -/
@[nolint dangerous_instance]
instance is_R_or_C_to_real : FiniteDimensional ℝ K :=
  ⟨⟨{1, i}, by
      rw [eq_top_iff]
      intro a _
      rw [Finset.coe_insert, Finset.coe_singleton, Submodule.mem_span_insert]
      refine' ⟨re a, im a • I, _, _⟩
      · rw [Submodule.mem_span_singleton]
        use im a
        
      simp [← re_add_im a, ← Algebra.smul_def, ← algebra_map_eq_of_real]⟩⟩

variable (K) (E : Type _) [NormedGroup E] [NormedSpace K E]

/-- A finite dimensional vector space Over an `is_R_or_C` is a proper metric space.

This is not an instance because it would cause a search for `finite_dimensional ?x E` before
`is_R_or_C ?x`. -/
theorem proper_is_R_or_C [FiniteDimensional K E] : ProperSpace E := by
  let this : NormedSpace ℝ E := RestrictScalars.normedSpace ℝ K E
  let this : FiniteDimensional ℝ E := FiniteDimensional.trans ℝ K E
  infer_instance

variable {E}

instance IsROrC.proper_space_submodule (S : Submodule K E) [FiniteDimensional K ↥S] : ProperSpace S :=
  proper_is_R_or_C K S

end FiniteDimensional

section Instances

noncomputable instance Real.isROrC : IsROrC ℝ :=
  { Real.nondiscreteNormedField, Real.metricSpace with re := AddMonoidHom.id ℝ, im := 0, i := 0,
    I_re_ax := by
      simp only [← AddMonoidHom.map_zero],
    I_mul_I_ax := Or.intro_left _ rfl,
    re_add_im_ax := fun z => by
      simp only [← add_zeroₓ, ← mul_zero, ← Algebra.id.map_eq_id, ← RingHom.id_apply, ← AddMonoidHom.id_apply],
    of_real_re_ax := fun r => by
      simp only [← AddMonoidHom.id_apply, ← Algebra.id.map_eq_self],
    of_real_im_ax := fun r => by
      simp only [← AddMonoidHom.zero_apply],
    mul_re_ax := fun z w => by
      simp only [← sub_zero, ← mul_zero, ← AddMonoidHom.zero_apply, ← AddMonoidHom.id_apply],
    mul_im_ax := fun z w => by
      simp only [← add_zeroₓ, ← zero_mul, ← mul_zero, ← AddMonoidHom.zero_apply],
    conj_re_ax := fun z => by
      simp only [← star_ring_end_apply, ← star_id_of_comm],
    conj_im_ax := fun z => by
      simp only [← neg_zero, ← AddMonoidHom.zero_apply],
    conj_I_ax := by
      simp only [← RingHom.map_zero, ← neg_zero],
    norm_sq_eq_def_ax := fun z => by
      simp only [← sq, ← Real.norm_eq_abs, abs_mul, ← abs_mul_self z, ← add_zeroₓ, ← mul_zero, ←
        AddMonoidHom.zero_apply, ← AddMonoidHom.id_apply],
    mul_im_I_ax := fun z => by
      simp only [← mul_zero, ← AddMonoidHom.zero_apply],
    inv_def_ax := fun z => by
      simp only [← star_ring_end_apply, ← star, ← sq, ← Real.norm_eq_abs, ← abs_mul_abs_self, div_eq_mul_inv, ←
        Algebra.id.map_eq_id, ← id.def, ← RingHom.id_apply, ← div_self_mul_self'],
    div_I_ax := fun z => by
      simp only [← div_zero, ← mul_zero, ← neg_zero] }

end Instances

namespace IsROrC

open ComplexConjugate

section CleanupLemmas

-- mathport name: «exprreR»
local notation "reR" => @IsROrC.re ℝ _

-- mathport name: «exprimR»
local notation "imR" => @IsROrC.im ℝ _

-- mathport name: «exprIR»
local notation "IR" => @IsROrC.i ℝ _

-- mathport name: «exprabsR»
local notation "absR" => @IsROrC.abs ℝ _

-- mathport name: «exprnorm_sqR»
local notation "norm_sqR" => @IsROrC.normSq ℝ _

@[simp, is_R_or_C_simps]
theorem re_to_real {x : ℝ} : reR x = x :=
  rfl

@[simp, is_R_or_C_simps]
theorem im_to_real {x : ℝ} : imR x = 0 :=
  rfl

@[simp, is_R_or_C_simps]
theorem conj_to_real {x : ℝ} : conj x = x :=
  rfl

@[simp, is_R_or_C_simps]
theorem I_to_real : IR = 0 :=
  rfl

@[simp, is_R_or_C_simps]
theorem norm_sq_to_real {x : ℝ} : normSq x = x * x := by
  simp [← IsROrC.normSq]

@[simp, is_R_or_C_simps]
theorem abs_to_real {x : ℝ} : absR x = HasAbs.abs x := by
  simp [← IsROrC.abs, ← abs, ← Real.sqrt_mul_self_eq_abs]

@[simp]
theorem coe_real_eq_id : @coe ℝ ℝ _ = id :=
  rfl

end CleanupLemmas

section LinearMaps

/-- The real part in a `is_R_or_C` field, as a linear map. -/
def reLm : K →ₗ[ℝ] ℝ :=
  { re with map_smul' := smul_re }

@[simp, is_R_or_C_simps]
theorem re_lm_coe : (reLm : K → ℝ) = re :=
  rfl

/-- The real part in a `is_R_or_C` field, as a continuous linear map. -/
noncomputable def reClm : K →L[ℝ] ℝ :=
  LinearMap.mkContinuous reLm 1 <| by
    simp only [← norm_eq_abs, ← re_lm_coe, ← one_mulₓ, ← abs_to_real]
    exact abs_re_le_abs

@[simp, is_R_or_C_simps]
theorem re_clm_norm : ∥(reClm : K →L[ℝ] ℝ)∥ = 1 := by
  apply le_antisymmₓ (LinearMap.mk_continuous_norm_le _ zero_le_one _)
  convert ContinuousLinearMap.ratio_le_op_norm _ (1 : K)
  · simp
    
  · infer_instance
    

@[simp, is_R_or_C_simps, norm_cast]
theorem re_clm_coe : ((reClm : K →L[ℝ] ℝ) : K →ₗ[ℝ] ℝ) = re_lm :=
  rfl

@[simp, is_R_or_C_simps]
theorem re_clm_apply : ((reClm : K →L[ℝ] ℝ) : K → ℝ) = re :=
  rfl

@[continuity]
theorem continuous_re : Continuous (re : K → ℝ) :=
  reClm.Continuous

/-- The imaginary part in a `is_R_or_C` field, as a linear map. -/
def imLm : K →ₗ[ℝ] ℝ :=
  { im with map_smul' := smul_im }

@[simp, is_R_or_C_simps]
theorem im_lm_coe : (imLm : K → ℝ) = im :=
  rfl

/-- The imaginary part in a `is_R_or_C` field, as a continuous linear map. -/
noncomputable def imClm : K →L[ℝ] ℝ :=
  LinearMap.mkContinuous imLm 1 <| by
    simp only [← norm_eq_abs, ← re_lm_coe, ← one_mulₓ, ← abs_to_real]
    exact abs_im_le_abs

@[simp, is_R_or_C_simps, norm_cast]
theorem im_clm_coe : ((imClm : K →L[ℝ] ℝ) : K →ₗ[ℝ] ℝ) = im_lm :=
  rfl

@[simp, is_R_or_C_simps]
theorem im_clm_apply : ((imClm : K →L[ℝ] ℝ) : K → ℝ) = im :=
  rfl

@[continuity]
theorem continuous_im : Continuous (im : K → ℝ) :=
  imClm.Continuous

/-- Conjugate as an `ℝ`-algebra equivalence -/
def conjAe : K ≃ₐ[ℝ] K :=
  { conj with invFun := conj, left_inv := conj_conj, right_inv := conj_conj, commutes' := conj_of_real }

@[simp, is_R_or_C_simps]
theorem conj_ae_coe : (conjAe : K → K) = conj :=
  rfl

/-- Conjugate as a linear isometry -/
noncomputable def conjLie : K ≃ₗᵢ[ℝ] K :=
  ⟨conjAe.toLinearEquiv, fun z => by
    simp' [← norm_eq_abs] with is_R_or_C_simps⟩

@[simp, is_R_or_C_simps]
theorem conj_lie_apply : (conjLie : K → K) = conj :=
  rfl

/-- Conjugate as a continuous linear equivalence -/
noncomputable def conjCle : K ≃L[ℝ] K :=
  @conjLie K _

@[simp, is_R_or_C_simps]
theorem conj_cle_coe : (@conjCle K _).toLinearEquiv = conjAe.toLinearEquiv :=
  rfl

@[simp, is_R_or_C_simps]
theorem conj_cle_apply : (conjCle : K → K) = conj :=
  rfl

@[simp, is_R_or_C_simps]
theorem conj_cle_norm : ∥(@conjCle K _ : K →L[ℝ] K)∥ = 1 :=
  (@conjLie K _).toLinearIsometry.norm_to_continuous_linear_map

instance (priority := 100) : HasContinuousStar K :=
  ⟨conjLie.Continuous⟩

@[continuity]
theorem continuous_conj : Continuous (conj : K → K) :=
  continuous_star

/-- The `ℝ → K` coercion, as a linear map -/
noncomputable def ofRealAm : ℝ →ₐ[ℝ] K :=
  Algebra.ofId ℝ K

@[simp, is_R_or_C_simps]
theorem of_real_am_coe : (ofRealAm : ℝ → K) = coe :=
  rfl

/-- The ℝ → K coercion, as a linear isometry -/
noncomputable def ofRealLi : ℝ →ₗᵢ[ℝ] K where
  toLinearMap := ofRealAm.toLinearMap
  norm_map' := by
    simp [← norm_eq_abs]

@[simp, is_R_or_C_simps]
theorem of_real_li_apply : (ofRealLi : ℝ → K) = coe :=
  rfl

/-- The `ℝ → K` coercion, as a continuous linear map -/
noncomputable def ofRealClm : ℝ →L[ℝ] K :=
  ofRealLi.toContinuousLinearMap

@[simp, is_R_or_C_simps]
theorem of_real_clm_coe : (@ofRealClm K _ : ℝ →ₗ[ℝ] K) = ofRealAm.toLinearMap :=
  rfl

@[simp, is_R_or_C_simps]
theorem of_real_clm_apply : (ofRealClm : ℝ → K) = coe :=
  rfl

@[simp, is_R_or_C_simps]
theorem of_real_clm_norm : ∥(ofRealClm : ℝ →L[ℝ] K)∥ = 1 :=
  LinearIsometry.norm_to_continuous_linear_map ofRealLi

@[continuity]
theorem continuous_of_real : Continuous (coe : ℝ → K) :=
  ofRealLi.Continuous

@[continuity]
theorem continuous_abs : Continuous (@IsROrC.abs K _) := by
  simp only [←
    show @IsROrC.abs K _ = HasNorm.norm by
      ext
      exact (norm_eq_abs _).symm,
    ← continuous_norm]

@[continuity]
theorem continuous_norm_sq : Continuous (@IsROrC.normSq K _) := by
  have : (@IsROrC.normSq K _ : K → ℝ) = fun x => IsROrC.abs x ^ 2 := by
    ext
    exact norm_sq_eq_abs _
  simp only [← this, ← continuous_abs.pow 2]

end LinearMaps

end IsROrC

