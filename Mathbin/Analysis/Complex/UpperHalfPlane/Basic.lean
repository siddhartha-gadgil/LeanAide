/-
Copyright (c) 2021 Alex Kontorovich and Heather Macbeth and Marc Masdeu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Kontorovich, Heather Macbeth, Marc Masdeu
-/
import Mathbin.LinearAlgebra.SpecialLinearGroup
import Mathbin.Analysis.Complex.Basic
import Mathbin.GroupTheory.GroupAction.Defs
import Mathbin.LinearAlgebra.GeneralLinearGroup

/-!
# The upper half plane and its automorphisms

This file defines `upper_half_plane` to be the upper half plane in `ℂ`.

We furthermore equip it with the structure of an `GL_pos 2 ℝ` action by
fractional linear transformations.

We define the notation `ℍ` for the upper half plane available in the locale
`upper_half_plane` so as not to conflict with the quaternions.
-/


noncomputable section

open Matrix Matrix.SpecialLinearGroup

open Classical BigOperators MatrixGroups

attribute [local instance] Fintype.card_fin_even

/- Disable this instances as it is not the simp-normal form, and having them disabled ensures
we state lemmas in this file without spurious `coe_fn` terms. -/
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToFun

-- mathport name: «expr↑ₘ »
local prefix:1024 "↑ₘ" => @coe _ (Matrix (Finₓ 2) (Finₓ 2) _) _

-- mathport name: «exprGL( , )⁺»
local notation "GL(" n ", " R ")" "⁺" => Matrix.gLPos (Finₓ n) R

-- ./././Mathport/Syntax/Translate/Basic.lean:1153:9: unsupported derive handler λ α, has_coe α exprℂ()
/-- The open upper half plane -/
def UpperHalfPlane :=
  { point : ℂ // 0 < point.im }deriving
  «./././Mathport/Syntax/Translate/Basic.lean:1153:9: unsupported derive handler λ α, has_coe α exprℂ()»

-- mathport name: «exprℍ»
localized [UpperHalfPlane] notation "ℍ" => UpperHalfPlane

namespace UpperHalfPlane

instance : Inhabited ℍ :=
  ⟨⟨Complex.i, by
      simp ⟩⟩

/-- Imaginary part -/
def im (z : ℍ) :=
  (z : ℂ).im

/-- Real part -/
def re (z : ℍ) :=
  (z : ℂ).re

/-- Constructor for `upper_half_plane`. It is useful if `⟨z, h⟩` makes Lean use a wrong
typeclass instance. -/
def mk (z : ℂ) (h : 0 < z.im) : ℍ :=
  ⟨z, h⟩

@[simp]
theorem coe_im (z : ℍ) : (z : ℂ).im = z.im :=
  rfl

@[simp]
theorem coe_re (z : ℍ) : (z : ℂ).re = z.re :=
  rfl

@[simp]
theorem mk_re (z : ℂ) (h : 0 < z.im) : (mk z h).re = z.re :=
  rfl

@[simp]
theorem mk_im (z : ℂ) (h : 0 < z.im) : (mk z h).im = z.im :=
  rfl

@[simp]
theorem coe_mk (z : ℂ) (h : 0 < z.im) : (mk z h : ℂ) = z :=
  rfl

@[simp]
theorem mk_coe (z : ℍ) (h : 0 < (z : ℂ).im := z.2) : mk z h = z :=
  Subtype.eta z h

theorem re_add_im (z : ℍ) : (z.re + z.im * Complex.i : ℂ) = z :=
  Complex.re_add_im z

theorem im_pos (z : ℍ) : 0 < z.im :=
  z.2

theorem im_ne_zero (z : ℍ) : z.im ≠ 0 :=
  z.im_pos.ne'

theorem ne_zero (z : ℍ) : (z : ℂ) ≠ 0 :=
  mt (congr_arg Complex.im) z.im_ne_zero

theorem norm_sq_pos (z : ℍ) : 0 < Complex.normSq (z : ℂ) := by
  rw [Complex.norm_sq_pos]
  exact z.ne_zero

theorem norm_sq_ne_zero (z : ℍ) : Complex.normSq (z : ℂ) ≠ 0 :=
  (norm_sq_pos z).ne'

/-- Numerator of the formula for a fractional linear transformation -/
@[simp]
def num (g : GL(2, ℝ)⁺) (z : ℍ) : ℂ :=
  (↑ₘg 0 0 : ℝ) * z + (↑ₘg 0 1 : ℝ)

/-- Denominator of the formula for a fractional linear transformation -/
@[simp]
def denom (g : GL(2, ℝ)⁺) (z : ℍ) : ℂ :=
  (↑ₘg 1 0 : ℝ) * z + (↑ₘg 1 1 : ℝ)

-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:30:4: unsupported: too many args: fin_cases ... #[[]]
theorem linear_ne_zero (cd : Finₓ 2 → ℝ) (z : ℍ) (h : cd ≠ 0) : (cd 0 : ℂ) * z + cd 1 ≠ 0 := by
  contrapose! h
  have : cd 0 = 0 := by
    -- we will need this twice
    apply_fun Complex.im  at h
    simpa only [← z.im_ne_zero, ← Complex.add_im, ← add_zeroₓ, ← coe_im, ← zero_mul, ← or_falseₓ, ← Complex.of_real_im,
      ← Complex.zero_im, ← Complex.mul_im, ← mul_eq_zero] using h
  simp only [← this, ← zero_mul, ← Complex.of_real_zero, ← zero_addₓ, ← Complex.of_real_eq_zero] at h
  ext i
  fin_cases i <;> assumption

theorem denom_ne_zero (g : GL(2, ℝ)⁺) (z : ℍ) : denom g z ≠ 0 := by
  intro H
  have DET := (mem_GL_pos _).1 g.prop
  have hz := z.prop
  simp only [← general_linear_group.coe_det_apply] at DET
  have H1 : (↑ₘg 1 0 : ℝ) = 0 ∨ z.im = 0 := by
    simpa using congr_arg Complex.im H
  cases H1
  · simp only [← H1, ← Complex.of_real_zero, ← denom, ← coe_fn_eq_coe, ← zero_mul, ← zero_addₓ, ←
      Complex.of_real_eq_zero] at H
    rw [← coe_coe, Matrix.det_fin_two (↑g : Matrix (Finₓ 2) (Finₓ 2) ℝ)] at DET
    simp only [← coe_coe, ← H, ← H1, ← mul_zero, ← sub_zero, ← lt_self_iff_false] at DET
    exact DET
    
  · change z.im > 0 at hz
    linarith
    

theorem norm_sq_denom_pos (g : GL(2, ℝ)⁺) (z : ℍ) : 0 < Complex.normSq (denom g z) :=
  Complex.norm_sq_pos.mpr (denom_ne_zero g z)

theorem norm_sq_denom_ne_zero (g : GL(2, ℝ)⁺) (z : ℍ) : Complex.normSq (denom g z) ≠ 0 :=
  ne_of_gtₓ (norm_sq_denom_pos g z)

/-- Fractional linear transformation, also known as the Moebius transformation -/
def smulAux' (g : GL(2, ℝ)⁺) (z : ℍ) : ℂ :=
  num g z / denom g z

theorem smul_aux'_im (g : GL(2, ℝ)⁺) (z : ℍ) : (smulAux' g z).im = det ↑ₘg * z.im / (denom g z).normSq := by
  rw [smul_aux', Complex.div_im]
  set NsqBot := (denom g z).normSq
  have : NsqBot ≠ 0 := by
    simp only [← denom_ne_zero g z, ← MonoidWithZeroHom.map_eq_zero, ← Ne.def, ← not_false_iff]
  field_simp [← smul_aux', -coe_coe]
  rw [Matrix.det_fin_two ↑ₘg]
  ring

/-- Fractional linear transformation, also known as the Moebius transformation -/
def smulAux (g : GL(2, ℝ)⁺) (z : ℍ) : ℍ :=
  ⟨smulAux' g z, by
    rw [smul_aux'_im]
    convert mul_pos ((mem_GL_pos _).1 g.prop) (div_pos z.im_pos (complex.norm_sq_pos.mpr (denom_ne_zero g z)))
    simp only [← general_linear_group.coe_det_apply, ← coe_coe]
    ring⟩

theorem denom_cocycle (x y : GL(2, ℝ)⁺) (z : ℍ) : denom (x * y) z = denom x (smulAux y z) * denom y z := by
  change _ = (_ * (_ / _) + _) * _
  field_simp [← denom_ne_zero, -denom, -Num]
  simp only [← Matrix.mul, ← dot_product, ← Finₓ.sum_univ_succ, ← denom, ← Num, ← coe_coe, ← Subgroup.coe_mul, ←
    general_linear_group.coe_mul, ← Fintype.univ_of_subsingleton, ← Finₓ.mk_eq_subtype_mk, ← Finₓ.mk_zero, ←
    Finset.sum_singleton, ← Finₓ.succ_zero_eq_one, ← Complex.of_real_add, ← Complex.of_real_mul]
  ring

theorem mul_smul' (x y : GL(2, ℝ)⁺) (z : ℍ) : smulAux (x * y) z = smulAux x (smulAux y z) := by
  ext1
  change _ / _ = (_ * (_ / _) + _) * _
  rw [denom_cocycle]
  field_simp [← denom_ne_zero, -denom, -Num]
  simp only [← Matrix.mul, ← dot_product, ← Finₓ.sum_univ_succ, ← Num, ← denom, ← coe_coe, ← Subgroup.coe_mul, ←
    general_linear_group.coe_mul, ← Fintype.univ_of_subsingleton, ← Finₓ.mk_eq_subtype_mk, ← Finₓ.mk_zero, ←
    Finset.sum_singleton, ← Finₓ.succ_zero_eq_one, ← Complex.of_real_add, ← Complex.of_real_mul]
  ring

/-- The action of ` GL_pos 2 ℝ` on the upper half-plane by fractional linear transformations. -/
instance : MulAction GL(2, ℝ)⁺ ℍ where
  smul := smulAux
  one_smul := fun z => by
    ext1
    change _ / _ = _
    simp [← coe_fn_coe_base']
  mul_smul := mul_smul'

section ModularScalarTowers

variable (Γ : Subgroup (SpecialLinearGroup (Finₓ 2) ℤ))

instance sLAction {R : Type _} [CommRingₓ R] [Algebra R ℝ] : MulAction SL(2,R) ℍ :=
  MulAction.compHom ℍ <| SpecialLinearGroup.toGLPos.comp <| map (algebraMap R ℝ)

instance : Coe SL(2,ℤ) GL(2, ℝ)⁺ :=
  ⟨fun g => ((g : SL(2,ℝ)) : GL(2, ℝ)⁺)⟩

instance sLOnGLPos : HasSmul SL(2,ℤ) GL(2, ℝ)⁺ :=
  ⟨fun s g => s * g⟩

theorem SL_on_GL_pos_smul_apply (s : SL(2,ℤ)) (g : GL(2, ℝ)⁺) (z : ℍ) : (s • g) • z = ((s : GL(2, ℝ)⁺) * g) • z :=
  rfl

instance SL_to_GL_tower :
    IsScalarTower SL(2,ℤ) GL(2, ℝ)⁺ ℍ where smul_assoc := by
    intro s g z
    simp only [← SL_on_GL_pos_smul_apply, ← coe_coe]
    apply mul_smul'

instance subgroupGLPos : HasSmul Γ GL(2, ℝ)⁺ :=
  ⟨fun s g => s * g⟩

theorem subgroup_on_GL_pos_smul_apply (s : Γ) (g : GL(2, ℝ)⁺) (z : ℍ) : (s • g) • z = ((s : GL(2, ℝ)⁺) * g) • z :=
  rfl

instance subgroup_on_GL_pos :
    IsScalarTower Γ GL(2, ℝ)⁺ ℍ where smul_assoc := by
    intro s g z
    simp only [← subgroup_on_GL_pos_smul_apply, ← coe_coe]
    apply mul_smul'

instance subgroupSL : HasSmul Γ SL(2,ℤ) :=
  ⟨fun s g => s * g⟩

theorem subgroup_on_SL_apply (s : Γ) (g : SL(2,ℤ)) (z : ℍ) : (s • g) • z = ((s : SL(2,ℤ)) * g) • z :=
  rfl

instance subgroup_to_SL_tower :
    IsScalarTower Γ SL(2,ℤ) ℍ where smul_assoc := fun s g z => by
    rw [subgroup_on_SL_apply]
    apply MulAction.mul_smul

end ModularScalarTowers

@[simp]
theorem coe_smul (g : GL(2, ℝ)⁺) (z : ℍ) : ↑(g • z) = num g z / denom g z :=
  rfl

@[simp]
theorem re_smul (g : GL(2, ℝ)⁺) (z : ℍ) : (g • z).re = (num g z / denom g z).re :=
  rfl

theorem im_smul (g : GL(2, ℝ)⁺) (z : ℍ) : (g • z).im = (num g z / denom g z).im :=
  rfl

theorem im_smul_eq_div_norm_sq (g : GL(2, ℝ)⁺) (z : ℍ) : (g • z).im = det ↑ₘg * z.im / Complex.normSq (denom g z) :=
  smul_aux'_im g z

@[simp]
theorem neg_smul (g : GL(2, ℝ)⁺) (z : ℍ) : -g • z = g • z := by
  ext1
  change _ / _ = _ / _
  field_simp [← denom_ne_zero, -denom, -Num]
  simp only [← Num, ← denom, ← coe_coe, ← Complex.of_real_neg, ← neg_mul, ← GL_pos.coe_neg_GL, ← Units.coe_neg, ←
    Pi.neg_apply]
  ring_nf

section SLModularAction

variable (g : SL(2,ℤ)) (z : ℍ) (Γ : Subgroup SL(2,ℤ))

@[simp]
theorem sl_moeb (A : SL(2,ℤ)) (z : ℍ) : A • z = (A : GL(2, ℝ)⁺) • z :=
  rfl

theorem subgroup_moeb (A : Γ) (z : ℍ) : A • z = (A : GL(2, ℝ)⁺) • z :=
  rfl

@[simp]
theorem subgroup_to_sl_moeb (A : Γ) (z : ℍ) : A • z = (A : SL(2,ℤ)) • z :=
  rfl

@[simp]
theorem SL_neg_smul (g : SL(2,ℤ)) (z : ℍ) : -g • z = g • z := by
  simp only [← coe_GL_pos_neg, ← sl_moeb, ← coe_coe, ← coe_int_neg, ← neg_smul]

theorem c_mul_im_sq_le_norm_sq_denom (z : ℍ) (g : SL(2,ℝ)) : ((↑ₘg 1 0 : ℝ) * z.im) ^ 2 ≤ Complex.normSq (denom g z) :=
  by
  let c := (↑ₘg 1 0 : ℝ)
  let d := (↑ₘg 1 1 : ℝ)
  calc (c * z.im) ^ 2 ≤ (c * z.im) ^ 2 + (c * z.re + d) ^ 2 := by
      nlinarith _ = Complex.normSq (denom g z) := by
      simp [← Complex.normSq] <;> ring

theorem SpecialLinearGroup.im_smul_eq_div_norm_sq : (g • z).im = z.im / Complex.normSq (denom g z) := by
  convert im_smul_eq_div_norm_sq g z
  simp only [← coe_coe, ← general_linear_group.coe_det_apply, ← coe_GL_pos_coe_GL_coe_matrix, ← Int.coe_cast_ring_hom, ←
    (g : SL(2,ℝ)).Prop, ← one_mulₓ]

theorem denom_apply (g : SL(2,ℤ)) (z : ℍ) :
    denom g z = (↑g : Matrix (Finₓ 2) (Finₓ 2) ℤ) 1 0 * z + (↑g : Matrix (Finₓ 2) (Finₓ 2) ℤ) 1 1 := by
  simp

end SLModularAction

end UpperHalfPlane

