/-
Copyright (c) 2017 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Mario Carneiro
-/
import Mathbin.Data.Real.Sqrt

/-!
# The complex numbers

The complex numbers are modelled as ℝ^2 in the obvious way and it is shown that they form a field
of characteristic zero. The result that the complex numbers are algebraically closed, see
`field_theory.algebraic_closure`.
-/


open BigOperators

open Set Function

/-! ### Definition and basic arithmmetic -/


/-- Complex numbers consist of two `real`s: a real part `re` and an imaginary part `im`. -/
structure Complex : Type where
  re : ℝ
  im : ℝ

-- mathport name: «exprℂ»
notation "ℂ" => Complex

namespace Complex

open ComplexConjugate

noncomputable instance : DecidableEq ℂ :=
  Classical.decEq _

/-- The equivalence between the complex numbers and `ℝ × ℝ`. -/
@[simps apply]
def equivRealProd : ℂ ≃ ℝ × ℝ where
  toFun := fun z => ⟨z.re, z.im⟩
  invFun := fun p => ⟨p.1, p.2⟩
  left_inv := fun ⟨x, y⟩ => rfl
  right_inv := fun ⟨x, y⟩ => rfl

@[simp]
theorem eta : ∀ z : ℂ, Complex.mk z.re z.im = z
  | ⟨a, b⟩ => rfl

@[ext]
theorem ext : ∀ {z w : ℂ}, z.re = w.re → z.im = w.im → z = w
  | ⟨zr, zi⟩, ⟨_, _⟩, rfl, rfl => rfl

theorem ext_iff {z w : ℂ} : z = w ↔ z.re = w.re ∧ z.im = w.im :=
  ⟨fun H => by
    simp [← H], And.ndrec ext⟩

theorem re_surjective : Surjective re := fun x => ⟨⟨x, 0⟩, rfl⟩

theorem im_surjective : Surjective im := fun y => ⟨⟨0, y⟩, rfl⟩

@[simp]
theorem range_re : Range re = univ :=
  re_surjective.range_eq

@[simp]
theorem range_im : Range im = univ :=
  im_surjective.range_eq

instance : Coe ℝ ℂ :=
  ⟨fun r => ⟨r, 0⟩⟩

@[simp, norm_cast]
theorem of_real_re (r : ℝ) : (r : ℂ).re = r :=
  rfl

@[simp, norm_cast]
theorem of_real_im (r : ℝ) : (r : ℂ).im = 0 :=
  rfl

theorem of_real_def (r : ℝ) : (r : ℂ) = ⟨r, 0⟩ :=
  rfl

@[simp, norm_cast]
theorem of_real_inj {z w : ℝ} : (z : ℂ) = w ↔ z = w :=
  ⟨congr_arg re, congr_arg _⟩

theorem of_real_injective : Function.Injective (coe : ℝ → ℂ) := fun z w => congr_arg re

instance : CanLift ℂ ℝ where
  cond := fun z => z.im = 0
  coe := coe
  prf := fun z hz => ⟨z.re, ext rfl hz.symm⟩

/-- The product of a set on the real axis and a set on the imaginary axis of the complex plane,
denoted by `s ×ℂ t`. -/
def _root_.set.re_prod_im (s t : Set ℝ) : Set ℂ :=
  re ⁻¹' s ∩ im ⁻¹' t

-- mathport name: «expr ×ℂ »
infixl:72 " ×ℂ " => Set.ReProdIm

theorem mem_re_prod_im {z : ℂ} {s t : Set ℝ} : z ∈ s ×ℂ t ↔ z.re ∈ s ∧ z.im ∈ t :=
  Iff.rfl

instance : Zero ℂ :=
  ⟨(0 : ℝ)⟩

instance : Inhabited ℂ :=
  ⟨0⟩

@[simp]
theorem zero_re : (0 : ℂ).re = 0 :=
  rfl

@[simp]
theorem zero_im : (0 : ℂ).im = 0 :=
  rfl

@[simp, norm_cast]
theorem of_real_zero : ((0 : ℝ) : ℂ) = 0 :=
  rfl

@[simp]
theorem of_real_eq_zero {z : ℝ} : (z : ℂ) = 0 ↔ z = 0 :=
  of_real_inj

theorem of_real_ne_zero {z : ℝ} : (z : ℂ) ≠ 0 ↔ z ≠ 0 :=
  not_congr of_real_eq_zero

instance : One ℂ :=
  ⟨(1 : ℝ)⟩

@[simp]
theorem one_re : (1 : ℂ).re = 1 :=
  rfl

@[simp]
theorem one_im : (1 : ℂ).im = 0 :=
  rfl

@[simp, norm_cast]
theorem of_real_one : ((1 : ℝ) : ℂ) = 1 :=
  rfl

@[simp]
theorem of_real_eq_one {z : ℝ} : (z : ℂ) = 1 ↔ z = 1 :=
  of_real_inj

theorem of_real_ne_one {z : ℝ} : (z : ℂ) ≠ 1 ↔ z ≠ 1 :=
  not_congr of_real_eq_one

instance : Add ℂ :=
  ⟨fun z w => ⟨z.re + w.re, z.im + w.im⟩⟩

@[simp]
theorem add_re (z w : ℂ) : (z + w).re = z.re + w.re :=
  rfl

@[simp]
theorem add_im (z w : ℂ) : (z + w).im = z.im + w.im :=
  rfl

@[simp]
theorem bit0_re (z : ℂ) : (bit0 z).re = bit0 z.re :=
  rfl

@[simp]
theorem bit1_re (z : ℂ) : (bit1 z).re = bit1 z.re :=
  rfl

@[simp]
theorem bit0_im (z : ℂ) : (bit0 z).im = bit0 z.im :=
  Eq.refl _

@[simp]
theorem bit1_im (z : ℂ) : (bit1 z).im = bit0 z.im :=
  add_zeroₓ _

@[simp, norm_cast]
theorem of_real_add (r s : ℝ) : ((r + s : ℝ) : ℂ) = r + s :=
  ext_iff.2 <| by
    simp

@[simp, norm_cast]
theorem of_real_bit0 (r : ℝ) : ((bit0 r : ℝ) : ℂ) = bit0 r :=
  ext_iff.2 <| by
    simp [← bit0]

@[simp, norm_cast]
theorem of_real_bit1 (r : ℝ) : ((bit1 r : ℝ) : ℂ) = bit1 r :=
  ext_iff.2 <| by
    simp [← bit1]

instance : Neg ℂ :=
  ⟨fun z => ⟨-z.re, -z.im⟩⟩

@[simp]
theorem neg_re (z : ℂ) : (-z).re = -z.re :=
  rfl

@[simp]
theorem neg_im (z : ℂ) : (-z).im = -z.im :=
  rfl

@[simp, norm_cast]
theorem of_real_neg (r : ℝ) : ((-r : ℝ) : ℂ) = -r :=
  ext_iff.2 <| by
    simp

instance : Sub ℂ :=
  ⟨fun z w => ⟨z.re - w.re, z.im - w.im⟩⟩

instance : Mul ℂ :=
  ⟨fun z w => ⟨z.re * w.re - z.im * w.im, z.re * w.im + z.im * w.re⟩⟩

@[simp]
theorem mul_re (z w : ℂ) : (z * w).re = z.re * w.re - z.im * w.im :=
  rfl

@[simp]
theorem mul_im (z w : ℂ) : (z * w).im = z.re * w.im + z.im * w.re :=
  rfl

@[simp, norm_cast]
theorem of_real_mul (r s : ℝ) : ((r * s : ℝ) : ℂ) = r * s :=
  ext_iff.2 <| by
    simp

theorem of_real_mul_re (r : ℝ) (z : ℂ) : (↑r * z).re = r * z.re := by
  simp

theorem of_real_mul_im (r : ℝ) (z : ℂ) : (↑r * z).im = r * z.im := by
  simp

theorem of_real_mul' (r : ℝ) (z : ℂ) : ↑r * z = ⟨r * z.re, r * z.im⟩ :=
  ext (of_real_mul_re _ _) (of_real_mul_im _ _)

/-! ### The imaginary unit, `I` -/


/-- The imaginary unit. -/
def i : ℂ :=
  ⟨0, 1⟩

@[simp]
theorem I_re : i.re = 0 :=
  rfl

@[simp]
theorem I_im : i.im = 1 :=
  rfl

@[simp]
theorem I_mul_I : I * I = -1 :=
  ext_iff.2 <| by
    simp

theorem I_mul (z : ℂ) : I * z = ⟨-z.im, z.re⟩ :=
  ext_iff.2 <| by
    simp

theorem I_ne_zero : (i : ℂ) ≠ 0 :=
  mt (congr_arg im) zero_ne_one.symm

theorem mk_eq_add_mul_I (a b : ℝ) : Complex.mk a b = a + b * I :=
  ext_iff.2 <| by
    simp

@[simp]
theorem re_add_im (z : ℂ) : (z.re : ℂ) + z.im * I = z :=
  ext_iff.2 <| by
    simp

theorem mul_I_re (z : ℂ) : (z * I).re = -z.im := by
  simp

theorem mul_I_im (z : ℂ) : (z * I).im = z.re := by
  simp

theorem I_mul_re (z : ℂ) : (I * z).re = -z.im := by
  simp

theorem I_mul_im (z : ℂ) : (I * z).im = z.re := by
  simp

@[simp]
theorem equiv_real_prod_symm_apply (p : ℝ × ℝ) : equivRealProd.symm p = p.1 + p.2 * I := by
  ext <;> simp [← equiv_real_prod]

/-! ### Commutative ring instance and lemmas -/


/- We use a nonstandard formula for the `ℕ` and `ℤ` actions to make sure there is no
diamond from the other actions they inherit through the `ℝ`-action on `ℂ` and action transitivity
defined in `data.complex.module.lean`. -/
instance : AddCommGroupₓ ℂ := by
  refine_struct
      { zero := (0 : ℂ), add := (· + ·), neg := Neg.neg, sub := Sub.sub,
        nsmul := fun n z => ⟨n • z.re - 0 * z.im, n • z.im + 0 * z.re⟩,
        zsmul := fun n z => ⟨n • z.re - 0 * z.im, n • z.im + 0 * z.re⟩ } <;>
    intros <;>
      try
          rfl <;>
        apply ext_iff.2 <;>
          constructor <;>
            simp <;>
              · first |
                  ring1|
                  ring_nf
                

instance : AddGroupWithOneₓ ℂ :=
  { Complex.addCommGroup with natCast := fun n => ⟨n, 0⟩,
    nat_cast_zero := by
      ext <;> simp [← Nat.castₓ],
    nat_cast_succ := fun _ => by
      ext <;> simp [← Nat.castₓ],
    intCast := fun n => ⟨n, 0⟩,
    int_cast_of_nat := fun _ => by
      ext <;> simp [← fun n => show @coe ℕ ℂ ⟨_⟩ n = ⟨n, 0⟩ from rfl],
    int_cast_neg_succ_of_nat := fun _ => by
      ext <;> simp [← fun n => show @coe ℕ ℂ ⟨_⟩ n = ⟨n, 0⟩ from rfl],
    one := 1 }

instance : CommRingₓ ℂ := by
  refine_struct
      { Complex.addGroupWithOne with zero := (0 : ℂ), add := (· + ·), one := 1, mul := (· * ·),
        npow := @npowRec _ ⟨(1 : ℂ)⟩ ⟨(· * ·)⟩ } <;>
    intros <;>
      try
          rfl <;>
        apply ext_iff.2 <;>
          constructor <;>
            simp <;>
              · first |
                  ring1|
                  ring_nf
                

/-- This shortcut instance ensures we do not find `ring` via the noncomputable `complex.field`
instance. -/
instance : Ringₓ ℂ := by
  infer_instance

/-- This shortcut instance ensures we do not find `comm_semiring` via the noncomputable
`complex.field` instance. -/
instance : CommSemiringₓ ℂ :=
  inferInstance

/-- The "real part" map, considered as an additive group homomorphism. -/
def reAddGroupHom : ℂ →+ ℝ where
  toFun := re
  map_zero' := zero_re
  map_add' := add_re

@[simp]
theorem coe_re_add_group_hom : (reAddGroupHom : ℂ → ℝ) = re :=
  rfl

/-- The "imaginary part" map, considered as an additive group homomorphism. -/
def imAddGroupHom : ℂ →+ ℝ where
  toFun := im
  map_zero' := zero_im
  map_add' := add_im

@[simp]
theorem coe_im_add_group_hom : (imAddGroupHom : ℂ → ℝ) = im :=
  rfl

@[simp]
theorem I_pow_bit0 (n : ℕ) : I ^ bit0 n = -1 ^ n := by
  rw [pow_bit0', I_mul_I]

@[simp]
theorem I_pow_bit1 (n : ℕ) : I ^ bit1 n = -1 ^ n * I := by
  rw [pow_bit1', I_mul_I]

/-! ### Complex conjugation -/


/-- This defines the complex conjugate as the `star` operation of the `star_ring ℂ`. It
is recommended to use the ring endomorphism version `star_ring_end`, available under the
notation `conj` in the locale `complex_conjugate`. -/
instance : StarRing ℂ where
  star := fun z => ⟨z.re, -z.im⟩
  star_involutive := fun x => by
    simp only [← eta, ← neg_negₓ]
  star_mul := fun a b => by
    ext <;> simp [← add_commₓ] <;> ring
  star_add := fun a b => by
    ext <;> simp [← add_commₓ]

@[simp]
theorem conj_re (z : ℂ) : (conj z).re = z.re :=
  rfl

@[simp]
theorem conj_im (z : ℂ) : (conj z).im = -z.im :=
  rfl

theorem conj_of_real (r : ℝ) : conj (r : ℂ) = r :=
  ext_iff.2 <| by
    simp [← conj]

@[simp]
theorem conj_I : conj i = -I :=
  ext_iff.2 <| by
    simp

theorem conj_bit0 (z : ℂ) : conj (bit0 z) = bit0 (conj z) :=
  ext_iff.2 <| by
    simp [← bit0]

theorem conj_bit1 (z : ℂ) : conj (bit1 z) = bit1 (conj z) :=
  ext_iff.2 <| by
    simp [← bit0]

@[simp]
theorem conj_neg_I : conj (-I) = I :=
  ext_iff.2 <| by
    simp

theorem eq_conj_iff_real {z : ℂ} : conj z = z ↔ ∃ r : ℝ, z = r :=
  ⟨fun h => ⟨z.re, ext rfl <| eq_zero_of_neg_eq (congr_arg im h)⟩, fun ⟨h, e⟩ => by
    rw [e, conj_of_real]⟩

theorem eq_conj_iff_re {z : ℂ} : conj z = z ↔ (z.re : ℂ) = z :=
  eq_conj_iff_real.trans
    ⟨by
      rintro ⟨r, rfl⟩ <;> simp , fun h => ⟨_, h.symm⟩⟩

theorem eq_conj_iff_im {z : ℂ} : conj z = z ↔ z.im = 0 :=
  ⟨fun h => add_self_eq_zero.mp (neg_eq_iff_add_eq_zero.mp (congr_arg im h)), fun h =>
    ext rfl (neg_eq_iff_add_eq_zero.mpr (add_self_eq_zero.mpr h))⟩

-- `simp_nf` complains about this being provable by `is_R_or_C.star_def` even
-- though it's not imported by this file.
@[simp, nolint simp_nf]
theorem star_def : (HasStar.star : ℂ → ℂ) = conj :=
  rfl

/-! ### Norm squared -/


/-- The norm squared function. -/
@[pp_nodot]
def normSq : ℂ →*₀ ℝ where
  toFun := fun z => z.re * z.re + z.im * z.im
  map_zero' := by
    simp
  map_one' := by
    simp
  map_mul' := fun z w => by
    dsimp'
    ring

theorem norm_sq_apply (z : ℂ) : normSq z = z.re * z.re + z.im * z.im :=
  rfl

@[simp]
theorem norm_sq_of_real (r : ℝ) : normSq r = r * r := by
  simp [← norm_sq]

@[simp]
theorem norm_sq_mk (x y : ℝ) : normSq ⟨x, y⟩ = x * x + y * y :=
  rfl

theorem norm_sq_add_mul_I (x y : ℝ) : normSq (x + y * I) = x ^ 2 + y ^ 2 := by
  rw [← mk_eq_add_mul_I, norm_sq_mk, sq, sq]

theorem norm_sq_eq_conj_mul_self {z : ℂ} : (normSq z : ℂ) = conj z * z := by
  ext <;> simp [← norm_sq, ← mul_comm]

@[simp]
theorem norm_sq_zero : normSq 0 = 0 :=
  normSq.map_zero

@[simp]
theorem norm_sq_one : normSq 1 = 1 :=
  normSq.map_one

@[simp]
theorem norm_sq_I : normSq i = 1 := by
  simp [← norm_sq]

theorem norm_sq_nonneg (z : ℂ) : 0 ≤ normSq z :=
  add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)

@[simp]
theorem range_norm_sq : Range normSq = Ici 0 :=
  (Subset.antisymm (range_subset_iff.2 norm_sq_nonneg)) fun x hx =>
    ⟨Real.sqrt x, by
      rw [norm_sq_of_real, Real.mul_self_sqrt hx]⟩

theorem norm_sq_eq_zero {z : ℂ} : normSq z = 0 ↔ z = 0 :=
  ⟨fun h =>
    ext (eq_zero_of_mul_self_add_mul_self_eq_zero h)
      (eq_zero_of_mul_self_add_mul_self_eq_zero <| (add_commₓ _ _).trans h),
    fun h => h.symm ▸ norm_sq_zero⟩

@[simp]
theorem norm_sq_pos {z : ℂ} : 0 < normSq z ↔ z ≠ 0 :=
  (norm_sq_nonneg z).lt_iff_ne.trans <| not_congr (eq_comm.trans norm_sq_eq_zero)

@[simp]
theorem norm_sq_neg (z : ℂ) : normSq (-z) = normSq z := by
  simp [← norm_sq]

@[simp]
theorem norm_sq_conj (z : ℂ) : normSq (conj z) = normSq z := by
  simp [← norm_sq]

theorem norm_sq_mul (z w : ℂ) : normSq (z * w) = normSq z * normSq w :=
  normSq.map_mul z w

theorem norm_sq_add (z w : ℂ) : normSq (z + w) = normSq z + normSq w + 2 * (z * conj w).re := by
  dsimp' [← norm_sq] <;> ring

theorem re_sq_le_norm_sq (z : ℂ) : z.re * z.re ≤ normSq z :=
  le_add_of_nonneg_right (mul_self_nonneg _)

theorem im_sq_le_norm_sq (z : ℂ) : z.im * z.im ≤ normSq z :=
  le_add_of_nonneg_left (mul_self_nonneg _)

theorem mul_conj (z : ℂ) : z * conj z = normSq z :=
  ext_iff.2 <| by
    simp [← norm_sq, ← mul_comm, ← sub_eq_neg_add, ← add_commₓ]

theorem add_conj (z : ℂ) : z + conj z = (2 * z.re : ℝ) :=
  ext_iff.2 <| by
    simp [← two_mul]

/-- The coercion `ℝ → ℂ` as a `ring_hom`. -/
def ofReal : ℝ →+* ℂ :=
  ⟨coe, of_real_one, of_real_mul, of_real_zero, of_real_add⟩

@[simp]
theorem of_real_eq_coe (r : ℝ) : ofReal r = r :=
  rfl

@[simp]
theorem I_sq : I ^ 2 = -1 := by
  rw [sq, I_mul_I]

@[simp]
theorem sub_re (z w : ℂ) : (z - w).re = z.re - w.re :=
  rfl

@[simp]
theorem sub_im (z w : ℂ) : (z - w).im = z.im - w.im :=
  rfl

@[simp, norm_cast]
theorem of_real_sub (r s : ℝ) : ((r - s : ℝ) : ℂ) = r - s :=
  ext_iff.2 <| by
    simp

@[simp, norm_cast]
theorem of_real_pow (r : ℝ) (n : ℕ) : ((r ^ n : ℝ) : ℂ) = r ^ n := by
  induction n <;> simp [*, ← of_real_mul, ← pow_succₓ]

theorem sub_conj (z : ℂ) : z - conj z = (2 * z.im : ℝ) * I :=
  ext_iff.2 <| by
    simp [← two_mul, ← sub_eq_add_neg]

theorem norm_sq_sub (z w : ℂ) : normSq (z - w) = normSq z + normSq w - 2 * (z * conj w).re := by
  rw [sub_eq_add_neg, norm_sq_add]
  simp only [← RingHom.map_neg, ← mul_neg, ← neg_re, ← Tactic.Ring.add_neg_eq_sub, ← norm_sq_neg]

/-! ### Inversion -/


noncomputable instance : Inv ℂ :=
  ⟨fun z => conj z * ((normSq z)⁻¹ : ℝ)⟩

theorem inv_def (z : ℂ) : z⁻¹ = conj z * ((normSq z)⁻¹ : ℝ) :=
  rfl

@[simp]
theorem inv_re (z : ℂ) : z⁻¹.re = z.re / normSq z := by
  simp [← inv_def, ← division_def]

@[simp]
theorem inv_im (z : ℂ) : z⁻¹.im = -z.im / normSq z := by
  simp [← inv_def, ← division_def]

@[simp, norm_cast]
theorem of_real_inv (r : ℝ) : ((r⁻¹ : ℝ) : ℂ) = r⁻¹ :=
  ext_iff.2 <| by
    simp

protected theorem inv_zero : (0⁻¹ : ℂ) = 0 := by
  rw [← of_real_zero, ← of_real_inv, inv_zero]

protected theorem mul_inv_cancel {z : ℂ} (h : z ≠ 0) : z * z⁻¹ = 1 := by
  rw [inv_def, ← mul_assoc, mul_conj, ← of_real_mul, mul_inv_cancel (mt norm_sq_eq_zero.1 h), of_real_one]

/-! ### Field instance and lemmas -/


noncomputable instance : Field ℂ :=
  { Complex.commRing with inv := Inv.inv, exists_pair_ne := ⟨0, 1, mt (congr_arg re) zero_ne_one⟩,
    mul_inv_cancel := @Complex.mul_inv_cancel, inv_zero := Complex.inv_zero }

@[simp]
theorem I_zpow_bit0 (n : ℤ) : I ^ bit0 n = -1 ^ n := by
  rw [zpow_bit0', I_mul_I]

@[simp]
theorem I_zpow_bit1 (n : ℤ) : I ^ bit1 n = -1 ^ n * I := by
  rw [zpow_bit1', I_mul_I]

theorem div_re (z w : ℂ) : (z / w).re = z.re * w.re / normSq w + z.im * w.im / normSq w := by
  simp [← div_eq_mul_inv, ← mul_assoc, ← sub_eq_add_neg]

theorem div_im (z w : ℂ) : (z / w).im = z.im * w.re / normSq w - z.re * w.im / normSq w := by
  simp [← div_eq_mul_inv, ← mul_assoc, ← sub_eq_add_neg, ← add_commₓ]

theorem conj_inv (x : ℂ) : conj x⁻¹ = (conj x)⁻¹ :=
  star_inv' _

@[simp, norm_cast]
theorem of_real_div (r s : ℝ) : ((r / s : ℝ) : ℂ) = r / s :=
  ofReal.map_div r s

@[simp, norm_cast]
theorem of_real_zpow (r : ℝ) (n : ℤ) : ((r ^ n : ℝ) : ℂ) = (r : ℂ) ^ n :=
  ofReal.map_zpow r n

@[simp]
theorem div_I (z : ℂ) : z / I = -(z * I) :=
  (div_eq_iff_mul_eq I_ne_zero).2 <| by
    simp [← mul_assoc]

@[simp]
theorem inv_I : I⁻¹ = -I := by
  simp [← inv_eq_one_div]

@[simp]
theorem norm_sq_inv (z : ℂ) : normSq z⁻¹ = (normSq z)⁻¹ :=
  normSq.map_inv z

@[simp]
theorem norm_sq_div (z w : ℂ) : normSq (z / w) = normSq z / normSq w :=
  normSq.map_div z w

/-! ### Cast lemmas -/


@[simp, norm_cast]
theorem of_real_nat_cast (n : ℕ) : ((n : ℝ) : ℂ) = n :=
  map_nat_cast ofReal n

@[simp, norm_cast]
theorem nat_cast_re (n : ℕ) : (n : ℂ).re = n := by
  rw [← of_real_nat_cast, of_real_re]

@[simp, norm_cast]
theorem nat_cast_im (n : ℕ) : (n : ℂ).im = 0 := by
  rw [← of_real_nat_cast, of_real_im]

@[simp, norm_cast]
theorem of_real_int_cast (n : ℤ) : ((n : ℝ) : ℂ) = n :=
  ofReal.map_int_cast n

@[simp, norm_cast]
theorem int_cast_re (n : ℤ) : (n : ℂ).re = n := by
  rw [← of_real_int_cast, of_real_re]

@[simp, norm_cast]
theorem int_cast_im (n : ℤ) : (n : ℂ).im = 0 := by
  rw [← of_real_int_cast, of_real_im]

@[simp, norm_cast]
theorem of_real_rat_cast (n : ℚ) : ((n : ℝ) : ℂ) = n :=
  map_rat_cast ofReal n

@[simp, norm_cast]
theorem rat_cast_re (q : ℚ) : (q : ℂ).re = q := by
  rw [← of_real_rat_cast, of_real_re]

@[simp, norm_cast]
theorem rat_cast_im (q : ℚ) : (q : ℂ).im = 0 := by
  rw [← of_real_rat_cast, of_real_im]

/-! ### Characteristic zero -/


instance char_zero_complex : CharZero ℂ :=
  char_zero_of_inj_zero fun n h => by
    rwa [← of_real_nat_cast, of_real_eq_zero, Nat.cast_eq_zero] at h

/-- A complex number `z` plus its conjugate `conj z` is `2` times its real part. -/
theorem re_eq_add_conj (z : ℂ) : (z.re : ℂ) = (z + conj z) / 2 := by
  simp only [← add_conj, ← of_real_mul, ← of_real_one, ← of_real_bit0, ← mul_div_cancel_left (z.re : ℂ) two_ne_zero']

/-- A complex number `z` minus its conjugate `conj z` is `2i` times its imaginary part. -/
theorem im_eq_sub_conj (z : ℂ) : (z.im : ℂ) = (z - conj z) / (2 * I) := by
  simp only [← sub_conj, ← of_real_mul, ← of_real_one, ← of_real_bit0, ← mul_right_commₓ, ←
    mul_div_cancel_left _ (mul_ne_zero two_ne_zero' I_ne_zero : 2 * I ≠ 0)]

/-! ### Absolute value -/


/-- The complex absolute value function, defined as the square root of the norm squared. -/
@[pp_nodot]
noncomputable def abs (z : ℂ) : ℝ :=
  (normSq z).sqrt

-- mathport name: «exprabs'»
local notation "abs'" => HasAbs.abs

@[simp, norm_cast]
theorem abs_of_real (r : ℝ) : abs r = abs r := by
  simp [← abs, ← norm_sq_of_real, ← Real.sqrt_mul_self_eq_abs]

theorem abs_of_nonneg {r : ℝ} (h : 0 ≤ r) : abs r = r :=
  (abs_of_real _).trans (abs_of_nonneg h)

theorem abs_of_nat (n : ℕ) : Complex.abs n = n :=
  calc
    Complex.abs n = Complex.abs (n : ℝ) := by
      rw [of_real_nat_cast]
    _ = _ := abs_of_nonneg (Nat.cast_nonneg n)
    

theorem mul_self_abs (z : ℂ) : abs z * abs z = normSq z :=
  Real.mul_self_sqrt (norm_sq_nonneg _)

theorem sq_abs (z : ℂ) : abs z ^ 2 = normSq z :=
  Real.sq_sqrt (norm_sq_nonneg _)

@[simp]
theorem sq_abs_sub_sq_re (z : ℂ) : abs z ^ 2 - z.re ^ 2 = z.im ^ 2 := by
  rw [sq_abs, norm_sq_apply, ← sq, ← sq, add_sub_cancel']

@[simp]
theorem sq_abs_sub_sq_im (z : ℂ) : abs z ^ 2 - z.im ^ 2 = z.re ^ 2 := by
  rw [← sq_abs_sub_sq_re, sub_sub_cancel]

@[simp]
theorem abs_zero : abs 0 = 0 := by
  simp [← abs]

@[simp]
theorem abs_one : abs 1 = 1 := by
  simp [← abs]

@[simp]
theorem abs_I : abs i = 1 := by
  simp [← abs]

@[simp]
theorem abs_two : abs 2 = 2 :=
  calc
    abs 2 = abs (2 : ℝ) := by
      rw [of_real_bit0, of_real_one]
    _ = (2 : ℝ) :=
      abs_of_nonneg
        (by
          norm_num)
    

theorem abs_nonneg (z : ℂ) : 0 ≤ abs z :=
  Real.sqrt_nonneg _

@[simp]
theorem range_abs : Range abs = Ici 0 :=
  (Subset.antisymm (range_subset_iff.2 abs_nonneg)) fun x hx => ⟨x, abs_of_nonneg hx⟩

@[simp]
theorem abs_eq_zero {z : ℂ} : abs z = 0 ↔ z = 0 :=
  (Real.sqrt_eq_zero <| norm_sq_nonneg _).trans norm_sq_eq_zero

theorem abs_ne_zero {z : ℂ} : abs z ≠ 0 ↔ z ≠ 0 :=
  not_congr abs_eq_zero

@[simp]
theorem abs_conj (z : ℂ) : abs (conj z) = abs z := by
  simp [← abs]

@[simp]
theorem abs_mul (z w : ℂ) : abs (z * w) = abs z * abs w := by
  rw [abs, norm_sq_mul, Real.sqrt_mul (norm_sq_nonneg _)] <;> rfl

/-- `complex.abs` as a `monoid_with_zero_hom`. -/
@[simps]
noncomputable def absHom : ℂ →*₀ ℝ where
  toFun := abs
  map_zero' := abs_zero
  map_one' := abs_one
  map_mul' := abs_mul

@[simp]
theorem abs_prod {ι : Type _} (s : Finset ι) (f : ι → ℂ) : abs (s.Prod f) = s.Prod fun i => abs (f i) :=
  map_prod absHom _ _

@[simp]
theorem abs_pow (z : ℂ) (n : ℕ) : abs (z ^ n) = abs z ^ n :=
  map_pow absHom z n

@[simp]
theorem abs_zpow (z : ℂ) (n : ℤ) : abs (z ^ n) = abs z ^ n :=
  absHom.map_zpow z n

theorem abs_re_le_abs (z : ℂ) : abs z.re ≤ abs z := by
  rw [mul_self_le_mul_self_iff (_root_.abs_nonneg z.re) (abs_nonneg _), abs_mul_abs_self, mul_self_abs] <;>
    apply re_sq_le_norm_sq

theorem abs_im_le_abs (z : ℂ) : abs z.im ≤ abs z := by
  rw [mul_self_le_mul_self_iff (_root_.abs_nonneg z.im) (abs_nonneg _), abs_mul_abs_self, mul_self_abs] <;>
    apply im_sq_le_norm_sq

theorem re_le_abs (z : ℂ) : z.re ≤ abs z :=
  (abs_le.1 (abs_re_le_abs _)).2

theorem im_le_abs (z : ℂ) : z.im ≤ abs z :=
  (abs_le.1 (abs_im_le_abs _)).2

@[simp]
theorem abs_re_lt_abs {z : ℂ} : abs z.re < abs z ↔ z.im ≠ 0 := by
  rw [abs, Real.lt_sqrt (_root_.abs_nonneg _), norm_sq_apply, _root_.sq_abs, ← sq, lt_add_iff_pos_right, mul_self_pos]

@[simp]
theorem abs_im_lt_abs {z : ℂ} : abs z.im < abs z ↔ z.re ≠ 0 := by
  simpa using @abs_re_lt_abs (z * I)

/-- The **triangle inequality** for complex numbers.
-/
theorem abs_add (z w : ℂ) : abs (z + w) ≤ abs z + abs w :=
  (mul_self_le_mul_self_iff (abs_nonneg _) (add_nonneg (abs_nonneg _) (abs_nonneg _))).2 <| by
    rw [mul_self_abs, add_mul_self_eq, mul_self_abs, mul_self_abs, add_right_commₓ, norm_sq_add, add_le_add_iff_left,
      mul_assoc, mul_le_mul_left (@zero_lt_two ℝ _ _)]
    simpa [-mul_re] using re_le_abs (z * conj w)

instance : IsAbsoluteValue abs where
  abv_nonneg := abs_nonneg
  abv_eq_zero := fun _ => abs_eq_zero
  abv_add := abs_add
  abv_mul := abs_mul

open IsAbsoluteValue

@[simp]
theorem abs_abs (z : ℂ) : abs (abs z) = abs z :=
  abs_of_nonneg (abs_nonneg _)

@[simp]
theorem abs_pos {z : ℂ} : 0 < abs z ↔ z ≠ 0 :=
  abv_pos abs

@[simp]
theorem abs_neg : ∀ z, abs (-z) = abs z :=
  abv_neg abs

theorem abs_sub_comm : ∀ z w, abs (z - w) = abs (w - z) :=
  abv_sub abs

theorem abs_sub_le : ∀ a b c, abs (a - c) ≤ abs (a - b) + abs (b - c) :=
  abv_sub_le abs

@[simp]
theorem abs_inv : ∀ z, abs z⁻¹ = (abs z)⁻¹ :=
  abv_inv abs

@[simp]
theorem abs_div : ∀ z w, abs (z / w) = abs z / abs w :=
  abv_div abs

theorem abs_abs_sub_le_abs_sub : ∀ z w, abs (abs z - abs w) ≤ abs (z - w) :=
  abs_abv_sub_le_abv_sub abs

theorem abs_le_abs_re_add_abs_im (z : ℂ) : abs z ≤ abs z.re + abs z.im := by
  simpa [← re_add_im] using abs_add z.re (z.im * I)

theorem abs_le_sqrt_two_mul_max (z : ℂ) : abs z ≤ Real.sqrt 2 * max (abs z.re) (abs z.im) := by
  cases' z with x y
  simp only [← abs, ← norm_sq_mk, sq]
  wlog (discharger := tactic.skip) hle : abs x ≤ abs y := le_totalₓ (abs x) (abs y) using x y, y x
  · calc Real.sqrt (x ^ 2 + y ^ 2) ≤ Real.sqrt (y ^ 2 + y ^ 2) :=
        Real.sqrt_le_sqrt (add_le_add_right (sq_le_sq.2 hle) _)_ = Real.sqrt 2 * max (abs x) (abs y) := by
        rw [max_eq_rightₓ hle, ← two_mul, Real.sqrt_mul two_pos.le, Real.sqrt_sq_eq_abs]
    
  · rwa [add_commₓ, max_commₓ]
    

theorem abs_re_div_abs_le_one (z : ℂ) : abs (z.re / z.abs) ≤ 1 :=
  if hz : z = 0 then by
    simp [← hz, ← zero_le_one]
  else by
    simp_rw [_root_.abs_div, abs_abs, div_le_iff (abs_pos.2 hz), one_mulₓ, abs_re_le_abs]

theorem abs_im_div_abs_le_one (z : ℂ) : abs (z.im / z.abs) ≤ 1 :=
  if hz : z = 0 then by
    simp [← hz, ← zero_le_one]
  else by
    simp_rw [_root_.abs_div, abs_abs, div_le_iff (abs_pos.2 hz), one_mulₓ, abs_im_le_abs]

@[simp, norm_cast]
theorem abs_cast_nat (n : ℕ) : abs (n : ℂ) = n := by
  rw [← of_real_nat_cast, abs_of_nonneg (Nat.cast_nonneg n)]

@[simp, norm_cast]
theorem int_cast_abs (n : ℤ) : ↑(abs n) = abs n := by
  rw [← of_real_int_cast, abs_of_real, Int.cast_abs]

theorem norm_sq_eq_abs (x : ℂ) : normSq x = abs x ^ 2 := by
  rw [abs, sq, Real.mul_self_sqrt (norm_sq_nonneg _)]

/-- We put a partial order on ℂ so that `z ≤ w` exactly if `w - z` is real and nonnegative.
Complex numbers with different imaginary parts are incomparable.
-/
protected def partialOrder : PartialOrderₓ ℂ where
  le := fun z w => z.re ≤ w.re ∧ z.im = w.im
  lt := fun z w => z.re < w.re ∧ z.im = w.im
  lt_iff_le_not_le := fun z w => by
    dsimp'
    rw [lt_iff_le_not_leₓ]
    tauto
  le_refl := fun x => ⟨le_rfl, rfl⟩
  le_trans := fun x y z h₁ h₂ => ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩
  le_antisymm := fun z w h₁ h₂ => ext (h₁.1.antisymm h₂.1) h₁.2

section ComplexOrder

localized [ComplexOrder] attribute [instance] Complex.partialOrder

theorem le_def {z w : ℂ} : z ≤ w ↔ z.re ≤ w.re ∧ z.im = w.im :=
  Iff.rfl

theorem lt_def {z w : ℂ} : z < w ↔ z.re < w.re ∧ z.im = w.im :=
  Iff.rfl

@[simp, norm_cast]
theorem real_le_real {x y : ℝ} : (x : ℂ) ≤ (y : ℂ) ↔ x ≤ y := by
  simp [← le_def]

@[simp, norm_cast]
theorem real_lt_real {x y : ℝ} : (x : ℂ) < (y : ℂ) ↔ x < y := by
  simp [← lt_def]

@[simp, norm_cast]
theorem zero_le_real {x : ℝ} : (0 : ℂ) ≤ (x : ℂ) ↔ 0 ≤ x :=
  real_le_real

@[simp, norm_cast]
theorem zero_lt_real {x : ℝ} : (0 : ℂ) < (x : ℂ) ↔ 0 < x :=
  real_lt_real

theorem not_le_iff {z w : ℂ} : ¬z ≤ w ↔ w.re < z.re ∨ z.im ≠ w.im := by
  rw [le_def, not_and_distrib, not_leₓ]

theorem not_lt_iff {z w : ℂ} : ¬z < w ↔ w.re ≤ z.re ∨ z.im ≠ w.im := by
  rw [lt_def, not_and_distrib, not_ltₓ]

theorem not_le_zero_iff {z : ℂ} : ¬z ≤ 0 ↔ 0 < z.re ∨ z.im ≠ 0 :=
  not_le_iff

theorem not_lt_zero_iff {z : ℂ} : ¬z < 0 ↔ 0 ≤ z.re ∨ z.im ≠ 0 :=
  not_lt_iff

/-- With `z ≤ w` iff `w - z` is real and nonnegative, `ℂ` is an ordered ring.
-/
protected def orderedCommRing : OrderedCommRing ℂ :=
  { Complex.partialOrder, Complex.commRing with zero_le_one := ⟨zero_le_one, rfl⟩,
    add_le_add_left := fun w z h y => ⟨add_le_add_left h.1 _, congr_arg2ₓ (· + ·) rfl h.2⟩,
    mul_pos := fun z w hz hw => by
      simp [← lt_def, ← mul_re, ← mul_im, hz.2, hw.2, ← mul_pos hz.1 hw.1] }

localized [ComplexOrder] attribute [instance] Complex.orderedCommRing

/-- With `z ≤ w` iff `w - z` is real and nonnegative, `ℂ` is a star ordered ring.
(That is, a star ring in which the nonnegative elements are those of the form `star z * z`.)
-/
protected def starOrderedRing : StarOrderedRing ℂ :=
  { Complex.orderedCommRing with
    nonneg_iff := fun r => by
      refine' ⟨fun hr => ⟨Real.sqrt r.re, _⟩, fun h => _⟩
      · have h₁ : 0 ≤ r.re := by
          rw [le_def] at hr
          exact hr.1
        have h₂ : r.im = 0 := by
          rw [le_def] at hr
          exact hr.2.symm
        ext
        · simp only [← of_real_im, ← star_def, ← of_real_re, ← sub_zero, ← conj_re, ← mul_re, ← mul_zero,
            Real.sqrt_mul h₁ r.re, ← Real.sqrt_mul_self h₁]
          
        · simp only [← h₂, ← add_zeroₓ, ← of_real_im, ← star_def, ← zero_mul, ← conj_im, ← mul_im, ← mul_zero, ←
            neg_zero]
          
        
      · obtain ⟨s, rfl⟩ := h
        simp only [norm_sq_eq_conj_mul_self, ← norm_sq_nonneg, ← zero_le_real, ← star_def]
         }

localized [ComplexOrder] attribute [instance] Complex.starOrderedRing

end ComplexOrder

/-! ### Cauchy sequences -/


theorem is_cau_seq_re (f : CauSeq ℂ abs) : IsCauSeq abs' fun n => (f n).re := fun ε ε0 =>
  (f.cauchy ε0).imp fun i H j ij =>
    lt_of_le_of_ltₓ
      (by
        simpa using abs_re_le_abs (f j - f i))
      (H _ ij)

theorem is_cau_seq_im (f : CauSeq ℂ abs) : IsCauSeq abs' fun n => (f n).im := fun ε ε0 =>
  (f.cauchy ε0).imp fun i H j ij =>
    lt_of_le_of_ltₓ
      (by
        simpa using abs_im_le_abs (f j - f i))
      (H _ ij)

/-- The real part of a complex Cauchy sequence, as a real Cauchy sequence. -/
noncomputable def cauSeqRe (f : CauSeq ℂ abs) : CauSeq ℝ abs' :=
  ⟨_, is_cau_seq_re f⟩

/-- The imaginary part of a complex Cauchy sequence, as a real Cauchy sequence. -/
noncomputable def cauSeqIm (f : CauSeq ℂ abs) : CauSeq ℝ abs' :=
  ⟨_, is_cau_seq_im f⟩

theorem is_cau_seq_abs {f : ℕ → ℂ} (hf : IsCauSeq abs f) : IsCauSeq abs' (abs ∘ f) := fun ε ε0 =>
  let ⟨i, hi⟩ := hf ε ε0
  ⟨i, fun j hj => lt_of_le_of_ltₓ (abs_abs_sub_le_abs_sub _ _) (hi j hj)⟩

/-- The limit of a Cauchy sequence of complex numbers. -/
noncomputable def limAux (f : CauSeq ℂ abs) : ℂ :=
  ⟨CauSeq.lim (cauSeqRe f), CauSeq.lim (cauSeqIm f)⟩

theorem equiv_lim_aux (f : CauSeq ℂ abs) : f ≈ CauSeq.const abs (limAux f) := fun ε ε0 =>
  (exists_forall_ge_and (CauSeq.equiv_lim ⟨_, is_cau_seq_re f⟩ _ (half_pos ε0))
        (CauSeq.equiv_lim ⟨_, is_cau_seq_im f⟩ _ (half_pos ε0))).imp
    fun i H j ij => by
    cases' H _ ij with H₁ H₂
    apply lt_of_le_of_ltₓ (abs_le_abs_re_add_abs_im _)
    dsimp' [← lim_aux]  at *
    have := add_lt_add H₁ H₂
    rwa [add_halves] at this

instance : CauSeq.IsComplete ℂ abs :=
  ⟨fun f => ⟨limAux f, equiv_lim_aux f⟩⟩

open CauSeq

theorem lim_eq_lim_im_add_lim_re (f : CauSeq ℂ abs) : limₓ f = ↑(limₓ (cauSeqRe f)) + ↑(limₓ (cauSeqIm f)) * I :=
  lim_eq_of_equiv_const <|
    calc
      f ≈ _ := equiv_lim_aux f
      _ = CauSeq.const abs (↑(limₓ (cauSeqRe f)) + ↑(limₓ (cauSeqIm f)) * I) :=
        CauSeq.ext fun _ =>
          Complex.ext
            (by
              simp [← lim_aux, ← cau_seq_re])
            (by
              simp [← lim_aux, ← cau_seq_im])
      

theorem lim_re (f : CauSeq ℂ abs) : limₓ (cauSeqRe f) = (limₓ f).re := by
  rw [lim_eq_lim_im_add_lim_re] <;> simp

theorem lim_im (f : CauSeq ℂ abs) : limₓ (cauSeqIm f) = (limₓ f).im := by
  rw [lim_eq_lim_im_add_lim_re] <;> simp

theorem is_cau_seq_conj (f : CauSeq ℂ abs) : IsCauSeq abs fun n => conj (f n) := fun ε ε0 =>
  let ⟨i, hi⟩ := f.2 ε ε0
  ⟨i, fun j hj => by
    rw [← RingHom.map_sub, abs_conj] <;> exact hi j hj⟩

/-- The complex conjugate of a complex Cauchy sequence, as a complex Cauchy sequence. -/
noncomputable def cauSeqConj (f : CauSeq ℂ abs) : CauSeq ℂ abs :=
  ⟨_, is_cau_seq_conj f⟩

theorem lim_conj (f : CauSeq ℂ abs) : limₓ (cauSeqConj f) = conj (limₓ f) :=
  Complex.ext
    (by
      simp [← cau_seq_conj, ← (lim_re _).symm, ← cau_seq_re])
    (by
      simp [← cau_seq_conj, ← (lim_im _).symm, ← cau_seq_im, ← (lim_neg _).symm] <;> rfl)

/-- The absolute value of a complex Cauchy sequence, as a real Cauchy sequence. -/
noncomputable def cauSeqAbs (f : CauSeq ℂ abs) : CauSeq ℝ abs' :=
  ⟨_, is_cau_seq_abs f.2⟩

theorem lim_abs (f : CauSeq ℂ abs) : limₓ (cauSeqAbs f) = abs (limₓ f) :=
  lim_eq_of_equiv_const fun ε ε0 =>
    let ⟨i, hi⟩ := equiv_lim f ε ε0
    ⟨i, fun j hj => lt_of_le_of_ltₓ (abs_abs_sub_le_abs_sub _ _) (hi j hj)⟩

variable {α : Type _} (s : Finset α)

@[simp, norm_cast]
theorem of_real_prod (f : α → ℝ) : ((∏ i in s, f i : ℝ) : ℂ) = ∏ i in s, (f i : ℂ) :=
  RingHom.map_prod ofReal _ _

@[simp, norm_cast]
theorem of_real_sum (f : α → ℝ) : ((∑ i in s, f i : ℝ) : ℂ) = ∑ i in s, (f i : ℂ) :=
  RingHom.map_sum ofReal _ _

@[simp]
theorem re_sum (f : α → ℂ) : (∑ i in s, f i).re = ∑ i in s, (f i).re :=
  reAddGroupHom.map_sum f s

@[simp]
theorem im_sum (f : α → ℂ) : (∑ i in s, f i).im = ∑ i in s, (f i).im :=
  imAddGroupHom.map_sum f s

end Complex

