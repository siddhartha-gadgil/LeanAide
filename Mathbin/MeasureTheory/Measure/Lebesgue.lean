/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Sébastien Gouëzel, Yury Kudryashov
-/
import Mathbin.Dynamics.Ergodic.MeasurePreserving
import Mathbin.LinearAlgebra.Determinant
import Mathbin.LinearAlgebra.Matrix.Diagonal
import Mathbin.LinearAlgebra.Matrix.Transvection
import Mathbin.MeasureTheory.Constructions.Pi
import Mathbin.MeasureTheory.Measure.Stieltjes

/-!
# Lebesgue measure on the real line and on `ℝⁿ`

We construct Lebesgue measure on the real line, as a particular case of Stieltjes measure associated
to the function `x ↦ x`. We obtain as a consequence Lebesgue measure on `ℝⁿ`. We prove that they
are translation invariant.

We show that, on `ℝⁿ`, a linear map acts on Lebesgue measure by rescaling it through the absolute
value of its determinant, in `real.map_linear_map_volume_pi_eq_smul_volume_pi`.

More properties of the Lebesgue measure are deduced from this in `haar_lebesgue.lean`, where they
are proved more generally for any additive Haar measure on a finite-dimensional real vector space.
-/


noncomputable section

open Classical Set Filter MeasureTheory MeasureTheory.Measure

open Ennreal (ofReal)

open BigOperators Ennreal Nnreal TopologicalSpace

/-!
### Definition of the Lebesgue measure and lengths of intervals
-/


/-- Lebesgue measure on the Borel sigma algebra, giving measure `b - a` to the interval `[a, b]`. -/
instance Real.measureSpace : MeasureSpace ℝ :=
  ⟨StieltjesFunction.id.Measure⟩

namespace Real

variable {ι : Type _} [Fintype ι]

open TopologicalSpace

theorem volume_val (s) : volume s = StieltjesFunction.id.Measure s :=
  rfl

@[simp]
theorem volume_Ico {a b : ℝ} : volume (Ico a b) = ofReal (b - a) := by
  simp [← volume_val]

@[simp]
theorem volume_Icc {a b : ℝ} : volume (Icc a b) = ofReal (b - a) := by
  simp [← volume_val]

@[simp]
theorem volume_Ioo {a b : ℝ} : volume (Ioo a b) = ofReal (b - a) := by
  simp [← volume_val]

@[simp]
theorem volume_Ioc {a b : ℝ} : volume (Ioc a b) = ofReal (b - a) := by
  simp [← volume_val]

@[simp]
theorem volume_singleton {a : ℝ} : volume ({a} : Set ℝ) = 0 := by
  simp [← volume_val]

@[simp]
theorem volume_univ : volume (Univ : Set ℝ) = ∞ :=
  Ennreal.eq_top_of_forall_nnreal_le fun r =>
    calc
      (r : ℝ≥0∞) = volume (Icc (0 : ℝ) r) := by
        simp
      _ ≤ volume Univ := measure_mono (subset_univ _)
      

@[simp]
theorem volume_ball (a r : ℝ) : volume (Metric.Ball a r) = ofReal (2 * r) := by
  rw [ball_eq_Ioo, volume_Ioo, ← sub_add, add_sub_cancel', two_mul]

@[simp]
theorem volume_closed_ball (a r : ℝ) : volume (Metric.ClosedBall a r) = ofReal (2 * r) := by
  rw [closed_ball_eq_Icc, volume_Icc, ← sub_add, add_sub_cancel', two_mul]

@[simp]
theorem volume_emetric_ball (a : ℝ) (r : ℝ≥0∞) : volume (Emetric.Ball a r) = 2 * r := by
  rcases eq_or_ne r ∞ with (rfl | hr)
  · rw [Metric.emetric_ball_top, volume_univ, two_mul, Ennreal.top_add]
    
  · lift r to ℝ≥0 using hr
    rw [Metric.emetric_ball_nnreal, volume_ball, two_mul, ← Nnreal.coe_add, Ennreal.of_real_coe_nnreal, Ennreal.coe_add,
      two_mul]
    

@[simp]
theorem volume_emetric_closed_ball (a : ℝ) (r : ℝ≥0∞) : volume (Emetric.ClosedBall a r) = 2 * r := by
  rcases eq_or_ne r ∞ with (rfl | hr)
  · rw [Emetric.closed_ball_top, volume_univ, two_mul, Ennreal.top_add]
    
  · lift r to ℝ≥0 using hr
    rw [Metric.emetric_closed_ball_nnreal, volume_closed_ball, two_mul, ← Nnreal.coe_add, Ennreal.of_real_coe_nnreal,
      Ennreal.coe_add, two_mul]
    

instance has_no_atoms_volume : HasNoAtoms (volume : Measureₓ ℝ) :=
  ⟨fun x => volume_singleton⟩

@[simp]
theorem volume_interval {a b : ℝ} : volume (Interval a b) = ofReal (abs (b - a)) := by
  rw [interval, volume_Icc, max_sub_min_eq_abs]

@[simp]
theorem volume_Ioi {a : ℝ} : volume (Ioi a) = ∞ :=
  top_unique <|
    (le_of_tendsto' Ennreal.tendsto_nat_nhds_top) fun n =>
      calc
        (n : ℝ≥0∞) = volume (Ioo a (a + n)) := by
          simp
        _ ≤ volume (Ioi a) := measure_mono Ioo_subset_Ioi_self
        

@[simp]
theorem volume_Ici {a : ℝ} : volume (Ici a) = ∞ := by
  simp [measure_congr Ioi_ae_eq_Ici]

@[simp]
theorem volume_Iio {a : ℝ} : volume (Iio a) = ∞ :=
  top_unique <|
    (le_of_tendsto' Ennreal.tendsto_nat_nhds_top) fun n =>
      calc
        (n : ℝ≥0∞) = volume (Ioo (a - n) a) := by
          simp
        _ ≤ volume (Iio a) := measure_mono Ioo_subset_Iio_self
        

@[simp]
theorem volume_Iic {a : ℝ} : volume (Iic a) = ∞ := by
  simp [measure_congr Iio_ae_eq_Iic]

instance locally_finite_volume : IsLocallyFiniteMeasure (volume : Measureₓ ℝ) :=
  ⟨fun x =>
    ⟨Ioo (x - 1) (x + 1), IsOpen.mem_nhds is_open_Ioo ⟨sub_lt_self _ zero_lt_one, lt_add_of_pos_right _ zero_lt_one⟩, by
      simp only [← Real.volume_Ioo, ← Ennreal.of_real_lt_top]⟩⟩

instance is_finite_measure_restrict_Icc (x y : ℝ) : IsFiniteMeasure (volume.restrict (Icc x y)) :=
  ⟨by
    simp ⟩

instance is_finite_measure_restrict_Ico (x y : ℝ) : IsFiniteMeasure (volume.restrict (Ico x y)) :=
  ⟨by
    simp ⟩

instance is_finite_measure_restrict_Ioc (x y : ℝ) : IsFiniteMeasure (volume.restrict (Ioc x y)) :=
  ⟨by
    simp ⟩

instance is_finite_measure_restrict_Ioo (x y : ℝ) : IsFiniteMeasure (volume.restrict (Ioo x y)) :=
  ⟨by
    simp ⟩

/-!
### Volume of a box in `ℝⁿ`
-/


theorem volume_Icc_pi {a b : ι → ℝ} : volume (Icc a b) = ∏ i, Ennreal.ofReal (b i - a i) := by
  rw [← pi_univ_Icc, volume_pi_pi]
  simp only [← Real.volume_Icc]

@[simp]
theorem volume_Icc_pi_to_real {a b : ι → ℝ} (h : a ≤ b) : (volume (Icc a b)).toReal = ∏ i, b i - a i := by
  simp only [← volume_Icc_pi, ← Ennreal.to_real_prod, ← Ennreal.to_real_of_real (sub_nonneg.2 (h _))]

theorem volume_pi_Ioo {a b : ι → ℝ} : volume (pi Univ fun i => Ioo (a i) (b i)) = ∏ i, Ennreal.ofReal (b i - a i) :=
  (measure_congr Measure.univ_pi_Ioo_ae_eq_Icc).trans volume_Icc_pi

@[simp]
theorem volume_pi_Ioo_to_real {a b : ι → ℝ} (h : a ≤ b) :
    (volume (pi Univ fun i => Ioo (a i) (b i))).toReal = ∏ i, b i - a i := by
  simp only [← volume_pi_Ioo, ← Ennreal.to_real_prod, ← Ennreal.to_real_of_real (sub_nonneg.2 (h _))]

theorem volume_pi_Ioc {a b : ι → ℝ} : volume (pi Univ fun i => Ioc (a i) (b i)) = ∏ i, Ennreal.ofReal (b i - a i) :=
  (measure_congr Measure.univ_pi_Ioc_ae_eq_Icc).trans volume_Icc_pi

@[simp]
theorem volume_pi_Ioc_to_real {a b : ι → ℝ} (h : a ≤ b) :
    (volume (pi Univ fun i => Ioc (a i) (b i))).toReal = ∏ i, b i - a i := by
  simp only [← volume_pi_Ioc, ← Ennreal.to_real_prod, ← Ennreal.to_real_of_real (sub_nonneg.2 (h _))]

theorem volume_pi_Ico {a b : ι → ℝ} : volume (pi Univ fun i => Ico (a i) (b i)) = ∏ i, Ennreal.ofReal (b i - a i) :=
  (measure_congr Measure.univ_pi_Ico_ae_eq_Icc).trans volume_Icc_pi

@[simp]
theorem volume_pi_Ico_to_real {a b : ι → ℝ} (h : a ≤ b) :
    (volume (pi Univ fun i => Ico (a i) (b i))).toReal = ∏ i, b i - a i := by
  simp only [← volume_pi_Ico, ← Ennreal.to_real_prod, ← Ennreal.to_real_of_real (sub_nonneg.2 (h _))]

@[simp]
theorem volume_pi_ball (a : ι → ℝ) {r : ℝ} (hr : 0 < r) :
    volume (Metric.Ball a r) = Ennreal.ofReal ((2 * r) ^ Fintype.card ι) := by
  simp only [← volume_pi_ball a hr, ← volume_ball, ← Finset.prod_const]
  exact (Ennreal.of_real_pow (mul_nonneg zero_le_two hr.le) _).symm

@[simp]
theorem volume_pi_closed_ball (a : ι → ℝ) {r : ℝ} (hr : 0 ≤ r) :
    volume (Metric.ClosedBall a r) = Ennreal.ofReal ((2 * r) ^ Fintype.card ι) := by
  simp only [← volume_pi_closed_ball a hr, ← volume_closed_ball, ← Finset.prod_const]
  exact (Ennreal.of_real_pow (mul_nonneg zero_le_two hr) _).symm

theorem volume_le_diam (s : Set ℝ) : volume s ≤ Emetric.diam s := by
  by_cases' hs : Metric.Bounded s
  · rw [Real.ediam_eq hs, ← volume_Icc]
    exact volume.mono (Real.subset_Icc_Inf_Sup_of_bounded hs)
    
  · rw [Metric.ediam_of_unbounded hs]
    exact le_top
    

theorem volume_pi_le_prod_diam (s : Set (ι → ℝ)) : volume s ≤ ∏ i : ι, Emetric.diam (Function.eval i '' s) :=
  calc
    volume s ≤ volume (pi Univ fun i => Closure (Function.eval i '' s)) :=
      volume.mono <| Subset.trans (subset_pi_eval_image Univ s) <| pi_mono fun i hi => subset_closure
    _ = ∏ i, volume (Closure <| Function.eval i '' s) := volume_pi_pi _
    _ ≤ ∏ i : ι, Emetric.diam (Function.eval i '' s) :=
      Finset.prod_le_prod' fun i hi => (volume_le_diam _).trans_eq (Emetric.diam_closure _)
    

theorem volume_pi_le_diam_pow (s : Set (ι → ℝ)) : volume s ≤ Emetric.diam s ^ Fintype.card ι :=
  calc
    volume s ≤ ∏ i : ι, Emetric.diam (Function.eval i '' s) := volume_pi_le_prod_diam s
    _ ≤ ∏ i : ι, (1 : ℝ≥0 ) * Emetric.diam s := Finset.prod_le_prod' fun i hi => (LipschitzWith.eval i).ediam_image_le s
    _ = Emetric.diam s ^ Fintype.card ι := by
      simp only [← Ennreal.coe_one, ← one_mulₓ, ← Finset.prod_const, ← Fintype.card]
    

/-!
### Images of the Lebesgue measure under translation/multiplication in ℝ
-/


instance is_add_left_invariant_real_volume : IsAddLeftInvariant (volume : Measureₓ ℝ) :=
  ⟨fun a =>
    Eq.symm <|
      Real.measure_ext_Ioo_rat fun p q => by
        simp [← measure.map_apply (measurable_const_add a) measurable_set_Ioo, ← sub_sub_sub_cancel_right]⟩

theorem smul_map_volume_mul_left {a : ℝ} (h : a ≠ 0) :
    Ennreal.ofReal (abs a) • Measure.map ((· * ·) a) volume = volume := by
  refine' (Real.measure_ext_Ioo_rat fun p q => _).symm
  cases' lt_or_gt_of_neₓ h with h h
  · simp only [← Real.volume_Ioo, ← measure.smul_apply, Ennreal.of_real_mul (le_of_ltₓ <| neg_pos.2 h), ←
      measure.map_apply (measurable_const_mul a) measurable_set_Ioo, ← neg_sub_neg, ← neg_mul, ←
      preimage_const_mul_Ioo_of_neg _ _ h, ← abs_of_neg h, ← mul_sub, ← smul_eq_mul, ← mul_div_cancel' _ (ne_of_ltₓ h)]
    
  · simp only [← Real.volume_Ioo, ← measure.smul_apply, Ennreal.of_real_mul (le_of_ltₓ h), ←
      measure.map_apply (measurable_const_mul a) measurable_set_Ioo, ← preimage_const_mul_Ioo _ _ h, ← abs_of_pos h, ←
      mul_sub, ← mul_div_cancel' _ (ne_of_gtₓ h), ← smul_eq_mul]
    

theorem map_volume_mul_left {a : ℝ} (h : a ≠ 0) : Measure.map ((· * ·) a) volume = Ennreal.ofReal (abs a⁻¹) • volume :=
  by
  conv_rhs =>
    rw [← Real.smul_map_volume_mul_left h, smul_smul, ← Ennreal.of_real_mul (abs_nonneg _), ← abs_mul, inv_mul_cancel h,
      abs_one, Ennreal.of_real_one, one_smul]

@[simp]
theorem volume_preimage_mul_left {a : ℝ} (h : a ≠ 0) (s : Set ℝ) :
    volume ((· * ·) a ⁻¹' s) = Ennreal.ofReal (abs a⁻¹) * volume s :=
  calc
    volume ((· * ·) a ⁻¹' s) = Measure.map ((· * ·) a) volume s :=
      ((Homeomorph.mulLeft₀ a h).toMeasurableEquiv.map_apply s).symm
    _ = Ennreal.ofReal (abs a⁻¹) * volume s := by
      rw [map_volume_mul_left h]
      rfl
    

theorem smul_map_volume_mul_right {a : ℝ} (h : a ≠ 0) : Ennreal.ofReal (abs a) • Measure.map (· * a) volume = volume :=
  by
  simpa only [← mul_comm] using Real.smul_map_volume_mul_left h

theorem map_volume_mul_right {a : ℝ} (h : a ≠ 0) : Measure.map (· * a) volume = Ennreal.ofReal (abs a⁻¹) • volume := by
  simpa only [← mul_comm] using Real.map_volume_mul_left h

@[simp]
theorem volume_preimage_mul_right {a : ℝ} (h : a ≠ 0) (s : Set ℝ) :
    volume ((· * a) ⁻¹' s) = Ennreal.ofReal (abs a⁻¹) * volume s :=
  calc
    volume ((· * a) ⁻¹' s) = Measure.map (· * a) volume s :=
      ((Homeomorph.mulRight₀ a h).toMeasurableEquiv.map_apply s).symm
    _ = Ennreal.ofReal (abs a⁻¹) * volume s := by
      rw [map_volume_mul_right h]
      rfl
    

instance : IsNegInvariant (volume : Measureₓ ℝ) :=
  ⟨Eq.symm <|
      Real.measure_ext_Ioo_rat fun p q => by
        simp [← show volume.neg (Ioo (p : ℝ) q) = _ from measure.map_apply measurable_neg measurable_set_Ioo]⟩

/-!
### Images of the Lebesgue measure under translation/linear maps in ℝⁿ
-/


open Matrix

/-- A diagonal matrix rescales Lebesgue according to its determinant. This is a special case of
`real.map_matrix_volume_pi_eq_smul_volume_pi`, that one should use instead (and whose proof
uses this particular case). -/
theorem smul_map_diagonal_volume_pi [DecidableEq ι] {D : ι → ℝ} (h : det (diagonalₓ D) ≠ 0) :
    Ennreal.ofReal (abs (det (diagonalₓ D))) • Measure.map (diagonalₓ D).toLin' volume = volume := by
  refine' (measure.pi_eq fun s hs => _).symm
  simp only [← det_diagonal, ← measure.coe_smul, ← Algebra.id.smul_eq_mul, ← Pi.smul_apply]
  rw [measure.map_apply _ (MeasurableSet.univ_pi_fintype hs)]
  swap
  · exact Continuous.measurable (LinearMap.continuous_on_pi _)
    
  have :
    (Matrix.toLin' (diagonal D) ⁻¹' Set.Pi Set.Univ fun i : ι => s i) =
      Set.Pi Set.Univ fun i : ι => (· * ·) (D i) ⁻¹' s i :=
    by
    ext f
    simp only [← LinearMap.coe_proj, ← Algebra.id.smul_eq_mul, ← LinearMap.smul_apply, ← mem_univ_pi, ← mem_preimage, ←
      LinearMap.pi_apply, ← diagonal_to_lin']
  have B : ∀ i, of_real (abs (D i)) * volume (Mul.mul (D i) ⁻¹' s i) = volume (s i) := by
    intro i
    have A : D i ≠ 0 := by
      simp only [← det_diagonal, ← Ne.def] at h
      exact Finset.prod_ne_zero_iff.1 h i (Finset.mem_univ i)
    rw [volume_preimage_mul_left A, ← mul_assoc, ← Ennreal.of_real_mul (abs_nonneg _), ← abs_mul, mul_inv_cancel A,
      abs_one, Ennreal.of_real_one, one_mulₓ]
  rw [this, volume_pi_pi, Finset.abs_prod, Ennreal.of_real_prod_of_nonneg fun i hi => abs_nonneg (D i), ←
    Finset.prod_mul_distrib]
  simp only [← B]

/-- A transvection preserves Lebesgue measure. -/
theorem volume_preserving_transvection_struct [DecidableEq ι] (t : TransvectionStruct ι ℝ) :
    MeasurePreserving t.toMatrix.toLin' := by
  /- We separate the coordinate along which there is a shearing from the other ones, and apply
    Fubini. Along this coordinate (and when all the other coordinates are fixed), it acts like a
    translation, and therefore preserves Lebesgue. -/
  let p : ι → Prop := fun i => i ≠ t.i
  let α : Type _ := { x // p x }
  let β : Type _ := { x // ¬p x }
  let g : (α → ℝ) → (β → ℝ) → β → ℝ := fun a b => (fun x => t.c * a ⟨t.j, t.hij.symm⟩) + b
  let F : (α → ℝ) × (β → ℝ) → (α → ℝ) × (β → ℝ) := fun p => (id p.1, g p.1 p.2)
  let e : (ι → ℝ) ≃ᵐ (α → ℝ) × (β → ℝ) := MeasurableEquiv.piEquivPiSubtypeProd (fun i : ι => ℝ) p
  have : (t.to_matrix.to_lin' : (ι → ℝ) → ι → ℝ) = e.symm ∘ F ∘ e := by
    cases t
    ext f k
    simp only [← LinearEquiv.map_smul, ← dite_eq_ite, ← LinearMap.id_coe, ← p, ← ite_not, ← Algebra.id.smul_eq_mul, ←
      one_mulₓ, ← dot_product, ← std_basis_matrix, ← MeasurableEquiv.pi_equiv_pi_subtype_prod_symm_apply, ← id.def, ←
      transvection, ← Pi.add_apply, ← zero_mul, ← LinearMap.smul_apply, ← Function.comp_app, ←
      MeasurableEquiv.pi_equiv_pi_subtype_prod_apply, ← Matrix.TransvectionStruct.to_matrix_mk, ← Matrix.mulVecₓ, ←
      LinearEquiv.map_add, ← ite_mul, ← e, ← Matrix.to_lin'_apply, ← Pi.smul_apply, ← Subtype.coe_mk, ← g, ←
      LinearMap.add_apply, ← Finset.sum_congr, ← Matrix.to_lin'_one]
    by_cases' h : t_i = k
    · simp only [← h, ← true_andₓ, ← Finset.mem_univ, ← if_true, ← eq_self_iff_true, ← Finset.sum_ite_eq, ← one_apply, ←
        boole_mul, ← add_commₓ]
      
    · simp only [← h, ← Ne.symm h, ← add_zeroₓ, ← if_false, ← Finset.sum_const_zero, ← false_andₓ, ← mul_zero]
      
  rw [this]
  have A : measure_preserving e := by
    convert volume_preserving_pi_equiv_pi_subtype_prod (fun i : ι => ℝ) p
  have B : measure_preserving F := by
    have g_meas : Measurable (Function.uncurry g) := by
      have : Measurable fun c : α → ℝ => c ⟨t.j, t.hij.symm⟩ := measurable_pi_apply ⟨t.j, t.hij.symm⟩
      refine' (measurable_pi_lambda _ fun i => Measurable.const_mul _ _).add measurable_snd
      exact this.comp measurable_fst
    exact (measure_preserving.id _).skew_product g_meas (eventually_of_forall fun a => map_add_left_eq_self _ _)
  exact ((A.symm e).comp B).comp A

/-- Any invertible matrix rescales Lebesgue measure through the absolute value of its
determinant. -/
theorem map_matrix_volume_pi_eq_smul_volume_pi [DecidableEq ι] {M : Matrix ι ι ℝ} (hM : det M ≠ 0) :
    Measure.map M.toLin' volume = Ennreal.ofReal (abs (det M)⁻¹) • volume := by
  -- This follows from the cases we have already proved, of diagonal matrices and transvections,
  -- as these matrices generate all invertible matrices.
  apply diagonal_transvection_induction_of_det_ne_zero _ M hM (fun D hD => _) (fun t => _) fun A B hA hB IHA IHB => _
  · conv_rhs => rw [← smul_map_diagonal_volume_pi hD]
    rw [smul_smul, ← Ennreal.of_real_mul (abs_nonneg _), ← abs_mul, inv_mul_cancel hD, abs_one, Ennreal.of_real_one,
      one_smul]
    
  · simp only [← Matrix.TransvectionStruct.det, ← Ennreal.of_real_one, ←
      (volume_preserving_transvection_struct _).map_eq, ← one_smul, ← _root_.inv_one, ← abs_one]
    
  · rw [to_lin'_mul, det_mul, LinearMap.coe_comp, ← measure.map_map, IHB, measure.map_smul, IHA, smul_smul, ←
      Ennreal.of_real_mul (abs_nonneg _), ← abs_mul, mul_comm, mul_inv]
    · apply Continuous.measurable
      apply LinearMap.continuous_on_pi
      
    · apply Continuous.measurable
      apply LinearMap.continuous_on_pi
      
    

/-- Any invertible linear map rescales Lebesgue measure through the absolute value of its
determinant. -/
theorem map_linear_map_volume_pi_eq_smul_volume_pi {f : (ι → ℝ) →ₗ[ℝ] ι → ℝ} (hf : f.det ≠ 0) :
    Measure.map f volume = Ennreal.ofReal (abs f.det⁻¹) • volume := by
  -- this is deduced from the matrix case
  classical
  let M := f.to_matrix'
  have A : f.det = det M := by
    simp only [← LinearMap.det_to_matrix']
  have B : f = M.to_lin' := by
    simp only [← to_lin'_to_matrix']
  rw [A, B]
  apply map_matrix_volume_pi_eq_smul_volume_pi
  rwa [A] at hf

end Real

open TopologicalSpace

theorem Filter.Eventually.volume_pos_of_nhds_real {p : ℝ → Prop} {a : ℝ} (h : ∀ᶠ x in 𝓝 a, p x) :
    (0 : ℝ≥0∞) < volume { x | p x } := by
  rcases h.exists_Ioo_subset with ⟨l, u, hx, hs⟩
  refine' lt_of_lt_of_leₓ _ (measure_mono hs)
  simpa [-mem_Ioo] using hx.1.trans hx.2

section RegionBetween

open Classical

variable {α : Type _}

/-- The region between two real-valued functions on an arbitrary set. -/
def RegionBetween (f g : α → ℝ) (s : Set α) : Set (α × ℝ) :=
  { p : α × ℝ | p.1 ∈ s ∧ p.2 ∈ Ioo (f p.1) (g p.1) }

theorem region_between_subset (f g : α → ℝ) (s : Set α) : RegionBetween f g s ⊆ s ×ˢ (Univ : Set ℝ) := by
  simpa only [← prod_univ, ← RegionBetween, ← Set.Preimage, ← set_of_subset_set_of] using fun a => And.left

variable [MeasurableSpace α] {μ : Measureₓ α} {f g : α → ℝ} {s : Set α}

/-- The region between two measurable functions on a measurable set is measurable. -/
theorem measurable_set_region_between (hf : Measurable f) (hg : Measurable g) (hs : MeasurableSet s) :
    MeasurableSet (RegionBetween f g s) := by
  dsimp' only [← RegionBetween, ← Ioo, ← mem_set_of_eq, ← set_of_and]
  refine'
    MeasurableSet.inter _
      ((measurable_set_lt (hf.comp measurable_fst) measurable_snd).inter
        (measurable_set_lt measurable_snd (hg.comp measurable_fst)))
  exact measurable_fst hs

/-- The region between two measurable functions on a measurable set is measurable;
a version for the region together with the graph of the upper function. -/
theorem measurable_set_region_between_oc (hf : Measurable f) (hg : Measurable g) (hs : MeasurableSet s) :
    MeasurableSet { p : α × ℝ | p.fst ∈ s ∧ p.snd ∈ Ioc (f p.fst) (g p.fst) } := by
  dsimp' only [← RegionBetween, ← Ioc, ← mem_set_of_eq, ← set_of_and]
  refine'
    MeasurableSet.inter _
      ((measurable_set_lt (hf.comp measurable_fst) measurable_snd).inter
        (measurable_set_le measurable_snd (hg.comp measurable_fst)))
  exact measurable_fst hs

/-- The region between two measurable functions on a measurable set is measurable;
a version for the region together with the graph of the lower function. -/
theorem measurable_set_region_between_co (hf : Measurable f) (hg : Measurable g) (hs : MeasurableSet s) :
    MeasurableSet { p : α × ℝ | p.fst ∈ s ∧ p.snd ∈ Ico (f p.fst) (g p.fst) } := by
  dsimp' only [← RegionBetween, ← Ico, ← mem_set_of_eq, ← set_of_and]
  refine'
    MeasurableSet.inter _
      ((measurable_set_le (hf.comp measurable_fst) measurable_snd).inter
        (measurable_set_lt measurable_snd (hg.comp measurable_fst)))
  exact measurable_fst hs

/-- The region between two measurable functions on a measurable set is measurable;
a version for the region together with the graphs of both functions. -/
theorem measurable_set_region_between_cc (hf : Measurable f) (hg : Measurable g) (hs : MeasurableSet s) :
    MeasurableSet { p : α × ℝ | p.fst ∈ s ∧ p.snd ∈ Icc (f p.fst) (g p.fst) } := by
  dsimp' only [← RegionBetween, ← Icc, ← mem_set_of_eq, ← set_of_and]
  refine'
    MeasurableSet.inter _
      ((measurable_set_le (hf.comp measurable_fst) measurable_snd).inter
        (measurable_set_le measurable_snd (hg.comp measurable_fst)))
  exact measurable_fst hs

/-- The graph of a measurable function is a measurable set. -/
theorem measurable_set_graph (hf : Measurable f) : MeasurableSet { p : α × ℝ | p.snd = f p.fst } := by
  simpa using measurable_set_region_between_cc hf hf MeasurableSet.univ

theorem volume_region_between_eq_lintegral' (hf : Measurable f) (hg : Measurable g) (hs : MeasurableSet s) :
    μ.Prod volume (RegionBetween f g s) = ∫⁻ y in s, Ennreal.ofReal ((g - f) y) ∂μ := by
  rw [measure.prod_apply]
  · have h : (fun x => volume { a | x ∈ s ∧ a ∈ Ioo (f x) (g x) }) = s.indicator fun x => Ennreal.ofReal (g x - f x) :=
      by
      funext x
      rw [indicator_apply]
      split_ifs
      · have hx : { a | x ∈ s ∧ a ∈ Ioo (f x) (g x) } = Ioo (f x) (g x) := by
          simp [← h, ← Ioo]
        simp only [← hx, ← Real.volume_Ioo, ← sub_zero]
        
      · have hx : { a | x ∈ s ∧ a ∈ Ioo (f x) (g x) } = ∅ := by
          simp [← h]
        simp only [← hx, ← measure_empty]
        
    dsimp' only [← RegionBetween, ← preimage_set_of_eq]
    rw [h, lintegral_indicator] <;> simp only [← hs, ← Pi.sub_apply]
    
  · exact measurable_set_region_between hf hg hs
    

/-- The volume of the region between two almost everywhere measurable functions on a measurable set
    can be represented as a Lebesgue integral. -/
theorem volume_region_between_eq_lintegral [SigmaFinite μ] (hf : AeMeasurable f (μ.restrict s))
    (hg : AeMeasurable g (μ.restrict s)) (hs : MeasurableSet s) :
    μ.Prod volume (RegionBetween f g s) = ∫⁻ y in s, Ennreal.ofReal ((g - f) y) ∂μ := by
  have h₁ :
    (fun y => Ennreal.ofReal ((g - f) y)) =ᵐ[μ.restrict s] fun y =>
      Ennreal.ofReal ((AeMeasurable.mk g hg - AeMeasurable.mk f hf) y) :=
    (hg.ae_eq_mk.sub hf.ae_eq_mk).fun_comp _
  have h₂ :
    (μ.restrict s).Prod volume (RegionBetween f g s) =
      (μ.restrict s).Prod volume (RegionBetween (AeMeasurable.mk f hf) (AeMeasurable.mk g hg) s) :=
    by
    apply measure_congr
    apply eventually_eq.rfl.inter
    exact
      ((ae_eq_comp' measurable_fst.ae_measurable hf.ae_eq_mk measure.prod_fst_absolutely_continuous).comp₂ _
            eventually_eq.rfl).inter
        (eventually_eq.rfl.comp₂ _
          (ae_eq_comp' measurable_fst.ae_measurable hg.ae_eq_mk measure.prod_fst_absolutely_continuous))
  rw [lintegral_congr_ae h₁, ← volume_region_between_eq_lintegral' hf.measurable_mk hg.measurable_mk hs]
  convert h₂ using 1
  · rw [measure.restrict_prod_eq_prod_univ]
    exact (measure.restrict_eq_self _ (region_between_subset f g s)).symm
    
  · rw [measure.restrict_prod_eq_prod_univ]
    exact (measure.restrict_eq_self _ (region_between_subset (AeMeasurable.mk f hf) (AeMeasurable.mk g hg) s)).symm
    

theorem volume_region_between_eq_integral' [SigmaFinite μ] (f_int : IntegrableOn f s μ) (g_int : IntegrableOn g s μ)
    (hs : MeasurableSet s) (hfg : f ≤ᵐ[μ.restrict s] g) :
    μ.Prod volume (RegionBetween f g s) = Ennreal.ofReal (∫ y in s, (g - f) y ∂μ) := by
  have h : g - f =ᵐ[μ.restrict s] fun x => Real.toNnreal (g x - f x) :=
    hfg.mono fun x hx => (Real.coe_to_nnreal _ <| sub_nonneg.2 hx).symm
  rw [volume_region_between_eq_lintegral f_int.ae_measurable g_int.ae_measurable hs, integral_congr_ae h,
    lintegral_congr_ae, lintegral_coe_eq_integral _ ((integrable_congr h).mp (g_int.sub f_int))]
  simpa only

/-- If two functions are integrable on a measurable set, and one function is less than
    or equal to the other on that set, then the volume of the region
    between the two functions can be represented as an integral. -/
theorem volume_region_between_eq_integral [SigmaFinite μ] (f_int : IntegrableOn f s μ) (g_int : IntegrableOn g s μ)
    (hs : MeasurableSet s) (hfg : ∀, ∀ x ∈ s, ∀, f x ≤ g x) :
    μ.Prod volume (RegionBetween f g s) = Ennreal.ofReal (∫ y in s, (g - f) y ∂μ) :=
  volume_region_between_eq_integral' f_int g_int hs ((ae_restrict_iff' hs).mpr (eventually_of_forall hfg))

end RegionBetween

