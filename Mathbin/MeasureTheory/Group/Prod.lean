/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import Mathbin.MeasureTheory.Constructions.Prod
import Mathbin.MeasureTheory.Group.Measure

/-!
# Measure theory in the product of groups
In this file we show properties about measure theory in products of measurable groups
and properties of iterated integrals in measurable groups.

These lemmas show the uniqueness of left invariant measures on measurable groups, up to
scaling. In this file we follow the proof and refer to the book *Measure Theory* by Paul Halmos.

The idea of the proof is to use the translation invariance of measures to prove `μ(F) = c * μ(E)`
for two sets `E` and `F`, where `c` is a constant that does not depend on `μ`. Let `e` and `f` be
the characteristic functions of `E` and `F`.
Assume that `μ` and `ν` are left-invariant measures. Then the map `(x, y) ↦ (y * x, x⁻¹)`
preserves the measure `μ.prod ν`, which means that
```
  ∫ x, ∫ y, h x y ∂ν ∂μ = ∫ x, ∫ y, h (y * x) x⁻¹ ∂ν ∂μ
```
If we apply this to `h x y := e x * f y⁻¹ / ν ((λ h, h * y⁻¹) ⁻¹' E)`, we can rewrite the RHS to
`μ(F)`, and the LHS to `c * μ(E)`, where `c = c(ν)` does not depend on `μ`.
Applying this to `μ` and to `ν` gives `μ (F) / μ (E) = ν (F) / ν (E)`, which is the uniqueness up to
scalar multiplication.

The proof in [Halmos] seems to contain an omission in §60 Th. A, see
`measure_theory.measure_lintegral_div_measure`.

-/


noncomputable section

open Set hiding prod_eq

open Function MeasureTheory

open Filter hiding map

open Classical Ennreal Pointwise MeasureTheory

variable (G : Type _) [MeasurableSpace G]

variable [Groupₓ G] [HasMeasurableMul₂ G]

variable (μ ν : Measureₓ G) [SigmaFinite ν] [SigmaFinite μ] {E : Set G}

/-- The map `(x, y) ↦ (x, xy)` as a `measurable_equiv`. This is a shear mapping. -/
@[to_additive "The map `(x, y) ↦ (x, x + y)` as a `measurable_equiv`.\nThis is a shear mapping."]
protected def MeasurableEquiv.shearMulRight [HasMeasurableInv G] : G × G ≃ᵐ G × G :=
  { Equivₓ.prodShear (Equivₓ.refl _) Equivₓ.mulLeft with measurable_to_fun := measurable_fst.prod_mk measurable_mul,
    measurable_inv_fun := measurable_fst.prod_mk <| measurable_fst.inv.mul measurable_snd }

variable {G}

namespace MeasureTheory

open Measureₓ

/-- A shear mapping preserves the measure `μ.prod ν`.
This condition is part of the definition of a measurable group in [Halmos, §59].
There, the map in this lemma is called `S`. -/
@[to_additive map_prod_sum_eq " An additive shear mapping preserves the measure `μ.prod ν`. "]
theorem map_prod_mul_eq [IsMulLeftInvariant ν] : map (fun z : G × G => (z.1, z.1 * z.2)) (μ.Prod ν) = μ.Prod ν :=
  ((MeasurePreserving.id μ).skew_product measurable_mul (Filter.eventually_of_forall <| map_mul_left_eq_self ν)).map_eq

/-- The function we are mapping along is `SR` in [Halmos, §59],
  where `S` is the map in `map_prod_mul_eq` and `R` is `prod.swap`. -/
@[to_additive map_prod_add_eq_swap "  "]
theorem map_prod_mul_eq_swap [IsMulLeftInvariant μ] : map (fun z : G × G => (z.2, z.2 * z.1)) (μ.Prod ν) = ν.Prod μ :=
  by
  rw [← prod_swap]
  simp_rw [map_map (measurable_snd.prod_mk (measurable_snd.mul measurable_fst)) measurable_swap]
  exact map_prod_mul_eq ν μ

@[to_additive]
theorem measurable_measure_mul_right (hE : MeasurableSet E) : Measurable fun x => μ ((fun y => y * x) ⁻¹' E) := by
  suffices
    Measurable fun y => μ ((fun x => (x, y)) ⁻¹' ((fun z : G × G => ((1 : G), z.1 * z.2)) ⁻¹' (univ : Set G) ×ˢ E)) by
    convert this
    ext1 x
    congr 1 with y : 1
    simp
  apply measurable_measure_prod_mk_right
  exact measurable_const.prod_mk (measurable_fst.mul measurable_snd) (measurable_set.univ.prod hE)

variable [HasMeasurableInv G]

/-- The function we are mapping along is `S⁻¹` in [Halmos, §59],
  where `S` is the map in `map_prod_mul_eq`. -/
@[to_additive map_prod_neg_add_eq]
theorem map_prod_inv_mul_eq [IsMulLeftInvariant ν] : map (fun z : G × G => (z.1, z.1⁻¹ * z.2)) (μ.Prod ν) = μ.Prod ν :=
  (MeasurableEquiv.shearMulRight G).map_apply_eq_iff_map_symm_apply_eq.mp <| map_prod_mul_eq μ ν

@[to_additive]
theorem quasi_measure_preserving_div [IsMulRightInvariant μ] :
    QuasiMeasurePreserving (fun p : G × G => p.1 / p.2) (μ.Prod μ) μ := by
  refine' quasi_measure_preserving.prod_of_left measurable_div _
  simp_rw [div_eq_mul_inv]
  apply eventually_of_forall
  refine' fun y => ⟨measurable_mul_const y⁻¹, (map_mul_right_eq_self μ y⁻¹).AbsolutelyContinuous⟩

variable [IsMulLeftInvariant μ]

/-- The function we are mapping along is `S⁻¹R` in [Halmos, §59],
  where `S` is the map in `map_prod_mul_eq` and `R` is `prod.swap`. -/
@[to_additive map_prod_neg_add_eq_swap]
theorem map_prod_inv_mul_eq_swap : map (fun z : G × G => (z.2, z.2⁻¹ * z.1)) (μ.Prod ν) = ν.Prod μ := by
  rw [← prod_swap]
  simp_rw [map_map (measurable_snd.prod_mk <| measurable_snd.inv.mul measurable_fst) measurable_swap]
  exact map_prod_inv_mul_eq ν μ

/-- The function we are mapping along is `S⁻¹RSR` in [Halmos, §59],
  where `S` is the map in `map_prod_mul_eq` and `R` is `prod.swap`. -/
@[to_additive map_prod_add_neg_eq]
theorem map_prod_mul_inv_eq [IsMulLeftInvariant ν] : map (fun z : G × G => (z.2 * z.1, z.1⁻¹)) (μ.Prod ν) = μ.Prod ν :=
  by
  suffices map ((fun z : G × G => (z.2, z.2⁻¹ * z.1)) ∘ fun z : G × G => (z.2, z.2 * z.1)) (μ.prod ν) = μ.prod ν by
    convert this
    ext1 ⟨x, y⟩
    simp
  simp_rw [←
    map_map (measurable_snd.prod_mk (measurable_snd.inv.mul measurable_fst))
      (measurable_snd.prod_mk (measurable_snd.mul measurable_fst)),
    map_prod_mul_eq_swap μ ν, map_prod_inv_mul_eq_swap ν μ]

@[to_additive]
theorem quasi_measure_preserving_inv : QuasiMeasurePreserving (Inv.inv : G → G) μ μ := by
  refine' ⟨measurable_inv, absolutely_continuous.mk fun s hsm hμs => _⟩
  rw [map_apply measurable_inv hsm, inv_preimage]
  have hf : Measurable fun z : G × G => (z.2 * z.1, z.1⁻¹) :=
    (measurable_snd.mul measurable_fst).prod_mk measurable_fst.inv
  suffices map (fun z : G × G => (z.2 * z.1, z.1⁻¹)) (μ.prod μ) (s⁻¹ ×ˢ s⁻¹) = 0 by
    simpa only [← map_prod_mul_inv_eq μ μ, ← prod_prod, ← mul_eq_zero, ← or_selfₓ] using this
  have hsm' : MeasurableSet (s⁻¹ ×ˢ s⁻¹) := hsm.inv.prod hsm.inv
  simp_rw [map_apply hf hsm', prod_apply_symm (hf hsm'), preimage_preimage, mk_preimage_prod, inv_preimage, inv_invₓ,
    measure_mono_null (inter_subset_right _ _) hμs, lintegral_zero]

@[to_additive]
theorem map_inv_absolutely_continuous : map Inv.inv μ ≪ μ :=
  (quasi_measure_preserving_inv μ).AbsolutelyContinuous

@[to_additive]
theorem measure_inv_null : μ E⁻¹ = 0 ↔ μ E = 0 := by
  refine' ⟨fun hE => _, (quasi_measure_preserving_inv μ).preimage_null⟩
  convert (quasi_measure_preserving_inv μ).preimage_null hE
  exact (inv_invₓ _).symm

@[to_additive]
theorem absolutely_continuous_map_inv : μ ≪ map Inv.inv μ := by
  refine' absolutely_continuous.mk fun s hs => _
  simp_rw [map_apply measurable_inv hs, inv_preimage, measure_inv_null, imp_self]

@[to_additive]
theorem lintegral_lintegral_mul_inv [IsMulLeftInvariant ν] (f : G → G → ℝ≥0∞)
    (hf : AeMeasurable (uncurry f) (μ.Prod ν)) : (∫⁻ x, ∫⁻ y, f (y * x) x⁻¹ ∂ν ∂μ) = ∫⁻ x, ∫⁻ y, f x y ∂ν ∂μ := by
  have h : Measurable fun z : G × G => (z.2 * z.1, z.1⁻¹) :=
    (measurable_snd.mul measurable_fst).prod_mk measurable_fst.inv
  have h2f : AeMeasurable (uncurry fun x y => f (y * x) x⁻¹) (μ.prod ν) := by
    apply hf.comp_measurable' h (map_prod_mul_inv_eq μ ν).AbsolutelyContinuous
  simp_rw [lintegral_lintegral h2f, lintegral_lintegral hf]
  conv_rhs => rw [← map_prod_mul_inv_eq μ ν]
  symm
  exact lintegral_map' (hf.mono' (map_prod_mul_inv_eq μ ν).AbsolutelyContinuous) h.ae_measurable

@[to_additive]
theorem measure_mul_right_null (y : G) : μ ((fun x => x * y) ⁻¹' E) = 0 ↔ μ E = 0 :=
  calc
    μ ((fun x => x * y) ⁻¹' E) = 0 ↔ μ ((fun x => y⁻¹ * x) ⁻¹' E⁻¹)⁻¹ = 0 := by
      simp_rw [← inv_preimage, preimage_preimage, mul_inv_rev, inv_invₓ]
    _ ↔ μ E = 0 := by
      simp only [← measure_inv_null μ, ← measure_preimage_mul]
    

@[to_additive]
theorem measure_mul_right_ne_zero (h2E : μ E ≠ 0) (y : G) : μ ((fun x => x * y) ⁻¹' E) ≠ 0 :=
  (not_iff_not_of_iff (measure_mul_right_null μ y)).mpr h2E

@[to_additive]
theorem quasi_measure_preserving_mul_right (g : G) : QuasiMeasurePreserving (fun h : G => h * g) μ μ := by
  refine' ⟨measurable_mul_const g, absolutely_continuous.mk fun s hs => _⟩
  rw [map_apply (measurable_mul_const g) hs, measure_mul_right_null]
  exact id

@[to_additive]
theorem map_mul_right_absolutely_continuous (g : G) : map (· * g) μ ≪ μ :=
  (quasi_measure_preserving_mul_right μ g).AbsolutelyContinuous

@[to_additive]
theorem absolutely_continuous_map_mul_right (g : G) : μ ≪ map (· * g) μ := by
  refine' absolutely_continuous.mk fun s hs => _
  rw [map_apply (measurable_mul_const g) hs, measure_mul_right_null]
  exact id

@[to_additive]
theorem quasi_measure_preserving_div_left (g : G) : QuasiMeasurePreserving (fun h : G => g / h) μ μ := by
  refine' ⟨measurable_const.div measurable_id, _⟩
  simp_rw [div_eq_mul_inv]
  rw [← map_map (measurable_const_mul g) measurable_inv]
  refine' ((map_inv_absolutely_continuous μ).map <| measurable_const_mul g).trans _
  rw [map_mul_left_eq_self]

@[to_additive]
theorem map_div_left_absolutely_continuous (g : G) : map (fun h => g / h) μ ≪ μ :=
  (quasi_measure_preserving_div_left μ g).AbsolutelyContinuous

@[to_additive]
theorem absolutely_continuous_map_div_left (g : G) : μ ≪ map (fun h => g / h) μ := by
  simp_rw [div_eq_mul_inv]
  rw [← map_map (measurable_const_mul g) measurable_inv]
  conv_lhs => rw [← map_mul_left_eq_self μ g]
  exact (absolutely_continuous_map_inv μ).map (measurable_const_mul g)

/-- This is the computation performed in the proof of [Halmos, §60 Th. A]. -/
@[to_additive]
theorem measure_mul_lintegral_eq [IsMulLeftInvariant ν] (Em : MeasurableSet E) (f : G → ℝ≥0∞) (hf : Measurable f) :
    (μ E * ∫⁻ y, f y ∂ν) = ∫⁻ x, ν ((fun z => z * x) ⁻¹' E) * f x⁻¹ ∂μ := by
  rw [← set_lintegral_one, ← lintegral_indicator _ Em, ←
    lintegral_lintegral_mul (measurable_const.indicator Em).AeMeasurable hf.ae_measurable, ←
    lintegral_lintegral_mul_inv μ ν]
  swap
  · exact (((measurable_const.indicator Em).comp measurable_fst).mul (hf.comp measurable_snd)).AeMeasurable
    
  have mE : ∀ x : G, Measurable fun y => ((fun z => z * x) ⁻¹' E).indicator (fun z => (1 : ℝ≥0∞)) y := fun x =>
    measurable_const.indicator (measurable_mul_const _ Em)
  have : ∀ x y, E.indicator (fun z : G => (1 : ℝ≥0∞)) (y * x) = ((fun z => z * x) ⁻¹' E).indicator (fun b : G => 1) y :=
    by
    intro x y
    symm
    convert indicator_comp_right fun y => y * x
    ext1 z
    rfl
  simp_rw [this, lintegral_mul_const _ (mE _), lintegral_indicator _ (measurable_mul_const _ Em), set_lintegral_one]

/-- Any two nonzero left-invariant measures are absolutely continuous w.r.t. each other. -/
@[to_additive " Any two nonzero left-invariant measures are absolutely continuous w.r.t. each\nother. "]
theorem absolutely_continuous_of_is_mul_left_invariant [IsMulLeftInvariant ν] (hν : ν ≠ 0) : μ ≪ ν := by
  refine' absolutely_continuous.mk fun E Em hνE => _
  have h1 := measure_mul_lintegral_eq μ ν Em 1 measurable_one
  simp_rw [Pi.one_apply, lintegral_one, mul_oneₓ, (measure_mul_right_null ν _).mpr hνE, lintegral_zero, mul_eq_zero,
    measure_univ_eq_zero.not.mpr hν, or_falseₓ] at h1
  exact h1

@[to_additive]
theorem ae_measure_preimage_mul_right_lt_top [IsMulLeftInvariant ν] (Em : MeasurableSet E) (hμE : μ E ≠ ∞) :
    ∀ᵐ x ∂μ, ν ((fun y => y * x) ⁻¹' E) < ∞ := by
  refine' ae_of_forall_measure_lt_top_ae_restrict' ν.inv _ _
  intro A hA h2A h3A
  simp only [← ν.inv_apply] at h3A
  apply ae_lt_top (measurable_measure_mul_right ν Em)
  have h1 := measure_mul_lintegral_eq μ ν Em (A⁻¹.indicator 1) (measurable_one.indicator hA.inv)
  rw [lintegral_indicator _ hA.inv] at h1
  simp_rw [Pi.one_apply, set_lintegral_one, ← image_inv, indicator_image inv_injective, image_inv, ←
    indicator_mul_right _ fun x => ν ((fun y => y * x) ⁻¹' E), Function.comp, Pi.one_apply, mul_oneₓ] at h1
  rw [← lintegral_indicator _ hA, ← h1]
  exact Ennreal.mul_ne_top hμE h3A.ne

@[to_additive]
theorem ae_measure_preimage_mul_right_lt_top_of_ne_zero [IsMulLeftInvariant ν] (Em : MeasurableSet E) (h2E : ν E ≠ 0)
    (h3E : ν E ≠ ∞) : ∀ᵐ x ∂μ, ν ((fun y => y * x) ⁻¹' E) < ∞ := by
  refine' (ae_measure_preimage_mul_right_lt_top ν ν Em h3E).filter_mono _
  refine' (absolutely_continuous_of_is_mul_left_invariant μ ν _).ae_le
  refine' mt _ h2E
  intro hν
  rw [hν, measure.coe_zero, Pi.zero_apply]

/-- A technical lemma relating two different measures. This is basically [Halmos, §60 Th. A].
  Note that if `f` is the characteristic function of a measurable set `F` this states that
  `μ F = c * μ E` for a constant `c` that does not depend on `μ`.

  Note: There is a gap in the last step of the proof in [Halmos].
  In the last line, the equality `g(x⁻¹)ν(Ex⁻¹) = f(x)` holds if we can prove that
  `0 < ν(Ex⁻¹) < ∞`. The first inequality follows from §59, Th. D, but the second inequality is
  not justified. We prove this inequality for almost all `x` in
  `measure_theory.ae_measure_preimage_mul_right_lt_top_of_ne_zero`. -/
@[to_additive]
theorem measure_lintegral_div_measure [IsMulLeftInvariant ν] (Em : MeasurableSet E) (h2E : ν E ≠ 0) (h3E : ν E ≠ ∞)
    (f : G → ℝ≥0∞) (hf : Measurable f) : (μ E * ∫⁻ y, f y⁻¹ / ν ((fun x => x * y⁻¹) ⁻¹' E) ∂ν) = ∫⁻ x, f x ∂μ := by
  set g := fun y => f y⁻¹ / ν ((fun x => x * y⁻¹) ⁻¹' E)
  have hg : Measurable g := (hf.comp measurable_inv).div ((measurable_measure_mul_right ν Em).comp measurable_inv)
  simp_rw [measure_mul_lintegral_eq μ ν Em g hg, g, inv_invₓ]
  refine' lintegral_congr_ae _
  refine' (ae_measure_preimage_mul_right_lt_top_of_ne_zero μ ν Em h2E h3E).mono fun x hx => _
  simp_rw [Ennreal.mul_div_cancel' (measure_mul_right_ne_zero ν h2E _) hx.ne]

@[to_additive]
theorem measure_mul_measure_eq [IsMulLeftInvariant ν] {E F : Set G} (hE : MeasurableSet E) (hF : MeasurableSet F)
    (h2E : ν E ≠ 0) (h3E : ν E ≠ ∞) : μ E * ν F = ν E * μ F := by
  have h1 := measure_lintegral_div_measure ν ν hE h2E h3E (F.indicator fun x => 1) (measurable_const.indicator hF)
  have h2 := measure_lintegral_div_measure μ ν hE h2E h3E (F.indicator fun x => 1) (measurable_const.indicator hF)
  rw [lintegral_indicator _ hF, set_lintegral_one] at h1 h2
  rw [← h1, mul_left_commₓ, h2]

/-- Left invariant Borel measures on a measurable group are unique (up to a scalar). -/
@[to_additive " Left invariant Borel measures on an additive measurable group are unique\n  (up to a scalar). "]
theorem measure_eq_div_smul [IsMulLeftInvariant ν] (hE : MeasurableSet E) (h2E : ν E ≠ 0) (h3E : ν E ≠ ∞) :
    μ = (μ E / ν E) • ν := by
  ext1 F hF
  rw [smul_apply, smul_eq_mul, mul_comm, ← mul_div_assoc, mul_comm, measure_mul_measure_eq μ ν hE hF h2E h3E,
    mul_div_assoc, Ennreal.mul_div_cancel' h2E h3E]

end MeasureTheory

