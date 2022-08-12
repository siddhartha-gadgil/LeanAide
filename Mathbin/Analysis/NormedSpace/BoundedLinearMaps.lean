/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl
-/
import Mathbin.Analysis.NormedSpace.Multilinear
import Mathbin.Analysis.NormedSpace.Units
import Mathbin.Analysis.Asymptotics.Asymptotics

/-!
# Bounded linear maps

This file defines a class stating that a map between normed vector spaces is (bi)linear and
continuous.
Instead of asking for continuity, the definition takes the equivalent condition (because the space
is normed) that `∥f x∥` is bounded by a multiple of `∥x∥`. Hence the "bounded" in the name refers to
`∥f x∥/∥x∥` rather than `∥f x∥` itself.

## Main definitions

* `is_bounded_linear_map`: Class stating that a map `f : E → F` is linear and has `∥f x∥` bounded
  by a multiple of `∥x∥`.
* `is_bounded_bilinear_map`: Class stating that a map `f : E × F → G` is bilinear and continuous,
  but through the simpler to provide statement that `∥f (x, y)∥` is bounded by a multiple of
  `∥x∥ * ∥y∥`
* `is_bounded_bilinear_map.linear_deriv`: Derivative of a continuous bilinear map as a linear map.
* `is_bounded_bilinear_map.deriv`: Derivative of a continuous bilinear map as a continuous linear
  map. The proof that it is indeed the derivative is `is_bounded_bilinear_map.has_fderiv_at` in
  `analysis.calculus.fderiv`.

## Main theorems

* `is_bounded_bilinear_map.continuous`: A bounded bilinear map is continuous.
* `continuous_linear_equiv.is_open`: The continuous linear equivalences are an open subset of the
  set of continuous linear maps between a pair of Banach spaces.  Placed in this file because its
  proof uses `is_bounded_bilinear_map.continuous`.

## Notes

The main use of this file is `is_bounded_bilinear_map`. The file `analysis.normed_space.multilinear`
already expounds the theory of multilinear maps, but the `2`-variables case is sufficiently simpler
to currently deserve its own treatment.

`is_bounded_linear_map` is effectively an unbundled version of `continuous_linear_map` (defined
in `topology.algebra.module.basic`, theory over normed spaces developed in
`analysis.normed_space.operator_norm`), albeit the name disparity. A bundled
`continuous_linear_map` is to be preferred over a `is_bounded_linear_map` hypothesis. Historical
artifact, really.
-/


noncomputable section

open Classical BigOperators TopologicalSpace

open Filter (Tendsto)

open Metric ContinuousLinearMap

variable {𝕜 : Type _} [NondiscreteNormedField 𝕜] {E : Type _} [NormedGroup E] [NormedSpace 𝕜 E] {F : Type _}
  [NormedGroup F] [NormedSpace 𝕜 F] {G : Type _} [NormedGroup G] [NormedSpace 𝕜 G]

/-- A function `f` satisfies `is_bounded_linear_map 𝕜 f` if it is linear and satisfies the
inequality `∥f x∥ ≤ M * ∥x∥` for some positive constant `M`. -/
structure IsBoundedLinearMap (𝕜 : Type _) [NormedField 𝕜] {E : Type _} [NormedGroup E] [NormedSpace 𝕜 E] {F : Type _}
  [NormedGroup F] [NormedSpace 𝕜 F] (f : E → F) extends IsLinearMap 𝕜 f : Prop where
  bound : ∃ M, 0 < M ∧ ∀ x : E, ∥f x∥ ≤ M * ∥x∥

theorem IsLinearMap.with_bound {f : E → F} (hf : IsLinearMap 𝕜 f) (M : ℝ) (h : ∀ x : E, ∥f x∥ ≤ M * ∥x∥) :
    IsBoundedLinearMap 𝕜 f :=
  ⟨hf,
    Classical.by_cases
      (fun this : M ≤ 0 =>
        ⟨1, zero_lt_one, fun x => (h x).trans <| mul_le_mul_of_nonneg_right (this.trans zero_le_one) (norm_nonneg x)⟩)
      fun this : ¬M ≤ 0 => ⟨M, lt_of_not_geₓ this, h⟩⟩

/-- A continuous linear map satisfies `is_bounded_linear_map` -/
theorem ContinuousLinearMap.is_bounded_linear_map (f : E →L[𝕜] F) : IsBoundedLinearMap 𝕜 f :=
  { f.toLinearMap.is_linear with bound := f.bound }

namespace IsBoundedLinearMap

/-- Construct a linear map from a function `f` satisfying `is_bounded_linear_map 𝕜 f`. -/
def toLinearMap (f : E → F) (h : IsBoundedLinearMap 𝕜 f) : E →ₗ[𝕜] F :=
  IsLinearMap.mk' _ h.to_is_linear_map

/-- Construct a continuous linear map from is_bounded_linear_map -/
def toContinuousLinearMap {f : E → F} (hf : IsBoundedLinearMap 𝕜 f) : E →L[𝕜] F :=
  { toLinearMap f hf with
    cont :=
      let ⟨C, Cpos, hC⟩ := hf.bound
      AddMonoidHomClass.continuous_of_bound (toLinearMap f hf) C hC }

theorem zero : IsBoundedLinearMap 𝕜 fun x : E => (0 : F) :=
  (0 : E →ₗ[𝕜] F).is_linear.with_bound 0 <| by
    simp [← le_reflₓ]

theorem id : IsBoundedLinearMap 𝕜 fun x : E => x :=
  LinearMap.id.is_linear.with_bound 1 <| by
    simp [← le_reflₓ]

theorem fst : IsBoundedLinearMap 𝕜 fun x : E × F => x.1 := by
  refine' (LinearMap.fst 𝕜 E F).is_linear.with_bound 1 fun x => _
  rw [one_mulₓ]
  exact le_max_leftₓ _ _

theorem snd : IsBoundedLinearMap 𝕜 fun x : E × F => x.2 := by
  refine' (LinearMap.snd 𝕜 E F).is_linear.with_bound 1 fun x => _
  rw [one_mulₓ]
  exact le_max_rightₓ _ _

variable {f g : E → F}

theorem smul (c : 𝕜) (hf : IsBoundedLinearMap 𝕜 f) : IsBoundedLinearMap 𝕜 (c • f) :=
  let ⟨hlf, M, hMp, hM⟩ := hf
  ((c • hlf.mk' f).is_linear.with_bound (∥c∥ * M)) fun x =>
    calc
      ∥c • f x∥ = ∥c∥ * ∥f x∥ := norm_smul c (f x)
      _ ≤ ∥c∥ * (M * ∥x∥) := mul_le_mul_of_nonneg_left (hM _) (norm_nonneg _)
      _ = ∥c∥ * M * ∥x∥ := (mul_assoc _ _ _).symm
      

theorem neg (hf : IsBoundedLinearMap 𝕜 f) : IsBoundedLinearMap 𝕜 fun e => -f e := by
  rw
    [show (fun e => -f e) = fun e => (-1 : 𝕜) • f e by
      funext
      simp ]
  exact smul (-1) hf

theorem add (hf : IsBoundedLinearMap 𝕜 f) (hg : IsBoundedLinearMap 𝕜 g) : IsBoundedLinearMap 𝕜 fun e => f e + g e :=
  let ⟨hlf, Mf, hMfp, hMf⟩ := hf
  let ⟨hlg, Mg, hMgp, hMg⟩ := hg
  ((hlf.mk' _ + hlg.mk' _).is_linear.with_bound (Mf + Mg)) fun x =>
    calc
      ∥f x + g x∥ ≤ Mf * ∥x∥ + Mg * ∥x∥ := norm_add_le_of_le (hMf x) (hMg x)
      _ ≤ (Mf + Mg) * ∥x∥ := by
        rw [add_mulₓ]
      

theorem sub (hf : IsBoundedLinearMap 𝕜 f) (hg : IsBoundedLinearMap 𝕜 g) : IsBoundedLinearMap 𝕜 fun e => f e - g e := by
  simpa [← sub_eq_add_neg] using add hf (neg hg)

theorem comp {g : F → G} (hg : IsBoundedLinearMap 𝕜 g) (hf : IsBoundedLinearMap 𝕜 f) : IsBoundedLinearMap 𝕜 (g ∘ f) :=
  (hg.toContinuousLinearMap.comp hf.toContinuousLinearMap).IsBoundedLinearMap

protected theorem tendsto (x : E) (hf : IsBoundedLinearMap 𝕜 f) : Tendsto f (𝓝 x) (𝓝 (f x)) :=
  let ⟨hf, M, hMp, hM⟩ := hf
  tendsto_iff_norm_tendsto_zero.2 <|
    squeeze_zero (fun e => norm_nonneg _)
      (fun e =>
        calc
          ∥f e - f x∥ = ∥hf.mk' f (e - x)∥ := by
            rw [(hf.mk' _).map_sub e x] <;> rfl
          _ ≤ M * ∥e - x∥ := hM (e - x)
          )
      (suffices Tendsto (fun e : E => M * ∥e - x∥) (𝓝 x) (𝓝 (M * 0)) by
        simpa
      tendsto_const_nhds.mul (tendsto_norm_sub_self _))

theorem continuous (hf : IsBoundedLinearMap 𝕜 f) : Continuous f :=
  continuous_iff_continuous_at.2 fun _ => hf.Tendsto _

theorem lim_zero_bounded_linear_map (hf : IsBoundedLinearMap 𝕜 f) : Tendsto f (𝓝 0) (𝓝 0) :=
  (hf.1.mk' _).map_zero ▸ continuous_iff_continuous_at.1 hf.Continuous 0

section

open Asymptotics Filter

theorem is_O_id {f : E → F} (h : IsBoundedLinearMap 𝕜 f) (l : Filter E) : f =O[l] fun x => x :=
  let ⟨M, hMp, hM⟩ := h.bound
  IsO.of_bound _ (mem_of_superset univ_mem fun x _ => hM x)

theorem is_O_comp {E : Type _} {g : F → G} (hg : IsBoundedLinearMap 𝕜 g) {f : E → F} (l : Filter E) :
    (fun x' => g (f x')) =O[l] f :=
  (hg.is_O_id ⊤).comp_tendsto le_top

theorem is_O_sub {f : E → F} (h : IsBoundedLinearMap 𝕜 f) (l : Filter E) (x : E) :
    (fun x' => f (x' - x)) =O[l] fun x' => x' - x :=
  is_O_comp h l

end

end IsBoundedLinearMap

section

variable {ι : Type _} [DecidableEq ι] [Fintype ι]

/-- Taking the cartesian product of two continuous multilinear maps
is a bounded linear operation. -/
theorem is_bounded_linear_map_prod_multilinear {E : ι → Type _} [∀ i, NormedGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] :
    IsBoundedLinearMap 𝕜 fun p : ContinuousMultilinearMap 𝕜 E F × ContinuousMultilinearMap 𝕜 E G => p.1.Prod p.2 :=
  { map_add := fun p₁ p₂ => by
      ext1 m
      rfl,
    map_smul := fun c p => by
      ext1 m
      rfl,
    bound :=
      ⟨1, zero_lt_one, fun p => by
        rw [one_mulₓ]
        apply ContinuousMultilinearMap.op_norm_le_bound _ (norm_nonneg _) fun m => _
        rw [ContinuousMultilinearMap.prod_apply, norm_prod_le_iff]
        constructor
        · exact
            (p.1.le_op_norm m).trans
              (mul_le_mul_of_nonneg_right (norm_fst_le p) (Finset.prod_nonneg fun i hi => norm_nonneg _))
          
        · exact
            (p.2.le_op_norm m).trans
              (mul_le_mul_of_nonneg_right (norm_snd_le p) (Finset.prod_nonneg fun i hi => norm_nonneg _))
          ⟩ }

-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:63:9: parse error
/-- Given a fixed continuous linear map `g`, associating to a continuous multilinear map `f` the
continuous multilinear map `f (g m₁, ..., g mₙ)` is a bounded linear operation. -/
theorem is_bounded_linear_map_continuous_multilinear_map_comp_linear (g : G →L[𝕜] E) :
    IsBoundedLinearMap 𝕜 fun f : ContinuousMultilinearMap 𝕜 (fun i : ι => E) F =>
      f.compContinuousLinearMap fun _ => g :=
  by
  refine'
    IsLinearMap.with_bound
      ⟨fun f₁ f₂ => by
        ext m
        rfl, fun c f => by
        ext m
        rfl⟩
      (∥g∥ ^ Fintype.card ι) fun f => _
  apply ContinuousMultilinearMap.op_norm_le_bound _ _ fun m => _
  · apply_rules [mul_nonneg, pow_nonneg, norm_nonneg]
    
  calc ∥f (g ∘ m)∥ ≤ ∥f∥ * ∏ i, ∥g (m i)∥ := f.le_op_norm _ _ ≤ ∥f∥ * ∏ i, ∥g∥ * ∥m i∥ := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact
        Finset.prod_le_prod (fun i hi => norm_nonneg _) fun i hi =>
          g.le_op_norm _ _ = ∥g∥ ^ Fintype.card ι * ∥f∥ * ∏ i, ∥m i∥ :=
      by
      simp [← Finset.prod_mul_distrib, ← Finset.card_univ]
      ring

end

section BilinearMap

namespace ContinuousLinearMap

/-! We prove some computation rules for continuous (semi-)bilinear maps in their first argument.
  If `f` is a continuuous bilinear map, to use the corresponding rules for the second argument, use
  `(f _).map_add` and similar.

  We have to assume that `F` and `G` are normed spaces in this section, to use
  `continuous_linear_map.to_normed_group`, but we don't need to assume this for the first argument
  of `f`.
-/


variable {R : Type _}

variable {𝕜₂ 𝕜' : Type _} [NondiscreteNormedField 𝕜'] [NondiscreteNormedField 𝕜₂]

variable {M : Type _} [TopologicalSpace M]

variable {σ₁₂ : 𝕜 →+* 𝕜₂} [RingHomIsometric σ₁₂]

variable {G' : Type _} [NormedGroup G'] [NormedSpace 𝕜₂ G'] [NormedSpace 𝕜' G']

variable [SmulCommClass 𝕜₂ 𝕜' G']

section Semiringₓ

variable [Semiringₓ R] [AddCommMonoidₓ M] [Module R M] {ρ₁₂ : R →+* 𝕜'}

theorem map_add₂ (f : M →SL[ρ₁₂] F →SL[σ₁₂] G') (x x' : M) (y : F) : f (x + x') y = f x y + f x' y := by
  rw [f.map_add, add_apply]

theorem map_zero₂ (f : M →SL[ρ₁₂] F →SL[σ₁₂] G') (y : F) : f 0 y = 0 := by
  rw [f.map_zero, zero_apply]

theorem map_smulₛₗ₂ (f : M →SL[ρ₁₂] F →SL[σ₁₂] G') (c : R) (x : M) (y : F) : f (c • x) y = ρ₁₂ c • f x y := by
  rw [f.map_smulₛₗ, smul_apply]

end Semiringₓ

section Ringₓ

variable [Ringₓ R] [AddCommGroupₓ M] [Module R M] {ρ₁₂ : R →+* 𝕜'}

theorem map_sub₂ (f : M →SL[ρ₁₂] F →SL[σ₁₂] G') (x x' : M) (y : F) : f (x - x') y = f x y - f x' y := by
  rw [f.map_sub, sub_apply]

theorem map_neg₂ (f : M →SL[ρ₁₂] F →SL[σ₁₂] G') (x : M) (y : F) : f (-x) y = -f x y := by
  rw [f.map_neg, neg_apply]

end Ringₓ

theorem map_smul₂ (f : E →L[𝕜] F →L[𝕜] G) (c : 𝕜) (x : E) (y : F) : f (c • x) y = c • f x y := by
  rw [f.map_smul, smul_apply]

end ContinuousLinearMap

variable (𝕜)

/-- A map `f : E × F → G` satisfies `is_bounded_bilinear_map 𝕜 f` if it is bilinear and
continuous. -/
structure IsBoundedBilinearMap (f : E × F → G) : Prop where
  add_left : ∀ (x₁ x₂ : E) (y : F), f (x₁ + x₂, y) = f (x₁, y) + f (x₂, y)
  smul_left : ∀ (c : 𝕜) (x : E) (y : F), f (c • x, y) = c • f (x, y)
  add_right : ∀ (x : E) (y₁ y₂ : F), f (x, y₁ + y₂) = f (x, y₁) + f (x, y₂)
  smul_right : ∀ (c : 𝕜) (x : E) (y : F), f (x, c • y) = c • f (x, y)
  bound : ∃ C > 0, ∀ (x : E) (y : F), ∥f (x, y)∥ ≤ C * ∥x∥ * ∥y∥

variable {𝕜}

variable {f : E × F → G}

-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:63:9: parse error
theorem ContinuousLinearMap.is_bounded_bilinear_map (f : E →L[𝕜] F →L[𝕜] G) :
    IsBoundedBilinearMap 𝕜 fun x : E × F => f x.1 x.2 :=
  { add_left := f.map_add₂, smul_left := f.map_smul₂, add_right := fun x => (f x).map_add,
    smul_right := fun c x => (f x).map_smul c,
    bound :=
      ⟨max ∥f∥ 1, zero_lt_one.trans_le (le_max_rightₓ _ _), fun x y =>
        (f.le_op_norm₂ x y).trans <| by
          apply_rules [mul_le_mul_of_nonneg_right, norm_nonneg, le_max_leftₓ]⟩ }

protected theorem IsBoundedBilinearMap.is_O (h : IsBoundedBilinearMap 𝕜 f) : f =O[⊤] fun p : E × F => ∥p.1∥ * ∥p.2∥ :=
  let ⟨C, Cpos, hC⟩ := h.bound
  Asymptotics.IsO.of_bound _ <|
    Filter.eventually_of_forall fun ⟨x, y⟩ => by
      simpa [← mul_assoc] using hC x y

theorem IsBoundedBilinearMap.is_O_comp {α : Type _} (H : IsBoundedBilinearMap 𝕜 f) {g : α → E} {h : α → F}
    {l : Filter α} : (fun x => f (g x, h x)) =O[l] fun x => ∥g x∥ * ∥h x∥ :=
  H.IsO.comp_tendsto le_top

protected theorem IsBoundedBilinearMap.is_O' (h : IsBoundedBilinearMap 𝕜 f) : f =O[⊤] fun p : E × F => ∥p∥ * ∥p∥ :=
  h.IsO.trans (Asymptotics.is_O_fst_prod'.norm_norm.mul Asymptotics.is_O_snd_prod'.norm_norm)

theorem IsBoundedBilinearMap.map_sub_left (h : IsBoundedBilinearMap 𝕜 f) {x y : E} {z : F} :
    f (x - y, z) = f (x, z) - f (y, z) :=
  calc
    f (x - y, z) = f (x + (-1 : 𝕜) • y, z) := by
      simp [← sub_eq_add_neg]
    _ = f (x, z) + (-1 : 𝕜) • f (y, z) := by
      simp only [← h.add_left, ← h.smul_left]
    _ = f (x, z) - f (y, z) := by
      simp [← sub_eq_add_neg]
    

theorem IsBoundedBilinearMap.map_sub_right (h : IsBoundedBilinearMap 𝕜 f) {x : E} {y z : F} :
    f (x, y - z) = f (x, y) - f (x, z) :=
  calc
    f (x, y - z) = f (x, y + (-1 : 𝕜) • z) := by
      simp [← sub_eq_add_neg]
    _ = f (x, y) + (-1 : 𝕜) • f (x, z) := by
      simp only [← h.add_right, ← h.smul_right]
    _ = f (x, y) - f (x, z) := by
      simp [← sub_eq_add_neg]
    

/-- Useful to use together with `continuous.comp₂`. -/
theorem IsBoundedBilinearMap.continuous (h : IsBoundedBilinearMap 𝕜 f) : Continuous f := by
  have one_ne : (1 : ℝ) ≠ 0 := by
    simp
  obtain ⟨C, Cpos : 0 < C, hC⟩ := h.bound
  rw [continuous_iff_continuous_at]
  intro x
  have H : ∀ (a : E) (b : F), ∥f (a, b)∥ ≤ C * ∥∥a∥ * ∥b∥∥ := by
    intro a b
    simpa [← mul_assoc] using hC a b
  have h₁ : (fun e : E × F => f (e.1 - x.1, e.2)) =o[𝓝 x] fun e => (1 : ℝ) := by
    refine' (Asymptotics.is_O_of_le' (𝓝 x) fun e => H (e.1 - x.1) e.2).trans_is_o _
    rw [Asymptotics.is_o_const_iff one_ne]
    convert ((continuous_fst.sub continuous_const).norm.mul continuous_snd.norm).ContinuousAt
    · simp
      
    infer_instance
  have h₂ : (fun e : E × F => f (x.1, e.2 - x.2)) =o[𝓝 x] fun e => (1 : ℝ) := by
    refine' (Asymptotics.is_O_of_le' (𝓝 x) fun e => H x.1 (e.2 - x.2)).trans_is_o _
    rw [Asymptotics.is_o_const_iff one_ne]
    convert (continuous_const.mul (continuous_snd.sub continuous_const).norm).ContinuousAt
    · simp
      
    infer_instance
  have := h₁.add h₂
  rw [Asymptotics.is_o_const_iff one_ne] at this
  change tendsto _ _ _
  convert this.add_const (f x)
  · ext e
    simp [← h.map_sub_left, ← h.map_sub_right]
    
  · simp
    

theorem IsBoundedBilinearMap.continuous_left (h : IsBoundedBilinearMap 𝕜 f) {e₂ : F} :
    Continuous fun e₁ => f (e₁, e₂) :=
  h.Continuous.comp (continuous_id.prod_mk continuous_const)

theorem IsBoundedBilinearMap.continuous_right (h : IsBoundedBilinearMap 𝕜 f) {e₁ : E} :
    Continuous fun e₂ => f (e₁, e₂) :=
  h.Continuous.comp (continuous_const.prod_mk continuous_id)

/-- Useful to use together with `continuous.comp₂`. -/
theorem ContinuousLinearMap.continuous₂ (f : E →L[𝕜] F →L[𝕜] G) : Continuous (Function.uncurry fun x y => f x y) :=
  f.IsBoundedBilinearMap.Continuous

-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:63:9: parse error
theorem IsBoundedBilinearMap.is_bounded_linear_map_left (h : IsBoundedBilinearMap 𝕜 f) (y : F) :
    IsBoundedLinearMap 𝕜 fun x => f (x, y) :=
  { map_add := fun x x' => h.add_left _ _ _, map_smul := fun c x => h.smul_left _ _ _,
    bound := by
      rcases h.bound with ⟨C, C_pos, hC⟩
      refine'
        ⟨C * (∥y∥ + 1),
          mul_pos C_pos
            (lt_of_lt_of_leₓ zero_lt_one
              (by
                simp )),
          fun x => _⟩
      have : ∥y∥ ≤ ∥y∥ + 1 := by
        simp [← zero_le_one]
      calc ∥f (x, y)∥ ≤ C * ∥x∥ * ∥y∥ := hC x y _ ≤ C * ∥x∥ * (∥y∥ + 1) := by
          apply_rules [norm_nonneg, mul_le_mul_of_nonneg_left, le_of_ltₓ C_pos, mul_nonneg]_ = C * (∥y∥ + 1) * ∥x∥ := by
          ring }

-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:63:9: parse error
theorem IsBoundedBilinearMap.is_bounded_linear_map_right (h : IsBoundedBilinearMap 𝕜 f) (x : E) :
    IsBoundedLinearMap 𝕜 fun y => f (x, y) :=
  { map_add := fun y y' => h.add_right _ _ _, map_smul := fun c y => h.smul_right _ _ _,
    bound := by
      rcases h.bound with ⟨C, C_pos, hC⟩
      refine'
        ⟨C * (∥x∥ + 1),
          mul_pos C_pos
            (lt_of_lt_of_leₓ zero_lt_one
              (by
                simp )),
          fun y => _⟩
      have : ∥x∥ ≤ ∥x∥ + 1 := by
        simp [← zero_le_one]
      calc ∥f (x, y)∥ ≤ C * ∥x∥ * ∥y∥ := hC x y _ ≤ C * (∥x∥ + 1) * ∥y∥ := by
          apply_rules [mul_le_mul_of_nonneg_right, norm_nonneg, mul_le_mul_of_nonneg_left, le_of_ltₓ C_pos] }

theorem is_bounded_bilinear_map_smul {𝕜' : Type _} [NormedField 𝕜'] [NormedAlgebra 𝕜 𝕜'] {E : Type _} [NormedGroup E]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜' E] [IsScalarTower 𝕜 𝕜' E] : IsBoundedBilinearMap 𝕜 fun p : 𝕜' × E => p.1 • p.2 :=
  (lsmul 𝕜 𝕜' : 𝕜' →L[𝕜] E →L[𝕜] E).IsBoundedBilinearMap

theorem is_bounded_bilinear_map_mul : IsBoundedBilinearMap 𝕜 fun p : 𝕜 × 𝕜 => p.1 * p.2 := by
  simp_rw [← smul_eq_mul] <;> exact is_bounded_bilinear_map_smul

theorem is_bounded_bilinear_map_comp : IsBoundedBilinearMap 𝕜 fun p : (F →L[𝕜] G) × (E →L[𝕜] F) => p.1.comp p.2 :=
  (compL 𝕜 E F G).IsBoundedBilinearMap

theorem ContinuousLinearMap.is_bounded_linear_map_comp_left (g : F →L[𝕜] G) :
    IsBoundedLinearMap 𝕜 fun f : E →L[𝕜] F => ContinuousLinearMap.comp g f :=
  is_bounded_bilinear_map_comp.is_bounded_linear_map_right _

theorem ContinuousLinearMap.is_bounded_linear_map_comp_right (f : E →L[𝕜] F) :
    IsBoundedLinearMap 𝕜 fun g : F →L[𝕜] G => ContinuousLinearMap.comp g f :=
  is_bounded_bilinear_map_comp.is_bounded_linear_map_left _

theorem is_bounded_bilinear_map_apply : IsBoundedBilinearMap 𝕜 fun p : (E →L[𝕜] F) × E => p.1 p.2 :=
  (ContinuousLinearMap.flip (apply 𝕜 F : E →L[𝕜] (E →L[𝕜] F) →L[𝕜] F)).IsBoundedBilinearMap

/-- The function `continuous_linear_map.smul_right`, associating to a continuous linear map
`f : E → 𝕜` and a scalar `c : F` the tensor product `f ⊗ c` as a continuous linear map from `E` to
`F`, is a bounded bilinear map. -/
theorem is_bounded_bilinear_map_smul_right :
    IsBoundedBilinearMap 𝕜 fun p => (ContinuousLinearMap.smulRight : (E →L[𝕜] 𝕜) → F → E →L[𝕜] F) p.1 p.2 :=
  (smulRightL 𝕜 E F).IsBoundedBilinearMap

/-- The composition of a continuous linear map with a continuous multilinear map is a bounded
bilinear operation. -/
theorem is_bounded_bilinear_map_comp_multilinear {ι : Type _} {E : ι → Type _} [DecidableEq ι] [Fintype ι]
    [∀ i, NormedGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] :
    IsBoundedBilinearMap 𝕜 fun p : (F →L[𝕜] G) × ContinuousMultilinearMap 𝕜 E F =>
      p.1.compContinuousMultilinearMap p.2 :=
  (compContinuousMultilinearMapL 𝕜 E F G).IsBoundedBilinearMap

/-- Definition of the derivative of a bilinear map `f`, given at a point `p` by
`q ↦ f(p.1, q.2) + f(q.1, p.2)` as in the standard formula for the derivative of a product.
We define this function here as a linear map `E × F →ₗ[𝕜] G`, then `is_bounded_bilinear_map.deriv`
strengthens it to a continuous linear map `E × F →L[𝕜] G`.
``. -/
def IsBoundedBilinearMap.linearDeriv (h : IsBoundedBilinearMap 𝕜 f) (p : E × F) : E × F →ₗ[𝕜] G where
  toFun := fun q => f (p.1, q.2) + f (q.1, p.2)
  map_add' := fun q₁ q₂ => by
    change f (p.1, q₁.2 + q₂.2) + f (q₁.1 + q₂.1, p.2) = f (p.1, q₁.2) + f (q₁.1, p.2) + (f (p.1, q₂.2) + f (q₂.1, p.2))
    simp [← h.add_left, ← h.add_right]
    abel
  map_smul' := fun c q => by
    change f (p.1, c • q.2) + f (c • q.1, p.2) = c • (f (p.1, q.2) + f (q.1, p.2))
    simp [← h.smul_left, ← h.smul_right, ← smul_add]

/-- The derivative of a bounded bilinear map at a point `p : E × F`, as a continuous linear map
from `E × F` to `G`. The statement that this is indeed the derivative of `f` is
`is_bounded_bilinear_map.has_fderiv_at` in `analysis.calculus.fderiv`. -/
def IsBoundedBilinearMap.deriv (h : IsBoundedBilinearMap 𝕜 f) (p : E × F) : E × F →L[𝕜] G :=
  (h.linearDeriv p).mkContinuousOfExistsBound <| by
    rcases h.bound with ⟨C, Cpos, hC⟩
    refine' ⟨C * ∥p.1∥ + C * ∥p.2∥, fun q => _⟩
    calc ∥f (p.1, q.2) + f (q.1, p.2)∥ ≤ C * ∥p.1∥ * ∥q.2∥ + C * ∥q.1∥ * ∥p.2∥ :=
        norm_add_le_of_le (hC _ _) (hC _ _)_ ≤ C * ∥p.1∥ * ∥q∥ + C * ∥q∥ * ∥p.2∥ := by
        apply add_le_add
        exact mul_le_mul_of_nonneg_left (le_max_rightₓ _ _) (mul_nonneg (le_of_ltₓ Cpos) (norm_nonneg _))
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        exact mul_le_mul_of_nonneg_left (le_max_leftₓ _ _) (le_of_ltₓ Cpos)_ = (C * ∥p.1∥ + C * ∥p.2∥) * ∥q∥ := by
        ring

@[simp]
theorem is_bounded_bilinear_map_deriv_coe (h : IsBoundedBilinearMap 𝕜 f) (p q : E × F) :
    h.deriv p q = f (p.1, q.2) + f (q.1, p.2) :=
  rfl

variable (𝕜)

/-- The function `lmul_left_right : 𝕜' × 𝕜' → (𝕜' →L[𝕜] 𝕜')` is a bounded bilinear map. -/
theorem ContinuousLinearMap.lmul_left_right_is_bounded_bilinear (𝕜' : Type _) [NormedRing 𝕜'] [NormedAlgebra 𝕜 𝕜'] :
    IsBoundedBilinearMap 𝕜 fun p : 𝕜' × 𝕜' => ContinuousLinearMap.lmulLeftRight 𝕜 𝕜' p.1 p.2 :=
  (ContinuousLinearMap.lmulLeftRight 𝕜 𝕜').IsBoundedBilinearMap

variable {𝕜}

-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:63:9: parse error
/-- Given a bounded bilinear map `f`, the map associating to a point `p` the derivative of `f` at
`p` is itself a bounded linear map. -/
theorem IsBoundedBilinearMap.is_bounded_linear_map_deriv (h : IsBoundedBilinearMap 𝕜 f) :
    IsBoundedLinearMap 𝕜 fun p : E × F => h.deriv p := by
  rcases h.bound with ⟨C, Cpos : 0 < C, hC⟩
  refine' IsLinearMap.with_bound ⟨fun p₁ p₂ => _, fun c p => _⟩ (C + C) fun p => _
  · ext <;> simp [← h.add_left, ← h.add_right] <;> abel
    
  · ext <;> simp [← h.smul_left, ← h.smul_right, ← smul_add]
    
  · refine' ContinuousLinearMap.op_norm_le_bound _ (mul_nonneg (add_nonneg Cpos.le Cpos.le) (norm_nonneg _)) fun q => _
    calc ∥f (p.1, q.2) + f (q.1, p.2)∥ ≤ C * ∥p.1∥ * ∥q.2∥ + C * ∥q.1∥ * ∥p.2∥ :=
        norm_add_le_of_le (hC _ _) (hC _ _)_ ≤ C * ∥p∥ * ∥q∥ + C * ∥q∥ * ∥p∥ := by
        apply_rules [add_le_add, mul_le_mul, norm_nonneg, Cpos.le, le_reflₓ, le_max_leftₓ, le_max_rightₓ,
          mul_nonneg]_ = (C + C) * ∥p∥ * ∥q∥ :=
        by
        ring
    

end BilinearMap

theorem Continuous.clm_comp {X} [TopologicalSpace X] {g : X → F →L[𝕜] G} {f : X → E →L[𝕜] F} (hg : Continuous g)
    (hf : Continuous f) : Continuous fun x => (g x).comp (f x) :=
  (compL 𝕜 E F G).continuous₂.comp₂ hg hf

theorem ContinuousOn.clm_comp {X} [TopologicalSpace X] {g : X → F →L[𝕜] G} {f : X → E →L[𝕜] F} {s : Set X}
    (hg : ContinuousOn g s) (hf : ContinuousOn f s) : ContinuousOn (fun x => (g x).comp (f x)) s :=
  (compL 𝕜 E F G).continuous₂.comp_continuous_on (hg.Prod hf)

namespace ContinuousLinearEquiv

open Set

/-!
### The set of continuous linear equivalences between two Banach spaces is open

In this section we establish that the set of continuous linear equivalences between two Banach
spaces is an open subset of the space of linear maps between them.
-/


protected theorem is_open [CompleteSpace E] : IsOpen (Range (coe : (E ≃L[𝕜] F) → E →L[𝕜] F)) := by
  rw [is_open_iff_mem_nhds, forall_range_iff]
  refine' fun e => IsOpen.mem_nhds _ (mem_range_self _)
  let O : (E →L[𝕜] F) → E →L[𝕜] E := fun f => (e.symm : F →L[𝕜] E).comp f
  have h_O : Continuous O := is_bounded_bilinear_map_comp.continuous_right
  convert units.is_open.preimage h_O using 1
  ext f'
  constructor
  · rintro ⟨e', rfl⟩
    exact ⟨(e'.trans e.symm).toUnit, rfl⟩
    
  · rintro ⟨w, hw⟩
    use (units_equiv 𝕜 E w).trans e
    ext x
    simp [← coe_fn_coe_base' w, ← hw]
    

protected theorem nhds [CompleteSpace E] (e : E ≃L[𝕜] F) : Range (coe : (E ≃L[𝕜] F) → E →L[𝕜] F) ∈ 𝓝 (e : E →L[𝕜] F) :=
  IsOpen.mem_nhds ContinuousLinearEquiv.is_open
    (by
      simp )

end ContinuousLinearEquiv

