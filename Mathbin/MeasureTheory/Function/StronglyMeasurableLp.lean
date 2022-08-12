/-
Copyright (c) 2022 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathbin.MeasureTheory.Function.SimpleFuncDenseLp
import Mathbin.MeasureTheory.Function.StronglyMeasurable

/-!
# Finitely strongly measurable functions in `Lp`

Functions in `Lp` for `0 < p < ∞` are finitely strongly measurable.

## Main statements

* `mem_ℒp.ae_fin_strongly_measurable`: if `mem_ℒp f p μ` with `0 < p < ∞`, then
  `ae_fin_strongly_measurable f μ`.
* `Lp.fin_strongly_measurable`: for `0 < p < ∞`, `Lp` functions are finitely strongly measurable.

## References

* Hytönen, Tuomas, Jan Van Neerven, Mark Veraar, and Lutz Weis. Analysis in Banach spaces.
Springer, 2016.
-/


open MeasureTheory Filter TopologicalSpace Function

open Ennreal TopologicalSpace MeasureTheory

namespace MeasureTheory

-- mathport name: «expr →ₛ »
local infixr:25 " →ₛ " => SimpleFunc

variable {α G : Type _} {p : ℝ≥0∞} {m m0 : MeasurableSpace α} {μ : Measure α} [NormedGroup G] {f : α → G}

-- ./././Mathport/Syntax/Translate/Basic.lean:647:16: unsupported tactic `borelize #[[expr G]]
theorem Memℒp.fin_strongly_measurable_of_strongly_measurable (hf : Memℒp f p μ) (hf_meas : StronglyMeasurable f)
    (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞) : FinStronglyMeasurable f μ := by
  trace "./././Mathport/Syntax/Translate/Basic.lean:647:16: unsupported tactic `borelize #[[expr G]]"
  have : separable_space (Set.Range f ∪ {0} : Set G) := hf_meas.separable_space_range_union_singleton
  let fs :=
    simple_func.approx_on f hf_meas.measurable (Set.Range f ∪ {0}) 0
      (by
        simp )
  refine' ⟨fs, _, _⟩
  · have h_fs_Lp : ∀ n, mem_ℒp (fs n) p μ := simple_func.mem_ℒp_approx_on_range hf_meas.measurable hf
    exact fun n => (fs n).measure_support_lt_top_of_mem_ℒp (h_fs_Lp n) hp_ne_zero hp_ne_top
    
  · intro x
    apply simple_func.tendsto_approx_on
    apply subset_closure
    simp
    

theorem Memℒp.ae_fin_strongly_measurable (hf : Memℒp f p μ) (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞) :
    AeFinStronglyMeasurable f μ :=
  ⟨hf.AeStronglyMeasurable.mk f,
    ((mem_ℒp_congr_ae hf.AeStronglyMeasurable.ae_eq_mk).mp hf).fin_strongly_measurable_of_strongly_measurable
      hf.AeStronglyMeasurable.strongly_measurable_mk hp_ne_zero hp_ne_top,
    hf.AeStronglyMeasurable.ae_eq_mk⟩

theorem Integrable.ae_fin_strongly_measurable (hf : Integrable f μ) : AeFinStronglyMeasurable f μ :=
  (mem_ℒp_one_iff_integrable.mpr hf).AeFinStronglyMeasurable one_ne_zero Ennreal.coe_ne_top

theorem lp.fin_strongly_measurable (f : lp G p μ) (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞) :
    FinStronglyMeasurable f μ :=
  (lp.mem_ℒp f).fin_strongly_measurable_of_strongly_measurable (lp.strongly_measurable f) hp_ne_zero hp_ne_top

end MeasureTheory

