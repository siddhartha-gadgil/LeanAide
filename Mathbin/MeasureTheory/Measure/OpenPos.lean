/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathbin.MeasureTheory.Measure.MeasureSpace

/-!
# Measures positive on nonempty opens

In this file we define a typeclass for measures that are positive on nonempty opens, see
`measure_theory.measure.is_open_pos_measure`. Examples include (additive) Haar measures, as well as
measures that have positive density with respect to a Haar measure. We also prove some basic facts
about these measures.

-/


open TopologicalSpace Ennreal MeasureTheory

open Set Function Filter

namespace MeasureTheory

namespace Measureₓ

section Basic

variable {X Y : Type _} [TopologicalSpace X] {m : MeasurableSpace X} [TopologicalSpace Y] [T2Space Y] (μ ν : Measure X)

/-- A measure is said to be `is_open_pos_measure` if it is positive on nonempty open sets. -/
class IsOpenPosMeasure : Prop where
  open_pos : ∀ U : Set X, IsOpen U → U.Nonempty → μ U ≠ 0

variable [IsOpenPosMeasure μ] {s U : Set X} {x : X}

theorem _root_.is_open.measure_ne_zero (hU : IsOpen U) (hne : U.Nonempty) : μ U ≠ 0 :=
  IsOpenPosMeasure.open_pos U hU hne

theorem _root_.is_open.measure_pos (hU : IsOpen U) (hne : U.Nonempty) : 0 < μ U :=
  (hU.measure_ne_zero μ hne).bot_lt

theorem _root_.is_open.measure_pos_iff (hU : IsOpen U) : 0 < μ U ↔ U.Nonempty :=
  ⟨fun h => ne_empty_iff_nonempty.1 fun he => h.ne' <| he.symm ▸ measure_empty, hU.measure_pos μ⟩

theorem _root_.is_open.measure_eq_zero_iff (hU : IsOpen U) : μ U = 0 ↔ U = ∅ := by
  simpa only [← not_ltₓ, ← nonpos_iff_eq_zero, ← not_nonempty_iff_eq_empty] using not_congr (hU.measure_pos_iff μ)

theorem measure_pos_of_nonempty_interior (h : (Interior s).Nonempty) : 0 < μ s :=
  (is_open_interior.measure_pos μ h).trans_le (measure_mono interior_subset)

theorem measure_pos_of_mem_nhds (h : s ∈ 𝓝 x) : 0 < μ s :=
  measure_pos_of_nonempty_interior _ ⟨x, mem_interior_iff_mem_nhds.2 h⟩

theorem is_open_pos_measure_smul {c : ℝ≥0∞} (h : c ≠ 0) : IsOpenPosMeasure (c • μ) :=
  ⟨fun U Uo Une => mul_ne_zero h (Uo.measure_ne_zero μ Une)⟩

variable {μ ν}

protected theorem AbsolutelyContinuous.is_open_pos_measure (h : μ ≪ ν) : IsOpenPosMeasure ν :=
  ⟨fun U ho hne h₀ => ho.measure_ne_zero μ hne (h h₀)⟩

theorem _root_.has_le.le.is_open_pos_measure (h : μ ≤ ν) : IsOpenPosMeasure ν :=
  h.AbsolutelyContinuous.IsOpenPosMeasure

theorem _root_.is_open.eq_empty_of_measure_zero (hU : IsOpen U) (h₀ : μ U = 0) : U = ∅ :=
  (hU.measure_eq_zero_iff μ).mp h₀

theorem interior_eq_empty_of_null (hs : μ s = 0) : Interior s = ∅ :=
  is_open_interior.eq_empty_of_measure_zero <| measure_mono_null interior_subset hs

/-- If two functions are a.e. equal on an open set and are continuous on this set, then they are
equal on this set. -/
theorem eq_on_open_of_ae_eq {f g : X → Y} (h : f =ᵐ[μ.restrict U] g) (hU : IsOpen U) (hf : ContinuousOn f U)
    (hg : ContinuousOn g U) : EqOn f g U := by
  replace h := ae_imp_of_ae_restrict h
  simp only [← eventually_eq, ← ae_iff, ← not_imp] at h
  have : IsOpen (U ∩ { a | f a ≠ g a }) := by
    refine' is_open_iff_mem_nhds.mpr fun a ha => inter_mem (hU.mem_nhds ha.1) _
    rcases ha with ⟨ha : a ∈ U, ha' : (f a, g a) ∈ diagonal Yᶜ⟩
    exact
      (hf.continuous_at (hU.mem_nhds ha)).prod_mk_nhds (hg.continuous_at (hU.mem_nhds ha))
        (is_closed_diagonal.is_open_compl.mem_nhds ha')
  replace := (this.eq_empty_of_measure_zero h).le
  exact fun x hx => not_not.1 fun h => this ⟨hx, h⟩

/-- If two continuous functions are a.e. equal, then they are equal. -/
theorem eq_of_ae_eq {f g : X → Y} (h : f =ᵐ[μ] g) (hf : Continuous f) (hg : Continuous g) : f = g :=
  suffices EqOn f g Univ from funext fun x => this trivialₓ
  eq_on_open_of_ae_eq (ae_restrict_of_ae h) is_open_univ hf.ContinuousOn hg.ContinuousOn

theorem eq_on_of_ae_eq {f g : X → Y} (h : f =ᵐ[μ.restrict s] g) (hf : ContinuousOn f s) (hg : ContinuousOn g s)
    (hU : s ⊆ Closure (Interior s)) : EqOn f g s :=
  have : Interior s ⊆ s := interior_subset
  (eq_on_open_of_ae_eq (ae_restrict_of_ae_restrict_of_subset this h) is_open_interior (hf.mono this)
        (hg.mono this)).of_subset_closure
    hf hg this hU

variable (μ)

theorem _root_.continuous.ae_eq_iff_eq {f g : X → Y} (hf : Continuous f) (hg : Continuous g) : f =ᵐ[μ] g ↔ f = g :=
  ⟨fun h => eq_of_ae_eq h hf hg, fun h => h ▸ eventually_eq.rfl⟩

end Basic

section LinearOrderₓ

variable {X Y : Type _} [TopologicalSpace X] [LinearOrderₓ X] [OrderTopology X] {m : MeasurableSpace X}
  [TopologicalSpace Y] [T2Space Y] (μ : Measure X) [IsOpenPosMeasure μ]

theorem measure_Ioi_pos [NoMaxOrder X] (a : X) : 0 < μ (Ioi a) :=
  is_open_Ioi.measure_pos μ nonempty_Ioi

theorem measure_Iio_pos [NoMinOrder X] (a : X) : 0 < μ (Iio a) :=
  is_open_Iio.measure_pos μ nonempty_Iio

theorem measure_Ioo_pos [DenselyOrdered X] {a b : X} : 0 < μ (Ioo a b) ↔ a < b :=
  (is_open_Ioo.measure_pos_iff μ).trans nonempty_Ioo

theorem measure_Ioo_eq_zero [DenselyOrdered X] {a b : X} : μ (Ioo a b) = 0 ↔ b ≤ a :=
  (is_open_Ioo.measure_eq_zero_iff μ).trans (Ioo_eq_empty_iff.trans not_ltₓ)

theorem eq_on_Ioo_of_ae_eq {a b : X} {f g : X → Y} (hfg : f =ᵐ[μ.restrict (Ioo a b)] g) (hf : ContinuousOn f (Ioo a b))
    (hg : ContinuousOn g (Ioo a b)) : EqOn f g (Ioo a b) :=
  eq_on_of_ae_eq hfg hf hg Ioo_subset_closure_interior

theorem eq_on_Ioc_of_ae_eq [DenselyOrdered X] {a b : X} {f g : X → Y} (hfg : f =ᵐ[μ.restrict (Ioc a b)] g)
    (hf : ContinuousOn f (Ioc a b)) (hg : ContinuousOn g (Ioc a b)) : EqOn f g (Ioc a b) :=
  eq_on_of_ae_eq hfg hf hg (Ioc_subset_closure_interior _ _)

theorem eq_on_Ico_of_ae_eq [DenselyOrdered X] {a b : X} {f g : X → Y} (hfg : f =ᵐ[μ.restrict (Ico a b)] g)
    (hf : ContinuousOn f (Ico a b)) (hg : ContinuousOn g (Ico a b)) : EqOn f g (Ico a b) :=
  eq_on_of_ae_eq hfg hf hg (Ico_subset_closure_interior _ _)

theorem eq_on_Icc_of_ae_eq [DenselyOrdered X] {a b : X} (hne : a ≠ b) {f g : X → Y} (hfg : f =ᵐ[μ.restrict (Icc a b)] g)
    (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc a b)) : EqOn f g (Icc a b) :=
  eq_on_of_ae_eq hfg hf hg (closure_interior_Icc hne).symm.Subset

end LinearOrderₓ

end Measureₓ

end MeasureTheory

open MeasureTheory MeasureTheory.Measure

namespace Metric

variable {X : Type _} [PseudoMetricSpace X] {m : MeasurableSpace X} (μ : Measureₓ X) [IsOpenPosMeasure μ]

theorem measure_ball_pos (x : X) {r : ℝ} (hr : 0 < r) : 0 < μ (Ball x r) :=
  is_open_ball.measure_pos μ (nonempty_ball.2 hr)

theorem measure_closed_ball_pos (x : X) {r : ℝ} (hr : 0 < r) : 0 < μ (ClosedBall x r) :=
  (measure_ball_pos μ x hr).trans_le (measure_mono ball_subset_closed_ball)

end Metric

namespace Emetric

variable {X : Type _} [PseudoEmetricSpace X] {m : MeasurableSpace X} (μ : Measureₓ X) [IsOpenPosMeasure μ]

theorem measure_ball_pos (x : X) {r : ℝ≥0∞} (hr : r ≠ 0) : 0 < μ (Ball x r) :=
  is_open_ball.measure_pos μ ⟨x, mem_ball_self hr.bot_lt⟩

theorem measure_closed_ball_pos (x : X) {r : ℝ≥0∞} (hr : r ≠ 0) : 0 < μ (ClosedBall x r) :=
  (measure_ball_pos μ x hr).trans_le (measure_mono ball_subset_closed_ball)

end Emetric

