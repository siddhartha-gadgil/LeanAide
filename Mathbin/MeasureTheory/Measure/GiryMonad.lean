/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathbin.MeasureTheory.Integral.Lebesgue

/-!
# The Giry monad

Let X be a measurable space. The collection of all measures on X again
forms a measurable space. This construction forms a monad on
measurable spaces and measurable functions, called the Giry monad.

Note that most sources use the term "Giry monad" for the restriction
to *probability* measures. Here we include all measures on X.

See also `measure_theory/category/Meas.lean`, containing an upgrade of the type-level
monad to an honest monad of the functor `Measure : Meas ⥤ Meas`.

## References

* <https://ncatlab.org/nlab/show/Giry+monad>

## Tags

giry monad
-/


noncomputable section

open Classical BigOperators Ennreal

open Classical Set Filter

variable {α β γ δ ε : Type _}

namespace MeasureTheory

namespace Measureₓ

variable [MeasurableSpace α] [MeasurableSpace β]

/-- Measurability structure on `measure`: Measures are measurable w.r.t. all projections -/
instance : MeasurableSpace (Measure α) :=
  ⨆ (s : Set α) (hs : MeasurableSet s), (borel ℝ≥0∞).comap fun μ => μ s

theorem measurable_coe {s : Set α} (hs : MeasurableSet s) : Measurable fun μ : Measure α => μ s :=
  Measurable.of_comap_le <| le_supr_of_le s <| le_supr_of_le hs <| le_rfl

theorem measurable_of_measurable_coe (f : β → Measure α)
    (h : ∀ (s : Set α) (hs : MeasurableSet s), Measurable fun b => f b s) : Measurable f :=
  Measurable.of_le_map <|
    supr₂_le fun s hs =>
      MeasurableSpace.comap_le_iff_le_map.2 <| by
        rw [MeasurableSpace.map_comp] <;> exact h s hs

theorem measurable_measure {μ : α → Measure β} :
    Measurable μ ↔ ∀ (s : Set β) (hs : MeasurableSet s), Measurable fun b => μ b s :=
  ⟨fun hμ s hs => (measurable_coe hs).comp hμ, measurable_of_measurable_coe μ⟩

theorem measurable_map (f : α → β) (hf : Measurable f) : Measurable fun μ : Measure α => map f μ :=
  (measurable_of_measurable_coe _) fun s hs =>
    suffices Measurable fun μ : Measure α => μ (f ⁻¹' s) by
      simpa [← map_apply, ← hs, ← hf]
    measurable_coe (hf hs)

theorem measurable_dirac : Measurable (Measure.dirac : α → Measure α) :=
  (measurable_of_measurable_coe _) fun s hs => by
    simp only [← dirac_apply', ← hs]
    exact measurable_one.indicator hs

theorem measurable_lintegral {f : α → ℝ≥0∞} (hf : Measurable f) : Measurable fun μ : Measure α => ∫⁻ x, f x ∂μ := by
  simp only [← lintegral_eq_supr_eapprox_lintegral, ← hf, ← simple_func.lintegral]
  refine' measurable_supr fun n => Finset.measurable_sum _ fun i _ => _
  refine' Measurable.const_mul _ _
  exact measurable_coe ((simple_func.eapprox f n).measurable_set_preimage _)

/-- Monadic join on `measure` in the category of measurable spaces and measurable
functions. -/
def join (m : Measure (Measure α)) : Measure α :=
  Measure.ofMeasurable (fun s hs => ∫⁻ μ, μ s ∂m)
    (by
      simp )
    (by
      intro f hf h
      simp [← measure_Union h hf]
      apply lintegral_tsum
      intro i
      exact measurable_coe (hf i))

@[simp]
theorem join_apply {m : Measure (Measure α)} : ∀ {s : Set α}, MeasurableSet s → join m s = ∫⁻ μ, μ s ∂m :=
  measure.of_measurable_apply

@[simp]
theorem join_zero : (0 : Measure (Measure α)).join = 0 := by
  ext1 s hs
  simp [← hs]

theorem measurable_join : Measurable (join : Measure (Measure α) → Measure α) :=
  (measurable_of_measurable_coe _) fun s hs => by
    simp only [← join_apply hs] <;> exact measurable_lintegral (measurable_coe hs)

theorem lintegral_join {m : Measure (Measure α)} {f : α → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ x, f x ∂join m) = ∫⁻ μ, ∫⁻ x, f x ∂μ ∂m := by
  rw [lintegral_eq_supr_eapprox_lintegral hf]
  have :
    ∀ n x,
      join m (⇑(simple_func.eapprox (fun a : α => f a) n) ⁻¹' {x}) =
        ∫⁻ μ, μ (⇑(simple_func.eapprox (fun a : α => f a) n) ⁻¹' {x}) ∂m :=
    fun n x => join_apply (simple_func.measurable_set_preimage _ _)
  simp only [← simple_func.lintegral, ← this]
  trans
  have :
    ∀ (s : ℕ → Finset ℝ≥0∞) (f : ℕ → ℝ≥0∞ → Measureₓ α → ℝ≥0∞) (hf : ∀ n r, Measurable (f n r))
      (hm : Monotone fun n μ => ∑ r in s n, r * f n r μ),
      (⨆ n : ℕ, ∑ r in s n, r * ∫⁻ μ, f n r μ ∂m) = ∫⁻ μ, ⨆ n : ℕ, ∑ r in s n, r * f n r μ ∂m :=
    by
    intro s f hf hm
    symm
    trans
    apply lintegral_supr
    · intro n
      exact Finset.measurable_sum _ fun r _ => (hf _ _).const_mul _
      
    · exact hm
      
    congr
    funext n
    trans
    apply lintegral_finset_sum
    · intro r _
      exact (hf _ _).const_mul _
      
    congr
    funext r
    apply lintegral_const_mul
    exact hf _ _
  specialize this fun n => simple_func.range (simple_func.eapprox f n)
  specialize this fun n r μ => μ (⇑(simple_func.eapprox (fun a : α => f a) n) ⁻¹' {r})
  refine' this _ _ <;> clear this
  · intro n r
    apply measurable_coe
    exact simple_func.measurable_set_preimage _ _
    
  · change Monotone fun n μ => (simple_func.eapprox f n).lintegral μ
    intro n m h μ
    refine' simple_func.lintegral_mono _ le_rfl
    apply simple_func.monotone_eapprox
    assumption
    
  congr
  funext μ
  symm
  apply lintegral_eq_supr_eapprox_lintegral
  exact hf

/-- Monadic bind on `measure`, only works in the category of measurable spaces and measurable
functions. When the function `f` is not measurable the result is not well defined. -/
def bind (m : Measure α) (f : α → Measure β) : Measure β :=
  join (map f m)

@[simp]
theorem bind_zero_left (f : α → Measure β) : bind 0 f = 0 := by
  simp [← bind]

@[simp]
theorem bind_zero_right (m : Measure α) : bind m (0 : α → Measure β) = 0 := by
  ext1 s hs
  simp only [← bind, ← hs, ← join_apply, ← coe_zero, ← Pi.zero_apply]
  rw [lintegral_map (measurable_coe hs) measurable_zero]
  simp

@[simp]
theorem bind_zero_right' (m : Measure α) : bind m (fun _ => 0 : α → Measure β) = 0 :=
  bind_zero_right m

@[simp]
theorem bind_apply {m : Measure α} {f : α → Measure β} {s : Set β} (hs : MeasurableSet s) (hf : Measurable f) :
    bind m f s = ∫⁻ a, f a s ∂m := by
  rw [bind, join_apply hs, lintegral_map (measurable_coe hs) hf]

theorem measurable_bind' {g : α → Measure β} (hg : Measurable g) : Measurable fun m => bind m g :=
  measurable_join.comp (measurable_map _ hg)

theorem lintegral_bind {m : Measure α} {μ : α → Measure β} {f : β → ℝ≥0∞} (hμ : Measurable μ) (hf : Measurable f) :
    (∫⁻ x, f x ∂bind m μ) = ∫⁻ a, ∫⁻ x, f x ∂μ a ∂m :=
  (lintegral_join hf).trans (lintegral_map (measurable_lintegral hf) hμ)

theorem bind_bind {γ} [MeasurableSpace γ] {m : Measure α} {f : α → Measure β} {g : β → Measure γ} (hf : Measurable f)
    (hg : Measurable g) : bind (bind m f) g = bind m fun a => bind (f a) g :=
  measure.ext fun s hs => by
    rw [bind_apply hs hg, bind_apply hs ((measurable_bind' hg).comp hf), lintegral_bind hf]
    · congr
      funext a
      exact (bind_apply hs hg).symm
      
    exact (measurable_coe hs).comp hg

theorem bind_dirac {f : α → Measure β} (hf : Measurable f) (a : α) : bind (dirac a) f = f a :=
  measure.ext fun s hs => by
    rw [bind_apply hs hf, lintegral_dirac' a ((measurable_coe hs).comp hf)]

theorem dirac_bind {m : Measure α} : bind m dirac = m :=
  measure.ext fun s hs => by
    simp [← bind_apply hs measurable_dirac, ← dirac_apply' _ hs, ← lintegral_indicator 1 hs]

theorem join_eq_bind (μ : Measure (Measure α)) : join μ = bind μ id := by
  rw [bind, map_id]

theorem join_map_map {f : α → β} (hf : Measurable f) (μ : Measure (Measure α)) :
    join (map (map f) μ) = map f (join μ) :=
  measure.ext fun s hs => by
    rw [join_apply hs, map_apply hf hs, join_apply, lintegral_map (measurable_coe hs) (measurable_map f hf)]
    · congr
      funext ν
      exact map_apply hf hs
      
    exact hf hs

theorem join_map_join (μ : Measure (Measure (Measure α))) : join (map join μ) = join (join μ) := by
  show bind μ join = join (join μ)
  rw [join_eq_bind, join_eq_bind, bind_bind measurable_id measurable_id]
  apply congr_arg (bind μ)
  funext ν
  exact join_eq_bind ν

theorem join_map_dirac (μ : Measure α) : join (map dirac μ) = μ :=
  dirac_bind

theorem join_dirac (μ : Measure α) : join (dirac μ) = μ :=
  Eq.trans (join_eq_bind (dirac μ)) (bind_dirac measurable_id _)

end Measureₓ

end MeasureTheory

