/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathbin.MeasureTheory.Constructions.BorelSpace
import Mathbin.Dynamics.Ergodic.MeasurePreserving
import Mathbin.Combinatorics.Pigeonhole

/-!
# Conservative systems

In this file we define `f : α → α` to be a *conservative* system w.r.t a measure `μ` if `f` is
non-singular (`measure_theory.quasi_measure_preserving`) and for every measurable set `s` of
positive measure at least one point `x ∈ s` returns back to `s` after some number of iterations of
`f`. There are several properties that look like they are stronger than this one but actually follow
from it:

* `measure_theory.conservative.frequently_measure_inter_ne_zero`,
  `measure_theory.conservative.exists_gt_measure_inter_ne_zero`: if `μ s ≠ 0`, then for infinitely
  many `n`, the measure of `s ∩ (f^[n]) ⁻¹' s` is positive.

* `measure_theory.conservative.measure_mem_forall_ge_image_not_mem_eq_zero`,
  `measure_theory.conservative.ae_mem_imp_frequently_image_mem`: a.e. every point of `s` visits `s`
  infinitely many times (Poincaré recurrence theorem).

We also prove the topological Poincaré recurrence theorem
`measure_theory.conservative.ae_frequently_mem_of_mem_nhds`. Let `f : α → α` be a conservative
dynamical system on a topological space with second countable topology and measurable open
sets. Then almost every point `x : α` is recurrent: it visits every neighborhood `s ∈ 𝓝 x`
infinitely many times.

## Tags

conservative dynamical system, Poincare recurrence theorem
-/


noncomputable section

open Classical Set Filter MeasureTheory Finset Function TopologicalSpace

open Classical TopologicalSpace

variable {ι : Type _} {α : Type _} [MeasurableSpace α] {f : α → α} {s : Set α} {μ : Measureₓ α}

namespace MeasureTheory

open Measureₓ

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (m «expr ≠ » 0)
/-- We say that a non-singular (`measure_theory.quasi_measure_preserving`) self-map is
*conservative* if for any measurable set `s` of positive measure there exists `x ∈ s` such that `x`
returns back to `s` under some iteration of `f`. -/
structure Conservative (f : α → α)
  (μ : Measure α := by
    run_tac
      volume_tac) extends
  QuasiMeasurePreserving f μ μ : Prop where
  exists_mem_image_mem : ∀ ⦃s⦄, MeasurableSet s → μ s ≠ 0 → ∃ x ∈ s, ∃ (m : _)(_ : m ≠ 0), (f^[m]) x ∈ s

/-- A self-map preserving a finite measure is conservative. -/
protected theorem MeasurePreserving.conservative [IsFiniteMeasure μ] (h : MeasurePreserving f μ μ) : Conservative f μ :=
  ⟨h.QuasiMeasurePreserving, fun s hsm h0 => h.exists_mem_image_mem hsm h0⟩

namespace Conservative

/-- The identity map is conservative w.r.t. any measure. -/
protected theorem id (μ : Measure α) : Conservative id μ :=
  { to_quasi_measure_preserving := QuasiMeasurePreserving.id μ,
    exists_mem_image_mem := fun s hs h0 =>
      let ⟨x, hx⟩ := nonempty_of_measure_ne_zero h0
      ⟨x, hx, 1, one_ne_zero, hx⟩ }

/-- If `f` is a conservative map and `s` is a measurable set of nonzero measure, then
for infinitely many values of `m` a positive measure of points `x ∈ s` returns back to `s`
after `m` iterations of `f`. -/
theorem frequently_measure_inter_ne_zero (hf : Conservative f μ) (hs : MeasurableSet s) (h0 : μ s ≠ 0) :
    ∃ᶠ m in at_top, μ (s ∩ f^[m] ⁻¹' s) ≠ 0 := by
  by_contra H
  simp only [← not_frequently, ← eventually_at_top, ← Ne.def, ← not_not] at H
  rcases H with ⟨N, hN⟩
  induction' N with N ihN
  · apply h0
    simpa using hN 0 le_rfl
    
  rw [imp_false] at ihN
  push_neg  at ihN
  rcases ihN with ⟨n, hn, hμn⟩
  set T := s ∩ ⋃ n ≥ N + 1, f^[n] ⁻¹' s
  have hT : MeasurableSet T :=
    hs.inter (MeasurableSet.bUnion (countable_encodable _) fun _ _ => hf.measurable.iterate _ hs)
  have hμT : μ T = 0 := by
    convert (measure_bUnion_null_iff <| countable_encodable _).2 hN
    rw [← inter_Union₂]
    rfl
  have : μ ((s ∩ f^[n] ⁻¹' s) \ T) ≠ 0 := by
    rwa [measure_diff_null hμT]
  rcases hf.exists_mem_image_mem ((hs.inter (hf.measurable.iterate n hs)).diff hT) this with
    ⟨x, ⟨⟨hxs, hxn⟩, hxT⟩, m, hm0, ⟨hxms, hxm⟩, hxx⟩
  refine' hxT ⟨hxs, mem_Union₂.2 ⟨n + m, _, _⟩⟩
  · exact add_le_add hn (Nat.one_le_of_lt <| pos_iff_ne_zero.2 hm0)
    
  · rwa [Set.mem_preimage, ← iterate_add_apply] at hxm
    

/-- If `f` is a conservative map and `s` is a measurable set of nonzero measure, then
for an arbitrarily large `m` a positive measure of points `x ∈ s` returns back to `s`
after `m` iterations of `f`. -/
theorem exists_gt_measure_inter_ne_zero (hf : Conservative f μ) (hs : MeasurableSet s) (h0 : μ s ≠ 0) (N : ℕ) :
    ∃ m > N, μ (s ∩ f^[m] ⁻¹' s) ≠ 0 :=
  let ⟨m, hm, hmN⟩ := ((hf.frequently_measure_inter_ne_zero hs h0).and_eventually (eventually_gt_at_top N)).exists
  ⟨m, hmN, hm⟩

/-- Poincaré recurrence theorem: given a conservative map `f` and a measurable set `s`, the set
of points `x ∈ s` such that `x` does not return to `s` after `≥ n` iterations has measure zero. -/
theorem measure_mem_forall_ge_image_not_mem_eq_zero (hf : Conservative f μ) (hs : MeasurableSet s) (n : ℕ) :
    μ ({ x ∈ s | ∀, ∀ m ≥ n, ∀, (f^[m]) x ∉ s }) = 0 := by
  by_contra H
  have : MeasurableSet (s ∩ { x | ∀, ∀ m ≥ n, ∀, (f^[m]) x ∉ s }) := by
    simp only [← set_of_forall, compl_set_of]
    exact hs.inter (MeasurableSet.bInter (countable_encodable _) fun m _ => hf.measurable.iterate m hs.compl)
  rcases(hf.exists_gt_measure_inter_ne_zero this H) n with ⟨m, hmn, hm⟩
  rcases nonempty_of_measure_ne_zero hm with ⟨x, ⟨hxs, hxn⟩, hxm, -⟩
  exact hxn m hmn.lt.le hxm

/-- Poincaré recurrence theorem: given a conservative map `f` and a measurable set `s`,
almost every point `x ∈ s` returns back to `s` infinitely many times. -/
theorem ae_mem_imp_frequently_image_mem (hf : Conservative f μ) (hs : MeasurableSet s) :
    ∀ᵐ x ∂μ, x ∈ s → ∃ᶠ n in at_top, (f^[n]) x ∈ s := by
  simp only [← frequently_at_top, ← @forall_swap (_ ∈ s), ← ae_all_iff]
  intro n
  filter_upwards [measure_zero_iff_ae_nmem.1 (hf.measure_mem_forall_ge_image_not_mem_eq_zero hs n)]
  simp

theorem inter_frequently_image_mem_ae_eq (hf : Conservative f μ) (hs : MeasurableSet s) :
    (s ∩ { x | ∃ᶠ n in at_top, (f^[n]) x ∈ s } : Set α) =ᵐ[μ] s :=
  inter_eventually_eq_left.2 <| hf.ae_mem_imp_frequently_image_mem hs

theorem measure_inter_frequently_image_mem_eq (hf : Conservative f μ) (hs : MeasurableSet s) :
    μ (s ∩ { x | ∃ᶠ n in at_top, (f^[n]) x ∈ s }) = μ s :=
  measure_congr (hf.inter_frequently_image_mem_ae_eq hs)

/-- Poincaré recurrence theorem: if `f` is a conservative dynamical system and `s` is a measurable
set, then for `μ`-a.e. `x`, if the orbit of `x` visits `s` at least once, then it visits `s`
infinitely many times.  -/
theorem ae_forall_image_mem_imp_frequently_image_mem (hf : Conservative f μ) (hs : MeasurableSet s) :
    ∀ᵐ x ∂μ, ∀ k, (f^[k]) x ∈ s → ∃ᶠ n in at_top, (f^[n]) x ∈ s := by
  refine' ae_all_iff.2 fun k => _
  refine' (hf.ae_mem_imp_frequently_image_mem (hf.measurable.iterate k hs)).mono fun x hx hk => _
  rw [← map_add_at_top_eq_nat k, frequently_map]
  refine' (hx hk).mono fun n hn => _
  rwa [add_commₓ, iterate_add_apply]

/-- If `f` is a conservative self-map and `s` is a measurable set of positive measure, then
`μ.ae`-frequently we have `x ∈ s` and `s` returns to `s` under infinitely many iterations of `f`. -/
theorem frequently_ae_mem_and_frequently_image_mem (hf : Conservative f μ) (hs : MeasurableSet s) (h0 : μ s ≠ 0) :
    ∃ᵐ x ∂μ, x ∈ s ∧ ∃ᶠ n in at_top, (f^[n]) x ∈ s :=
  ((frequently_ae_mem_iff.2 h0).and_eventually (hf.ae_mem_imp_frequently_image_mem hs)).mono fun x hx =>
    ⟨hx.1, hx.2 hx.1⟩

/-- Poincaré recurrence theorem. Let `f : α → α` be a conservative dynamical system on a topological
space with second countable topology and measurable open sets. Then almost every point `x : α`
is recurrent: it visits every neighborhood `s ∈ 𝓝 x` infinitely many times. -/
theorem ae_frequently_mem_of_mem_nhds [TopologicalSpace α] [SecondCountableTopology α] [OpensMeasurableSpace α]
    {f : α → α} {μ : Measure α} (h : Conservative f μ) : ∀ᵐ x ∂μ, ∀, ∀ s ∈ 𝓝 x, ∀, ∃ᶠ n in at_top, (f^[n]) x ∈ s := by
  have : ∀, ∀ s ∈ countable_basis α, ∀, ∀ᵐ x ∂μ, x ∈ s → ∃ᶠ n in at_top, (f^[n]) x ∈ s := fun s hs =>
    h.ae_mem_imp_frequently_image_mem (is_open_of_mem_countable_basis hs).MeasurableSet
  refine' ((ae_ball_iff <| countable_countable_basis α).2 this).mono fun x hx s hs => _
  rcases(is_basis_countable_basis α).mem_nhds_iff.1 hs with ⟨o, hoS, hxo, hos⟩
  exact (hx o hoS hxo).mono fun n hn => hos hn

/-- Iteration of a conservative system is a conservative system. -/
protected theorem iterate (hf : Conservative f μ) (n : ℕ) : Conservative (f^[n]) μ := by
  cases n
  · exact conservative.id μ
    
  -- Discharge the trivial case `n = 0`
  refine' ⟨hf.1.iterate _, fun s hs hs0 => _⟩
  rcases(hf.frequently_ae_mem_and_frequently_image_mem hs hs0).exists with ⟨x, hxs, hx⟩
  /- We take a point `x ∈ s` such that `f^[k] x ∈ s` for infinitely many values of `k`,
    then we choose two of these values `k < l` such that `k ≡ l [MOD (n + 1)]`.
    Then `f^[k] x ∈ s` and `(f^[n + 1])^[(l - k) / (n + 1)] (f^[k] x) = f^[l] x ∈ s`. -/
  rw [Nat.frequently_at_top_iff_infinite] at hx
  rcases Nat.exists_lt_modeq_of_infinite hx n.succ_pos with ⟨k, hk, l, hl, hkl, hn⟩
  set m := (l - k) / (n + 1)
  have : (n + 1) * m = l - k := by
    apply Nat.mul_div_cancel'ₓ
    exact (Nat.modeq_iff_dvd' hkl.le).1 hn
  refine' ⟨(f^[k]) x, hk, m, _, _⟩
  · intro hm
    rw [hm, mul_zero, eq_comm, tsub_eq_zero_iff_le] at this
    exact this.not_lt hkl
    
  · rwa [← iterate_mul, this, ← iterate_add_apply, tsub_add_cancel_of_le]
    exact hkl.le
    

end Conservative

end MeasureTheory

