/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Yury Kudryashov, Heather Macbeth
-/
import Mathbin.MeasureTheory.Integral.MeanInequalities
import Mathbin.Topology.ContinuousFunction.Compact
import Mathbin.Topology.MetricSpace.Metrizable

/-!
# Density of simple functions

Show that each Borel measurable function can be approximated pointwise
by a sequence of simple functions.

## Main definitions

* `measure_theory.simple_func.nearest_pt (e : ℕ → α) (N : ℕ) : α →ₛ ℕ`: the `simple_func` sending
  each `x : α` to the point `e k` which is the nearest to `x` among `e 0`, ..., `e N`.
* `measure_theory.simple_func.approx_on (f : β → α) (hf : measurable f) (s : set α) (y₀ : α)
  (h₀ : y₀ ∈ s) [separable_space s] (n : ℕ) : β →ₛ α` : a simple function that takes values in `s`
  and approximates `f`.

## Main results

* `tendsto_approx_on` (pointwise convergence): If `f x ∈ s`, then the sequence of simple
  approximations `measure_theory.simple_func.approx_on f hf s y₀ h₀ n`, evaluated at `x`,
  tends to `f x` as `n` tends to `∞`.

## Notations

* `α →ₛ β` (local notation): the type of simple functions `α → β`.
-/


open Set Function Filter TopologicalSpace Ennreal Emetric Finset

open Classical TopologicalSpace Ennreal MeasureTheory BigOperators

variable {α β ι E F 𝕜 : Type _}

noncomputable section

namespace MeasureTheory

-- mathport name: «expr →ₛ »
local infixr:25 " →ₛ " => SimpleFunc

namespace SimpleFunc

/-! ### Pointwise approximation by simple functions -/


variable [MeasurableSpace α] [PseudoEmetricSpace α] [OpensMeasurableSpace α]

/-- `nearest_pt_ind e N x` is the index `k` such that `e k` is the nearest point to `x` among the
points `e 0`, ..., `e N`. If more than one point are at the same distance from `x`, then
`nearest_pt_ind e N x` returns the least of their indexes. -/
noncomputable def nearestPtInd (e : ℕ → α) : ℕ → α →ₛ ℕ
  | 0 => const α 0
  | N + 1 =>
    piecewise (⋂ k ≤ N, { x | edist (e (N + 1)) x < edist (e k) x })
      (MeasurableSet.Inter fun k =>
        MeasurableSet.Inter_Prop fun hk => measurable_set_lt measurable_edist_right measurable_edist_right)
      (const α <| N + 1) (nearest_pt_ind N)

/-- `nearest_pt e N x` is the nearest point to `x` among the points `e 0`, ..., `e N`. If more than
one point are at the same distance from `x`, then `nearest_pt e N x` returns the point with the
least possible index. -/
noncomputable def nearestPt (e : ℕ → α) (N : ℕ) : α →ₛ α :=
  (nearestPtInd e N).map e

@[simp]
theorem nearest_pt_ind_zero (e : ℕ → α) : nearestPtInd e 0 = const α 0 :=
  rfl

@[simp]
theorem nearest_pt_zero (e : ℕ → α) : nearestPt e 0 = const α (e 0) :=
  rfl

theorem nearest_pt_ind_succ (e : ℕ → α) (N : ℕ) (x : α) :
    nearestPtInd e (N + 1) x =
      if ∀, ∀ k ≤ N, ∀, edist (e (N + 1)) x < edist (e k) x then N + 1 else nearestPtInd e N x :=
  by
  simp only [← nearest_pt_ind, ← coe_piecewise, ← Set.piecewise]
  congr
  simp

theorem nearest_pt_ind_le (e : ℕ → α) (N : ℕ) (x : α) : nearestPtInd e N x ≤ N := by
  induction' N with N ihN
  · simp
    
  simp only [← nearest_pt_ind_succ]
  split_ifs
  exacts[le_rfl, ihN.trans N.le_succ]

theorem edist_nearest_pt_le (e : ℕ → α) (x : α) {k N : ℕ} (hk : k ≤ N) : edist (nearestPt e N x) x ≤ edist (e k) x := by
  induction' N with N ihN generalizing k
  · simp [← nonpos_iff_eq_zero.1 hk, ← le_reflₓ]
    
  · simp only [← nearest_pt, ← nearest_pt_ind_succ, ← map_apply]
    split_ifs
    · rcases hk.eq_or_lt with (rfl | hk)
      exacts[le_rfl, (h k (Nat.lt_succ_iffₓ.1 hk)).le]
      
    · push_neg  at h
      rcases h with ⟨l, hlN, hxl⟩
      rcases hk.eq_or_lt with (rfl | hk)
      exacts[(ihN hlN).trans hxl, ihN (Nat.lt_succ_iffₓ.1 hk)]
      
    

theorem tendsto_nearest_pt {e : ℕ → α} {x : α} (hx : x ∈ Closure (range e)) :
    Tendsto (fun N => nearestPt e N x) atTop (𝓝 x) := by
  refine' (at_top_basis.tendsto_iff nhds_basis_eball).2 fun ε hε => _
  rcases Emetric.mem_closure_iff.1 hx ε hε with ⟨_, ⟨N, rfl⟩, hN⟩
  rw [edist_comm] at hN
  exact ⟨N, trivialₓ, fun n hn => (edist_nearest_pt_le e x hn).trans_lt hN⟩

variable [MeasurableSpace β] {f : β → α}

/-- Approximate a measurable function by a sequence of simple functions `F n` such that
`F n x ∈ s`. -/
noncomputable def approxOn (f : β → α) (hf : Measurable f) (s : Set α) (y₀ : α) (h₀ : y₀ ∈ s) [SeparableSpace s]
    (n : ℕ) : β →ₛ α :=
  have : Nonempty s := ⟨⟨y₀, h₀⟩⟩
  comp (nearest_pt (fun k => Nat.casesOn k y₀ (coe ∘ dense_seq s) : ℕ → α) n) f hf

@[simp]
theorem approx_on_zero {f : β → α} (hf : Measurable f) {s : Set α} {y₀ : α} (h₀ : y₀ ∈ s) [SeparableSpace s] (x : β) :
    approxOn f hf s y₀ h₀ 0 x = y₀ :=
  rfl

theorem approx_on_mem {f : β → α} (hf : Measurable f) {s : Set α} {y₀ : α} (h₀ : y₀ ∈ s) [SeparableSpace s] (n : ℕ)
    (x : β) : approxOn f hf s y₀ h₀ n x ∈ s := by
  have : Nonempty s := ⟨⟨y₀, h₀⟩⟩
  suffices ∀ n, (Nat.casesOn n y₀ (coe ∘ dense_seq s) : α) ∈ s by
    apply this
  rintro (_ | n)
  exacts[h₀, Subtype.mem _]

@[simp]
theorem approx_on_comp {γ : Type _} [MeasurableSpace γ] {f : β → α} (hf : Measurable f) {g : γ → β} (hg : Measurable g)
    {s : Set α} {y₀ : α} (h₀ : y₀ ∈ s) [SeparableSpace s] (n : ℕ) :
    approxOn (f ∘ g) (hf.comp hg) s y₀ h₀ n = (approxOn f hf s y₀ h₀ n).comp g hg :=
  rfl

theorem tendsto_approx_on {f : β → α} (hf : Measurable f) {s : Set α} {y₀ : α} (h₀ : y₀ ∈ s) [SeparableSpace s] {x : β}
    (hx : f x ∈ Closure s) : Tendsto (fun n => approxOn f hf s y₀ h₀ n x) atTop (𝓝 <| f x) := by
  have : Nonempty s := ⟨⟨y₀, h₀⟩⟩
  rw [← @Subtype.range_coe _ s, ← image_univ, ← (dense_range_dense_seq s).closure_eq] at hx
  simp only [← approx_on, ← coe_comp]
  refine' tendsto_nearest_pt (closure_minimal _ is_closed_closure hx)
  simp only [← Nat.range_cases_on, ← closure_union, ← range_comp coe]
  exact subset.trans (image_closure_subset_closure_image continuous_subtype_coe) (subset_union_right _ _)

theorem edist_approx_on_mono {f : β → α} (hf : Measurable f) {s : Set α} {y₀ : α} (h₀ : y₀ ∈ s) [SeparableSpace s]
    (x : β) {m n : ℕ} (h : m ≤ n) : edist (approxOn f hf s y₀ h₀ n x) (f x) ≤ edist (approxOn f hf s y₀ h₀ m x) (f x) :=
  by
  dsimp' only [← approx_on, ← coe_comp, ← (· ∘ ·)]
  exact edist_nearest_pt_le _ _ ((nearest_pt_ind_le _ _ _).trans h)

theorem edist_approx_on_le {f : β → α} (hf : Measurable f) {s : Set α} {y₀ : α} (h₀ : y₀ ∈ s) [SeparableSpace s] (x : β)
    (n : ℕ) : edist (approxOn f hf s y₀ h₀ n x) (f x) ≤ edist y₀ (f x) :=
  edist_approx_on_mono hf h₀ x (zero_le n)

theorem edist_approx_on_y0_le {f : β → α} (hf : Measurable f) {s : Set α} {y₀ : α} (h₀ : y₀ ∈ s) [SeparableSpace s]
    (x : β) (n : ℕ) : edist y₀ (approxOn f hf s y₀ h₀ n x) ≤ edist y₀ (f x) + edist y₀ (f x) :=
  calc
    edist y₀ (approxOn f hf s y₀ h₀ n x) ≤ edist y₀ (f x) + edist (approxOn f hf s y₀ h₀ n x) (f x) :=
      edist_triangle_right _ _ _
    _ ≤ edist y₀ (f x) + edist y₀ (f x) := add_le_add_left (edist_approx_on_le hf h₀ x n) _
    

end SimpleFunc

end MeasureTheory

