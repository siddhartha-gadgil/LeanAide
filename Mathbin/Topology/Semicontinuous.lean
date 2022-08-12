/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathbin.Algebra.IndicatorFunction
import Mathbin.Topology.Algebra.Group
import Mathbin.Topology.ContinuousOn
import Mathbin.Topology.Instances.Ennreal

/-!
# Semicontinuous maps

A function `f` from a topological space `α` to an ordered space `β` is lower semicontinuous at a
point `x` if, for any `y < f x`, for any `x'` close enough to `x`, one has `f x' > y`. In other
words, `f` can jump up, but it can not jump down.

Upper semicontinuous functions are defined similarly.

This file introduces these notions, and a basic API around them mimicking the API for continuous
functions.

## Main definitions and results

We introduce 4 definitions related to lower semicontinuity:
* `lower_semicontinuous_within_at f s x`
* `lower_semicontinuous_at f x`
* `lower_semicontinuous_on f s`
* `lower_semicontinuous f`

We build a basic API using dot notation around these notions, and we prove that
* constant functions are lower semicontinuous;
* `indicator s (λ _, y)` is lower semicontinuous when `s` is open and `0 ≤ y`, or when `s` is closed
  and `y ≤ 0`;
* continuous functions are lower semicontinuous;
* composition with a continuous monotone functions maps lower semicontinuous functions to lower
  semicontinuous functions. If the function is anti-monotone, it instead maps lower semicontinuous
  functions to upper semicontinuous functions;
* a sum of two (or finitely many) lower semicontinuous functions is lower semicontinuous;
* a supremum of a family of lower semicontinuous functions is lower semicontinuous;
* An infinite sum of `ℝ≥0∞`-valued lower semicontinuous functions is lower semicontinuous.

Similar results are stated and proved for upper semicontinuity.

We also prove that a function is continuous if and only if it is both lower and upper
semicontinuous.

## Implementation details

All the nontrivial results for upper semicontinuous functions are deduced from the corresponding
ones for lower semicontinuous functions using `order_dual`.

-/


open TopologicalSpace BigOperators Ennreal

open Set

variable {α : Type _} [TopologicalSpace α] {β : Type _} [Preorderₓ β] {f g : α → β} {x : α} {s t : Set α} {y z : β}

/-! ### Main definitions -/


/-- A real function `f` is lower semicontinuous at `x` within a set `s` if, for any `ε > 0`, for all
`x'` close enough to `x` in  `s`, then `f x'` is at least `f x - ε`. We formulate this in a general
preordered space, using an arbitrary `y < f x` instead of `f x - ε`. -/
def LowerSemicontinuousWithinAt (f : α → β) (s : Set α) (x : α) :=
  ∀, ∀ y < f x, ∀, ∀ᶠ x' in 𝓝[s] x, y < f x'

/-- A real function `f` is lower semicontinuous on a set `s` if, for any `ε > 0`, for any `x ∈ s`,
for all `x'` close enough to `x` in `s`, then `f x'` is at least `f x - ε`. We formulate this in
a general preordered space, using an arbitrary `y < f x` instead of `f x - ε`.-/
def LowerSemicontinuousOn (f : α → β) (s : Set α) :=
  ∀, ∀ x ∈ s, ∀, LowerSemicontinuousWithinAt f s x

/-- A real function `f` is lower semicontinuous at `x` if, for any `ε > 0`, for all `x'` close
enough to `x`, then `f x'` is at least `f x - ε`. We formulate this in a general preordered space,
using an arbitrary `y < f x` instead of `f x - ε`. -/
def LowerSemicontinuousAt (f : α → β) (x : α) :=
  ∀, ∀ y < f x, ∀, ∀ᶠ x' in 𝓝 x, y < f x'

/-- A real function `f` is lower semicontinuous if, for any `ε > 0`, for any `x`, for all `x'` close
enough to `x`, then `f x'` is at least `f x - ε`. We formulate this in a general preordered space,
using an arbitrary `y < f x` instead of `f x - ε`. -/
def LowerSemicontinuous (f : α → β) :=
  ∀ x, LowerSemicontinuousAt f x

/-- A real function `f` is upper semicontinuous at `x` within a set `s` if, for any `ε > 0`, for all
`x'` close enough to `x` in  `s`, then `f x'` is at most `f x + ε`. We formulate this in a general
preordered space, using an arbitrary `y > f x` instead of `f x + ε`. -/
def UpperSemicontinuousWithinAt (f : α → β) (s : Set α) (x : α) :=
  ∀ y, f x < y → ∀ᶠ x' in 𝓝[s] x, f x' < y

/-- A real function `f` is upper semicontinuous on a set `s` if, for any `ε > 0`, for any `x ∈ s`,
for all `x'` close enough to `x` in `s`, then `f x'` is at most `f x + ε`. We formulate this in a
general preordered space, using an arbitrary `y > f x` instead of `f x + ε`.-/
def UpperSemicontinuousOn (f : α → β) (s : Set α) :=
  ∀, ∀ x ∈ s, ∀, UpperSemicontinuousWithinAt f s x

/-- A real function `f` is upper semicontinuous at `x` if, for any `ε > 0`, for all `x'` close
enough to `x`, then `f x'` is at most `f x + ε`. We formulate this in a general preordered space,
using an arbitrary `y > f x` instead of `f x + ε`. -/
def UpperSemicontinuousAt (f : α → β) (x : α) :=
  ∀ y, f x < y → ∀ᶠ x' in 𝓝 x, f x' < y

/-- A real function `f` is upper semicontinuous if, for any `ε > 0`, for any `x`, for all `x'`
close enough to `x`, then `f x'` is at most `f x + ε`. We formulate this in a general preordered
space, using an arbitrary `y > f x` instead of `f x + ε`.-/
def UpperSemicontinuous (f : α → β) :=
  ∀ x, UpperSemicontinuousAt f x

/-!
### Lower semicontinuous functions
-/


/-! #### Basic dot notation interface for lower semicontinuity -/


theorem LowerSemicontinuousWithinAt.mono (h : LowerSemicontinuousWithinAt f s x) (hst : t ⊆ s) :
    LowerSemicontinuousWithinAt f t x := fun y hy => Filter.Eventually.filter_mono (nhds_within_mono _ hst) (h y hy)

theorem lower_semicontinuous_within_at_univ_iff : LowerSemicontinuousWithinAt f Univ x ↔ LowerSemicontinuousAt f x := by
  simp [← LowerSemicontinuousWithinAt, ← LowerSemicontinuousAt, ← nhds_within_univ]

theorem LowerSemicontinuousAt.lower_semicontinuous_within_at (s : Set α) (h : LowerSemicontinuousAt f x) :
    LowerSemicontinuousWithinAt f s x := fun y hy => Filter.Eventually.filter_mono nhds_within_le_nhds (h y hy)

theorem LowerSemicontinuousOn.lower_semicontinuous_within_at (h : LowerSemicontinuousOn f s) (hx : x ∈ s) :
    LowerSemicontinuousWithinAt f s x :=
  h x hx

theorem LowerSemicontinuousOn.mono (h : LowerSemicontinuousOn f s) (hst : t ⊆ s) : LowerSemicontinuousOn f t :=
  fun x hx => (h x (hst hx)).mono hst

theorem lower_semicontinuous_on_univ_iff : LowerSemicontinuousOn f Univ ↔ LowerSemicontinuous f := by
  simp [← LowerSemicontinuousOn, ← LowerSemicontinuous, ← lower_semicontinuous_within_at_univ_iff]

theorem LowerSemicontinuous.lower_semicontinuous_at (h : LowerSemicontinuous f) (x : α) : LowerSemicontinuousAt f x :=
  h x

theorem LowerSemicontinuous.lower_semicontinuous_within_at (h : LowerSemicontinuous f) (s : Set α) (x : α) :
    LowerSemicontinuousWithinAt f s x :=
  (h x).LowerSemicontinuousWithinAt s

theorem LowerSemicontinuous.lower_semicontinuous_on (h : LowerSemicontinuous f) (s : Set α) :
    LowerSemicontinuousOn f s := fun x hx => h.LowerSemicontinuousWithinAt s x

/-! #### Constants -/


theorem lower_semicontinuous_within_at_const : LowerSemicontinuousWithinAt (fun x => z) s x := fun y hy =>
  Filter.eventually_of_forall fun x => hy

theorem lower_semicontinuous_at_const : LowerSemicontinuousAt (fun x => z) x := fun y hy =>
  Filter.eventually_of_forall fun x => hy

theorem lower_semicontinuous_on_const : LowerSemicontinuousOn (fun x => z) s := fun x hx =>
  lower_semicontinuous_within_at_const

theorem lower_semicontinuous_const : LowerSemicontinuous fun x : α => z := fun x => lower_semicontinuous_at_const

/-! #### Indicators -/


section

variable [Zero β]

theorem IsOpen.lower_semicontinuous_indicator (hs : IsOpen s) (hy : 0 ≤ y) :
    LowerSemicontinuous (indicatorₓ s fun x => y) := by
  intro x z hz
  by_cases' h : x ∈ s <;> simp [← h] at hz
  · filter_upwards [hs.mem_nhds h]
    simp (config := { contextual := true })[← hz]
    
  · apply Filter.eventually_of_forall fun x' => _
    by_cases' h' : x' ∈ s <;> simp [← h', ← hz.trans_le hy, ← hz]
    

theorem IsOpen.lower_semicontinuous_on_indicator (hs : IsOpen s) (hy : 0 ≤ y) :
    LowerSemicontinuousOn (indicatorₓ s fun x => y) t :=
  (hs.lower_semicontinuous_indicator hy).LowerSemicontinuousOn t

theorem IsOpen.lower_semicontinuous_at_indicator (hs : IsOpen s) (hy : 0 ≤ y) :
    LowerSemicontinuousAt (indicatorₓ s fun x => y) x :=
  (hs.lower_semicontinuous_indicator hy).LowerSemicontinuousAt x

theorem IsOpen.lower_semicontinuous_within_at_indicator (hs : IsOpen s) (hy : 0 ≤ y) :
    LowerSemicontinuousWithinAt (indicatorₓ s fun x => y) t x :=
  (hs.lower_semicontinuous_indicator hy).LowerSemicontinuousWithinAt t x

theorem IsClosed.lower_semicontinuous_indicator (hs : IsClosed s) (hy : y ≤ 0) :
    LowerSemicontinuous (indicatorₓ s fun x => y) := by
  intro x z hz
  by_cases' h : x ∈ s <;> simp [← h] at hz
  · apply Filter.eventually_of_forall fun x' => _
    by_cases' h' : x' ∈ s <;> simp [← h', ← hz, ← hz.trans_le hy]
    
  · filter_upwards [hs.is_open_compl.mem_nhds h]
    simp (config := { contextual := true })[← hz]
    

theorem IsClosed.lower_semicontinuous_on_indicator (hs : IsClosed s) (hy : y ≤ 0) :
    LowerSemicontinuousOn (indicatorₓ s fun x => y) t :=
  (hs.lower_semicontinuous_indicator hy).LowerSemicontinuousOn t

theorem IsClosed.lower_semicontinuous_at_indicator (hs : IsClosed s) (hy : y ≤ 0) :
    LowerSemicontinuousAt (indicatorₓ s fun x => y) x :=
  (hs.lower_semicontinuous_indicator hy).LowerSemicontinuousAt x

theorem IsClosed.lower_semicontinuous_within_at_indicator (hs : IsClosed s) (hy : y ≤ 0) :
    LowerSemicontinuousWithinAt (indicatorₓ s fun x => y) t x :=
  (hs.lower_semicontinuous_indicator hy).LowerSemicontinuousWithinAt t x

end

/-! #### Relationship with continuity -/


theorem lower_semicontinuous_iff_is_open : LowerSemicontinuous f ↔ ∀ y, IsOpen (f ⁻¹' Ioi y) :=
  ⟨fun H y => is_open_iff_mem_nhds.2 fun x hx => H x y hx, fun H x y y_lt => IsOpen.mem_nhds (H y) y_lt⟩

theorem LowerSemicontinuous.is_open_preimage (hf : LowerSemicontinuous f) (y : β) : IsOpen (f ⁻¹' Ioi y) :=
  lower_semicontinuous_iff_is_open.1 hf y

section

variable {γ : Type _} [LinearOrderₓ γ] [TopologicalSpace γ] [OrderTopology γ]

theorem ContinuousWithinAt.lower_semicontinuous_within_at {f : α → γ} (h : ContinuousWithinAt f s x) :
    LowerSemicontinuousWithinAt f s x := fun y hy => h (Ioi_mem_nhds hy)

theorem ContinuousAt.lower_semicontinuous_at {f : α → γ} (h : ContinuousAt f x) : LowerSemicontinuousAt f x :=
  fun y hy => h (Ioi_mem_nhds hy)

theorem ContinuousOn.lower_semicontinuous_on {f : α → γ} (h : ContinuousOn f s) : LowerSemicontinuousOn f s :=
  fun x hx => (h x hx).LowerSemicontinuousWithinAt

theorem Continuous.lower_semicontinuous {f : α → γ} (h : Continuous f) : LowerSemicontinuous f := fun x =>
  h.ContinuousAt.LowerSemicontinuousAt

end

/-! ### Composition -/


section

variable {γ : Type _} [LinearOrderₓ γ] [TopologicalSpace γ] [OrderTopology γ]

variable {δ : Type _} [LinearOrderₓ δ] [TopologicalSpace δ] [OrderTopology δ]

theorem ContinuousAt.comp_lower_semicontinuous_within_at {g : γ → δ} {f : α → γ} (hg : ContinuousAt g (f x))
    (hf : LowerSemicontinuousWithinAt f s x) (gmon : Monotone g) : LowerSemicontinuousWithinAt (g ∘ f) s x := by
  intro y hy
  by_cases' h : ∃ l, l < f x
  · obtain ⟨z, zlt, hz⟩ : ∃ z < f x, Ioc z (f x) ⊆ g ⁻¹' Ioi y := exists_Ioc_subset_of_mem_nhds (hg (Ioi_mem_nhds hy)) h
    filter_upwards [hf z zlt] with a ha
    calc y < g (min (f x) (f a)) :=
        hz
          (by
            simp [← zlt, ← ha, ← le_reflₓ])_ ≤ g (f a) :=
        gmon (min_le_rightₓ _ _)
    
  · simp only [← not_exists, ← not_ltₓ] at h
    exact Filter.eventually_of_forall fun a => hy.trans_le (gmon (h (f a)))
    

theorem ContinuousAt.comp_lower_semicontinuous_at {g : γ → δ} {f : α → γ} (hg : ContinuousAt g (f x))
    (hf : LowerSemicontinuousAt f x) (gmon : Monotone g) : LowerSemicontinuousAt (g ∘ f) x := by
  simp only [lower_semicontinuous_within_at_univ_iff] at hf⊢
  exact hg.comp_lower_semicontinuous_within_at hf gmon

theorem Continuous.comp_lower_semicontinuous_on {g : γ → δ} {f : α → γ} (hg : Continuous g)
    (hf : LowerSemicontinuousOn f s) (gmon : Monotone g) : LowerSemicontinuousOn (g ∘ f) s := fun x hx =>
  hg.ContinuousAt.comp_lower_semicontinuous_within_at (hf x hx) gmon

theorem Continuous.comp_lower_semicontinuous {g : γ → δ} {f : α → γ} (hg : Continuous g) (hf : LowerSemicontinuous f)
    (gmon : Monotone g) : LowerSemicontinuous (g ∘ f) := fun x =>
  hg.ContinuousAt.comp_lower_semicontinuous_at (hf x) gmon

theorem ContinuousAt.comp_lower_semicontinuous_within_at_antitone {g : γ → δ} {f : α → γ} (hg : ContinuousAt g (f x))
    (hf : LowerSemicontinuousWithinAt f s x) (gmon : Antitone g) : UpperSemicontinuousWithinAt (g ∘ f) s x :=
  @ContinuousAt.comp_lower_semicontinuous_within_at α _ x s γ _ _ _ δᵒᵈ _ _ _ g f hg hf gmon

theorem ContinuousAt.comp_lower_semicontinuous_at_antitone {g : γ → δ} {f : α → γ} (hg : ContinuousAt g (f x))
    (hf : LowerSemicontinuousAt f x) (gmon : Antitone g) : UpperSemicontinuousAt (g ∘ f) x :=
  @ContinuousAt.comp_lower_semicontinuous_at α _ x γ _ _ _ δᵒᵈ _ _ _ g f hg hf gmon

theorem Continuous.comp_lower_semicontinuous_on_antitone {g : γ → δ} {f : α → γ} (hg : Continuous g)
    (hf : LowerSemicontinuousOn f s) (gmon : Antitone g) : UpperSemicontinuousOn (g ∘ f) s := fun x hx =>
  hg.ContinuousAt.comp_lower_semicontinuous_within_at_antitone (hf x hx) gmon

theorem Continuous.comp_lower_semicontinuous_antitone {g : γ → δ} {f : α → γ} (hg : Continuous g)
    (hf : LowerSemicontinuous f) (gmon : Antitone g) : UpperSemicontinuous (g ∘ f) := fun x =>
  hg.ContinuousAt.comp_lower_semicontinuous_at_antitone (hf x) gmon

end

/-! #### Addition -/


section

variable {ι : Type _} {γ : Type _} [LinearOrderedAddCommMonoid γ] [TopologicalSpace γ] [OrderTopology γ]

/-- The sum of two lower semicontinuous functions is lower semicontinuous. Formulated with an
explicit continuity assumption on addition, for application to `ereal`. The unprimed version of
the lemma uses `[has_continuous_add]`. -/
theorem LowerSemicontinuousWithinAt.add' {f g : α → γ} (hf : LowerSemicontinuousWithinAt f s x)
    (hg : LowerSemicontinuousWithinAt g s x) (hcont : ContinuousAt (fun p : γ × γ => p.1 + p.2) (f x, g x)) :
    LowerSemicontinuousWithinAt (fun z => f z + g z) s x := by
  intro y hy
  obtain ⟨u, v, u_open, xu, v_open, xv, h⟩ :
    ∃ u v : Set γ, IsOpen u ∧ f x ∈ u ∧ IsOpen v ∧ g x ∈ v ∧ u ×ˢ v ⊆ { p : γ × γ | y < p.fst + p.snd } :=
    mem_nhds_prod_iff'.1 (hcont (is_open_Ioi.mem_nhds hy))
  by_cases' hx₁ : ∃ l, l < f x
  · obtain ⟨z₁, z₁lt, h₁⟩ : ∃ z₁ < f x, Ioc z₁ (f x) ⊆ u := exists_Ioc_subset_of_mem_nhds (u_open.mem_nhds xu) hx₁
    by_cases' hx₂ : ∃ l, l < g x
    · obtain ⟨z₂, z₂lt, h₂⟩ : ∃ z₂ < g x, Ioc z₂ (g x) ⊆ v := exists_Ioc_subset_of_mem_nhds (v_open.mem_nhds xv) hx₂
      filter_upwards [hf z₁ z₁lt, hg z₂ z₂lt] with z h₁z h₂z
      have A1 : min (f z) (f x) ∈ u := by
        by_cases' H : f z ≤ f x
        · simp [← H]
          exact h₁ ⟨h₁z, H⟩
          
        · simp [← le_of_not_leₓ H]
          exact h₁ ⟨z₁lt, le_rfl⟩
          
      have A2 : min (g z) (g x) ∈ v := by
        by_cases' H : g z ≤ g x
        · simp [← H]
          exact h₂ ⟨h₂z, H⟩
          
        · simp [← le_of_not_leₓ H]
          exact h₂ ⟨z₂lt, le_rfl⟩
          
      have : (min (f z) (f x), min (g z) (g x)) ∈ u ×ˢ v := ⟨A1, A2⟩
      calc y < min (f z) (f x) + min (g z) (g x) := h this _ ≤ f z + g z :=
          add_le_add (min_le_leftₓ _ _) (min_le_leftₓ _ _)
      
    · simp only [← not_exists, ← not_ltₓ] at hx₂
      filter_upwards [hf z₁ z₁lt] with z h₁z
      have A1 : min (f z) (f x) ∈ u := by
        by_cases' H : f z ≤ f x
        · simp [← H]
          exact h₁ ⟨h₁z, H⟩
          
        · simp [← le_of_not_leₓ H]
          exact h₁ ⟨z₁lt, le_rfl⟩
          
      have : (min (f z) (f x), g x) ∈ u ×ˢ v := ⟨A1, xv⟩
      calc y < min (f z) (f x) + g x := h this _ ≤ f z + g z := add_le_add (min_le_leftₓ _ _) (hx₂ (g z))
      
    
  · simp only [← not_exists, ← not_ltₓ] at hx₁
    by_cases' hx₂ : ∃ l, l < g x
    · obtain ⟨z₂, z₂lt, h₂⟩ : ∃ z₂ < g x, Ioc z₂ (g x) ⊆ v := exists_Ioc_subset_of_mem_nhds (v_open.mem_nhds xv) hx₂
      filter_upwards [hg z₂ z₂lt] with z h₂z
      have A2 : min (g z) (g x) ∈ v := by
        by_cases' H : g z ≤ g x
        · simp [← H]
          exact h₂ ⟨h₂z, H⟩
          
        · simp [← le_of_not_leₓ H]
          exact h₂ ⟨z₂lt, le_rfl⟩
          
      have : (f x, min (g z) (g x)) ∈ u ×ˢ v := ⟨xu, A2⟩
      calc y < f x + min (g z) (g x) := h this _ ≤ f z + g z := add_le_add (hx₁ (f z)) (min_le_leftₓ _ _)
      
    · simp only [← not_exists, ← not_ltₓ] at hx₁ hx₂
      apply Filter.eventually_of_forall
      intro z
      have : (f x, g x) ∈ u ×ˢ v := ⟨xu, xv⟩
      calc y < f x + g x := h this _ ≤ f z + g z := add_le_add (hx₁ (f z)) (hx₂ (g z))
      
    

/-- The sum of two lower semicontinuous functions is lower semicontinuous. Formulated with an
explicit continuity assumption on addition, for application to `ereal`. The unprimed version of
the lemma uses `[has_continuous_add]`. -/
theorem LowerSemicontinuousAt.add' {f g : α → γ} (hf : LowerSemicontinuousAt f x) (hg : LowerSemicontinuousAt g x)
    (hcont : ContinuousAt (fun p : γ × γ => p.1 + p.2) (f x, g x)) : LowerSemicontinuousAt (fun z => f z + g z) x := by
  simp_rw [← lower_semicontinuous_within_at_univ_iff] at *
  exact hf.add' hg hcont

/-- The sum of two lower semicontinuous functions is lower semicontinuous. Formulated with an
explicit continuity assumption on addition, for application to `ereal`. The unprimed version of
the lemma uses `[has_continuous_add]`. -/
theorem LowerSemicontinuousOn.add' {f g : α → γ} (hf : LowerSemicontinuousOn f s) (hg : LowerSemicontinuousOn g s)
    (hcont : ∀, ∀ x ∈ s, ∀, ContinuousAt (fun p : γ × γ => p.1 + p.2) (f x, g x)) :
    LowerSemicontinuousOn (fun z => f z + g z) s := fun x hx => (hf x hx).add' (hg x hx) (hcont x hx)

/-- The sum of two lower semicontinuous functions is lower semicontinuous. Formulated with an
explicit continuity assumption on addition, for application to `ereal`. The unprimed version of
the lemma uses `[has_continuous_add]`. -/
theorem LowerSemicontinuous.add' {f g : α → γ} (hf : LowerSemicontinuous f) (hg : LowerSemicontinuous g)
    (hcont : ∀ x, ContinuousAt (fun p : γ × γ => p.1 + p.2) (f x, g x)) : LowerSemicontinuous fun z => f z + g z :=
  fun x => (hf x).add' (hg x) (hcont x)

variable [HasContinuousAdd γ]

/-- The sum of two lower semicontinuous functions is lower semicontinuous. Formulated with
`[has_continuous_add]`. The primed version of the lemma uses an explicit continuity assumption on
addition, for application to `ereal`. -/
theorem LowerSemicontinuousWithinAt.add {f g : α → γ} (hf : LowerSemicontinuousWithinAt f s x)
    (hg : LowerSemicontinuousWithinAt g s x) : LowerSemicontinuousWithinAt (fun z => f z + g z) s x :=
  hf.add' hg continuous_add.ContinuousAt

/-- The sum of two lower semicontinuous functions is lower semicontinuous. Formulated with
`[has_continuous_add]`. The primed version of the lemma uses an explicit continuity assumption on
addition, for application to `ereal`. -/
theorem LowerSemicontinuousAt.add {f g : α → γ} (hf : LowerSemicontinuousAt f x) (hg : LowerSemicontinuousAt g x) :
    LowerSemicontinuousAt (fun z => f z + g z) x :=
  hf.add' hg continuous_add.ContinuousAt

/-- The sum of two lower semicontinuous functions is lower semicontinuous. Formulated with
`[has_continuous_add]`. The primed version of the lemma uses an explicit continuity assumption on
addition, for application to `ereal`. -/
theorem LowerSemicontinuousOn.add {f g : α → γ} (hf : LowerSemicontinuousOn f s) (hg : LowerSemicontinuousOn g s) :
    LowerSemicontinuousOn (fun z => f z + g z) s :=
  hf.add' hg fun x hx => continuous_add.ContinuousAt

/-- The sum of two lower semicontinuous functions is lower semicontinuous. Formulated with
`[has_continuous_add]`. The primed version of the lemma uses an explicit continuity assumption on
addition, for application to `ereal`. -/
theorem LowerSemicontinuous.add {f g : α → γ} (hf : LowerSemicontinuous f) (hg : LowerSemicontinuous g) :
    LowerSemicontinuous fun z => f z + g z :=
  hf.add' hg fun x => continuous_add.ContinuousAt

theorem lower_semicontinuous_within_at_sum {f : ι → α → γ} {a : Finset ι}
    (ha : ∀, ∀ i ∈ a, ∀, LowerSemicontinuousWithinAt (f i) s x) :
    LowerSemicontinuousWithinAt (fun z => ∑ i in a, f i z) s x := by
  classical
  induction' a using Finset.induction_on with i a ia IH generalizing ha
  · exact lower_semicontinuous_within_at_const
    
  · simp only [← ia, ← Finset.sum_insert, ← not_false_iff]
    exact
      LowerSemicontinuousWithinAt.add (ha _ (Finset.mem_insert_self i a))
        (IH fun j ja => ha j (Finset.mem_insert_of_mem ja))
    

theorem lower_semicontinuous_at_sum {f : ι → α → γ} {a : Finset ι} (ha : ∀, ∀ i ∈ a, ∀, LowerSemicontinuousAt (f i) x) :
    LowerSemicontinuousAt (fun z => ∑ i in a, f i z) x := by
  simp_rw [← lower_semicontinuous_within_at_univ_iff] at *
  exact lower_semicontinuous_within_at_sum ha

theorem lower_semicontinuous_on_sum {f : ι → α → γ} {a : Finset ι} (ha : ∀, ∀ i ∈ a, ∀, LowerSemicontinuousOn (f i) s) :
    LowerSemicontinuousOn (fun z => ∑ i in a, f i z) s := fun x hx =>
  lower_semicontinuous_within_at_sum fun i hi => ha i hi x hx

theorem lower_semicontinuous_sum {f : ι → α → γ} {a : Finset ι} (ha : ∀, ∀ i ∈ a, ∀, LowerSemicontinuous (f i)) :
    LowerSemicontinuous fun z => ∑ i in a, f i z := fun x => lower_semicontinuous_at_sum fun i hi => ha i hi x

end

/-! #### Supremum -/


section

variable {ι : Sort _} {δ : Type _} [CompleteLinearOrder δ]

theorem lower_semicontinuous_within_at_supr {f : ι → α → δ} (h : ∀ i, LowerSemicontinuousWithinAt (f i) s x) :
    LowerSemicontinuousWithinAt (fun x' => ⨆ i, f i x') s x := by
  intro y hy
  rcases lt_supr_iff.1 hy with ⟨i, hi⟩
  filter_upwards [h i y hi] with _ hx' using lt_supr_iff.2 ⟨i, hx'⟩

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i hi)
theorem lower_semicontinuous_within_at_bsupr {p : ι → Prop} {f : ∀ (i) (h : p i), α → δ}
    (h : ∀ i hi, LowerSemicontinuousWithinAt (f i hi) s x) :
    LowerSemicontinuousWithinAt (fun x' => ⨆ (i) (hi), f i hi x') s x :=
  lower_semicontinuous_within_at_supr fun i => lower_semicontinuous_within_at_supr fun hi => h i hi

theorem lower_semicontinuous_at_supr {f : ι → α → δ} (h : ∀ i, LowerSemicontinuousAt (f i) x) :
    LowerSemicontinuousAt (fun x' => ⨆ i, f i x') x := by
  simp_rw [← lower_semicontinuous_within_at_univ_iff] at *
  exact lower_semicontinuous_within_at_supr h

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i hi)
theorem lower_semicontinuous_at_bsupr {p : ι → Prop} {f : ∀ (i) (h : p i), α → δ}
    (h : ∀ i hi, LowerSemicontinuousAt (f i hi) x) : LowerSemicontinuousAt (fun x' => ⨆ (i) (hi), f i hi x') x :=
  lower_semicontinuous_at_supr fun i => lower_semicontinuous_at_supr fun hi => h i hi

theorem lower_semicontinuous_on_supr {f : ι → α → δ} (h : ∀ i, LowerSemicontinuousOn (f i) s) :
    LowerSemicontinuousOn (fun x' => ⨆ i, f i x') s := fun x hx => lower_semicontinuous_within_at_supr fun i => h i x hx

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i hi)
theorem lower_semicontinuous_on_bsupr {p : ι → Prop} {f : ∀ (i) (h : p i), α → δ}
    (h : ∀ i hi, LowerSemicontinuousOn (f i hi) s) : LowerSemicontinuousOn (fun x' => ⨆ (i) (hi), f i hi x') s :=
  lower_semicontinuous_on_supr fun i => lower_semicontinuous_on_supr fun hi => h i hi

theorem lower_semicontinuous_supr {f : ι → α → δ} (h : ∀ i, LowerSemicontinuous (f i)) :
    LowerSemicontinuous fun x' => ⨆ i, f i x' := fun x => lower_semicontinuous_at_supr fun i => h i x

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i hi)
theorem lower_semicontinuous_bsupr {p : ι → Prop} {f : ∀ (i) (h : p i), α → δ}
    (h : ∀ i hi, LowerSemicontinuous (f i hi)) : LowerSemicontinuous fun x' => ⨆ (i) (hi), f i hi x' :=
  lower_semicontinuous_supr fun i => lower_semicontinuous_supr fun hi => h i hi

end

/-! #### Infinite sums -/


section

variable {ι : Type _}

theorem lower_semicontinuous_within_at_tsum {f : ι → α → ℝ≥0∞} (h : ∀ i, LowerSemicontinuousWithinAt (f i) s x) :
    LowerSemicontinuousWithinAt (fun x' => ∑' i, f i x') s x := by
  simp_rw [Ennreal.tsum_eq_supr_sum]
  apply lower_semicontinuous_within_at_supr fun b => _
  exact lower_semicontinuous_within_at_sum fun i hi => h i

theorem lower_semicontinuous_at_tsum {f : ι → α → ℝ≥0∞} (h : ∀ i, LowerSemicontinuousAt (f i) x) :
    LowerSemicontinuousAt (fun x' => ∑' i, f i x') x := by
  simp_rw [← lower_semicontinuous_within_at_univ_iff] at *
  exact lower_semicontinuous_within_at_tsum h

theorem lower_semicontinuous_on_tsum {f : ι → α → ℝ≥0∞} (h : ∀ i, LowerSemicontinuousOn (f i) s) :
    LowerSemicontinuousOn (fun x' => ∑' i, f i x') s := fun x hx =>
  lower_semicontinuous_within_at_tsum fun i => h i x hx

theorem lower_semicontinuous_tsum {f : ι → α → ℝ≥0∞} (h : ∀ i, LowerSemicontinuous (f i)) :
    LowerSemicontinuous fun x' => ∑' i, f i x' := fun x => lower_semicontinuous_at_tsum fun i => h i x

end

/-!
### Upper semicontinuous functions
-/


/-! #### Basic dot notation interface for upper semicontinuity -/


theorem UpperSemicontinuousWithinAt.mono (h : UpperSemicontinuousWithinAt f s x) (hst : t ⊆ s) :
    UpperSemicontinuousWithinAt f t x := fun y hy => Filter.Eventually.filter_mono (nhds_within_mono _ hst) (h y hy)

theorem upper_semicontinuous_within_at_univ_iff : UpperSemicontinuousWithinAt f Univ x ↔ UpperSemicontinuousAt f x := by
  simp [← UpperSemicontinuousWithinAt, ← UpperSemicontinuousAt, ← nhds_within_univ]

theorem UpperSemicontinuousAt.upper_semicontinuous_within_at (s : Set α) (h : UpperSemicontinuousAt f x) :
    UpperSemicontinuousWithinAt f s x := fun y hy => Filter.Eventually.filter_mono nhds_within_le_nhds (h y hy)

theorem UpperSemicontinuousOn.upper_semicontinuous_within_at (h : UpperSemicontinuousOn f s) (hx : x ∈ s) :
    UpperSemicontinuousWithinAt f s x :=
  h x hx

theorem UpperSemicontinuousOn.mono (h : UpperSemicontinuousOn f s) (hst : t ⊆ s) : UpperSemicontinuousOn f t :=
  fun x hx => (h x (hst hx)).mono hst

theorem upper_semicontinuous_on_univ_iff : UpperSemicontinuousOn f Univ ↔ UpperSemicontinuous f := by
  simp [← UpperSemicontinuousOn, ← UpperSemicontinuous, ← upper_semicontinuous_within_at_univ_iff]

theorem UpperSemicontinuous.upper_semicontinuous_at (h : UpperSemicontinuous f) (x : α) : UpperSemicontinuousAt f x :=
  h x

theorem UpperSemicontinuous.upper_semicontinuous_within_at (h : UpperSemicontinuous f) (s : Set α) (x : α) :
    UpperSemicontinuousWithinAt f s x :=
  (h x).UpperSemicontinuousWithinAt s

theorem UpperSemicontinuous.upper_semicontinuous_on (h : UpperSemicontinuous f) (s : Set α) :
    UpperSemicontinuousOn f s := fun x hx => h.UpperSemicontinuousWithinAt s x

/-! #### Constants -/


theorem upper_semicontinuous_within_at_const : UpperSemicontinuousWithinAt (fun x => z) s x := fun y hy =>
  Filter.eventually_of_forall fun x => hy

theorem upper_semicontinuous_at_const : UpperSemicontinuousAt (fun x => z) x := fun y hy =>
  Filter.eventually_of_forall fun x => hy

theorem upper_semicontinuous_on_const : UpperSemicontinuousOn (fun x => z) s := fun x hx =>
  upper_semicontinuous_within_at_const

theorem upper_semicontinuous_const : UpperSemicontinuous fun x : α => z := fun x => upper_semicontinuous_at_const

/-! #### Indicators -/


section

variable [Zero β]

theorem IsOpen.upper_semicontinuous_indicator (hs : IsOpen s) (hy : y ≤ 0) :
    UpperSemicontinuous (indicatorₓ s fun x => y) :=
  @IsOpen.lower_semicontinuous_indicator α _ βᵒᵈ _ s y _ hs hy

theorem IsOpen.upper_semicontinuous_on_indicator (hs : IsOpen s) (hy : y ≤ 0) :
    UpperSemicontinuousOn (indicatorₓ s fun x => y) t :=
  (hs.upper_semicontinuous_indicator hy).UpperSemicontinuousOn t

theorem IsOpen.upper_semicontinuous_at_indicator (hs : IsOpen s) (hy : y ≤ 0) :
    UpperSemicontinuousAt (indicatorₓ s fun x => y) x :=
  (hs.upper_semicontinuous_indicator hy).UpperSemicontinuousAt x

theorem IsOpen.upper_semicontinuous_within_at_indicator (hs : IsOpen s) (hy : y ≤ 0) :
    UpperSemicontinuousWithinAt (indicatorₓ s fun x => y) t x :=
  (hs.upper_semicontinuous_indicator hy).UpperSemicontinuousWithinAt t x

theorem IsClosed.upper_semicontinuous_indicator (hs : IsClosed s) (hy : 0 ≤ y) :
    UpperSemicontinuous (indicatorₓ s fun x => y) :=
  @IsClosed.lower_semicontinuous_indicator α _ βᵒᵈ _ s y _ hs hy

theorem IsClosed.upper_semicontinuous_on_indicator (hs : IsClosed s) (hy : 0 ≤ y) :
    UpperSemicontinuousOn (indicatorₓ s fun x => y) t :=
  (hs.upper_semicontinuous_indicator hy).UpperSemicontinuousOn t

theorem IsClosed.upper_semicontinuous_at_indicator (hs : IsClosed s) (hy : 0 ≤ y) :
    UpperSemicontinuousAt (indicatorₓ s fun x => y) x :=
  (hs.upper_semicontinuous_indicator hy).UpperSemicontinuousAt x

theorem IsClosed.upper_semicontinuous_within_at_indicator (hs : IsClosed s) (hy : 0 ≤ y) :
    UpperSemicontinuousWithinAt (indicatorₓ s fun x => y) t x :=
  (hs.upper_semicontinuous_indicator hy).UpperSemicontinuousWithinAt t x

end

/-! #### Relationship with continuity -/


theorem upper_semicontinuous_iff_is_open : UpperSemicontinuous f ↔ ∀ y, IsOpen (f ⁻¹' Iio y) :=
  ⟨fun H y => is_open_iff_mem_nhds.2 fun x hx => H x y hx, fun H x y y_lt => IsOpen.mem_nhds (H y) y_lt⟩

theorem UpperSemicontinuous.is_open_preimage (hf : UpperSemicontinuous f) (y : β) : IsOpen (f ⁻¹' Iio y) :=
  upper_semicontinuous_iff_is_open.1 hf y

section

variable {γ : Type _} [LinearOrderₓ γ] [TopologicalSpace γ] [OrderTopology γ]

theorem ContinuousWithinAt.upper_semicontinuous_within_at {f : α → γ} (h : ContinuousWithinAt f s x) :
    UpperSemicontinuousWithinAt f s x := fun y hy => h (Iio_mem_nhds hy)

theorem ContinuousAt.upper_semicontinuous_at {f : α → γ} (h : ContinuousAt f x) : UpperSemicontinuousAt f x :=
  fun y hy => h (Iio_mem_nhds hy)

theorem ContinuousOn.upper_semicontinuous_on {f : α → γ} (h : ContinuousOn f s) : UpperSemicontinuousOn f s :=
  fun x hx => (h x hx).UpperSemicontinuousWithinAt

theorem Continuous.upper_semicontinuous {f : α → γ} (h : Continuous f) : UpperSemicontinuous f := fun x =>
  h.ContinuousAt.UpperSemicontinuousAt

end

/-! ### Composition -/


section

variable {γ : Type _} [LinearOrderₓ γ] [TopologicalSpace γ] [OrderTopology γ]

variable {δ : Type _} [LinearOrderₓ δ] [TopologicalSpace δ] [OrderTopology δ]

theorem ContinuousAt.comp_upper_semicontinuous_within_at {g : γ → δ} {f : α → γ} (hg : ContinuousAt g (f x))
    (hf : UpperSemicontinuousWithinAt f s x) (gmon : Monotone g) : UpperSemicontinuousWithinAt (g ∘ f) s x :=
  @ContinuousAt.comp_lower_semicontinuous_within_at α _ x s γᵒᵈ _ _ _ δᵒᵈ _ _ _ g f hg hf gmon.dual

theorem ContinuousAt.comp_upper_semicontinuous_at {g : γ → δ} {f : α → γ} (hg : ContinuousAt g (f x))
    (hf : UpperSemicontinuousAt f x) (gmon : Monotone g) : UpperSemicontinuousAt (g ∘ f) x :=
  @ContinuousAt.comp_lower_semicontinuous_at α _ x γᵒᵈ _ _ _ δᵒᵈ _ _ _ g f hg hf gmon.dual

theorem Continuous.comp_upper_semicontinuous_on {g : γ → δ} {f : α → γ} (hg : Continuous g)
    (hf : UpperSemicontinuousOn f s) (gmon : Monotone g) : UpperSemicontinuousOn (g ∘ f) s := fun x hx =>
  hg.ContinuousAt.comp_upper_semicontinuous_within_at (hf x hx) gmon

theorem Continuous.comp_upper_semicontinuous {g : γ → δ} {f : α → γ} (hg : Continuous g) (hf : UpperSemicontinuous f)
    (gmon : Monotone g) : UpperSemicontinuous (g ∘ f) := fun x =>
  hg.ContinuousAt.comp_upper_semicontinuous_at (hf x) gmon

theorem ContinuousAt.comp_upper_semicontinuous_within_at_antitone {g : γ → δ} {f : α → γ} (hg : ContinuousAt g (f x))
    (hf : UpperSemicontinuousWithinAt f s x) (gmon : Antitone g) : LowerSemicontinuousWithinAt (g ∘ f) s x :=
  @ContinuousAt.comp_upper_semicontinuous_within_at α _ x s γ _ _ _ δᵒᵈ _ _ _ g f hg hf gmon

theorem ContinuousAt.comp_upper_semicontinuous_at_antitone {g : γ → δ} {f : α → γ} (hg : ContinuousAt g (f x))
    (hf : UpperSemicontinuousAt f x) (gmon : Antitone g) : LowerSemicontinuousAt (g ∘ f) x :=
  @ContinuousAt.comp_upper_semicontinuous_at α _ x γ _ _ _ δᵒᵈ _ _ _ g f hg hf gmon

theorem Continuous.comp_upper_semicontinuous_on_antitone {g : γ → δ} {f : α → γ} (hg : Continuous g)
    (hf : UpperSemicontinuousOn f s) (gmon : Antitone g) : LowerSemicontinuousOn (g ∘ f) s := fun x hx =>
  hg.ContinuousAt.comp_upper_semicontinuous_within_at_antitone (hf x hx) gmon

theorem Continuous.comp_upper_semicontinuous_antitone {g : γ → δ} {f : α → γ} (hg : Continuous g)
    (hf : UpperSemicontinuous f) (gmon : Antitone g) : LowerSemicontinuous (g ∘ f) := fun x =>
  hg.ContinuousAt.comp_upper_semicontinuous_at_antitone (hf x) gmon

end

/-! #### Addition -/


section

variable {ι : Type _} {γ : Type _} [LinearOrderedAddCommMonoid γ] [TopologicalSpace γ] [OrderTopology γ]

/-- The sum of two upper semicontinuous functions is upper semicontinuous. Formulated with an
explicit continuity assumption on addition, for application to `ereal`. The unprimed version of
the lemma uses `[has_continuous_add]`. -/
theorem UpperSemicontinuousWithinAt.add' {f g : α → γ} (hf : UpperSemicontinuousWithinAt f s x)
    (hg : UpperSemicontinuousWithinAt g s x) (hcont : ContinuousAt (fun p : γ × γ => p.1 + p.2) (f x, g x)) :
    UpperSemicontinuousWithinAt (fun z => f z + g z) s x :=
  @LowerSemicontinuousWithinAt.add' α _ x s γᵒᵈ _ _ _ _ _ hf hg hcont

/-- The sum of two upper semicontinuous functions is upper semicontinuous. Formulated with an
explicit continuity assumption on addition, for application to `ereal`. The unprimed version of
the lemma uses `[has_continuous_add]`. -/
theorem UpperSemicontinuousAt.add' {f g : α → γ} (hf : UpperSemicontinuousAt f x) (hg : UpperSemicontinuousAt g x)
    (hcont : ContinuousAt (fun p : γ × γ => p.1 + p.2) (f x, g x)) : UpperSemicontinuousAt (fun z => f z + g z) x := by
  simp_rw [← upper_semicontinuous_within_at_univ_iff] at *
  exact hf.add' hg hcont

/-- The sum of two upper semicontinuous functions is upper semicontinuous. Formulated with an
explicit continuity assumption on addition, for application to `ereal`. The unprimed version of
the lemma uses `[has_continuous_add]`. -/
theorem UpperSemicontinuousOn.add' {f g : α → γ} (hf : UpperSemicontinuousOn f s) (hg : UpperSemicontinuousOn g s)
    (hcont : ∀, ∀ x ∈ s, ∀, ContinuousAt (fun p : γ × γ => p.1 + p.2) (f x, g x)) :
    UpperSemicontinuousOn (fun z => f z + g z) s := fun x hx => (hf x hx).add' (hg x hx) (hcont x hx)

/-- The sum of two upper semicontinuous functions is upper semicontinuous. Formulated with an
explicit continuity assumption on addition, for application to `ereal`. The unprimed version of
the lemma uses `[has_continuous_add]`. -/
theorem UpperSemicontinuous.add' {f g : α → γ} (hf : UpperSemicontinuous f) (hg : UpperSemicontinuous g)
    (hcont : ∀ x, ContinuousAt (fun p : γ × γ => p.1 + p.2) (f x, g x)) : UpperSemicontinuous fun z => f z + g z :=
  fun x => (hf x).add' (hg x) (hcont x)

variable [HasContinuousAdd γ]

/-- The sum of two upper semicontinuous functions is upper semicontinuous. Formulated with
`[has_continuous_add]`. The primed version of the lemma uses an explicit continuity assumption on
addition, for application to `ereal`. -/
theorem UpperSemicontinuousWithinAt.add {f g : α → γ} (hf : UpperSemicontinuousWithinAt f s x)
    (hg : UpperSemicontinuousWithinAt g s x) : UpperSemicontinuousWithinAt (fun z => f z + g z) s x :=
  hf.add' hg continuous_add.ContinuousAt

/-- The sum of two upper semicontinuous functions is upper semicontinuous. Formulated with
`[has_continuous_add]`. The primed version of the lemma uses an explicit continuity assumption on
addition, for application to `ereal`. -/
theorem UpperSemicontinuousAt.add {f g : α → γ} (hf : UpperSemicontinuousAt f x) (hg : UpperSemicontinuousAt g x) :
    UpperSemicontinuousAt (fun z => f z + g z) x :=
  hf.add' hg continuous_add.ContinuousAt

/-- The sum of two upper semicontinuous functions is upper semicontinuous. Formulated with
`[has_continuous_add]`. The primed version of the lemma uses an explicit continuity assumption on
addition, for application to `ereal`. -/
theorem UpperSemicontinuousOn.add {f g : α → γ} (hf : UpperSemicontinuousOn f s) (hg : UpperSemicontinuousOn g s) :
    UpperSemicontinuousOn (fun z => f z + g z) s :=
  hf.add' hg fun x hx => continuous_add.ContinuousAt

/-- The sum of two upper semicontinuous functions is upper semicontinuous. Formulated with
`[has_continuous_add]`. The primed version of the lemma uses an explicit continuity assumption on
addition, for application to `ereal`. -/
theorem UpperSemicontinuous.add {f g : α → γ} (hf : UpperSemicontinuous f) (hg : UpperSemicontinuous g) :
    UpperSemicontinuous fun z => f z + g z :=
  hf.add' hg fun x => continuous_add.ContinuousAt

theorem upper_semicontinuous_within_at_sum {f : ι → α → γ} {a : Finset ι}
    (ha : ∀, ∀ i ∈ a, ∀, UpperSemicontinuousWithinAt (f i) s x) :
    UpperSemicontinuousWithinAt (fun z => ∑ i in a, f i z) s x :=
  @lower_semicontinuous_within_at_sum α _ x s ι γᵒᵈ _ _ _ _ f a ha

theorem upper_semicontinuous_at_sum {f : ι → α → γ} {a : Finset ι} (ha : ∀, ∀ i ∈ a, ∀, UpperSemicontinuousAt (f i) x) :
    UpperSemicontinuousAt (fun z => ∑ i in a, f i z) x := by
  simp_rw [← upper_semicontinuous_within_at_univ_iff] at *
  exact upper_semicontinuous_within_at_sum ha

theorem upper_semicontinuous_on_sum {f : ι → α → γ} {a : Finset ι} (ha : ∀, ∀ i ∈ a, ∀, UpperSemicontinuousOn (f i) s) :
    UpperSemicontinuousOn (fun z => ∑ i in a, f i z) s := fun x hx =>
  upper_semicontinuous_within_at_sum fun i hi => ha i hi x hx

theorem upper_semicontinuous_sum {f : ι → α → γ} {a : Finset ι} (ha : ∀, ∀ i ∈ a, ∀, UpperSemicontinuous (f i)) :
    UpperSemicontinuous fun z => ∑ i in a, f i z := fun x => upper_semicontinuous_at_sum fun i hi => ha i hi x

end

/-! #### Infimum -/


section

variable {ι : Sort _} {δ : Type _} [CompleteLinearOrder δ]

theorem upper_semicontinuous_within_at_infi {f : ι → α → δ} (h : ∀ i, UpperSemicontinuousWithinAt (f i) s x) :
    UpperSemicontinuousWithinAt (fun x' => ⨅ i, f i x') s x :=
  @lower_semicontinuous_within_at_supr α _ x s ι δᵒᵈ _ f h

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i hi)
theorem upper_semicontinuous_within_at_binfi {p : ι → Prop} {f : ∀ (i) (h : p i), α → δ}
    (h : ∀ i hi, UpperSemicontinuousWithinAt (f i hi) s x) :
    UpperSemicontinuousWithinAt (fun x' => ⨅ (i) (hi), f i hi x') s x :=
  upper_semicontinuous_within_at_infi fun i => upper_semicontinuous_within_at_infi fun hi => h i hi

theorem upper_semicontinuous_at_infi {f : ι → α → δ} (h : ∀ i, UpperSemicontinuousAt (f i) x) :
    UpperSemicontinuousAt (fun x' => ⨅ i, f i x') x :=
  @lower_semicontinuous_at_supr α _ x ι δᵒᵈ _ f h

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i hi)
theorem upper_semicontinuous_at_binfi {p : ι → Prop} {f : ∀ (i) (h : p i), α → δ}
    (h : ∀ i hi, UpperSemicontinuousAt (f i hi) x) : UpperSemicontinuousAt (fun x' => ⨅ (i) (hi), f i hi x') x :=
  upper_semicontinuous_at_infi fun i => upper_semicontinuous_at_infi fun hi => h i hi

theorem upper_semicontinuous_on_infi {f : ι → α → δ} (h : ∀ i, UpperSemicontinuousOn (f i) s) :
    UpperSemicontinuousOn (fun x' => ⨅ i, f i x') s := fun x hx => upper_semicontinuous_within_at_infi fun i => h i x hx

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i hi)
theorem upper_semicontinuous_on_binfi {p : ι → Prop} {f : ∀ (i) (h : p i), α → δ}
    (h : ∀ i hi, UpperSemicontinuousOn (f i hi) s) : UpperSemicontinuousOn (fun x' => ⨅ (i) (hi), f i hi x') s :=
  upper_semicontinuous_on_infi fun i => upper_semicontinuous_on_infi fun hi => h i hi

theorem upper_semicontinuous_infi {f : ι → α → δ} (h : ∀ i, UpperSemicontinuous (f i)) :
    UpperSemicontinuous fun x' => ⨅ i, f i x' := fun x => upper_semicontinuous_at_infi fun i => h i x

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i hi)
theorem upper_semicontinuous_binfi {p : ι → Prop} {f : ∀ (i) (h : p i), α → δ}
    (h : ∀ i hi, UpperSemicontinuous (f i hi)) : UpperSemicontinuous fun x' => ⨅ (i) (hi), f i hi x' :=
  upper_semicontinuous_infi fun i => upper_semicontinuous_infi fun hi => h i hi

end

section

variable {γ : Type _} [LinearOrderₓ γ] [TopologicalSpace γ] [OrderTopology γ]

theorem continuous_within_at_iff_lower_upper_semicontinuous_within_at {f : α → γ} :
    ContinuousWithinAt f s x ↔ LowerSemicontinuousWithinAt f s x ∧ UpperSemicontinuousWithinAt f s x := by
  refine' ⟨fun h => ⟨h.LowerSemicontinuousWithinAt, h.UpperSemicontinuousWithinAt⟩, _⟩
  rintro ⟨h₁, h₂⟩
  intro v hv
  simp only [← Filter.mem_map]
  by_cases' Hl : ∃ l, l < f x
  · rcases exists_Ioc_subset_of_mem_nhds hv Hl with ⟨l, lfx, hl⟩
    by_cases' Hu : ∃ u, f x < u
    · rcases exists_Ico_subset_of_mem_nhds hv Hu with ⟨u, fxu, hu⟩
      filter_upwards [h₁ l lfx, h₂ u fxu] with a lfa fau
      cases' le_or_gtₓ (f a) (f x) with h h
      · exact hl ⟨lfa, h⟩
        
      · exact hu ⟨le_of_ltₓ h, fau⟩
        
      
    · simp only [← not_exists, ← not_ltₓ] at Hu
      filter_upwards [h₁ l lfx] with a lfa using hl ⟨lfa, Hu (f a)⟩
      
    
  · simp only [← not_exists, ← not_ltₓ] at Hl
    by_cases' Hu : ∃ u, f x < u
    · rcases exists_Ico_subset_of_mem_nhds hv Hu with ⟨u, fxu, hu⟩
      filter_upwards [h₂ u fxu] with a lfa
      apply hu
      exact ⟨Hl (f a), lfa⟩
      
    · simp only [← not_exists, ← not_ltₓ] at Hu
      apply Filter.eventually_of_forall
      intro a
      have : f a = f x := le_antisymmₓ (Hu _) (Hl _)
      rw [this]
      exact mem_of_mem_nhds hv
      
    

theorem continuous_at_iff_lower_upper_semicontinuous_at {f : α → γ} :
    ContinuousAt f x ↔ LowerSemicontinuousAt f x ∧ UpperSemicontinuousAt f x := by
  simp_rw [← continuous_within_at_univ, ← lower_semicontinuous_within_at_univ_iff, ←
    upper_semicontinuous_within_at_univ_iff, continuous_within_at_iff_lower_upper_semicontinuous_within_at]

theorem continuous_on_iff_lower_upper_semicontinuous_on {f : α → γ} :
    ContinuousOn f s ↔ LowerSemicontinuousOn f s ∧ UpperSemicontinuousOn f s := by
  simp only [← ContinuousOn, ← continuous_within_at_iff_lower_upper_semicontinuous_within_at]
  exact ⟨fun H => ⟨fun x hx => (H x hx).1, fun x hx => (H x hx).2⟩, fun H x hx => ⟨H.1 x hx, H.2 x hx⟩⟩

theorem continuous_iff_lower_upper_semicontinuous {f : α → γ} :
    Continuous f ↔ LowerSemicontinuous f ∧ UpperSemicontinuous f := by
  simp_rw [continuous_iff_continuous_on_univ, continuous_on_iff_lower_upper_semicontinuous_on,
    lower_semicontinuous_on_univ_iff, upper_semicontinuous_on_univ_iff]

end

