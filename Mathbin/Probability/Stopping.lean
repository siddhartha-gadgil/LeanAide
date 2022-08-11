/-
Copyright (c) 2021 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
import Mathbin.MeasureTheory.Function.ConditionalExpectation
import Mathbin.Topology.Instances.Discrete

/-!
# Filtration and stopping time

This file defines some standard definition from the theory of stochastic processes including
filtrations and stopping times. These definitions are used to model the amount of information
at a specific time and is the first step in formalizing stochastic processes.

## Main definitions

* `measure_theory.filtration`: a filtration on a measurable space
* `measure_theory.adapted`: a sequence of functions `u` is said to be adapted to a
  filtration `f` if at each point in time `i`, `u i` is `f i`-strongly measurable
* `measure_theory.prog_measurable`: a sequence of functions `u` is said to be progressively
  measurable with respect to a filtration `f` if at each point in time `i`, `u` restricted to
  `set.Iic i × α` is strongly measurable with respect to the product `measurable_space` structure
  where the σ-algebra used for `α` is `f i`.
* `measure_theory.filtration.natural`: the natural filtration with respect to a sequence of
  measurable functions is the smallest filtration to which it is adapted to
* `measure_theory.is_stopping_time`: a stopping time with respect to some filtration `f` is a
  function `τ` such that for all `i`, the preimage of `{j | j ≤ i}` along `τ` is
  `f i`-measurable
* `measure_theory.is_stopping_time.measurable_space`: the σ-algebra associated with a stopping time

## Main results

* `adapted.prog_measurable_of_continuous`: a continuous adapted process is progressively measurable.
* `prog_measurable.stopped_process`: the stopped process of a progressively measurable process is
  progressively measurable.
* `mem_ℒp_stopped_process`: if a process belongs to `ℒp` at every time in `ℕ`, then its stopped
  process belongs to `ℒp` as well.

## Tags

filtration, stopping time, stochastic process

-/


open Filter Order TopologicalSpace

open Classical MeasureTheory Nnreal Ennreal TopologicalSpace BigOperators

namespace MeasureTheory

/-! ### Filtrations -/


/-- A `filtration` on measurable space `α` with σ-algebra `m` is a monotone
sequence of sub-σ-algebras of `m`. -/
structure Filtration {α : Type _} (ι : Type _) [Preorderₓ ι] (m : MeasurableSpace α) where
  seq : ι → MeasurableSpace α
  mono' : Monotone seq
  le' : ∀ i : ι, seq i ≤ m

variable {α β ι : Type _} {m : MeasurableSpace α}

instance [Preorderₓ ι] : CoeFun (Filtration ι m) fun _ => ι → MeasurableSpace α :=
  ⟨fun f => f.seq⟩

namespace Filtration

variable [Preorderₓ ι]

protected theorem mono {i j : ι} (f : Filtration ι m) (hij : i ≤ j) : f i ≤ f j :=
  f.mono' hij

protected theorem le (f : Filtration ι m) (i : ι) : f i ≤ m :=
  f.le' i

@[ext]
protected theorem ext {f g : Filtration ι m} (h : (f : ι → MeasurableSpace α) = g) : f = g := by
  cases f
  cases g
  simp only
  exact h

variable (ι)

/-- The constant filtration which is equal to `m` for all `i : ι`. -/
def const (m' : MeasurableSpace α) (hm' : m' ≤ m) : Filtration ι m :=
  ⟨fun _ => m', monotone_const, fun _ => hm'⟩

variable {ι}

@[simp]
theorem const_apply {m' : MeasurableSpace α} {hm' : m' ≤ m} (i : ι) : const ι m' hm' i = m' :=
  rfl

instance : Inhabited (Filtration ι m) :=
  ⟨const ι m le_rfl⟩

instance : LE (Filtration ι m) :=
  ⟨fun f g => ∀ i, f i ≤ g i⟩

instance : HasBot (Filtration ι m) :=
  ⟨const ι ⊥ bot_le⟩

instance : HasTop (Filtration ι m) :=
  ⟨const ι m le_rfl⟩

instance : HasSup (Filtration ι m) :=
  ⟨fun f g =>
    { seq := fun i => f i⊔g i,
      mono' := fun i j hij => sup_le ((f.mono hij).trans le_sup_left) ((g.mono hij).trans le_sup_right),
      le' := fun i => sup_le (f.le i) (g.le i) }⟩

@[norm_cast]
theorem coe_fn_sup {f g : Filtration ι m} : ⇑(f⊔g) = f⊔g :=
  rfl

instance : HasInf (Filtration ι m) :=
  ⟨fun f g =>
    { seq := fun i => f i⊓g i,
      mono' := fun i j hij => le_inf (inf_le_left.trans (f.mono hij)) (inf_le_right.trans (g.mono hij)),
      le' := fun i => inf_le_left.trans (f.le i) }⟩

@[norm_cast]
theorem coe_fn_inf {f g : Filtration ι m} : ⇑(f⊓g) = f⊓g :=
  rfl

instance : HasSupₓ (Filtration ι m) :=
  ⟨fun s =>
    { seq := fun i => sup ((fun f : Filtration ι m => f i) '' s),
      mono' := fun i j hij => by
        refine' Sup_le fun m' hm' => _
        rw [Set.mem_image] at hm'
        obtain ⟨f, hf_mem, hfm'⟩ := hm'
        rw [← hfm']
        refine' (f.mono hij).trans _
        have hfj_mem : f j ∈ (fun g : filtration ι m => g j) '' s := ⟨f, hf_mem, rfl⟩
        exact le_Sup hfj_mem,
      le' := fun i => by
        refine' Sup_le fun m' hm' => _
        rw [Set.mem_image] at hm'
        obtain ⟨f, hf_mem, hfm'⟩ := hm'
        rw [← hfm']
        exact f.le i }⟩

theorem Sup_def (s : Set (Filtration ι m)) (i : ι) : sup s i = sup ((fun f : Filtration ι m => f i) '' s) :=
  rfl

noncomputable instance : HasInfₓ (Filtration ι m) :=
  ⟨fun s =>
    { seq := fun i => if Set.Nonempty s then inf ((fun f : Filtration ι m => f i) '' s) else m,
      mono' := fun i j hij => by
        by_cases' h_nonempty : Set.Nonempty s
        swap
        · simp only [← h_nonempty, ← Set.nonempty_image_iff, ← if_false, ← le_reflₓ]
          
        simp only [← h_nonempty, ← if_true, ← le_Inf_iff, ← Set.mem_image, ← forall_exists_index, ← and_imp, ←
          forall_apply_eq_imp_iff₂]
        refine' fun f hf_mem => le_transₓ _ (f.mono hij)
        have hfi_mem : f i ∈ (fun g : filtration ι m => g i) '' s := ⟨f, hf_mem, rfl⟩
        exact Inf_le hfi_mem,
      le' := fun i => by
        by_cases' h_nonempty : Set.Nonempty s
        swap
        · simp only [← h_nonempty, ← if_false, ← le_reflₓ]
          
        simp only [← h_nonempty, ← if_true]
        obtain ⟨f, hf_mem⟩ := h_nonempty
        exact le_transₓ (Inf_le ⟨f, hf_mem, rfl⟩) (f.le i) }⟩

theorem Inf_def (s : Set (Filtration ι m)) (i : ι) :
    inf s i = if Set.Nonempty s then inf ((fun f : Filtration ι m => f i) '' s) else m :=
  rfl

noncomputable instance : CompleteLattice (Filtration ι m) where
  le := (· ≤ ·)
  le_refl := fun f i => le_rfl
  le_trans := fun f g h h_fg h_gh i => (h_fg i).trans (h_gh i)
  le_antisymm := fun f g h_fg h_gf => filtration.ext <| funext fun i => (h_fg i).antisymm (h_gf i)
  sup := (·⊔·)
  le_sup_left := fun f g i => le_sup_left
  le_sup_right := fun f g i => le_sup_right
  sup_le := fun f g h h_fh h_gh i => sup_le (h_fh i) (h_gh _)
  inf := (·⊓·)
  inf_le_left := fun f g i => inf_le_left
  inf_le_right := fun f g i => inf_le_right
  le_inf := fun f g h h_fg h_fh i => le_inf (h_fg i) (h_fh i)
  sup := sup
  le_Sup := fun s f hf_mem i => le_Sup ⟨f, hf_mem, rfl⟩
  Sup_le := fun s f h_forall i =>
    Sup_le fun m' hm' => by
      obtain ⟨g, hg_mem, hfm'⟩ := hm'
      rw [← hfm']
      exact h_forall g hg_mem i
  inf := inf
  Inf_le := fun s f hf_mem i => by
    have hs : s.nonempty := ⟨f, hf_mem⟩
    simp only [← Inf_def, ← hs, ← if_true]
    exact Inf_le ⟨f, hf_mem, rfl⟩
  le_Inf := fun s f h_forall i => by
    by_cases' hs : s.nonempty
    swap
    · simp only [← Inf_def, ← hs, ← if_false]
      exact f.le i
      
    simp only [← Inf_def, ← hs, ← if_true, ← le_Inf_iff, ← Set.mem_image, ← forall_exists_index, ← and_imp, ←
      forall_apply_eq_imp_iff₂]
    exact fun g hg_mem => h_forall g hg_mem i
  top := ⊤
  bot := ⊥
  le_top := fun f i => f.le' i
  bot_le := fun f i => bot_le

end Filtration

theorem measurable_set_of_filtration [Preorderₓ ι] {f : Filtration ι m} {s : Set α} {i : ι}
    (hs : measurable_set[f i] s) : measurable_set[m] s :=
  f.le i s hs

/-- A measure is σ-finite with respect to filtration if it is σ-finite with respect
to all the sub-σ-algebra of the filtration. -/
class SigmaFiniteFiltration [Preorderₓ ι] (μ : Measure α) (f : Filtration ι m) : Prop where
  SigmaFinite : ∀ i : ι, SigmaFinite (μ.trim (f.le i))

instance sigma_finite_of_sigma_finite_filtration [Preorderₓ ι] (μ : Measure α) (f : Filtration ι m)
    [hf : SigmaFiniteFiltration μ f] (i : ι) : SigmaFinite (μ.trim (f.le i)) := by
  apply hf.sigma_finite

-- can't exact here
instance (priority := 100) IsFiniteMeasure.sigma_finite_filtration [Preorderₓ ι] (μ : Measure α) (f : Filtration ι m)
    [IsFiniteMeasure μ] : SigmaFiniteFiltration μ f :=
  ⟨fun n => by
    infer_instance⟩

/-- Given a integrable function `g`, the conditional expectations of `g` with respect to a
filtration is uniformly integrable. -/
theorem Integrable.uniform_integrable_condexp_filtration [Preorderₓ ι] {μ : Measure α} [IsFiniteMeasure μ]
    {f : Filtration ι m} {g : α → ℝ} (hg : Integrable g μ) : UniformIntegrable (fun i => μ[g|f i]) 1 μ :=
  hg.uniform_integrable_condexp f.le

section AdaptedProcess

variable [TopologicalSpace β] [Preorderₓ ι] {u v : ι → α → β} {f : Filtration ι m}

/-- A sequence of functions `u` is adapted to a filtration `f` if for all `i`,
`u i` is `f i`-measurable. -/
def Adapted (f : Filtration ι m) (u : ι → α → β) : Prop :=
  ∀ i : ι, strongly_measurable[f i] (u i)

namespace Adapted

theorem add [Add β] [HasContinuousAdd β] (hu : Adapted f u) (hv : Adapted f v) : Adapted f (u + v) := fun i =>
  (hu i).add (hv i)

theorem neg [AddGroupₓ β] [TopologicalAddGroup β] (hu : Adapted f u) : Adapted f (-u) := fun i => (hu i).neg

theorem smul [HasSmul ℝ β] [HasContinuousSmul ℝ β] (c : ℝ) (hu : Adapted f u) : Adapted f (c • u) := fun i =>
  (hu i).const_smul c

end Adapted

variable (β)

theorem adapted_zero [Zero β] (f : Filtration ι m) : Adapted f (0 : ι → α → β) := fun i =>
  @strongly_measurable_zero α β (f i) _ _

variable {β}

/-- Progressively measurable process. A sequence of functions `u` is said to be progressively
measurable with respect to a filtration `f` if at each point in time `i`, `u` restricted to
`set.Iic i × α` is measurable with respect to the product `measurable_space` structure where the
σ-algebra used for `α` is `f i`.
The usual definition uses the interval `[0,i]`, which we replace by `set.Iic i`. We recover the
usual definition for index types `ℝ≥0` or `ℕ`. -/
def ProgMeasurable [MeasurableSpace ι] (f : Filtration ι m) (u : ι → α → β) : Prop :=
  ∀ i, strongly_measurable[Subtype.measurableSpace.Prod (f i)] fun p : Set.Iic i × α => u p.1 p.2

theorem prog_measurable_const [MeasurableSpace ι] (f : Filtration ι m) (b : β) :
    ProgMeasurable f (fun _ _ => b : ι → α → β) := fun i =>
  @strongly_measurable_const _ _ (Subtype.measurableSpace.Prod (f i)) _ _

namespace ProgMeasurable

variable [MeasurableSpace ι]

protected theorem adapted (h : ProgMeasurable f u) : Adapted f u := by
  intro i
  have : u i = (fun p : Set.Iic i × α => u p.1 p.2) ∘ fun x => (⟨i, set.mem_Iic.mpr le_rfl⟩, x) := rfl
  rw [this]
  exact (h i).comp_measurable measurable_prod_mk_left

protected theorem comp {t : ι → α → ι} [TopologicalSpace ι] [BorelSpace ι] [MetrizableSpace ι] (h : ProgMeasurable f u)
    (ht : ProgMeasurable f t) (ht_le : ∀ i x, t i x ≤ i) : ProgMeasurable f fun i x => u (t i x) x := by
  intro i
  have :
    (fun p : ↥(Set.Iic i) × α => u (t (p.fst : ι) p.snd) p.snd) =
      (fun p : ↥(Set.Iic i) × α => u (p.fst : ι) p.snd) ∘ fun p : ↥(Set.Iic i) × α =>
        (⟨t (p.fst : ι) p.snd, set.mem_Iic.mpr ((ht_le _ _).trans p.fst.prop)⟩, p.snd) :=
    rfl
  rw [this]
  exact (h i).comp_measurable ((ht i).Measurable.subtype_mk.prod_mk measurable_snd)

section Arithmetic

@[to_additive]
protected theorem mul [Mul β] [HasContinuousMul β] (hu : ProgMeasurable f u) (hv : ProgMeasurable f v) :
    ProgMeasurable f fun i x => u i x * v i x := fun i => (hu i).mul (hv i)

@[to_additive]
protected theorem finset_prod' {γ} [CommMonoidₓ β] [HasContinuousMul β] {U : γ → ι → α → β} {s : Finset γ}
    (h : ∀, ∀ c ∈ s, ∀, ProgMeasurable f (U c)) : ProgMeasurable f (∏ c in s, U c) :=
  Finset.prod_induction U (ProgMeasurable f) (fun _ _ => ProgMeasurable.mul) (prog_measurable_const _ 1) h

@[to_additive]
protected theorem finset_prod {γ} [CommMonoidₓ β] [HasContinuousMul β] {U : γ → ι → α → β} {s : Finset γ}
    (h : ∀, ∀ c ∈ s, ∀, ProgMeasurable f (U c)) : ProgMeasurable f fun i a => ∏ c in s, U c i a := by
  convert prog_measurable.finset_prod' h
  ext i a
  simp only [← Finset.prod_apply]

@[to_additive]
protected theorem inv [Groupₓ β] [TopologicalGroup β] (hu : ProgMeasurable f u) :
    ProgMeasurable f fun i x => (u i x)⁻¹ := fun i => (hu i).inv

@[to_additive]
protected theorem div [Groupₓ β] [TopologicalGroup β] (hu : ProgMeasurable f u) (hv : ProgMeasurable f v) :
    ProgMeasurable f fun i x => u i x / v i x := fun i => (hu i).div (hv i)

end Arithmetic

end ProgMeasurable

theorem prog_measurable_of_tendsto' {γ} [MeasurableSpace ι] [MetrizableSpace β] (fltr : Filter γ) [fltr.ne_bot]
    [fltr.IsCountablyGenerated] {U : γ → ι → α → β} (h : ∀ l, ProgMeasurable f (U l))
    (h_tendsto : Tendsto U fltr (𝓝 u)) : ProgMeasurable f u := by
  intro i
  apply
    @strongly_measurable_of_tendsto (Set.Iic i × α) β γ (MeasurableSpace.prod _ (f i)) _ _ fltr _ _ _ _ fun l => h l i
  rw [tendsto_pi_nhds] at h_tendsto⊢
  intro x
  specialize h_tendsto x.fst
  rw [tendsto_nhds] at h_tendsto⊢
  exact fun s hs h_mem => h_tendsto { g | g x.snd ∈ s } (hs.Preimage (continuous_apply x.snd)) h_mem

theorem prog_measurable_of_tendsto [MeasurableSpace ι] [MetrizableSpace β] {U : ℕ → ι → α → β}
    (h : ∀ l, ProgMeasurable f (U l)) (h_tendsto : Tendsto U atTop (𝓝 u)) : ProgMeasurable f u :=
  prog_measurable_of_tendsto' atTop h h_tendsto

/-- A continuous and adapted process is progressively measurable. -/
theorem Adapted.prog_measurable_of_continuous [TopologicalSpace ι] [MetrizableSpace ι] [MeasurableSpace ι]
    [SecondCountableTopology ι] [OpensMeasurableSpace ι] [MetrizableSpace β] (h : Adapted f u)
    (hu_cont : ∀ x, Continuous fun i => u i x) : ProgMeasurable f u := fun i =>
  @strongly_measurable_uncurry_of_continuous_of_strongly_measurable _ _ (Set.Iic i) _ _ _ _ _ _ _ (f i) _
    (fun x => (hu_cont x).comp continuous_induced_dom) fun j => (h j).mono (f.mono j.Prop)

end AdaptedProcess

namespace Filtration

variable [TopologicalSpace β] [MetrizableSpace β] [mβ : MeasurableSpace β] [BorelSpace β] [Preorderₓ ι]

include mβ

/-- Given a sequence of functions, the natural filtration is the smallest sequence
of σ-algebras such that that sequence of functions is measurable with respect to
the filtration. -/
def natural (u : ι → α → β) (hum : ∀ i, StronglyMeasurable (u i)) : Filtration ι m where
  seq := fun i => ⨆ j ≤ i, MeasurableSpace.comap (u j) mβ
  mono' := fun i j hij => bsupr_mono fun k => ge_transₓ hij
  le' := fun i => by
    refine' supr₂_le _
    rintro j hj s ⟨t, ht, rfl⟩
    exact (hum j).Measurable ht

theorem adapted_natural {u : ι → α → β} (hum : ∀ i, strongly_measurable[m] (u i)) : Adapted (natural u hum) u := by
  intro i
  refine' strongly_measurable.mono _ (le_supr₂_of_le i (le_reflₓ i) le_rfl)
  rw [strongly_measurable_iff_measurable_separable]
  exact ⟨measurable_iff_comap_le.2 le_rfl, (hum i).is_separable_range⟩

end Filtration

/-! ### Stopping times -/


/-- A stopping time with respect to some filtration `f` is a function
`τ` such that for all `i`, the preimage of `{j | j ≤ i}` along `τ` is measurable
with respect to `f i`.

Intuitively, the stopping time `τ` describes some stopping rule such that at time
`i`, we may determine it with the information we have at time `i`. -/
def IsStoppingTime [Preorderₓ ι] (f : Filtration ι m) (τ : α → ι) :=
  ∀ i : ι, measurable_set[f i] <| { x | τ x ≤ i }

theorem is_stopping_time_const [Preorderₓ ι] (f : Filtration ι m) (i : ι) : IsStoppingTime f fun x => i := fun j => by
  simp only [← MeasurableSet.const]

section MeasurableSet

section Preorderₓ

variable [Preorderₓ ι] {f : Filtration ι m} {τ : α → ι}

protected theorem IsStoppingTime.measurable_set_le (hτ : IsStoppingTime f τ) (i : ι) :
    measurable_set[f i] { x | τ x ≤ i } :=
  hτ i

theorem IsStoppingTime.measurable_set_lt_of_pred [PredOrder ι] (hτ : IsStoppingTime f τ) (i : ι) :
    measurable_set[f i] { x | τ x < i } := by
  by_cases' hi_min : IsMin i
  · suffices { x : α | τ x < i } = ∅ by
      rw [this]
      exact @MeasurableSet.empty _ (f i)
    ext1 x
    simp only [← Set.mem_set_of_eq, ← Set.mem_empty_eq, ← iff_falseₓ]
    rw [is_min_iff_forall_not_lt] at hi_min
    exact hi_min (τ x)
    
  have : { x : α | τ x < i } = τ ⁻¹' Set.Iio i := rfl
  rw [this, ← Iic_pred_of_not_is_min hi_min]
  exact f.mono (pred_le i) _ (hτ.measurable_set_le <| pred i)

end Preorderₓ

section CountableStoppingTime

namespace IsStoppingTime

variable [PartialOrderₓ ι] {τ : α → ι} {f : Filtration ι m}

protected theorem measurable_set_eq_of_countable (hτ : IsStoppingTime f τ) (h_countable : (Set.Range τ).Countable)
    (i : ι) : measurable_set[f i] { a | τ a = i } := by
  have : { a | τ a = i } = { a | τ a ≤ i } \ ⋃ (j ∈ Set.Range τ) (hj : j < i), { a | τ a ≤ j } := by
    ext1 a
    simp only [← Set.mem_set_of_eq, ← Set.mem_range, ← Set.Union_exists, ← Set.Union_Union_eq', ← Set.mem_diff, ←
      Set.mem_Union, ← exists_prop, ← not_exists, ← not_and, ← not_leₓ]
    constructor <;> intro h
    · simp only [← h, ← lt_iff_le_not_leₓ, ← le_reflₓ, ← and_imp, ← imp_self, ← implies_true_iff, ← and_selfₓ]
      
    · have h_lt_or_eq : τ a < i ∨ τ a = i := lt_or_eq_of_leₓ h.1
      rcases h_lt_or_eq with (h_lt | rfl)
      · exfalso
        exact h.2 a h_lt (le_reflₓ (τ a))
        
      · rfl
        
      
  rw [this]
  refine' (hτ.measurable_set_le i).diff _
  refine' MeasurableSet.bUnion h_countable fun j hj => _
  by_cases' hji : j < i
  · simp only [← hji, ← Set.Union_true]
    exact f.mono hji.le _ (hτ.measurable_set_le j)
    
  · simp only [← hji, ← Set.Union_false]
    exact @MeasurableSet.empty _ (f i)
    

protected theorem measurable_set_eq_of_encodable [Encodable ι] (hτ : IsStoppingTime f τ) (i : ι) :
    measurable_set[f i] { a | τ a = i } :=
  hτ.measurable_set_eq_of_countable (Set.countable_encodable _) i

protected theorem measurable_set_lt_of_countable (hτ : IsStoppingTime f τ) (h_countable : (Set.Range τ).Countable)
    (i : ι) : measurable_set[f i] { a | τ a < i } := by
  have : { a | τ a < i } = { a | τ a ≤ i } \ { a | τ a = i } := by
    ext1 x
    simp [← lt_iff_le_and_ne]
  rw [this]
  exact (hτ.measurable_set_le i).diff (hτ.measurable_set_eq_of_countable h_countable i)

protected theorem measurable_set_lt_of_encodable [Encodable ι] (hτ : IsStoppingTime f τ) (i : ι) :
    measurable_set[f i] { a | τ a < i } :=
  hτ.measurable_set_lt_of_countable (Set.countable_encodable _) i

protected theorem measurable_set_ge_of_countable {ι} [LinearOrderₓ ι] {τ : α → ι} {f : Filtration ι m}
    (hτ : IsStoppingTime f τ) (h_countable : (Set.Range τ).Countable) (i : ι) : measurable_set[f i] { a | i ≤ τ a } :=
  by
  have : { x | i ≤ τ x } = { x | τ x < i }ᶜ := by
    ext1 x
    simp only [← Set.mem_set_of_eq, ← Set.mem_compl_eq, ← not_ltₓ]
  rw [this]
  exact (hτ.measurable_set_lt_of_countable h_countable i).compl

protected theorem measurable_set_ge_of_encodable {ι} [LinearOrderₓ ι] {τ : α → ι} {f : Filtration ι m} [Encodable ι]
    (hτ : IsStoppingTime f τ) (i : ι) : measurable_set[f i] { a | i ≤ τ a } :=
  hτ.measurable_set_ge_of_countable (Set.countable_encodable _) i

end IsStoppingTime

end CountableStoppingTime

section LinearOrderₓ

variable [LinearOrderₓ ι] {f : Filtration ι m} {τ : α → ι}

theorem IsStoppingTime.measurable_set_gt (hτ : IsStoppingTime f τ) (i : ι) : measurable_set[f i] { x | i < τ x } := by
  have : { x | i < τ x } = { x | τ x ≤ i }ᶜ := by
    ext1 x
    simp only [← Set.mem_set_of_eq, ← Set.mem_compl_eq, ← not_leₓ]
  rw [this]
  exact (hτ.measurable_set_le i).compl

section TopologicalSpace

variable [TopologicalSpace ι] [OrderTopology ι] [FirstCountableTopology ι]

/-- Auxiliary lemma for `is_stopping_time.measurable_set_lt`. -/
theorem IsStoppingTime.measurable_set_lt_of_is_lub (hτ : IsStoppingTime f τ) (i : ι) (h_lub : IsLub (Set.Iio i) i) :
    measurable_set[f i] { x | τ x < i } := by
  by_cases' hi_min : IsMin i
  · suffices { x : α | τ x < i } = ∅ by
      rw [this]
      exact @MeasurableSet.empty _ (f i)
    ext1 x
    simp only [← Set.mem_set_of_eq, ← Set.mem_empty_eq, ← iff_falseₓ]
    exact is_min_iff_forall_not_lt.mp hi_min (τ x)
    
  obtain ⟨seq, -, -, h_tendsto, h_bound⟩ :
    ∃ seq : ℕ → ι, Monotone seq ∧ (∀ j, seq j ≤ i) ∧ tendsto seq at_top (𝓝 i) ∧ ∀ j, seq j < i
  exact h_lub.exists_seq_monotone_tendsto (not_is_min_iff.mp hi_min)
  have h_Ioi_eq_Union : Set.Iio i = ⋃ j, { k | k ≤ seq j } := by
    ext1 k
    simp only [← Set.mem_Iio, ← Set.mem_Union, ← Set.mem_set_of_eq]
    refine' ⟨fun hk_lt_i => _, fun h_exists_k_le_seq => _⟩
    · rw [tendsto_at_top'] at h_tendsto
      have h_nhds : Set.Ici k ∈ 𝓝 i := mem_nhds_iff.mpr ⟨Set.Ioi k, Set.Ioi_subset_Ici le_rfl, is_open_Ioi, hk_lt_i⟩
      obtain ⟨a, ha⟩ : ∃ a : ℕ, ∀ b : ℕ, b ≥ a → k ≤ seq b := h_tendsto (Set.Ici k) h_nhds
      exact ⟨a, ha a le_rfl⟩
      
    · obtain ⟨j, hk_seq_j⟩ := h_exists_k_le_seq
      exact hk_seq_j.trans_lt (h_bound j)
      
  have h_lt_eq_preimage : { x : α | τ x < i } = τ ⁻¹' Set.Iio i := by
    ext1 x
    simp only [← Set.mem_set_of_eq, ← Set.mem_preimage, ← Set.mem_Iio]
  rw [h_lt_eq_preimage, h_Ioi_eq_Union]
  simp only [← Set.preimage_Union, ← Set.preimage_set_of_eq]
  exact MeasurableSet.Union fun n => f.mono (h_bound n).le _ (hτ.measurable_set_le (seq n))

theorem IsStoppingTime.measurable_set_lt (hτ : IsStoppingTime f τ) (i : ι) : measurable_set[f i] { x | τ x < i } := by
  obtain ⟨i', hi'_lub⟩ : ∃ i', IsLub (Set.Iio i) i'
  exact exists_lub_Iio i
  cases' lub_Iio_eq_self_or_Iio_eq_Iic i hi'_lub with hi'_eq_i h_Iio_eq_Iic
  · rw [← hi'_eq_i] at hi'_lub⊢
    exact hτ.measurable_set_lt_of_is_lub i' hi'_lub
    
  · have h_lt_eq_preimage : { x : α | τ x < i } = τ ⁻¹' Set.Iio i := rfl
    rw [h_lt_eq_preimage, h_Iio_eq_Iic]
    exact f.mono (lub_Iio_le i hi'_lub) _ (hτ.measurable_set_le i')
    

theorem IsStoppingTime.measurable_set_ge (hτ : IsStoppingTime f τ) (i : ι) : measurable_set[f i] { x | i ≤ τ x } := by
  have : { x | i ≤ τ x } = { x | τ x < i }ᶜ := by
    ext1 x
    simp only [← Set.mem_set_of_eq, ← Set.mem_compl_eq, ← not_ltₓ]
  rw [this]
  exact (hτ.measurable_set_lt i).compl

theorem IsStoppingTime.measurable_set_eq (hτ : IsStoppingTime f τ) (i : ι) : measurable_set[f i] { x | τ x = i } := by
  have : { x | τ x = i } = { x | τ x ≤ i } ∩ { x | τ x ≥ i } := by
    ext1 x
    simp only [← Set.mem_set_of_eq, ← ge_iff_le, ← Set.mem_inter_eq, ← le_antisymm_iffₓ]
  rw [this]
  exact (hτ.measurable_set_le i).inter (hτ.measurable_set_ge i)

theorem IsStoppingTime.measurable_set_eq_le (hτ : IsStoppingTime f τ) {i j : ι} (hle : i ≤ j) :
    measurable_set[f j] { x | τ x = i } :=
  f.mono hle _ <| hτ.measurable_set_eq i

theorem IsStoppingTime.measurable_set_lt_le (hτ : IsStoppingTime f τ) {i j : ι} (hle : i ≤ j) :
    measurable_set[f j] { x | τ x < i } :=
  f.mono hle _ <| hτ.measurable_set_lt i

end TopologicalSpace

end LinearOrderₓ

section Encodable

theorem is_stopping_time_of_measurable_set_eq [Preorderₓ ι] [Encodable ι] {f : Filtration ι m} {τ : α → ι}
    (hτ : ∀ i, measurable_set[f i] { x | τ x = i }) : IsStoppingTime f τ := by
  intro i
  rw
    [show { x | τ x ≤ i } = ⋃ k ≤ i, { x | τ x = k } by
      ext
      simp ]
  refine' MeasurableSet.bUnion (Set.countable_encodable _) fun k hk => _
  exact f.mono hk _ (hτ k)

end Encodable

end MeasurableSet

namespace IsStoppingTime

protected theorem max [LinearOrderₓ ι] {f : Filtration ι m} {τ π : α → ι} (hτ : IsStoppingTime f τ)
    (hπ : IsStoppingTime f π) : IsStoppingTime f fun x => max (τ x) (π x) := by
  intro i
  simp_rw [max_le_iff, Set.set_of_and]
  exact (hτ i).inter (hπ i)

protected theorem max_const [LinearOrderₓ ι] {f : Filtration ι m} {τ : α → ι} (hτ : IsStoppingTime f τ) (i : ι) :
    IsStoppingTime f fun x => max (τ x) i :=
  hτ.max (is_stopping_time_const f i)

protected theorem min [LinearOrderₓ ι] {f : Filtration ι m} {τ π : α → ι} (hτ : IsStoppingTime f τ)
    (hπ : IsStoppingTime f π) : IsStoppingTime f fun x => min (τ x) (π x) := by
  intro i
  simp_rw [min_le_iff, Set.set_of_or]
  exact (hτ i).union (hπ i)

protected theorem min_const [LinearOrderₓ ι] {f : Filtration ι m} {τ : α → ι} (hτ : IsStoppingTime f τ) (i : ι) :
    IsStoppingTime f fun x => min (τ x) i :=
  hτ.min (is_stopping_time_const f i)

theorem add_const [AddGroupₓ ι] [Preorderₓ ι] [CovariantClass ι ι (Function.swap (· + ·)) (· ≤ ·)]
    [CovariantClass ι ι (· + ·) (· ≤ ·)] {f : Filtration ι m} {τ : α → ι} (hτ : IsStoppingTime f τ) {i : ι}
    (hi : 0 ≤ i) : IsStoppingTime f fun x => τ x + i := by
  intro j
  simp_rw [← le_sub_iff_add_le]
  exact f.mono (sub_le_self j hi) _ (hτ (j - i))

theorem add_const_nat {f : Filtration ℕ m} {τ : α → ℕ} (hτ : IsStoppingTime f τ) {i : ℕ} :
    IsStoppingTime f fun x => τ x + i := by
  refine' is_stopping_time_of_measurable_set_eq fun j => _
  by_cases' hij : i ≤ j
  · simp_rw [eq_comm, ← Nat.sub_eq_iff_eq_addₓ hij, eq_comm]
    exact f.mono (j.sub_le i) _ (hτ.measurable_set_eq (j - i))
    
  · rw [not_leₓ] at hij
    convert MeasurableSet.empty
    ext x
    simp only [← Set.mem_empty_eq, ← iff_falseₓ]
    rintro (hx : τ x + i = j)
    linarith
    

-- generalize to certain encodable type?
theorem add {f : Filtration ℕ m} {τ π : α → ℕ} (hτ : IsStoppingTime f τ) (hπ : IsStoppingTime f π) :
    IsStoppingTime f (τ + π) := by
  intro i
  rw [(_ : { x | (τ + π) x ≤ i } = ⋃ k ≤ i, { x | π x = k } ∩ { x | τ x + k ≤ i })]
  · exact
      MeasurableSet.Union fun k =>
        MeasurableSet.Union_Prop fun hk => (hπ.measurable_set_eq_le hk).inter (hτ.add_const_nat i)
    
  ext
  simp only [← Pi.add_apply, ← Set.mem_set_of_eq, ← Set.mem_Union, ← Set.mem_inter_eq, ← exists_prop]
  refine'
    ⟨fun h =>
      ⟨π x, by
        linarith, rfl, h⟩,
      _⟩
  rintro ⟨j, hj, rfl, h⟩
  assumption

section Preorderₓ

variable [Preorderₓ ι] {f : Filtration ι m} {τ π : α → ι}

/-- The associated σ-algebra with a stopping time. -/
protected def measurableSpace (hτ : IsStoppingTime f τ) : MeasurableSpace α where
  MeasurableSet' := fun s => ∀ i : ι, measurable_set[f i] (s ∩ { x | τ x ≤ i })
  measurable_set_empty := fun i => (Set.empty_inter { x | τ x ≤ i }).symm ▸ @MeasurableSet.empty _ (f i)
  measurable_set_compl := fun s hs i => by
    rw [(_ : sᶜ ∩ { x | τ x ≤ i } = (sᶜ ∪ { x | τ x ≤ i }ᶜ) ∩ { x | τ x ≤ i })]
    · refine' MeasurableSet.inter _ _
      · rw [← Set.compl_inter]
        exact (hs i).compl
        
      · exact hτ i
        
      
    · rw [Set.union_inter_distrib_right]
      simp only [← Set.compl_inter_self, ← Set.union_empty]
      
  measurable_set_Union := fun s hs i => by
    rw [forall_swap] at hs
    rw [Set.Union_inter]
    exact MeasurableSet.Union (hs i)

protected theorem measurable_set (hτ : IsStoppingTime f τ) (s : Set α) :
    measurable_set[hτ.MeasurableSpace] s ↔ ∀ i : ι, measurable_set[f i] (s ∩ { x | τ x ≤ i }) :=
  Iff.rfl

theorem measurable_space_mono (hτ : IsStoppingTime f τ) (hπ : IsStoppingTime f π) (hle : τ ≤ π) :
    hτ.MeasurableSpace ≤ hπ.MeasurableSpace := by
  intro s hs i
  rw [(_ : s ∩ { x | π x ≤ i } = s ∩ { x | τ x ≤ i } ∩ { x | π x ≤ i })]
  · exact (hs i).inter (hπ i)
    
  · ext
    simp only [← Set.mem_inter_eq, ← iff_self_and, ← And.congr_left_iff, ← Set.mem_set_of_eq]
    intro hle' _
    exact le_transₓ (hle _) hle'
    

theorem measurable_space_le_of_encodable [Encodable ι] (hτ : IsStoppingTime f τ) : hτ.MeasurableSpace ≤ m := by
  intro s hs
  change ∀ i, measurable_set[f i] (s ∩ { x | τ x ≤ i }) at hs
  rw [(_ : s = ⋃ i, s ∩ { x | τ x ≤ i })]
  · exact MeasurableSet.Union fun i => f.le i _ (hs i)
    
  · ext x
    constructor <;> rw [Set.mem_Union]
    · exact fun hx => ⟨τ x, hx, le_rfl⟩
      
    · rintro ⟨_, hx, _⟩
      exact hx
      
    

theorem measurable_space_le' [IsCountablyGenerated (atTop : Filter ι)] [(atTop : Filter ι).ne_bot]
    (hτ : IsStoppingTime f τ) : hτ.MeasurableSpace ≤ m := by
  intro s hs
  change ∀ i, measurable_set[f i] (s ∩ { x | τ x ≤ i }) at hs
  obtain ⟨seq : ℕ → ι, h_seq_tendsto⟩ := at_top.exists_seq_tendsto
  rw [(_ : s = ⋃ n, s ∩ { x | τ x ≤ seq n })]
  · exact MeasurableSet.Union fun i => f.le (seq i) _ (hs (seq i))
    
  · ext x
    constructor <;> rw [Set.mem_Union]
    · intro hx
      suffices : ∃ i, τ x ≤ seq i
      exact ⟨this.some, hx, this.some_spec⟩
      rw [tendsto_at_top] at h_seq_tendsto
      exact (h_seq_tendsto (τ x)).exists
      
    · rintro ⟨_, hx, _⟩
      exact hx
      
    
  all_goals
    infer_instance

theorem measurable_space_le {ι} [SemilatticeSup ι] {f : Filtration ι m} {τ : α → ι}
    [IsCountablyGenerated (atTop : Filter ι)] (hτ : IsStoppingTime f τ) : hτ.MeasurableSpace ≤ m := by
  cases is_empty_or_nonempty ι
  · have : IsEmpty α := ⟨fun x => IsEmpty.false (τ x)⟩
    intro s hsτ
    suffices hs : s = ∅
    · rw [hs]
      exact MeasurableSet.empty
      
    have : Unique (Set α) := Set.uniqueEmpty
    rw [Unique.eq_default s, Unique.eq_default ∅]
    
  exact measurable_space_le' hτ

example {f : Filtration ℕ m} {τ : α → ℕ} (hτ : IsStoppingTime f τ) : hτ.MeasurableSpace ≤ m :=
  hτ.measurable_space_le

example {f : Filtration ℝ m} {τ : α → ℝ} (hτ : IsStoppingTime f τ) : hτ.MeasurableSpace ≤ m :=
  hτ.measurable_space_le

@[simp]
theorem measurable_space_const (f : Filtration ι m) (i : ι) : (is_stopping_time_const f i).MeasurableSpace = f i := by
  ext1 s
  change measurable_set[(is_stopping_time_const f i).MeasurableSpace] s ↔ measurable_set[f i] s
  rw [is_stopping_time.measurable_set]
  constructor <;> intro h
  · specialize h i
    simpa only [← le_reflₓ, ← Set.set_of_true, ← Set.inter_univ] using h
    
  · intro j
    by_cases' hij : i ≤ j
    · simp only [← hij, ← Set.set_of_true, ← Set.inter_univ]
      exact f.mono hij _ h
      
    · simp only [← hij, ← Set.set_of_false, ← Set.inter_empty, ← MeasurableSet.empty]
      
    

theorem measurable_set_inter_eq_iff (hτ : IsStoppingTime f τ) (s : Set α) (i : ι) :
    measurable_set[hτ.MeasurableSpace] (s ∩ { x | τ x = i }) ↔ measurable_set[f i] (s ∩ { x | τ x = i }) := by
  have : ∀ j, { x : α | τ x = i } ∩ { x : α | τ x ≤ j } = { x : α | τ x = i } ∩ { x | i ≤ j } := by
    intro j
    ext1 x
    simp only [← Set.mem_inter_eq, ← Set.mem_set_of_eq, ← And.congr_right_iff]
    intro hxi
    rw [hxi]
  constructor <;> intro h
  · specialize h i
    simpa only [← Set.inter_assoc, ← this, ← le_reflₓ, ← Set.set_of_true, ← Set.inter_univ] using h
    
  · intro j
    rw [Set.inter_assoc, this]
    by_cases' hij : i ≤ j
    · simp only [← hij, ← Set.set_of_true, ← Set.inter_univ]
      exact f.mono hij _ h
      
    · simp [← hij]
      
    

theorem measurable_space_le_of_le_const (hτ : IsStoppingTime f τ) {i : ι} (hτ_le : ∀ x, τ x ≤ i) :
    hτ.MeasurableSpace ≤ f i :=
  (measurable_space_mono hτ _ hτ_le).trans (measurable_space_const _ _).le

theorem le_measurable_space_of_const_le (hτ : IsStoppingTime f τ) {i : ι} (hτ_le : ∀ x, i ≤ τ x) :
    f i ≤ hτ.MeasurableSpace :=
  (measurable_space_const _ _).symm.le.trans (measurable_space_mono _ hτ hτ_le)

end Preorderₓ

instance sigma_finite_stopping_time {ι} [SemilatticeSup ι] [OrderBot ι] [(Filter.atTop : Filter ι).IsCountablyGenerated]
    {μ : Measure α} {f : Filtration ι m} {τ : α → ι} [SigmaFiniteFiltration μ f] (hτ : IsStoppingTime f τ) :
    SigmaFinite (μ.trim hτ.measurable_space_le) := by
  refine' sigma_finite_trim_mono hτ.measurable_space_le _
  · exact f ⊥
    
  · exact hτ.le_measurable_space_of_const_le fun _ => bot_le
    
  · infer_instance
    

section LinearOrderₓ

variable [LinearOrderₓ ι] {f : Filtration ι m} {τ π : α → ι}

protected theorem measurable_set_le' (hτ : IsStoppingTime f τ) (i : ι) :
    measurable_set[hτ.MeasurableSpace] { x | τ x ≤ i } := by
  intro j
  have : { x : α | τ x ≤ i } ∩ { x : α | τ x ≤ j } = { x : α | τ x ≤ min i j } := by
    ext1 x
    simp only [← Set.mem_inter_eq, ← Set.mem_set_of_eq, ← le_min_iff]
  rw [this]
  exact f.mono (min_le_rightₓ i j) _ (hτ _)

protected theorem measurable_set_gt' (hτ : IsStoppingTime f τ) (i : ι) :
    measurable_set[hτ.MeasurableSpace] { x | i < τ x } := by
  have : { x : α | i < τ x } = { x : α | τ x ≤ i }ᶜ := by
    ext1 x
    simp
  rw [this]
  exact (hτ.measurable_set_le' i).compl

protected theorem measurable_set_eq' [TopologicalSpace ι] [OrderTopology ι] [FirstCountableTopology ι]
    (hτ : IsStoppingTime f τ) (i : ι) : measurable_set[hτ.MeasurableSpace] { x | τ x = i } := by
  rw [← Set.univ_inter { x | τ x = i }, measurable_set_inter_eq_iff, Set.univ_inter]
  exact hτ.measurable_set_eq i

protected theorem measurable_set_ge' [TopologicalSpace ι] [OrderTopology ι] [FirstCountableTopology ι]
    (hτ : IsStoppingTime f τ) (i : ι) : measurable_set[hτ.MeasurableSpace] { x | i ≤ τ x } := by
  have : { x | i ≤ τ x } = { x | τ x = i } ∪ { x | i < τ x } := by
    ext1 x
    simp only [← le_iff_lt_or_eqₓ, ← Set.mem_set_of_eq, ← Set.mem_union_eq]
    rw [@eq_comm _ i, or_comm]
  rw [this]
  exact (hτ.measurable_set_eq' i).union (hτ.measurable_set_gt' i)

protected theorem measurable_set_lt' [TopologicalSpace ι] [OrderTopology ι] [FirstCountableTopology ι]
    (hτ : IsStoppingTime f τ) (i : ι) : measurable_set[hτ.MeasurableSpace] { x | τ x < i } := by
  have : { x | τ x < i } = { x | τ x ≤ i } \ { x | τ x = i } := by
    ext1 x
    simp only [← lt_iff_le_and_ne, ← Set.mem_set_of_eq, ← Set.mem_diff]
  rw [this]
  exact (hτ.measurable_set_le' i).diff (hτ.measurable_set_eq' i)

section Countable

protected theorem measurable_set_eq_of_countable' (hτ : IsStoppingTime f τ) (h_countable : (Set.Range τ).Countable)
    (i : ι) : measurable_set[hτ.MeasurableSpace] { x | τ x = i } := by
  rw [← Set.univ_inter { x | τ x = i }, measurable_set_inter_eq_iff, Set.univ_inter]
  exact hτ.measurable_set_eq_of_countable h_countable i

protected theorem measurable_set_eq_of_encodable' [Encodable ι] (hτ : IsStoppingTime f τ) (i : ι) :
    measurable_set[hτ.MeasurableSpace] { a | τ a = i } :=
  hτ.measurable_set_eq_of_countable' (Set.countable_encodable _) i

protected theorem measurable_set_ge_of_countable' (hτ : IsStoppingTime f τ) (h_countable : (Set.Range τ).Countable)
    (i : ι) : measurable_set[hτ.MeasurableSpace] { x | i ≤ τ x } := by
  have : { x | i ≤ τ x } = { x | τ x = i } ∪ { x | i < τ x } := by
    ext1 x
    simp only [← le_iff_lt_or_eqₓ, ← Set.mem_set_of_eq, ← Set.mem_union_eq]
    rw [@eq_comm _ i, or_comm]
  rw [this]
  exact (hτ.measurable_set_eq_of_countable' h_countable i).union (hτ.measurable_set_gt' i)

protected theorem measurable_set_ge_of_encodable' [Encodable ι] (hτ : IsStoppingTime f τ) (i : ι) :
    measurable_set[hτ.MeasurableSpace] { a | i ≤ τ a } :=
  hτ.measurable_set_ge_of_countable' (Set.countable_encodable _) i

protected theorem measurable_set_lt_of_countable' (hτ : IsStoppingTime f τ) (h_countable : (Set.Range τ).Countable)
    (i : ι) : measurable_set[hτ.MeasurableSpace] { x | τ x < i } := by
  have : { x | τ x < i } = { x | τ x ≤ i } \ { x | τ x = i } := by
    ext1 x
    simp only [← lt_iff_le_and_ne, ← Set.mem_set_of_eq, ← Set.mem_diff]
  rw [this]
  exact (hτ.measurable_set_le' i).diff (hτ.measurable_set_eq_of_countable' h_countable i)

protected theorem measurable_set_lt_of_encodable' [Encodable ι] (hτ : IsStoppingTime f τ) (i : ι) :
    measurable_set[hτ.MeasurableSpace] { a | τ a < i } :=
  hτ.measurable_set_lt_of_countable' (Set.countable_encodable _) i

protected theorem measurable_space_le_of_countable (hτ : IsStoppingTime f τ) (h_countable : (Set.Range τ).Countable) :
    hτ.MeasurableSpace ≤ m := by
  intro s hs
  change ∀ i, measurable_set[f i] (s ∩ { x | τ x ≤ i }) at hs
  rw [(_ : s = ⋃ i ∈ Set.Range τ, s ∩ { x | τ x ≤ i })]
  · exact MeasurableSet.bUnion h_countable fun i _ => f.le i _ (hs i)
    
  · ext x
    constructor <;> rw [Set.mem_Union]
    · exact fun hx =>
        ⟨τ x, by
          simpa using hx⟩
      
    · rintro ⟨i, hx⟩
      simp only [← Set.mem_range, ← Set.Union_exists, ← Set.mem_Union, ← Set.mem_inter_eq, ← Set.mem_set_of_eq, ←
        exists_prop, ← exists_and_distrib_right] at hx
      exact hx.1.2
      
    

end Countable

protected theorem measurable [TopologicalSpace ι] [MeasurableSpace ι] [BorelSpace ι] [OrderTopology ι]
    [SecondCountableTopology ι] (hτ : IsStoppingTime f τ) : measurable[hτ.MeasurableSpace] τ :=
  @measurable_of_Iic ι α _ _ _ hτ.MeasurableSpace _ _ _ _ fun i => hτ.measurable_set_le' i

protected theorem measurable_of_le [TopologicalSpace ι] [MeasurableSpace ι] [BorelSpace ι] [OrderTopology ι]
    [SecondCountableTopology ι] (hτ : IsStoppingTime f τ) {i : ι} (hτ_le : ∀ x, τ x ≤ i) : measurable[f i] τ :=
  hτ.Measurable.mono (measurable_space_le_of_le_const _ hτ_le) le_rfl

theorem measurable_space_min (hτ : IsStoppingTime f τ) (hπ : IsStoppingTime f π) :
    (hτ.min hπ).MeasurableSpace = hτ.MeasurableSpace⊓hπ.MeasurableSpace := by
  refine' le_antisymmₓ _ _
  · exact
      le_inf (measurable_space_mono _ hτ fun _ => min_le_leftₓ _ _)
        (measurable_space_mono _ hπ fun _ => min_le_rightₓ _ _)
    
  · intro s
    change
      measurable_set[hτ.measurable_space] s ∧ measurable_set[hπ.measurable_space] s →
        measurable_set[(hτ.min hπ).MeasurableSpace] s
    simp_rw [is_stopping_time.measurable_set]
    have : ∀ i, { x | min (τ x) (π x) ≤ i } = { x | τ x ≤ i } ∪ { x | π x ≤ i } := by
      intro i
      ext1 x
      simp
    simp_rw [this, Set.inter_union_distrib_left]
    exact fun h i => (h.left i).union (h.right i)
    

theorem measurable_set_min_iff (hτ : IsStoppingTime f τ) (hπ : IsStoppingTime f π) (s : Set α) :
    measurable_set[(hτ.min hπ).MeasurableSpace] s ↔
      measurable_set[hτ.MeasurableSpace] s ∧ measurable_set[hπ.MeasurableSpace] s :=
  by
  rw [measurable_space_min]
  rfl

theorem measurable_space_min_const (hτ : IsStoppingTime f τ) {i : ι} :
    (hτ.min_const i).MeasurableSpace = hτ.MeasurableSpace⊓f i := by
  rw [hτ.measurable_space_min (is_stopping_time_const _ i), measurable_space_const]

theorem measurable_set_min_const_iff (hτ : IsStoppingTime f τ) (s : Set α) {i : ι} :
    measurable_set[(hτ.min_const i).MeasurableSpace] s ↔ measurable_set[hτ.MeasurableSpace] s ∧ measurable_set[f i] s :=
  by
  rw [measurable_space_min_const, MeasurableSpace.measurable_set_inf]

theorem measurable_set_inter_le [TopologicalSpace ι] [SecondCountableTopology ι] [OrderTopology ι] [MeasurableSpace ι]
    [BorelSpace ι] (hτ : IsStoppingTime f τ) (hπ : IsStoppingTime f π) (s : Set α)
    (hs : measurable_set[hτ.MeasurableSpace] s) : measurable_set[(hτ.min hπ).MeasurableSpace] (s ∩ { x | τ x ≤ π x }) :=
  by
  simp_rw [is_stopping_time.measurable_set] at hs⊢
  intro i
  have :
    s ∩ { x | τ x ≤ π x } ∩ { x | min (τ x) (π x) ≤ i } =
      s ∩ { x | τ x ≤ i } ∩ { x | min (τ x) (π x) ≤ i } ∩ { x | min (τ x) i ≤ min (min (τ x) (π x)) i } :=
    by
    ext1 x
    simp only [← min_le_iff, ← Set.mem_inter_eq, ← Set.mem_set_of_eq, ← le_min_iff, ← le_reflₓ, ← true_andₓ, ←
      and_trueₓ, ← true_orₓ, ← or_trueₓ]
    by_cases' hτi : τ x ≤ i
    · simp only [← hτi, ← true_orₓ, ← and_trueₓ, ← And.congr_right_iff]
      intro hx
      constructor <;> intro h
      · exact Or.inl h
        
      · cases h
        · exact h
          
        · exact hτi.trans h
          
        
      
    simp only [← hτi, ← false_orₓ, ← and_falseₓ, ← false_andₓ, ← iff_falseₓ, ← not_and, ← not_leₓ, ← and_imp]
    refine' fun hx hτ_le_π => lt_of_lt_of_leₓ _ hτ_le_π
    rw [← not_leₓ]
    exact hτi
  rw [this]
  refine' ((hs i).inter ((hτ.min hπ) i)).inter _
  apply measurable_set_le
  · exact (hτ.min_const i).measurable_of_le fun _ => min_le_rightₓ _ _
    
  · exact ((hτ.min hπ).min_const i).measurable_of_le fun _ => min_le_rightₓ _ _
    

theorem measurable_set_inter_le_iff [TopologicalSpace ι] [SecondCountableTopology ι] [OrderTopology ι]
    [MeasurableSpace ι] [BorelSpace ι] (hτ : IsStoppingTime f τ) (hπ : IsStoppingTime f π) (s : Set α) :
    measurable_set[hτ.MeasurableSpace] (s ∩ { x | τ x ≤ π x }) ↔
      measurable_set[(hτ.min hπ).MeasurableSpace] (s ∩ { x | τ x ≤ π x }) :=
  by
  constructor <;> intro h
  · have : s ∩ { x | τ x ≤ π x } = s ∩ { x | τ x ≤ π x } ∩ { x | τ x ≤ π x } := by
      rw [Set.inter_assoc, Set.inter_self]
    rw [this]
    exact measurable_set_inter_le _ _ _ h
    
  · rw [measurable_set_min_iff] at h
    exact h.1
    

theorem measurable_set_le_stopping_time [TopologicalSpace ι] [SecondCountableTopology ι] [OrderTopology ι]
    [MeasurableSpace ι] [BorelSpace ι] (hτ : IsStoppingTime f τ) (hπ : IsStoppingTime f π) :
    measurable_set[hτ.MeasurableSpace] { x | τ x ≤ π x } := by
  rw [hτ.measurable_set]
  intro j
  have : { x | τ x ≤ π x } ∩ { x | τ x ≤ j } = { x | min (τ x) j ≤ min (π x) j } ∩ { x | τ x ≤ j } := by
    ext1 x
    simp only [← Set.mem_inter_eq, ← Set.mem_set_of_eq, ← min_le_iff, ← le_min_iff, ← le_reflₓ, ← and_trueₓ, ←
      And.congr_left_iff]
    intro h
    simp only [← h, ← or_selfₓ, ← and_trueₓ]
    by_cases' hj : j ≤ π x
    · simp only [← hj, ← h.trans hj, ← or_selfₓ]
      
    · simp only [← hj, ← or_falseₓ]
      
  rw [this]
  refine' MeasurableSet.inter _ (hτ.measurable_set_le j)
  apply measurable_set_le
  · exact (hτ.min_const j).measurable_of_le fun _ => min_le_rightₓ _ _
    
  · exact (hπ.min_const j).measurable_of_le fun _ => min_le_rightₓ _ _
    

theorem measurable_set_stopping_time_le [TopologicalSpace ι] [SecondCountableTopology ι] [OrderTopology ι]
    [MeasurableSpace ι] [BorelSpace ι] (hτ : IsStoppingTime f τ) (hπ : IsStoppingTime f π) :
    measurable_set[hπ.MeasurableSpace] { x | τ x ≤ π x } := by
  suffices measurable_set[(hτ.min hπ).MeasurableSpace] { x : α | τ x ≤ π x } by
    rw [measurable_set_min_iff hτ hπ] at this
    exact this.2
  rw [← Set.univ_inter { x : α | τ x ≤ π x }, ← hτ.measurable_set_inter_le_iff hπ, Set.univ_inter]
  exact measurable_set_le_stopping_time hτ hπ

theorem measurable_set_eq_stopping_time [AddGroupₓ ι] [TopologicalSpace ι] [MeasurableSpace ι] [BorelSpace ι]
    [OrderTopology ι] [MeasurableSingletonClass ι] [SecondCountableTopology ι] [HasMeasurableSub₂ ι]
    (hτ : IsStoppingTime f τ) (hπ : IsStoppingTime f π) : measurable_set[hτ.MeasurableSpace] { x | τ x = π x } := by
  rw [hτ.measurable_set]
  intro j
  have : { x | τ x = π x } ∩ { x | τ x ≤ j } = { x | min (τ x) j = min (π x) j } ∩ { x | τ x ≤ j } ∩ { x | π x ≤ j } :=
    by
    ext1 x
    simp only [← Set.mem_inter_eq, ← Set.mem_set_of_eq]
    refine' ⟨fun h => ⟨⟨_, h.2⟩, _⟩, fun h => ⟨_, h.1.2⟩⟩
    · rw [h.1]
      
    · rw [← h.1]
      exact h.2
      
    · cases' h with h' hσ_le
      cases' h' with h_eq hτ_le
      rwa [min_eq_leftₓ hτ_le, min_eq_leftₓ hσ_le] at h_eq
      
  rw [this]
  refine' MeasurableSet.inter (MeasurableSet.inter _ (hτ.measurable_set_le j)) (hπ.measurable_set_le j)
  apply measurable_set_eq_fun
  · exact (hτ.min_const j).measurable_of_le fun _ => min_le_rightₓ _ _
    
  · exact (hπ.min_const j).measurable_of_le fun _ => min_le_rightₓ _ _
    

theorem measurable_set_eq_stopping_time_of_encodable [Encodable ι] [TopologicalSpace ι] [MeasurableSpace ι]
    [BorelSpace ι] [OrderTopology ι] [MeasurableSingletonClass ι] [SecondCountableTopology ι] (hτ : IsStoppingTime f τ)
    (hπ : IsStoppingTime f π) : measurable_set[hτ.MeasurableSpace] { x | τ x = π x } := by
  rw [hτ.measurable_set]
  intro j
  have : { x | τ x = π x } ∩ { x | τ x ≤ j } = { x | min (τ x) j = min (π x) j } ∩ { x | τ x ≤ j } ∩ { x | π x ≤ j } :=
    by
    ext1 x
    simp only [← Set.mem_inter_eq, ← Set.mem_set_of_eq]
    refine' ⟨fun h => ⟨⟨_, h.2⟩, _⟩, fun h => ⟨_, h.1.2⟩⟩
    · rw [h.1]
      
    · rw [← h.1]
      exact h.2
      
    · cases' h with h' hπ_le
      cases' h' with h_eq hτ_le
      rwa [min_eq_leftₓ hτ_le, min_eq_leftₓ hπ_le] at h_eq
      
  rw [this]
  refine' MeasurableSet.inter (MeasurableSet.inter _ (hτ.measurable_set_le j)) (hπ.measurable_set_le j)
  apply measurable_set_eq_fun_of_encodable
  · exact (hτ.min_const j).measurable_of_le fun _ => min_le_rightₓ _ _
    
  · exact (hπ.min_const j).measurable_of_le fun _ => min_le_rightₓ _ _
    

end LinearOrderₓ

end IsStoppingTime

section LinearOrderₓ

/-! ## Stopped value and stopped process -/


/-- Given a map `u : ι → α → E`, its stopped value with respect to the stopping
time `τ` is the map `x ↦ u (τ x) x`. -/
def stoppedValue (u : ι → α → β) (τ : α → ι) : α → β := fun x => u (τ x) x

theorem stopped_value_const (u : ι → α → β) (i : ι) : (stoppedValue u fun x => i) = u i :=
  rfl

variable [LinearOrderₓ ι]

/-- Given a map `u : ι → α → E`, the stopped process with respect to `τ` is `u i x` if
`i ≤ τ x`, and `u (τ x) x` otherwise.

Intuitively, the stopped process stops evolving once the stopping time has occured. -/
def stoppedProcess (u : ι → α → β) (τ : α → ι) : ι → α → β := fun i x => u (min i (τ x)) x

theorem stopped_process_eq_of_le {u : ι → α → β} {τ : α → ι} {i : ι} {x : α} (h : i ≤ τ x) :
    stoppedProcess u τ i x = u i x := by
  simp [← stopped_process, ← min_eq_leftₓ h]

theorem stopped_process_eq_of_ge {u : ι → α → β} {τ : α → ι} {i : ι} {x : α} (h : τ x ≤ i) :
    stoppedProcess u τ i x = u (τ x) x := by
  simp [← stopped_process, ← min_eq_rightₓ h]

section ProgMeasurable

variable [MeasurableSpace ι] [TopologicalSpace ι] [OrderTopology ι] [SecondCountableTopology ι] [BorelSpace ι]
  [TopologicalSpace β] {u : ι → α → β} {τ : α → ι} {f : Filtration ι m}

theorem prog_measurable_min_stopping_time [MetrizableSpace ι] (hτ : IsStoppingTime f τ) :
    ProgMeasurable f fun i x => min i (τ x) := by
  intro i
  let m_prod : MeasurableSpace (Set.Iic i × α) := MeasurableSpace.prod _ (f i)
  let m_set : ∀ t : Set (Set.Iic i × α), MeasurableSpace t := fun _ => @Subtype.measurableSpace (Set.Iic i × α) _ m_prod
  let s := { p : Set.Iic i × α | τ p.2 ≤ i }
  have hs : measurable_set[m_prod] s := @measurable_snd (Set.Iic i) α _ (f i) _ (hτ i)
  have h_meas_fst : ∀ t : Set (Set.Iic i × α), measurable[m_set t] fun x : t => ((x : Set.Iic i × α).fst : ι) :=
    fun t => (@measurable_subtype_coe (Set.Iic i × α) m_prod _).fst.subtype_coe
  apply Measurable.strongly_measurable
  refine' measurable_of_restrict_of_restrict_compl hs _ _
  · refine' @Measurable.min _ _ _ _ _ (m_set s) _ _ _ _ _ (h_meas_fst s) _
    refine' @measurable_of_Iic ι s _ _ _ (m_set s) _ _ _ _ fun j => _
    have h_set_eq :
      (fun x : s => τ (x : Set.Iic i × α).snd) ⁻¹' Set.Iic j =
        (fun x : s => (x : Set.Iic i × α).snd) ⁻¹' { x | τ x ≤ min i j } :=
      by
      ext1 x
      simp only [← Set.mem_preimage, ← Set.mem_Iic, ← iff_and_self, ← le_min_iff, ← Set.mem_set_of_eq]
      exact fun _ => x.prop
    rw [h_set_eq]
    suffices h_meas : @Measurable _ _ (m_set s) (f i) fun x : s => (x : Set.Iic i × α).snd
    exact h_meas (f.mono (min_le_leftₓ _ _) _ (hτ.measurable_set_le (min i j)))
    exact measurable_snd.comp (@measurable_subtype_coe _ m_prod _)
    
  · suffices h_min_eq_left :
      (fun x : sᶜ => min (↑(x : Set.Iic i × α).fst) (τ (x : Set.Iic i × α).snd)) = fun x : sᶜ =>
        ↑(x : Set.Iic i × α).fst
    · rw [Set.restrict, h_min_eq_left]
      exact h_meas_fst _
      
    ext1 x
    rw [min_eq_leftₓ]
    have hx_fst_le : ↑(x : Set.Iic i × α).fst ≤ i := (x : Set.Iic i × α).fst.Prop
    refine' hx_fst_le.trans (le_of_ltₓ _)
    convert x.prop
    simp only [← not_leₓ, ← Set.mem_compl_eq, ← Set.mem_set_of_eq]
    

theorem ProgMeasurable.stopped_process [MetrizableSpace ι] (h : ProgMeasurable f u) (hτ : IsStoppingTime f τ) :
    ProgMeasurable f (stoppedProcess u τ) :=
  h.comp (prog_measurable_min_stopping_time hτ) fun i x => min_le_leftₓ _ _

theorem ProgMeasurable.adapted_stopped_process [MetrizableSpace ι] (h : ProgMeasurable f u) (hτ : IsStoppingTime f τ) :
    Adapted f (stoppedProcess u τ) :=
  (h.stoppedProcess hτ).Adapted

theorem ProgMeasurable.strongly_measurable_stopped_process [MetrizableSpace ι] (hu : ProgMeasurable f u)
    (hτ : IsStoppingTime f τ) (i : ι) : StronglyMeasurable (stoppedProcess u τ i) :=
  (hu.adapted_stopped_process hτ i).mono (f.le _)

theorem strongly_measurable_stopped_value_of_le (h : ProgMeasurable f u) (hτ : IsStoppingTime f τ) {n : ι}
    (hτ_le : ∀ x, τ x ≤ n) : strongly_measurable[f n] (stoppedValue u τ) := by
  have : stopped_value u τ = (fun p : Set.Iic n × α => u (↑p.fst) p.snd) ∘ fun x => (⟨τ x, hτ_le x⟩, x) := by
    ext1 x
    simp only [← stopped_value, ← Function.comp_app, ← Subtype.coe_mk]
  rw [this]
  refine' strongly_measurable.comp_measurable (h n) _
  exact (hτ.measurable_of_le hτ_le).subtype_mk.prod_mk measurable_id

theorem measurable_stopped_value [MetrizableSpace β] [MeasurableSpace β] [BorelSpace β] (hf_prog : ProgMeasurable f u)
    (hτ : IsStoppingTime f τ) : measurable[hτ.MeasurableSpace] (stoppedValue u τ) := by
  have h_str_meas : ∀ i, strongly_measurable[f i] (stopped_value u fun x => min (τ x) i) := fun i =>
    strongly_measurable_stopped_value_of_le hf_prog (hτ.min_const i) fun _ => min_le_rightₓ _ _
  intro t ht i
  suffices
    stopped_value u τ ⁻¹' t ∩ { x : α | τ x ≤ i } = (stopped_value u fun x => min (τ x) i) ⁻¹' t ∩ { x : α | τ x ≤ i }
    by
    rw [this]
    exact ((h_str_meas i).Measurable ht).inter (hτ.measurable_set_le i)
  ext1 x
  simp only [← stopped_value, ← Set.mem_inter_eq, ← Set.mem_preimage, ← Set.mem_set_of_eq, ← And.congr_left_iff]
  intro h
  rw [min_eq_leftₓ h]

end ProgMeasurable

end LinearOrderₓ

section Nat

/-! ### Filtrations indexed by `ℕ` -/


open Filtration

variable {f : Filtration ℕ m} {u : ℕ → α → β} {τ π : α → ℕ}

theorem stopped_value_sub_eq_sum [AddCommGroupₓ β] (hle : τ ≤ π) :
    stoppedValue u π - stoppedValue u τ = fun x => (∑ i in Finset.ico (τ x) (π x), u (i + 1) - u i) x := by
  ext x
  rw [Finset.sum_Ico_eq_sub _ (hle x), Finset.sum_range_sub, Finset.sum_range_sub]
  simp [← stopped_value]

theorem stopped_value_sub_eq_sum' [AddCommGroupₓ β] (hle : τ ≤ π) {N : ℕ} (hbdd : ∀ x, π x ≤ N) :
    stoppedValue u π - stoppedValue u τ = fun x =>
      (∑ i in Finset.range (N + 1), Set.indicatorₓ { x | τ x ≤ i ∧ i < π x } (u (i + 1) - u i)) x :=
  by
  rw [stopped_value_sub_eq_sum hle]
  ext x
  simp only [← Finset.sum_apply, ← Finset.sum_indicator_eq_sum_filter]
  refine' Finset.sum_congr _ fun _ _ => rfl
  ext i
  simp only [← Finset.mem_filter, ← Set.mem_set_of_eq, ← Finset.mem_range, ← Finset.mem_Ico]
  exact ⟨fun h => ⟨lt_transₓ h.2 (Nat.lt_succ_iffₓ.2 <| hbdd _), h⟩, fun h => h.2⟩

section AddCommMonoidₓ

variable [AddCommMonoidₓ β]

/-- For filtrations indexed by `ℕ`, `adapted` and `prog_measurable` are equivalent. This lemma
provides `adapted f u → prog_measurable f u`. See `prog_measurable.adapted` for the reverse
direction, which is true more generally. -/
theorem Adapted.prog_measurable_of_nat [TopologicalSpace β] [HasContinuousAdd β] (h : Adapted f u) :
    ProgMeasurable f u := by
  intro i
  have :
    (fun p : ↥(Set.Iic i) × α => u (↑p.fst) p.snd) = fun p : ↥(Set.Iic i) × α =>
      ∑ j in Finset.range (i + 1), if ↑p.fst = j then u j p.snd else 0 :=
    by
    ext1 p
    rw [Finset.sum_ite_eq]
    have hp_mem : (p.fst : ℕ) ∈ Finset.range (i + 1) := finset.mem_range_succ_iff.mpr p.fst.prop
    simp only [← hp_mem, ← if_true]
  rw [this]
  refine' Finset.strongly_measurable_sum _ fun j hj => strongly_measurable.ite _ _ _
  · suffices h_meas : measurable[MeasurableSpace.prod _ (f i)] fun a : ↥(Set.Iic i) × α => (a.fst : ℕ)
    exact h_meas (measurable_set_singleton j)
    exact measurable_fst.subtype_coe
    
  · have h_le : j ≤ i := finset.mem_range_succ_iff.mp hj
    exact (strongly_measurable.mono (h j) (f.mono h_le)).comp_measurable measurable_snd
    
  · exact strongly_measurable_const
    

/-- For filtrations indexed by `ℕ`, the stopped process obtained from an adapted process is
adapted. -/
theorem Adapted.stopped_process_of_nat [TopologicalSpace β] [HasContinuousAdd β] (hu : Adapted f u)
    (hτ : IsStoppingTime f τ) : Adapted f (stoppedProcess u τ) :=
  (hu.prog_measurable_of_nat.stoppedProcess hτ).Adapted

theorem Adapted.strongly_measurable_stopped_process_of_nat [TopologicalSpace β] [HasContinuousAdd β]
    (hτ : IsStoppingTime f τ) (hu : Adapted f u) (n : ℕ) : StronglyMeasurable (stoppedProcess u τ n) :=
  hu.prog_measurable_of_nat.strongly_measurable_stopped_process hτ n

theorem stopped_value_eq {N : ℕ} (hbdd : ∀ x, τ x ≤ N) :
    stoppedValue u τ = fun x => (∑ i in Finset.range (N + 1), Set.indicatorₓ { x | τ x = i } (u i)) x := by
  ext y
  rw [stopped_value, Finset.sum_apply, Finset.sum_eq_single (τ y)]
  · rw [Set.indicator_of_mem]
    exact rfl
    
  · exact fun i hi hneq => Set.indicator_of_not_mem hneq.symm _
    
  · intro hy
    rw [Set.indicator_of_not_mem]
    exact fun _ => hy (Finset.mem_range.2 <| lt_of_le_of_ltₓ (hbdd _) (Nat.lt_succ_selfₓ _))
    

theorem stopped_process_eq (n : ℕ) :
    stoppedProcess u τ n =
      Set.indicatorₓ { a | n ≤ τ a } (u n) + ∑ i in Finset.range n, Set.indicatorₓ { a | τ a = i } (u i) :=
  by
  ext x
  rw [Pi.add_apply, Finset.sum_apply]
  cases le_or_ltₓ n (τ x)
  · rw [stopped_process_eq_of_le h, Set.indicator_of_mem, Finset.sum_eq_zero, add_zeroₓ]
    · intro m hm
      rw [Finset.mem_range] at hm
      exact Set.indicator_of_not_mem (lt_of_lt_of_leₓ hm h).Ne.symm _
      
    · exact h
      
    
  · rw [stopped_process_eq_of_ge (le_of_ltₓ h), Finset.sum_eq_single_of_mem (τ x)]
    · rw [Set.indicator_of_not_mem, zero_addₓ, Set.indicator_of_mem]
      · exact rfl
        
      -- refl does not work
      · exact not_leₓ.2 h
        
      
    · rwa [Finset.mem_range]
      
    · intro b hb hneq
      rw [Set.indicator_of_not_mem]
      exact hneq.symm
      
    

end AddCommMonoidₓ

section NormedGroup

variable [NormedGroup β] {p : ℝ≥0∞} {μ : Measure α}

theorem mem_ℒp_stopped_process (hτ : IsStoppingTime f τ) (hu : ∀ n, Memℒp (u n) p μ) (n : ℕ) :
    Memℒp (stoppedProcess u τ n) p μ := by
  rw [stopped_process_eq]
  refine' mem_ℒp.add _ _
  · exact mem_ℒp.indicator (f.le n { a : α | n ≤ τ a } (hτ.measurable_set_ge n)) (hu n)
    
  · suffices mem_ℒp (fun x => ∑ i : ℕ in Finset.range n, { a : α | τ a = i }.indicator (u i) x) p μ by
      convert this
      ext1 x
      simp only [← Finset.sum_apply]
    refine' mem_ℒp_finset_sum _ fun i hi => mem_ℒp.indicator _ (hu i)
    exact f.le i { a : α | τ a = i } (hτ.measurable_set_eq i)
    

theorem integrable_stopped_process (hτ : IsStoppingTime f τ) (hu : ∀ n, Integrable (u n) μ) (n : ℕ) :
    Integrable (stoppedProcess u τ n) μ := by
  simp_rw [← mem_ℒp_one_iff_integrable] at hu⊢
  exact mem_ℒp_stopped_process hτ hu n

theorem mem_ℒp_stopped_value (hτ : IsStoppingTime f τ) (hu : ∀ n, Memℒp (u n) p μ) {N : ℕ} (hbdd : ∀ x, τ x ≤ N) :
    Memℒp (stoppedValue u τ) p μ := by
  rw [stopped_value_eq hbdd]
  suffices mem_ℒp (fun x => ∑ i : ℕ in Finset.range (N + 1), { a : α | τ a = i }.indicator (u i) x) p μ by
    convert this
    ext1 x
    simp only [← Finset.sum_apply]
  refine' mem_ℒp_finset_sum _ fun i hi => mem_ℒp.indicator _ (hu i)
  exact f.le i { a : α | τ a = i } (hτ.measurable_set_eq i)

theorem integrable_stopped_value (hτ : IsStoppingTime f τ) (hu : ∀ n, Integrable (u n) μ) {N : ℕ}
    (hbdd : ∀ x, τ x ≤ N) : Integrable (stoppedValue u τ) μ := by
  simp_rw [← mem_ℒp_one_iff_integrable] at hu⊢
  exact mem_ℒp_stopped_value hτ hu hbdd

end NormedGroup

end Nat

section PiecewiseConst

variable [Preorderₓ ι] {𝒢 : Filtration ι m} {τ η : α → ι} {i j : ι} {s : Set α} [DecidablePred (· ∈ s)]

/-- Given stopping times `τ` and `η` which are bounded below, `set.piecewise s τ η` is also
a stopping time with respect to the same filtration. -/
theorem IsStoppingTime.piecewise_of_le (hτ_st : IsStoppingTime 𝒢 τ) (hη_st : IsStoppingTime 𝒢 η) (hτ : ∀ x, i ≤ τ x)
    (hη : ∀ x, i ≤ η x) (hs : measurable_set[𝒢 i] s) : IsStoppingTime 𝒢 (s.piecewise τ η) := by
  intro n
  have : { x | s.piecewise τ η x ≤ n } = s ∩ { x | τ x ≤ n } ∪ sᶜ ∩ { x | η x ≤ n } := by
    ext1 x
    simp only [← Set.piecewise, ← Set.mem_inter_eq, ← Set.mem_set_of_eq, ← And.congr_right_iff]
    by_cases' hx : x ∈ s <;> simp [← hx]
  rw [this]
  by_cases' hin : i ≤ n
  · have hs_n : measurable_set[𝒢 n] s := 𝒢.mono hin _ hs
    exact (hs_n.inter (hτ_st n)).union (hs_n.compl.inter (hη_st n))
    
  · have hτn : ∀ x, ¬τ x ≤ n := fun x hτn => hin ((hτ x).trans hτn)
    have hηn : ∀ x, ¬η x ≤ n := fun x hηn => hin ((hη x).trans hηn)
    simp [← hτn, ← hηn]
    

theorem is_stopping_time_piecewise_const (hij : i ≤ j) (hs : measurable_set[𝒢 i] s) :
    IsStoppingTime 𝒢 (s.piecewise (fun _ => i) fun _ => j) :=
  (is_stopping_time_const 𝒢 i).piecewise_of_le (is_stopping_time_const 𝒢 j) (fun x => le_rfl) (fun _ => hij) hs

theorem stopped_value_piecewise_const {ι' : Type _} {i j : ι'} {f : ι' → α → ℝ} :
    stoppedValue f (s.piecewise (fun _ => i) fun _ => j) = s.piecewise (f i) (f j) := by
  ext x
  rw [stopped_value]
  by_cases' hx : x ∈ s <;> simp [← hx]

theorem stopped_value_piecewise_const' {ι' : Type _} {i j : ι'} {f : ι' → α → ℝ} :
    stoppedValue f (s.piecewise (fun _ => i) fun _ => j) = s.indicator (f i) + sᶜ.indicator (f j) := by
  ext x
  rw [stopped_value]
  by_cases' hx : x ∈ s <;> simp [← hx]

end PiecewiseConst

end MeasureTheory

