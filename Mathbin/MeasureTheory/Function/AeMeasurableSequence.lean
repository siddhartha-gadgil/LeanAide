/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathbin.MeasureTheory.MeasurableSpace

/-!
# Sequence of measurable functions associated to a sequence of a.e.-measurable functions

We define here tools to prove statements about limits (infi, supr...) of sequences of
`ae_measurable` functions.
Given a sequence of a.e.-measurable functions `f : ι → α → β` with hypothesis
`hf : ∀ i, ae_measurable (f i) μ`, and a pointwise property `p : α → (ι → β) → Prop` such that we
have `hp : ∀ᵐ x ∂μ, p x (λ n, f n x)`, we define a sequence of measurable functions `ae_seq hf p`
and a measurable set `ae_seq_set hf p`, such that
* `μ (ae_seq_set hf p)ᶜ = 0`
* `x ∈ ae_seq_set hf p → ∀ i : ι, ae_seq hf hp i x = f i x`
* `x ∈ ae_seq_set hf p → p x (λ n, f n x)`
-/


open MeasureTheory

open Classical

variable {α β γ ι : Type _} [MeasurableSpace α] [MeasurableSpace β] {f : ι → α → β} {μ : Measureₓ α}
  {p : α → (ι → β) → Prop}

/-- If we have the additional hypothesis `∀ᵐ x ∂μ, p x (λ n, f n x)`, this is a measurable set
whose complement has measure 0 such that for all `x ∈ ae_seq_set`, `f i x` is equal to
`(hf i).mk (f i) x` for all `i` and we have the pointwise property `p x (λ n, f n x)`. -/
def AeSeqSet (hf : ∀ i, AeMeasurable (f i) μ) (p : α → (ι → β) → Prop) : Set α :=
  ToMeasurable μ ({ x | (∀ i, f i x = (hf i).mk (f i) x) ∧ p x fun n => f n x }ᶜ)ᶜ

/-- A sequence of measurable functions that are equal to `f` and verify property `p` on the
measurable set `ae_seq_set hf p`. -/
noncomputable def aeSeq (hf : ∀ i, AeMeasurable (f i) μ) (p : α → (ι → β) → Prop) : ι → α → β := fun i x =>
  ite (x ∈ AeSeqSet hf p) ((hf i).mk (f i) x) (⟨f i x⟩ : Nonempty β).some

namespace aeSeq

section MemAeSeqSet

theorem mk_eq_fun_of_mem_ae_seq_set (hf : ∀ i, AeMeasurable (f i) μ) {x : α} (hx : x ∈ AeSeqSet hf p) (i : ι) :
    (hf i).mk (f i) x = f i x := by
  have h_ss : AeSeqSet hf p ⊆ { x | ∀ i, f i x = (hf i).mk (f i) x } := by
    rw [AeSeqSet, ← compl_compl { x | ∀ i, f i x = (hf i).mk (f i) x }, Set.compl_subset_compl]
    refine' Set.Subset.trans (set.compl_subset_compl.mpr fun x h => _) (subset_to_measurable _ _)
    exact h.1
  exact (h_ss hx i).symm

theorem ae_seq_eq_mk_of_mem_ae_seq_set (hf : ∀ i, AeMeasurable (f i) μ) {x : α} (hx : x ∈ AeSeqSet hf p) (i : ι) :
    aeSeq hf p i x = (hf i).mk (f i) x := by
  simp only [← aeSeq, ← hx, ← if_true]

theorem ae_seq_eq_fun_of_mem_ae_seq_set (hf : ∀ i, AeMeasurable (f i) μ) {x : α} (hx : x ∈ AeSeqSet hf p) (i : ι) :
    aeSeq hf p i x = f i x := by
  simp only [← ae_seq_eq_mk_of_mem_ae_seq_set hf hx i, ← mk_eq_fun_of_mem_ae_seq_set hf hx i]

theorem prop_of_mem_ae_seq_set (hf : ∀ i, AeMeasurable (f i) μ) {x : α} (hx : x ∈ AeSeqSet hf p) :
    p x fun n => aeSeq hf p n x := by
  simp only [← aeSeq, ← hx, ← if_true]
  rw [funext fun n => mk_eq_fun_of_mem_ae_seq_set hf hx n]
  have h_ss : AeSeqSet hf p ⊆ { x | p x fun n => f n x } := by
    rw [← compl_compl { x | p x fun n => f n x }, AeSeqSet, Set.compl_subset_compl]
    refine' Set.Subset.trans (set.compl_subset_compl.mpr _) (subset_to_measurable _ _)
    exact fun x hx => hx.2
  have hx' := Set.mem_of_subset_of_mem h_ss hx
  exact hx'

theorem fun_prop_of_mem_ae_seq_set (hf : ∀ i, AeMeasurable (f i) μ) {x : α} (hx : x ∈ AeSeqSet hf p) :
    p x fun n => f n x := by
  have h_eq : (fun n => f n x) = fun n => aeSeq hf p n x :=
    funext fun n => (ae_seq_eq_fun_of_mem_ae_seq_set hf hx n).symm
  rw [h_eq]
  exact prop_of_mem_ae_seq_set hf hx

end MemAeSeqSet

theorem ae_seq_set_measurable_set {hf : ∀ i, AeMeasurable (f i) μ} : MeasurableSet (AeSeqSet hf p) :=
  (measurable_set_to_measurable _ _).compl

theorem measurable (hf : ∀ i, AeMeasurable (f i) μ) (p : α → (ι → β) → Prop) (i : ι) : Measurable (aeSeq hf p i) :=
  Measurable.ite ae_seq_set_measurable_set (hf i).measurable_mk <| measurable_const' fun x y => rfl

theorem measure_compl_ae_seq_set_eq_zero [Encodable ι] (hf : ∀ i, AeMeasurable (f i) μ)
    (hp : ∀ᵐ x ∂μ, p x fun n => f n x) : μ (AeSeqSet hf pᶜ) = 0 := by
  rw [AeSeqSet, compl_compl, measure_to_measurable]
  have hf_eq := fun i => (hf i).ae_eq_mk
  simp_rw [Filter.EventuallyEq, ← ae_all_iff] at hf_eq
  exact Filter.Eventually.and hf_eq hp

theorem ae_seq_eq_mk_ae [Encodable ι] (hf : ∀ i, AeMeasurable (f i) μ) (hp : ∀ᵐ x ∂μ, p x fun n => f n x) :
    ∀ᵐ a : α ∂μ, ∀ i : ι, aeSeq hf p i a = (hf i).mk (f i) a := by
  have h_ss : AeSeqSet hf p ⊆ { a : α | ∀ i, aeSeq hf p i a = (hf i).mk (f i) a } := fun x hx i => by
    simp only [← aeSeq, ← hx, ← if_true]
  exact
    le_antisymmₓ
      (le_transₓ (measure_mono (set.compl_subset_compl.mpr h_ss)) (le_of_eqₓ (measure_compl_ae_seq_set_eq_zero hf hp)))
      (zero_le _)

theorem ae_seq_eq_fun_ae [Encodable ι] (hf : ∀ i, AeMeasurable (f i) μ) (hp : ∀ᵐ x ∂μ, p x fun n => f n x) :
    ∀ᵐ a : α ∂μ, ∀ i : ι, aeSeq hf p i a = f i a := by
  have h_ss : { a : α | ¬∀ i : ι, aeSeq hf p i a = f i a } ⊆ AeSeqSet hf pᶜ := fun x =>
    mt fun hx i => ae_seq_eq_fun_of_mem_ae_seq_set hf hx i
  exact measure_mono_null h_ss (measure_compl_ae_seq_set_eq_zero hf hp)

theorem ae_seq_n_eq_fun_n_ae [Encodable ι] (hf : ∀ i, AeMeasurable (f i) μ) (hp : ∀ᵐ x ∂μ, p x fun n => f n x) (n : ι) :
    aeSeq hf p n =ᵐ[μ] f n :=
  ae_all_iff.mp (ae_seq_eq_fun_ae hf hp) n

theorem supr [CompleteLattice β] [Encodable ι] (hf : ∀ i, AeMeasurable (f i) μ) (hp : ∀ᵐ x ∂μ, p x fun n => f n x) :
    (⨆ n, aeSeq hf p n) =ᵐ[μ] ⨆ n, f n := by
  simp_rw [Filter.EventuallyEq, ae_iff, supr_apply]
  have h_ss : AeSeqSet hf p ⊆ { a : α | (⨆ i : ι, aeSeq hf p i a) = ⨆ i : ι, f i a } := by
    intro x hx
    congr
    exact funext fun i => ae_seq_eq_fun_of_mem_ae_seq_set hf hx i
  exact measure_mono_null (set.compl_subset_compl.mpr h_ss) (measure_compl_ae_seq_set_eq_zero hf hp)

end aeSeq

