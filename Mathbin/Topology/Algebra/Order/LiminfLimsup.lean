/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Yury Kudryashov
-/
import Mathbin.Order.LiminfLimsup
import Mathbin.Topology.Algebra.Order.Basic

/-!
# Lemmas about liminf and limsup in an order topology.
-/


open Filter

open TopologicalSpace Classical

universe u v

variable {α : Type u} {β : Type v}

section LiminfLimsup

section OrderClosedTopology

variable [SemilatticeSup α] [TopologicalSpace α] [OrderTopology α]

theorem is_bounded_le_nhds (a : α) : (𝓝 a).IsBounded (· ≤ ·) :=
  (is_top_or_exists_gt a).elim (fun h => ⟨a, eventually_of_forall h⟩) fun ⟨b, hb⟩ => ⟨b, ge_mem_nhds hb⟩

theorem Filter.Tendsto.is_bounded_under_le {f : Filter β} {u : β → α} {a : α} (h : Tendsto u f (𝓝 a)) :
    f.IsBoundedUnder (· ≤ ·) u :=
  (is_bounded_le_nhds a).mono h

theorem Filter.Tendsto.bdd_above_range_of_cofinite {u : β → α} {a : α} (h : Tendsto u cofinite (𝓝 a)) :
    BddAbove (Set.Range u) :=
  h.is_bounded_under_le.bdd_above_range_of_cofinite

theorem Filter.Tendsto.bdd_above_range {u : ℕ → α} {a : α} (h : Tendsto u atTop (𝓝 a)) : BddAbove (Set.Range u) :=
  h.is_bounded_under_le.bdd_above_range

theorem is_cobounded_ge_nhds (a : α) : (𝓝 a).IsCobounded (· ≥ ·) :=
  (is_bounded_le_nhds a).is_cobounded_flip

theorem Filter.Tendsto.is_cobounded_under_ge {f : Filter β} {u : β → α} {a : α} [NeBot f] (h : Tendsto u f (𝓝 a)) :
    f.IsCoboundedUnder (· ≥ ·) u :=
  h.is_bounded_under_le.is_cobounded_flip

end OrderClosedTopology

section OrderClosedTopology

variable [SemilatticeInf α] [TopologicalSpace α] [OrderTopology α]

theorem is_bounded_ge_nhds (a : α) : (𝓝 a).IsBounded (· ≥ ·) :=
  @is_bounded_le_nhds αᵒᵈ _ _ _ a

theorem Filter.Tendsto.is_bounded_under_ge {f : Filter β} {u : β → α} {a : α} (h : Tendsto u f (𝓝 a)) :
    f.IsBoundedUnder (· ≥ ·) u :=
  (is_bounded_ge_nhds a).mono h

theorem Filter.Tendsto.bdd_below_range_of_cofinite {u : β → α} {a : α} (h : Tendsto u cofinite (𝓝 a)) :
    BddBelow (Set.Range u) :=
  h.is_bounded_under_ge.bdd_below_range_of_cofinite

theorem Filter.Tendsto.bdd_below_range {u : ℕ → α} {a : α} (h : Tendsto u atTop (𝓝 a)) : BddBelow (Set.Range u) :=
  h.is_bounded_under_ge.bdd_below_range

theorem is_cobounded_le_nhds (a : α) : (𝓝 a).IsCobounded (· ≤ ·) :=
  (is_bounded_ge_nhds a).is_cobounded_flip

theorem Filter.Tendsto.is_cobounded_under_le {f : Filter β} {u : β → α} {a : α} [NeBot f] (h : Tendsto u f (𝓝 a)) :
    f.IsCoboundedUnder (· ≤ ·) u :=
  h.is_bounded_under_ge.is_cobounded_flip

end OrderClosedTopology

section ConditionallyCompleteLinearOrder

variable [ConditionallyCompleteLinearOrder α]

theorem lt_mem_sets_of_Limsup_lt {f : Filter α} {b} (h : f.IsBounded (· ≤ ·)) (l : f.limsup < b) : ∀ᶠ a in f, a < b :=
  let ⟨c, (h : ∀ᶠ a in f, a ≤ c), hcb⟩ := exists_lt_of_cInf_lt h l
  (mem_of_superset h) fun a hac => lt_of_le_of_ltₓ hac hcb

theorem gt_mem_sets_of_Liminf_gt : ∀ {f : Filter α} {b}, f.IsBounded (· ≥ ·) → b < f.liminf → ∀ᶠ a in f, b < a :=
  @lt_mem_sets_of_Limsup_lt αᵒᵈ _

variable [TopologicalSpace α] [OrderTopology α]

/-- If the liminf and the limsup of a filter coincide, then this filter converges to
their common value, at least if the filter is eventually bounded above and below. -/
theorem le_nhds_of_Limsup_eq_Liminf {f : Filter α} {a : α} (hl : f.IsBounded (· ≤ ·)) (hg : f.IsBounded (· ≥ ·))
    (hs : f.limsup = a) (hi : f.liminf = a) : f ≤ 𝓝 a :=
  tendsto_order.2 <|
    And.intro (fun b hb => gt_mem_sets_of_Liminf_gt hg <| hi.symm ▸ hb) fun b hb =>
      lt_mem_sets_of_Limsup_lt hl <| hs.symm ▸ hb

theorem Limsup_nhds (a : α) : limsup (𝓝 a) = a :=
  cInf_eq_of_forall_ge_of_forall_gt_exists_lt (is_bounded_le_nhds a)
    (fun a' (h : { n : α | n ≤ a' } ∈ 𝓝 a) => show a ≤ a' from @mem_of_mem_nhds α _ a _ h) fun b (hba : a < b) =>
    show ∃ (c : _)(h : { n : α | n ≤ c } ∈ 𝓝 a), c < b from
      match dense_or_discrete a b with
      | Or.inl ⟨c, hac, hcb⟩ => ⟨c, ge_mem_nhds hac, hcb⟩
      | Or.inr ⟨_, h⟩ => ⟨a, (𝓝 a).sets_of_superset (gt_mem_nhds hba) h, hba⟩

theorem Liminf_nhds : ∀ a : α, liminf (𝓝 a) = a :=
  @Limsup_nhds αᵒᵈ _ _ _

/-- If a filter is converging, its limsup coincides with its limit. -/
theorem Liminf_eq_of_le_nhds {f : Filter α} {a : α} [NeBot f] (h : f ≤ 𝓝 a) : f.liminf = a :=
  have hb_ge : IsBounded (· ≥ ·) f := (is_bounded_ge_nhds a).mono h
  have hb_le : IsBounded (· ≤ ·) f := (is_bounded_le_nhds a).mono h
  le_antisymmₓ
    (calc
      f.liminf ≤ f.limsup := Liminf_le_Limsup hb_le hb_ge
      _ ≤ (𝓝 a).limsup := Limsup_le_Limsup_of_le h hb_ge.is_cobounded_flip (is_bounded_le_nhds a)
      _ = a := Limsup_nhds a
      )
    (calc
      a = (𝓝 a).liminf := (Liminf_nhds a).symm
      _ ≤ f.liminf := Liminf_le_Liminf_of_le h (is_bounded_ge_nhds a) hb_le.is_cobounded_flip
      )

/-- If a filter is converging, its liminf coincides with its limit. -/
theorem Limsup_eq_of_le_nhds : ∀ {f : Filter α} {a : α} [NeBot f], f ≤ 𝓝 a → f.limsup = a :=
  @Liminf_eq_of_le_nhds αᵒᵈ _ _ _

/-- If a function has a limit, then its limsup coincides with its limit. -/
theorem Filter.Tendsto.limsup_eq {f : Filter β} {u : β → α} {a : α} [NeBot f] (h : Tendsto u f (𝓝 a)) :
    limsupₓ f u = a :=
  Limsup_eq_of_le_nhds h

/-- If a function has a limit, then its liminf coincides with its limit. -/
theorem Filter.Tendsto.liminf_eq {f : Filter β} {u : β → α} {a : α} [NeBot f] (h : Tendsto u f (𝓝 a)) :
    liminfₓ f u = a :=
  Liminf_eq_of_le_nhds h

/-- If the liminf and the limsup of a function coincide, then the limit of the function
exists and has the same value -/
theorem tendsto_of_liminf_eq_limsup {f : Filter β} {u : β → α} {a : α} (hinf : liminfₓ f u = a) (hsup : limsupₓ f u = a)
    (h : f.IsBoundedUnder (· ≤ ·) u := by
      run_tac
        is_bounded_default)
    (h' : f.IsBoundedUnder (· ≥ ·) u := by
      run_tac
        is_bounded_default) :
    Tendsto u f (𝓝 a) :=
  le_nhds_of_Limsup_eq_Liminf h h' hsup hinf

/-- If a number `a` is less than or equal to the `liminf` of a function `f` at some filter
and is greater than or equal to the `limsup` of `f`, then `f` tends to `a` along this filter. -/
theorem tendsto_of_le_liminf_of_limsup_le {f : Filter β} {u : β → α} {a : α} (hinf : a ≤ liminfₓ f u)
    (hsup : limsupₓ f u ≤ a)
    (h : f.IsBoundedUnder (· ≤ ·) u := by
      run_tac
        is_bounded_default)
    (h' : f.IsBoundedUnder (· ≥ ·) u := by
      run_tac
        is_bounded_default) :
    Tendsto u f (𝓝 a) :=
  if hf : f = ⊥ then hf.symm ▸ tendsto_bot
  else
    have : ne_bot f := ⟨hf⟩
    tendsto_of_liminf_eq_limsup (le_antisymmₓ (le_transₓ (liminf_le_limsup h h') hsup) hinf)
      (le_antisymmₓ hsup (le_transₓ hinf (liminf_le_limsup h h'))) h h'

/-- Assume that, for any `a < b`, a sequence can not be infinitely many times below `a` and
above `b`. If it is also ultimately bounded above and below, then it has to converge. This even
works if `a` and `b` are restricted to a dense subset.
-/
theorem tendsto_of_no_upcrossings [DenselyOrdered α] {f : Filter β} {u : β → α} {s : Set α} (hs : Dense s)
    (H : ∀, ∀ a ∈ s, ∀, ∀ b ∈ s, ∀, a < b → ¬((∃ᶠ n in f, u n < a) ∧ ∃ᶠ n in f, b < u n))
    (h : f.IsBoundedUnder (· ≤ ·) u := by
      run_tac
        is_bounded_default)
    (h' : f.IsBoundedUnder (· ≥ ·) u := by
      run_tac
        is_bounded_default) :
    ∃ c : α, Tendsto u f (𝓝 c) := by
  by_cases' hbot : f = ⊥
  · rw [hbot]
    exact ⟨Inf ∅, tendsto_bot⟩
    
  have : ne_bot f := ⟨hbot⟩
  refine' ⟨limsup f u, _⟩
  apply tendsto_of_le_liminf_of_limsup_le _ le_rfl h h'
  by_contra' hlt
  obtain ⟨a, ⟨⟨la, au⟩, as⟩⟩ : ∃ a, (f.liminf u < a ∧ a < f.limsup u) ∧ a ∈ s :=
    dense_iff_inter_open.1 hs (Set.Ioo (f.liminf u) (f.limsup u)) is_open_Ioo (Set.nonempty_Ioo.2 hlt)
  obtain ⟨b, ⟨⟨ab, bu⟩, bs⟩⟩ : ∃ b, (a < b ∧ b < f.limsup u) ∧ b ∈ s :=
    dense_iff_inter_open.1 hs (Set.Ioo a (f.limsup u)) is_open_Ioo (Set.nonempty_Ioo.2 au)
  have A : ∃ᶠ n in f, u n < a := frequently_lt_of_liminf_lt (is_bounded.is_cobounded_ge h) la
  have B : ∃ᶠ n in f, b < u n := frequently_lt_of_lt_limsup (is_bounded.is_cobounded_le h') bu
  exact H a as b bs ab ⟨A, B⟩

end ConditionallyCompleteLinearOrder

end LiminfLimsup

