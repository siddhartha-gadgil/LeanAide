/-
Copyright (c) 2020 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Mario Carneiro
-/
import Mathbin.Tactic.ByContra
import Mathbin.Data.Set.Basic

/-!
# Well-founded relations

A relation is well-founded if it can be used for induction: for each `x`, `(∀ y, r y x → P y) → P x`
implies `P x`. Well-founded relations can be used for induction and recursion, including
construction of fixed points in the space of dependent functions `Π x : α , β x`.

The predicate `well_founded` is defined in the core library. In this file we prove some extra lemmas
and provide a few new definitions: `well_founded.min`, `well_founded.sup`, and `well_founded.succ`.
-/


variable {α : Type _}

namespace WellFounded

theorem not_gt_of_lt {α : Sort _} {r : α → α → Prop} (h : WellFounded r) : ∀ ⦃a b⦄, r a b → ¬r b a
  | a => fun b hab hba => not_gt_of_lt hba hab

protected theorem is_asymm {α : Sort _} {r : α → α → Prop} (h : WellFounded r) : IsAsymm α r :=
  ⟨h.not_gt_of_lt⟩

instance {α : Sort _} [HasWellFounded α] : IsAsymm α HasWellFounded.R :=
  HasWellFounded.wf.IsAsymm

protected theorem is_irrefl {α : Sort _} {r : α → α → Prop} (h : WellFounded r) : IsIrrefl α r :=
  @IsAsymm.is_irrefl α r h.IsAsymm

instance {α : Sort _} [HasWellFounded α] : IsIrrefl α HasWellFounded.R :=
  IsAsymm.is_irrefl

/-- If `r` is a well-founded relation, then any nonempty set has a minimal element
with respect to `r`. -/
theorem has_min {α} {r : α → α → Prop} (H : WellFounded r) (s : Set α) : s.Nonempty → ∃ a ∈ s, ∀, ∀ x ∈ s, ∀, ¬r x a
  | ⟨a, ha⟩ =>
    ((Acc.recOnₓ (H.apply a)) fun x _ IH =>
        not_imp_not.1 fun hne hx => hne <| ⟨x, hx, fun y hy hyx => hne <| IH y hyx hy⟩)
      ha

/-- A minimal element of a nonempty set in a well-founded order.

If you're working with a nonempty linear order, consider defining a
`conditionally_complete_linear_order_bot` instance via
`well_founded.conditionally_complete_linear_order_with_bot` and using `Inf` instead. -/
noncomputable def min {r : α → α → Prop} (H : WellFounded r) (p : Set α) (h : p.Nonempty) : α :=
  Classical.some (H.has_min p h)

theorem min_mem {r : α → α → Prop} (H : WellFounded r) (p : Set α) (h : p.Nonempty) : H.min p h ∈ p :=
  let ⟨h, _⟩ := Classical.some_spec (H.has_min p h)
  h

theorem not_lt_min {r : α → α → Prop} (H : WellFounded r) (p : Set α) (h : p.Nonempty) {x} (xp : x ∈ p) :
    ¬r x (H.min p h) :=
  let ⟨_, h'⟩ := Classical.some_spec (H.has_min p h)
  h' _ xp

theorem well_founded_iff_has_min {r : α → α → Prop} :
    WellFounded r ↔ ∀ p : Set α, p.Nonempty → ∃ m ∈ p, ∀, ∀ x ∈ p, ∀, ¬r x m := by
  classical
  constructor
  · exact has_min
    
  · set counterexamples := { x : α | ¬Acc r x }
    intro exists_max
    fconstructor
    intro x
    by_contra hx
    obtain ⟨m, m_mem, hm⟩ := exists_max counterexamples ⟨x, hx⟩
    refine' m_mem (Acc.intro _ fun y y_gt_m => _)
    by_contra hy
    exact hm y hy y_gt_m
    

theorem eq_iff_not_lt_of_le {α} [PartialOrderₓ α] {x y : α} : x ≤ y → y = x ↔ ¬x < y := by
  constructor
  · intro xle nge
    cases le_not_le_of_ltₓ nge
    rw [xle left] at nge
    exact lt_irreflₓ x nge
    
  · intro ngt xle
    contrapose! ngt
    exact lt_of_le_of_neₓ xle (Ne.symm ngt)
    

theorem well_founded_iff_has_max' [PartialOrderₓ α] :
    WellFounded ((· > ·) : α → α → Prop) ↔ ∀ p : Set α, p.Nonempty → ∃ m ∈ p, ∀, ∀ x ∈ p, ∀, m ≤ x → x = m := by
  simp only [← eq_iff_not_lt_of_le, ← well_founded_iff_has_min]

theorem well_founded_iff_has_min' [PartialOrderₓ α] :
    WellFounded (LT.lt : α → α → Prop) ↔ ∀ p : Set α, p.Nonempty → ∃ m ∈ p, ∀, ∀ x ∈ p, ∀, x ≤ m → x = m :=
  @well_founded_iff_has_max' αᵒᵈ _

open Set

/-- The supremum of a bounded, well-founded order -/
protected noncomputable def sup {r : α → α → Prop} (wf : WellFounded r) (s : Set α) (h : Bounded r s) : α :=
  wf.min { x | ∀, ∀ a ∈ s, ∀, r a x } h

protected theorem lt_sup {r : α → α → Prop} (wf : WellFounded r) {s : Set α} (h : Bounded r s) {x} (hx : x ∈ s) :
    r x (wf.sup s h) :=
  min_mem wf { x | ∀, ∀ a ∈ s, ∀, r a x } h x hx

section

open Classical

/-- A successor of an element `x` in a well-founded order is a minimal element `y` such that
`x < y` if one exists. Otherwise it is `x` itself. -/
protected noncomputable def succ {r : α → α → Prop} (wf : WellFounded r) (x : α) : α :=
  if h : ∃ y, r x y then wf.min { y | r x y } h else x

protected theorem lt_succ {r : α → α → Prop} (wf : WellFounded r) {x : α} (h : ∃ y, r x y) : r x (wf.succ x) := by
  rw [WellFounded.succ, dif_pos h]
  apply min_mem

end

protected theorem lt_succ_iff {r : α → α → Prop} [wo : IsWellOrder α r] {x : α} (h : ∃ y, r x y) (y : α) :
    r y (wo.wf.succ x) ↔ r y x ∨ y = x := by
  constructor
  · intro h'
    have : ¬r x y := by
      intro hy
      rw [WellFounded.succ, dif_pos] at h'
      exact wo.wf.not_lt_min _ h hy h'
    rcases trichotomous_of r x y with (hy | hy | hy)
    exfalso
    exact this hy
    right
    exact hy.symm
    left
    exact hy
    
  rintro (hy | rfl)
  exact trans hy (wo.wf.lt_succ h)
  exact wo.wf.lt_succ h

section LinearOrderₓ

variable {β : Type _} [LinearOrderₓ β] (h : WellFounded ((· < ·) : β → β → Prop)) {γ : Type _} [PartialOrderₓ γ]

theorem min_le {x : β} {s : Set β} (hx : x ∈ s) (hne : s.Nonempty := ⟨x, hx⟩) : h.min s hne ≤ x :=
  not_ltₓ.1 <| h.not_lt_min _ _ hx

private theorem eq_strict_mono_iff_eq_range_aux {f g : β → γ} (hf : StrictMono f) (hg : StrictMono g)
    (hfg : Set.Range f = Set.Range g) {b : β} (H : ∀, ∀ a < b, ∀, f a = g a) : f b ≤ g b := by
  obtain ⟨c, hc⟩ : g b ∈ Set.Range f := by
    rw [hfg]
    exact Set.mem_range_self b
  cases' lt_or_leₓ c b with hcb hbc
  · rw [H c hcb] at hc
    rw [hg.injective hc] at hcb
    exact hcb.false.elim
    
  · rw [← hc]
    exact hf.monotone hbc
    

include h

theorem eq_strict_mono_iff_eq_range {f g : β → γ} (hf : StrictMono f) (hg : StrictMono g) :
    Set.Range f = Set.Range g ↔ f = g :=
  ⟨fun hfg => by
    funext a
    apply h.induction a
    exact fun b H =>
      le_antisymmₓ (eq_strict_mono_iff_eq_range_aux hf hg hfg H)
        (eq_strict_mono_iff_eq_range_aux hg hf hfg.symm fun a hab => (H a hab).symm),
    congr_arg _⟩

theorem self_le_of_strict_mono {φ : β → β} (hφ : StrictMono φ) : ∀ n, n ≤ φ n := by
  by_contra' h₁
  have h₂ := h.min_mem _ h₁
  exact h.not_lt_min _ h₁ (hφ h₂) h₂

end LinearOrderₓ

end WellFounded

namespace Function

variable {β : Type _} (f : α → β)

section LT

variable [LT β] (h : WellFounded ((· < ·) : β → β → Prop))

/-- Given a function `f : α → β` where `β` carries a well-founded `<`, this is an element of `α`
whose image under `f` is minimal in the sense of `function.not_lt_argmin`. -/
noncomputable def argmin [Nonempty α] : α :=
  WellFounded.min (InvImage.wfₓ f h) Set.Univ Set.univ_nonempty

theorem not_lt_argmin [Nonempty α] (a : α) : ¬f a < f (argmin f h) :=
  WellFounded.not_lt_min (InvImage.wfₓ f h) _ _ (Set.mem_univ a)

/-- Given a function `f : α → β` where `β` carries a well-founded `<`, and a non-empty subset `s`
of `α`, this is an element of `s` whose image under `f` is minimal in the sense of
`function.not_lt_argmin_on`. -/
noncomputable def argminOn (s : Set α) (hs : s.Nonempty) : α :=
  WellFounded.min (InvImage.wfₓ f h) s hs

@[simp]
theorem argmin_on_mem (s : Set α) (hs : s.Nonempty) : argminOn f h s hs ∈ s :=
  WellFounded.min_mem _ _ _

@[simp]
theorem not_lt_argmin_on (s : Set α) {a : α} (ha : a ∈ s) (hs : s.Nonempty := Set.nonempty_of_mem ha) :
    ¬f a < f (argminOn f h s hs) :=
  WellFounded.not_lt_min (InvImage.wfₓ f h) s hs ha

end LT

section LinearOrderₓ

variable [LinearOrderₓ β] (h : WellFounded ((· < ·) : β → β → Prop))

@[simp]
theorem argmin_le (a : α) [Nonempty α] : f (argmin f h) ≤ f a :=
  not_ltₓ.mp <| not_lt_argmin f h a

@[simp]
theorem argmin_on_le (s : Set α) {a : α} (ha : a ∈ s) (hs : s.Nonempty := Set.nonempty_of_mem ha) :
    f (argminOn f h s hs) ≤ f a :=
  not_ltₓ.mp <| not_lt_argmin_on f h s ha hs

end LinearOrderₓ

end Function

