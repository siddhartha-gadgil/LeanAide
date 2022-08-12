/-
Copyright (c) 2018 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Johannes Hölzl, Rémy Degenne
-/
import Mathbin.Order.Filter.Cofinite

/-!
# liminfs and limsups of functions and filters

Defines the Liminf/Limsup of a function taking values in a conditionally complete lattice, with
respect to an arbitrary filter.

We define `f.Limsup` (`f.Liminf`) where `f` is a filter taking values in a conditionally complete
lattice. `f.Limsup` is the smallest element `a` such that, eventually, `u ≤ a` (and vice versa for
`f.Liminf`). To work with the Limsup along a function `u` use `(f.map u).Limsup`.

Usually, one defines the Limsup as `Inf (Sup s)` where the Inf is taken over all sets in the filter.
For instance, in ℕ along a function `u`, this is `Inf_n (Sup_{k ≥ n} u k)` (and the latter quantity
decreases with `n`, so this is in fact a limit.). There is however a difficulty: it is well possible
that `u` is not bounded on the whole space, only eventually (think of `Limsup (λx, 1/x)` on ℝ. Then
there is no guarantee that the quantity above really decreases (the value of the `Sup` beforehand is
not really well defined, as one can not use ∞), so that the Inf could be anything. So one can not
use this `Inf Sup ...` definition in conditionally complete lattices, and one has to use a less
tractable definition.

In conditionally complete lattices, the definition is only useful for filters which are eventually
bounded above (otherwise, the Limsup would morally be +∞, which does not belong to the space) and
which are frequently bounded below (otherwise, the Limsup would morally be -∞, which is not in the
space either). We start with definitions of these concepts for arbitrary filters, before turning to
the definitions of Limsup and Liminf.

In complete lattices, however, it coincides with the `Inf Sup` definition.
-/


open Filter Set

open Filter

variable {α β γ ι : Type _}

namespace Filter

section Relation

/-- `f.is_bounded (≺)`: the filter `f` is eventually bounded w.r.t. the relation `≺`, i.e.
eventually, it is bounded by some uniform bound.
`r` will be usually instantiated with `≤` or `≥`. -/
def IsBounded (r : α → α → Prop) (f : Filter α) :=
  ∃ b, ∀ᶠ x in f, r x b

/-- `f.is_bounded_under (≺) u`: the image of the filter `f` under `u` is eventually bounded w.r.t.
the relation `≺`, i.e. eventually, it is bounded by some uniform bound. -/
def IsBoundedUnder (r : α → α → Prop) (f : Filter β) (u : β → α) :=
  (f.map u).IsBounded r

variable {r : α → α → Prop} {f g : Filter α}

/-- `f` is eventually bounded if and only if, there exists an admissible set on which it is
bounded. -/
theorem is_bounded_iff : f.IsBounded r ↔ ∃ s ∈ f.Sets, ∃ b, s ⊆ { x | r x b } :=
  Iff.intro (fun ⟨b, hb⟩ => ⟨{ a | r a b }, hb, b, Subset.refl _⟩) fun ⟨s, hs, b, hb⟩ => ⟨b, mem_of_superset hs hb⟩

/-- A bounded function `u` is in particular eventually bounded. -/
theorem is_bounded_under_of {f : Filter β} {u : β → α} : (∃ b, ∀ x, r (u x) b) → f.IsBoundedUnder r u
  | ⟨b, hb⟩ => ⟨b, show ∀ᶠ x in f, r (u x) b from eventually_of_forall hb⟩

theorem is_bounded_bot : IsBounded r ⊥ ↔ Nonempty α := by
  simp [← is_bounded, ← exists_true_iff_nonempty]

theorem is_bounded_top : IsBounded r ⊤ ↔ ∃ t, ∀ x, r x t := by
  simp [← is_bounded, ← eq_univ_iff_forall]

theorem is_bounded_principal (s : Set α) : IsBounded r (𝓟 s) ↔ ∃ t, ∀, ∀ x ∈ s, ∀, r x t := by
  simp [← is_bounded, ← subset_def]

theorem is_bounded_sup [IsTrans α r] (hr : ∀ b₁ b₂, ∃ b, r b₁ b ∧ r b₂ b) :
    IsBounded r f → IsBounded r g → IsBounded r (f⊔g)
  | ⟨b₁, h₁⟩, ⟨b₂, h₂⟩ =>
    let ⟨b, rb₁b, rb₂b⟩ := hr b₁ b₂
    ⟨b, eventually_sup.mpr ⟨h₁.mono fun x h => trans h rb₁b, h₂.mono fun x h => trans h rb₂b⟩⟩

theorem IsBounded.mono (h : f ≤ g) : IsBounded r g → IsBounded r f
  | ⟨b, hb⟩ => ⟨b, h hb⟩

theorem IsBoundedUnder.mono {f g : Filter β} {u : β → α} (h : f ≤ g) : g.IsBoundedUnder r u → f.IsBoundedUnder r u :=
  fun hg => hg.mono (map_mono h)

theorem IsBoundedUnder.mono_le [Preorderₓ β] {l : Filter α} {u v : α → β} (hu : IsBoundedUnder (· ≤ ·) l u)
    (hv : v ≤ᶠ[l] u) : IsBoundedUnder (· ≤ ·) l v :=
  hu.imp fun b hb => (eventually_map.1 hb).mp <| hv.mono fun x => le_transₓ

theorem IsBoundedUnder.mono_ge [Preorderₓ β] {l : Filter α} {u v : α → β} (hu : IsBoundedUnder (· ≥ ·) l u)
    (hv : u ≤ᶠ[l] v) : IsBoundedUnder (· ≥ ·) l v :=
  @IsBoundedUnder.mono_le α βᵒᵈ _ _ _ _ hu hv

theorem IsBounded.is_bounded_under {q : β → β → Prop} {u : α → β} (hf : ∀ a₀ a₁, r a₀ a₁ → q (u a₀) (u a₁)) :
    f.IsBounded r → f.IsBoundedUnder q u
  | ⟨b, h⟩ => ⟨u b, show ∀ᶠ x in f, q (u x) (u b) from h.mono fun x => hf x b⟩

theorem not_is_bounded_under_of_tendsto_at_top [Preorderₓ β] [NoMaxOrder β] {f : α → β} {l : Filter α} [l.ne_bot]
    (hf : Tendsto f l atTop) : ¬IsBoundedUnder (· ≤ ·) l f := by
  rintro ⟨b, hb⟩
  rw [eventually_map] at hb
  obtain ⟨b', h⟩ := exists_gt b
  have hb' := (tendsto_at_top.mp hf) b'
  have : { x : α | f x ≤ b } ∩ { x : α | b' ≤ f x } = ∅ :=
    eq_empty_of_subset_empty fun x hx => (not_le_of_lt h) (le_transₓ hx.2 hx.1)
  exact (nonempty_of_mem (hb.and hb')).ne_empty this

theorem not_is_bounded_under_of_tendsto_at_bot [Preorderₓ β] [NoMinOrder β] {f : α → β} {l : Filter α} [l.ne_bot]
    (hf : Tendsto f l atBot) : ¬IsBoundedUnder (· ≥ ·) l f :=
  @not_is_bounded_under_of_tendsto_at_top α βᵒᵈ _ _ _ _ _ hf

theorem IsBoundedUnder.bdd_above_range_of_cofinite [SemilatticeSup β] {f : α → β}
    (hf : IsBoundedUnder (· ≤ ·) cofinite f) : BddAbove (Range f) := by
  rcases hf with ⟨b, hb⟩
  have : Nonempty β := ⟨b⟩
  rw [← image_univ, ← union_compl_self { x | f x ≤ b }, image_union, bdd_above_union]
  exact ⟨⟨b, ball_image_iff.2 fun x => id⟩, (hb.image f).BddAbove⟩

theorem IsBoundedUnder.bdd_below_range_of_cofinite [SemilatticeInf β] {f : α → β}
    (hf : IsBoundedUnder (· ≥ ·) cofinite f) : BddBelow (Range f) :=
  @IsBoundedUnder.bdd_above_range_of_cofinite α βᵒᵈ _ _ hf

theorem IsBoundedUnder.bdd_above_range [SemilatticeSup β] {f : ℕ → β} (hf : IsBoundedUnder (· ≤ ·) atTop f) :
    BddAbove (Range f) := by
  rw [← Nat.cofinite_eq_at_top] at hf
  exact hf.bdd_above_range_of_cofinite

theorem IsBoundedUnder.bdd_below_range [SemilatticeInf β] {f : ℕ → β} (hf : IsBoundedUnder (· ≥ ·) atTop f) :
    BddBelow (Range f) :=
  @IsBoundedUnder.bdd_above_range βᵒᵈ _ _ hf

/-- `is_cobounded (≺) f` states that the filter `f` does not tend to infinity w.r.t. `≺`. This is
also called frequently bounded. Will be usually instantiated with `≤` or `≥`.

There is a subtlety in this definition: we want `f.is_cobounded` to hold for any `f` in the case of
complete lattices. This will be relevant to deduce theorems on complete lattices from their
versions on conditionally complete lattices with additional assumptions. We have to be careful in
the edge case of the trivial filter containing the empty set: the other natural definition
  `¬ ∀ a, ∀ᶠ n in f, a ≤ n`
would not work as well in this case.
-/
def IsCobounded (r : α → α → Prop) (f : Filter α) :=
  ∃ b, ∀ a, (∀ᶠ x in f, r x a) → r b a

/-- `is_cobounded_under (≺) f u` states that the image of the filter `f` under the map `u` does not
tend to infinity w.r.t. `≺`. This is also called frequently bounded. Will be usually instantiated
with `≤` or `≥`. -/
def IsCoboundedUnder (r : α → α → Prop) (f : Filter β) (u : β → α) :=
  (f.map u).IsCobounded r

/-- To check that a filter is frequently bounded, it suffices to have a witness
which bounds `f` at some point for every admissible set.

This is only an implication, as the other direction is wrong for the trivial filter.-/
theorem IsCobounded.mk [IsTrans α r] (a : α) (h : ∀, ∀ s ∈ f, ∀, ∃ x ∈ s, r a x) : f.IsCobounded r :=
  ⟨a, fun y s =>
    let ⟨x, h₁, h₂⟩ := h _ s
    trans h₂ h₁⟩

/-- A filter which is eventually bounded is in particular frequently bounded (in the opposite
direction). At least if the filter is not trivial. -/
theorem IsBounded.is_cobounded_flip [IsTrans α r] [NeBot f] : f.IsBounded r → f.IsCobounded (flip r)
  | ⟨a, ha⟩ =>
    ⟨a, fun b hb =>
      let ⟨x, rxa, rbx⟩ := (ha.And hb).exists
      show r b a from trans rbx rxa⟩

theorem IsBounded.is_cobounded_ge [Preorderₓ α] [NeBot f] (h : f.IsBounded (· ≤ ·)) : f.IsCobounded (· ≥ ·) :=
  h.is_cobounded_flip

theorem IsBounded.is_cobounded_le [Preorderₓ α] [NeBot f] (h : f.IsBounded (· ≥ ·)) : f.IsCobounded (· ≤ ·) :=
  h.is_cobounded_flip

theorem is_cobounded_bot : IsCobounded r ⊥ ↔ ∃ b, ∀ x, r b x := by
  simp [← is_cobounded]

theorem is_cobounded_top : IsCobounded r ⊤ ↔ Nonempty α := by
  simp (config := { contextual := true })[← is_cobounded, ← eq_univ_iff_forall, ← exists_true_iff_nonempty]

theorem is_cobounded_principal (s : Set α) : (𝓟 s).IsCobounded r ↔ ∃ b, ∀ a, (∀, ∀ x ∈ s, ∀, r x a) → r b a := by
  simp [← is_cobounded, ← subset_def]

theorem IsCobounded.mono (h : f ≤ g) : f.IsCobounded r → g.IsCobounded r
  | ⟨b, hb⟩ => ⟨b, fun a ha => hb a (h ha)⟩

end Relation

theorem is_cobounded_le_of_bot [Preorderₓ α] [OrderBot α] {f : Filter α} : f.IsCobounded (· ≤ ·) :=
  ⟨⊥, fun a h => bot_le⟩

theorem is_cobounded_ge_of_top [Preorderₓ α] [OrderTop α] {f : Filter α} : f.IsCobounded (· ≥ ·) :=
  ⟨⊤, fun a h => le_top⟩

theorem is_bounded_le_of_top [Preorderₓ α] [OrderTop α] {f : Filter α} : f.IsBounded (· ≤ ·) :=
  ⟨⊤, eventually_of_forall fun _ => le_top⟩

theorem is_bounded_ge_of_bot [Preorderₓ α] [OrderBot α] {f : Filter α} : f.IsBounded (· ≥ ·) :=
  ⟨⊥, eventually_of_forall fun _ => bot_le⟩

@[simp]
theorem _root_.order_iso.is_bounded_under_le_comp [Preorderₓ α] [Preorderₓ β] (e : α ≃o β) {l : Filter γ} {u : γ → α} :
    (IsBoundedUnder (· ≤ ·) l fun x => e (u x)) ↔ IsBoundedUnder (· ≤ ·) l u :=
  e.Surjective.exists.trans <|
    exists_congr fun a => by
      simp only [← eventually_map, ← e.le_iff_le]

@[simp]
theorem _root_.order_iso.is_bounded_under_ge_comp [Preorderₓ α] [Preorderₓ β] (e : α ≃o β) {l : Filter γ} {u : γ → α} :
    (IsBoundedUnder (· ≥ ·) l fun x => e (u x)) ↔ IsBoundedUnder (· ≥ ·) l u :=
  e.dual.is_bounded_under_le_comp

@[simp, to_additive]
theorem is_bounded_under_le_inv [OrderedCommGroup α] {l : Filter β} {u : β → α} :
    (IsBoundedUnder (· ≤ ·) l fun x => (u x)⁻¹) ↔ IsBoundedUnder (· ≥ ·) l u :=
  (OrderIso.inv α).is_bounded_under_ge_comp

@[simp, to_additive]
theorem is_bounded_under_ge_inv [OrderedCommGroup α] {l : Filter β} {u : β → α} :
    (IsBoundedUnder (· ≥ ·) l fun x => (u x)⁻¹) ↔ IsBoundedUnder (· ≤ ·) l u :=
  (OrderIso.inv α).is_bounded_under_le_comp

theorem IsBoundedUnder.sup [SemilatticeSup α] {f : Filter β} {u v : β → α} :
    f.IsBoundedUnder (· ≤ ·) u → f.IsBoundedUnder (· ≤ ·) v → f.IsBoundedUnder (· ≤ ·) fun a => u a⊔v a
  | ⟨bu, (hu : ∀ᶠ x in f, u x ≤ bu)⟩, ⟨bv, (hv : ∀ᶠ x in f, v x ≤ bv)⟩ =>
    ⟨bu⊔bv,
      show ∀ᶠ x in f, u x⊔v x ≤ bu⊔bv by
        filter_upwards [hu, hv] with _ using sup_le_sup⟩

@[simp]
theorem is_bounded_under_le_sup [SemilatticeSup α] {f : Filter β} {u v : β → α} :
    (f.IsBoundedUnder (· ≤ ·) fun a => u a⊔v a) ↔ f.IsBoundedUnder (· ≤ ·) u ∧ f.IsBoundedUnder (· ≤ ·) v :=
  ⟨fun h =>
    ⟨h.mono_le <| eventually_of_forall fun _ => le_sup_left, h.mono_le <| eventually_of_forall fun _ => le_sup_right⟩,
    fun h => h.1.sup h.2⟩

theorem IsBoundedUnder.inf [SemilatticeInf α] {f : Filter β} {u v : β → α} :
    f.IsBoundedUnder (· ≥ ·) u → f.IsBoundedUnder (· ≥ ·) v → f.IsBoundedUnder (· ≥ ·) fun a => u a⊓v a :=
  @IsBoundedUnder.sup αᵒᵈ β _ _ _ _

@[simp]
theorem is_bounded_under_ge_inf [SemilatticeInf α] {f : Filter β} {u v : β → α} :
    (f.IsBoundedUnder (· ≥ ·) fun a => u a⊓v a) ↔ f.IsBoundedUnder (· ≥ ·) u ∧ f.IsBoundedUnder (· ≥ ·) v :=
  @is_bounded_under_le_sup αᵒᵈ _ _ _ _ _

theorem is_bounded_under_le_abs [LinearOrderedAddCommGroup α] {f : Filter β} {u : β → α} :
    (f.IsBoundedUnder (· ≤ ·) fun a => abs (u a)) ↔ f.IsBoundedUnder (· ≤ ·) u ∧ f.IsBoundedUnder (· ≥ ·) u :=
  is_bounded_under_le_sup.trans <| and_congr Iff.rfl is_bounded_under_le_neg

/-- Filters are automatically bounded or cobounded in complete lattices. To use the same statements
in complete and conditionally complete lattices but let automation fill automatically the
boundedness proofs in complete lattices, we use the tactic `is_bounded_default` in the statements,
in the form `(hf : f.is_bounded (≥) . is_bounded_default)`. -/
unsafe def is_bounded_default : tactic Unit :=
  tactic.applyc `` is_cobounded_le_of_bot <|>
    tactic.applyc `` is_cobounded_ge_of_top <|>
      tactic.applyc `` is_bounded_le_of_top <|> tactic.applyc `` is_bounded_ge_of_bot

section ConditionallyCompleteLattice

variable [ConditionallyCompleteLattice α]

/-- The `Limsup` of a filter `f` is the infimum of the `a` such that, eventually for `f`,
holds `x ≤ a`. -/
def limsup (f : Filter α) : α :=
  inf { a | ∀ᶠ n in f, n ≤ a }

/-- The `Liminf` of a filter `f` is the supremum of the `a` such that, eventually for `f`,
holds `x ≥ a`. -/
def liminf (f : Filter α) : α :=
  sup { a | ∀ᶠ n in f, a ≤ n }

/-- The `limsup` of a function `u` along a filter `f` is the infimum of the `a` such that,
eventually for `f`, holds `u x ≤ a`. -/
def limsupₓ (f : Filter β) (u : β → α) : α :=
  (f.map u).limsup

/-- The `liminf` of a function `u` along a filter `f` is the supremum of the `a` such that,
eventually for `f`, holds `u x ≥ a`. -/
def liminfₓ (f : Filter β) (u : β → α) : α :=
  (f.map u).liminf

section

variable {f : Filter β} {u : β → α}

theorem limsup_eq : f.limsup u = inf { a | ∀ᶠ n in f, u n ≤ a } :=
  rfl

theorem liminf_eq : f.liminf u = sup { a | ∀ᶠ n in f, a ≤ u n } :=
  rfl

end

theorem Limsup_le_of_le {f : Filter α} {a}
    (hf : f.IsCobounded (· ≤ ·) := by
      run_tac
        is_bounded_default)
    (h : ∀ᶠ n in f, n ≤ a) : f.limsup ≤ a :=
  cInf_le hf h

theorem le_Liminf_of_le {f : Filter α} {a}
    (hf : f.IsCobounded (· ≥ ·) := by
      run_tac
        is_bounded_default)
    (h : ∀ᶠ n in f, a ≤ n) : a ≤ f.liminf :=
  le_cSup hf h

theorem le_Limsup_of_le {f : Filter α} {a}
    (hf : f.IsBounded (· ≤ ·) := by
      run_tac
        is_bounded_default)
    (h : ∀ b, (∀ᶠ n in f, n ≤ b) → a ≤ b) : a ≤ f.limsup :=
  le_cInf hf h

theorem Liminf_le_of_le {f : Filter α} {a}
    (hf : f.IsBounded (· ≥ ·) := by
      run_tac
        is_bounded_default)
    (h : ∀ b, (∀ᶠ n in f, b ≤ n) → b ≤ a) : f.liminf ≤ a :=
  cSup_le hf h

theorem Liminf_le_Limsup {f : Filter α} [NeBot f]
    (h₁ : f.IsBounded (· ≤ ·) := by
      run_tac
        is_bounded_default)
    (h₂ : f.IsBounded (· ≥ ·) := by
      run_tac
        is_bounded_default) :
    f.liminf ≤ f.limsup :=
  (Liminf_le_of_le h₂) fun a₀ ha₀ =>
    (le_Limsup_of_le h₁) fun a₁ ha₁ =>
      show a₀ ≤ a₁ from
        let ⟨b, hb₀, hb₁⟩ := (ha₀.And ha₁).exists
        le_transₓ hb₀ hb₁

theorem Liminf_le_Liminf {f g : Filter α}
    (hf : f.IsBounded (· ≥ ·) := by
      run_tac
        is_bounded_default)
    (hg : g.IsCobounded (· ≥ ·) := by
      run_tac
        is_bounded_default)
    (h : ∀ a, (∀ᶠ n in f, a ≤ n) → ∀ᶠ n in g, a ≤ n) : f.liminf ≤ g.liminf :=
  cSup_le_cSup hg hf h

theorem Limsup_le_Limsup {f g : Filter α}
    (hf : f.IsCobounded (· ≤ ·) := by
      run_tac
        is_bounded_default)
    (hg : g.IsBounded (· ≤ ·) := by
      run_tac
        is_bounded_default)
    (h : ∀ a, (∀ᶠ n in g, n ≤ a) → ∀ᶠ n in f, n ≤ a) : f.limsup ≤ g.limsup :=
  cInf_le_cInf hf hg h

theorem Limsup_le_Limsup_of_le {f g : Filter α} (h : f ≤ g)
    (hf : f.IsCobounded (· ≤ ·) := by
      run_tac
        is_bounded_default)
    (hg : g.IsBounded (· ≤ ·) := by
      run_tac
        is_bounded_default) :
    f.limsup ≤ g.limsup :=
  Limsup_le_Limsup hf hg fun a ha => h ha

theorem Liminf_le_Liminf_of_le {f g : Filter α} (h : g ≤ f)
    (hf : f.IsBounded (· ≥ ·) := by
      run_tac
        is_bounded_default)
    (hg : g.IsCobounded (· ≥ ·) := by
      run_tac
        is_bounded_default) :
    f.liminf ≤ g.liminf :=
  Liminf_le_Liminf hf hg fun a ha => h ha

theorem limsup_le_limsup {α : Type _} [ConditionallyCompleteLattice β] {f : Filter α} {u v : α → β} (h : u ≤ᶠ[f] v)
    (hu : f.IsCoboundedUnder (· ≤ ·) u := by
      run_tac
        is_bounded_default)
    (hv : f.IsBoundedUnder (· ≤ ·) v := by
      run_tac
        is_bounded_default) :
    f.limsup u ≤ f.limsup v :=
  (Limsup_le_Limsup hu hv) fun b => h.trans

theorem liminf_le_liminf {α : Type _} [ConditionallyCompleteLattice β] {f : Filter α} {u v : α → β}
    (h : ∀ᶠ a in f, u a ≤ v a)
    (hu : f.IsBoundedUnder (· ≥ ·) u := by
      run_tac
        is_bounded_default)
    (hv : f.IsCoboundedUnder (· ≥ ·) v := by
      run_tac
        is_bounded_default) :
    f.liminf u ≤ f.liminf v :=
  @limsup_le_limsup βᵒᵈ α _ _ _ _ h hv hu

theorem limsup_le_limsup_of_le {α β} [ConditionallyCompleteLattice β] {f g : Filter α} (h : f ≤ g) {u : α → β}
    (hf : f.IsCoboundedUnder (· ≤ ·) u := by
      run_tac
        is_bounded_default)
    (hg : g.IsBoundedUnder (· ≤ ·) u := by
      run_tac
        is_bounded_default) :
    f.limsup u ≤ g.limsup u :=
  Limsup_le_Limsup_of_le (map_mono h) hf hg

theorem liminf_le_liminf_of_le {α β} [ConditionallyCompleteLattice β] {f g : Filter α} (h : g ≤ f) {u : α → β}
    (hf : f.IsBoundedUnder (· ≥ ·) u := by
      run_tac
        is_bounded_default)
    (hg : g.IsCoboundedUnder (· ≥ ·) u := by
      run_tac
        is_bounded_default) :
    f.liminf u ≤ g.liminf u :=
  Liminf_le_Liminf_of_le (map_mono h) hf hg

theorem Limsup_principal {s : Set α} (h : BddAbove s) (hs : s.Nonempty) : (𝓟 s).limsup = sup s := by
  simp [← Limsup] <;> exact cInf_upper_bounds_eq_cSup h hs

theorem Liminf_principal {s : Set α} (h : BddBelow s) (hs : s.Nonempty) : (𝓟 s).liminf = inf s :=
  @Limsup_principal αᵒᵈ _ s h hs

theorem limsup_congr {α : Type _} [ConditionallyCompleteLattice β] {f : Filter α} {u v : α → β}
    (h : ∀ᶠ a in f, u a = v a) : limsupₓ f u = limsupₓ f v := by
  rw [limsup_eq]
  congr with b
  exact
    eventually_congr
      (h.mono fun x hx => by
        simp [← hx])

theorem liminf_congr {α : Type _} [ConditionallyCompleteLattice β] {f : Filter α} {u v : α → β}
    (h : ∀ᶠ a in f, u a = v a) : liminfₓ f u = liminfₓ f v :=
  @limsup_congr βᵒᵈ _ _ _ _ _ h

theorem limsup_const {α : Type _} [ConditionallyCompleteLattice β] {f : Filter α} [NeBot f] (b : β) :
    (limsupₓ f fun x => b) = b := by
  simpa only [← limsup_eq, ← eventually_const] using cInf_Ici

theorem liminf_const {α : Type _} [ConditionallyCompleteLattice β] {f : Filter α} [NeBot f] (b : β) :
    (liminfₓ f fun x => b) = b :=
  @limsup_const βᵒᵈ α _ f _ b

theorem liminf_le_limsup {f : Filter β} [NeBot f] {u : β → α}
    (h : f.IsBoundedUnder (· ≤ ·) u := by
      run_tac
        is_bounded_default)
    (h' : f.IsBoundedUnder (· ≥ ·) u := by
      run_tac
        is_bounded_default) :
    liminfₓ f u ≤ limsupₓ f u :=
  Liminf_le_Limsup h h'

end ConditionallyCompleteLattice

section CompleteLattice

variable [CompleteLattice α]

@[simp]
theorem Limsup_bot : (⊥ : Filter α).limsup = ⊥ :=
  bot_unique <|
    Inf_le <| by
      simp

@[simp]
theorem Liminf_bot : (⊥ : Filter α).liminf = ⊤ :=
  top_unique <|
    le_Sup <| by
      simp

@[simp]
theorem Limsup_top : (⊤ : Filter α).limsup = ⊤ :=
  top_unique <|
    le_Inf <| by
      simp [← eq_univ_iff_forall] <;> exact fun b hb => top_unique <| hb _

@[simp]
theorem Liminf_top : (⊤ : Filter α).liminf = ⊥ :=
  bot_unique <|
    Sup_le <| by
      simp [← eq_univ_iff_forall] <;> exact fun b hb => bot_unique <| hb _

/-- Same as limsup_const applied to `⊥` but without the `ne_bot f` assumption -/
theorem limsup_const_bot {f : Filter β} : (limsupₓ f fun x : β => (⊥ : α)) = (⊥ : α) := by
  rw [limsup_eq, eq_bot_iff]
  exact Inf_le (eventually_of_forall fun x => le_rfl)

/-- Same as limsup_const applied to `⊤` but without the `ne_bot f` assumption -/
theorem liminf_const_top {f : Filter β} : (liminfₓ f fun x : β => (⊤ : α)) = (⊤ : α) :=
  @limsup_const_bot αᵒᵈ β _ _

theorem HasBasis.Limsup_eq_infi_Sup {ι} {p : ι → Prop} {s} {f : Filter α} (h : f.HasBasis p s) :
    f.limsup = ⨅ (i) (hi : p i), sup (s i) :=
  le_antisymmₓ (le_infi₂ fun i hi => Inf_le <| h.eventually_iff.2 ⟨i, hi, fun x => le_Sup⟩)
    (le_Inf fun a ha =>
      let ⟨i, hi, ha⟩ := h.eventually_iff.1 ha
      infi₂_le_of_le _ hi <| Sup_le ha)

theorem HasBasis.Liminf_eq_supr_Inf {p : ι → Prop} {s : ι → Set α} {f : Filter α} (h : f.HasBasis p s) :
    f.liminf = ⨆ (i) (hi : p i), inf (s i) :=
  @HasBasis.Limsup_eq_infi_Sup αᵒᵈ _ _ _ _ _ h

theorem Limsup_eq_infi_Sup {f : Filter α} : f.limsup = ⨅ s ∈ f, sup s :=
  f.basis_sets.Limsup_eq_infi_Sup

theorem Liminf_eq_supr_Inf {f : Filter α} : f.liminf = ⨆ s ∈ f, inf s :=
  @Limsup_eq_infi_Sup αᵒᵈ _ _

/-- In a complete lattice, the limsup of a function is the infimum over sets `s` in the filter
of the supremum of the function over `s` -/
theorem limsup_eq_infi_supr {f : Filter β} {u : β → α} : f.limsup u = ⨅ s ∈ f, ⨆ a ∈ s, u a :=
  (f.basis_sets.map u).Limsup_eq_infi_Sup.trans <| by
    simp only [← Sup_image, ← id]

theorem limsup_eq_infi_supr_of_nat {u : ℕ → α} : limsupₓ atTop u = ⨅ n : ℕ, ⨆ i ≥ n, u i :=
  (at_top_basis.map u).Limsup_eq_infi_Sup.trans <| by
    simp only [← Sup_image, ← infi_const] <;> rfl

theorem limsup_eq_infi_supr_of_nat' {u : ℕ → α} : limsupₓ atTop u = ⨅ n : ℕ, ⨆ i : ℕ, u (i + n) := by
  simp only [← limsup_eq_infi_supr_of_nat, ← supr_ge_eq_supr_nat_add]

theorem HasBasis.limsup_eq_infi_supr {p : ι → Prop} {s : ι → Set β} {f : Filter β} {u : β → α} (h : f.HasBasis p s) :
    f.limsup u = ⨅ (i) (hi : p i), ⨆ a ∈ s i, u a :=
  (h.map u).Limsup_eq_infi_Sup.trans <| by
    simp only [← Sup_image, ← id]

/-- In a complete lattice, the liminf of a function is the infimum over sets `s` in the filter
of the supremum of the function over `s` -/
theorem liminf_eq_supr_infi {f : Filter β} {u : β → α} : f.liminf u = ⨆ s ∈ f, ⨅ a ∈ s, u a :=
  @limsup_eq_infi_supr αᵒᵈ β _ _ _

theorem liminf_eq_supr_infi_of_nat {u : ℕ → α} : liminfₓ atTop u = ⨆ n : ℕ, ⨅ i ≥ n, u i :=
  @limsup_eq_infi_supr_of_nat αᵒᵈ _ u

theorem liminf_eq_supr_infi_of_nat' {u : ℕ → α} : liminfₓ atTop u = ⨆ n : ℕ, ⨅ i : ℕ, u (i + n) :=
  @limsup_eq_infi_supr_of_nat' αᵒᵈ _ _

theorem HasBasis.liminf_eq_supr_infi {p : ι → Prop} {s : ι → Set β} {f : Filter β} {u : β → α} (h : f.HasBasis p s) :
    f.liminf u = ⨆ (i) (hi : p i), ⨅ a ∈ s i, u a :=
  @HasBasis.limsup_eq_infi_supr αᵒᵈ _ _ _ _ _ _ _ h

@[simp]
theorem liminf_nat_add (f : ℕ → α) (k : ℕ) : (atTop.liminf fun i => f (i + k)) = atTop.liminf f := by
  simp_rw [liminf_eq_supr_infi_of_nat]
  exact supr_infi_ge_nat_add f k

@[simp]
theorem limsup_nat_add (f : ℕ → α) (k : ℕ) : (atTop.limsup fun i => f (i + k)) = atTop.limsup f :=
  @liminf_nat_add αᵒᵈ _ f k

theorem liminf_le_of_frequently_le' {α β} [CompleteLattice β] {f : Filter α} {u : α → β} {x : β}
    (h : ∃ᶠ a in f, u a ≤ x) : f.liminf u ≤ x := by
  rw [liminf_eq]
  refine' Sup_le fun b hb => _
  have hbx : ∃ᶠ a in f, b ≤ x := by
    revert h
    rw [← not_imp_not, not_frequently, not_frequently]
    exact fun h => hb.mp (h.mono fun a hbx hba hax => hbx (hba.trans hax))
  exact hbx.exists.some_spec

theorem le_limsup_of_frequently_le' {α β} [CompleteLattice β] {f : Filter α} {u : α → β} {x : β}
    (h : ∃ᶠ a in f, x ≤ u a) : x ≤ f.limsup u :=
  @liminf_le_of_frequently_le' _ βᵒᵈ _ _ _ _ h

end CompleteLattice

section ConditionallyCompleteLinearOrder

theorem eventually_lt_of_lt_liminf {f : Filter α} [ConditionallyCompleteLinearOrder β] {u : α → β} {b : β}
    (h : b < liminfₓ f u)
    (hu : f.IsBoundedUnder (· ≥ ·) u := by
      run_tac
        is_bounded_default) :
    ∀ᶠ a in f, b < u a := by
  obtain ⟨c, hc, hbc⟩ : ∃ (c : β)(hc : c ∈ { c : β | ∀ᶠ n : α in f, c ≤ u n }), b < c := exists_lt_of_lt_cSup hu h
  exact hc.mono fun x hx => lt_of_lt_of_leₓ hbc hx

theorem eventually_lt_of_limsup_lt {f : Filter α} [ConditionallyCompleteLinearOrder β] {u : α → β} {b : β}
    (h : limsupₓ f u < b)
    (hu : f.IsBoundedUnder (· ≤ ·) u := by
      run_tac
        is_bounded_default) :
    ∀ᶠ a in f, u a < b :=
  @eventually_lt_of_lt_liminf _ βᵒᵈ _ _ _ _ h hu

theorem le_limsup_of_frequently_le {α β} [ConditionallyCompleteLinearOrder β] {f : Filter α} {u : α → β} {b : β}
    (hu_le : ∃ᶠ x in f, b ≤ u x)
    (hu : f.IsBoundedUnder (· ≤ ·) u := by
      run_tac
        is_bounded_default) :
    b ≤ f.limsup u := by
  revert hu_le
  rw [← not_imp_not, not_frequently]
  simp_rw [← lt_iff_not_geₓ]
  exact fun h => eventually_lt_of_limsup_lt h hu

theorem liminf_le_of_frequently_le {α β} [ConditionallyCompleteLinearOrder β] {f : Filter α} {u : α → β} {b : β}
    (hu_le : ∃ᶠ x in f, u x ≤ b)
    (hu : f.IsBoundedUnder (· ≥ ·) u := by
      run_tac
        is_bounded_default) :
    f.liminf u ≤ b :=
  @le_limsup_of_frequently_le _ βᵒᵈ _ f u b hu_le hu

theorem frequently_lt_of_lt_limsup {α β} [ConditionallyCompleteLinearOrder β] {f : Filter α} {u : α → β} {b : β}
    (hu : f.IsCoboundedUnder (· ≤ ·) u := by
      run_tac
        is_bounded_default)
    (h : b < f.limsup u) : ∃ᶠ x in f, b < u x := by
  contrapose! h
  apply Limsup_le_of_le hu
  simpa using h

theorem frequently_lt_of_liminf_lt {α β} [ConditionallyCompleteLinearOrder β] {f : Filter α} {u : α → β} {b : β}
    (hu : f.IsCoboundedUnder (· ≥ ·) u := by
      run_tac
        is_bounded_default)
    (h : f.liminf u < b) : ∃ᶠ x in f, u x < b :=
  @frequently_lt_of_lt_limsup _ βᵒᵈ _ f u b hu h

end ConditionallyCompleteLinearOrder

end Filter

section Order

open Filter

theorem Monotone.is_bounded_under_le_comp [Nonempty β] [LinearOrderₓ β] [Preorderₓ γ] [NoMaxOrder γ] {g : β → γ}
    {f : α → β} {l : Filter α} (hg : Monotone g) (hg' : Tendsto g atTop atTop) :
    IsBoundedUnder (· ≤ ·) l (g ∘ f) ↔ IsBoundedUnder (· ≤ ·) l f := by
  refine' ⟨_, fun h => h.IsBoundedUnder hg⟩
  rintro ⟨c, hc⟩
  rw [eventually_map] at hc
  obtain ⟨b, hb⟩ : ∃ b, ∀, ∀ a ≥ b, ∀, c < g a := eventually_at_top.1 (hg'.eventually_gt_at_top c)
  exact ⟨b, hc.mono fun x hx => not_ltₓ.1 fun h => (hb _ h.le).not_le hx⟩

theorem Monotone.is_bounded_under_ge_comp [Nonempty β] [LinearOrderₓ β] [Preorderₓ γ] [NoMinOrder γ] {g : β → γ}
    {f : α → β} {l : Filter α} (hg : Monotone g) (hg' : Tendsto g atBot atBot) :
    IsBoundedUnder (· ≥ ·) l (g ∘ f) ↔ IsBoundedUnder (· ≥ ·) l f :=
  hg.dual.is_bounded_under_le_comp hg'

theorem Antitone.is_bounded_under_le_comp [Nonempty β] [LinearOrderₓ β] [Preorderₓ γ] [NoMaxOrder γ] {g : β → γ}
    {f : α → β} {l : Filter α} (hg : Antitone g) (hg' : Tendsto g atBot atTop) :
    IsBoundedUnder (· ≤ ·) l (g ∘ f) ↔ IsBoundedUnder (· ≥ ·) l f :=
  hg.dual_right.is_bounded_under_ge_comp hg'

theorem Antitone.is_bounded_under_ge_comp [Nonempty β] [LinearOrderₓ β] [Preorderₓ γ] [NoMinOrder γ] {g : β → γ}
    {f : α → β} {l : Filter α} (hg : Antitone g) (hg' : Tendsto g atTop atBot) :
    IsBoundedUnder (· ≥ ·) l (g ∘ f) ↔ IsBoundedUnder (· ≤ ·) l f :=
  hg.dual_right.is_bounded_under_le_comp hg'

theorem GaloisConnection.l_limsup_le [ConditionallyCompleteLattice β] [ConditionallyCompleteLattice γ] {f : Filter α}
    {v : α → β} {l : β → γ} {u : γ → β} (gc : GaloisConnection l u)
    (hlv : f.IsBoundedUnder (· ≤ ·) fun x => l (v x) := by
      run_tac
        is_bounded_default)
    (hv_co : f.IsCoboundedUnder (· ≤ ·) v := by
      run_tac
        is_bounded_default) :
    l (f.limsup v) ≤ f.limsup fun x => l (v x) := by
  refine' le_Limsup_of_le hlv fun c hc => _
  rw [Filter.eventually_map] at hc
  simp_rw [gc _ _] at hc⊢
  exact Limsup_le_of_le hv_co hc

theorem OrderIso.limsup_apply {γ} [ConditionallyCompleteLattice β] [ConditionallyCompleteLattice γ] {f : Filter α}
    {u : α → β} (g : β ≃o γ)
    (hu : f.IsBoundedUnder (· ≤ ·) u := by
      run_tac
        is_bounded_default)
    (hu_co : f.IsCoboundedUnder (· ≤ ·) u := by
      run_tac
        is_bounded_default)
    (hgu : f.IsBoundedUnder (· ≤ ·) fun x => g (u x) := by
      run_tac
        is_bounded_default)
    (hgu_co : f.IsCoboundedUnder (· ≤ ·) fun x => g (u x) := by
      run_tac
        is_bounded_default) :
    g (f.limsup u) = f.limsup fun x => g (u x) := by
  refine' le_antisymmₓ (g.to_galois_connection.l_limsup_le hgu hu_co) _
  rw [← g.symm.symm_apply_apply (f.limsup fun x : α => g (u x)), g.symm_symm]
  refine' g.monotone _
  have hf : u = fun i => g.symm (g (u i)) := funext fun i => (g.symm_apply_apply (u i)).symm
  nth_rw 0[hf]
  refine' g.symm.to_galois_connection.l_limsup_le _ hgu_co
  simp_rw [g.symm_apply_apply]
  exact hu

theorem OrderIso.liminf_apply {γ} [ConditionallyCompleteLattice β] [ConditionallyCompleteLattice γ] {f : Filter α}
    {u : α → β} (g : β ≃o γ)
    (hu : f.IsBoundedUnder (· ≥ ·) u := by
      run_tac
        is_bounded_default)
    (hu_co : f.IsCoboundedUnder (· ≥ ·) u := by
      run_tac
        is_bounded_default)
    (hgu : f.IsBoundedUnder (· ≥ ·) fun x => g (u x) := by
      run_tac
        is_bounded_default)
    (hgu_co : f.IsCoboundedUnder (· ≥ ·) fun x => g (u x) := by
      run_tac
        is_bounded_default) :
    g (f.liminf u) = f.liminf fun x => g (u x) :=
  @OrderIso.limsup_apply α βᵒᵈ γᵒᵈ _ _ f u g.dual hu hu_co hgu hgu_co

end Order

