/-
Copyright (c) 2018 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathbin.Order.Bounds
import Mathbin.Data.Set.Intervals.Basic
import Mathbin.Data.Set.Finite
import Mathbin.Data.Set.Lattice

/-!
# Theory of conditionally complete lattices.

A conditionally complete lattice is a lattice in which every non-empty bounded subset s
has a least upper bound and a greatest lower bound, denoted below by Sup s and Inf s.
Typical examples are real, nat, int with their usual orders.

The theory is very comparable to the theory of complete lattices, except that suitable
boundedness and nonemptiness assumptions have to be added to most statements.
We introduce two predicates bdd_above and bdd_below to express this boundedness, prove
their basic properties, and then go on to prove most useful properties of Sup and Inf
in conditionally complete lattices.

To differentiate the statements between complete lattices and conditionally complete
lattices, we prefix Inf and Sup in the statements by c, giving cInf and cSup. For instance,
Inf_le is a statement in complete lattices ensuring Inf s ≤ x, while cInf_le is the same
statement in conditionally complete lattices with an additional assumption that s is
bounded below.
-/


open Function OrderDual Set

variable {α β γ : Type _} {ι : Sort _}

section

/-!
Extension of Sup and Inf from a preorder `α` to `with_top α` and `with_bot α`
-/


open Classical

noncomputable instance {α : Type _} [Preorderₓ α] [HasSupₓ α] : HasSupₓ (WithTop α) :=
  ⟨fun S => if ⊤ ∈ S then ⊤ else if BddAbove (coe ⁻¹' S : Set α) then ↑(sup (coe ⁻¹' S : Set α)) else ⊤⟩

noncomputable instance {α : Type _} [HasInfₓ α] : HasInfₓ (WithTop α) :=
  ⟨fun S => if S ⊆ {⊤} then ⊤ else ↑(inf (coe ⁻¹' S : Set α))⟩

noncomputable instance {α : Type _} [HasSupₓ α] : HasSupₓ (WithBot α) :=
  ⟨(@WithTop.hasInf αᵒᵈ _).inf⟩

noncomputable instance {α : Type _} [Preorderₓ α] [HasInfₓ α] : HasInfₓ (WithBot α) :=
  ⟨(@WithTop.hasSup αᵒᵈ _ _).sup⟩

@[simp]
theorem WithTop.cInf_empty {α : Type _} [HasInfₓ α] : inf (∅ : Set (WithTop α)) = ⊤ :=
  if_pos <| Set.empty_subset _

@[simp]
theorem WithBot.cSup_empty {α : Type _} [HasSupₓ α] : sup (∅ : Set (WithBot α)) = ⊥ :=
  if_pos <| Set.empty_subset _

end

/-- A conditionally complete lattice is a lattice in which
every nonempty subset which is bounded above has a supremum, and
every nonempty subset which is bounded below has an infimum.
Typical examples are real numbers or natural numbers.

To differentiate the statements from the corresponding statements in (unconditional)
complete lattices, we prefix Inf and Sup by a c everywhere. The same statements should
hold in both worlds, sometimes with additional assumptions of nonemptiness or
boundedness.-/
-- section
class ConditionallyCompleteLattice (α : Type _) extends Lattice α, HasSupₓ α, HasInfₓ α where
  le_cSup : ∀ s a, BddAbove s → a ∈ s → a ≤ Sup s
  cSup_le : ∀ s a, Set.Nonempty s → a ∈ UpperBounds s → Sup s ≤ a
  cInf_le : ∀ s a, BddBelow s → a ∈ s → Inf s ≤ a
  le_cInf : ∀ s a, Set.Nonempty s → a ∈ LowerBounds s → a ≤ Inf s

-- ./././Mathport/Syntax/Translate/Basic.lean:1467:11: unsupported: advanced extends in structure
/-- A conditionally complete linear order is a linear order in which
every nonempty subset which is bounded above has a supremum, and
every nonempty subset which is bounded below has an infimum.
Typical examples are real numbers or natural numbers.

To differentiate the statements from the corresponding statements in (unconditional)
complete linear orders, we prefix Inf and Sup by a c everywhere. The same statements should
hold in both worlds, sometimes with additional assumptions of nonemptiness or
boundedness.-/
class ConditionallyCompleteLinearOrder (α : Type _) extends ConditionallyCompleteLattice α,
  "./././Mathport/Syntax/Translate/Basic.lean:1467:11: unsupported: advanced extends in structure"

/-- A conditionally complete linear order with `bot` is a linear order with least element, in which
every nonempty subset which is bounded above has a supremum, and every nonempty subset (necessarily
bounded below) has an infimum.  A typical example is the natural numbers.

To differentiate the statements from the corresponding statements in (unconditional)
complete linear orders, we prefix Inf and Sup by a c everywhere. The same statements should
hold in both worlds, sometimes with additional assumptions of nonemptiness or
boundedness.-/
@[ancestor ConditionallyCompleteLinearOrder HasBot]
class ConditionallyCompleteLinearOrderBot (α : Type _) extends ConditionallyCompleteLinearOrder α, HasBot α where
  bot_le : ∀ x : α, ⊥ ≤ x
  cSup_empty : Sup ∅ = ⊥

-- see Note [lower instance priority]
instance (priority := 100) ConditionallyCompleteLinearOrderBot.toOrderBot [h : ConditionallyCompleteLinearOrderBot α] :
    OrderBot α :=
  { h with }

/-- A complete lattice is a conditionally complete lattice, as there are no restrictions
on the properties of Inf and Sup in a complete lattice.-/
-- see Note [lower instance priority]
instance (priority := 100) CompleteLattice.toConditionallyCompleteLattice [CompleteLattice α] :
    ConditionallyCompleteLattice α :=
  { ‹CompleteLattice α› with
    le_cSup := by
      intros <;> apply le_Sup <;> assumption,
    cSup_le := by
      intros <;> apply Sup_le <;> assumption,
    cInf_le := by
      intros <;> apply Inf_le <;> assumption,
    le_cInf := by
      intros <;> apply le_Inf <;> assumption }

-- see Note [lower instance priority]
instance (priority := 100) CompleteLinearOrder.toConditionallyCompleteLinearOrderBot {α : Type _}
    [CompleteLinearOrder α] : ConditionallyCompleteLinearOrderBot α :=
  { CompleteLattice.toConditionallyCompleteLattice, ‹CompleteLinearOrder α› with cSup_empty := Sup_empty }

section

open Classical

/-- A well founded linear order is conditionally complete, with a bottom element. -/
@[reducible]
noncomputable def IsWellOrder.conditionallyCompleteLinearOrderBot (α : Type _) [i₁ : LinearOrderₓ α] [i₂ : OrderBot α]
    [h : IsWellOrder α (· < ·)] : ConditionallyCompleteLinearOrderBot α :=
  { i₁, i₂, LinearOrderₓ.toLattice with inf := fun s => if hs : s.Nonempty then h.wf.min s hs else ⊥,
    cInf_le := fun s a hs has => by
      have s_ne : s.nonempty := ⟨a, has⟩
      simpa [← s_ne] using not_ltₓ.1 (h.wf.not_lt_min s s_ne has),
    le_cInf := fun s a hs has => by
      simp only [← hs, ← dif_pos]
      exact has (h.wf.min_mem s hs),
    sup := fun s => if hs : (UpperBounds s).Nonempty then h.wf.min _ hs else ⊥,
    le_cSup := fun s a hs has => by
      have h's : (UpperBounds s).Nonempty := hs
      simp only [← h's, ← dif_pos]
      exact h.wf.min_mem _ h's has,
    cSup_le := fun s a hs has => by
      have h's : (UpperBounds s).Nonempty := ⟨a, has⟩
      simp only [← h's, ← dif_pos]
      simpa using h.wf.not_lt_min _ h's has,
    cSup_empty := by
      simpa using eq_bot_iff.2 (not_ltₓ.1 <| h.wf.not_lt_min _ _ <| mem_univ ⊥) }

end

section OrderDual

instance (α : Type _) [ConditionallyCompleteLattice α] : ConditionallyCompleteLattice αᵒᵈ :=
  { OrderDual.hasInfₓ α, OrderDual.hasSupₓ α, OrderDual.lattice α with
    le_cSup := @ConditionallyCompleteLattice.cInf_le α _, cSup_le := @ConditionallyCompleteLattice.le_cInf α _,
    le_cInf := @ConditionallyCompleteLattice.cSup_le α _, cInf_le := @ConditionallyCompleteLattice.le_cSup α _ }

instance (α : Type _) [ConditionallyCompleteLinearOrder α] : ConditionallyCompleteLinearOrder αᵒᵈ :=
  { OrderDual.conditionallyCompleteLattice α, OrderDual.linearOrder α with }

end OrderDual

section ConditionallyCompleteLattice

variable [ConditionallyCompleteLattice α] {s t : Set α} {a b : α}

theorem le_cSup (h₁ : BddAbove s) (h₂ : a ∈ s) : a ≤ sup s :=
  ConditionallyCompleteLattice.le_cSup s a h₁ h₂

theorem cSup_le (h₁ : s.Nonempty) (h₂ : ∀, ∀ b ∈ s, ∀, b ≤ a) : sup s ≤ a :=
  ConditionallyCompleteLattice.cSup_le s a h₁ h₂

theorem cInf_le (h₁ : BddBelow s) (h₂ : a ∈ s) : inf s ≤ a :=
  ConditionallyCompleteLattice.cInf_le s a h₁ h₂

theorem le_cInf (h₁ : s.Nonempty) (h₂ : ∀, ∀ b ∈ s, ∀, a ≤ b) : a ≤ inf s :=
  ConditionallyCompleteLattice.le_cInf s a h₁ h₂

theorem le_cSup_of_le (hs : BddAbove s) (hb : b ∈ s) (h : a ≤ b) : a ≤ sup s :=
  le_transₓ h (le_cSup hs hb)

theorem cInf_le_of_le (hs : BddBelow s) (hb : b ∈ s) (h : b ≤ a) : inf s ≤ a :=
  le_transₓ (cInf_le hs hb) h

theorem cSup_le_cSup (ht : BddAbove t) (hs : s.Nonempty) (h : s ⊆ t) : sup s ≤ sup t :=
  cSup_le hs fun a ha => le_cSup ht (h ha)

theorem cInf_le_cInf (ht : BddBelow t) (hs : s.Nonempty) (h : s ⊆ t) : inf t ≤ inf s :=
  le_cInf hs fun a ha => cInf_le ht (h ha)

theorem le_cSup_iff (h : BddAbove s) (hs : s.Nonempty) : a ≤ sup s ↔ ∀ b, b ∈ UpperBounds s → a ≤ b :=
  ⟨fun h b hb => le_transₓ h (cSup_le hs hb), fun hb => hb _ fun x => le_cSup h⟩

theorem cInf_le_iff (h : BddBelow s) (hs : s.Nonempty) : inf s ≤ a ↔ ∀, ∀ b ∈ LowerBounds s, ∀, b ≤ a :=
  ⟨fun h b hb => le_transₓ (le_cInf hs hb) h, fun hb => hb _ fun x => cInf_le h⟩

theorem is_lub_cSup (ne : s.Nonempty) (H : BddAbove s) : IsLub s (sup s) :=
  ⟨fun x => le_cSup H, fun x => cSup_le Ne⟩

theorem is_lub_csupr [Nonempty ι] {f : ι → α} (H : BddAbove (Range f)) : IsLub (Range f) (⨆ i, f i) :=
  is_lub_cSup (range_nonempty f) H

theorem is_lub_csupr_set {f : β → α} {s : Set β} (H : BddAbove (f '' s)) (Hne : s.Nonempty) :
    IsLub (f '' s) (⨆ i : s, f i) := by
  rw [← Sup_image']
  exact is_lub_cSup (Hne.image _) H

theorem is_glb_cInf (ne : s.Nonempty) (H : BddBelow s) : IsGlb s (inf s) :=
  ⟨fun x => cInf_le H, fun x => le_cInf Ne⟩

theorem is_glb_cinfi [Nonempty ι] {f : ι → α} (H : BddBelow (Range f)) : IsGlb (Range f) (⨅ i, f i) :=
  is_glb_cInf (range_nonempty f) H

theorem is_glb_cinfi_set {f : β → α} {s : Set β} (H : BddBelow (f '' s)) (Hne : s.Nonempty) :
    IsGlb (f '' s) (⨅ i : s, f i) :=
  @is_lub_csupr_set αᵒᵈ _ _ _ _ H Hne

theorem csupr_le_iff [Nonempty ι] {f : ι → α} {a : α} (hf : BddAbove (Range f)) : supr f ≤ a ↔ ∀ i, f i ≤ a :=
  (is_lub_le_iff <| is_lub_csupr hf).trans forall_range_iff

theorem le_cinfi_iff [Nonempty ι] {f : ι → α} {a : α} (hf : BddBelow (Range f)) : a ≤ infi f ↔ ∀ i, a ≤ f i :=
  (le_is_glb_iff <| is_glb_cinfi hf).trans forall_range_iff

theorem csupr_set_le_iff {ι : Type _} {s : Set ι} {f : ι → α} {a : α} (hs : s.Nonempty) (hf : BddAbove (f '' s)) :
    (⨆ i : s, f i) ≤ a ↔ ∀, ∀ i ∈ s, ∀, f i ≤ a :=
  (is_lub_le_iff <| is_lub_csupr_set hf hs).trans ball_image_iff

theorem le_cinfi_set_iff {ι : Type _} {s : Set ι} {f : ι → α} {a : α} (hs : s.Nonempty) (hf : BddBelow (f '' s)) :
    (a ≤ ⨅ i : s, f i) ↔ ∀, ∀ i ∈ s, ∀, a ≤ f i :=
  (le_is_glb_iff <| is_glb_cinfi_set hf hs).trans ball_image_iff

theorem IsLub.cSup_eq (H : IsLub s a) (ne : s.Nonempty) : sup s = a :=
  (is_lub_cSup Ne ⟨a, H.1⟩).unique H

theorem IsLub.csupr_eq [Nonempty ι] {f : ι → α} (H : IsLub (Range f) a) : (⨆ i, f i) = a :=
  H.cSup_eq (range_nonempty f)

theorem IsLub.csupr_set_eq {s : Set β} {f : β → α} (H : IsLub (f '' s) a) (Hne : s.Nonempty) : (⨆ i : s, f i) = a :=
  IsLub.cSup_eq (image_eq_range f s ▸ H) (image_eq_range f s ▸ Hne.Image f)

/-- A greatest element of a set is the supremum of this set. -/
theorem IsGreatest.cSup_eq (H : IsGreatest s a) : sup s = a :=
  H.IsLub.cSup_eq H.Nonempty

theorem IsGreatest.Sup_mem (H : IsGreatest s a) : sup s ∈ s :=
  H.cSup_eq.symm ▸ H.1

theorem IsGlb.cInf_eq (H : IsGlb s a) (ne : s.Nonempty) : inf s = a :=
  (is_glb_cInf Ne ⟨a, H.1⟩).unique H

theorem IsGlb.cinfi_eq [Nonempty ι] {f : ι → α} (H : IsGlb (Range f) a) : (⨅ i, f i) = a :=
  H.cInf_eq (range_nonempty f)

theorem IsGlb.cinfi_set_eq {s : Set β} {f : β → α} (H : IsGlb (f '' s) a) (Hne : s.Nonempty) : (⨅ i : s, f i) = a :=
  IsGlb.cInf_eq (image_eq_range f s ▸ H) (image_eq_range f s ▸ Hne.Image f)

/-- A least element of a set is the infimum of this set. -/
theorem IsLeast.cInf_eq (H : IsLeast s a) : inf s = a :=
  H.IsGlb.cInf_eq H.Nonempty

theorem IsLeast.Inf_mem (H : IsLeast s a) : inf s ∈ s :=
  H.cInf_eq.symm ▸ H.1

theorem subset_Icc_cInf_cSup (hb : BddBelow s) (ha : BddAbove s) : s ⊆ Icc (inf s) (sup s) := fun x hx =>
  ⟨cInf_le hb hx, le_cSup ha hx⟩

theorem cSup_le_iff (hb : BddAbove s) (hs : s.Nonempty) : sup s ≤ a ↔ ∀, ∀ b ∈ s, ∀, b ≤ a :=
  is_lub_le_iff (is_lub_cSup hs hb)

theorem le_cInf_iff (hb : BddBelow s) (hs : s.Nonempty) : a ≤ inf s ↔ ∀, ∀ b ∈ s, ∀, a ≤ b :=
  le_is_glb_iff (is_glb_cInf hs hb)

theorem cSup_lower_bounds_eq_cInf {s : Set α} (h : BddBelow s) (hs : s.Nonempty) : sup (LowerBounds s) = inf s :=
  (is_lub_cSup h <| hs.mono fun x hx y hy => hy hx).unique (is_glb_cInf hs h).IsLub

theorem cInf_upper_bounds_eq_cSup {s : Set α} (h : BddAbove s) (hs : s.Nonempty) : inf (UpperBounds s) = sup s :=
  (is_glb_cInf h <| hs.mono fun x hx y hy => hy hx).unique (is_lub_cSup hs h).IsGlb

theorem not_mem_of_lt_cInf {x : α} {s : Set α} (h : x < inf s) (hs : BddBelow s) : x ∉ s := fun hx =>
  lt_irreflₓ _ (h.trans_le (cInf_le hs hx))

theorem not_mem_of_cSup_lt {x : α} {s : Set α} (h : sup s < x) (hs : BddAbove s) : x ∉ s :=
  @not_mem_of_lt_cInf αᵒᵈ _ x s h hs

/-- Introduction rule to prove that `b` is the supremum of `s`: it suffices to check that `b`
is larger than all elements of `s`, and that this is not the case of any `w<b`.
See `Sup_eq_of_forall_le_of_forall_lt_exists_gt` for a version in complete lattices. -/
theorem cSup_eq_of_forall_le_of_forall_lt_exists_gt (hs : s.Nonempty) (H : ∀, ∀ a ∈ s, ∀, a ≤ b)
    (H' : ∀ w, w < b → ∃ a ∈ s, w < a) : sup s = b :=
  (eq_of_le_of_not_lt (cSup_le hs H)) fun hb =>
    let ⟨a, ha, ha'⟩ := H' _ hb
    lt_irreflₓ _ <| ha'.trans_le <| le_cSup ⟨b, H⟩ ha

/-- Introduction rule to prove that `b` is the infimum of `s`: it suffices to check that `b`
is smaller than all elements of `s`, and that this is not the case of any `w>b`.
See `Inf_eq_of_forall_ge_of_forall_gt_exists_lt` for a version in complete lattices. -/
theorem cInf_eq_of_forall_ge_of_forall_gt_exists_lt :
    s.Nonempty → (∀, ∀ a ∈ s, ∀, b ≤ a) → (∀ w, b < w → ∃ a ∈ s, a < w) → inf s = b :=
  @cSup_eq_of_forall_le_of_forall_lt_exists_gt αᵒᵈ _ _ _

/-- b < Sup s when there is an element a in s with b < a, when s is bounded above.
This is essentially an iff, except that the assumptions for the two implications are
slightly different (one needs boundedness above for one direction, nonemptiness and linear
order for the other one), so we formulate separately the two implications, contrary to
the complete_lattice case.-/
theorem lt_cSup_of_lt (hs : BddAbove s) (ha : a ∈ s) (h : b < a) : b < sup s :=
  lt_of_lt_of_leₓ h (le_cSup hs ha)

/-- Inf s < b when there is an element a in s with a < b, when s is bounded below.
This is essentially an iff, except that the assumptions for the two implications are
slightly different (one needs boundedness below for one direction, nonemptiness and linear
order for the other one), so we formulate separately the two implications, contrary to
the complete_lattice case.-/
theorem cInf_lt_of_lt : BddBelow s → a ∈ s → a < b → inf s < b :=
  @lt_cSup_of_lt αᵒᵈ _ _ _ _

/-- If all elements of a nonempty set `s` are less than or equal to all elements
of a nonempty set `t`, then there exists an element between these sets. -/
theorem exists_between_of_forall_le (sne : s.Nonempty) (tne : t.Nonempty) (hst : ∀, ∀ x ∈ s, ∀, ∀ y ∈ t, ∀, x ≤ y) :
    (UpperBounds s ∩ LowerBounds t).Nonempty :=
  ⟨inf t, fun x hx => le_cInf tne <| hst x hx, fun y hy => cInf_le (sne.mono hst) hy⟩

/-- The supremum of a singleton is the element of the singleton-/
@[simp]
theorem cSup_singleton (a : α) : sup {a} = a :=
  is_greatest_singleton.cSup_eq

/-- The infimum of a singleton is the element of the singleton-/
@[simp]
theorem cInf_singleton (a : α) : inf {a} = a :=
  is_least_singleton.cInf_eq

@[simp]
theorem cSup_pair (a b : α) : sup {a, b} = a⊔b :=
  (@is_lub_pair _ _ a b).cSup_eq (insert_nonempty _ _)

@[simp]
theorem cInf_pair (a b : α) : inf {a, b} = a⊓b :=
  (@is_glb_pair _ _ a b).cInf_eq (insert_nonempty _ _)

/-- If a set is bounded below and above, and nonempty, its infimum is less than or equal to
its supremum.-/
theorem cInf_le_cSup (hb : BddBelow s) (ha : BddAbove s) (ne : s.Nonempty) : inf s ≤ sup s :=
  is_glb_le_is_lub (is_glb_cInf Ne hb) (is_lub_cSup Ne ha) Ne

/-- The sup of a union of two sets is the max of the suprema of each subset, under the assumptions
that all sets are bounded above and nonempty.-/
theorem cSup_union (hs : BddAbove s) (sne : s.Nonempty) (ht : BddAbove t) (tne : t.Nonempty) :
    sup (s ∪ t) = sup s⊔sup t :=
  ((is_lub_cSup sne hs).union (is_lub_cSup tne ht)).cSup_eq sne.inl

/-- The inf of a union of two sets is the min of the infima of each subset, under the assumptions
that all sets are bounded below and nonempty.-/
theorem cInf_union (hs : BddBelow s) (sne : s.Nonempty) (ht : BddBelow t) (tne : t.Nonempty) :
    inf (s ∪ t) = inf s⊓inf t :=
  @cSup_union αᵒᵈ _ _ _ hs sne ht tne

/-- The supremum of an intersection of two sets is bounded by the minimum of the suprema of each
set, if all sets are bounded above and nonempty.-/
theorem cSup_inter_le (hs : BddAbove s) (ht : BddAbove t) (hst : (s ∩ t).Nonempty) : sup (s ∩ t) ≤ sup s⊓sup t :=
  (cSup_le hst) fun x hx => le_inf (le_cSup hs hx.1) (le_cSup ht hx.2)

/-- The infimum of an intersection of two sets is bounded below by the maximum of the
infima of each set, if all sets are bounded below and nonempty.-/
theorem le_cInf_inter : BddBelow s → BddBelow t → (s ∩ t).Nonempty → inf s⊔inf t ≤ inf (s ∩ t) :=
  @cSup_inter_le αᵒᵈ _ _ _

/-- The supremum of insert a s is the maximum of a and the supremum of s, if s is
nonempty and bounded above.-/
theorem cSup_insert (hs : BddAbove s) (sne : s.Nonempty) : sup (insert a s) = a⊔sup s :=
  ((is_lub_cSup sne hs).insert a).cSup_eq (insert_nonempty a s)

/-- The infimum of insert a s is the minimum of a and the infimum of s, if s is
nonempty and bounded below.-/
theorem cInf_insert (hs : BddBelow s) (sne : s.Nonempty) : inf (insert a s) = a⊓inf s :=
  @cSup_insert αᵒᵈ _ _ _ hs sne

@[simp]
theorem cInf_Icc (h : a ≤ b) : inf (Icc a b) = a :=
  (is_glb_Icc h).cInf_eq (nonempty_Icc.2 h)

@[simp]
theorem cInf_Ici : inf (Ici a) = a :=
  is_least_Ici.cInf_eq

@[simp]
theorem cInf_Ico (h : a < b) : inf (Ico a b) = a :=
  (is_glb_Ico h).cInf_eq (nonempty_Ico.2 h)

@[simp]
theorem cInf_Ioc [DenselyOrdered α] (h : a < b) : inf (Ioc a b) = a :=
  (is_glb_Ioc h).cInf_eq (nonempty_Ioc.2 h)

@[simp]
theorem cInf_Ioi [NoMaxOrder α] [DenselyOrdered α] : inf (Ioi a) = a :=
  cInf_eq_of_forall_ge_of_forall_gt_exists_lt nonempty_Ioi (fun _ => le_of_ltₓ) fun w hw => by
    simpa using exists_between hw

@[simp]
theorem cInf_Ioo [DenselyOrdered α] (h : a < b) : inf (Ioo a b) = a :=
  (is_glb_Ioo h).cInf_eq (nonempty_Ioo.2 h)

@[simp]
theorem cSup_Icc (h : a ≤ b) : sup (Icc a b) = b :=
  (is_lub_Icc h).cSup_eq (nonempty_Icc.2 h)

@[simp]
theorem cSup_Ico [DenselyOrdered α] (h : a < b) : sup (Ico a b) = b :=
  (is_lub_Ico h).cSup_eq (nonempty_Ico.2 h)

@[simp]
theorem cSup_Iic : sup (Iic a) = a :=
  is_greatest_Iic.cSup_eq

@[simp]
theorem cSup_Iio [NoMinOrder α] [DenselyOrdered α] : sup (Iio a) = a :=
  cSup_eq_of_forall_le_of_forall_lt_exists_gt nonempty_Iio (fun _ => le_of_ltₓ) fun w hw => by
    simpa [← and_comm] using exists_between hw

@[simp]
theorem cSup_Ioc (h : a < b) : sup (Ioc a b) = b :=
  (is_lub_Ioc h).cSup_eq (nonempty_Ioc.2 h)

@[simp]
theorem cSup_Ioo [DenselyOrdered α] (h : a < b) : sup (Ioo a b) = b :=
  (is_lub_Ioo h).cSup_eq (nonempty_Ioo.2 h)

/-- The indexed supremum of a function is bounded above by a uniform bound-/
theorem csupr_le [Nonempty ι] {f : ι → α} {c : α} (H : ∀ x, f x ≤ c) : supr f ≤ c :=
  cSup_le (range_nonempty f)
    (by
      rwa [forall_range_iff])

/-- The indexed supremum of a function is bounded below by the value taken at one point-/
theorem le_csupr {f : ι → α} (H : BddAbove (Range f)) (c : ι) : f c ≤ supr f :=
  le_cSup H (mem_range_self _)

theorem le_csupr_of_le {f : ι → α} (H : BddAbove (Range f)) (c : ι) (h : a ≤ f c) : a ≤ supr f :=
  le_transₓ h (le_csupr H c)

/-- The indexed supremum of two functions are comparable if the functions are pointwise comparable-/
theorem csupr_mono {f g : ι → α} (B : BddAbove (Range g)) (H : ∀ x, f x ≤ g x) : supr f ≤ supr g := by
  cases is_empty_or_nonempty ι
  · rw [supr_of_empty', supr_of_empty']
    
  · exact csupr_le fun x => le_csupr_of_le B x (H x)
    

theorem le_csupr_set {f : β → α} {s : Set β} (H : BddAbove (f '' s)) {c : β} (hc : c ∈ s) : f c ≤ ⨆ i : s, f i :=
  (le_cSup H <| mem_image_of_mem f hc).trans_eq Sup_image'

/-- The indexed infimum of two functions are comparable if the functions are pointwise comparable-/
theorem cinfi_mono {f g : ι → α} (B : BddBelow (Range f)) (H : ∀ x, f x ≤ g x) : infi f ≤ infi g :=
  @csupr_mono αᵒᵈ _ _ _ _ B H

/-- The indexed minimum of a function is bounded below by a uniform lower bound-/
theorem le_cinfi [Nonempty ι] {f : ι → α} {c : α} (H : ∀ x, c ≤ f x) : c ≤ infi f :=
  @csupr_le αᵒᵈ _ _ _ _ _ H

/-- The indexed infimum of a function is bounded above by the value taken at one point-/
theorem cinfi_le {f : ι → α} (H : BddBelow (Range f)) (c : ι) : infi f ≤ f c :=
  @le_csupr αᵒᵈ _ _ _ H c

theorem cinfi_le_of_le {f : ι → α} (H : BddBelow (Range f)) (c : ι) (h : f c ≤ a) : infi f ≤ a :=
  @le_csupr_of_le αᵒᵈ _ _ _ _ H c h

theorem cinfi_set_le {f : β → α} {s : Set β} (H : BddBelow (f '' s)) {c : β} (hc : c ∈ s) : (⨅ i : s, f i) ≤ f c :=
  @le_csupr_set αᵒᵈ _ _ _ _ H _ hc

@[simp]
theorem csupr_const [hι : Nonempty ι] {a : α} : (⨆ b : ι, a) = a := by
  rw [supr, range_const, cSup_singleton]

@[simp]
theorem cinfi_const [hι : Nonempty ι] {a : α} : (⨅ b : ι, a) = a :=
  @csupr_const αᵒᵈ _ _ _ _

@[simp]
theorem supr_unique [Unique ι] {s : ι → α} : (⨆ i, s i) = s default := by
  have : ∀ i, s i = s default := fun i => congr_arg s (Unique.eq_default i)
  simp only [← this, ← csupr_const]

@[simp]
theorem infi_unique [Unique ι] {s : ι → α} : (⨅ i, s i) = s default :=
  @supr_unique αᵒᵈ _ _ _ _

@[simp]
theorem csupr_pos {p : Prop} {f : p → α} (hp : p) : (⨆ h : p, f h) = f hp :=
  have := uniqueProp hp
  supr_unique

@[simp]
theorem cinfi_pos {p : Prop} {f : p → α} (hp : p) : (⨅ h : p, f h) = f hp :=
  @csupr_pos αᵒᵈ _ _ _ hp

theorem csupr_set {s : Set β} {f : β → α} : (⨆ x : s, f x) = sup (f '' s) := by
  rw [supr]
  congr
  ext
  rw [mem_image, mem_range, SetCoe.exists]
  simp_rw [Subtype.coe_mk, exists_prop]

theorem cinfi_set {s : Set β} {f : β → α} : (⨅ x : s, f x) = inf (f '' s) :=
  @csupr_set αᵒᵈ _ _ _ _

/-- Introduction rule to prove that `b` is the supremum of `f`: it suffices to check that `b`
is larger than `f i` for all `i`, and that this is not the case of any `w<b`.
See `supr_eq_of_forall_le_of_forall_lt_exists_gt` for a version in complete lattices. -/
theorem csupr_eq_of_forall_le_of_forall_lt_exists_gt [Nonempty ι] {f : ι → α} (h₁ : ∀ i, f i ≤ b)
    (h₂ : ∀ w, w < b → ∃ i, w < f i) : (⨆ i : ι, f i) = b :=
  cSup_eq_of_forall_le_of_forall_lt_exists_gt (range_nonempty f) (forall_range_iff.mpr h₁) fun w hw =>
    exists_range_iff.mpr <| h₂ w hw

/-- Introduction rule to prove that `b` is the infimum of `f`: it suffices to check that `b`
is smaller than `f i` for all `i`, and that this is not the case of any `w>b`.
See `infi_eq_of_forall_ge_of_forall_gt_exists_lt` for a version in complete lattices. -/
theorem cinfi_eq_of_forall_ge_of_forall_gt_exists_lt [Nonempty ι] {f : ι → α} (h₁ : ∀ i, b ≤ f i)
    (h₂ : ∀ w, b < w → ∃ i, f i < w) : (⨅ i : ι, f i) = b :=
  @csupr_eq_of_forall_le_of_forall_lt_exists_gt αᵒᵈ _ _ _ _ ‹_› ‹_› ‹_›

/-- Nested intervals lemma: if `f` is a monotone sequence, `g` is an antitone sequence, and
`f n ≤ g n` for all `n`, then `⨆ n, f n` belongs to all the intervals `[f n, g n]`. -/
theorem Monotone.csupr_mem_Inter_Icc_of_antitone [SemilatticeSup β] {f g : β → α} (hf : Monotone f) (hg : Antitone g)
    (h : f ≤ g) : (⨆ n, f n) ∈ ⋂ n, Icc (f n) (g n) := by
  refine' mem_Inter.2 fun n => _
  have : Nonempty β := ⟨n⟩
  have : ∀ m, f m ≤ g n := fun m => hf.forall_le_of_antitone hg h m n
  exact ⟨le_csupr ⟨g <| n, forall_range_iff.2 this⟩ _, csupr_le this⟩

/-- Nested intervals lemma: if `[f n, g n]` is an antitone sequence of nonempty
closed intervals, then `⨆ n, f n` belongs to all the intervals `[f n, g n]`. -/
theorem csupr_mem_Inter_Icc_of_antitone_Icc [SemilatticeSup β] {f g : β → α} (h : Antitone fun n => Icc (f n) (g n))
    (h' : ∀ n, f n ≤ g n) : (⨆ n, f n) ∈ ⋂ n, Icc (f n) (g n) :=
  Monotone.csupr_mem_Inter_Icc_of_antitone (fun m n hmn => ((Icc_subset_Icc_iff (h' n)).1 (h hmn)).1)
    (fun m n hmn => ((Icc_subset_Icc_iff (h' n)).1 (h hmn)).2) h'

theorem Finset.Nonempty.sup'_eq_cSup_image {s : Finset β} (hs : s.Nonempty) (f : β → α) : s.sup' hs f = sup (f '' s) :=
  eq_of_forall_ge_iff fun a => by
    simp [← cSup_le_iff (s.finite_to_set.image f).BddAbove (hs.to_set.image f)]

theorem Finset.Nonempty.sup'_id_eq_cSup {s : Finset α} (hs : s.Nonempty) : s.sup' hs id = sup s := by
  rw [hs.sup'_eq_cSup_image, image_id]

/-- Introduction rule to prove that b is the supremum of s: it suffices to check that
1) b is an upper bound
2) every other upper bound b' satisfies b ≤ b'.-/
theorem cSup_eq_of_is_forall_le_of_forall_le_imp_ge (hs : s.Nonempty) (h_is_ub : ∀, ∀ a ∈ s, ∀, a ≤ b)
    (h_b_le_ub : ∀ ub, (∀, ∀ a ∈ s, ∀, a ≤ ub) → b ≤ ub) : sup s = b :=
  (cSup_le hs h_is_ub).antisymm ((h_b_le_ub _) fun a => le_cSup ⟨b, h_is_ub⟩)

end ConditionallyCompleteLattice

instance Pi.conditionallyCompleteLattice {ι : Type _} {α : ∀ i : ι, Type _} [∀ i, ConditionallyCompleteLattice (α i)] :
    ConditionallyCompleteLattice (∀ i, α i) :=
  { Pi.lattice, Pi.hasSupₓ, Pi.hasInfₓ with
    le_cSup := fun s f ⟨g, hg⟩ hf i => le_cSup ⟨g i, Set.forall_range_iff.2 fun ⟨f', hf'⟩ => hg hf' i⟩ ⟨⟨f, hf⟩, rfl⟩,
    cSup_le := fun s f hs hf i =>
      (cSup_le
          (by
            have := hs.to_subtype <;> apply range_nonempty))
        fun b ⟨⟨g, hg⟩, hb⟩ => hb ▸ hf hg i,
    cInf_le := fun s f ⟨g, hg⟩ hf i => cInf_le ⟨g i, Set.forall_range_iff.2 fun ⟨f', hf'⟩ => hg hf' i⟩ ⟨⟨f, hf⟩, rfl⟩,
    le_cInf := fun s f hs hf i =>
      (le_cInf
          (by
            have := hs.to_subtype <;> apply range_nonempty))
        fun b ⟨⟨g, hg⟩, hb⟩ => hb ▸ hf hg i }

section ConditionallyCompleteLinearOrder

variable [ConditionallyCompleteLinearOrder α] {s t : Set α} {a b : α}

theorem Finset.Nonempty.cSup_eq_max' {s : Finset α} (h : s.Nonempty) : sup ↑s = s.max' h :=
  eq_of_forall_ge_iff fun a => (cSup_le_iff s.BddAbove h.to_set).trans (s.max'_le_iff h).symm

theorem Finset.Nonempty.cInf_eq_min' {s : Finset α} (h : s.Nonempty) : inf ↑s = s.min' h :=
  @Finset.Nonempty.cSup_eq_max' αᵒᵈ _ s h

theorem Finset.Nonempty.cSup_mem {s : Finset α} (h : s.Nonempty) : sup (s : Set α) ∈ s := by
  rw [h.cSup_eq_max']
  exact s.max'_mem _

theorem Finset.Nonempty.cInf_mem {s : Finset α} (h : s.Nonempty) : inf (s : Set α) ∈ s :=
  @Finset.Nonempty.cSup_mem αᵒᵈ _ _ h

theorem Set.Nonempty.cSup_mem (h : s.Nonempty) (hs : s.Finite) : sup s ∈ s := by
  lift s to Finset α using hs
  exact Finset.Nonempty.cSup_mem h

theorem Set.Nonempty.cInf_mem (h : s.Nonempty) (hs : s.Finite) : inf s ∈ s :=
  @Set.Nonempty.cSup_mem αᵒᵈ _ _ h hs

theorem Set.Finite.cSup_lt_iff (hs : s.Finite) (h : s.Nonempty) : sup s < a ↔ ∀, ∀ x ∈ s, ∀, x < a :=
  ⟨fun h x hx => (le_cSup hs.BddAbove hx).trans_lt h, fun H => H _ <| h.cSup_mem hs⟩

theorem Set.Finite.lt_cInf_iff (hs : s.Finite) (h : s.Nonempty) : a < inf s ↔ ∀, ∀ x ∈ s, ∀, a < x :=
  @Set.Finite.cSup_lt_iff αᵒᵈ _ _ _ hs h

/-- When b < Sup s, there is an element a in s with b < a, if s is nonempty and the order is
a linear order. -/
theorem exists_lt_of_lt_cSup (hs : s.Nonempty) (hb : b < sup s) : ∃ a ∈ s, b < a := by
  contrapose! hb
  exact cSup_le hs hb

/-- Indexed version of the above lemma `exists_lt_of_lt_cSup`.
When `b < supr f`, there is an element `i` such that `b < f i`.
-/
theorem exists_lt_of_lt_csupr [Nonempty ι] {f : ι → α} (h : b < supr f) : ∃ i, b < f i :=
  let ⟨_, ⟨i, rfl⟩, h⟩ := exists_lt_of_lt_cSup (range_nonempty f) h
  ⟨i, h⟩

/-- When Inf s < b, there is an element a in s with a < b, if s is nonempty and the order is
a linear order.-/
theorem exists_lt_of_cInf_lt (hs : s.Nonempty) (hb : inf s < b) : ∃ a ∈ s, a < b :=
  @exists_lt_of_lt_cSup αᵒᵈ _ _ _ hs hb

/-- Indexed version of the above lemma `exists_lt_of_cInf_lt`
When `infi f < a`, there is an element `i` such that `f i < a`.
-/
theorem exists_lt_of_cinfi_lt [Nonempty ι] {f : ι → α} (h : infi f < a) : ∃ i, f i < a :=
  @exists_lt_of_lt_csupr αᵒᵈ _ _ _ _ _ h

open Function

variable [IsWellOrder α (· < ·)]

theorem Inf_eq_argmin_on (hs : s.Nonempty) : inf s = argminOn id (@IsWellOrder.wf α (· < ·) _) s hs :=
  IsLeast.cInf_eq ⟨argmin_on_mem _ _ _ _, fun a ha => argmin_on_le id _ _ ha⟩

theorem is_least_Inf (hs : s.Nonempty) : IsLeast s (inf s) := by
  rw [Inf_eq_argmin_on hs]
  exact ⟨argmin_on_mem _ _ _ _, fun a ha => argmin_on_le id _ _ ha⟩

theorem le_cInf_iff' (hs : s.Nonempty) : b ≤ inf s ↔ b ∈ LowerBounds s :=
  le_is_glb_iff (is_least_Inf hs).IsGlb

theorem Inf_mem (hs : s.Nonempty) : inf s ∈ s :=
  (is_least_Inf hs).1

theorem MonotoneOn.map_Inf {β : Type _} [ConditionallyCompleteLattice β] {f : α → β} (hf : MonotoneOn f s)
    (hs : s.Nonempty) : f (inf s) = inf (f '' s) :=
  (hf.map_is_least (is_least_Inf hs)).cInf_eq.symm

theorem Monotone.map_Inf {β : Type _} [ConditionallyCompleteLattice β] {f : α → β} (hf : Monotone f) (hs : s.Nonempty) :
    f (inf s) = inf (f '' s) :=
  (hf.map_is_least (is_least_Inf hs)).cInf_eq.symm

end ConditionallyCompleteLinearOrder

/-!
### Lemmas about a conditionally complete linear order with bottom element

In this case we have `Sup ∅ = ⊥`, so we can drop some `nonempty`/`set.nonempty` assumptions.
-/


section ConditionallyCompleteLinearOrderBot

variable [ConditionallyCompleteLinearOrderBot α]

@[simp]
theorem cSup_empty : (sup ∅ : α) = ⊥ :=
  ConditionallyCompleteLinearOrderBot.cSup_empty

@[simp]
theorem csupr_of_empty [IsEmpty ι] (f : ι → α) : (⨆ i, f i) = ⊥ := by
  rw [supr_of_empty', cSup_empty]

@[simp]
theorem csupr_false (f : False → α) : (⨆ i, f i) = ⊥ :=
  csupr_of_empty f

@[simp]
theorem cInf_univ : inf (Univ : Set α) = ⊥ :=
  is_least_univ.cInf_eq

theorem is_lub_cSup' {s : Set α} (hs : BddAbove s) : IsLub s (sup s) := by
  rcases eq_empty_or_nonempty s with (rfl | hne)
  · simp only [← cSup_empty, ← is_lub_empty]
    
  · exact is_lub_cSup hne hs
    

theorem cSup_le_iff' {s : Set α} (hs : BddAbove s) {a : α} : sup s ≤ a ↔ ∀, ∀ x ∈ s, ∀, x ≤ a :=
  is_lub_le_iff (is_lub_cSup' hs)

theorem cSup_le' {s : Set α} {a : α} (h : a ∈ UpperBounds s) : sup s ≤ a :=
  (cSup_le_iff' ⟨a, h⟩).2 h

theorem le_cSup_iff' {s : Set α} {a : α} (h : BddAbove s) : a ≤ sup s ↔ ∀ b, b ∈ UpperBounds s → a ≤ b :=
  ⟨fun h b hb => le_transₓ h (cSup_le' hb), fun hb => hb _ fun x => le_cSup h⟩

theorem le_csupr_iff' {s : ι → α} {a : α} (h : BddAbove (Range s)) : a ≤ supr s ↔ ∀ b, (∀ i, s i ≤ b) → a ≤ b := by
  simp [← supr, ← h, ← le_cSup_iff', ← UpperBounds]

theorem le_cInf_iff'' {s : Set α} {a : α} (ne : s.Nonempty) : a ≤ inf s ↔ ∀ b : α, b ∈ s → a ≤ b :=
  le_cInf_iff ⟨⊥, fun a _ => bot_le⟩ Ne

theorem cInf_le' {s : Set α} {a : α} (h : a ∈ s) : inf s ≤ a :=
  cInf_le ⟨⊥, fun a _ => bot_le⟩ h

theorem exists_lt_of_lt_cSup' {s : Set α} {a : α} (h : a < sup s) : ∃ b ∈ s, a < b := by
  contrapose! h
  exact cSup_le' h

theorem csupr_le_iff' {f : ι → α} (h : BddAbove (Range f)) {a : α} : (⨆ i, f i) ≤ a ↔ ∀ i, f i ≤ a :=
  (cSup_le_iff' h).trans forall_range_iff

theorem csupr_le' {f : ι → α} {a : α} (h : ∀ i, f i ≤ a) : (⨆ i, f i) ≤ a :=
  cSup_le' <| forall_range_iff.2 h

theorem exists_lt_of_lt_csupr' {f : ι → α} {a : α} (h : a < ⨆ i, f i) : ∃ i, a < f i := by
  contrapose! h
  exact csupr_le' h

theorem csupr_mono' {ι'} {f : ι → α} {g : ι' → α} (hg : BddAbove (Range g)) (h : ∀ i, ∃ i', f i ≤ g i') :
    supr f ≤ supr g :=
  csupr_le' fun i => Exists.elim (h i) (le_csupr_of_le hg)

theorem cInf_le_cInf' {s t : Set α} (h₁ : t.Nonempty) (h₂ : t ⊆ s) : inf s ≤ inf t :=
  cInf_le_cInf (OrderBot.bdd_below s) h₁ h₂

end ConditionallyCompleteLinearOrderBot

namespace WithTop

open Classical

variable [ConditionallyCompleteLinearOrderBot α]

/-- The Sup of a non-empty set is its least upper bound for a conditionally
complete lattice with a top. -/
theorem is_lub_Sup' {β : Type _} [ConditionallyCompleteLattice β] {s : Set (WithTop β)} (hs : s.Nonempty) :
    IsLub s (sup s) := by
  constructor
  · show ite _ _ _ ∈ _
    split_ifs
    · intro _ _
      exact le_top
      
    · rintro (⟨⟩ | a) ha
      · contradiction
        
      apply some_le_some.2
      exact le_cSup h_1 ha
      
    · intro _ _
      exact le_top
      
    
  · show ite _ _ _ ∈ _
    split_ifs
    · rintro (⟨⟩ | a) ha
      · exact le_rfl
        
      · exact False.elim (not_top_le_coe a (ha h))
        
      
    · rintro (⟨⟩ | b) hb
      · exact le_top
        
      refine' some_le_some.2 (cSup_le _ _)
      · rcases hs with ⟨⟨⟩ | b, hb⟩
        · exact absurd hb h
          
        · exact ⟨b, hb⟩
          
        
      · intro a ha
        exact some_le_some.1 (hb ha)
        
      
    · rintro (⟨⟩ | b) hb
      · exact le_rfl
        
      · exfalso
        apply h_1
        use b
        intro a ha
        exact some_le_some.1 (hb ha)
        
      
    

theorem is_lub_Sup (s : Set (WithTop α)) : IsLub s (sup s) := by
  cases' s.eq_empty_or_nonempty with hs hs
  · rw [hs]
    show IsLub ∅ (ite _ _ _)
    split_ifs
    · cases h
      
    · rw [preimage_empty, cSup_empty]
      exact is_lub_empty
      
    · exfalso
      apply h_1
      use ⊥
      rintro a ⟨⟩
      
    
  exact is_lub_Sup' hs

/-- The Inf of a bounded-below set is its greatest lower bound for a conditionally
complete lattice with a top. -/
theorem is_glb_Inf' {β : Type _} [ConditionallyCompleteLattice β] {s : Set (WithTop β)} (hs : BddBelow s) :
    IsGlb s (inf s) := by
  constructor
  · show ite _ _ _ ∈ _
    split_ifs
    · intro a ha
      exact top_le_iff.2 (Set.mem_singleton_iff.1 (h ha))
      
    · rintro (⟨⟩ | a) ha
      · exact le_top
        
      refine' some_le_some.2 (cInf_le _ ha)
      rcases hs with ⟨⟨⟩ | b, hb⟩
      · exfalso
        apply h
        intro c hc
        rw [mem_singleton_iff, ← top_le_iff]
        exact hb hc
        
      use b
      intro c hc
      exact some_le_some.1 (hb hc)
      
    
  · show ite _ _ _ ∈ _
    split_ifs
    · intro _ _
      exact le_top
      
    · rintro (⟨⟩ | a) ha
      · exfalso
        apply h
        intro b hb
        exact Set.mem_singleton_iff.2 (top_le_iff.1 (ha hb))
        
      · refine' some_le_some.2 (le_cInf _ _)
        · classical
          contrapose! h
          rintro (⟨⟩ | a) ha
          · exact mem_singleton ⊤
            
          · exact (h ⟨a, ha⟩).elim
            
          
        · intro b hb
          rw [← some_le_some]
          exact ha hb
          
        
      
    

theorem is_glb_Inf (s : Set (WithTop α)) : IsGlb s (inf s) := by
  by_cases' hs : BddBelow s
  · exact is_glb_Inf' hs
    
  · exfalso
    apply hs
    use ⊥
    intro _ _
    exact bot_le
    

noncomputable instance : CompleteLinearOrder (WithTop α) :=
  { WithTop.linearOrder, WithTop.lattice, WithTop.orderTop, WithTop.orderBot with sup := sup,
    le_Sup := fun s => (is_lub_Sup s).1, Sup_le := fun s => (is_lub_Sup s).2, inf := inf,
    le_Inf := fun s => (is_glb_Inf s).2, Inf_le := fun s => (is_glb_Inf s).1 }

theorem coe_Sup {s : Set α} (hb : BddAbove s) : (↑(sup s) : WithTop α) = ⨆ a ∈ s, ↑a := by
  cases' s.eq_empty_or_nonempty with hs hs
  · rw [hs, cSup_empty]
    simp only [← Set.mem_empty_eq, ← supr_bot, ← supr_false]
    rfl
    
  apply le_antisymmₓ
  · refine' coe_le_iff.2 fun b hb => (cSup_le hs) fun a has => coe_le_coe.1 <| hb ▸ _
    exact le_supr₂_of_le a has le_rfl
    
  · exact supr₂_le fun a ha => coe_le_coe.2 <| le_cSup hb ha
    

theorem coe_Inf {s : Set α} (hs : s.Nonempty) : (↑(inf s) : WithTop α) = ⨅ a ∈ s, ↑a := by
  obtain ⟨x, hx⟩ := hs
  have : (⨅ a ∈ s, ↑a : WithTop α) ≤ x := infi₂_le_of_le x hx le_rfl
  rcases le_coe_iff.1 this with ⟨r, r_eq, hr⟩
  refine' le_antisymmₓ (le_infi₂ fun a ha => coe_le_coe.2 <| cInf_le (OrderBot.bdd_below s) ha) _
  · rw [r_eq]
    apply coe_le_coe.2 (le_cInf ⟨x, hx⟩ fun a has => coe_le_coe.1 _)
    rw [← r_eq]
    exact infi₂_le_of_le a has le_rfl
    

end WithTop

namespace Monotone

variable [Preorderₓ α] [ConditionallyCompleteLattice β] {f : α → β} (h_mono : Monotone f)

/-! A monotone function into a conditionally complete lattice preserves the ordering properties of
`Sup` and `Inf`. -/


theorem le_cSup_image {s : Set α} {c : α} (hcs : c ∈ s) (h_bdd : BddAbove s) : f c ≤ sup (f '' s) :=
  le_cSup (map_bdd_above h_mono h_bdd) (mem_image_of_mem f hcs)

theorem cSup_image_le {s : Set α} (hs : s.Nonempty) {B : α} (hB : B ∈ UpperBounds s) : sup (f '' s) ≤ f B :=
  cSup_le (Nonempty.image f hs) (h_mono.mem_upper_bounds_image hB)

theorem cInf_image_le {s : Set α} {c : α} (hcs : c ∈ s) (h_bdd : BddBelow s) : inf (f '' s) ≤ f c :=
  @le_cSup_image αᵒᵈ βᵒᵈ _ _ _ (fun x y hxy => h_mono hxy) _ _ hcs h_bdd

theorem le_cInf_image {s : Set α} (hs : s.Nonempty) {B : α} (hB : B ∈ LowerBounds s) : f B ≤ inf (f '' s) :=
  @cSup_image_le αᵒᵈ βᵒᵈ _ _ _ (fun x y hxy => h_mono hxy) _ hs _ hB

end Monotone

namespace GaloisConnection

variable [ConditionallyCompleteLattice α] [ConditionallyCompleteLattice β] [Nonempty ι] {l : α → β} {u : β → α}

theorem l_cSup (gc : GaloisConnection l u) {s : Set α} (hne : s.Nonempty) (hbdd : BddAbove s) :
    l (sup s) = ⨆ x : s, l x :=
  Eq.symm <| IsLub.csupr_set_eq (gc.is_lub_l_image <| is_lub_cSup hne hbdd) hne

theorem l_cSup' (gc : GaloisConnection l u) {s : Set α} (hne : s.Nonempty) (hbdd : BddAbove s) :
    l (sup s) = sup (l '' s) := by
  rw [gc.l_cSup hne hbdd, csupr_set]

theorem l_csupr (gc : GaloisConnection l u) {f : ι → α} (hf : BddAbove (Range f)) : l (⨆ i, f i) = ⨆ i, l (f i) := by
  rw [supr, gc.l_cSup (range_nonempty _) hf, supr_range']

theorem l_csupr_set (gc : GaloisConnection l u) {s : Set γ} {f : γ → α} (hf : BddAbove (f '' s)) (hne : s.Nonempty) :
    l (⨆ i : s, f i) = ⨆ i : s, l (f i) := by
  have := hne.to_subtype
  rw [image_eq_range] at hf
  exact gc.l_csupr hf

theorem u_cInf (gc : GaloisConnection l u) {s : Set β} (hne : s.Nonempty) (hbdd : BddBelow s) :
    u (inf s) = ⨅ x : s, u x :=
  gc.dual.l_cSup hne hbdd

theorem u_cInf' (gc : GaloisConnection l u) {s : Set β} (hne : s.Nonempty) (hbdd : BddBelow s) :
    u (inf s) = inf (u '' s) :=
  gc.dual.l_cSup' hne hbdd

theorem u_cinfi (gc : GaloisConnection l u) {f : ι → β} (hf : BddBelow (Range f)) : u (⨅ i, f i) = ⨅ i, u (f i) :=
  gc.dual.l_csupr hf

theorem u_cinfi_set (gc : GaloisConnection l u) {s : Set γ} {f : γ → β} (hf : BddBelow (f '' s)) (hne : s.Nonempty) :
    u (⨅ i : s, f i) = ⨅ i : s, u (f i) :=
  gc.dual.l_csupr_set hf hne

end GaloisConnection

namespace OrderIso

variable [ConditionallyCompleteLattice α] [ConditionallyCompleteLattice β] [Nonempty ι]

theorem map_cSup (e : α ≃o β) {s : Set α} (hne : s.Nonempty) (hbdd : BddAbove s) : e (sup s) = ⨆ x : s, e x :=
  e.to_galois_connection.l_cSup hne hbdd

theorem map_cSup' (e : α ≃o β) {s : Set α} (hne : s.Nonempty) (hbdd : BddAbove s) : e (sup s) = sup (e '' s) :=
  e.to_galois_connection.l_cSup' hne hbdd

theorem map_csupr (e : α ≃o β) {f : ι → α} (hf : BddAbove (Range f)) : e (⨆ i, f i) = ⨆ i, e (f i) :=
  e.to_galois_connection.l_csupr hf

theorem map_csupr_set (e : α ≃o β) {s : Set γ} {f : γ → α} (hf : BddAbove (f '' s)) (hne : s.Nonempty) :
    e (⨆ i : s, f i) = ⨆ i : s, e (f i) :=
  e.to_galois_connection.l_csupr_set hf hne

theorem map_cInf (e : α ≃o β) {s : Set α} (hne : s.Nonempty) (hbdd : BddBelow s) : e (inf s) = ⨅ x : s, e x :=
  e.dual.map_cSup hne hbdd

theorem map_cInf' (e : α ≃o β) {s : Set α} (hne : s.Nonempty) (hbdd : BddBelow s) : e (inf s) = inf (e '' s) :=
  e.dual.map_cSup' hne hbdd

theorem map_cinfi (e : α ≃o β) {f : ι → α} (hf : BddBelow (Range f)) : e (⨅ i, f i) = ⨅ i, e (f i) :=
  e.dual.map_csupr hf

theorem map_cinfi_set (e : α ≃o β) {s : Set γ} {f : γ → α} (hf : BddBelow (f '' s)) (hne : s.Nonempty) :
    e (⨅ i : s, f i) = ⨅ i : s, e (f i) :=
  e.dual.map_csupr_set hf hne

end OrderIso

/-!
### Supremum/infimum of `set.image2`

A collection of lemmas showing what happens to the suprema/infima of `s` and `t` when mapped under
a binary function whose partial evaluations are lower/upper adjoints of Galois connections.
-/


section

variable [ConditionallyCompleteLattice α] [ConditionallyCompleteLattice β] [ConditionallyCompleteLattice γ]
  {f : α → β → γ} {s : Set α} {t : Set β}

variable {l u : α → β → γ} {l₁ u₁ : β → γ → α} {l₂ u₂ : α → γ → β}

theorem cSup_image2_eq_cSup_cSup (h₁ : ∀ b, GaloisConnection (swap l b) (u₁ b))
    (h₂ : ∀ a, GaloisConnection (l a) (u₂ a)) (hs₀ : s.Nonempty) (hs₁ : BddAbove s) (ht₀ : t.Nonempty)
    (ht₁ : BddAbove t) : sup (Image2 l s t) = l (sup s) (sup t) := by
  refine' eq_of_forall_ge_iff fun c => _
  rw [cSup_le_iff (hs₁.image2 (fun _ => (h₁ _).monotone_l) (fun _ => (h₂ _).monotone_l) ht₁) (hs₀.image2 ht₀),
    forall_image2_iff, forall₂_swap, (h₂ _).le_iff_le, cSup_le_iff ht₁ ht₀]
  simp_rw [← (h₂ _).le_iff_le, (h₁ _).le_iff_le, cSup_le_iff hs₁ hs₀]

theorem cSup_image2_eq_cSup_cInf (h₁ : ∀ b, GaloisConnection (swap l b) (u₁ b))
    (h₂ : ∀ a, GaloisConnection (l a ∘ of_dual) (to_dual ∘ u₂ a)) :
    s.Nonempty → BddAbove s → t.Nonempty → BddBelow t → sup (Image2 l s t) = l (sup s) (inf t) :=
  @cSup_image2_eq_cSup_cSup _ βᵒᵈ _ _ _ _ _ _ _ _ _ h₁ h₂

theorem cSup_image2_eq_cInf_cSup (h₁ : ∀ b, GaloisConnection (swap l b ∘ of_dual) (to_dual ∘ u₁ b))
    (h₂ : ∀ a, GaloisConnection (l a) (u₂ a)) :
    s.Nonempty → BddBelow s → t.Nonempty → BddAbove t → sup (Image2 l s t) = l (inf s) (sup t) :=
  @cSup_image2_eq_cSup_cSup αᵒᵈ _ _ _ _ _ _ _ _ _ _ h₁ h₂

theorem cSup_image2_eq_cInf_cInf (h₁ : ∀ b, GaloisConnection (swap l b ∘ of_dual) (to_dual ∘ u₁ b))
    (h₂ : ∀ a, GaloisConnection (l a ∘ of_dual) (to_dual ∘ u₂ a)) :
    s.Nonempty → BddBelow s → t.Nonempty → BddBelow t → sup (Image2 l s t) = l (inf s) (inf t) :=
  @cSup_image2_eq_cSup_cSup αᵒᵈ βᵒᵈ _ _ _ _ _ _ _ _ _ h₁ h₂

theorem cInf_image2_eq_cInf_cInf (h₁ : ∀ b, GaloisConnection (l₁ b) (swap u b))
    (h₂ : ∀ a, GaloisConnection (l₂ a) (u a)) :
    s.Nonempty → BddBelow s → t.Nonempty → BddBelow t → inf (Image2 u s t) = u (inf s) (inf t) :=
  @cSup_image2_eq_cSup_cSup αᵒᵈ βᵒᵈ γᵒᵈ _ _ _ _ _ _ l₁ l₂ (fun _ => (h₁ _).dual) fun _ => (h₂ _).dual

theorem cInf_image2_eq_cInf_cSup (h₁ : ∀ b, GaloisConnection (l₁ b) (swap u b))
    (h₂ : ∀ a, GaloisConnection (to_dual ∘ l₂ a) (u a ∘ of_dual)) :
    s.Nonempty → BddBelow s → t.Nonempty → BddAbove t → inf (Image2 u s t) = u (inf s) (sup t) :=
  @cInf_image2_eq_cInf_cInf _ βᵒᵈ _ _ _ _ _ _ _ _ _ h₁ h₂

theorem cInf_image2_eq_cSup_cInf (h₁ : ∀ b, GaloisConnection (to_dual ∘ l₁ b) (swap u b ∘ of_dual))
    (h₂ : ∀ a, GaloisConnection (l₂ a) (u a)) :
    s.Nonempty → BddAbove s → t.Nonempty → BddBelow t → inf (Image2 u s t) = u (sup s) (inf t) :=
  @cInf_image2_eq_cInf_cInf αᵒᵈ _ _ _ _ _ _ _ _ _ _ h₁ h₂

theorem cInf_image2_eq_cSup_cSup (h₁ : ∀ b, GaloisConnection (to_dual ∘ l₁ b) (swap u b ∘ of_dual))
    (h₂ : ∀ a, GaloisConnection (to_dual ∘ l₂ a) (u a ∘ of_dual)) :
    s.Nonempty → BddAbove s → t.Nonempty → BddAbove t → inf (Image2 u s t) = u (sup s) (sup t) :=
  @cInf_image2_eq_cInf_cInf αᵒᵈ βᵒᵈ _ _ _ _ _ _ _ _ _ h₁ h₂

end

/-!
### Relation between `Sup` / `Inf` and `finset.sup'` / `finset.inf'`

Like the `Sup` of a `conditionally_complete_lattice`, `finset.sup'` also requires the set to be
non-empty. As a result, we can translate between the two.
-/


namespace Finset

theorem sup'_eq_cSup_image [ConditionallyCompleteLattice β] (s : Finset α) (H) (f : α → β) :
    s.sup' H f = sup (f '' s) := by
  apply le_antisymmₓ
  · refine' (Finset.sup'_le _ _) fun a ha => _
    refine' le_cSup ⟨s.sup' H f, _⟩ ⟨a, ha, rfl⟩
    rintro i ⟨j, hj, rfl⟩
    exact Finset.le_sup' _ hj
    
  · apply cSup_le ((coe_nonempty.mpr H).Image _)
    rintro _ ⟨a, ha, rfl⟩
    exact Finset.le_sup' _ ha
    

theorem inf'_eq_cInf_image [ConditionallyCompleteLattice β] (s : Finset α) (H) (f : α → β) :
    s.inf' H f = inf (f '' s) :=
  @sup'_eq_cSup_image _ βᵒᵈ _ _ _ _

theorem sup'_id_eq_cSup [ConditionallyCompleteLattice α] (s : Finset α) (H) : s.sup' H id = sup s := by
  rw [sup'_eq_cSup_image s H, Set.image_id]

theorem inf'_id_eq_cInf [ConditionallyCompleteLattice α] (s : Finset α) (H) : s.inf' H id = inf s :=
  @sup'_id_eq_cSup αᵒᵈ _ _ _

end Finset

section WithTopBot

/-!
### Complete lattice structure on `with_top (with_bot α)`

If `α` is a `conditionally_complete_lattice`, then we show that `with_top α` and `with_bot α`
also inherit the structure of conditionally complete lattices. Furthermore, we show
that `with_top (with_bot α)` naturally inherits the structure of a complete lattice. Note that
for α a conditionally complete lattice, `Sup` and `Inf` both return junk values
for sets which are empty or unbounded. The extension of `Sup` to `with_top α` fixes
the unboundedness problem and the extension to `with_bot α` fixes the problem with
the empty set.

This result can be used to show that the extended reals [-∞, ∞] are a complete lattice.
-/


open Classical

/-- Adding a top element to a conditionally complete lattice
gives a conditionally complete lattice -/
noncomputable instance WithTop.conditionallyCompleteLattice {α : Type _} [ConditionallyCompleteLattice α] :
    ConditionallyCompleteLattice (WithTop α) :=
  { WithTop.lattice, WithTop.hasSup, WithTop.hasInf with
    le_cSup := fun S a hS haS => (WithTop.is_lub_Sup' ⟨a, haS⟩).1 haS,
    cSup_le := fun S a hS haS => (WithTop.is_lub_Sup' hS).2 haS,
    cInf_le := fun S a hS haS => (WithTop.is_glb_Inf' hS).1 haS,
    le_cInf := fun S a hS haS => (WithTop.is_glb_Inf' ⟨a, haS⟩).2 haS }

/-- Adding a bottom element to a conditionally complete lattice
gives a conditionally complete lattice -/
noncomputable instance WithBot.conditionallyCompleteLattice {α : Type _} [ConditionallyCompleteLattice α] :
    ConditionallyCompleteLattice (WithBot α) :=
  { WithBot.lattice, WithBot.hasSup, WithBot.hasInf with
    le_cSup := (@WithTop.conditionallyCompleteLattice αᵒᵈ _).cInf_le,
    cSup_le := (@WithTop.conditionallyCompleteLattice αᵒᵈ _).le_cInf,
    cInf_le := (@WithTop.conditionallyCompleteLattice αᵒᵈ _).le_cSup,
    le_cInf := (@WithTop.conditionallyCompleteLattice αᵒᵈ _).cSup_le }

noncomputable instance WithTop.WithBot.completeLattice {α : Type _} [ConditionallyCompleteLattice α] :
    CompleteLattice (WithTop (WithBot α)) :=
  { WithTop.hasInf, WithTop.hasSup, WithTop.boundedOrder, WithTop.lattice with
    le_Sup := fun S a haS => (WithTop.is_lub_Sup' ⟨a, haS⟩).1 haS,
    Sup_le := fun S a ha => by
      cases' S.eq_empty_or_nonempty with h
      · show ite _ _ _ ≤ a
        split_ifs
        · rw [h] at h_1
          cases h_1
          
        · convert bot_le
          convert WithBot.cSup_empty
          rw [h]
          rfl
          
        · exfalso
          apply h_2
          use ⊥
          rw [h]
          rintro b ⟨⟩
          
        
      · refine' (WithTop.is_lub_Sup' h).2 ha
        ,
    Inf_le := fun S a haS =>
      show ite _ _ _ ≤ a by
        split_ifs
        · cases' a with a
          exact le_rfl
          cases h haS <;> tauto
          
        · cases a
          · exact le_top
            
          · apply WithTop.some_le_some.2
            refine' cInf_le _ haS
            use ⊥
            intro b hb
            exact bot_le
            
          ,
    le_Inf := fun S a haS => (WithTop.is_glb_Inf' ⟨a, haS⟩).2 haS }

noncomputable instance WithTop.WithBot.completeLinearOrder {α : Type _} [ConditionallyCompleteLinearOrder α] :
    CompleteLinearOrder (WithTop (WithBot α)) :=
  { WithTop.WithBot.completeLattice, WithTop.linearOrder with }

end WithTopBot

section Groupₓ

variable {ι' : Sort _} [Nonempty ι] [Nonempty ι'] [ConditionallyCompleteLattice α] [Groupₓ α]

@[to_additive]
theorem le_mul_cinfi [CovariantClass α α (· * ·) (· ≤ ·)] {a : α} {g : α} {h : ι → α} (H : ∀ j, a ≤ g * h j) :
    a ≤ g * infi h :=
  inv_mul_le_iff_le_mul.mp <| le_cinfi fun hi => inv_mul_le_iff_le_mul.mpr <| H _

@[to_additive]
theorem mul_csupr_le [CovariantClass α α (· * ·) (· ≤ ·)] {a : α} {g : α} {h : ι → α} (H : ∀ j, g * h j ≤ a) :
    g * supr h ≤ a :=
  @le_mul_cinfi αᵒᵈ _ _ _ _ _ _ _ _ H

@[to_additive]
theorem le_cinfi_mul [CovariantClass α α (Function.swap (· * ·)) (· ≤ ·)] {a : α} {g : ι → α} {h : α}
    (H : ∀ i, a ≤ g i * h) : a ≤ infi g * h :=
  mul_inv_le_iff_le_mul.mp <| le_cinfi fun gi => mul_inv_le_iff_le_mul.mpr <| H _

@[to_additive]
theorem csupr_mul_le [CovariantClass α α (Function.swap (· * ·)) (· ≤ ·)] {a : α} {g : ι → α} {h : α}
    (H : ∀ i, g i * h ≤ a) : supr g * h ≤ a :=
  @le_cinfi_mul αᵒᵈ _ _ _ _ _ _ _ _ H

@[to_additive]
theorem le_cinfi_mul_cinfi [CovariantClass α α (· * ·) (· ≤ ·)] [CovariantClass α α (Function.swap (· * ·)) (· ≤ ·)]
    {a : α} {g : ι → α} {h : ι' → α} (H : ∀ i j, a ≤ g i * h j) : a ≤ infi g * infi h :=
  le_cinfi_mul fun i => le_mul_cinfi <| H _

@[to_additive]
theorem csupr_mul_csupr_le [CovariantClass α α (· * ·) (· ≤ ·)] [CovariantClass α α (Function.swap (· * ·)) (· ≤ ·)]
    {a : α} {g : ι → α} {h : ι' → α} (H : ∀ i j, g i * h j ≤ a) : supr g * supr h ≤ a :=
  csupr_mul_le fun i => mul_csupr_le <| H _

end Groupₓ

