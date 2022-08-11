/-
Copyright (c) 2020 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Mario Carneiro, Yury G. Kudryashov
-/
import Mathbin.Order.Basic
import Mathbin.Logic.IsEmpty

/-!
# Unbundled relation classes

In this file we prove some properties of `is_*` classes defined in `init.algebra.classes`. The main
difference between these classes and the usual order classes (`preorder` etc) is that usual classes
extend `has_le` and/or `has_lt` while these classes take a relation as an explicit argument.

-/


universe u v

variable {α : Type u} {β : Type v} {r : α → α → Prop} {s : β → β → Prop}

open Function

theorem of_eq [IsRefl α r] : ∀ {a b}, a = b → r a b
  | _, _, ⟨h⟩ => refl _

theorem comm [IsSymm α r] {a b : α} : r a b ↔ r b a :=
  ⟨symm, symm⟩

theorem antisymm' [IsAntisymm α r] {a b : α} : r a b → r b a → b = a := fun h h' => antisymm h' h

theorem antisymm_iff [IsRefl α r] [IsAntisymm α r] {a b : α} : r a b ∧ r b a ↔ a = b :=
  ⟨fun h => antisymm h.1 h.2, by
    rintro rfl
    exact ⟨refl _, refl _⟩⟩

/-- A version of `antisymm` with `r` explicit.

This lemma matches the lemmas from lean core in `init.algebra.classes`, but is missing there.  -/
@[elabWithoutExpectedType]
theorem antisymm_of (r : α → α → Prop) [IsAntisymm α r] {a b : α} : r a b → r b a → a = b :=
  antisymm

/-- A version of `antisymm'` with `r` explicit.

This lemma matches the lemmas from lean core in `init.algebra.classes`, but is missing there.  -/
@[elabWithoutExpectedType]
theorem antisymm_of' (r : α → α → Prop) [IsAntisymm α r] {a b : α} : r a b → r b a → b = a :=
  antisymm'

/-- A version of `comm` with `r` explicit.

This lemma matches the lemmas from lean core in `init.algebra.classes`, but is missing there.  -/
theorem comm_of (r : α → α → Prop) [IsSymm α r] {a b : α} : r a b ↔ r b a :=
  comm

theorem IsRefl.swap (r) [IsRefl α r] : IsRefl α (swap r) :=
  ⟨refl_of r⟩

theorem IsIrrefl.swap (r) [IsIrrefl α r] : IsIrrefl α (swap r) :=
  ⟨irrefl_of r⟩

theorem IsTrans.swap (r) [IsTrans α r] : IsTrans α (swap r) :=
  ⟨fun a b c h₁ h₂ => trans_of r h₂ h₁⟩

theorem IsAntisymm.swap (r) [IsAntisymm α r] : IsAntisymm α (swap r) :=
  ⟨fun a b h₁ h₂ => antisymm h₂ h₁⟩

theorem IsAsymm.swap (r) [IsAsymm α r] : IsAsymm α (swap r) :=
  ⟨fun a b h₁ h₂ => asymm_of r h₂ h₁⟩

theorem IsTotal.swap (r) [IsTotal α r] : IsTotal α (swap r) :=
  ⟨fun a b => (total_of r a b).swap⟩

theorem IsTrichotomous.swap (r) [IsTrichotomous α r] : IsTrichotomous α (swap r) :=
  ⟨fun a b => by
    simpa [← swap, ← Or.comm, ← Or.left_comm] using trichotomous_of r a b⟩

theorem IsPreorder.swap (r) [IsPreorder α r] : IsPreorder α (swap r) :=
  { @IsRefl.swap α r _, @IsTrans.swap α r _ with }

theorem IsStrictOrder.swap (r) [IsStrictOrder α r] : IsStrictOrder α (swap r) :=
  { @IsIrrefl.swap α r _, @IsTrans.swap α r _ with }

theorem IsPartialOrder.swap (r) [IsPartialOrder α r] : IsPartialOrder α (swap r) :=
  { @IsPreorder.swap α r _, @IsAntisymm.swap α r _ with }

theorem IsTotalPreorder.swap (r) [IsTotalPreorder α r] : IsTotalPreorder α (swap r) :=
  { @IsPreorder.swap α r _, @IsTotal.swap α r _ with }

theorem IsLinearOrder.swap (r) [IsLinearOrder α r] : IsLinearOrder α (swap r) :=
  { @IsPartialOrder.swap α r _, @IsTotal.swap α r _ with }

protected theorem IsAsymm.is_antisymm (r) [IsAsymm α r] : IsAntisymm α r :=
  ⟨fun x y h₁ h₂ => (asymm h₁ h₂).elim⟩

protected theorem IsAsymm.is_irrefl [IsAsymm α r] : IsIrrefl α r :=
  ⟨fun a h => asymm h h⟩

protected theorem IsTotal.is_trichotomous (r) [IsTotal α r] : IsTrichotomous α r :=
  ⟨fun a b => Or.left_comm.1 (Or.inr <| total_of r a b)⟩

-- see Note [lower instance priority]
instance (priority := 100) IsTotal.to_is_refl (r) [IsTotal α r] : IsRefl α r :=
  ⟨fun a => (or_selfₓ _).1 <| total_of r a a⟩

theorem ne_of_irrefl {r} [IsIrrefl α r] : ∀ {x y : α}, r x y → x ≠ y
  | _, _, h, rfl => irrefl _ h

theorem ne_of_irrefl' {r} [IsIrrefl α r] : ∀ {x y : α}, r x y → y ≠ x
  | _, _, h, rfl => irrefl _ h

theorem not_rel_of_subsingleton (r) [IsIrrefl α r] [Subsingleton α] (x y) : ¬r x y :=
  Subsingleton.elimₓ x y ▸ irrefl x

theorem rel_of_subsingleton (r) [IsRefl α r] [Subsingleton α] (x y) : r x y :=
  Subsingleton.elimₓ x y ▸ refl x

@[simp]
theorem empty_relation_apply (a b : α) : EmptyRelation a b ↔ False :=
  Iff.rfl

theorem eq_empty_relation (r) [IsIrrefl α r] [Subsingleton α] : r = EmptyRelation :=
  funext₂ <| by
    simpa using not_rel_of_subsingleton r

instance : IsIrrefl α EmptyRelation :=
  ⟨fun a => id⟩

theorem trans_trichotomous_left [IsTrans α r] [IsTrichotomous α r] {a b c : α} : ¬r b a → r b c → r a c := by
  intro h₁ h₂
  rcases trichotomous_of r a b with (h₃ | h₃ | h₃)
  exact trans h₃ h₂
  rw [h₃]
  exact h₂
  exfalso
  exact h₁ h₃

theorem trans_trichotomous_right [IsTrans α r] [IsTrichotomous α r] {a b c : α} : r a b → ¬r c b → r a c := by
  intro h₁ h₂
  rcases trichotomous_of r b c with (h₃ | h₃ | h₃)
  exact trans h₁ h₃
  rw [← h₃]
  exact h₁
  exfalso
  exact h₂ h₃

theorem transitive_of_trans (r : α → α → Prop) [IsTrans α r] : Transitive r := fun _ _ _ => trans

/-- Construct a partial order from a `is_strict_order` relation.

See note [reducible non-instances]. -/
@[reducible]
def partialOrderOfSO (r) [IsStrictOrder α r] : PartialOrderₓ α where
  le := fun x y => x = y ∨ r x y
  lt := r
  le_refl := fun x => Or.inl rfl
  le_trans := fun x y z h₁ h₂ =>
    match y, z, h₁, h₂ with
    | _, _, Or.inl rfl, h₂ => h₂
    | _, _, h₁, Or.inl rfl => h₁
    | _, _, Or.inr h₁, Or.inr h₂ => Or.inr (trans h₁ h₂)
  le_antisymm := fun x y h₁ h₂ =>
    match y, h₁, h₂ with
    | _, Or.inl rfl, h₂ => rfl
    | _, h₁, Or.inl rfl => rfl
    | _, Or.inr h₁, Or.inr h₂ => (asymm h₁ h₂).elim
  lt_iff_le_not_le := fun x y =>
    ⟨fun h =>
      ⟨Or.inr h,
        not_orₓ
          (fun e => by
            rw [e] at h <;> exact irrefl _ h)
          (asymm h)⟩,
      fun ⟨h₁, h₂⟩ => h₁.resolve_left fun e => h₂ <| e ▸ Or.inl rfl⟩

/-- This is basically the same as `is_strict_total_order`, but that definition has a redundant
assumption `is_incomp_trans α lt`. -/
@[algebra]
class IsStrictTotalOrder' (α : Type u) (lt : α → α → Prop) extends IsTrichotomous α lt, IsStrictOrder α lt : Prop

/-- Construct a linear order from an `is_strict_total_order'` relation.

See note [reducible non-instances]. -/
@[reducible]
def linearOrderOfSTO' (r) [IsStrictTotalOrder' α r] [∀ x y, Decidable ¬r x y] : LinearOrderₓ α :=
  { partialOrderOfSO r with
    le_total := fun x y =>
      match y, trichotomous_of r x y with
      | y, Or.inl h => Or.inl (Or.inr h)
      | _, Or.inr (Or.inl rfl) => Or.inl (Or.inl rfl)
      | _, Or.inr (Or.inr h) => Or.inr (Or.inr h),
    decidableLe := fun x y =>
      decidableOfIff (¬r y x)
        ⟨fun h => ((trichotomous_of r y x).resolve_left h).imp Eq.symm id, fun h =>
          h.elim (fun h => h ▸ irrefl_of _ _) (asymm_of r)⟩ }

theorem IsStrictTotalOrder'.swap (r) [IsStrictTotalOrder' α r] : IsStrictTotalOrder' α (swap r) :=
  { IsTrichotomous.swap r, IsStrictOrder.swap r with }

/-! ### Order connection -/


/-- A connected order is one satisfying the condition `a < c → a < b ∨ b < c`.
  This is recognizable as an intuitionistic substitute for `a ≤ b ∨ b ≤ a` on
  the constructive reals, and is also known as negative transitivity,
  since the contrapositive asserts transitivity of the relation `¬ a < b`.  -/
@[algebra]
class IsOrderConnected (α : Type u) (lt : α → α → Prop) : Prop where
  conn : ∀ a b c, lt a c → lt a b ∨ lt b c

theorem IsOrderConnected.neg_trans {r : α → α → Prop} [IsOrderConnected α r] {a b c} (h₁ : ¬r a b) (h₂ : ¬r b c) :
    ¬r a c :=
  mt (IsOrderConnected.conn a b c) <| by
    simp [← h₁, ← h₂]

theorem is_strict_weak_order_of_is_order_connected [IsAsymm α r] [IsOrderConnected α r] : IsStrictWeakOrder α r :=
  { @IsAsymm.is_irrefl α r _ with trans := fun a b c h₁ h₂ => (IsOrderConnected.conn _ c _ h₁).resolve_right (asymm h₂),
    incomp_trans := fun a b c ⟨h₁, h₂⟩ ⟨h₃, h₄⟩ =>
      ⟨IsOrderConnected.neg_trans h₁ h₃, IsOrderConnected.neg_trans h₄ h₂⟩ }

-- see Note [lower instance priority]
instance (priority := 100) is_order_connected_of_is_strict_total_order' [IsStrictTotalOrder' α r] :
    IsOrderConnected α r :=
  ⟨fun a b c h => (trichotomous _ _).imp_right fun o => o.elim (fun e => e ▸ h) fun h' => trans h' h⟩

-- see Note [lower instance priority]
instance (priority := 100) is_strict_total_order_of_is_strict_total_order' [IsStrictTotalOrder' α r] :
    IsStrictTotalOrder α r :=
  { is_strict_weak_order_of_is_order_connected with }

/-! ### Extensional relation -/


/-- An extensional relation is one in which an element is determined by its set
  of predecessors. It is named for the `x ∈ y` relation in set theory, whose
  extensionality is one of the first axioms of ZFC. -/
@[algebra]
class IsExtensional (α : Type u) (r : α → α → Prop) : Prop where
  ext : ∀ a b, (∀ x, r x a ↔ r x b) → a = b

-- see Note [lower instance priority]
instance (priority := 100) is_extensional_of_is_strict_total_order' [IsStrictTotalOrder' α r] : IsExtensional α r :=
  ⟨fun a b H =>
    ((@trichotomous _ r _ a b).resolve_left <| mt (H _).2 (irrefl a)).resolve_right <| mt (H _).1 (irrefl b)⟩

/-! ### Well-order -/


/-- A well order is a well-founded linear order. -/
@[algebra]
class IsWellOrder (α : Type u) (r : α → α → Prop) extends IsStrictTotalOrder' α r : Prop where
  wf : WellFounded r

-- see Note [lower instance priority]
instance (priority := 100) IsWellOrder.is_strict_total_order {α} (r : α → α → Prop) [IsWellOrder α r] :
    IsStrictTotalOrder α r := by
  infer_instance

-- see Note [lower instance priority]
instance (priority := 100) IsWellOrder.is_extensional {α} (r : α → α → Prop) [IsWellOrder α r] : IsExtensional α r := by
  infer_instance

-- see Note [lower instance priority]
instance (priority := 100) IsWellOrder.is_trichotomous {α} (r : α → α → Prop) [IsWellOrder α r] : IsTrichotomous α r :=
  by
  infer_instance

-- see Note [lower instance priority]
instance (priority := 100) IsWellOrder.is_trans {α} (r : α → α → Prop) [IsWellOrder α r] : IsTrans α r := by
  infer_instance

-- see Note [lower instance priority]
instance (priority := 100) IsWellOrder.is_irrefl {α} (r : α → α → Prop) [IsWellOrder α r] : IsIrrefl α r := by
  infer_instance

-- see Note [lower instance priority]
instance (priority := 100) IsWellOrder.is_asymm {α} (r : α → α → Prop) [IsWellOrder α r] : IsAsymm α r := by
  infer_instance

/-- Construct a decidable linear order from a well-founded linear order. -/
noncomputable def IsWellOrder.linearOrder (r : α → α → Prop) [IsWellOrder α r] : LinearOrderₓ α := by
  let this := fun x y => Classical.dec ¬r x y
  exact linearOrderOfSTO' r

/-- Derive a `has_well_founded` instance from a `is_well_order` instance. -/
def IsWellOrder.toHasWellFounded [LT α] [hwo : IsWellOrder α (· < ·)] : HasWellFounded α where
  R := (· < ·)
  wf := hwo.wf

-- This isn't made into an instance as it loops with `is_irrefl α r`.
theorem Subsingleton.is_well_order [Subsingleton α] (r : α → α → Prop) [hr : IsIrrefl α r] : IsWellOrder α r :=
  { hr with trichotomous := fun a b => Or.inr <| Or.inl <| Subsingleton.elimₓ a b,
    trans := fun a b c h => (not_rel_of_subsingleton r a b h).elim,
    wf := ⟨fun a => ⟨_, fun y h => (not_rel_of_subsingleton r y a h).elim⟩⟩ }

instance EmptyRelation.is_well_order [Subsingleton α] : IsWellOrder α EmptyRelation :=
  Subsingleton.is_well_order _

instance (priority := 100) IsEmpty.is_well_order [IsEmpty α] (r : α → α → Prop) : IsWellOrder α r where
  trichotomous := isEmptyElim
  irrefl := isEmptyElim
  trans := isEmptyElim
  wf := well_founded_of_empty r

instance Prod.Lex.is_well_order [IsWellOrder α r] [IsWellOrder β s] : IsWellOrder (α × β) (Prod.Lex r s) where
  trichotomous := fun ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ =>
    match @trichotomous _ r _ a₁ b₁ with
    | Or.inl h₁ => Or.inl <| Prod.Lex.left _ _ h₁
    | Or.inr (Or.inr h₁) => Or.inr <| Or.inr <| Prod.Lex.left _ _ h₁
    | Or.inr (Or.inl e) =>
      e ▸
        match @trichotomous _ s _ a₂ b₂ with
        | Or.inl h => Or.inl <| Prod.Lex.right _ h
        | Or.inr (Or.inr h) => Or.inr <| Or.inr <| Prod.Lex.right _ h
        | Or.inr (Or.inl e) => e ▸ Or.inr <| Or.inl rfl
  irrefl := fun ⟨a₁, a₂⟩ h => by
    cases' h with _ _ _ _ h _ _ _ h <;> [exact irrefl _ h, exact irrefl _ h]
  trans := fun a b c h₁ h₂ => by
    cases' h₁ with a₁ a₂ b₁ b₂ ab a₁ b₁ b₂ ab <;> cases' h₂ with _ _ c₁ c₂ bc _ _ c₂ bc
    · exact Prod.Lex.left _ _ (trans ab bc)
      
    · exact Prod.Lex.left _ _ ab
      
    · exact Prod.Lex.left _ _ bc
      
    · exact Prod.Lex.right _ (trans ab bc)
      
  wf := Prod.lex_wf IsWellOrder.wf IsWellOrder.wf

namespace Set

/-- An unbounded or cofinal set. -/
def Unbounded (r : α → α → Prop) (s : Set α) : Prop :=
  ∀ a, ∃ b ∈ s, ¬r b a

/-- A bounded or final set. Not to be confused with `metric.bounded`. -/
def Bounded (r : α → α → Prop) (s : Set α) : Prop :=
  ∃ a, ∀, ∀ b ∈ s, ∀, r b a

@[simp]
theorem not_bounded_iff {r : α → α → Prop} (s : Set α) : ¬Bounded r s ↔ Unbounded r s := by
  simp only [← bounded, ← unbounded, ← not_forall, ← not_exists, ← exists_prop, ← not_and, ← not_not]

@[simp]
theorem not_unbounded_iff {r : α → α → Prop} (s : Set α) : ¬Unbounded r s ↔ Bounded r s := by
  rw [not_iff_comm, not_bounded_iff]

theorem unbounded_of_is_empty [IsEmpty α] {r : α → α → Prop} (s : Set α) : Unbounded r s :=
  isEmptyElim

end Set

namespace Prod

instance is_refl_preimage_fst {r : α → α → Prop} [h : IsRefl α r] : IsRefl (α × α) (Prod.fst ⁻¹'o r) :=
  ⟨fun a => refl_of r a.1⟩

instance is_refl_preimage_snd {r : α → α → Prop} [h : IsRefl α r] : IsRefl (α × α) (Prod.snd ⁻¹'o r) :=
  ⟨fun a => refl_of r a.2⟩

instance is_trans_preimage_fst {r : α → α → Prop} [h : IsTrans α r] : IsTrans (α × α) (Prod.fst ⁻¹'o r) :=
  ⟨fun _ _ _ => trans_of r⟩

instance is_trans_preimage_snd {r : α → α → Prop} [h : IsTrans α r] : IsTrans (α × α) (Prod.snd ⁻¹'o r) :=
  ⟨fun _ _ _ => trans_of r⟩

end Prod

/-! ### Strict-non strict relations -/


/-- An unbundled relation class stating that `r` is the nonstrict relation corresponding to the
strict relation `s`. Compare `preorder.lt_iff_le_not_le`. This is mostly meant to provide dot
notation on `(⊆)` and `(⊂)`. -/
class IsNonstrictStrictOrder (α : Type _) (r s : α → α → Prop) where
  right_iff_left_not_left (a b : α) : s a b ↔ r a b ∧ ¬r b a

theorem right_iff_left_not_left {r s : α → α → Prop} [IsNonstrictStrictOrder α r s] {a b : α} :
    s a b ↔ r a b ∧ ¬r b a :=
  IsNonstrictStrictOrder.right_iff_left_not_left _ _

/-- A version of `right_iff_left_not_left` with explicit `r` and `s`. -/
theorem right_iff_left_not_left_of (r s : α → α → Prop) [IsNonstrictStrictOrder α r s] {a b : α} :
    s a b ↔ r a b ∧ ¬r b a :=
  right_iff_left_not_left

-- The free parameter `r` is strictly speaking not uniquely determined by `s`, but in practice it
-- always has a unique instance, so this is not dangerous.
-- see Note [lower instance priority]
@[nolint dangerous_instance]
instance (priority := 100) IsNonstrictStrictOrder.to_is_irrefl {r : α → α → Prop} {s : α → α → Prop}
    [IsNonstrictStrictOrder α r s] : IsIrrefl α s :=
  ⟨fun a h => ((right_iff_left_not_left_of r s).1 h).2 ((right_iff_left_not_left_of r s).1 h).1⟩

/-! #### `⊆` and `⊂` -/


section Subset

variable [HasSubset α] {a b c : α}

@[refl]
theorem subset_refl [IsRefl α (· ⊆ ·)] (a : α) : a ⊆ a :=
  refl _

theorem subset_rfl [IsRefl α (· ⊆ ·)] : a ⊆ a :=
  refl _

theorem subset_of_eq [IsRefl α (· ⊆ ·)] : a = b → a ⊆ b := fun h => h ▸ subset_rfl

theorem superset_of_eq [IsRefl α (· ⊆ ·)] : a = b → b ⊆ a := fun h => h ▸ subset_rfl

theorem ne_of_not_subset [IsRefl α (· ⊆ ·)] : ¬a ⊆ b → a ≠ b :=
  mt subset_of_eq

theorem ne_of_not_superset [IsRefl α (· ⊆ ·)] : ¬a ⊆ b → b ≠ a :=
  mt superset_of_eq

@[trans]
theorem subset_trans [IsTrans α (· ⊆ ·)] {a b c : α} : a ⊆ b → b ⊆ c → a ⊆ c :=
  trans

theorem subset_antisymm [IsAntisymm α (· ⊆ ·)] (h : a ⊆ b) (h' : b ⊆ a) : a = b :=
  antisymm h h'

theorem superset_antisymm [IsAntisymm α (· ⊆ ·)] (h : a ⊆ b) (h' : b ⊆ a) : b = a :=
  antisymm' h h'

alias subset_of_eq ← Eq.subset'

--TODO: Fix it and kill `eq.subset`
alias superset_of_eq ← Eq.superset

alias subset_trans ← HasSubset.Subset.trans

alias subset_antisymm ← HasSubset.Subset.antisymm

alias superset_antisymm ← HasSubset.Subset.antisymm'

theorem subset_antisymm_iff [IsRefl α (· ⊆ ·)] [IsAntisymm α (· ⊆ ·)] : a = b ↔ a ⊆ b ∧ b ⊆ a :=
  ⟨fun h => ⟨h.subset', h.Superset⟩, fun h => h.1.antisymm h.2⟩

theorem superset_antisymm_iff [IsRefl α (· ⊆ ·)] [IsAntisymm α (· ⊆ ·)] : a = b ↔ b ⊆ a ∧ a ⊆ b :=
  ⟨fun h => ⟨h.Superset, h.subset'⟩, fun h => h.1.antisymm' h.2⟩

end Subset

section Ssubset

variable [HasSsubset α]

theorem ssubset_irrefl [IsIrrefl α (· ⊂ ·)] (a : α) : ¬a ⊂ a :=
  irrefl _

theorem ssubset_irrfl [IsIrrefl α (· ⊂ ·)] {a : α} : ¬a ⊂ a :=
  irrefl _

theorem ne_of_ssubset [IsIrrefl α (· ⊂ ·)] {a b : α} : a ⊂ b → a ≠ b :=
  ne_of_irrefl

theorem ne_of_ssuperset [IsIrrefl α (· ⊂ ·)] {a b : α} : a ⊂ b → b ≠ a :=
  ne_of_irrefl'

@[trans]
theorem ssubset_trans [IsTrans α (· ⊂ ·)] {a b c : α} : a ⊂ b → b ⊂ c → a ⊂ c :=
  trans

theorem ssubset_asymm [IsAsymm α (· ⊂ ·)] {a b : α} (h : a ⊂ b) : ¬b ⊂ a :=
  asymm h

alias ssubset_irrfl ← HasSsubset.Ssubset.false

alias ne_of_ssubset ← HasSsubset.Ssubset.ne

alias ne_of_ssuperset ← HasSsubset.Ssubset.ne'

alias ssubset_trans ← HasSsubset.Ssubset.trans

alias ssubset_asymm ← HasSsubset.Ssubset.asymm

end Ssubset

section SubsetSsubset

variable [HasSubset α] [HasSsubset α] [IsNonstrictStrictOrder α (· ⊆ ·) (· ⊂ ·)] {a b c : α}

theorem ssubset_iff_subset_not_subset : a ⊂ b ↔ a ⊆ b ∧ ¬b ⊆ a :=
  right_iff_left_not_left

theorem subset_of_ssubset (h : a ⊂ b) : a ⊆ b :=
  (ssubset_iff_subset_not_subset.1 h).1

theorem not_subset_of_ssubset (h : a ⊂ b) : ¬b ⊆ a :=
  (ssubset_iff_subset_not_subset.1 h).2

theorem not_ssubset_of_subset (h : a ⊆ b) : ¬b ⊂ a := fun h' => not_subset_of_ssubset h' h

theorem ssubset_of_subset_not_subset (h₁ : a ⊆ b) (h₂ : ¬b ⊆ a) : a ⊂ b :=
  ssubset_iff_subset_not_subset.2 ⟨h₁, h₂⟩

alias subset_of_ssubset ← HasSsubset.Ssubset.subset

alias not_subset_of_ssubset ← HasSsubset.Ssubset.not_subset

alias not_ssubset_of_subset ← HasSubset.Subset.not_ssubset

alias ssubset_of_subset_not_subset ← HasSubset.Subset.ssubset_of_not_subset

theorem ssubset_of_subset_of_ssubset [IsTrans α (· ⊆ ·)] (h₁ : a ⊆ b) (h₂ : b ⊂ c) : a ⊂ c :=
  (h₁.trans h₂.Subset).ssubset_of_not_subset fun h => h₂.not_subset <| h.trans h₁

theorem ssubset_of_ssubset_of_subset [IsTrans α (· ⊆ ·)] (h₁ : a ⊂ b) (h₂ : b ⊆ c) : a ⊂ c :=
  (h₁.Subset.trans h₂).ssubset_of_not_subset fun h => h₁.not_subset <| h₂.trans h

theorem ssubset_of_subset_of_ne [IsAntisymm α (· ⊆ ·)] (h₁ : a ⊆ b) (h₂ : a ≠ b) : a ⊂ b :=
  h₁.ssubset_of_not_subset <| mt h₁.antisymm h₂

theorem ssubset_of_ne_of_subset [IsAntisymm α (· ⊆ ·)] (h₁ : a ≠ b) (h₂ : a ⊆ b) : a ⊂ b :=
  ssubset_of_subset_of_ne h₂ h₁

theorem eq_or_ssubset_of_subset [IsAntisymm α (· ⊆ ·)] (h : a ⊆ b) : a = b ∨ a ⊂ b :=
  (em (b ⊆ a)).imp h.antisymm h.ssubset_of_not_subset

theorem ssubset_or_eq_of_subset [IsAntisymm α (· ⊆ ·)] (h : a ⊆ b) : a ⊂ b ∨ a = b :=
  (eq_or_ssubset_of_subset h).swap

alias ssubset_of_subset_of_ssubset ← HasSubset.Subset.trans_ssubset

alias ssubset_of_ssubset_of_subset ← HasSsubset.Ssubset.trans_subset

alias ssubset_of_subset_of_ne ← HasSubset.Subset.ssubset_of_ne

alias ssubset_of_ne_of_subset ← Ne.ssubset_of_subset

alias eq_or_ssubset_of_subset ← HasSubset.Subset.eq_or_ssubset

alias ssubset_or_eq_of_subset ← HasSubset.Subset.ssubset_or_eq

theorem ssubset_iff_subset_ne [IsAntisymm α (· ⊆ ·)] : a ⊂ b ↔ a ⊆ b ∧ a ≠ b :=
  ⟨fun h => ⟨h.Subset, h.Ne⟩, fun h => h.1.ssubset_of_ne h.2⟩

theorem subset_iff_ssubset_or_eq [IsRefl α (· ⊆ ·)] [IsAntisymm α (· ⊆ ·)] : a ⊆ b ↔ a ⊂ b ∨ a = b :=
  ⟨fun h => h.ssubset_or_eq, fun h => h.elim subset_of_ssubset subset_of_eq⟩

end SubsetSsubset

/-! ### Conversion of bundled order typeclasses to unbundled relation typeclasses -/


instance [Preorderₓ α] : IsRefl α (· ≤ ·) :=
  ⟨le_reflₓ⟩

instance [Preorderₓ α] : IsRefl α (· ≥ ·) :=
  IsRefl.swap _

instance [Preorderₓ α] : IsTrans α (· ≤ ·) :=
  ⟨@le_transₓ _ _⟩

instance [Preorderₓ α] : IsTrans α (· ≥ ·) :=
  IsTrans.swap _

instance [Preorderₓ α] : IsPreorder α (· ≤ ·) where

instance [Preorderₓ α] : IsPreorder α (· ≥ ·) where

instance [Preorderₓ α] : IsIrrefl α (· < ·) :=
  ⟨lt_irreflₓ⟩

instance [Preorderₓ α] : IsIrrefl α (· > ·) :=
  IsIrrefl.swap _

instance [Preorderₓ α] : IsTrans α (· < ·) :=
  ⟨@lt_transₓ _ _⟩

instance [Preorderₓ α] : IsTrans α (· > ·) :=
  IsTrans.swap _

instance [Preorderₓ α] : IsAsymm α (· < ·) :=
  ⟨@lt_asymmₓ _ _⟩

instance [Preorderₓ α] : IsAsymm α (· > ·) :=
  IsAsymm.swap _

instance [Preorderₓ α] : IsAntisymm α (· < ·) :=
  IsAsymm.is_antisymm _

instance [Preorderₓ α] : IsAntisymm α (· > ·) :=
  IsAsymm.is_antisymm _

instance [Preorderₓ α] : IsStrictOrder α (· < ·) where

instance [Preorderₓ α] : IsStrictOrder α (· > ·) where

instance [Preorderₓ α] : IsNonstrictStrictOrder α (· ≤ ·) (· < ·) :=
  ⟨@lt_iff_le_not_leₓ _ _⟩

instance [PartialOrderₓ α] : IsAntisymm α (· ≤ ·) :=
  ⟨@le_antisymmₓ _ _⟩

instance [PartialOrderₓ α] : IsAntisymm α (· ≥ ·) :=
  IsAntisymm.swap _

instance [PartialOrderₓ α] : IsPartialOrder α (· ≤ ·) where

instance [PartialOrderₓ α] : IsPartialOrder α (· ≥ ·) where

instance [LinearOrderₓ α] : IsTotal α (· ≤ ·) :=
  ⟨le_totalₓ⟩

instance [LinearOrderₓ α] : IsTotal α (· ≥ ·) :=
  IsTotal.swap _

instance LinearOrderₓ.is_total_preorder [LinearOrderₓ α] : IsTotalPreorder α (· ≤ ·) := by
  infer_instance

instance [LinearOrderₓ α] : IsTotalPreorder α (· ≥ ·) where

instance [LinearOrderₓ α] : IsLinearOrder α (· ≤ ·) where

instance [LinearOrderₓ α] : IsLinearOrder α (· ≥ ·) where

instance [LinearOrderₓ α] : IsTrichotomous α (· < ·) :=
  ⟨lt_trichotomyₓ⟩

instance [LinearOrderₓ α] : IsTrichotomous α (· > ·) :=
  IsTrichotomous.swap _

instance [LinearOrderₓ α] : IsTrichotomous α (· ≤ ·) :=
  IsTotal.is_trichotomous _

instance [LinearOrderₓ α] : IsTrichotomous α (· ≥ ·) :=
  IsTotal.is_trichotomous _

instance [LinearOrderₓ α] : IsStrictTotalOrder α (· < ·) := by
  infer_instance

instance [LinearOrderₓ α] : IsStrictTotalOrder' α (· < ·) where

instance [LinearOrderₓ α] : IsOrderConnected α (· < ·) := by
  infer_instance

instance [LinearOrderₓ α] : IsIncompTrans α (· < ·) := by
  infer_instance

instance [LinearOrderₓ α] : IsStrictWeakOrder α (· < ·) := by
  infer_instance

theorem transitive_le [Preorderₓ α] : Transitive (@LE.le α _) :=
  transitive_of_trans _

theorem transitive_lt [Preorderₓ α] : Transitive (@LT.lt α _) :=
  transitive_of_trans _

theorem transitive_ge [Preorderₓ α] : Transitive (@Ge α _) :=
  transitive_of_trans _

theorem transitive_gt [Preorderₓ α] : Transitive (@Gt α _) :=
  transitive_of_trans _

instance OrderDual.is_total_le [LE α] [IsTotal α (· ≤ ·)] : IsTotal αᵒᵈ (· ≤ ·) :=
  @IsTotal.swap α _ _

instance Nat.Lt.is_well_order : IsWellOrder ℕ (· < ·) :=
  ⟨Nat.lt_wf⟩

instance [LinearOrderₓ α] [h : IsWellOrder α (· < ·)] : IsWellOrder αᵒᵈ (· > ·) :=
  h

instance [LinearOrderₓ α] [h : IsWellOrder α (· > ·)] : IsWellOrder αᵒᵈ (· < ·) :=
  h

