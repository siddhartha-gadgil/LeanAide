/-
Copyright (c) 2022 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathbin.ModelTheory.Semantics

/-!
# Ordered First-Ordered Structures
This file defines ordered first-order languages and structures, as well as their theories.

## Main Definitions
* `first_order.language.order` is the language consisting of a single relation representing `≤`.
* `first_order.language.order_Structure` is the structure on an ordered type, assigning the symbol
representing `≤` to the actual relation `≤`.
* `first_order.language.is_ordered` points out a specific symbol in a language as representing `≤`.
* `first_order.language.is_ordered_structure` indicates that a structure over a
* `first_order.language.Theory.linear_order` and similar define the theories of preorders,
partial orders, and linear orders.
* `first_order.language.Theory.DLO` defines the theory of dense linear orders without endpoints, a
particularly useful example in model theory.


## Main Results
* `partial_order`s model the theory of partial orders, `linear_order`s model the theory of
linear orders, and dense linear orders without endpoints model `Theory.DLO`.

-/


universe u v w w'

namespace FirstOrder

namespace Language

open FirstOrder

open Structure

variable {L : Language.{u, v}} {α : Type w} {M : Type w'} {n : ℕ}

/-- The language consisting of a single relation representing `≤`. -/
protected def order : Language :=
  Language.mk₂ Empty Empty Empty Empty Unit

namespace Order

instance structure [LE M] : Language.order.Structure M :=
  Structure.mk₂ Empty.elim Empty.elim Empty.elim Empty.elim fun _ => (· ≤ ·)

instance : IsRelational Language.order :=
  language.is_relational_mk₂

instance : Subsingleton (Language.order.Relations n) :=
  language.subsingleton_mk₂_relations

end Order

/-- A language is ordered if it has a symbol representing `≤`. -/
class IsOrdered (L : Language.{u, v}) where
  leSymb : L.Relations 2

export IsOrdered (leSymb)

section IsOrdered

variable [IsOrdered L]

/-- Joins two terms `t₁, t₂` in a formula representing `t₁ ≤ t₂`. -/
def Term.le (t₁ t₂ : L.Term (Sum α (Finₓ n))) : L.BoundedFormula α n :=
  leSymb.boundedFormula₂ t₁ t₂

/-- Joins two terms `t₁, t₂` in a formula representing `t₁ < t₂`. -/
def Term.lt (t₁ t₂ : L.Term (Sum α (Finₓ n))) : L.BoundedFormula α n :=
  t₁.le t₂⊓∼(t₂.le t₁)

variable (L)

/-- The language homomorphism sending the unique symbol `≤` of `language.order` to `≤` in an ordered
 language. -/
def orderLhom : language.order →ᴸ L :=
  Lhom.mk₂ Empty.elim Empty.elim Empty.elim Empty.elim fun _ => leSymb

end IsOrdered

instance : IsOrdered Language.order :=
  ⟨Unit.star⟩

@[simp]
theorem order_Lhom_le_symb [L.IsOrdered] : (orderLhom L).onRelation leSymb = (leSymb : L.Relations 2) :=
  rfl

@[simp]
theorem order_Lhom_order : orderLhom Language.order = Lhom.id Language.order :=
  Lhom.funext (Subsingleton.elimₓ _ _) (Subsingleton.elimₓ _ _)

instance : IsOrdered (L.Sum Language.order) :=
  ⟨Sum.inr IsOrdered.leSymb⟩

/-- The theory of preorders. -/
protected def Theory.Preorder : Language.order.Theory :=
  {leSymb.Reflexive, leSymb.Transitive}

/-- The theory of partial orders. -/
protected def Theory.PartialOrder : Language.order.Theory :=
  {leSymb.Reflexive, leSymb.antisymmetric, leSymb.Transitive}

/-- The theory of linear orders. -/
protected def Theory.LinearOrder : Language.order.Theory :=
  {leSymb.Reflexive, leSymb.antisymmetric, leSymb.Transitive, leSymb.Total}

/-- A sentence indicating that an order has no top element:
$\forall x, \exists y, \neg y \le x$.   -/
protected def Sentence.noTopOrder : Language.order.Sentence :=
  ∀'∃'∼((&1).le &0)

/-- A sentence indicating that an order has no bottom element:
$\forall x, \exists y, \neg x \le y$. -/
protected def Sentence.noBotOrder : Language.order.Sentence :=
  ∀'∃'∼((&0).le &1)

/-- A sentence indicating that an order is dense:
$\forall x, \forall y, x < y \to \exists z, x < z \wedge z < y$. -/
protected def Sentence.denselyOrdered : Language.order.Sentence :=
  ∀'∀'((&0).lt &1 ⟹ ∃'((&0).lt &2⊓(&2).lt &1))

/-- The theory of dense linear orders without endpoints. -/
protected def Theory.DLO : Language.order.Theory :=
  Theory.linear_order ∪ {Sentence.noTopOrder, Sentence.noBotOrder, Sentence.denselyOrdered}

variable (L M)

/-- A structure is ordered if its language has a `≤` symbol whose interpretation is -/
abbrev IsOrderedStructure [IsOrdered L] [LE M] [L.Structure M] : Prop :=
  Lhom.IsExpansionOn (orderLhom L) M

variable {L M}

@[simp]
theorem is_ordered_structure_iff [IsOrdered L] [LE M] [L.Structure M] :
    L.IsOrderedStructure M ↔ Lhom.IsExpansionOn (orderLhom L) M :=
  Iff.rfl

instance is_ordered_structure_has_le [LE M] : IsOrderedStructure Language.order M := by
  rw [is_ordered_structure_iff, order_Lhom_order]
  exact Lhom.id_is_expansion_on M

instance model_preorder [Preorderₓ M] : M ⊨ Theory.preorder := by
  simp only [← Theory.preorder, ← Theory.model_iff, ← Set.mem_insert_iff, ← Set.mem_singleton_iff, ← forall_eq_or_imp, ←
    relations.realize_reflexive, ← rel_map_apply₂, ← forall_eq, ← relations.realize_transitive]
  exact ⟨le_reflₓ, fun _ _ _ => le_transₓ⟩

instance model_partial_order [PartialOrderₓ M] : M ⊨ Theory.partial_order := by
  simp only [← Theory.partial_order, ← Theory.model_iff, ← Set.mem_insert_iff, ← Set.mem_singleton_iff, ←
    forall_eq_or_imp, ← relations.realize_reflexive, ← rel_map_apply₂, ← relations.realize_antisymmetric, ← forall_eq, ←
    relations.realize_transitive]
  exact ⟨le_reflₓ, fun _ _ => le_antisymmₓ, fun _ _ _ => le_transₓ⟩

instance model_linear_order [LinearOrderₓ M] : M ⊨ Theory.linear_order := by
  simp only [← Theory.linear_order, ← Theory.model_iff, ← Set.mem_insert_iff, ← Set.mem_singleton_iff, ←
    forall_eq_or_imp, ← relations.realize_reflexive, ← rel_map_apply₂, ← relations.realize_antisymmetric, ←
    relations.realize_transitive, ← forall_eq, ← relations.realize_total]
  exact ⟨le_reflₓ, fun _ _ => le_antisymmₓ, fun _ _ _ => le_transₓ, le_totalₓ⟩

section IsOrderedStructure

variable [IsOrdered L] [L.Structure M]

@[simp]
theorem rel_map_le_symb [LE M] [L.IsOrderedStructure M] {a b : M} : RelMap (leSymb : L.Relations 2) ![a, b] ↔ a ≤ b :=
  by
  rw [← order_Lhom_le_symb, Lhom.is_expansion_on.map_on_relation]
  rfl

@[simp]
theorem Term.realize_le [LE M] [L.IsOrderedStructure M] {t₁ t₂ : L.Term (Sum α (Finₓ n))} {v : α → M}
    {xs : Finₓ n → M} : (t₁.le t₂).realize v xs ↔ t₁.realize (Sum.elim v xs) ≤ t₂.realize (Sum.elim v xs) := by
  simp [← term.le]

@[simp]
theorem Term.realize_lt [Preorderₓ M] [L.IsOrderedStructure M] {t₁ t₂ : L.Term (Sum α (Finₓ n))} {v : α → M}
    {xs : Finₓ n → M} : (t₁.lt t₂).realize v xs ↔ t₁.realize (Sum.elim v xs) < t₂.realize (Sum.elim v xs) := by
  simp [← term.lt, ← lt_iff_le_not_leₓ]

end IsOrderedStructure

section LE

variable [LE M]

theorem realize_no_top_order_iff : M ⊨ sentence.no_top_order ↔ NoTopOrder M := by
  simp only [← sentence.no_top_order, ← sentence.realize, ← formula.realize, ← bounded_formula.realize_all, ←
    bounded_formula.realize_ex, ← bounded_formula.realize_not, ← realize, ← term.realize_le, ← Sum.elim_inr]
  refine' ⟨fun h => ⟨fun a => h a⟩, _⟩
  intro h a
  exact exists_not_le a

@[simp]
theorem realize_no_top_order [h : NoTopOrder M] : M ⊨ sentence.no_top_order :=
  realize_no_top_order_iff.2 h

theorem realize_no_bot_order_iff : M ⊨ sentence.no_bot_order ↔ NoBotOrder M := by
  simp only [← sentence.no_bot_order, ← sentence.realize, ← formula.realize, ← bounded_formula.realize_all, ←
    bounded_formula.realize_ex, ← bounded_formula.realize_not, ← realize, ← term.realize_le, ← Sum.elim_inr]
  refine' ⟨fun h => ⟨fun a => h a⟩, _⟩
  intro h a
  exact exists_not_ge a

@[simp]
theorem realize_no_bot_order [h : NoBotOrder M] : M ⊨ sentence.no_bot_order :=
  realize_no_bot_order_iff.2 h

end LE

theorem realize_densely_ordered_iff [Preorderₓ M] : M ⊨ sentence.densely_ordered ↔ DenselyOrdered M := by
  simp only [← sentence.densely_ordered, ← sentence.realize, ← formula.realize, ← bounded_formula.realize_imp, ←
    bounded_formula.realize_all, ← realize, ← term.realize_lt, ← Sum.elim_inr, ← bounded_formula.realize_ex, ←
    bounded_formula.realize_inf]
  refine' ⟨fun h => ⟨fun a b ab => h a b ab⟩, _⟩
  intro h a b ab
  exact exists_between ab

@[simp]
theorem realize_densely_ordered [Preorderₓ M] [h : DenselyOrdered M] : M ⊨ sentence.densely_ordered :=
  realize_densely_ordered_iff.2 h

instance model_DLO [LinearOrderₓ M] [DenselyOrdered M] [NoTopOrder M] [NoBotOrder M] : M ⊨ Theory.DLO := by
  simp only [← Theory.DLO, ← Set.union_insert, ← Set.union_singleton, ← Theory.model_iff, ← Set.mem_insert_iff, ←
    forall_eq_or_imp, ← realize_no_top_order, ← realize_no_bot_order, ← realize_densely_ordered, ← true_andₓ]
  rw [← Theory.model_iff]
  infer_instance

end Language

end FirstOrder

