/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathbin.Data.Set.Basic
import Mathbin.Order.Lattice
import Mathbin.Order.Max

/-!
# Directed indexed families and sets

This file defines directed indexed families and directed sets. An indexed family/set is
directed iff each pair of elements has a shared upper bound.

## Main declarations

* `directed r f`: Predicate stating that the indexed family `f` is `r`-directed.
* `directed_on r s`: Predicate stating that the set `s` is `r`-directed.
* `is_directed α r`: Prop-valued mixin stating that `α` is `r`-directed. Follows the style of the
  unbundled relation classes such as `is_total`.
-/


open Function

universe u v w

variable {α : Type u} {β : Type v} {ι : Sort w} (r s : α → α → Prop)

-- mathport name: «expr ≼ »
local infixl:50 " ≼ " => r

/-- A family of elements of α is directed (with respect to a relation `≼` on α)
  if there is a member of the family `≼`-above any pair in the family.  -/
def Directed (f : ι → α) :=
  ∀ x y, ∃ z, f x ≼ f z ∧ f y ≼ f z

/-- A subset of α is directed if there is an element of the set `≼`-above any
  pair of elements in the set. -/
def DirectedOn (s : Set α) :=
  ∀, ∀ x ∈ s, ∀, ∀ y ∈ s, ∀, ∃ z ∈ s, x ≼ z ∧ y ≼ z

variable {r}

theorem directed_on_iff_directed {s} : @DirectedOn α r s ↔ Directed r (coe : s → α) := by
  simp [← Directed, ← DirectedOn] <;>
    refine'
      ball_congr fun x hx => by
        simp <;> rfl

alias directed_on_iff_directed ↔ DirectedOn.directed_coe _

theorem directed_on_image {s} {f : β → α} : DirectedOn r (f '' s) ↔ DirectedOn (f ⁻¹'o r) s := by
  simp only [← DirectedOn, ← Set.ball_image_iff, ← Set.bex_image_iff, ← Order.Preimage]

theorem DirectedOn.mono {s : Set α} (h : DirectedOn r s) {r' : α → α → Prop} (H : ∀ {a b}, r a b → r' a b) :
    DirectedOn r' s := fun x hx y hy =>
  let ⟨z, zs, xz, yz⟩ := h x hx y hy
  ⟨z, zs, H xz, H yz⟩

theorem directed_comp {ι} {f : ι → β} {g : β → α} : Directed r (g ∘ f) ↔ Directed (g ⁻¹'o r) f :=
  Iff.rfl

theorem Directed.mono {s : α → α → Prop} {ι} {f : ι → α} (H : ∀ a b, r a b → s a b) (h : Directed r f) : Directed s f :=
  fun a b =>
  let ⟨c, h₁, h₂⟩ := h a b
  ⟨c, H _ _ h₁, H _ _ h₂⟩

theorem Directed.mono_comp {ι} {rb : β → β → Prop} {g : α → β} {f : ι → α} (hg : ∀ ⦃x y⦄, x ≼ y → rb (g x) (g y))
    (hf : Directed r f) : Directed rb (g ∘ f) :=
  directed_comp.2 <| hf.mono hg

/-- A monotone function on a sup-semilattice is directed. -/
theorem directed_of_sup [SemilatticeSup α] {f : α → β} {r : β → β → Prop} (H : ∀ ⦃i j⦄, i ≤ j → r (f i) (f j)) :
    Directed r f := fun a b => ⟨a⊔b, H le_sup_left, H le_sup_right⟩

theorem Monotone.directed_le [SemilatticeSup α] [Preorderₓ β] {f : α → β} : Monotone f → Directed (· ≤ ·) f :=
  directed_of_sup

theorem Directed.extend_bot [Preorderₓ α] [OrderBot α] {e : ι → β} {f : ι → α} (hf : Directed (· ≤ ·) f)
    (he : Function.Injective e) : Directed (· ≤ ·) (Function.extendₓ e f ⊥) := by
  intro a b
  rcases(em (∃ i, e i = a)).symm with (ha | ⟨i, rfl⟩)
  · use b
    simp [← Function.extend_apply' _ _ _ ha]
    
  rcases(em (∃ i, e i = b)).symm with (hb | ⟨j, rfl⟩)
  · use e i
    simp [← Function.extend_apply' _ _ _ hb]
    
  rcases hf i j with ⟨k, hi, hj⟩
  use e k
  simp only [← Function.extend_applyₓ he, *, ← true_andₓ]

/-- An antitone function on an inf-semilattice is directed. -/
theorem directed_of_inf [SemilatticeInf α] {r : β → β → Prop} {f : α → β} (hf : ∀ a₁ a₂, a₁ ≤ a₂ → r (f a₂) (f a₁)) :
    Directed r f := fun x y => ⟨x⊓y, hf _ _ inf_le_left, hf _ _ inf_le_right⟩

/-- `is_directed α r` states that for any elements `a`, `b` there exists an element `c` such that
`r a c` and `r b c`. -/
class IsDirected (α : Type _) (r : α → α → Prop) : Prop where
  Directed (a b : α) : ∃ c, r a c ∧ r b c

theorem directed_of (r : α → α → Prop) [IsDirected α r] (a b : α) : ∃ c, r a c ∧ r b c :=
  IsDirected.directed _ _

theorem directed_id [IsDirected α r] : Directed r id := by
  convert directed_of r

theorem directed_id_iff : Directed r id ↔ IsDirected α r :=
  ⟨fun h => ⟨h⟩, @directed_id _ _⟩

theorem directed_on_univ [IsDirected α r] : DirectedOn r Set.Univ := fun a _ b _ =>
  let ⟨c, hc⟩ := directed_of r a b
  ⟨c, trivialₓ, hc⟩

theorem directed_on_univ_iff : DirectedOn r Set.Univ ↔ IsDirected α r :=
  ⟨fun h =>
    ⟨fun a b =>
      let ⟨c, _, hc⟩ := h a trivialₓ b trivialₓ
      ⟨c, hc⟩⟩,
    @directed_on_univ _ _⟩

-- see Note [lower instance priority]
instance (priority := 100) IsTotal.to_is_directed [IsTotal α r] : IsDirected α r :=
  ⟨fun a b => Or.cases_on (total_of r a b) (fun h => ⟨b, h, refl _⟩) fun h => ⟨a, refl _, h⟩⟩

theorem is_directed_mono [IsDirected α r] (h : ∀ ⦃a b⦄, r a b → s a b) : IsDirected α s :=
  ⟨fun a b =>
    let ⟨c, ha, hb⟩ := IsDirected.directed a b
    ⟨c, h ha, h hb⟩⟩

theorem exists_ge_ge [LE α] [IsDirected α (· ≤ ·)] (a b : α) : ∃ c, a ≤ c ∧ b ≤ c :=
  directed_of (· ≤ ·) a b

theorem exists_le_le [LE α] [IsDirected α (· ≥ ·)] (a b : α) : ∃ c, c ≤ a ∧ c ≤ b :=
  directed_of (· ≥ ·) a b

instance OrderDual.is_directed_ge [LE α] [IsDirected α (· ≤ ·)] : IsDirected αᵒᵈ (· ≥ ·) := by
  assumption

instance OrderDual.is_directed_le [LE α] [IsDirected α (· ≥ ·)] : IsDirected αᵒᵈ (· ≤ ·) := by
  assumption

section Preorderₓ

variable [Preorderₓ α] {a : α}

protected theorem IsMin.is_bot [IsDirected α (· ≥ ·)] (h : IsMin a) : IsBot a := fun b =>
  let ⟨c, hca, hcb⟩ := exists_le_le a b
  (h hca).trans hcb

protected theorem IsMax.is_top [IsDirected α (· ≤ ·)] (h : IsMax a) : IsTop a :=
  h.toDual.IsBot

theorem is_top_or_exists_gt [IsDirected α (· ≤ ·)] (a : α) : IsTop a ∨ ∃ b, a < b :=
  (em (IsMax a)).imp IsMax.is_top not_is_max_iff.mp

theorem is_bot_or_exists_lt [IsDirected α (· ≥ ·)] (a : α) : IsBot a ∨ ∃ b, b < a :=
  @is_top_or_exists_gt αᵒᵈ _ _ a

theorem is_bot_iff_is_min [IsDirected α (· ≥ ·)] : IsBot a ↔ IsMin a :=
  ⟨IsBot.is_min, IsMin.is_bot⟩

theorem is_top_iff_is_max [IsDirected α (· ≤ ·)] : IsTop a ↔ IsMax a :=
  ⟨IsTop.is_max, IsMax.is_top⟩

variable (β) [PartialOrderₓ β]

theorem exists_lt_of_directed_ge [IsDirected β (· ≥ ·)] [Nontrivial β] : ∃ a b : β, a < b := by
  rcases exists_pair_ne β with ⟨a, b, hne⟩
  rcases is_bot_or_exists_lt a with (ha | ⟨c, hc⟩)
  exacts[⟨a, b, (ha b).lt_of_ne hne⟩, ⟨_, _, hc⟩]

theorem exists_lt_of_directed_le [IsDirected β (· ≤ ·)] [Nontrivial β] : ∃ a b : β, a < b :=
  let ⟨a, b, h⟩ := exists_lt_of_directed_ge βᵒᵈ
  ⟨b, a, h⟩

end Preorderₓ

-- see Note [lower instance priority]
instance (priority := 100) SemilatticeSup.to_is_directed_le [SemilatticeSup α] : IsDirected α (· ≤ ·) :=
  ⟨fun a b => ⟨a⊔b, le_sup_left, le_sup_right⟩⟩

-- see Note [lower instance priority]
instance (priority := 100) SemilatticeInf.to_is_directed_ge [SemilatticeInf α] : IsDirected α (· ≥ ·) :=
  ⟨fun a b => ⟨a⊓b, inf_le_left, inf_le_right⟩⟩

-- see Note [lower instance priority]
instance (priority := 100) OrderTop.to_is_directed_le [LE α] [OrderTop α] : IsDirected α (· ≤ ·) :=
  ⟨fun a b => ⟨⊤, le_top, le_top⟩⟩

-- see Note [lower instance priority]
instance (priority := 100) OrderBot.to_is_directed_ge [LE α] [OrderBot α] : IsDirected α (· ≥ ·) :=
  ⟨fun a b => ⟨⊥, bot_le, bot_le⟩⟩

