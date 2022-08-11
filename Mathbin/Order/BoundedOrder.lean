/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathbin.Data.Option.Basic
import Mathbin.Logic.Nontrivial
import Mathbin.Order.Lattice
import Mathbin.Order.Max
import Mathbin.Tactic.PiInstances

/-!
# ⊤ and ⊥, bounded lattices and variants

This file defines top and bottom elements (greatest and least elements) of a type, the bounded
variants of different kinds of lattices, sets up the typeclass hierarchy between them and provides
instances for `Prop` and `fun`.

## Main declarations

* `has_<top/bot> α`: Typeclasses to declare the `⊤`/`⊥` notation.
* `order_<top/bot> α`: Order with a top/bottom element.
* `bounded_order α`: Order with a top and bottom element.
* `with_<top/bot> α`: Equips `option α` with the order on `α` plus `none` as the top/bottom element.
* `is_compl x y`: In a bounded lattice, predicate for "`x` is a complement of `y`". Note that in a
  non distributive lattice, an element can have several complements.
* `is_complemented α`: Typeclass stating that any element of a lattice has a complement.

## Common lattices

* Distributive lattices with a bottom element. Notated by `[distrib_lattice α] [order_bot α]`
  It captures the properties of `disjoint` that are common to `generalized_boolean_algebra` and
  `distrib_lattice` when `order_bot`.
* Bounded and distributive lattice. Notated by `[distrib_lattice α] [bounded_order α]`.
  Typical examples include `Prop` and `set α`.
-/


open OrderDual

universe u v

variable {α : Type u} {β : Type v}

/-! ### Top, bottom element -/


-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:51:50: missing argument
-- ./././Mathport/Syntax/Translate/Basic.lean:1209:19: in notation_class: ./././Mathport/Syntax/Translate/Tactic/Basic.lean:54:35: expecting parse arg
/-- Typeclass for the `⊤` (`\top`) notation -/
@[«./././Mathport/Syntax/Translate/Basic.lean:1209:19: in notation_class: ./././Mathport/Syntax/Translate/Tactic/Basic.lean:54:35: expecting parse arg»]
class HasTop (α : Type u) where
  top : α

-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:51:50: missing argument
-- ./././Mathport/Syntax/Translate/Basic.lean:1209:19: in notation_class: ./././Mathport/Syntax/Translate/Tactic/Basic.lean:54:35: expecting parse arg
/-- Typeclass for the `⊥` (`\bot`) notation -/
@[«./././Mathport/Syntax/Translate/Basic.lean:1209:19: in notation_class: ./././Mathport/Syntax/Translate/Tactic/Basic.lean:54:35: expecting parse arg»]
class HasBot (α : Type u) where
  bot : α

-- mathport name: «expr⊤»
notation "⊤" => HasTop.top

-- mathport name: «expr⊥»
notation "⊥" => HasBot.bot

instance (priority := 100) has_top_nonempty (α : Type u) [HasTop α] : Nonempty α :=
  ⟨⊤⟩

instance (priority := 100) has_bot_nonempty (α : Type u) [HasBot α] : Nonempty α :=
  ⟨⊥⟩

attribute [matchPattern] HasBot.bot HasTop.top

/-- An order is an `order_top` if it has a greatest element.
We state this using a data mixin, holding the value of `⊤` and the greatest element constraint. -/
@[ancestor HasTop]
class OrderTop (α : Type u) [LE α] extends HasTop α where
  le_top : ∀ a : α, a ≤ ⊤

section OrderTop

section LE

variable [LE α] [OrderTop α] {a : α}

@[simp]
theorem le_top : a ≤ ⊤ :=
  OrderTop.le_top a

@[simp]
theorem is_top_top : IsTop (⊤ : α) := fun _ => le_top

end LE

section Preorderₓ

variable [Preorderₓ α] [OrderTop α] {a b : α}

@[simp]
theorem is_max_top : IsMax (⊤ : α) :=
  is_top_top.IsMax

@[simp]
theorem not_top_lt : ¬⊤ < a :=
  is_max_top.not_lt

theorem ne_top_of_lt (h : a < b) : a ≠ ⊤ :=
  (h.trans_le le_top).Ne

alias ne_top_of_lt ← LT.lt.ne_top

end Preorderₓ

variable [PartialOrderₓ α] [OrderTop α] [Preorderₓ β] {f : α → β} {a b : α}

@[simp]
theorem is_max_iff_eq_top : IsMax a ↔ a = ⊤ :=
  ⟨fun h => h.eq_of_le le_top, fun h b _ => h.symm ▸ le_top⟩

@[simp]
theorem is_top_iff_eq_top : IsTop a ↔ a = ⊤ :=
  ⟨fun h => h.IsMax.eq_of_le le_top, fun h b => h.symm ▸ le_top⟩

theorem not_is_max_iff_ne_top : ¬IsMax a ↔ a ≠ ⊤ :=
  is_max_iff_eq_top.Not

theorem not_is_top_iff_ne_top : ¬IsTop a ↔ a ≠ ⊤ :=
  is_top_iff_eq_top.Not

alias is_max_iff_eq_top ↔ IsMax.eq_top _

alias is_top_iff_eq_top ↔ IsTop.eq_top _

@[simp]
theorem top_le_iff : ⊤ ≤ a ↔ a = ⊤ :=
  le_top.le_iff_eq.trans eq_comm

theorem top_unique (h : ⊤ ≤ a) : a = ⊤ :=
  le_top.antisymm h

theorem eq_top_iff : a = ⊤ ↔ ⊤ ≤ a :=
  top_le_iff.symm

theorem eq_top_mono (h : a ≤ b) (h₂ : a = ⊤) : b = ⊤ :=
  top_unique <| h₂ ▸ h

theorem lt_top_iff_ne_top : a < ⊤ ↔ a ≠ ⊤ :=
  le_top.lt_iff_ne

@[simp]
theorem not_lt_top_iff : ¬a < ⊤ ↔ a = ⊤ :=
  lt_top_iff_ne_top.not_left

theorem eq_top_or_lt_top (a : α) : a = ⊤ ∨ a < ⊤ :=
  le_top.eq_or_lt

theorem Ne.lt_top (h : a ≠ ⊤) : a < ⊤ :=
  lt_top_iff_ne_top.mpr h

theorem Ne.lt_top' (h : ⊤ ≠ a) : a < ⊤ :=
  h.symm.lt_top

theorem ne_top_of_le_ne_top (hb : b ≠ ⊤) (hab : a ≤ b) : a ≠ ⊤ :=
  (hab.trans_lt hb.lt_top).Ne

theorem StrictMono.apply_eq_top_iff (hf : StrictMono f) : f a = f ⊤ ↔ a = ⊤ :=
  ⟨fun h => not_lt_top_iff.1 fun ha => (hf ha).Ne h, congr_arg _⟩

theorem StrictAnti.apply_eq_top_iff (hf : StrictAnti f) : f a = f ⊤ ↔ a = ⊤ :=
  ⟨fun h => not_lt_top_iff.1 fun ha => (hf ha).ne' h, congr_arg _⟩

variable [Nontrivial α]

theorem not_is_min_top : ¬IsMin (⊤ : α) := fun h =>
  let ⟨a, ha⟩ := exists_ne (⊤ : α)
  ha <| top_le_iff.1 <| h le_top

end OrderTop

theorem StrictMono.maximal_preimage_top [LinearOrderₓ α] [Preorderₓ β] [OrderTop β] {f : α → β} (H : StrictMono f) {a}
    (h_top : f a = ⊤) (x : α) : x ≤ a :=
  H.maximal_of_maximal_image
    (fun p => by
      rw [h_top]
      exact le_top)
    x

theorem OrderTop.ext_top {α} {hA : PartialOrderₓ α} (A : OrderTop α) {hB : PartialOrderₓ α} (B : OrderTop α)
    (H :
      ∀ x y : α,
        (have := hA
          x ≤ y) ↔
          x ≤ y) :
    (have := A
      ⊤ :
        α) =
      ⊤ :=
  top_unique <| by
    rw [← H] <;> apply le_top

theorem OrderTop.ext {α} [PartialOrderₓ α] {A B : OrderTop α} : A = B := by
  have tt := OrderTop.ext_top A B fun _ _ => Iff.rfl
  cases' A with _ ha
  cases' B with _ hb
  congr
  exact le_antisymmₓ (hb _) (ha _)

/-- An order is an `order_bot` if it has a least element.
We state this using a data mixin, holding the value of `⊥` and the least element constraint. -/
@[ancestor HasBot]
class OrderBot (α : Type u) [LE α] extends HasBot α where
  bot_le : ∀ a : α, ⊥ ≤ a

section OrderBot

section LE

variable [LE α] [OrderBot α] {a : α}

@[simp]
theorem bot_le : ⊥ ≤ a :=
  OrderBot.bot_le a

@[simp]
theorem is_bot_bot : IsBot (⊥ : α) := fun _ => bot_le

end LE

namespace OrderDual

variable (α)

instance [HasBot α] : HasTop αᵒᵈ :=
  ⟨(⊥ : α)⟩

instance [HasTop α] : HasBot αᵒᵈ :=
  ⟨(⊤ : α)⟩

instance [LE α] [OrderBot α] : OrderTop αᵒᵈ :=
  { OrderDual.hasTop α with le_top := @bot_le α _ _ }

instance [LE α] [OrderTop α] : OrderBot αᵒᵈ :=
  { OrderDual.hasBot α with bot_le := @le_top α _ _ }

@[simp]
theorem of_dual_bot [HasTop α] : ofDual ⊥ = (⊤ : α) :=
  rfl

@[simp]
theorem of_dual_top [HasBot α] : ofDual ⊤ = (⊥ : α) :=
  rfl

@[simp]
theorem to_dual_bot [HasBot α] : toDual (⊥ : α) = ⊤ :=
  rfl

@[simp]
theorem to_dual_top [HasTop α] : toDual (⊤ : α) = ⊥ :=
  rfl

end OrderDual

section Preorderₓ

variable [Preorderₓ α] [OrderBot α] {a b : α}

@[simp]
theorem is_min_bot : IsMin (⊥ : α) :=
  is_bot_bot.IsMin

@[simp]
theorem not_lt_bot : ¬a < ⊥ :=
  is_min_bot.not_lt

theorem ne_bot_of_gt (h : a < b) : b ≠ ⊥ :=
  (bot_le.trans_lt h).ne'

alias ne_bot_of_gt ← LT.lt.ne_bot

end Preorderₓ

variable [PartialOrderₓ α] [OrderBot α] [Preorderₓ β] {f : α → β} {a b : α}

@[simp]
theorem is_min_iff_eq_bot : IsMin a ↔ a = ⊥ :=
  ⟨fun h => h.eq_of_ge bot_le, fun h b _ => h.symm ▸ bot_le⟩

@[simp]
theorem is_bot_iff_eq_bot : IsBot a ↔ a = ⊥ :=
  ⟨fun h => h.IsMin.eq_of_ge bot_le, fun h b => h.symm ▸ bot_le⟩

theorem not_is_min_iff_ne_bot : ¬IsMin a ↔ a ≠ ⊥ :=
  is_min_iff_eq_bot.Not

theorem not_is_bot_iff_ne_bot : ¬IsBot a ↔ a ≠ ⊥ :=
  is_bot_iff_eq_bot.Not

alias is_min_iff_eq_bot ↔ IsMin.eq_bot _

alias is_bot_iff_eq_bot ↔ IsBot.eq_bot _

@[simp]
theorem le_bot_iff : a ≤ ⊥ ↔ a = ⊥ :=
  bot_le.le_iff_eq

theorem bot_unique (h : a ≤ ⊥) : a = ⊥ :=
  h.antisymm bot_le

theorem eq_bot_iff : a = ⊥ ↔ a ≤ ⊥ :=
  le_bot_iff.symm

theorem eq_bot_mono (h : a ≤ b) (h₂ : b = ⊥) : a = ⊥ :=
  bot_unique <| h₂ ▸ h

theorem bot_lt_iff_ne_bot : ⊥ < a ↔ a ≠ ⊥ :=
  bot_le.lt_iff_ne.trans ne_comm

@[simp]
theorem not_bot_lt_iff : ¬⊥ < a ↔ a = ⊥ :=
  bot_lt_iff_ne_bot.not_left

theorem eq_bot_or_bot_lt (a : α) : a = ⊥ ∨ ⊥ < a :=
  bot_le.eq_or_gt

theorem eq_bot_of_minimal (h : ∀ b, ¬b < a) : a = ⊥ :=
  (eq_bot_or_bot_lt a).resolve_right (h ⊥)

theorem Ne.bot_lt (h : a ≠ ⊥) : ⊥ < a :=
  bot_lt_iff_ne_bot.mpr h

theorem Ne.bot_lt' (h : ⊥ ≠ a) : ⊥ < a :=
  h.symm.bot_lt

theorem ne_bot_of_le_ne_bot (hb : b ≠ ⊥) (hab : b ≤ a) : a ≠ ⊥ :=
  (hb.bot_lt.trans_le hab).ne'

theorem StrictMono.apply_eq_bot_iff (hf : StrictMono f) : f a = f ⊥ ↔ a = ⊥ :=
  hf.dual.apply_eq_top_iff

theorem StrictAnti.apply_eq_bot_iff (hf : StrictAnti f) : f a = f ⊥ ↔ a = ⊥ :=
  hf.dual.apply_eq_top_iff

variable [Nontrivial α]

theorem not_is_max_bot : ¬IsMax (⊥ : α) :=
  @not_is_min_top αᵒᵈ _ _ _

end OrderBot

theorem StrictMono.minimal_preimage_bot [LinearOrderₓ α] [PartialOrderₓ β] [OrderBot β] {f : α → β} (H : StrictMono f)
    {a} (h_bot : f a = ⊥) (x : α) : a ≤ x :=
  H.minimal_of_minimal_image
    (fun p => by
      rw [h_bot]
      exact bot_le)
    x

theorem OrderBot.ext_bot {α} {hA : PartialOrderₓ α} (A : OrderBot α) {hB : PartialOrderₓ α} (B : OrderBot α)
    (H :
      ∀ x y : α,
        (have := hA
          x ≤ y) ↔
          x ≤ y) :
    (have := A
      ⊥ :
        α) =
      ⊥ :=
  bot_unique <| by
    rw [← H] <;> apply bot_le

theorem OrderBot.ext {α} [PartialOrderₓ α] {A B : OrderBot α} : A = B := by
  have tt := OrderBot.ext_bot A B fun _ _ => Iff.rfl
  cases' A with a ha
  cases' B with b hb
  congr
  exact le_antisymmₓ (ha _) (hb _)

section SemilatticeSupTop

variable [SemilatticeSup α] [OrderTop α] {a : α}

@[simp]
theorem top_sup_eq : ⊤⊔a = ⊤ :=
  sup_of_le_left le_top

@[simp]
theorem sup_top_eq : a⊔⊤ = ⊤ :=
  sup_of_le_right le_top

end SemilatticeSupTop

section SemilatticeSupBot

variable [SemilatticeSup α] [OrderBot α] {a b : α}

@[simp]
theorem bot_sup_eq : ⊥⊔a = a :=
  sup_of_le_right bot_le

@[simp]
theorem sup_bot_eq : a⊔⊥ = a :=
  sup_of_le_left bot_le

@[simp]
theorem sup_eq_bot_iff : a⊔b = ⊥ ↔ a = ⊥ ∧ b = ⊥ := by
  rw [eq_bot_iff, sup_le_iff] <;> simp

end SemilatticeSupBot

section SemilatticeInfTop

variable [SemilatticeInf α] [OrderTop α] {a b : α}

@[simp]
theorem top_inf_eq : ⊤⊓a = a :=
  inf_of_le_right le_top

@[simp]
theorem inf_top_eq : a⊓⊤ = a :=
  inf_of_le_left le_top

@[simp]
theorem inf_eq_top_iff : a⊓b = ⊤ ↔ a = ⊤ ∧ b = ⊤ :=
  @sup_eq_bot_iff αᵒᵈ _ _ _ _

end SemilatticeInfTop

section SemilatticeInfBot

variable [SemilatticeInf α] [OrderBot α] {a : α}

@[simp]
theorem bot_inf_eq : ⊥⊓a = ⊥ :=
  inf_of_le_left bot_le

@[simp]
theorem inf_bot_eq : a⊓⊥ = ⊥ :=
  inf_of_le_right bot_le

end SemilatticeInfBot

/-! ### Bounded order -/


/-- A bounded order describes an order `(≤)` with a top and bottom element,
  denoted `⊤` and `⊥` respectively. -/
@[ancestor OrderTop OrderBot]
class BoundedOrder (α : Type u) [LE α] extends OrderTop α, OrderBot α

instance (α : Type u) [LE α] [BoundedOrder α] : BoundedOrder αᵒᵈ :=
  { OrderDual.orderTop α, OrderDual.orderBot α with }

theorem BoundedOrder.ext {α} [PartialOrderₓ α] {A B : BoundedOrder α} : A = B := by
  have ht : @BoundedOrder.toOrderTop α _ A = @BoundedOrder.toOrderTop α _ B := OrderTop.ext
  have hb : @BoundedOrder.toOrderBot α _ A = @BoundedOrder.toOrderBot α _ B := OrderBot.ext
  cases A
  cases B
  injection ht with h
  injection hb with h'
  convert rfl
  · exact h.symm
    
  · exact h'.symm
    

/-- Propositions form a distributive lattice. -/
instance Prop.distribLattice : DistribLattice Prop where
  le := fun a b => a → b
  le_refl := fun _ => id
  le_trans := fun a b c f g => g ∘ f
  le_antisymm := fun a b Hab Hba => propext ⟨Hab, Hba⟩
  sup := Or
  le_sup_left := @Or.inl
  le_sup_right := @Or.inr
  sup_le := fun a b c => Or.ndrec
  inf := And
  inf_le_left := @And.left
  inf_le_right := @And.right
  le_inf := fun a b c Hab Hac Ha => And.intro (Hab Ha) (Hac Ha)
  le_sup_inf := fun a b c H => or_iff_not_imp_left.2 fun Ha => ⟨H.1.resolve_left Ha, H.2.resolve_left Ha⟩

/-- Propositions form a bounded order. -/
instance Prop.boundedOrder : BoundedOrder Prop where
  top := True
  le_top := fun a Ha => True.intro
  bot := False
  bot_le := @False.elim

instance Prop.le_is_total : IsTotal Prop (· ≤ ·) :=
  ⟨fun p q => by
    change (p → q) ∨ (q → p)
    tauto!⟩

noncomputable instance Prop.linearOrder : LinearOrderₓ Prop := by
  classical <;> exact Lattice.toLinearOrder Prop

theorem subrelation_iff_le {r s : α → α → Prop} : Subrelation r s ↔ r ≤ s :=
  Iff.rfl

-- ./././Mathport/Syntax/Translate/Basic.lean:703:4: warning: unsupported binary notation `«->»
@[simp]
theorem le_Prop_eq : ((· ≤ ·) : Prop → Prop → Prop) = («->» · ·) :=
  rfl

@[simp]
theorem sup_Prop_eq : (·⊔·) = (· ∨ ·) :=
  rfl

@[simp]
theorem inf_Prop_eq : (·⊓·) = (· ∧ ·) :=
  rfl

section Logic

/-!
#### In this section we prove some properties about monotone and antitone operations on `Prop`
-/


section Preorderₓ

variable [Preorderₓ α]

theorem monotone_and {p q : α → Prop} (m_p : Monotone p) (m_q : Monotone q) : Monotone fun x => p x ∧ q x :=
  fun a b h => And.imp (m_p h) (m_q h)

-- Note: by finish [monotone] doesn't work
theorem monotone_or {p q : α → Prop} (m_p : Monotone p) (m_q : Monotone q) : Monotone fun x => p x ∨ q x := fun a b h =>
  Or.imp (m_p h) (m_q h)

theorem monotone_le {x : α} : Monotone ((· ≤ ·) x) := fun y z h' h => h.trans h'

theorem monotone_lt {x : α} : Monotone ((· < ·) x) := fun y z h' h => h.trans_le h'

theorem antitone_le {x : α} : Antitone (· ≤ x) := fun y z h' h => h'.trans h

theorem antitone_lt {x : α} : Antitone (· < x) := fun y z h' h => h'.trans_lt h

theorem Monotone.forall {P : β → α → Prop} (hP : ∀ x, Monotone (P x)) : Monotone fun y => ∀ x, P x y :=
  fun y y' hy h x => hP x hy <| h x

theorem Antitone.forall {P : β → α → Prop} (hP : ∀ x, Antitone (P x)) : Antitone fun y => ∀ x, P x y :=
  fun y y' hy h x => hP x hy (h x)

theorem Monotone.ball {P : β → α → Prop} {s : Set β} (hP : ∀, ∀ x ∈ s, ∀, Monotone (P x)) :
    Monotone fun y => ∀, ∀ x ∈ s, ∀, P x y := fun y y' hy h x hx => hP x hx hy (h x hx)

theorem Antitone.ball {P : β → α → Prop} {s : Set β} (hP : ∀, ∀ x ∈ s, ∀, Antitone (P x)) :
    Antitone fun y => ∀, ∀ x ∈ s, ∀, P x y := fun y y' hy h x hx => hP x hx hy (h x hx)

end Preorderₓ

section SemilatticeSup

variable [SemilatticeSup α]

theorem exists_ge_and_iff_exists {P : α → Prop} {x₀ : α} (hP : Monotone P) : (∃ x, x₀ ≤ x ∧ P x) ↔ ∃ x, P x :=
  ⟨fun h => h.imp fun x h => h.2, fun ⟨x, hx⟩ => ⟨x⊔x₀, le_sup_right, hP le_sup_left hx⟩⟩

end SemilatticeSup

section SemilatticeInf

variable [SemilatticeInf α]

theorem exists_le_and_iff_exists {P : α → Prop} {x₀ : α} (hP : Antitone P) : (∃ x, x ≤ x₀ ∧ P x) ↔ ∃ x, P x :=
  exists_ge_and_iff_exists hP.dual_left

end SemilatticeInf

end Logic

/-! ### Function lattices -/


namespace Pi

variable {ι : Type _} {α' : ι → Type _}

instance [∀ i, HasBot (α' i)] : HasBot (∀ i, α' i) :=
  ⟨fun i => ⊥⟩

@[simp]
theorem bot_apply [∀ i, HasBot (α' i)] (i : ι) : (⊥ : ∀ i, α' i) i = ⊥ :=
  rfl

theorem bot_def [∀ i, HasBot (α' i)] : (⊥ : ∀ i, α' i) = fun i => ⊥ :=
  rfl

instance [∀ i, HasTop (α' i)] : HasTop (∀ i, α' i) :=
  ⟨fun i => ⊤⟩

@[simp]
theorem top_apply [∀ i, HasTop (α' i)] (i : ι) : (⊤ : ∀ i, α' i) i = ⊤ :=
  rfl

theorem top_def [∀ i, HasTop (α' i)] : (⊤ : ∀ i, α' i) = fun i => ⊤ :=
  rfl

instance [∀ i, LE (α' i)] [∀ i, OrderTop (α' i)] : OrderTop (∀ i, α' i) :=
  { Pi.hasTop with le_top := fun _ _ => le_top }

instance [∀ i, LE (α' i)] [∀ i, OrderBot (α' i)] : OrderBot (∀ i, α' i) :=
  { Pi.hasBot with bot_le := fun _ _ => bot_le }

instance [∀ i, LE (α' i)] [∀ i, BoundedOrder (α' i)] : BoundedOrder (∀ i, α' i) :=
  { Pi.orderTop, Pi.orderBot with }

end Pi

section Subsingleton

variable [PartialOrderₓ α] [BoundedOrder α]

theorem eq_bot_of_bot_eq_top (hα : (⊥ : α) = ⊤) (x : α) : x = (⊥ : α) :=
  eq_bot_mono le_top (Eq.symm hα)

theorem eq_top_of_bot_eq_top (hα : (⊥ : α) = ⊤) (x : α) : x = (⊤ : α) :=
  eq_top_mono bot_le hα

theorem subsingleton_of_top_le_bot (h : (⊤ : α) ≤ (⊥ : α)) : Subsingleton α :=
  ⟨fun a b => le_antisymmₓ (le_transₓ le_top <| le_transₓ h bot_le) (le_transₓ le_top <| le_transₓ h bot_le)⟩

theorem subsingleton_of_bot_eq_top (hα : (⊥ : α) = (⊤ : α)) : Subsingleton α :=
  subsingleton_of_top_le_bot (ge_of_eq hα)

theorem subsingleton_iff_bot_eq_top : (⊥ : α) = (⊤ : α) ↔ Subsingleton α :=
  ⟨subsingleton_of_bot_eq_top, fun h => Subsingleton.elimₓ ⊥ ⊤⟩

end Subsingleton

section lift

/-- Pullback an `order_top`. -/
-- See note [reducible non-instances]
@[reducible]
def OrderTop.lift [LE α] [HasTop α] [LE β] [OrderTop β] (f : α → β) (map_le : ∀ a b, f a ≤ f b → a ≤ b)
    (map_top : f ⊤ = ⊤) : OrderTop α :=
  ⟨⊤, fun a =>
    map_le _ _ <| by
      rw [map_top]
      exact le_top⟩

/-- Pullback an `order_bot`. -/
-- See note [reducible non-instances]
@[reducible]
def OrderBot.lift [LE α] [HasBot α] [LE β] [OrderBot β] (f : α → β) (map_le : ∀ a b, f a ≤ f b → a ≤ b)
    (map_bot : f ⊥ = ⊥) : OrderBot α :=
  ⟨⊥, fun a =>
    map_le _ _ <| by
      rw [map_bot]
      exact bot_le⟩

/-- Pullback a `bounded_order`. -/
-- See note [reducible non-instances]
@[reducible]
def BoundedOrder.lift [LE α] [HasTop α] [HasBot α] [LE β] [BoundedOrder β] (f : α → β)
    (map_le : ∀ a b, f a ≤ f b → a ≤ b) (map_top : f ⊤ = ⊤) (map_bot : f ⊥ = ⊥) : BoundedOrder α :=
  { OrderTop.lift f map_le map_top, OrderBot.lift f map_le map_bot with }

end lift

/-! ### `with_bot`, `with_top` -/


/-- Attach `⊥` to a type. -/
def WithBot (α : Type _) :=
  Option α

namespace WithBot

variable {a b : α}

unsafe instance [has_to_format α] :
    has_to_format (WithBot α) where to_format := fun x =>
    match x with
    | none => "⊥"
    | some x => to_fmt x

instance [HasRepr α] : HasRepr (WithBot α) :=
  ⟨fun o =>
    match o with
    | none => "⊥"
    | some a => "↑" ++ reprₓ a⟩

instance : CoeTₓ α (WithBot α) :=
  ⟨some⟩

instance : HasBot (WithBot α) :=
  ⟨none⟩

unsafe instance {α : Type} [reflected _ α] [has_reflect α] : has_reflect (WithBot α)
  | ⊥ => quote.1 ⊥
  | (a : α) => (quote.1 (coe : α → WithBot α)).subst (quote.1 a)

instance : Inhabited (WithBot α) :=
  ⟨⊥⟩

theorem none_eq_bot : (none : WithBot α) = (⊥ : WithBot α) :=
  rfl

theorem some_eq_coe (a : α) : (some a : WithBot α) = (↑a : WithBot α) :=
  rfl

@[simp]
theorem bot_ne_coe : ⊥ ≠ (a : WithBot α) :=
  fun.

@[simp]
theorem coe_ne_bot : (a : WithBot α) ≠ ⊥ :=
  fun.

/-- Recursor for `with_bot` using the preferred forms `⊥` and `↑a`. -/
@[elab_as_eliminator]
def recBotCoe {C : WithBot α → Sort _} (h₁ : C ⊥) (h₂ : ∀ a : α, C a) : ∀ n : WithBot α, C n :=
  Option.rec h₁ h₂

@[simp]
theorem rec_bot_coe_bot {C : WithBot α → Sort _} (d : C ⊥) (f : ∀ a : α, C a) : @recBotCoe _ C d f ⊥ = d :=
  rfl

@[simp]
theorem rec_bot_coe_coe {C : WithBot α → Sort _} (d : C ⊥) (f : ∀ a : α, C a) (x : α) : @recBotCoe _ C d f ↑x = f x :=
  rfl

/-- Specialization of `option.get_or_else` to values in `with_bot α` that respects API boundaries.
-/
def unbot' (d : α) (x : WithBot α) : α :=
  recBotCoe d id x

@[simp]
theorem unbot'_bot {α} (d : α) : unbot' d ⊥ = d :=
  rfl

@[simp]
theorem unbot'_coe {α} (d x : α) : unbot' d x = x :=
  rfl

@[norm_cast]
theorem coe_eq_coe : (a : WithBot α) = b ↔ a = b :=
  Option.some_inj

/-- Lift a map `f : α → β` to `with_bot α → with_bot β`. Implemented using `option.map`. -/
def map (f : α → β) : WithBot α → WithBot β :=
  Option.map f

@[simp]
theorem map_bot (f : α → β) : map f ⊥ = ⊥ :=
  rfl

@[simp]
theorem map_coe (f : α → β) (a : α) : map f a = f a :=
  rfl

theorem ne_bot_iff_exists {x : WithBot α} : x ≠ ⊥ ↔ ∃ a : α, ↑a = x :=
  Option.ne_none_iff_exists

/-- Deconstruct a `x : with_bot α` to the underlying value in `α`, given a proof that `x ≠ ⊥`. -/
def unbot : ∀ x : WithBot α, x ≠ ⊥ → α
  | ⊥, h => absurd rfl h
  | some x, h => x

@[simp]
theorem coe_unbot (x : WithBot α) (h : x ≠ ⊥) : (x.unbot h : WithBot α) = x := by
  cases x
  simpa using h
  rfl

@[simp]
theorem unbot_coe (x : α) (h : (x : WithBot α) ≠ ⊥ := coe_ne_bot) : (x : WithBot α).unbot h = x :=
  rfl

instance : CanLift (WithBot α) α where
  coe := coe
  cond := fun r => r ≠ ⊥
  prf := fun x h => ⟨x.unbot h, coe_unbot _ _⟩

section LE

variable [LE α]

instance (priority := 10) : LE (WithBot α) :=
  ⟨fun o₁ o₂ : Option α => ∀, ∀ a ∈ o₁, ∀, ∃ b ∈ o₂, a ≤ b⟩

@[simp]
theorem some_le_some : @LE.le (WithBot α) _ (some a) (some b) ↔ a ≤ b := by
  simp [← (· ≤ ·)]

@[simp, norm_cast]
theorem coe_le_coe : (a : WithBot α) ≤ b ↔ a ≤ b :=
  some_le_some

@[simp]
theorem none_le {a : WithBot α} : @LE.le (WithBot α) _ none a := fun b h => Option.noConfusion h

instance : OrderBot (WithBot α) :=
  { WithBot.hasBot with bot_le := fun a => none_le }

instance [OrderTop α] : OrderTop (WithBot α) where
  top := some ⊤
  le_top := fun o a ha => by
    cases ha <;> exact ⟨_, rfl, le_top⟩

instance [OrderTop α] : BoundedOrder (WithBot α) :=
  { WithBot.orderTop, WithBot.orderBot with }

theorem not_coe_le_bot (a : α) : ¬(a : WithBot α) ≤ ⊥ := fun h =>
  let ⟨b, hb, _⟩ := h _ rfl
  Option.not_mem_none _ hb

theorem coe_le : ∀ {o : Option α}, b ∈ o → ((a : WithBot α) ≤ o ↔ a ≤ b)
  | _, rfl => coe_le_coe

theorem coe_le_iff : ∀ {x : WithBot α}, ↑a ≤ x ↔ ∃ b : α, x = b ∧ a ≤ b
  | some a => by
    simp [← some_eq_coe, ← coe_eq_coe]
  | none =>
    iff_of_false (not_coe_le_bot _) <| by
      simp [← none_eq_bot]

theorem le_coe_iff : ∀ {x : WithBot α}, x ≤ b ↔ ∀ a, x = ↑a → a ≤ b
  | some b => by
    simp [← some_eq_coe, ← coe_eq_coe]
  | none => by
    simp [← none_eq_bot]

protected theorem _root_.is_max.with_bot (h : IsMax a) : IsMax (a : WithBot α)
  | none, _ => bot_le
  | some b, hb => some_le_some.2 <| h <| some_le_some.1 hb

end LE

section LT

variable [LT α]

instance (priority := 10) : LT (WithBot α) :=
  ⟨fun o₁ o₂ : Option α => ∃ b ∈ o₂, ∀, ∀ a ∈ o₁, ∀, a < b⟩

@[simp]
theorem some_lt_some : @LT.lt (WithBot α) _ (some a) (some b) ↔ a < b := by
  simp [← (· < ·)]

@[simp, norm_cast]
theorem coe_lt_coe : (a : WithBot α) < b ↔ a < b :=
  some_lt_some

@[simp]
theorem none_lt_some (a : α) : @LT.lt (WithBot α) _ none (some a) :=
  ⟨a, rfl, fun b hb => (Option.not_mem_none _ hb).elim⟩

theorem bot_lt_coe (a : α) : (⊥ : WithBot α) < a :=
  none_lt_some a

@[simp]
theorem not_lt_none (a : WithBot α) : ¬@LT.lt (WithBot α) _ a none := fun ⟨_, h, _⟩ => Option.not_mem_none _ h

theorem lt_iff_exists_coe : ∀ {a b : WithBot α}, a < b ↔ ∃ p : α, b = p ∧ a < p
  | a, some b => by
    simp [← some_eq_coe, ← coe_eq_coe]
  | a, none =>
    iff_of_false (not_lt_none _) <| by
      simp [← none_eq_bot]

theorem lt_coe_iff : ∀ {x : WithBot α}, x < b ↔ ∀ a, x = ↑a → a < b
  | some b => by
    simp [← some_eq_coe, ← coe_eq_coe, ← coe_lt_coe]
  | none => by
    simp [← none_eq_bot, ← bot_lt_coe]

end LT

instance [Preorderₓ α] : Preorderₓ (WithBot α) where
  le := (· ≤ ·)
  lt := (· < ·)
  lt_iff_le_not_le := by
    intros
    cases a <;> cases b <;> simp [← lt_iff_le_not_leₓ] <;> simp [← (· < ·), ← (· ≤ ·)]
  le_refl := fun o a ha => ⟨a, ha, le_rfl⟩
  le_trans := fun o₁ o₂ o₃ h₁ h₂ a ha =>
    let ⟨b, hb, ab⟩ := h₁ a ha
    let ⟨c, hc, bc⟩ := h₂ b hb
    ⟨c, hc, le_transₓ ab bc⟩

instance [PartialOrderₓ α] : PartialOrderₓ (WithBot α) :=
  { WithBot.preorder with
    le_antisymm := fun o₁ o₂ h₁ h₂ => by
      cases' o₁ with a
      · cases' o₂ with b
        · rfl
          
        rcases h₂ b rfl with ⟨_, ⟨⟩, _⟩
        
      · rcases h₁ a rfl with ⟨b, ⟨⟩, h₁'⟩
        rcases h₂ b rfl with ⟨_, ⟨⟩, h₂'⟩
        rw [le_antisymmₓ h₁' h₂']
         }

theorem map_le_iff [Preorderₓ α] [Preorderₓ β] (f : α → β) (mono_iff : ∀ {a b}, f a ≤ f b ↔ a ≤ b) :
    ∀ a b : WithBot α, a.map f ≤ b.map f ↔ a ≤ b
  | ⊥, _ => by
    simp only [← map_bot, ← bot_le]
  | (a : α), ⊥ => by
    simp only [← map_coe, ← map_bot, ← coe_ne_bot, ← not_coe_le_bot _]
  | (a : α), (b : α) => by
    simpa using mono_iff

theorem le_coe_get_or_else [Preorderₓ α] : ∀ (a : WithBot α) (b : α), a ≤ a.getOrElse b
  | some a, b => le_reflₓ a
  | none, b => fun _ h => Option.noConfusion h

@[simp]
theorem get_or_else_bot (a : α) : Option.getOrElse (⊥ : WithBot α) a = a :=
  rfl

theorem get_or_else_bot_le_iff [LE α] [OrderBot α] {a : WithBot α} {b : α} : a.getOrElse ⊥ ≤ b ↔ a ≤ b := by
  cases a <;> simp [← none_eq_bot, ← some_eq_coe]

theorem get_or_else_bot_lt_iff [PartialOrderₓ α] [OrderBot α] {a : WithBot α} {b : α} (ha : a ≠ ⊥) :
    a.getOrElse ⊥ < b ↔ a < b := by
  obtain ⟨a, rfl⟩ := ne_bot_iff_exists.mp ha
  simp only [← lt_iff_le_and_ne, ← get_or_else_bot_le_iff, ← And.congr_right_iff]
  intro h
  apply Iff.not
  simp only [← WithBot.coe_eq_coe, ← Option.get_or_else_coe, ← iff_selfₓ]

instance [SemilatticeSup α] : SemilatticeSup (WithBot α) :=
  { WithBot.orderBot, WithBot.partialOrder with sup := Option.liftOrGet (·⊔·),
    le_sup_left := fun o₁ o₂ a ha => by
      cases ha <;> cases o₂ <;> simp [← Option.liftOrGet],
    le_sup_right := fun o₁ o₂ a ha => by
      cases ha <;> cases o₁ <;> simp [← Option.liftOrGet],
    sup_le := fun o₁ o₂ o₃ h₁ h₂ a ha => by
      cases' o₁ with b <;> cases' o₂ with c <;> cases ha
      · exact h₂ a rfl
        
      · exact h₁ a rfl
        
      · rcases h₁ b rfl with ⟨d, ⟨⟩, h₁'⟩
        simp at h₂
        exact ⟨d, rfl, sup_le h₁' h₂⟩
         }

theorem coe_sup [SemilatticeSup α] (a b : α) : ((a⊔b : α) : WithBot α) = a⊔b :=
  rfl

instance [SemilatticeInf α] : SemilatticeInf (WithBot α) :=
  { WithBot.orderBot, WithBot.partialOrder with inf := fun o₁ o₂ => o₁.bind fun a => o₂.map fun b => a⊓b,
    inf_le_left := fun o₁ o₂ a ha => by
      simp [← map] at ha
      rcases ha with ⟨b, rfl, c, rfl, rfl⟩
      exact ⟨_, rfl, inf_le_left⟩,
    inf_le_right := fun o₁ o₂ a ha => by
      simp [← map] at ha
      rcases ha with ⟨b, rfl, c, rfl, rfl⟩
      exact ⟨_, rfl, inf_le_right⟩,
    le_inf := fun o₁ o₂ o₃ h₁ h₂ a ha => by
      cases ha
      rcases h₁ a rfl with ⟨b, ⟨⟩, ab⟩
      rcases h₂ a rfl with ⟨c, ⟨⟩, ac⟩
      exact ⟨_, rfl, le_inf ab ac⟩ }

theorem coe_inf [SemilatticeInf α] (a b : α) : ((a⊓b : α) : WithBot α) = a⊓b :=
  rfl

instance [Lattice α] : Lattice (WithBot α) :=
  { WithBot.semilatticeSup, WithBot.semilatticeInf with }

instance decidableLe [LE α] [@DecidableRel α (· ≤ ·)] : @DecidableRel (WithBot α) (· ≤ ·)
  | none, x => is_true fun a h => Option.noConfusion h
  | some x, some y =>
    if h : x ≤ y then isTrue (some_le_some.2 h)
    else
      is_false <| by
        simp [*]
  | some x, none =>
    is_false fun h => by
      rcases h x rfl with ⟨y, ⟨_⟩, _⟩

instance decidableLt [LT α] [@DecidableRel α (· < ·)] : @DecidableRel (WithBot α) (· < ·)
  | none, some x =>
    is_true <| by
      exists x, rfl <;> rintro _ ⟨⟩
  | some x, some y =>
    if h : x < y then
      is_true <| by
        simp [*]
    else
      is_false <| by
        simp [*]
  | x, none =>
    is_false <| by
      rintro ⟨a, ⟨⟨⟩⟩⟩

instance is_total_le [LE α] [IsTotal α (· ≤ ·)] : IsTotal (WithBot α) (· ≤ ·) :=
  ⟨fun a b =>
    match a, b with
    | none, _ => Or.inl bot_le
    | _, none => Or.inr bot_le
    | some x, some y => (total_of (· ≤ ·) x y).imp some_le_some.2 some_le_some.2⟩

instance [LinearOrderₓ α] : LinearOrderₓ (WithBot α) :=
  Lattice.toLinearOrder _

-- this is not marked simp because the corresponding with_top lemmas are used
@[norm_cast]
theorem coe_min [LinearOrderₓ α] (x y : α) : ((min x y : α) : WithBot α) = min x y :=
  rfl

-- this is not marked simp because the corresponding with_top lemmas are used
@[norm_cast]
theorem coe_max [LinearOrderₓ α] (x y : α) : ((max x y : α) : WithBot α) = max x y :=
  rfl

theorem well_founded_lt [Preorderₓ α] (h : @WellFounded α (· < ·)) : @WellFounded (WithBot α) (· < ·) :=
  have acc_bot : Acc ((· < ·) : WithBot α → WithBot α → Prop) ⊥ :=
    Acc.intro _ fun a ha => (not_le_of_gtₓ ha bot_le).elim
  ⟨fun a =>
    Option.recOn a acc_bot fun a =>
      Acc.intro _ fun b =>
        Option.recOn b (fun _ => acc_bot) fun b =>
          WellFounded.induction h b
            (show
              ∀ b : α,
                (∀ c, c < b → (c : WithBot α) < a → Acc ((· < ·) : WithBot α → WithBot α → Prop) c) →
                  (b : WithBot α) < a → Acc ((· < ·) : WithBot α → WithBot α → Prop) b
              from fun b ih hba =>
              Acc.intro _ fun c =>
                Option.recOn c (fun _ => acc_bot) fun c hc => ih _ (some_lt_some.1 hc) (lt_transₓ hc hba))⟩

instance [LT α] [DenselyOrdered α] [NoMinOrder α] : DenselyOrdered (WithBot α) :=
  ⟨fun a b =>
    match a, b with
    | a, none => fun h : a < ⊥ => (not_lt_none _ h).elim
    | none, some b => fun h =>
      let ⟨a, ha⟩ := exists_lt b
      ⟨a, bot_lt_coe a, coe_lt_coe.2 ha⟩
    | some a, some b => fun h =>
      let ⟨a, ha₁, ha₂⟩ := exists_between (coe_lt_coe.1 h)
      ⟨a, coe_lt_coe.2 ha₁, coe_lt_coe.2 ha₂⟩⟩

theorem lt_iff_exists_coe_btwn [Preorderₓ α] [DenselyOrdered α] [NoMinOrder α] {a b : WithBot α} :
    a < b ↔ ∃ x : α, a < ↑x ∧ ↑x < b :=
  ⟨fun h =>
    let ⟨y, hy⟩ := exists_between h
    let ⟨x, hx⟩ := lt_iff_exists_coe.1 hy.1
    ⟨x, hx.1 ▸ hy⟩,
    fun ⟨x, hx⟩ => lt_transₓ hx.1 hx.2⟩

instance [LE α] [NoTopOrder α] [Nonempty α] : NoTopOrder (WithBot α) :=
  ⟨by
    apply rec_bot_coe
    · exact ‹Nonempty α›.elim fun a => ⟨a, not_coe_le_bot a⟩
      
    · intro a
      obtain ⟨b, h⟩ := exists_not_le a
      exact
        ⟨b, by
          rwa [coe_le_coe]⟩
      ⟩

instance [LT α] [NoMaxOrder α] [Nonempty α] : NoMaxOrder (WithBot α) :=
  ⟨by
    apply WithBot.recBotCoe
    · apply ‹Nonempty α›.elim
      exact fun a => ⟨a, WithBot.bot_lt_coe a⟩
      
    · intro a
      obtain ⟨b, ha⟩ := exists_gt a
      exact ⟨b, with_bot.coe_lt_coe.mpr ha⟩
      ⟩

end WithBot

/-- Attach `⊤` to a type. -/
--TODO(Mario): Construct using order dual on with_bot
def WithTop (α : Type _) :=
  Option α

namespace WithTop

variable {a b : α}

unsafe instance [has_to_format α] :
    has_to_format (WithTop α) where to_format := fun x =>
    match x with
    | none => "⊤"
    | some x => to_fmt x

instance [HasRepr α] : HasRepr (WithTop α) :=
  ⟨fun o =>
    match o with
    | none => "⊤"
    | some a => "↑" ++ reprₓ a⟩

instance : CoeTₓ α (WithTop α) :=
  ⟨some⟩

instance : HasTop (WithTop α) :=
  ⟨none⟩

unsafe instance {α : Type} [reflected _ α] [has_reflect α] : has_reflect (WithTop α)
  | ⊤ => quote.1 ⊤
  | (a : α) => (quote.1 (coe : α → WithTop α)).subst (quote.1 a)

instance : Inhabited (WithTop α) :=
  ⟨⊤⟩

theorem none_eq_top : (none : WithTop α) = (⊤ : WithTop α) :=
  rfl

theorem some_eq_coe (a : α) : (some a : WithTop α) = (↑a : WithTop α) :=
  rfl

@[simp]
theorem top_ne_coe : ⊤ ≠ (a : WithTop α) :=
  fun.

@[simp]
theorem coe_ne_top : (a : WithTop α) ≠ ⊤ :=
  fun.

/-- Recursor for `with_top` using the preferred forms `⊤` and `↑a`. -/
@[elab_as_eliminator]
def recTopCoe {C : WithTop α → Sort _} (h₁ : C ⊤) (h₂ : ∀ a : α, C a) : ∀ n : WithTop α, C n :=
  Option.rec h₁ h₂

@[simp]
theorem rec_top_coe_top {C : WithTop α → Sort _} (d : C ⊤) (f : ∀ a : α, C a) : @recTopCoe _ C d f ⊤ = d :=
  rfl

@[simp]
theorem rec_top_coe_coe {C : WithTop α → Sort _} (d : C ⊤) (f : ∀ a : α, C a) (x : α) : @recTopCoe _ C d f ↑x = f x :=
  rfl

/-- Specialization of `option.get_or_else` to values in `with_top α` that respects API boundaries.
-/
def untop' (d : α) (x : WithTop α) : α :=
  recTopCoe d id x

@[simp]
theorem untop'_top {α} (d : α) : untop' d ⊤ = d :=
  rfl

@[simp]
theorem untop'_coe {α} (d x : α) : untop' d x = x :=
  rfl

@[norm_cast]
theorem coe_eq_coe : (a : WithTop α) = b ↔ a = b :=
  Option.some_inj

/-- Lift a map `f : α → β` to `with_top α → with_top β`. Implemented using `option.map`. -/
def map (f : α → β) : WithTop α → WithTop β :=
  Option.map f

@[simp]
theorem map_top (f : α → β) : map f ⊤ = ⊤ :=
  rfl

@[simp]
theorem map_coe (f : α → β) (a : α) : map f a = f a :=
  rfl

theorem ne_top_iff_exists {x : WithTop α} : x ≠ ⊤ ↔ ∃ a : α, ↑a = x :=
  Option.ne_none_iff_exists

/-- Deconstruct a `x : with_top α` to the underlying value in `α`, given a proof that `x ≠ ⊤`. -/
def untop : ∀ x : WithTop α, x ≠ ⊤ → α :=
  WithBot.unbot

@[simp]
theorem coe_untop (x : WithTop α) (h : x ≠ ⊤) : (x.untop h : WithTop α) = x :=
  WithBot.coe_unbot x h

@[simp]
theorem untop_coe (x : α) (h : (x : WithTop α) ≠ ⊤ := coe_ne_top) : (x : WithTop α).untop h = x :=
  rfl

instance : CanLift (WithTop α) α where
  coe := coe
  cond := fun r => r ≠ ⊤
  prf := fun x h => ⟨x.untop h, coe_untop _ _⟩

section LE

variable [LE α]

instance (priority := 10) : LE (WithTop α) :=
  ⟨fun o₁ o₂ : Option α => ∀, ∀ a ∈ o₂, ∀, ∃ b ∈ o₁, b ≤ a⟩

@[simp]
theorem some_le_some : @LE.le (WithTop α) _ (some a) (some b) ↔ a ≤ b := by
  simp [← (· ≤ ·)]

@[simp, norm_cast]
theorem coe_le_coe : (a : WithTop α) ≤ b ↔ a ≤ b :=
  some_le_some

@[simp]
theorem le_none {a : WithTop α} : @LE.le (WithTop α) _ a none := fun b h => Option.noConfusion h

instance : OrderTop (WithTop α) :=
  { WithTop.hasTop with le_top := fun a => le_none }

instance [OrderBot α] : OrderBot (WithTop α) where
  bot := some ⊥
  bot_le := fun o a ha => by
    cases ha <;> exact ⟨_, rfl, bot_le⟩

instance [OrderBot α] : BoundedOrder (WithTop α) :=
  { WithTop.orderTop, WithTop.orderBot with }

theorem not_top_le_coe (a : α) : ¬(⊤ : WithTop α) ≤ ↑a :=
  WithBot.not_coe_le_bot (toDual a)

theorem le_coe : ∀ {o : Option α}, a ∈ o → (@LE.le (WithTop α) _ o b ↔ a ≤ b)
  | _, rfl => coe_le_coe

theorem le_coe_iff : ∀ {x : WithTop α}, x ≤ b ↔ ∃ a : α, x = a ∧ a ≤ b
  | some a => by
    simp [← some_eq_coe, ← coe_eq_coe]
  | none =>
    iff_of_false (not_top_le_coe _) <| by
      simp [← none_eq_top]

theorem coe_le_iff : ∀ {x : WithTop α}, ↑a ≤ x ↔ ∀ b, x = ↑b → a ≤ b
  | some b => by
    simp [← some_eq_coe, ← coe_eq_coe]
  | none => by
    simp [← none_eq_top]

protected theorem _root_.is_min.with_top (h : IsMin a) : IsMin (a : WithTop α)
  | none, _ => le_top
  | some b, hb => some_le_some.2 <| h <| some_le_some.1 hb

end LE

section LT

variable [LT α]

instance (priority := 10) : LT (WithTop α) :=
  ⟨fun o₁ o₂ : Option α => ∃ b ∈ o₁, ∀, ∀ a ∈ o₂, ∀, b < a⟩

@[simp]
theorem some_lt_some : @LT.lt (WithTop α) _ (some a) (some b) ↔ a < b := by
  simp [← (· < ·)]

@[simp, norm_cast]
theorem coe_lt_coe : (a : WithTop α) < b ↔ a < b :=
  some_lt_some

@[simp]
theorem some_lt_none (a : α) : @LT.lt (WithTop α) _ (some a) none :=
  ⟨a, rfl, fun b hb => (Option.not_mem_none _ hb).elim⟩

theorem coe_lt_top (a : α) : (a : WithTop α) < ⊤ :=
  some_lt_none a

@[simp]
theorem not_none_lt (a : WithTop α) : ¬@LT.lt (WithTop α) _ none a := fun ⟨_, h, _⟩ => Option.not_mem_none _ h

theorem lt_iff_exists_coe : ∀ {a b : WithTop α}, a < b ↔ ∃ p : α, a = p ∧ ↑p < b
  | some a, b => by
    simp [← some_eq_coe, ← coe_eq_coe]
  | none, b =>
    iff_of_false (not_none_lt _) <| by
      simp [← none_eq_top]

theorem coe_lt_iff : ∀ {x : WithTop α}, ↑a < x ↔ ∀ b, x = ↑b → a < b
  | some b => by
    simp [← some_eq_coe, ← coe_eq_coe, ← coe_lt_coe]
  | none => by
    simp [← none_eq_top, ← coe_lt_top]

end LT

instance [Preorderₓ α] : Preorderₓ (WithTop α) where
  le := (· ≤ ·)
  lt := (· < ·)
  lt_iff_le_not_le := by
    intros
    cases a <;> cases b <;> simp [← lt_iff_le_not_leₓ] <;> simp [← (· < ·), ← (· ≤ ·)]
  le_refl := fun o a ha => ⟨a, ha, le_rfl⟩
  le_trans := fun o₁ o₂ o₃ h₁ h₂ c hc =>
    let ⟨b, hb, bc⟩ := h₂ c hc
    let ⟨a, ha, ab⟩ := h₁ b hb
    ⟨a, ha, le_transₓ ab bc⟩

instance [PartialOrderₓ α] : PartialOrderₓ (WithTop α) :=
  { WithTop.preorder with
    le_antisymm := fun o₁ o₂ h₁ h₂ => by
      cases' o₂ with b
      · cases' o₁ with a
        · rfl
          
        rcases h₂ a rfl with ⟨_, ⟨⟩, _⟩
        
      · rcases h₁ b rfl with ⟨a, ⟨⟩, h₁'⟩
        rcases h₂ a rfl with ⟨_, ⟨⟩, h₂'⟩
        rw [le_antisymmₓ h₁' h₂']
         }

theorem map_le_iff [Preorderₓ α] [Preorderₓ β] (f : α → β) (a b : WithTop α) (mono_iff : ∀ {a b}, f a ≤ f b ↔ a ≤ b) :
    a.map f ≤ b.map f ↔ a ≤ b :=
  @WithBot.map_le_iff αᵒᵈ βᵒᵈ _ _ f (fun a b => mono_iff) b a

instance [SemilatticeInf α] : SemilatticeInf (WithTop α) :=
  { WithTop.partialOrder with inf := Option.liftOrGet (·⊓·),
    inf_le_left := fun o₁ o₂ a ha => by
      cases ha <;> cases o₂ <;> simp [← Option.liftOrGet],
    inf_le_right := fun o₁ o₂ a ha => by
      cases ha <;> cases o₁ <;> simp [← Option.liftOrGet],
    le_inf := fun o₁ o₂ o₃ h₁ h₂ a ha => by
      cases' o₂ with b <;> cases' o₃ with c <;> cases ha
      · exact h₂ a rfl
        
      · exact h₁ a rfl
        
      · rcases h₁ b rfl with ⟨d, ⟨⟩, h₁'⟩
        simp at h₂
        exact ⟨d, rfl, le_inf h₁' h₂⟩
         }

theorem coe_inf [SemilatticeInf α] (a b : α) : ((a⊓b : α) : WithTop α) = a⊓b :=
  rfl

instance [SemilatticeSup α] : SemilatticeSup (WithTop α) :=
  { WithTop.partialOrder with sup := fun o₁ o₂ => o₁.bind fun a => o₂.map fun b => a⊔b,
    le_sup_left := fun o₁ o₂ a ha => by
      simp [← map] at ha
      rcases ha with ⟨b, rfl, c, rfl, rfl⟩
      exact ⟨_, rfl, le_sup_left⟩,
    le_sup_right := fun o₁ o₂ a ha => by
      simp [← map] at ha
      rcases ha with ⟨b, rfl, c, rfl, rfl⟩
      exact ⟨_, rfl, le_sup_right⟩,
    sup_le := fun o₁ o₂ o₃ h₁ h₂ a ha => by
      cases ha
      rcases h₁ a rfl with ⟨b, ⟨⟩, ab⟩
      rcases h₂ a rfl with ⟨c, ⟨⟩, ac⟩
      exact ⟨_, rfl, sup_le ab ac⟩ }

theorem coe_sup [SemilatticeSup α] (a b : α) : ((a⊔b : α) : WithTop α) = a⊔b :=
  rfl

instance [Lattice α] : Lattice (WithTop α) :=
  { WithTop.semilatticeSup, WithTop.semilatticeInf with }

instance decidableLe [LE α] [@DecidableRel α (· ≤ ·)] : @DecidableRel (WithTop α) (· ≤ ·) := fun x y =>
  @WithBot.decidableLe αᵒᵈ _ _ y x

instance decidableLt [LT α] [@DecidableRel α (· < ·)] : @DecidableRel (WithTop α) (· < ·) := fun x y =>
  @WithBot.decidableLt αᵒᵈ _ _ y x

instance is_total_le [LE α] [IsTotal α (· ≤ ·)] : IsTotal (WithTop α) (· ≤ ·) :=
  @OrderDual.is_total_le (WithBot αᵒᵈ) _ _

instance [LinearOrderₓ α] : LinearOrderₓ (WithTop α) :=
  Lattice.toLinearOrder _

@[simp, norm_cast]
theorem coe_min [LinearOrderₓ α] (x y : α) : (↑(min x y) : WithTop α) = min x y :=
  rfl

@[simp, norm_cast]
theorem coe_max [LinearOrderₓ α] (x y : α) : (↑(max x y) : WithTop α) = max x y :=
  rfl

theorem well_founded_lt [Preorderₓ α] (h : @WellFounded α (· < ·)) : @WellFounded (WithTop α) (· < ·) :=
  have acc_some : ∀ a : α, Acc ((· < ·) : WithTop α → WithTop α → Prop) (some a) := fun a =>
    Acc.intro _
      (WellFounded.induction h a
        (show
          ∀ b, (∀ c, c < b → ∀ d : WithTop α, d < some c → Acc (· < ·) d) → ∀ y : WithTop α, y < some b → Acc (· < ·) y
          from fun b ih c =>
          Option.recOn c (fun hc => (not_lt_of_geₓ le_top hc).elim) fun c hc => Acc.intro _ (ih _ (some_lt_some.1 hc))))
  ⟨fun a =>
    Option.recOn a (Acc.intro _ fun y => Option.recOn y (fun h => (lt_irreflₓ _ h).elim) fun _ _ => acc_some _)
      acc_some⟩

theorem well_founded_gt [Preorderₓ α] (h : @WellFounded α (· > ·)) : @WellFounded (WithTop α) (· > ·) :=
  @WithBot.well_founded_lt αᵒᵈ _ h

theorem _root_.with_bot.well_founded_gt [Preorderₓ α] (h : @WellFounded α (· > ·)) : @WellFounded (WithBot α) (· > ·) :=
  @WithTop.well_founded_lt αᵒᵈ _ h

instance [LT α] [DenselyOrdered α] [NoMaxOrder α] : DenselyOrdered (WithTop α) :=
  OrderDual.densely_ordered (WithBot αᵒᵈ)

theorem lt_iff_exists_coe_btwn [Preorderₓ α] [DenselyOrdered α] [NoMaxOrder α] {a b : WithTop α} :
    a < b ↔ ∃ x : α, a < ↑x ∧ ↑x < b :=
  ⟨fun h =>
    let ⟨y, hy⟩ := exists_between h
    let ⟨x, hx⟩ := lt_iff_exists_coe.1 hy.2
    ⟨x, hx.1 ▸ hy⟩,
    fun ⟨x, hx⟩ => lt_transₓ hx.1 hx.2⟩

instance [LE α] [NoBotOrder α] [Nonempty α] : NoBotOrder (WithTop α) :=
  OrderDual.no_bot_order (WithBot αᵒᵈ)

instance [LT α] [NoMinOrder α] [Nonempty α] : NoMinOrder (WithTop α) :=
  OrderDual.no_min_order (WithBot αᵒᵈ)

end WithTop

section Mono

variable [Preorderₓ α] [Preorderₓ β] {f : α → β}

protected theorem Monotone.with_bot_map (hf : Monotone f) : Monotone (WithBot.map f)
  | ⊥, _, h => bot_le
  | (a : α), ⊥, h => (WithBot.not_coe_le_bot _ h).elim
  | (a : α), (b : α), h => WithBot.coe_le_coe.2 (hf (WithBot.coe_le_coe.1 h))

protected theorem Monotone.with_top_map (hf : Monotone f) : Monotone (WithTop.map f) :=
  hf.dual.with_bot_map.dual

protected theorem StrictMono.with_bot_map (hf : StrictMono f) : StrictMono (WithBot.map f)
  | ⊥, (a : α), h => WithBot.bot_lt_coe _
  | (a : α), (b : α), h => WithBot.coe_lt_coe.mpr (hf <| WithBot.coe_lt_coe.mp h)

protected theorem StrictMono.with_top_map (hf : StrictMono f) : StrictMono (WithTop.map f) :=
  hf.dual.with_bot_map.dual

end Mono

/-! ### Subtype, order dual, product lattices -/


namespace Subtype

variable {p : α → Prop}

/-- A subtype remains a `⊥`-order if the property holds at `⊥`. -/
-- See note [reducible non-instances]
@[reducible]
protected def orderBot [LE α] [OrderBot α] (hbot : p ⊥) : OrderBot { x : α // p x } where
  bot := ⟨⊥, hbot⟩
  bot_le := fun _ => bot_le

/-- A subtype remains a `⊤`-order if the property holds at `⊤`. -/
-- See note [reducible non-instances]
@[reducible]
protected def orderTop [LE α] [OrderTop α] (htop : p ⊤) : OrderTop { x : α // p x } where
  top := ⟨⊤, htop⟩
  le_top := fun _ => le_top

/-- A subtype remains a bounded order if the property holds at `⊥` and `⊤`. -/
-- See note [reducible non-instances]
@[reducible]
protected def boundedOrder [LE α] [BoundedOrder α] (hbot : p ⊥) (htop : p ⊤) : BoundedOrder (Subtype p) :=
  { Subtype.orderTop htop, Subtype.orderBot hbot with }

variable [PartialOrderₓ α]

@[simp]
theorem mk_bot [OrderBot α] [OrderBot (Subtype p)] (hbot : p ⊥) : mk ⊥ hbot = ⊥ :=
  le_bot_iff.1 <| coe_le_coe.1 bot_le

@[simp]
theorem mk_top [OrderTop α] [OrderTop (Subtype p)] (htop : p ⊤) : mk ⊤ htop = ⊤ :=
  top_le_iff.1 <| coe_le_coe.1 le_top

theorem coe_bot [OrderBot α] [OrderBot (Subtype p)] (hbot : p ⊥) : ((⊥ : Subtype p) : α) = ⊥ :=
  congr_arg coe (mk_bot hbot).symm

theorem coe_top [OrderTop α] [OrderTop (Subtype p)] (htop : p ⊤) : ((⊤ : Subtype p) : α) = ⊤ :=
  congr_arg coe (mk_top htop).symm

@[simp]
theorem coe_eq_bot_iff [OrderBot α] [OrderBot (Subtype p)] (hbot : p ⊥) {x : { x // p x }} : (x : α) = ⊥ ↔ x = ⊥ := by
  rw [← coe_bot hbot, ext_iff]

@[simp]
theorem coe_eq_top_iff [OrderTop α] [OrderTop (Subtype p)] (htop : p ⊤) {x : { x // p x }} : (x : α) = ⊤ ↔ x = ⊤ := by
  rw [← coe_top htop, ext_iff]

@[simp]
theorem mk_eq_bot_iff [OrderBot α] [OrderBot (Subtype p)] (hbot : p ⊥) {x : α} (hx : p x) :
    (⟨x, hx⟩ : Subtype p) = ⊥ ↔ x = ⊥ :=
  (coe_eq_bot_iff hbot).symm

@[simp]
theorem mk_eq_top_iff [OrderTop α] [OrderTop (Subtype p)] (htop : p ⊤) {x : α} (hx : p x) :
    (⟨x, hx⟩ : Subtype p) = ⊤ ↔ x = ⊤ :=
  (coe_eq_top_iff htop).symm

end Subtype

namespace Prod

variable (α β)

instance [HasTop α] [HasTop β] : HasTop (α × β) :=
  ⟨⟨⊤, ⊤⟩⟩

instance [HasBot α] [HasBot β] : HasBot (α × β) :=
  ⟨⟨⊥, ⊥⟩⟩

instance [LE α] [LE β] [OrderTop α] [OrderTop β] : OrderTop (α × β) :=
  { Prod.hasTop α β with le_top := fun a => ⟨le_top, le_top⟩ }

instance [LE α] [LE β] [OrderBot α] [OrderBot β] : OrderBot (α × β) :=
  { Prod.hasBot α β with bot_le := fun a => ⟨bot_le, bot_le⟩ }

instance [LE α] [LE β] [BoundedOrder α] [BoundedOrder β] : BoundedOrder (α × β) :=
  { Prod.orderTop α β, Prod.orderBot α β with }

end Prod

section LinearOrderₓ

variable [LinearOrderₓ α]

-- `simp` can prove these, so they shouldn't be simp-lemmas.
theorem min_bot_left [OrderBot α] (a : α) : min ⊥ a = ⊥ :=
  bot_inf_eq

theorem max_top_left [OrderTop α] (a : α) : max ⊤ a = ⊤ :=
  top_sup_eq

theorem min_top_left [OrderTop α] (a : α) : min ⊤ a = a :=
  top_inf_eq

theorem max_bot_left [OrderBot α] (a : α) : max ⊥ a = a :=
  bot_sup_eq

theorem min_top_right [OrderTop α] (a : α) : min a ⊤ = a :=
  inf_top_eq

theorem max_bot_right [OrderBot α] (a : α) : max a ⊥ = a :=
  sup_bot_eq

theorem min_bot_right [OrderBot α] (a : α) : min a ⊥ = ⊥ :=
  inf_bot_eq

theorem max_top_right [OrderTop α] (a : α) : max a ⊤ = ⊤ :=
  sup_top_eq

@[simp]
theorem min_eq_bot [OrderBot α] {a b : α} : min a b = ⊥ ↔ a = ⊥ ∨ b = ⊥ := by
  simp only [inf_eq_min, le_bot_iff, ← inf_le_iff]

@[simp]
theorem max_eq_top [OrderTop α] {a b : α} : max a b = ⊤ ↔ a = ⊤ ∨ b = ⊤ :=
  @min_eq_bot αᵒᵈ _ _ a b

@[simp]
theorem max_eq_bot [OrderBot α] {a b : α} : max a b = ⊥ ↔ a = ⊥ ∧ b = ⊥ :=
  sup_eq_bot_iff

@[simp]
theorem min_eq_top [OrderTop α] {a b : α} : min a b = ⊤ ↔ a = ⊤ ∧ b = ⊤ :=
  inf_eq_top_iff

end LinearOrderₓ

/-! ### Disjointness and complements -/


section Disjoint

section SemilatticeInfBot

variable [SemilatticeInf α] [OrderBot α] {a b c d : α}

/-- Two elements of a lattice are disjoint if their inf is the bottom element.
  (This generalizes disjoint sets, viewed as members of the subset lattice.) -/
def Disjoint (a b : α) : Prop :=
  a⊓b ≤ ⊥

theorem disjoint_iff : Disjoint a b ↔ a⊓b = ⊥ :=
  le_bot_iff

theorem Disjoint.eq_bot : Disjoint a b → a⊓b = ⊥ :=
  bot_unique

theorem Disjoint.comm : Disjoint a b ↔ Disjoint b a := by
  rw [Disjoint, Disjoint, inf_comm]

@[symm]
theorem Disjoint.symm ⦃a b : α⦄ : Disjoint a b → Disjoint b a :=
  Disjoint.comm.1

theorem symmetric_disjoint : Symmetric (Disjoint : α → α → Prop) :=
  Disjoint.symm

theorem disjoint_assoc : Disjoint (a⊓b) c ↔ Disjoint a (b⊓c) := by
  rw [Disjoint, Disjoint, inf_assoc]

@[simp]
theorem disjoint_bot_left : Disjoint ⊥ a :=
  inf_le_left

@[simp]
theorem disjoint_bot_right : Disjoint a ⊥ :=
  inf_le_right

theorem Disjoint.mono (h₁ : a ≤ b) (h₂ : c ≤ d) : Disjoint b d → Disjoint a c :=
  le_transₓ <| inf_le_inf h₁ h₂

theorem Disjoint.mono_left (h : a ≤ b) : Disjoint b c → Disjoint a c :=
  Disjoint.mono h le_rfl

theorem Disjoint.mono_right : b ≤ c → Disjoint a c → Disjoint a b :=
  Disjoint.mono le_rfl

variable (c)

theorem Disjoint.inf_left (h : Disjoint a b) : Disjoint (a⊓c) b :=
  h.mono_left inf_le_left

theorem Disjoint.inf_left' (h : Disjoint a b) : Disjoint (c⊓a) b :=
  h.mono_left inf_le_right

theorem Disjoint.inf_right (h : Disjoint a b) : Disjoint a (b⊓c) :=
  h.mono_right inf_le_left

theorem Disjoint.inf_right' (h : Disjoint a b) : Disjoint a (c⊓b) :=
  h.mono_right inf_le_right

variable {c}

@[simp]
theorem disjoint_self : Disjoint a a ↔ a = ⊥ := by
  simp [← Disjoint]

/- TODO: Rename `disjoint.eq_bot` to `disjoint.inf_eq` and `disjoint.eq_bot_of_self` to
`disjoint.eq_bot` -/
alias disjoint_self ↔ Disjoint.eq_bot_of_self _

theorem Disjoint.ne (ha : a ≠ ⊥) (hab : Disjoint a b) : a ≠ b := fun h =>
  ha <|
    disjoint_self.1 <| by
      rwa [← h] at hab

theorem Disjoint.eq_bot_of_le (hab : Disjoint a b) (h : a ≤ b) : a = ⊥ :=
  eq_bot_iff.2
    (by
      rwa [← inf_eq_left.2 h])

theorem Disjoint.eq_bot_of_ge (hab : Disjoint a b) : b ≤ a → b = ⊥ :=
  hab.symm.eq_bot_of_le

theorem Disjoint.of_disjoint_inf_of_le (h : Disjoint (a⊓b) c) (hle : a ≤ c) : Disjoint a b :=
  disjoint_iff.2 <| h.eq_bot_of_le <| inf_le_of_left_le hle

theorem Disjoint.of_disjoint_inf_of_le' (h : Disjoint (a⊓b) c) (hle : b ≤ c) : Disjoint a b :=
  disjoint_iff.2 <| h.eq_bot_of_le <| inf_le_of_right_le hle

end SemilatticeInfBot

section Lattice

variable [Lattice α] [BoundedOrder α] {a : α}

@[simp]
theorem disjoint_top : Disjoint a ⊤ ↔ a = ⊥ := by
  simp [← disjoint_iff]

@[simp]
theorem top_disjoint : Disjoint ⊤ a ↔ a = ⊥ := by
  simp [← disjoint_iff]

end Lattice

section DistribLatticeBot

variable [DistribLattice α] [OrderBot α] {a b c : α}

@[simp]
theorem disjoint_sup_left : Disjoint (a⊔b) c ↔ Disjoint a c ∧ Disjoint b c := by
  simp only [← disjoint_iff, ← inf_sup_right, ← sup_eq_bot_iff]

@[simp]
theorem disjoint_sup_right : Disjoint a (b⊔c) ↔ Disjoint a b ∧ Disjoint a c := by
  simp only [← disjoint_iff, ← inf_sup_left, ← sup_eq_bot_iff]

theorem Disjoint.sup_left (ha : Disjoint a c) (hb : Disjoint b c) : Disjoint (a⊔b) c :=
  disjoint_sup_left.2 ⟨ha, hb⟩

theorem Disjoint.sup_right (hb : Disjoint a b) (hc : Disjoint a c) : Disjoint a (b⊔c) :=
  disjoint_sup_right.2 ⟨hb, hc⟩

theorem Disjoint.left_le_of_le_sup_right (h : a ≤ b⊔c) (hd : Disjoint a c) : a ≤ b :=
  le_of_inf_le_sup_le (le_transₓ hd bot_le) <| sup_le h le_sup_right

theorem Disjoint.left_le_of_le_sup_left (h : a ≤ c⊔b) (hd : Disjoint a c) : a ≤ b :=
  hd.left_le_of_le_sup_right <| by
    rwa [sup_comm]

end DistribLatticeBot

end Disjoint

section Codisjoint

section SemilatticeSupTop

variable [SemilatticeSup α] [OrderTop α] {a b c d : α}

/-- Two elements of a lattice are codisjoint if their sup is the top element. -/
def Codisjoint (a b : α) : Prop :=
  ⊤ ≤ a⊔b

theorem codisjoint_iff : Codisjoint a b ↔ a⊔b = ⊤ :=
  top_le_iff

theorem Codisjoint.eq_top : Codisjoint a b → a⊔b = ⊤ :=
  top_unique

theorem Codisjoint.comm : Codisjoint a b ↔ Codisjoint b a := by
  rw [Codisjoint, Codisjoint, sup_comm]

@[symm]
theorem Codisjoint.symm ⦃a b : α⦄ : Codisjoint a b → Codisjoint b a :=
  Codisjoint.comm.1

theorem symmetric_codisjoint : Symmetric (Codisjoint : α → α → Prop) :=
  Codisjoint.symm

theorem codisjoint_assoc : Codisjoint (a⊔b) c ↔ Codisjoint a (b⊔c) := by
  rw [Codisjoint, Codisjoint, sup_assoc]

@[simp]
theorem codisjoint_top_left : Codisjoint ⊤ a :=
  le_sup_left

@[simp]
theorem codisjoint_top_right : Codisjoint a ⊤ :=
  le_sup_right

theorem Codisjoint.mono (h₁ : a ≤ b) (h₂ : c ≤ d) : Codisjoint a c → Codisjoint b d :=
  le_trans' <| sup_le_sup h₁ h₂

theorem Codisjoint.mono_left (h : a ≤ b) : Codisjoint a c → Codisjoint b c :=
  Codisjoint.mono h le_rfl

theorem Codisjoint.mono_right : b ≤ c → Codisjoint a b → Codisjoint a c :=
  Codisjoint.mono le_rfl

variable (c)

theorem Codisjoint.sup_left (h : Codisjoint a b) : Codisjoint (a⊔c) b :=
  h.mono_left le_sup_left

theorem Codisjoint.sup_left' (h : Codisjoint a b) : Codisjoint (c⊔a) b :=
  h.mono_left le_sup_right

theorem Codisjoint.sup_right (h : Codisjoint a b) : Codisjoint a (b⊔c) :=
  h.mono_right le_sup_left

theorem Codisjoint.sup_right' (h : Codisjoint a b) : Codisjoint a (c⊔b) :=
  h.mono_right le_sup_right

variable {c}

@[simp]
theorem codisjoint_self : Codisjoint a a ↔ a = ⊤ := by
  simp [← Codisjoint]

/- TODO: Rename `codisjoint.eq_top` to `codisjoint.sup_eq` and `codisjoint.eq_top_of_self` to
`codisjoint.eq_top` -/
alias codisjoint_self ↔ Codisjoint.eq_top_of_self _

theorem Codisjoint.ne (ha : a ≠ ⊤) (hab : Codisjoint a b) : a ≠ b := fun h =>
  ha <|
    codisjoint_self.1 <| by
      rwa [← h] at hab

theorem Codisjoint.eq_top_of_ge (hab : Codisjoint a b) (h : b ≤ a) : a = ⊤ :=
  eq_top_iff.2 <| by
    rwa [← sup_eq_left.2 h]

theorem Codisjoint.eq_top_of_le (hab : Codisjoint a b) : a ≤ b → b = ⊤ :=
  hab.symm.eq_top_of_ge

theorem Codisjoint.of_codisjoint_sup_of_le (h : Codisjoint (a⊔b) c) (hle : c ≤ a) : Codisjoint a b :=
  codisjoint_iff.2 <| h.eq_top_of_ge <| le_sup_of_le_left hle

theorem Codisjoint.of_codisjoint_sup_of_le' (h : Codisjoint (a⊔b) c) (hle : c ≤ b) : Codisjoint a b :=
  codisjoint_iff.2 <| h.eq_top_of_ge <| le_sup_of_le_right hle

end SemilatticeSupTop

section Lattice

variable [Lattice α] [BoundedOrder α] {a : α}

@[simp]
theorem codisjoint_bot : Codisjoint a ⊥ ↔ a = ⊤ := by
  simp [← codisjoint_iff]

@[simp]
theorem bot_codisjoint : Codisjoint ⊥ a ↔ a = ⊤ := by
  simp [← codisjoint_iff]

end Lattice

section DistribLatticeTop

variable [DistribLattice α] [OrderTop α] {a b c : α}

@[simp]
theorem codisjoint_inf_left : Codisjoint (a⊓b) c ↔ Codisjoint a c ∧ Codisjoint b c := by
  simp only [← codisjoint_iff, ← sup_inf_right, ← inf_eq_top_iff]

@[simp]
theorem codisjoint_inf_right : Codisjoint a (b⊓c) ↔ Codisjoint a b ∧ Codisjoint a c := by
  simp only [← codisjoint_iff, ← sup_inf_left, ← inf_eq_top_iff]

theorem Codisjoint.inf_left (ha : Codisjoint a c) (hb : Codisjoint b c) : Codisjoint (a⊓b) c :=
  codisjoint_inf_left.2 ⟨ha, hb⟩

theorem Codisjoint.inf_right (hb : Codisjoint a b) (hc : Codisjoint a c) : Codisjoint a (b⊓c) :=
  codisjoint_inf_right.2 ⟨hb, hc⟩

theorem Codisjoint.left_le_of_le_inf_right (h : a⊓b ≤ c) (hd : Codisjoint b c) : a ≤ c :=
  le_of_inf_le_sup_le (le_inf h inf_le_right) <| le_top.trans hd.symm

theorem Codisjoint.left_le_of_le_inf_left (h : b⊓a ≤ c) (hd : Codisjoint b c) : a ≤ c :=
  hd.left_le_of_le_inf_right <| by
    rwa [inf_comm]

end DistribLatticeTop

end Codisjoint

theorem Disjoint.dual [SemilatticeInf α] [OrderBot α] {a b : α} : Disjoint a b → Codisjoint (toDual a) (toDual b) :=
  id

theorem Codisjoint.dual [SemilatticeSup α] [OrderTop α] {a b : α} : Codisjoint a b → Disjoint (toDual a) (toDual b) :=
  id

@[simp]
theorem disjoint_to_dual_iff [SemilatticeSup α] [OrderTop α] {a b : α} :
    Disjoint (toDual a) (toDual b) ↔ Codisjoint a b :=
  Iff.rfl

@[simp]
theorem disjoint_of_dual_iff [SemilatticeInf α] [OrderBot α] {a b : αᵒᵈ} :
    Disjoint (ofDual a) (ofDual b) ↔ Codisjoint a b :=
  Iff.rfl

@[simp]
theorem codisjoint_to_dual_iff [SemilatticeInf α] [OrderBot α] {a b : α} :
    Codisjoint (toDual a) (toDual b) ↔ Disjoint a b :=
  Iff.rfl

@[simp]
theorem codisjoint_of_dual_iff [SemilatticeSup α] [OrderTop α] {a b : αᵒᵈ} :
    Codisjoint (ofDual a) (ofDual b) ↔ Disjoint a b :=
  Iff.rfl

section IsCompl

/-- Two elements `x` and `y` are complements of each other if `x ⊔ y = ⊤` and `x ⊓ y = ⊥`. -/
@[protect_proj]
structure IsCompl [Lattice α] [BoundedOrder α] (x y : α) : Prop where
  Disjoint : Disjoint x y
  Codisjoint : Codisjoint x y

namespace IsCompl

section BoundedOrder

variable [Lattice α] [BoundedOrder α] {x y z : α}

@[symm]
protected theorem symm (h : IsCompl x y) : IsCompl y x :=
  ⟨h.1.symm, h.2.symm⟩

theorem of_eq (h₁ : x⊓y = ⊥) (h₂ : x⊔y = ⊤) : IsCompl x y :=
  ⟨le_of_eqₓ h₁, ge_of_eq h₂⟩

theorem inf_eq_bot (h : IsCompl x y) : x⊓y = ⊥ :=
  h.Disjoint.eq_bot

theorem sup_eq_top (h : IsCompl x y) : x⊔y = ⊤ :=
  h.Codisjoint.eq_top

theorem dual (h : IsCompl x y) : IsCompl (toDual x) (toDual y) :=
  ⟨h.2, h.1⟩

theorem of_dual {a b : αᵒᵈ} (h : IsCompl a b) : IsCompl (ofDual a) (ofDual b) :=
  ⟨h.2, h.1⟩

end BoundedOrder

variable [DistribLattice α] [BoundedOrder α] {a b x y z : α}

theorem inf_left_le_of_le_sup_right (h : IsCompl x y) (hle : a ≤ b⊔y) : a⊓x ≤ b :=
  calc
    a⊓x ≤ (b⊔y)⊓x := inf_le_inf hle le_rfl
    _ = b⊓x⊔y⊓x := inf_sup_right
    _ = b⊓x := by
      rw [h.symm.inf_eq_bot, sup_bot_eq]
    _ ≤ b := inf_le_left
    

theorem le_sup_right_iff_inf_left_le {a b} (h : IsCompl x y) : a ≤ b⊔y ↔ a⊓x ≤ b :=
  ⟨h.inf_left_le_of_le_sup_right, h.symm.dual.inf_left_le_of_le_sup_right⟩

theorem inf_left_eq_bot_iff (h : IsCompl y z) : x⊓y = ⊥ ↔ x ≤ z := by
  rw [← le_bot_iff, ← h.le_sup_right_iff_inf_left_le, bot_sup_eq]

theorem inf_right_eq_bot_iff (h : IsCompl y z) : x⊓z = ⊥ ↔ x ≤ y :=
  h.symm.inf_left_eq_bot_iff

theorem disjoint_left_iff (h : IsCompl y z) : Disjoint x y ↔ x ≤ z := by
  rw [disjoint_iff]
  exact h.inf_left_eq_bot_iff

theorem disjoint_right_iff (h : IsCompl y z) : Disjoint x z ↔ x ≤ y :=
  h.symm.disjoint_left_iff

theorem le_left_iff (h : IsCompl x y) : z ≤ x ↔ Disjoint z y :=
  h.disjoint_right_iff.symm

theorem le_right_iff (h : IsCompl x y) : z ≤ y ↔ Disjoint z x :=
  h.symm.le_left_iff

theorem left_le_iff (h : IsCompl x y) : x ≤ z ↔ ⊤ ≤ z⊔y :=
  h.dual.le_left_iff

theorem right_le_iff (h : IsCompl x y) : y ≤ z ↔ ⊤ ≤ z⊔x :=
  h.symm.left_le_iff

protected theorem antitone {x' y'} (h : IsCompl x y) (h' : IsCompl x' y') (hx : x ≤ x') : y' ≤ y :=
  h'.right_le_iff.2 <| le_transₓ h.symm.Codisjoint (sup_le_sup_left hx _)

theorem right_unique (hxy : IsCompl x y) (hxz : IsCompl x z) : y = z :=
  le_antisymmₓ (hxz.Antitone hxy <| le_reflₓ x) (hxy.Antitone hxz <| le_reflₓ x)

theorem left_unique (hxz : IsCompl x z) (hyz : IsCompl y z) : x = y :=
  hxz.symm.RightUnique hyz.symm

theorem sup_inf {x' y'} (h : IsCompl x y) (h' : IsCompl x' y') : IsCompl (x⊔x') (y⊓y') :=
  of_eq
    (by
      rw [inf_sup_right, ← inf_assoc, h.inf_eq_bot, bot_inf_eq, bot_sup_eq, inf_left_comm, h'.inf_eq_bot, inf_bot_eq])
    (by
      rw [sup_inf_left, @sup_comm _ _ x, sup_assoc, h.sup_eq_top, sup_top_eq, top_inf_eq, sup_assoc, sup_left_comm,
        h'.sup_eq_top, sup_top_eq])

theorem inf_sup {x' y'} (h : IsCompl x y) (h' : IsCompl x' y') : IsCompl (x⊓x') (y⊔y') :=
  (h.symm.sup_inf h'.symm).symm

end IsCompl

section

variable [Lattice α] [BoundedOrder α] {a b x : α}

@[simp]
theorem is_compl_to_dual_iff : IsCompl (toDual a) (toDual b) ↔ IsCompl a b :=
  ⟨IsCompl.of_dual, IsCompl.dual⟩

@[simp]
theorem is_compl_of_dual_iff {a b : αᵒᵈ} : IsCompl (ofDual a) (ofDual b) ↔ IsCompl a b :=
  ⟨IsCompl.dual, IsCompl.of_dual⟩

theorem is_compl_bot_top : IsCompl (⊥ : α) ⊤ :=
  IsCompl.of_eq bot_inf_eq sup_top_eq

theorem is_compl_top_bot : IsCompl (⊤ : α) ⊥ :=
  IsCompl.of_eq inf_bot_eq top_sup_eq

theorem eq_top_of_is_compl_bot (h : IsCompl x ⊥) : x = ⊤ :=
  sup_bot_eq.symm.trans h.sup_eq_top

theorem eq_top_of_bot_is_compl (h : IsCompl ⊥ x) : x = ⊤ :=
  eq_top_of_is_compl_bot h.symm

theorem eq_bot_of_is_compl_top (h : IsCompl x ⊤) : x = ⊥ :=
  eq_top_of_is_compl_bot h.dual

theorem eq_bot_of_top_is_compl (h : IsCompl ⊤ x) : x = ⊥ :=
  eq_top_of_bot_is_compl h.dual

end

/-- A complemented bounded lattice is one where every element has a (not necessarily unique)
complement. -/
class IsComplemented (α) [Lattice α] [BoundedOrder α] : Prop where
  exists_is_compl : ∀ a : α, ∃ b : α, IsCompl a b

export IsComplemented (exists_is_compl)

namespace IsComplemented

variable [Lattice α] [BoundedOrder α] [IsComplemented α]

instance : IsComplemented αᵒᵈ :=
  ⟨fun a =>
    let ⟨b, hb⟩ := exists_is_compl (show α from a)
    ⟨b, hb.dual⟩⟩

end IsComplemented

end IsCompl

section Nontrivial

variable [PartialOrderₓ α] [BoundedOrder α] [Nontrivial α]

theorem bot_ne_top : (⊥ : α) ≠ ⊤ := fun H => not_nontrivial_iff_subsingleton.mpr (subsingleton_of_bot_eq_top H) ‹_›

theorem top_ne_bot : (⊤ : α) ≠ ⊥ :=
  bot_ne_top.symm

theorem bot_lt_top : (⊥ : α) < ⊤ :=
  lt_top_iff_ne_top.2 bot_ne_top

end Nontrivial

section Bool

open Bool

instance : BoundedOrder Bool where
  top := true
  le_top := fun x => le_tt
  bot := false
  bot_le := fun x => ff_le

@[simp]
theorem top_eq_tt : ⊤ = tt :=
  rfl

@[simp]
theorem bot_eq_ff : ⊥ = ff :=
  rfl

end Bool

