/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathbin.Order.RelClasses

/-!
# Lexicographic ordering of lists.

The lexicographic order on `list α` is defined by `L < M` iff
* `[] < (a :: L)` for any `a` and `L`,
* `(a :: L) < (b :: M)` where `a < b`, or
* `(a :: L) < (a :: M)` where `L < M`.

## See also

Related files are:
* `data.finset.colex`: Colexicographic order on finite sets.
* `data.psigma.order`: Lexicographic order on `Σ' i, α i`.
* `data.pi.lex`: Lexicographic order on `Πₗ i, α i`.
* `data.sigma.order`: Lexicographic order on `Σ i, α i`.
* `data.prod.lex`: Lexicographic order on `α × β`.
-/


namespace List

open Nat

universe u

variable {α : Type u}

/-! ### lexicographic ordering -/


/-- Given a strict order `<` on `α`, the lexicographic strict order on `list α`, for which
`[a0, ..., an] < [b0, ..., b_k]` if `a0 < b0` or `a0 = b0` and `[a1, ..., an] < [b1, ..., bk]`.
The definition is given for any relation `r`, not only strict orders. -/
inductive Lex (r : α → α → Prop) : List α → List α → Prop
  | nil {a l} : lex [] (a :: l)
  | cons {a l₁ l₂} (h : lex l₁ l₂) : lex (a :: l₁) (a :: l₂)
  | rel {a₁ l₁ a₂ l₂} (h : r a₁ a₂) : lex (a₁ :: l₁) (a₂ :: l₂)

namespace Lex

theorem cons_iff {r : α → α → Prop} [IsIrrefl α r] {a l₁ l₂} : Lex r (a :: l₁) (a :: l₂) ↔ Lex r l₁ l₂ :=
  ⟨fun h => by
    cases' h with _ _ _ _ _ h _ _ _ _ h <;> [exact h, exact (irrefl_of r a h).elim], Lex.cons⟩

@[simp]
theorem not_nil_right (r : α → α → Prop) (l : List α) : ¬Lex r l [] :=
  fun.

instance is_order_connected (r : α → α → Prop) [IsOrderConnected α r] [IsTrichotomous α r] :
    IsOrderConnected (List α) (Lex r) :=
  ⟨fun l₁ =>
    match l₁ with
    | _, [], c :: l₃, nil => Or.inr nil
    | _, [], c :: l₃, rel _ => Or.inr nil
    | _, [], c :: l₃, cons _ => Or.inr nil
    | _, b :: l₂, c :: l₃, nil => Or.inl nil
    | a :: l₁, b :: l₂, c :: l₃, rel h => (IsOrderConnected.conn _ b _ h).imp rel rel
    | a :: l₁, b :: l₂, _ :: l₃, cons h => by
      rcases trichotomous_of r a b with (ab | rfl | ab)
      · exact Or.inl (rel ab)
        
      · exact (_match _ l₂ _ h).imp cons cons
        
      · exact Or.inr (rel ab)
        ⟩

instance is_trichotomous (r : α → α → Prop) [IsTrichotomous α r] : IsTrichotomous (List α) (Lex r) :=
  ⟨fun l₁ =>
    match l₁ with
    | [], [] => Or.inr (Or.inl rfl)
    | [], b :: l₂ => Or.inl nil
    | a :: l₁, [] => Or.inr (Or.inr nil)
    | a :: l₁, b :: l₂ => by
      rcases trichotomous_of r a b with (ab | rfl | ab)
      · exact Or.inl (rel ab)
        
      · exact (_match l₁ l₂).imp cons (Or.imp (congr_arg _) cons)
        
      · exact Or.inr (Or.inr (rel ab))
        ⟩

instance is_asymm (r : α → α → Prop) [IsAsymm α r] : IsAsymm (List α) (Lex r) :=
  ⟨fun l₁ =>
    match l₁ with
    | a :: l₁, b :: l₂, lex.rel h₁, lex.rel h₂ => asymm h₁ h₂
    | a :: l₁, b :: l₂, lex.rel h₁, lex.cons h₂ => asymm h₁ h₁
    | a :: l₁, b :: l₂, lex.cons h₁, lex.rel h₂ => asymm h₂ h₂
    | a :: l₁, b :: l₂, lex.cons h₁, lex.cons h₂ => _match _ _ h₁ h₂⟩

instance is_strict_total_order (r : α → α → Prop) [IsStrictTotalOrder' α r] : IsStrictTotalOrder' (List α) (Lex r) :=
  { is_strict_weak_order_of_is_order_connected with }

instance decidableRel [DecidableEq α] (r : α → α → Prop) [DecidableRel r] : DecidableRel (Lex r)
  | l₁, [] =>
    is_false fun h => by
      cases h
  | [], b :: l₂ => isTrue Lex.nil
  | a :: l₁, b :: l₂ => by
    have := DecidableRel l₁ l₂
    refine' decidableOfIff (r a b ∨ a = b ∧ lex r l₁ l₂) ⟨fun h => _, fun h => _⟩
    · rcases h with (h | ⟨rfl, h⟩)
      · exact lex.rel h
        
      · exact lex.cons h
        
      
    · rcases h with (_ | ⟨_, _, _, h⟩ | ⟨_, _, _, _, h⟩)
      · exact Or.inr ⟨rfl, h⟩
        
      · exact Or.inl h
        
      

theorem append_right (r : α → α → Prop) : ∀ {s₁ s₂} (t), Lex r s₁ s₂ → Lex r s₁ (s₂ ++ t)
  | _, _, t, nil => nil
  | _, _, t, cons h => cons (append_right _ h)
  | _, _, t, rel r => rel r

theorem append_left (R : α → α → Prop) {t₁ t₂} (h : Lex R t₁ t₂) : ∀ s, Lex R (s ++ t₁) (s ++ t₂)
  | [] => h
  | a :: l => cons (append_left l)

theorem imp {r s : α → α → Prop} (H : ∀ a b, r a b → s a b) : ∀ l₁ l₂, Lex r l₁ l₂ → Lex s l₁ l₂
  | _, _, nil => nil
  | _, _, cons h => cons (imp _ _ h)
  | _, _, rel r => rel (H _ _ r)

theorem to_ne : ∀ {l₁ l₂ : List α}, Lex (· ≠ ·) l₁ l₂ → l₁ ≠ l₂
  | _, _, cons h, e => to_ne h (List.cons.injₓ e).2
  | _, _, rel r, e => r (List.cons.injₓ e).1

theorem _root_.decidable.list.lex.ne_iff [DecidableEq α] {l₁ l₂ : List α} (H : length l₁ ≤ length l₂) :
    Lex (· ≠ ·) l₁ l₂ ↔ l₁ ≠ l₂ :=
  ⟨to_ne, fun h => by
    induction' l₁ with a l₁ IH generalizing l₂ <;> cases' l₂ with b l₂
    · contradiction
      
    · apply nil
      
    · exact (not_lt_of_geₓ H).elim (succ_pos _)
      
    · by_cases' ab : a = b
      · subst b
        apply cons
        exact IH (le_of_succ_le_succ H) (mt (congr_arg _) h)
        
      · exact rel ab
        
      ⟩

theorem ne_iff {l₁ l₂ : List α} (H : length l₁ ≤ length l₂) : Lex (· ≠ ·) l₁ l₂ ↔ l₁ ≠ l₂ := by
  classical <;> exact Decidable.List.Lex.ne_iff H

end Lex

--Note: this overrides an instance in core lean
instance hasLt' [LT α] : LT (List α) :=
  ⟨Lex (· < ·)⟩

theorem nil_lt_cons [LT α] (a : α) (l : List α) : [] < a :: l :=
  lex.nil

instance [LinearOrderₓ α] : LinearOrderₓ (List α) :=
  linearOrderOfSTO' (Lex (· < ·))

--Note: this overrides an instance in core lean
instance hasLe' [LinearOrderₓ α] : LE (List α) :=
  Preorderₓ.toHasLe _

end List

