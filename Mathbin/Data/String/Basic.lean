/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathbin.Data.List.Lex
import Mathbin.Data.Char

/-!
# Strings

Supplementary theorems about the `string` type.
-/


namespace Stringₓ

/-- `<` on string iterators. This coincides with `<` on strings as lists. -/
def ltb : Iterator → Iterator → Bool
  | s₁, s₂ => by
    cases s₂.has_next
    · exact ff
      
    cases h₁ : s₁.has_next
    · exact tt
      
    exact
      if s₁.curr = s₂.curr then
        have : s₁.next.2.length < s₁.2.length :=
          match s₁, h₁ with
          | ⟨_, a :: l⟩, h => Nat.lt_succ_selfₓ _
        ltb s₁.next s₂.next
      else s₁.curr < s₂.curr

instance hasLt' : LT Stringₓ :=
  ⟨fun s₁ s₂ => ltb s₁.mkIterator s₂.mkIterator⟩

instance decidableLt : @DecidableRel Stringₓ (· < ·) := by
  infer_instance

-- short-circuit type class inference
@[simp]
theorem lt_iff_to_list_lt : ∀ {s₁ s₂ : Stringₓ}, s₁ < s₂ ↔ s₁.toList < s₂.toList
  | ⟨i₁⟩, ⟨i₂⟩ => by
    suffices ∀ {p₁ p₂ s₁ s₂}, ltb ⟨p₁, s₁⟩ ⟨p₂, s₂⟩ ↔ s₁ < s₂ from this
    intros
    induction' s₁ with a s₁ IH generalizing p₁ p₂ s₂ <;> cases' s₂ with b s₂ <;> rw [ltb] <;> simp [← iterator.has_next]
    · rfl
      
    · exact iff_of_true rfl List.Lex.nil
      
    · exact iff_of_false Bool.ff_ne_tt (not_lt_of_lt List.Lex.nil)
      
    · dsimp' [← iterator.has_next, ← iterator.curr, ← iterator.next]
      split_ifs
      · subst b
        exact IH.trans list.lex.cons_iff.symm
        
      · simp
        refine' ⟨List.Lex.rel, fun e => _⟩
        cases e
        · cases h rfl
          
        assumption
        
      

instance hasLe : LE Stringₓ :=
  ⟨fun s₁ s₂ => ¬s₂ < s₁⟩

instance decidableLe : @DecidableRel Stringₓ (· ≤ ·) := by
  infer_instance

-- short-circuit type class inference
@[simp]
theorem le_iff_to_list_le {s₁ s₂ : Stringₓ} : s₁ ≤ s₂ ↔ s₁.toList ≤ s₂.toList :=
  (not_congr lt_iff_to_list_lt).trans not_ltₓ

theorem to_list_inj : ∀ {s₁ s₂}, toList s₁ = toList s₂ ↔ s₁ = s₂
  | ⟨s₁⟩, ⟨s₂⟩ => ⟨congr_arg _, congr_arg _⟩

theorem nil_as_string_eq_empty : [].asString = "" :=
  rfl

@[simp]
theorem to_list_empty : "".toList = [] :=
  rfl

theorem as_string_inv_to_list (s : Stringₓ) : s.toList.asString = s := by
  cases s
  rfl

@[simp]
theorem to_list_singleton (c : Charₓ) : (Stringₓ.singleton c).toList = [c] :=
  rfl

theorem to_list_nonempty : ∀ {s : Stringₓ}, s ≠ Stringₓ.empty → s.toList = s.head :: (s.popn 1).toList
  | ⟨s⟩, h => by
    cases s <;> [cases h rfl, rfl]

@[simp]
theorem head_empty : "".head = default :=
  rfl

@[simp]
theorem popn_empty {n : ℕ} : "".popn n = "" := by
  induction' n with n hn
  · rfl
    
  · rcases hs : "" with ⟨_ | ⟨hd, tl⟩⟩
    · rw [hs] at hn
      conv_rhs => rw [← hn]
      simp only [← popn, ← mk_iterator, ← iterator.nextn, ← iterator.next]
      
    · simpa only [to_list_inj] using hs
      
    

instance : LinearOrderₓ Stringₓ where
  lt := (· < ·)
  le := (· ≤ ·)
  decidableLt := by
    infer_instance
  decidableLe := Stringₓ.decidableLe
  DecidableEq := by
    infer_instance
  le_refl := fun a => le_iff_to_list_le.2 le_rfl
  le_trans := fun a b c => by
    simp only [← le_iff_to_list_le]
    exact fun h₁ h₂ => h₁.trans h₂
  le_total := fun a b => by
    simp only [← le_iff_to_list_le]
    exact le_totalₓ _ _
  le_antisymm := fun a b => by
    simp only [← le_iff_to_list_le, to_list_inj]
    apply le_antisymmₓ
  lt_iff_le_not_le := fun a b => by
    simp only [← le_iff_to_list_le, ← lt_iff_to_list_lt, ← lt_iff_le_not_leₓ]

end Stringₓ

open Stringₓ

theorem List.to_list_inv_as_string (l : List Charₓ) : l.asString.toList = l := by
  cases hl : l.as_string
  exact StringImp.mk.inj hl.symm

@[simp]
theorem List.length_as_string (l : List Charₓ) : l.asString.length = l.length :=
  rfl

@[simp]
theorem List.as_string_inj {l l' : List Charₓ} : l.asString = l'.asString ↔ l = l' :=
  ⟨fun h => by
    rw [← List.to_list_inv_as_string l, ← List.to_list_inv_as_string l', to_list_inj, h], fun h => h ▸ rfl⟩

@[simp]
theorem Stringₓ.length_to_list (s : Stringₓ) : s.toList.length = s.length := by
  rw [← Stringₓ.as_string_inv_to_list s, List.to_list_inv_as_string, List.length_as_string]

theorem List.as_string_eq {l : List Charₓ} {s : Stringₓ} : l.asString = s ↔ l = s.toList := by
  rw [← as_string_inv_to_list s, List.as_string_inj, as_string_inv_to_list s]

