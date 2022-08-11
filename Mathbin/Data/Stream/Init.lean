/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Mathbin.Data.Stream.Defs
import Mathbin.Tactic.Ext

/-!
# Streams a.k.a. infinite lists a.k.a. infinite sequences

This file used to be in the core library. It was moved to `mathlib` and renamed to `init` to avoid
name clashes.  -/


open Nat Function Option

universe u v w

namespace Streamₓ

variable {α : Type u} {β : Type v} {δ : Type w}

instance {α} [Inhabited α] : Inhabited (Streamₓ α) :=
  ⟨Streamₓ.const default⟩

protected theorem eta (s : Streamₓ α) : head s :: tail s = s :=
  funext fun i => by
    cases i <;> rfl

theorem nth_zero_cons (a : α) (s : Streamₓ α) : nth (a :: s) 0 = a :=
  rfl

theorem head_cons (a : α) (s : Streamₓ α) : head (a :: s) = a :=
  rfl

theorem tail_cons (a : α) (s : Streamₓ α) : tail (a :: s) = s :=
  rfl

theorem tail_drop (n : Nat) (s : Streamₓ α) : tail (drop n s) = drop n (tail s) :=
  funext fun i => by
    unfold tail drop
    simp [← nth, ← Nat.add_comm, ← Nat.add_left_comm]

theorem nth_drop (n m : Nat) (s : Streamₓ α) : nth (drop m s) n = nth s (n + m) :=
  rfl

theorem tail_eq_drop (s : Streamₓ α) : tail s = drop 1 s :=
  rfl

theorem drop_drop (n m : Nat) (s : Streamₓ α) : drop n (drop m s) = drop (n + m) s :=
  funext fun i => by
    unfold drop
    rw [Nat.add_assoc]

theorem nth_succ (n : Nat) (s : Streamₓ α) : nth s (succ n) = nth (tail s) n :=
  rfl

theorem drop_succ (n : Nat) (s : Streamₓ α) : drop (succ n) s = drop n (tail s) :=
  rfl

@[simp]
theorem head_drop {α} (a : Streamₓ α) (n : ℕ) : (a.drop n).head = a.nth n := by
  simp only [← drop, ← head, ← Nat.zero_add, ← Streamₓ.nth]

@[ext]
protected theorem ext {s₁ s₂ : Streamₓ α} : (∀ n, nth s₁ n = nth s₂ n) → s₁ = s₂ := fun h => funext h

theorem all_def (p : α → Prop) (s : Streamₓ α) : All p s = ∀ n, p (nth s n) :=
  rfl

theorem any_def (p : α → Prop) (s : Streamₓ α) : Any p s = ∃ n, p (nth s n) :=
  rfl

theorem mem_cons (a : α) (s : Streamₓ α) : a ∈ a :: s :=
  Exists.introₓ 0 rfl

theorem mem_cons_of_mem {a : α} {s : Streamₓ α} (b : α) : a ∈ s → a ∈ b :: s := fun ⟨n, h⟩ =>
  Exists.introₓ (succ n)
    (by
      rw [nth_succ, tail_cons, h])

theorem eq_or_mem_of_mem_cons {a b : α} {s : Streamₓ α} : a ∈ b :: s → a = b ∨ a ∈ s := fun ⟨n, h⟩ => by
  cases' n with n'
  · left
    exact h
    
  · right
    rw [nth_succ, tail_cons] at h
    exact ⟨n', h⟩
    

theorem mem_of_nth_eq {n : Nat} {s : Streamₓ α} {a : α} : a = nth s n → a ∈ s := fun h => Exists.introₓ n h

section Map

variable (f : α → β)

theorem drop_map (n : Nat) (s : Streamₓ α) : drop n (map f s) = map f (drop n s) :=
  Streamₓ.ext fun i => rfl

theorem nth_map (n : Nat) (s : Streamₓ α) : nth (map f s) n = f (nth s n) :=
  rfl

theorem tail_map (s : Streamₓ α) : tail (map f s) = map f (tail s) := by
  rw [tail_eq_drop]
  rfl

theorem head_map (s : Streamₓ α) : head (map f s) = f (head s) :=
  rfl

theorem map_eq (s : Streamₓ α) : map f s = f (head s) :: map f (tail s) := by
  rw [← Streamₓ.eta (map f s), tail_map, head_map]

theorem map_cons (a : α) (s : Streamₓ α) : map f (a :: s) = f a :: map f s := by
  rw [← Streamₓ.eta (map f (a :: s)), map_eq]
  rfl

theorem map_id (s : Streamₓ α) : map id s = s :=
  rfl

theorem map_map (g : β → δ) (f : α → β) (s : Streamₓ α) : map g (map f s) = map (g ∘ f) s :=
  rfl

theorem map_tail (s : Streamₓ α) : map f (tail s) = tail (map f s) :=
  rfl

theorem mem_map {a : α} {s : Streamₓ α} : a ∈ s → f a ∈ map f s := fun ⟨n, h⟩ =>
  Exists.introₓ n
    (by
      rw [nth_map, h])

theorem exists_of_mem_map {f} {b : β} {s : Streamₓ α} : b ∈ map f s → ∃ a, a ∈ s ∧ f a = b := fun ⟨n, h⟩ =>
  ⟨nth s n, ⟨n, rfl⟩, h.symm⟩

end Map

section Zip

variable (f : α → β → δ)

theorem drop_zip (n : Nat) (s₁ : Streamₓ α) (s₂ : Streamₓ β) : drop n (zip f s₁ s₂) = zip f (drop n s₁) (drop n s₂) :=
  Streamₓ.ext fun i => rfl

theorem nth_zip (n : Nat) (s₁ : Streamₓ α) (s₂ : Streamₓ β) : nth (zip f s₁ s₂) n = f (nth s₁ n) (nth s₂ n) :=
  rfl

theorem head_zip (s₁ : Streamₓ α) (s₂ : Streamₓ β) : head (zip f s₁ s₂) = f (head s₁) (head s₂) :=
  rfl

theorem tail_zip (s₁ : Streamₓ α) (s₂ : Streamₓ β) : tail (zip f s₁ s₂) = zip f (tail s₁) (tail s₂) :=
  rfl

theorem zip_eq (s₁ : Streamₓ α) (s₂ : Streamₓ β) : zip f s₁ s₂ = f (head s₁) (head s₂) :: zip f (tail s₁) (tail s₂) :=
  by
  rw [← Streamₓ.eta (zip f s₁ s₂)]
  rfl

end Zip

theorem mem_const (a : α) : a ∈ const a :=
  Exists.introₓ 0 rfl

theorem const_eq (a : α) : const a = a :: const a := by
  apply Streamₓ.ext
  intro n
  cases n <;> rfl

theorem tail_const (a : α) : tail (const a) = const a :=
  suffices tail (a :: const a) = const a by
    rwa [← const_eq] at this
  rfl

theorem map_const (f : α → β) (a : α) : map f (const a) = const (f a) :=
  rfl

theorem nth_const (n : Nat) (a : α) : nth (const a) n = a :=
  rfl

theorem drop_const (n : Nat) (a : α) : drop n (const a) = const a :=
  Streamₓ.ext fun i => rfl

theorem head_iterate (f : α → α) (a : α) : head (iterate f a) = a :=
  rfl

theorem tail_iterate (f : α → α) (a : α) : tail (iterate f a) = iterate f (f a) := by
  funext n
  induction' n with n' ih
  · rfl
    
  · unfold tail iterate
    unfold tail iterate  at ih
    rw [add_one] at ih
    dsimp'  at ih
    rw [add_one]
    dsimp'
    rw [ih]
    

theorem iterate_eq (f : α → α) (a : α) : iterate f a = a :: iterate f (f a) := by
  rw [← Streamₓ.eta (iterate f a)]
  rw [tail_iterate]
  rfl

theorem nth_zero_iterate (f : α → α) (a : α) : nth (iterate f a) 0 = a :=
  rfl

theorem nth_succ_iterate (n : Nat) (f : α → α) (a : α) : nth (iterate f a) (succ n) = nth (iterate f (f a)) n := by
  rw [nth_succ, tail_iterate]

section Bisim

variable (R : Streamₓ α → Streamₓ α → Prop)

-- mathport name: «expr ~ »
local infixl:50 " ~ " => R

def IsBisimulation :=
  ∀ ⦃s₁ s₂⦄, s₁ ~ s₂ → head s₁ = head s₂ ∧ tail s₁ ~ tail s₂

theorem nth_of_bisim (bisim : IsBisimulation R) :
    ∀ {s₁ s₂} (n), s₁ ~ s₂ → nth s₁ n = nth s₂ n ∧ drop (n + 1) s₁ ~ drop (n + 1) s₂
  | s₁, s₂, 0, h => bisim h
  | s₁, s₂, n + 1, h =>
    match bisim h with
    | ⟨h₁, trel⟩ => nth_of_bisim n trel

-- If two streams are bisimilar, then they are equal
theorem eq_of_bisim (bisim : IsBisimulation R) : ∀ {s₁ s₂}, s₁ ~ s₂ → s₁ = s₂ := fun s₁ s₂ r =>
  Streamₓ.ext fun n => And.elim_left (nth_of_bisim R bisim n r)

end Bisim

theorem bisim_simple (s₁ s₂ : Streamₓ α) : head s₁ = head s₂ → s₁ = tail s₁ → s₂ = tail s₂ → s₁ = s₂ :=
  fun hh ht₁ ht₂ =>
  eq_of_bisim (fun s₁ s₂ => head s₁ = head s₂ ∧ s₁ = tail s₁ ∧ s₂ = tail s₂)
    (fun s₁ s₂ ⟨h₁, h₂, h₃⟩ => by
      constructor
      exact h₁
      rw [← h₂, ← h₃]
      repeat'
          constructor <;>
        assumption)
    (And.intro hh (And.intro ht₁ ht₂))

theorem coinduction {s₁ s₂ : Streamₓ α} :
    head s₁ = head s₂ → (∀ (β : Type u) (fr : Streamₓ α → β), fr s₁ = fr s₂ → fr (tail s₁) = fr (tail s₂)) → s₁ = s₂ :=
  fun hh ht =>
  eq_of_bisim
    (fun s₁ s₂ => head s₁ = head s₂ ∧ ∀ (β : Type u) (fr : Streamₓ α → β), fr s₁ = fr s₂ → fr (tail s₁) = fr (tail s₂))
    (fun s₁ s₂ h =>
      have h₁ : head s₁ = head s₂ := And.elim_left h
      have h₂ : head (tail s₁) = head (tail s₂) := And.elim_right h α (@head α) h₁
      have h₃ :
        ∀ (β : Type u) (fr : Streamₓ α → β), fr (tail s₁) = fr (tail s₂) → fr (tail (tail s₁)) = fr (tail (tail s₂)) :=
        fun β fr => And.elim_right h β fun s => fr (tail s)
      And.intro h₁ (And.intro h₂ h₃))
    (And.intro hh ht)

theorem iterate_id (a : α) : iterate id a = const a :=
  coinduction rfl fun β fr ch => by
    rw [tail_iterate, tail_const]
    exact ch

attribute [local reducible] Streamₓ

theorem map_iterate (f : α → α) (a : α) : iterate f (f a) = map f (iterate f a) := by
  funext n
  induction' n with n' ih
  · rfl
    
  · unfold map iterate nth
    dsimp'
    unfold map iterate nth  at ih
    dsimp'  at ih
    rw [ih]
    

section Corec

theorem corec_def (f : α → β) (g : α → α) (a : α) : corec f g a = map f (iterate g a) :=
  rfl

theorem corec_eq (f : α → β) (g : α → α) (a : α) : corec f g a = f a :: corec f g (g a) := by
  rw [corec_def, map_eq, head_iterate, tail_iterate]
  rfl

theorem corec_id_id_eq_const (a : α) : corec id id a = const a := by
  rw [corec_def, map_id, iterate_id]

theorem corec_id_f_eq_iterate (f : α → α) (a : α) : corec id f a = iterate f a :=
  rfl

end Corec

section Corec'

theorem corec'_eq (f : α → β × α) (a : α) : corec' f a = (f a).1 :: corec' f (f a).2 :=
  corec_eq _ _ _

end Corec'

theorem unfolds_eq (g : α → β) (f : α → α) (a : α) : unfolds g f a = g a :: unfolds g f (f a) := by
  unfold unfolds
  rw [corec_eq]

theorem nth_unfolds_head_tail : ∀ (n : Nat) (s : Streamₓ α), nth (unfolds head tail s) n = nth s n := by
  intro n
  induction' n with n' ih
  · intro s
    rfl
    
  · intro s
    rw [nth_succ, nth_succ, unfolds_eq, tail_cons, ih]
    

theorem unfolds_head_eq : ∀ s : Streamₓ α, unfolds head tail s = s := fun s =>
  Streamₓ.ext fun n => nth_unfolds_head_tail n s

theorem interleave_eq (s₁ s₂ : Streamₓ α) : s₁ ⋈ s₂ = head s₁ :: head s₂ :: (tail s₁ ⋈ tail s₂) := by
  unfold interleave corec_on
  rw [corec_eq]
  dsimp'
  rw [corec_eq]
  rfl

theorem tail_interleave (s₁ s₂ : Streamₓ α) : tail (s₁ ⋈ s₂) = s₂ ⋈ tail s₁ := by
  unfold interleave corec_on
  rw [corec_eq]
  rfl

theorem interleave_tail_tail (s₁ s₂ : Streamₓ α) : tail s₁ ⋈ tail s₂ = tail (tail (s₁ ⋈ s₂)) := by
  rw [interleave_eq s₁ s₂]
  rfl

theorem nth_interleave_left : ∀ (n : Nat) (s₁ s₂ : Streamₓ α), nth (s₁ ⋈ s₂) (2 * n) = nth s₁ n
  | 0, s₁, s₂ => rfl
  | succ n, s₁, s₂ => by
    change nth (s₁ ⋈ s₂) (succ (succ (2 * n))) = nth s₁ (succ n)
    rw [nth_succ, nth_succ, interleave_eq, tail_cons, tail_cons, nth_interleave_left]
    rfl

theorem nth_interleave_right : ∀ (n : Nat) (s₁ s₂ : Streamₓ α), nth (s₁ ⋈ s₂) (2 * n + 1) = nth s₂ n
  | 0, s₁, s₂ => rfl
  | succ n, s₁, s₂ => by
    change nth (s₁ ⋈ s₂) (succ (succ (2 * n + 1))) = nth s₂ (succ n)
    rw [nth_succ, nth_succ, interleave_eq, tail_cons, tail_cons, nth_interleave_right]
    rfl

theorem mem_interleave_left {a : α} {s₁ : Streamₓ α} (s₂ : Streamₓ α) : a ∈ s₁ → a ∈ s₁ ⋈ s₂ := fun ⟨n, h⟩ =>
  Exists.introₓ (2 * n)
    (by
      rw [h, nth_interleave_left])

theorem mem_interleave_right {a : α} {s₁ : Streamₓ α} (s₂ : Streamₓ α) : a ∈ s₂ → a ∈ s₁ ⋈ s₂ := fun ⟨n, h⟩ =>
  Exists.introₓ (2 * n + 1)
    (by
      rw [h, nth_interleave_right])

theorem odd_eq (s : Streamₓ α) : odd s = even (tail s) :=
  rfl

theorem head_even (s : Streamₓ α) : head (even s) = head s :=
  rfl

theorem tail_even (s : Streamₓ α) : tail (even s) = even (tail (tail s)) := by
  unfold even
  rw [corec_eq]
  rfl

theorem even_cons_cons (a₁ a₂ : α) (s : Streamₓ α) : even (a₁ :: a₂ :: s) = a₁ :: even s := by
  unfold even
  rw [corec_eq]
  rfl

theorem even_tail (s : Streamₓ α) : even (tail s) = odd s :=
  rfl

theorem even_interleave (s₁ s₂ : Streamₓ α) : even (s₁ ⋈ s₂) = s₁ :=
  eq_of_bisim (fun s₁' s₁ => ∃ s₂, s₁' = even (s₁ ⋈ s₂))
    (fun s₁' s₁ ⟨s₂, h₁⟩ => by
      rw [h₁]
      constructor
      · rfl
        
      · exact
          ⟨tail s₂, by
            rw [interleave_eq, even_cons_cons, tail_cons]⟩
        )
    (Exists.introₓ s₂ rfl)

theorem interleave_even_odd (s₁ : Streamₓ α) : even s₁ ⋈ odd s₁ = s₁ :=
  eq_of_bisim (fun s' s => s' = even s ⋈ odd s)
    (fun s' s (h : s' = even s ⋈ odd s) => by
      rw [h]
      constructor
      · rfl
        
      · simp [← odd_eq, ← odd_eq, ← tail_interleave, ← tail_even]
        )
    rfl

theorem nth_even : ∀ (n : Nat) (s : Streamₓ α), nth (even s) n = nth s (2 * n)
  | 0, s => rfl
  | succ n, s => by
    change nth (even s) (succ n) = nth s (succ (succ (2 * n)))
    rw [nth_succ, nth_succ, tail_even, nth_even]
    rfl

theorem nth_odd : ∀ (n : Nat) (s : Streamₓ α), nth (odd s) n = nth s (2 * n + 1) := fun n s => by
  rw [odd_eq, nth_even]
  rfl

theorem mem_of_mem_even (a : α) (s : Streamₓ α) : a ∈ even s → a ∈ s := fun ⟨n, h⟩ =>
  Exists.introₓ (2 * n)
    (by
      rw [h, nth_even])

theorem mem_of_mem_odd (a : α) (s : Streamₓ α) : a ∈ odd s → a ∈ s := fun ⟨n, h⟩ =>
  Exists.introₓ (2 * n + 1)
    (by
      rw [h, nth_odd])

theorem nil_append_stream (s : Streamₓ α) : appendStream [] s = s :=
  rfl

theorem cons_append_stream (a : α) (l : List α) (s : Streamₓ α) : appendStream (a :: l) s = a :: appendStream l s :=
  rfl

theorem append_append_stream : ∀ (l₁ l₂ : List α) (s : Streamₓ α), l₁ ++ l₂ ++ₛ s = l₁ ++ₛ (l₂ ++ₛ s)
  | [], l₂, s => rfl
  | List.cons a l₁, l₂, s => by
    rw [List.cons_append, cons_append_stream, cons_append_stream, append_append_stream]

theorem map_append_stream (f : α → β) : ∀ (l : List α) (s : Streamₓ α), map f (l ++ₛ s) = List.map f l ++ₛ map f s
  | [], s => rfl
  | List.cons a l, s => by
    rw [cons_append_stream, List.map_cons, map_cons, cons_append_stream, map_append_stream]

theorem drop_append_stream : ∀ (l : List α) (s : Streamₓ α), drop l.length (l ++ₛ s) = s
  | [], s => by
    rfl
  | List.cons a l, s => by
    rw [List.length_cons, add_one, drop_succ, cons_append_stream, tail_cons, drop_append_stream]

theorem append_stream_head_tail (s : Streamₓ α) : [head s] ++ₛ tail s = s := by
  rw [cons_append_stream, nil_append_stream, Streamₓ.eta]

theorem mem_append_stream_right : ∀ {a : α} (l : List α) {s : Streamₓ α}, a ∈ s → a ∈ l ++ₛ s
  | a, [], s, h => h
  | a, List.cons b l, s, h =>
    have ih : a ∈ l ++ₛ s := mem_append_stream_right l h
    mem_cons_of_mem _ ih

theorem mem_append_stream_left : ∀ {a : α} {l : List α} (s : Streamₓ α), a ∈ l → a ∈ l ++ₛ s
  | a, [], s, h => absurd h (List.not_mem_nilₓ _)
  | a, List.cons b l, s, h =>
    Or.elim (List.eq_or_mem_of_mem_consₓ h) (fun aeqb : a = b => Exists.introₓ 0 aeqb) fun ainl : a ∈ l =>
      mem_cons_of_mem b (mem_append_stream_left s ainl)

@[simp]
theorem take_zero (s : Streamₓ α) : take 0 s = [] :=
  rfl

@[simp]
theorem take_succ (n : Nat) (s : Streamₓ α) : take (succ n) s = head s :: take n (tail s) :=
  rfl

@[simp]
theorem length_take (n : ℕ) (s : Streamₓ α) : (take n s).length = n := by
  induction n generalizing s <;> simp [*]

theorem nth_take_succ : ∀ (n : Nat) (s : Streamₓ α), List.nth (take (succ n) s) n = some (nth s n)
  | 0, s => rfl
  | n + 1, s => by
    rw [take_succ, add_one, List.nth, nth_take_succ]
    rfl

theorem append_take_drop : ∀ (n : Nat) (s : Streamₓ α), appendStream (take n s) (drop n s) = s := by
  intro n
  induction' n with n' ih
  · intro s
    rfl
    
  · intro s
    rw [take_succ, drop_succ, cons_append_stream, ih (tail s), Streamₓ.eta]
    

-- Take theorem reduces a proof of equality of infinite streams to an
-- induction over all their finite approximations.
theorem take_theorem (s₁ s₂ : Streamₓ α) : (∀ n : Nat, take n s₁ = take n s₂) → s₁ = s₂ := by
  intro h
  apply Streamₓ.ext
  intro n
  induction' n with n ih
  · have aux := h 1
    simp [← take] at aux
    exact aux
    
  · have h₁ : some (nth s₁ (succ n)) = some (nth s₂ (succ n)) := by
      rw [← nth_take_succ, ← nth_take_succ, h (succ (succ n))]
    injection h₁
    

protected theorem cycle_g_cons (a : α) (a₁ : α) (l₁ : List α) (a₀ : α) (l₀ : List α) :
    Streamₓ.cycleG (a, a₁ :: l₁, a₀, l₀) = (a₁, l₁, a₀, l₀) :=
  rfl

theorem cycle_eq : ∀ (l : List α) (h : l ≠ []), cycle l h = l ++ₛ cycle l h
  | [], h => absurd rfl h
  | List.cons a l, h =>
    have gen :
      ∀ l' a',
        corec Streamₓ.cycleF Streamₓ.cycleG (a', l', a, l) =
          a' :: l' ++ₛ corec Streamₓ.cycleF Streamₓ.cycleG (a, l, a, l) :=
      by
      intro l'
      induction' l' with a₁ l₁ ih
      · intros
        rw [corec_eq]
        rfl
        
      · intros
        rw [corec_eq, Streamₓ.cycle_g_cons, ih a₁]
        rfl
        
    gen l a

theorem mem_cycle {a : α} {l : List α} : ∀ h : l ≠ [], a ∈ l → a ∈ cycle l h := fun h ainl => by
  rw [cycle_eq]
  exact mem_append_stream_left _ ainl

theorem cycle_singleton (a : α) (h : [a] ≠ []) : cycle [a] h = const a :=
  coinduction rfl fun β fr ch => by
    rwa [cycle_eq, const_eq]

theorem tails_eq (s : Streamₓ α) : tails s = tail s :: tails (tail s) := by
  unfold tails <;> rw [corec_eq] <;> rfl

theorem nth_tails : ∀ (n : Nat) (s : Streamₓ α), nth (tails s) n = drop n (tail s) := by
  intro n
  induction' n with n' ih
  · intros
    rfl
    
  · intro s
    rw [nth_succ, drop_succ, tails_eq, tail_cons, ih]
    

theorem tails_eq_iterate (s : Streamₓ α) : tails s = iterate tail (tail s) :=
  rfl

theorem inits_core_eq (l : List α) (s : Streamₓ α) : initsCore l s = l :: initsCore (l ++ [head s]) (tail s) := by
  unfold inits_core corec_on
  rw [corec_eq]
  rfl

theorem tail_inits (s : Streamₓ α) : tail (inits s) = initsCore [head s, head (tail s)] (tail (tail s)) := by
  unfold inits
  rw [inits_core_eq]
  rfl

theorem inits_tail (s : Streamₓ α) : inits (tail s) = initsCore [head (tail s)] (tail (tail s)) :=
  rfl

theorem cons_nth_inits_core :
    ∀ (a : α) (n : Nat) (l : List α) (s : Streamₓ α), a :: nth (initsCore l s) n = nth (initsCore (a :: l) s) n := by
  intro a n
  induction' n with n' ih
  · intros
    rfl
    
  · intro l s
    rw [nth_succ, inits_core_eq, tail_cons, ih, inits_core_eq (a :: l) s]
    rfl
    

theorem nth_inits : ∀ (n : Nat) (s : Streamₓ α), nth (inits s) n = take (succ n) s := by
  intro n
  induction' n with n' ih
  · intros
    rfl
    
  · intros
    rw [nth_succ, take_succ, ← ih, tail_inits, inits_tail, cons_nth_inits_core]
    

theorem inits_eq (s : Streamₓ α) : inits s = [head s] :: map (List.cons (head s)) (inits (tail s)) := by
  apply Streamₓ.ext
  intro n
  cases n
  · rfl
    
  · rw [nth_inits, nth_succ, tail_cons, nth_map, nth_inits]
    rfl
    

theorem zip_inits_tails (s : Streamₓ α) : zip appendStream (inits s) (tails s) = const s := by
  apply Streamₓ.ext
  intro n
  rw [nth_zip, nth_inits, nth_tails, nth_const, take_succ, cons_append_stream, append_take_drop, Streamₓ.eta]

theorem identity (s : Streamₓ α) : pure id ⊛ s = s :=
  rfl

theorem composition (g : Streamₓ (β → δ)) (f : Streamₓ (α → β)) (s : Streamₓ α) : pure comp ⊛ g ⊛ f ⊛ s = g ⊛ (f ⊛ s) :=
  rfl

theorem homomorphism (f : α → β) (a : α) : pure f ⊛ pure a = pure (f a) :=
  rfl

theorem interchange (fs : Streamₓ (α → β)) (a : α) : fs ⊛ pure a = (pure fun f : α → β => f a) ⊛ fs :=
  rfl

theorem map_eq_apply (f : α → β) (s : Streamₓ α) : map f s = pure f ⊛ s :=
  rfl

theorem nth_nats (n : Nat) : nth nats n = n :=
  rfl

theorem nats_eq : nats = 0 :: map succ nats := by
  apply Streamₓ.ext
  intro n
  cases n
  rfl
  rw [nth_succ]
  rfl

end Streamₓ

