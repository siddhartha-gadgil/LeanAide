/-
Copyright (c) 2014 Floris van Doorn (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
import Mathbin.Algebra.Order.Ring

/-!
# Basic operations on the natural numbers

This file contains:
- instances on the natural numbers
- some basic lemmas about natural numbers
- extra recursors:
  * `le_rec_on`, `le_induction`: recursion and induction principles starting at non-zero numbers
  * `decreasing_induction`: recursion growing downwards
  * `le_rec_on'`, `decreasing_induction'`: versions with slightly weaker assumptions
  * `strong_rec'`: recursion based on strong inequalities
- decidability instances on predicates about the natural numbers

-/


universe u v

/-! ### instances -/


instance : Nontrivial ℕ :=
  ⟨⟨0, 1, Nat.zero_ne_one⟩⟩

instance : CommSemiringₓ ℕ where
  add := Nat.add
  add_assoc := Nat.add_assoc
  zero := Nat.zero
  zero_add := Nat.zero_add
  add_zero := Nat.add_zero
  add_comm := Nat.add_comm
  mul := Nat.mul
  mul_assoc := Nat.mul_assoc
  one := Nat.succ Nat.zero
  one_mul := Nat.one_mul
  mul_one := Nat.mul_one
  left_distrib := Nat.left_distrib
  right_distrib := Nat.right_distrib
  zero_mul := Nat.zero_mul
  mul_zero := Nat.mul_zero
  mul_comm := Nat.mul_comm
  natCast := id
  nat_cast_zero := rfl
  nat_cast_succ := fun n => rfl
  nsmul := fun m n => m * n
  nsmul_zero' := Nat.zero_mul
  nsmul_succ' := fun n x => by
    rw [Nat.succ_eq_add_one, Nat.add_comm, Nat.right_distrib, Nat.one_mul]

instance : LinearOrderedSemiring Nat :=
  { Nat.commSemiring, Nat.linearOrder with add_left_cancel := @Nat.add_left_cancel, lt := Nat.Lt,
    add_le_add_left := @Nat.add_le_add_leftₓ, le_of_add_le_add_left := @Nat.le_of_add_le_add_leftₓ,
    zero_le_one := Nat.le_of_ltₓ (Nat.zero_lt_succₓ 0), mul_lt_mul_of_pos_left := @Nat.mul_lt_mul_of_pos_leftₓ,
    mul_lt_mul_of_pos_right := @Nat.mul_lt_mul_of_pos_rightₓ, DecidableEq := Nat.decidableEq,
    exists_pair_ne := ⟨0, 1, ne_of_ltₓ Nat.zero_lt_oneₓ⟩ }

-- all the fields are already included in the linear_ordered_semiring instance
instance : LinearOrderedCancelAddCommMonoid ℕ :=
  { Nat.linearOrderedSemiring with add_left_cancel := @Nat.add_left_cancel }

instance : LinearOrderedCommMonoidWithZero ℕ :=
  { Nat.linearOrderedSemiring, (inferInstance : CommMonoidWithZero ℕ) with
    mul_le_mul_left := fun a b h c => Nat.mul_le_mul_leftₓ c h }

instance : OrderedCommSemiring ℕ :=
  { Nat.commSemiring, Nat.linearOrderedSemiring with }

/-! Extra instances to short-circuit type class resolution -/


instance : AddCommMonoidₓ Nat := by
  infer_instance

instance : AddMonoidₓ Nat := by
  infer_instance

instance : Monoidₓ Nat := by
  infer_instance

instance : CommMonoidₓ Nat := by
  infer_instance

instance : CommSemigroupₓ Nat := by
  infer_instance

instance : Semigroupₓ Nat := by
  infer_instance

instance : AddCommSemigroupₓ Nat := by
  infer_instance

instance : AddSemigroupₓ Nat := by
  infer_instance

instance : Distribₓ Nat := by
  infer_instance

instance : Semiringₓ Nat := by
  infer_instance

instance : OrderedSemiring Nat := by
  infer_instance

instance Nat.orderBot : OrderBot ℕ where
  bot := 0
  bot_le := Nat.zero_leₓ

instance : CanonicallyOrderedCommSemiring ℕ :=
  { Nat.nontrivial, Nat.orderBot, (inferInstance : OrderedAddCommMonoid ℕ), (inferInstance : LinearOrderedSemiring ℕ),
    (inferInstance : CommSemiringₓ ℕ) with exists_add_of_le := fun a b h => (Nat.Le.dest h).imp fun _ => Eq.symm,
    le_self_add := Nat.le_add_rightₓ, eq_zero_or_eq_zero_of_mul_eq_zero := fun a b => Nat.eq_zero_of_mul_eq_zero }

instance : CanonicallyLinearOrderedAddMonoid ℕ :=
  { (inferInstance : CanonicallyOrderedAddMonoid ℕ), Nat.linearOrder with }

instance Nat.Subtype.orderBot (s : Set ℕ) [DecidablePred (· ∈ s)] [h : Nonempty s] : OrderBot s where
  bot := ⟨Nat.findₓ (nonempty_subtype.1 h), Nat.find_specₓ (nonempty_subtype.1 h)⟩
  bot_le := fun x => Nat.find_min'ₓ _ x.2

instance Nat.Subtype.semilatticeSup (s : Set ℕ) : SemilatticeSup s :=
  { Subtype.linearOrder s, LinearOrderₓ.toLattice with }

theorem Nat.Subtype.coe_bot {s : Set ℕ} [DecidablePred (· ∈ s)] [h : Nonempty s] :
    ((⊥ : s) : ℕ) = Nat.findₓ (nonempty_subtype.1 h) :=
  rfl

protected theorem Nat.nsmul_eq_mul (m n : ℕ) : m • n = m * n :=
  rfl

theorem Nat.eq_of_mul_eq_mul_rightₓ {n m k : ℕ} (Hm : 0 < m) (H : n * m = k * m) : n = k := by
  rw [mul_comm n m, mul_comm k m] at H <;> exact Nat.eq_of_mul_eq_mul_leftₓ Hm H

instance Nat.cancelCommMonoidWithZero : CancelCommMonoidWithZero ℕ :=
  { (inferInstance : CommMonoidWithZero ℕ) with
    mul_left_cancel_of_ne_zero := fun _ _ _ h1 h2 => Nat.eq_of_mul_eq_mul_leftₓ (Nat.pos_of_ne_zeroₓ h1) h2,
    mul_right_cancel_of_ne_zero := fun _ _ _ h1 h2 => Nat.eq_of_mul_eq_mul_rightₓ (Nat.pos_of_ne_zeroₓ h1) h2 }

attribute [simp]
  Nat.not_lt_zeroₓ Nat.succ_ne_zero Nat.succ_ne_self Nat.zero_ne_one Nat.one_ne_zero Nat.zero_ne_bit1 Nat.bit1_ne_zero Nat.bit0_ne_one Nat.one_ne_bit0 Nat.bit0_ne_bit1 Nat.bit1_ne_bit0

/-!
Inject some simple facts into the type class system.
This `fact` should not be confused with the factorial function `nat.fact`!
-/


section Facts

instance succ_pos'' (n : ℕ) : Fact (0 < n.succ) :=
  ⟨n.succ_pos⟩

instance pos_of_one_lt (n : ℕ) [h : Fact (1 < n)] : Fact (0 < n) :=
  ⟨lt_transₓ zero_lt_one h.1⟩

end Facts

variable {m n k : ℕ}

namespace Nat

/-!
### Recursion and `set.range`
-/


section Set

open Set

theorem zero_union_range_succ : {0} ∪ Range succ = univ := by
  ext n
  cases n <;> simp

variable {α : Type _}

theorem range_of_succ (f : ℕ → α) : {f 0} ∪ Range (f ∘ succ) = Range f := by
  rw [← image_singleton, range_comp, ← image_union, zero_union_range_succ, image_univ]

theorem range_rec {α : Type _} (x : α) (f : ℕ → α → α) :
    (Set.Range fun n => Nat.rec x f n : Set α) = {x} ∪ Set.Range fun n => Nat.rec (f 0 x) (f ∘ succ) n := by
  convert (range_of_succ _).symm
  ext n
  induction' n with n ihn
  · rfl
    
  · dsimp'  at ihn⊢
    rw [ihn]
    

theorem range_cases_on {α : Type _} (x : α) (f : ℕ → α) :
    (Set.Range fun n => Nat.casesOn n x f : Set α) = {x} ∪ Set.Range f :=
  (range_of_succ _).symm

end Set

/-! ### The units of the natural numbers as a `monoid` and `add_monoid` -/


theorem units_eq_one (u : ℕˣ) : u = 1 :=
  Units.ext <| Nat.eq_one_of_dvd_one ⟨u.inv, u.val_inv.symm⟩

theorem add_units_eq_zero (u : AddUnits ℕ) : u = 0 :=
  AddUnits.ext <| (Nat.eq_zero_of_add_eq_zero u.val_neg).1

@[simp]
protected theorem is_unit_iff {n : ℕ} : IsUnit n ↔ n = 1 :=
  Iff.intro
    (fun ⟨u, hu⟩ =>
      match n, u, hu, Nat.units_eq_one u with
      | _, _, rfl, rfl => rfl)
    fun h => h.symm ▸ ⟨1, rfl⟩

instance uniqueUnits : Unique ℕˣ where
  default := 1
  uniq := Nat.units_eq_one

instance uniqueAddUnits : Unique (AddUnits ℕ) where
  default := 0
  uniq := Nat.add_units_eq_zero

/-! ### Equalities and inequalities involving zero and one -/


theorem one_le_iff_ne_zero {n : ℕ} : 1 ≤ n ↔ n ≠ 0 :=
  (show 1 ≤ n ↔ 0 < n from Iff.rfl).trans pos_iff_ne_zero

theorem one_lt_iff_ne_zero_and_ne_one : ∀ {n : ℕ}, 1 < n ↔ n ≠ 0 ∧ n ≠ 1
  | 0 => by
    decide
  | 1 => by
    decide
  | n + 2 => by
    decide

protected theorem mul_ne_zero {n m : ℕ} (n0 : n ≠ 0) (m0 : m ≠ 0) : n * m ≠ 0
  | nm => (eq_zero_of_mul_eq_zero nm).elim n0 m0

@[simp]
protected theorem mul_eq_zero {a b : ℕ} : a * b = 0 ↔ a = 0 ∨ b = 0 :=
  Iff.intro eq_zero_of_mul_eq_zero
    (by
      simp (config := { contextual := true })[← or_imp_distrib])

@[simp]
protected theorem zero_eq_mul {a b : ℕ} : 0 = a * b ↔ a = 0 ∨ b = 0 := by
  rw [eq_comm, Nat.mul_eq_zero]

theorem eq_zero_of_double_le {a : ℕ} (h : 2 * a ≤ a) : a = 0 :=
  add_right_eq_selfₓ.mp <| le_antisymmₓ ((two_mul a).symm.trans_le h) le_add_self

theorem eq_zero_of_mul_le {a b : ℕ} (hb : 2 ≤ b) (h : b * a ≤ a) : a = 0 :=
  eq_zero_of_double_le <| le_transₓ (Nat.mul_le_mul_rightₓ _ hb) h

theorem le_zero_iffₓ {i : ℕ} : i ≤ 0 ↔ i = 0 :=
  ⟨Nat.eq_zero_of_le_zeroₓ, fun h => h ▸ le_reflₓ i⟩

theorem zero_max {m : ℕ} : max 0 m = m :=
  max_eq_rightₓ (zero_le _)

@[simp]
theorem min_eq_zero_iff {m n : ℕ} : min m n = 0 ↔ m = 0 ∨ n = 0 := by
  constructor
  · intro h
    cases' le_totalₓ n m with H H
    · simpa [← H] using Or.inr h
      
    · simpa [← H] using Or.inl h
      
    
  · rintro (rfl | rfl) <;> simp
    

@[simp]
theorem max_eq_zero_iff {m n : ℕ} : max m n = 0 ↔ m = 0 ∧ n = 0 := by
  constructor
  · intro h
    cases' le_totalₓ n m with H H
    · simp only [← H, ← max_eq_leftₓ] at h
      exact ⟨h, le_antisymmₓ (H.trans h.le) (zero_le _)⟩
      
    · simp only [← H, ← max_eq_rightₓ] at h
      exact ⟨le_antisymmₓ (H.trans h.le) (zero_le _), h⟩
      
    
  · rintro ⟨rfl, rfl⟩
    simp
    

theorem add_eq_max_iff {n m : ℕ} : n + m = max n m ↔ n = 0 ∨ m = 0 := by
  rw [← min_eq_zero_iff]
  cases' le_totalₓ n m with H H <;> simp [← H]

theorem add_eq_min_iff {n m : ℕ} : n + m = min n m ↔ n = 0 ∧ m = 0 := by
  rw [← max_eq_zero_iff]
  cases' le_totalₓ n m with H H <;> simp [← H]

theorem one_le_of_lt {n m : ℕ} (h : n < m) : 1 ≤ m :=
  lt_of_le_of_ltₓ (Nat.zero_leₓ _) h

theorem eq_one_of_mul_eq_one_right {m n : ℕ} (H : m * n = 1) : m = 1 :=
  eq_one_of_dvd_one ⟨n, H.symm⟩

theorem eq_one_of_mul_eq_one_left {m n : ℕ} (H : m * n = 1) : n = 1 :=
  eq_one_of_mul_eq_one_right
    (by
      rwa [mul_comm])

/-! ### `succ` -/


theorem _root_.has_lt.lt.nat_succ_le {n m : ℕ} (h : n < m) : succ n ≤ m :=
  succ_le_of_ltₓ h

theorem succ_eq_one_add (n : ℕ) : n.succ = 1 + n := by
  rw [Nat.succ_eq_add_one, Nat.add_comm]

theorem eq_of_lt_succ_of_not_lt {a b : ℕ} (h1 : a < b + 1) (h2 : ¬a < b) : a = b :=
  have h3 : a ≤ b := le_of_lt_succₓ h1
  Or.elim (eq_or_lt_of_not_ltₓ h2) (fun h => h) fun h => absurd h (not_lt_of_geₓ h3)

theorem eq_of_le_of_lt_succ {n m : ℕ} (h₁ : n ≤ m) (h₂ : m < n + 1) : m = n :=
  Nat.le_antisymmₓ (le_of_succ_le_succₓ h₂) h₁

theorem one_add (n : ℕ) : 1 + n = succ n := by
  simp [← add_commₓ]

@[simp]
theorem succ_pos' {n : ℕ} : 0 < succ n :=
  succ_posₓ n

theorem succ_inj' {n m : ℕ} : succ n = succ m ↔ n = m :=
  ⟨succ.injₓ, congr_arg _⟩

theorem succ_injective : Function.Injective Nat.succ := fun x y => succ.injₓ

theorem succ_ne_succ {n m : ℕ} : succ n ≠ succ m ↔ n ≠ m :=
  succ_injective.ne_iff

@[simp]
theorem succ_succ_ne_one (n : ℕ) : n.succ.succ ≠ 1 :=
  succ_ne_succ.mpr n.succ_ne_zero

@[simp]
theorem one_lt_succ_succ (n : ℕ) : 1 < n.succ.succ :=
  succ_lt_succ <| succ_posₓ n

theorem two_le_iff : ∀ n, 2 ≤ n ↔ n ≠ 0 ∧ n ≠ 1
  | 0 => by
    simp
  | 1 => by
    simp
  | n + 2 => by
    simp

theorem succ_le_succ_iff {m n : ℕ} : succ m ≤ succ n ↔ m ≤ n :=
  ⟨le_of_succ_le_succₓ, succ_le_succₓ⟩

theorem max_succ_succ {m n : ℕ} : max (succ m) (succ n) = succ (max m n) := by
  by_cases' h1 : m ≤ n
  rw [max_eq_rightₓ h1, max_eq_rightₓ (succ_le_succ h1)]
  · rw [not_leₓ] at h1
    have h2 := le_of_ltₓ h1
    rw [max_eq_leftₓ h2, max_eq_leftₓ (succ_le_succ h2)]
    

theorem not_succ_lt_self {n : ℕ} : ¬succ n < n :=
  not_lt_of_geₓ (Nat.le_succₓ _)

theorem lt_succ_iffₓ {m n : ℕ} : m < succ n ↔ m ≤ n :=
  ⟨le_of_lt_succₓ, lt_succ_of_leₓ⟩

theorem succ_le_iff {m n : ℕ} : succ m ≤ n ↔ m < n :=
  ⟨lt_of_succ_leₓ, succ_le_of_ltₓ⟩

theorem lt_iff_add_one_le {m n : ℕ} : m < n ↔ m + 1 ≤ n := by
  rw [succ_le_iff]

-- Just a restatement of `nat.lt_succ_iff` using `+1`.
theorem lt_add_one_iff {a b : ℕ} : a < b + 1 ↔ a ≤ b :=
  lt_succ_iff

-- A flipped version of `lt_add_one_iff`.
theorem lt_one_add_iff {a b : ℕ} : a < 1 + b ↔ a ≤ b := by
  simp only [← add_commₓ, ← lt_succ_iff]

-- This is true reflexively, by the definition of `≤` on ℕ,
-- but it's still useful to have, to convince Lean to change the syntactic type.
theorem add_one_le_iff {a b : ℕ} : a + 1 ≤ b ↔ a < b :=
  Iff.refl _

theorem one_add_le_iff {a b : ℕ} : 1 + a ≤ b ↔ a < b := by
  simp only [← add_commₓ, ← add_one_le_iff]

theorem of_le_succ {n m : ℕ} (H : n ≤ m.succ) : n ≤ m ∨ n = m.succ :=
  H.lt_or_eq_dec.imp le_of_lt_succₓ id

theorem succ_lt_succ_iff {m n : ℕ} : succ m < succ n ↔ m < n :=
  ⟨lt_of_succ_lt_succₓ, succ_lt_succₓ⟩

@[simp]
theorem lt_one_iff {n : ℕ} : n < 1 ↔ n = 0 :=
  lt_succ_iffₓ.trans le_zero_iffₓ

theorem div_le_iff_le_mul_add_pred {m n k : ℕ} (n0 : 0 < n) : m / n ≤ k ↔ m ≤ n * k + (n - 1) := by
  rw [← lt_succ_iff, div_lt_iff_lt_mul n0, succ_mul, mul_comm]
  cases n
  · cases n0
    
  exact lt_succ_iff

theorem two_lt_of_ne : ∀ {n}, n ≠ 0 → n ≠ 1 → n ≠ 2 → 2 < n
  | 0, h, _, _ => (h rfl).elim
  | 1, _, h, _ => (h rfl).elim
  | 2, _, _, h => (h rfl).elim
  | n + 3, _, _, _ => by
    decide

theorem forall_lt_succ {P : ℕ → Prop} {n : ℕ} : (∀, ∀ m < n.succ, ∀, P m) ↔ (∀, ∀ m < n, ∀, P m) ∧ P n :=
  ⟨fun H => ⟨fun m hm => H m (lt_succ_iffₓ.2 hm.le), H n (lt_succ_selfₓ n)⟩, by
    rintro ⟨H, hn⟩ m hm
    rcases eq_or_lt_of_le (lt_succ_iff.1 hm) with (rfl | hmn)
    · exact hn
      
    · exact H m hmn
      ⟩

theorem exists_lt_succ {P : ℕ → Prop} {n : ℕ} : (∃ m < n.succ, P m) ↔ (∃ m < n, P m) ∨ P n := by
  rw [← not_iff_not]
  push_neg
  exact forall_lt_succ

/-! ### `add` -/


-- Sometimes a bare `nat.add` or similar appears as a consequence of unfolding
-- during pattern matching. These lemmas package them back up as typeclass
-- mediated operations.
@[simp]
theorem add_def {a b : ℕ} : Nat.add a b = a + b :=
  rfl

@[simp]
theorem mul_def {a b : ℕ} : Nat.mul a b = a * b :=
  rfl

theorem exists_eq_add_of_le : ∀ {m n : ℕ}, m ≤ n → ∃ k : ℕ, n = m + k
  | 0, 0, h =>
    ⟨0, by
      simp ⟩
  | 0, n + 1, h =>
    ⟨n + 1, by
      simp ⟩
  | m + 1, n + 1, h =>
    let ⟨k, hk⟩ := exists_eq_add_of_le (Nat.le_of_succ_le_succₓ h)
    ⟨k, by
      simp [← hk, ← add_commₓ, ← add_left_commₓ]⟩

theorem exists_eq_add_of_lt : ∀ {m n : ℕ}, m < n → ∃ k : ℕ, n = m + k + 1
  | 0, 0, h => False.elim <| lt_irreflₓ _ h
  | 0, n + 1, h =>
    ⟨n, by
      simp ⟩
  | m + 1, n + 1, h =>
    let ⟨k, hk⟩ := exists_eq_add_of_le (Nat.le_of_succ_le_succₓ h)
    ⟨k, by
      simp [← hk]⟩

theorem add_pos_left {m : ℕ} (h : 0 < m) (n : ℕ) : 0 < m + n :=
  calc
    m + n > 0 + n := Nat.add_lt_add_rightₓ h n
    _ = n := Nat.zero_add n
    _ ≥ 0 := zero_le n
    

theorem add_pos_right (m : ℕ) {n : ℕ} (h : 0 < n) : 0 < m + n := by
  rw [add_commₓ]
  exact add_pos_left h m

theorem add_pos_iff_pos_or_pos (m n : ℕ) : 0 < m + n ↔ 0 < m ∨ 0 < n :=
  Iff.intro
    (by
      intro h
      cases' m with m
      · simp [← zero_addₓ] at h
        exact Or.inr h
        
      exact Or.inl (succ_pos _))
    (by
      intro h
      cases' h with mpos npos
      · apply add_pos_left mpos
        
      apply add_pos_right _ npos)

theorem add_eq_one_iff : ∀ {a b : ℕ}, a + b = 1 ↔ a = 0 ∧ b = 1 ∨ a = 1 ∧ b = 0
  | 0, 0 => by
    decide
  | 1, 0 => by
    decide
  | a + 2, _ => by
    rw [add_right_commₓ] <;>
      exact by
        decide
  | _, b + 1 => by
    rw [← add_assocₓ] <;> simp only [← Nat.succ_inj', ← Nat.succ_ne_zero] <;> simp

theorem le_add_one_iff {i j : ℕ} : i ≤ j + 1 ↔ i ≤ j ∨ i = j + 1 :=
  ⟨fun h =>
    match Nat.eq_or_lt_of_leₓ h with
    | Or.inl h => Or.inr h
    | Or.inr h => Or.inl <| Nat.le_of_succ_le_succₓ h,
    Or.ndrec (fun h => le_transₓ h <| Nat.le_add_rightₓ _ _) le_of_eqₓ⟩

theorem le_and_le_add_one_iff {x a : ℕ} : a ≤ x ∧ x ≤ a + 1 ↔ x = a ∨ x = a + 1 := by
  rw [le_add_one_iff, and_or_distrib_left, ← le_antisymm_iffₓ, eq_comm, and_iff_right_of_imp]
  rintro rfl
  exact a.le_succ

theorem add_succ_lt_add {a b c d : ℕ} (hab : a < b) (hcd : c < d) : a + c + 1 < b + d := by
  rw [add_assocₓ]
  exact add_lt_add_of_lt_of_le hab (Nat.succ_le_iff.2 hcd)

/-! ### `pred` -/


@[simp]
theorem add_succ_sub_one (n m : ℕ) : n + succ m - 1 = n + m := by
  rw [add_succ, succ_sub_one]

@[simp]
theorem succ_add_sub_one (n m : ℕ) : succ n + m - 1 = n + m := by
  rw [succ_add, succ_sub_one]

theorem pred_eq_sub_one (n : ℕ) : pred n = n - 1 :=
  rfl

theorem pred_eq_of_eq_succ {m n : ℕ} (H : m = n.succ) : m.pred = n := by
  simp [← H]

@[simp]
theorem pred_eq_succ_iff {n m : ℕ} : pred n = succ m ↔ n = m + 2 := by
  cases n <;> constructor <;> rintro ⟨⟩ <;> rfl

theorem pred_sub (n m : ℕ) : pred n - m = pred (n - m) := by
  rw [← Nat.sub_one, Nat.sub_sub, one_add, sub_succ]

theorem le_pred_of_ltₓ {n m : ℕ} (h : m < n) : m ≤ n - 1 :=
  Nat.sub_le_sub_rightₓ h 1

theorem le_of_pred_lt {m n : ℕ} : pred m < n → m ≤ n :=
  match m with
  | 0 => le_of_ltₓ
  | m + 1 => id

/-- This ensures that `simp` succeeds on `pred (n + 1) = n`. -/
@[simp]
theorem pred_one_add (n : ℕ) : pred (1 + n) = n := by
  rw [add_commₓ, add_one, pred_succ]

theorem pred_le_iff {n m : ℕ} : pred n ≤ m ↔ n ≤ succ m :=
  ⟨le_succ_of_pred_leₓ, by
    cases n
    · exact fun h => zero_le m
      
    exact le_of_succ_le_succ⟩

/-! ### `sub`

Most lemmas come from the `has_ordered_sub` instance on `ℕ`. -/


instance : HasOrderedSub ℕ := by
  constructor
  intro m n k
  induction' n with n ih generalizing k
  · simp
    
  · simp only [← sub_succ, ← add_succ, ← succ_add, ← ih, ← pred_le_iff]
    

theorem lt_pred_iff {n m : ℕ} : n < pred m ↔ succ n < m :=
  show n < m - 1 ↔ n + 1 < m from lt_tsub_iff_right

theorem lt_of_lt_pred {a b : ℕ} (h : a < b - 1) : a < b :=
  lt_of_succ_ltₓ (lt_pred_iff.1 h)

theorem le_or_le_of_add_eq_add_pred {a b c d : ℕ} (h : c + d = a + b - 1) : a ≤ c ∨ b ≤ d := by
  cases' le_or_ltₓ a c with h' h' <;> [left, right]
  · exact h'
    
  · replace h' := add_lt_add_right h' d
    rw [h] at h'
    cases' b.eq_zero_or_pos with hb hb
    · rw [hb]
      exact zero_le d
      
    rw [a.add_sub_assoc hb, add_lt_add_iff_left] at h'
    exact Nat.le_of_pred_lt h'
    

/-- A version of `nat.sub_succ` in the form `_ - 1` instead of `nat.pred _`. -/
theorem sub_succ' (a b : ℕ) : a - b.succ = a - b - 1 :=
  rfl

/-! ### `mul` -/


theorem succ_mul_pos (m : ℕ) (hn : 0 < n) : 0 < succ m * n :=
  mul_pos (succ_posₓ m) hn

theorem mul_self_le_mul_self {n m : ℕ} (h : n ≤ m) : n * n ≤ m * m :=
  Decidable.mul_le_mul h h (zero_le _) (zero_le _)

theorem mul_self_lt_mul_self : ∀ {n m : ℕ}, n < m → n * n < m * m
  | 0, m, h => mul_pos h h
  | succ n, m, h => Decidable.mul_lt_mul h (le_of_ltₓ h) (succ_posₓ _) (zero_le _)

theorem mul_self_le_mul_self_iff {n m : ℕ} : n ≤ m ↔ n * n ≤ m * m :=
  ⟨mul_self_le_mul_self, le_imp_le_of_lt_imp_ltₓ mul_self_lt_mul_self⟩

theorem mul_self_lt_mul_self_iff {n m : ℕ} : n < m ↔ n * n < m * m :=
  le_iff_le_iff_lt_iff_lt.1 mul_self_le_mul_self_iff

theorem le_mul_self : ∀ n : ℕ, n ≤ n * n
  | 0 => le_rfl
  | n + 1 => by
    let t := Nat.mul_le_mul_leftₓ (n + 1) (succ_posₓ n)
    simp at t <;> exact t

theorem le_mul_of_pos_left {m n : ℕ} (h : 0 < n) : m ≤ n * m := by
  conv => lhs rw [← one_mulₓ m]
  exact
    Decidable.mul_le_mul_of_nonneg_right h.nat_succ_le
      (by
        decide)

theorem le_mul_of_pos_right {m n : ℕ} (h : 0 < n) : m ≤ m * n := by
  conv => lhs rw [← mul_oneₓ m]
  exact
    Decidable.mul_le_mul_of_nonneg_left h.nat_succ_le
      (by
        decide)

theorem two_mul_ne_two_mul_add_one {n m} : 2 * n ≠ 2 * m + 1 :=
  mt (congr_arg (· % 2))
    (by
      rw [add_commₓ, add_mul_mod_self_left, mul_mod_right, mod_eq_of_lt] <;> simp )

theorem mul_eq_one_iff : ∀ {a b : ℕ}, a * b = 1 ↔ a = 1 ∧ b = 1
  | 0, 0 => by
    decide
  | 0, 1 => by
    decide
  | 1, 0 => by
    decide
  | a + 2, 0 => by
    simp
  | 0, b + 2 => by
    simp
  | a + 1, b + 1 =>
    ⟨fun h => by
      simp only [← add_mulₓ, ← mul_addₓ, ← mul_addₓ, ← one_mulₓ, ← mul_oneₓ, ← (add_assocₓ _ _ _).symm, ← Nat.succ_inj',
          ← add_eq_zero_iff] at h <;>
        simp [← h.1.2, ← h.2],
      fun h => by
      simp only [← h, ← mul_oneₓ]⟩

protected theorem mul_left_inj {a b c : ℕ} (ha : 0 < a) : b * a = c * a ↔ b = c :=
  ⟨Nat.eq_of_mul_eq_mul_rightₓ ha, fun e => e ▸ rfl⟩

protected theorem mul_right_inj {a b c : ℕ} (ha : 0 < a) : a * b = a * c ↔ b = c :=
  ⟨Nat.eq_of_mul_eq_mul_leftₓ ha, fun e => e ▸ rfl⟩

theorem mul_left_injective {a : ℕ} (ha : 0 < a) : Function.Injective fun x => x * a := fun _ _ =>
  eq_of_mul_eq_mul_rightₓ ha

theorem mul_right_injective {a : ℕ} (ha : 0 < a) : Function.Injective fun x => a * x := fun _ _ =>
  Nat.eq_of_mul_eq_mul_leftₓ ha

theorem mul_ne_mul_left {a b c : ℕ} (ha : 0 < a) : b * a ≠ c * a ↔ b ≠ c :=
  (mul_left_injective ha).ne_iff

theorem mul_ne_mul_right {a b c : ℕ} (ha : 0 < a) : a * b ≠ a * c ↔ b ≠ c :=
  (mul_right_injective ha).ne_iff

theorem mul_right_eq_self_iff {a b : ℕ} (ha : 0 < a) : a * b = a ↔ b = 1 :=
  suffices a * b = a * 1 ↔ b = 1 by
    rwa [mul_oneₓ] at this
  Nat.mul_right_inj ha

theorem mul_left_eq_self_iff {a b : ℕ} (hb : 0 < b) : a * b = b ↔ a = 1 := by
  rw [mul_comm, Nat.mul_right_eq_self_iff hb]

theorem lt_succ_iff_lt_or_eq {n i : ℕ} : n < i.succ ↔ n < i ∨ n = i :=
  lt_succ_iffₓ.trans Decidable.le_iff_lt_or_eqₓ

theorem mul_self_inj {n m : ℕ} : n * n = m * m ↔ n = m :=
  le_antisymm_iffₓ.trans (le_antisymm_iffₓ.trans (and_congr mul_self_le_mul_self_iff mul_self_le_mul_self_iff)).symm

theorem le_add_pred_of_pos (n : ℕ) {i : ℕ} (hi : i ≠ 0) : n ≤ i + (n - 1) := by
  refine' le_transₓ _ add_tsub_le_assoc
  simp [← add_commₓ, ← Nat.add_sub_assocₓ, ← one_le_iff_ne_zero.2 hi]

/-!
### Recursion and induction principles

This section is here due to dependencies -- the lemmas here require some of the lemmas
proved above, and some of the results in later sections depend on the definitions in this section.
-/


@[simp]
theorem rec_zero {C : ℕ → Sort u} (h0 : C 0) (h : ∀ n, C n → C (n + 1)) : (Nat.rec h0 h : ∀ n, C n) 0 = h0 :=
  rfl

@[simp]
theorem rec_add_one {C : ℕ → Sort u} (h0 : C 0) (h : ∀ n, C n → C (n + 1)) (n : ℕ) :
    (Nat.rec h0 h : ∀ n, C n) (n + 1) = h n ((Nat.rec h0 h : ∀ n, C n) n) :=
  rfl

/-- Recursion starting at a non-zero number: given a map `C k → C (k+1)` for each `k`,
there is a map from `C n` to each `C m`, `n ≤ m`. For a version where the assumption is only made
when `k ≥ n`, see `le_rec_on'`. -/
@[elab_as_eliminator]
def leRecOn {C : ℕ → Sort u} {n : ℕ} : ∀ {m : ℕ}, n ≤ m → (∀ {k}, C k → C (k + 1)) → C n → C m
  | 0, H, next, x => Eq.recOnₓ (Nat.eq_zero_of_le_zeroₓ H) x
  | m + 1, H, next, x =>
    Or.byCases (of_le_succ H) (fun h : n ≤ m => next <| le_rec_on h (@next) x) fun h : n = m + 1 => Eq.recOnₓ h x

theorem le_rec_on_self {C : ℕ → Sort u} {n} {h : n ≤ n} {next} (x : C n) : (leRecOn h next x : C n) = x := by
  cases n <;> unfold le_rec_on Or.byCases <;> rw [dif_neg n.not_succ_le_self, dif_pos rfl]

theorem le_rec_on_succ {C : ℕ → Sort u} {n m} (h1 : n ≤ m) {h2 : n ≤ m + 1} {next} (x : C n) :
    (leRecOn h2 (@next) x : C (m + 1)) = next (leRecOn h1 (@next) x : C m) := by
  conv => lhs rw [le_rec_on, Or.byCases, dif_pos h1]

theorem le_rec_on_succ' {C : ℕ → Sort u} {n} {h : n ≤ n + 1} {next} (x : C n) :
    (leRecOn h next x : C (n + 1)) = next x := by
  rw [le_rec_on_succ (le_reflₓ n), le_rec_on_self]

theorem le_rec_on_trans {C : ℕ → Sort u} {n m k} (hnm : n ≤ m) (hmk : m ≤ k) {next} (x : C n) :
    (leRecOn (le_transₓ hnm hmk) (@next) x : C k) = leRecOn hmk (@next) (leRecOn hnm (@next) x) := by
  induction' hmk with k hmk ih
  · rw [le_rec_on_self]
    
  rw [le_rec_on_succ (le_transₓ hnm hmk), ih, le_rec_on_succ]

theorem le_rec_on_succ_left {C : ℕ → Sort u} {n m} (h1 : n ≤ m) (h2 : n + 1 ≤ m) {next : ∀ ⦃k⦄, C k → C (k + 1)}
    (x : C n) : (leRecOn h2 next (next x) : C m) = (leRecOn h1 next x : C m) := by
  rw [Subsingleton.elimₓ h1 (le_transₓ (le_succ n) h2), le_rec_on_trans (le_succ n) h2, le_rec_on_succ']

theorem le_rec_on_injective {C : ℕ → Sort u} {n m} (hnm : n ≤ m) (next : ∀ n, C n → C (n + 1))
    (Hnext : ∀ n, Function.Injective (next n)) : Function.Injective (leRecOn hnm next) := by
  induction' hnm with m hnm ih
  · intro x y H
    rwa [le_rec_on_self, le_rec_on_self] at H
    
  intro x y H
  rw [le_rec_on_succ hnm, le_rec_on_succ hnm] at H
  exact ih (Hnext _ H)

theorem le_rec_on_surjective {C : ℕ → Sort u} {n m} (hnm : n ≤ m) (next : ∀ n, C n → C (n + 1))
    (Hnext : ∀ n, Function.Surjective (next n)) : Function.Surjective (leRecOn hnm next) := by
  induction' hnm with m hnm ih
  · intro x
    use x
    rw [le_rec_on_self]
    
  intro x
  rcases Hnext _ x with ⟨w, rfl⟩
  rcases ih w with ⟨x, rfl⟩
  use x
  rw [le_rec_on_succ]

/-- Recursion principle based on `<`. -/
@[elab_as_eliminator]
protected def strongRec' {p : ℕ → Sort u} (H : ∀ n, (∀ m, m < n → p m) → p n) : ∀ n : ℕ, p n
  | n => H n fun m hm => strong_rec' m

/-- Recursion principle based on `<` applied to some natural number. -/
@[elab_as_eliminator]
def strongRecOn' {P : ℕ → Sort _} (n : ℕ) (h : ∀ n, (∀ m, m < n → P m) → P n) : P n :=
  Nat.strongRec' h n

theorem strong_rec_on_beta' {P : ℕ → Sort _} {h} {n : ℕ} :
    (strongRecOn' n h : P n) = h n fun m hmn => (strongRecOn' m h : P m) := by
  simp only [← strong_rec_on']
  rw [Nat.strongRec']

/-- Induction principle starting at a non-zero number. For maps to a `Sort*` see `le_rec_on`. -/
@[elab_as_eliminator]
theorem le_induction {P : Nat → Prop} {m} (h0 : P m) (h1 : ∀ n, m ≤ n → P n → P (n + 1)) : ∀ n, m ≤ n → P n := by
  apply Nat.LessThanOrEqual.ndrec h0 <;> exact h1

/-- Decreasing induction: if `P (k+1)` implies `P k`, then `P n` implies `P m` for all `m ≤ n`.
Also works for functions to `Sort*`. For a version assuming only the assumption for `k < n`, see
`decreasing_induction'`. -/
@[elab_as_eliminator]
def decreasingInduction {P : ℕ → Sort _} (h : ∀ n, P (n + 1) → P n) {m n : ℕ} (mn : m ≤ n) (hP : P n) : P m :=
  leRecOn mn (fun k ih hsk => ih <| h k hsk) (fun h => h) hP

@[simp]
theorem decreasing_induction_self {P : ℕ → Sort _} (h : ∀ n, P (n + 1) → P n) {n : ℕ} (nn : n ≤ n) (hP : P n) :
    (decreasingInduction h nn hP : P n) = hP := by
  dunfold decreasing_induction
  rw [le_rec_on_self]

theorem decreasing_induction_succ {P : ℕ → Sort _} (h : ∀ n, P (n + 1) → P n) {m n : ℕ} (mn : m ≤ n) (msn : m ≤ n + 1)
    (hP : P (n + 1)) : (decreasingInduction h msn hP : P m) = decreasingInduction h mn (h n hP) := by
  dunfold decreasing_induction
  rw [le_rec_on_succ]

@[simp]
theorem decreasing_induction_succ' {P : ℕ → Sort _} (h : ∀ n, P (n + 1) → P n) {m : ℕ} (msm : m ≤ m + 1)
    (hP : P (m + 1)) : (decreasingInduction h msm hP : P m) = h m hP := by
  dunfold decreasing_induction
  rw [le_rec_on_succ']

theorem decreasing_induction_trans {P : ℕ → Sort _} (h : ∀ n, P (n + 1) → P n) {m n k : ℕ} (mn : m ≤ n) (nk : n ≤ k)
    (hP : P k) :
    (decreasingInduction h (le_transₓ mn nk) hP : P m) = decreasingInduction h mn (decreasingInduction h nk hP) := by
  induction' nk with k nk ih
  rw [decreasing_induction_self]
  rw [decreasing_induction_succ h (le_transₓ mn nk), ih, decreasing_induction_succ]

theorem decreasing_induction_succ_left {P : ℕ → Sort _} (h : ∀ n, P (n + 1) → P n) {m n : ℕ} (smn : m + 1 ≤ n)
    (mn : m ≤ n) (hP : P n) : (decreasingInduction h mn hP : P m) = h m (decreasingInduction h smn hP) := by
  rw [Subsingleton.elimₓ mn (le_transₓ (le_succ m) smn), decreasing_induction_trans, decreasing_induction_succ']

/-- Given a predicate on two naturals `P : ℕ → ℕ → Prop`, `P a b` is true for all `a < b` if
`P (a + 1) (a + 1)` is true for all `a`, `P 0 (b + 1)` is true for all `b` and for all
`a < b`, `P (a + 1) b` is true and `P a (b + 1)` is true implies `P (a + 1) (b + 1)` is true. -/
@[elab_as_eliminator]
theorem diag_induction (P : ℕ → ℕ → Prop) (ha : ∀ a, P (a + 1) (a + 1)) (hb : ∀ b, P 0 (b + 1))
    (hd : ∀ a b, a < b → P (a + 1) b → P a (b + 1) → P (a + 1) (b + 1)) : ∀ a b, a < b → P a b
  | 0, b + 1, h => hb _
  | a + 1, b + 1, h => by
    apply hd _ _ ((add_lt_add_iff_right _).1 h)
    · have : a + 1 = b ∨ a + 1 < b := by
        rwa [← le_iff_eq_or_lt, ← Nat.lt_succ_iffₓ]
      rcases this with (rfl | _)
      · exact ha _
        
      apply diag_induction (a + 1) b this
      
    apply diag_induction a (b + 1)
    apply lt_of_le_of_ltₓ (Nat.le_succₓ _) h

/-- Given `P : ℕ → ℕ → Sort*`, if for all `a b : ℕ` we can extend `P` from the rectangle
strictly below `(a,b)` to `P a b`, then we have `P n m` for all `n m : ℕ`.
Note that for non-`Prop` output it is preferable to use the equation compiler directly if possible,
since this produces equation lemmas. -/
@[elab_as_eliminator]
def strongSubRecursion {P : ℕ → ℕ → Sort _} (H : ∀ a b, (∀ x y, x < a → y < b → P x y) → P a b) : ∀ n m : ℕ, P n m
  | n, m => H n m fun x y hx hy => strong_sub_recursion x y

/-- Given `P : ℕ → ℕ → Sort*`, if we have `P i 0` and `P 0 i` for all `i : ℕ`,
and for any `x y : ℕ` we can extend `P` from `(x,y+1)` and `(x+1,y)` to `(x+1,y+1)`
then we have `P n m` for all `n m : ℕ`.
Note that for non-`Prop` output it is preferable to use the equation compiler directly if possible,
since this produces equation lemmas. -/
@[elab_as_eliminator]
def pincerRecursion {P : ℕ → ℕ → Sort _} (Ha0 : ∀ a : ℕ, P a 0) (H0b : ∀ b : ℕ, P 0 b)
    (H : ∀ x y : ℕ, P x y.succ → P x.succ y → P x.succ y.succ) : ∀ n m : ℕ, P n m
  | a, 0 => Ha0 a
  | 0, b => H0b b
  | Nat.succ a, Nat.succ b => H _ _ (pincer_recursion _ _) (pincer_recursion _ _)

/-- Recursion starting at a non-zero number: given a map `C k → C (k+1)` for each `k ≥ n`,
there is a map from `C n` to each `C m`, `n ≤ m`. -/
@[elab_as_eliminator]
def leRecOn' {C : ℕ → Sort _} {n : ℕ} : ∀ {m : ℕ}, n ≤ m → (∀ ⦃k⦄, n ≤ k → C k → C (k + 1)) → C n → C m
  | 0, H, next, x => Eq.recOnₓ (Nat.eq_zero_of_le_zeroₓ H) x
  | m + 1, H, next, x =>
    Or.byCases (of_le_succ H) (fun h : n ≤ m => next h <| le_rec_on' h next x) fun h : n = m + 1 => Eq.recOnₓ h x

/-- Decreasing induction: if `P (k+1)` implies `P k` for all `m ≤ k < n`, then `P n` implies `P m`.
Also works for functions to `Sort*`. Weakens the assumptions of `decreasing_induction`. -/
@[elab_as_eliminator]
def decreasingInduction' {P : ℕ → Sort _} {m n : ℕ} (h : ∀, ∀ k < n, ∀, m ≤ k → P (k + 1) → P k) (mn : m ≤ n)
    (hP : P n) : P m := by
  -- induction mn using nat.le_rec_on' generalizing h hP -- this doesn't work unfortunately
    refine' le_rec_on' mn _ _ h hP <;>
    clear h hP mn n
  · intro n mn ih h hP
    apply ih
    · exact fun k hk => h k hk.step
      
    · exact h n (lt_succ_self n) mn hP
      
    
  · intro h hP
    exact hP
    

/-- A subset of `ℕ` containing `b : ℕ` and closed under `nat.succ` contains every `n ≥ b`. -/
theorem set_induction_bounded {b : ℕ} {S : Set ℕ} (hb : b ∈ S) (h_ind : ∀ k : ℕ, k ∈ S → k + 1 ∈ S) {n : ℕ}
    (hbn : b ≤ n) : n ∈ S :=
  @leRecOn (fun n => n ∈ S) b n hbn h_ind hb

/-- A subset of `ℕ` containing zero and closed under `nat.succ` contains all of `ℕ`. -/
theorem set_induction {S : Set ℕ} (hb : 0 ∈ S) (h_ind : ∀ k : ℕ, k ∈ S → k + 1 ∈ S) (n : ℕ) : n ∈ S :=
  set_induction_bounded hb h_ind (zero_le n)

theorem set_eq_univ {S : Set ℕ} : S = Set.Univ ↔ 0 ∈ S ∧ ∀ k : ℕ, k ∈ S → k + 1 ∈ S :=
  ⟨by
    rintro rfl <;> simp , fun ⟨h0, hs⟩ => Set.eq_univ_of_forall (set_induction h0 hs)⟩

/-! ### `div` -/


attribute [simp] Nat.div_selfₓ

protected theorem div_le_of_le_mul' {m n : ℕ} {k} (h : m ≤ k * n) : m / k ≤ n :=
  (Nat.eq_zero_or_posₓ k).elim
    (fun k0 => by
      rw [k0, Nat.div_zeroₓ] <;> apply zero_le)
    fun k0 =>
    (mul_le_mul_left k0).1 <|
      calc
        k * (m / k) ≤ m % k + k * (m / k) := Nat.le_add_leftₓ _ _
        _ = m := mod_add_divₓ _ _
        _ ≤ k * n := h
        

protected theorem div_le_self' (m n : ℕ) : m / n ≤ m :=
  (Nat.eq_zero_or_posₓ n).elim
    (fun n0 => by
      rw [n0, Nat.div_zeroₓ] <;> apply zero_le)
    fun n0 =>
    Nat.div_le_of_le_mul' <|
      calc
        m = 1 * m := (one_mulₓ _).symm
        _ ≤ n * m := Nat.mul_le_mul_rightₓ _ n0
        

/-- A version of `nat.div_lt_self` using successors, rather than additional hypotheses. -/
theorem div_lt_self' (n b : ℕ) : (n + 1) / (b + 2) < n + 1 :=
  Nat.div_lt_selfₓ (Nat.succ_posₓ n) (Nat.succ_lt_succₓ (Nat.succ_posₓ _))

theorem le_div_iff_mul_le' {x y : ℕ} {k : ℕ} (k0 : 0 < k) : x ≤ y / k ↔ x * k ≤ y :=
  le_div_iff_mul_leₓ k0

theorem div_lt_iff_lt_mul' {x y : ℕ} {k : ℕ} (k0 : 0 < k) : x / k < y ↔ x < y * k :=
  lt_iff_lt_of_le_iff_le <| le_div_iff_mul_le' k0

theorem one_le_div_iff {a b : ℕ} (hb : 0 < b) : 1 ≤ a / b ↔ b ≤ a := by
  rw [le_div_iff_mul_le hb, one_mulₓ]

theorem div_lt_one_iff {a b : ℕ} (hb : 0 < b) : a / b < 1 ↔ a < b :=
  lt_iff_lt_of_le_iff_le <| one_le_div_iff hb

protected theorem div_le_div_right {n m : ℕ} (h : n ≤ m) {k : ℕ} : n / k ≤ m / k :=
  ((Nat.eq_zero_or_posₓ k).elim fun k0 => by
      simp [← k0])
    fun hk => (le_div_iff_mul_le' hk).2 <| le_transₓ (Nat.div_mul_le_selfₓ _ _) h

theorem lt_of_div_lt_div {m n k : ℕ} : m / k < n / k → m < n :=
  lt_imp_lt_of_le_imp_le fun h => Nat.div_le_div_right h

protected theorem div_pos {a b : ℕ} (hba : b ≤ a) (hb : 0 < b) : 0 < a / b :=
  Nat.pos_of_ne_zeroₓ fun h =>
    lt_irreflₓ a
      (calc
        a = a % b := by
          simpa [← h] using (mod_add_div a b).symm
        _ < b := Nat.mod_ltₓ a hb
        _ ≤ a := hba
        )

protected theorem div_lt_of_lt_mul {m n k : ℕ} (h : m < n * k) : m / n < k :=
  lt_of_mul_lt_mul_left
    (calc
      n * (m / n) ≤ m % n + n * (m / n) := Nat.le_add_leftₓ _ _
      _ = m := mod_add_divₓ _ _
      _ < n * k := h
      )
    (Nat.zero_leₓ n)

theorem lt_mul_of_div_lt {a b c : ℕ} (h : a / c < b) (w : 0 < c) : a < b * c :=
  lt_of_not_geₓ <| not_le_of_gtₓ h ∘ (Nat.le_div_iff_mul_leₓ w).2

protected theorem div_eq_zero_iff {a b : ℕ} (hb : 0 < b) : a / b = 0 ↔ a < b :=
  ⟨fun h => by
    rw [← mod_add_div a b, h, mul_zero, add_zeroₓ] <;> exact mod_lt _ hb, fun h => by
    rw [← Nat.mul_right_inj hb, ← @add_left_cancel_iffₓ _ _ (a % b), mod_add_div, mod_eq_of_lt h, mul_zero, add_zeroₓ]⟩

protected theorem div_eq_zero {a b : ℕ} (hb : a < b) : a / b = 0 :=
  (Nat.div_eq_zero_iff <| (zero_le a).trans_lt hb).mpr hb

theorem eq_zero_of_le_div {a b : ℕ} (hb : 2 ≤ b) (h : a ≤ a / b) : a = 0 :=
  eq_zero_of_mul_le hb <| by
    rw [mul_comm] <;>
      exact
        (Nat.le_div_iff_mul_le'
              (lt_of_lt_of_leₓ
                (by
                  decide)
                hb)).1
          h

theorem mul_div_le_mul_div_assoc (a b c : ℕ) : a * (b / c) ≤ a * b / c :=
  if hc0 : c = 0 then by
    simp [← hc0]
  else
    (Nat.le_div_iff_mul_leₓ (Nat.pos_of_ne_zeroₓ hc0)).2
      (by
        rw [mul_assoc] <;> exact Nat.mul_le_mul_leftₓ _ (Nat.div_mul_le_selfₓ _ _))

theorem div_mul_div_le_div (a b c : ℕ) : a / c * b / a ≤ b / c :=
  if ha0 : a = 0 then by
    simp [← ha0]
  else
    calc
      a / c * b / a ≤ b * a / c / a :=
        Nat.div_le_div_right
          (by
            rw [mul_comm] <;> exact mul_div_le_mul_div_assoc _ _ _)
      _ = b / c := by
        rw [Nat.div_div_eq_div_mulₓ, mul_comm b, mul_comm c, Nat.mul_div_mulₓ _ _ (Nat.pos_of_ne_zeroₓ ha0)]
      

theorem eq_zero_of_le_half {a : ℕ} (h : a ≤ a / 2) : a = 0 :=
  eq_zero_of_le_div le_rfl h

protected theorem eq_mul_of_div_eq_right {a b c : ℕ} (H1 : b ∣ a) (H2 : a / b = c) : a = b * c := by
  rw [← H2, Nat.mul_div_cancel'ₓ H1]

protected theorem div_eq_iff_eq_mul_right {a b c : ℕ} (H : 0 < b) (H' : b ∣ a) : a / b = c ↔ a = b * c :=
  ⟨Nat.eq_mul_of_div_eq_right H', Nat.div_eq_of_eq_mul_rightₓ H⟩

protected theorem div_eq_iff_eq_mul_left {a b c : ℕ} (H : 0 < b) (H' : b ∣ a) : a / b = c ↔ a = c * b := by
  rw [mul_comm] <;> exact Nat.div_eq_iff_eq_mul_right H H'

protected theorem eq_mul_of_div_eq_left {a b c : ℕ} (H1 : b ∣ a) (H2 : a / b = c) : a = c * b := by
  rw [mul_comm, Nat.eq_mul_of_div_eq_right H1 H2]

protected theorem lt_div_iff_mul_lt {n d : ℕ} (hnd : d ∣ n) (a : ℕ) : a < n / d ↔ d * a < n := by
  rcases d.eq_zero_or_pos with (rfl | hd0)
  · simp [← zero_dvd_iff.mp hnd]
    
  rw [← mul_lt_mul_left hd0, ← Nat.eq_mul_of_div_eq_right hnd rfl]

protected theorem mul_div_cancel_left' {a b : ℕ} (Hd : a ∣ b) : a * (b / a) = b := by
  rw [mul_comm, Nat.div_mul_cancelₓ Hd]

/-- Alias of `nat.mul_div_mul` -/
--TODO: Update `nat.mul_div_mul` in the core?
protected theorem mul_div_mul_left (a b : ℕ) {c : ℕ} (hc : 0 < c) : c * a / (c * b) = a / b :=
  Nat.mul_div_mulₓ a b hc

protected theorem mul_div_mul_right (a b : ℕ) {c : ℕ} (hc : 0 < c) : a * c / (b * c) = a / b := by
  rw [mul_comm, mul_comm b, a.mul_div_mul_left b hc]

theorem lt_div_mul_add {a b : ℕ} (hb : 0 < b) : a < a / b * b + b := by
  rw [← Nat.succ_mul, ← Nat.div_lt_iff_lt_mulₓ hb]
  exact Nat.lt_succ_selfₓ _

theorem div_eq_iff_eq_of_dvd_dvd {n x y : ℕ} (hn : n ≠ 0) (hx : x ∣ n) (hy : y ∣ n) : n / x = n / y ↔ x = y := by
  constructor
  · intro h
    rw [← mul_right_inj' hn]
    apply Nat.eq_mul_of_div_eq_left (dvd_mul_of_dvd_left hy x)
    rw [eq_comm, mul_comm, Nat.mul_div_assocₓ _ hy]
    exact Nat.eq_mul_of_div_eq_right hx h
    
  · intro h
    rw [h]
    

theorem mul_div_mul_comm_of_dvd_dvd {a b c d : ℕ} (hac : c ∣ a) (hbd : d ∣ b) : a * b / (c * d) = a / c * (b / d) := by
  rcases c.eq_zero_or_pos with (rfl | hc0)
  · simp
    
  rcases d.eq_zero_or_pos with (rfl | hd0)
  · simp
    
  obtain ⟨k1, rfl⟩ := hac
  obtain ⟨k2, rfl⟩ := hbd
  rw [mul_mul_mul_commₓ, Nat.mul_div_cancel_leftₓ _ hc0, Nat.mul_div_cancel_leftₓ _ hd0,
    Nat.mul_div_cancel_leftₓ _ (mul_pos hc0 hd0)]

@[simp]
protected theorem div_left_inj {a b d : ℕ} (hda : d ∣ a) (hdb : d ∣ b) : a / d = b / d ↔ a = b := by
  refine' ⟨fun h => _, congr_arg _⟩
  rw [← Nat.mul_div_cancel'ₓ hda, ← Nat.mul_div_cancel'ₓ hdb, h]

/-! ### `mod`, `dvd` -/


theorem div_add_modₓ (m k : ℕ) : k * (m / k) + m % k = m :=
  (Nat.add_comm _ _).trans (mod_add_divₓ _ _)

theorem mod_add_div' (m k : ℕ) : m % k + m / k * k = m := by
  rw [mul_comm]
  exact mod_add_div _ _

theorem div_add_mod' (m k : ℕ) : m / k * k + m % k = m := by
  rw [mul_comm]
  exact div_add_mod _ _

protected theorem div_mod_unique {n k m d : ℕ} (h : 0 < k) : n / k = d ∧ n % k = m ↔ m + k * d = n ∧ m < k :=
  ⟨fun ⟨e₁, e₂⟩ => e₁ ▸ e₂ ▸ ⟨mod_add_divₓ _ _, mod_ltₓ _ h⟩, fun ⟨h₁, h₂⟩ =>
    h₁ ▸ by
      rw [add_mul_div_left _ _ h, add_mul_mod_self_left] <;> simp [← div_eq_of_lt, ← mod_eq_of_lt, ← h₂]⟩

theorem two_mul_odd_div_two {n : ℕ} (hn : n % 2 = 1) : 2 * (n / 2) = n - 1 := by
  conv => rhs rw [← Nat.mod_add_divₓ n 2, hn, add_tsub_cancel_left]

theorem div_dvd_of_dvd {a b : ℕ} (h : b ∣ a) : a / b ∣ a :=
  ⟨b, (Nat.div_mul_cancelₓ h).symm⟩

protected theorem div_div_self : ∀ {a b : ℕ}, b ∣ a → 0 < a → a / (a / b) = b
  | a, 0, h₁, h₂ => by
    rw [eq_zero_of_zero_dvd h₁, Nat.div_zeroₓ, Nat.div_zeroₓ]
  | 0, b, h₁, h₂ =>
    absurd h₂
      (by
        decide)
  | a + 1, b + 1, h₁, h₂ =>
    (Nat.mul_left_inj (Nat.div_pos (le_of_dvdₓ (succ_posₓ a) h₁) (succ_posₓ b))).1 <| by
      rw [Nat.div_mul_cancelₓ (div_dvd_of_dvd h₁), Nat.mul_div_cancel'ₓ h₁]

theorem mod_mul_right_div_self (a b c : ℕ) : a % (b * c) / b = a / b % c := by
  rcases Nat.eq_zero_or_posₓ b with (rfl | hb)
  · simp
    
  rcases Nat.eq_zero_or_posₓ c with (rfl | hc)
  · simp
    
  conv_rhs => rw [← mod_add_div a (b * c)]
  rw [mul_assoc, Nat.add_mul_div_leftₓ _ _ hb, add_mul_mod_self_left,
    mod_eq_of_lt (Nat.div_lt_of_lt_mul (mod_lt _ (mul_pos hb hc)))]

theorem mod_mul_left_div_self (a b c : ℕ) : a % (c * b) / b = a / b % c := by
  rw [mul_comm c, mod_mul_right_div_self]

@[simp]
protected theorem dvd_one {n : ℕ} : n ∣ 1 ↔ n = 1 :=
  ⟨eq_one_of_dvd_one, fun e => e.symm ▸ dvd_rfl⟩

protected theorem dvd_add_left {k m n : ℕ} (h : k ∣ n) : k ∣ m + n ↔ k ∣ m :=
  (Nat.dvd_add_iff_left h).symm

protected theorem dvd_add_right {k m n : ℕ} (h : k ∣ m) : k ∣ m + n ↔ k ∣ n :=
  (Nat.dvd_add_iff_right h).symm

@[simp]
protected theorem not_two_dvd_bit1 (n : ℕ) : ¬2 ∣ bit1 n := by
  rw [bit1, Nat.dvd_add_right two_dvd_bit0, Nat.dvd_one]
  cc

/-- A natural number `m` divides the sum `m + n` if and only if `m` divides `n`.-/
@[simp]
protected theorem dvd_add_self_left {m n : ℕ} : m ∣ m + n ↔ m ∣ n :=
  Nat.dvd_add_right (dvd_refl m)

/-- A natural number `m` divides the sum `n + m` if and only if `m` divides `n`.-/
@[simp]
protected theorem dvd_add_self_right {m n : ℕ} : m ∣ n + m ↔ m ∣ n :=
  Nat.dvd_add_left (dvd_refl m)

-- TODO: update `nat.dvd_sub` in core
theorem dvd_sub' {k m n : ℕ} (h₁ : k ∣ m) (h₂ : k ∣ n) : k ∣ m - n := by
  cases' le_totalₓ n m with H H
  · exact dvd_sub H h₁ h₂
    
  · rw [tsub_eq_zero_iff_le.mpr H]
    exact dvd_zero k
    

theorem not_dvd_of_pos_of_lt {a b : ℕ} (h1 : 0 < b) (h2 : b < a) : ¬a ∣ b := by
  rintro ⟨c, rfl⟩
  rcases Nat.eq_zero_or_posₓ c with (rfl | hc)
  · exact lt_irreflₓ 0 h1
    
  · exact not_ltₓ.2 (le_mul_of_pos_right hc) h2
    

protected theorem mul_dvd_mul_iff_left {a b c : ℕ} (ha : 0 < a) : a * b ∣ a * c ↔ b ∣ c :=
  exists_congr fun d => by
    rw [mul_assoc, Nat.mul_right_inj ha]

protected theorem mul_dvd_mul_iff_right {a b c : ℕ} (hc : 0 < c) : a * c ∣ b * c ↔ a ∣ b :=
  exists_congr fun d => by
    rw [mul_right_commₓ, Nat.mul_left_inj hc]

theorem succ_div : ∀ a b : ℕ, (a + 1) / b = a / b + if b ∣ a + 1 then 1 else 0
  | a, 0 => by
    simp
  | 0, 1 => by
    simp
  | 0, b + 2 => by
    have hb2 : b + 2 > 1 := by
      decide
    simp [← ne_of_gtₓ hb2, ← div_eq_of_lt hb2]
  | a + 1, b + 1 => by
    rw [Nat.div_def]
    conv_rhs => rw [Nat.div_def]
    by_cases' hb_eq_a : b = a + 1
    · simp [← hb_eq_a, ← le_reflₓ]
      
    by_cases' hb_le_a1 : b ≤ a + 1
    · have hb_le_a : b ≤ a := le_of_lt_succ (lt_of_le_of_neₓ hb_le_a1 hb_eq_a)
      have h₁ : 0 < b + 1 ∧ b + 1 ≤ a + 1 + 1 := ⟨succ_pos _, (add_le_add_iff_right _).2 hb_le_a1⟩
      have h₂ : 0 < b + 1 ∧ b + 1 ≤ a + 1 := ⟨succ_pos _, (add_le_add_iff_right _).2 hb_le_a⟩
      have dvd_iff : b + 1 ∣ a - b + 1 ↔ b + 1 ∣ a + 1 + 1 := by
        rw [Nat.dvd_add_iff_left (dvd_refl (b + 1)), ← add_tsub_add_eq_tsub_right a 1 b, add_commₓ (_ - _), add_assocₓ,
          tsub_add_cancel_of_le (succ_le_succ hb_le_a), add_commₓ 1]
      have wf : a - b < a + 1 := lt_succ_of_le tsub_le_self
      rw [if_pos h₁, if_pos h₂, add_tsub_add_eq_tsub_right, ← tsub_add_eq_add_tsub hb_le_a,
        have := wf
        succ_div (a - b),
        add_tsub_add_eq_tsub_right]
      simp [← dvd_iff, ← succ_eq_add_one, ← add_commₓ 1, ← add_assocₓ]
      
    · have hba : ¬b ≤ a := not_le_of_gtₓ (lt_transₓ (lt_succ_self a) (lt_of_not_geₓ hb_le_a1))
      have hb_dvd_a : ¬b + 1 ∣ a + 2 := fun h => hb_le_a1 (le_of_succ_le_succ (le_of_dvd (succ_pos _) h))
      simp [← hba, ← hb_le_a1, ← hb_dvd_a]
      

theorem succ_div_of_dvd {a b : ℕ} (hba : b ∣ a + 1) : (a + 1) / b = a / b + 1 := by
  rw [succ_div, if_pos hba]

theorem succ_div_of_not_dvd {a b : ℕ} (hba : ¬b ∣ a + 1) : (a + 1) / b = a / b := by
  rw [succ_div, if_neg hba, add_zeroₓ]

theorem dvd_iff_div_mul_eq (n d : ℕ) : d ∣ n ↔ n / d * d = n :=
  ⟨fun h => Nat.div_mul_cancelₓ h, fun h => Dvd.intro_left (n / d) h⟩

theorem dvd_iff_le_div_mul (n d : ℕ) : d ∣ n ↔ n ≤ n / d * d :=
  ((dvd_iff_div_mul_eq _ _).trans le_antisymm_iffₓ).trans (and_iff_right (div_mul_le_selfₓ n d))

theorem dvd_iff_dvd_dvd (n d : ℕ) : d ∣ n ↔ ∀ k : ℕ, k ∣ d → k ∣ n :=
  ⟨fun h k hkd => dvd_trans hkd h, fun h => h _ dvd_rfl⟩

@[simp]
theorem mod_mod_of_dvd (n : Nat) {m k : Nat} (h : m ∣ k) : n % k % m = n % m := by
  conv => rhs rw [← mod_add_div n k]
  rcases h with ⟨t, rfl⟩
  rw [mul_assoc, add_mul_mod_self_left]

@[simp]
theorem mod_modₓ (a n : ℕ) : a % n % n = a % n :=
  (Nat.eq_zero_or_posₓ n).elim
    (fun n0 => by
      simp [← n0])
    fun npos => mod_eq_of_ltₓ (mod_ltₓ _ npos)

/-- If `a` and `b` are equal mod `c`, `a - b` is zero mod `c`. -/
theorem sub_mod_eq_zero_of_mod_eq {a b c : ℕ} (h : a % c = b % c) : (a - b) % c = 0 := by
  rw [← Nat.mod_add_divₓ a c, ← Nat.mod_add_divₓ b c, ← h, tsub_add_eq_tsub_tsub, add_tsub_cancel_left, ← mul_tsub,
    Nat.mul_mod_rightₓ]

@[simp]
theorem one_mod (n : ℕ) : 1 % (n + 2) = 1 :=
  Nat.mod_eq_of_ltₓ (add_lt_add_right n.succ_pos 1)

theorem dvd_sub_mod (k : ℕ) : n ∣ k - k % n :=
  ⟨k / n, tsub_eq_of_eq_add_rev (Nat.mod_add_divₓ k n).symm⟩

@[simp]
theorem mod_add_modₓ (m n k : ℕ) : (m % n + k) % n = (m + k) % n := by
  have := (add_mul_mod_self_left (m % n + k) n (m / n)).symm <;> rwa [add_right_commₓ, mod_add_div] at this

@[simp]
theorem add_mod_modₓ (m n k : ℕ) : (m + n % k) % k = (m + n) % k := by
  rw [add_commₓ, mod_add_mod, add_commₓ]

theorem add_modₓ (a b n : ℕ) : (a + b) % n = (a % n + b % n) % n := by
  rw [add_mod_mod, mod_add_mod]

theorem add_mod_eq_add_mod_right {m n k : ℕ} (i : ℕ) (H : m % n = k % n) : (m + i) % n = (k + i) % n := by
  rw [← mod_add_mod, ← mod_add_mod k, H]

theorem add_mod_eq_add_mod_left {m n k : ℕ} (i : ℕ) (H : m % n = k % n) : (i + m) % n = (i + k) % n := by
  rw [add_commₓ, add_mod_eq_add_mod_right _ H, add_commₓ]

theorem add_mod_eq_ite {a b n : ℕ} : (a + b) % n = if n ≤ a % n + b % n then a % n + b % n - n else a % n + b % n := by
  cases n
  · simp
    
  rw [Nat.add_modₓ]
  split_ifs with h
  · rw [Nat.mod_eq_sub_modₓ h, Nat.mod_eq_of_ltₓ]
    exact (tsub_lt_iff_right h).mpr (Nat.add_lt_addₓ (a.mod_lt n.zero_lt_succ) (b.mod_lt n.zero_lt_succ))
    
  · exact Nat.mod_eq_of_ltₓ (lt_of_not_geₓ h)
    

theorem mul_modₓ (a b n : ℕ) : a * b % n = a % n * (b % n) % n := by
  conv_lhs =>
    rw [← mod_add_div a n, ← mod_add_div' b n, right_distrib, left_distrib, left_distrib, mul_assoc, mul_assoc, ←
      left_distrib n _ _, add_mul_mod_self_left, ← mul_assoc, add_mul_mod_self_right]

theorem dvd_div_of_mul_dvd {a b c : ℕ} (h : a * b ∣ c) : b ∣ c / a :=
  if ha : a = 0 then by
    simp [← ha]
  else
    have ha : 0 < a := Nat.pos_of_ne_zeroₓ ha
    have h1 : ∃ d, c = a * b * d := h
    let ⟨d, hd⟩ := h1
    have h2 : c / a = b * d :=
      Nat.div_eq_of_eq_mul_rightₓ ha
        (by
          simpa [← mul_assoc] using hd)
    show ∃ d, c / a = b * d from ⟨d, h2⟩

theorem mul_dvd_of_dvd_div {a b c : ℕ} (hab : c ∣ b) (h : a ∣ b / c) : c * a ∣ b :=
  have h1 : ∃ d, b / c = a * d := h
  have h2 : ∃ e, b = c * e := hab
  let ⟨d, hd⟩ := h1
  let ⟨e, he⟩ := h2
  have h3 : b = a * d * c := Nat.eq_mul_of_div_eq_left hab hd
  show ∃ d, b = c * a * d from
    ⟨d, by
      cc⟩

@[simp]
theorem dvd_div_iff {a b c : ℕ} (hbc : c ∣ b) : a ∣ b / c ↔ c * a ∣ b :=
  ⟨fun h => mul_dvd_of_dvd_div hbc h, fun h => dvd_div_of_mul_dvd h⟩

theorem div_mul_div_comm {a b c d : ℕ} (hab : b ∣ a) (hcd : d ∣ c) : a / b * (c / d) = a * c / (b * d) :=
  have exi1 : ∃ x, a = b * x := hab
  have exi2 : ∃ y, c = d * y := hcd
  if hb : b = 0 then by
    simp [← hb]
  else
    have : 0 < b := Nat.pos_of_ne_zeroₓ hb
    if hd : d = 0 then by
      simp [← hd]
    else by
      have : 0 < d := Nat.pos_of_ne_zeroₓ hd
      cases' exi1 with x hx
      cases' exi2 with y hy
      rw [hx, hy, Nat.mul_div_cancel_leftₓ, Nat.mul_div_cancel_leftₓ]
      symm
      apply Nat.div_eq_of_eq_mul_leftₓ
      apply mul_pos
      repeat'
        assumption
      cc

@[simp]
theorem div_div_div_eq_div : ∀ {a b c : ℕ} (dvd : b ∣ a) (dvd2 : a ∣ c), c / (a / b) / b = c / a
  | 0, _ => by
    simp
  | a + 1, 0 => fun _ dvd _ => by
    simpa using dvd
  | a + 1, c + 1 =>
    have a_split : a + 1 ≠ 0 := succ_ne_zero a
    have c_split : c + 1 ≠ 0 := succ_ne_zero c
    fun b dvd dvd2 => by
    rcases dvd2 with ⟨k, rfl⟩
    rcases dvd with ⟨k2, pr⟩
    have k2_nonzero : k2 ≠ 0 := fun k2_zero => by
      simpa [← k2_zero] using pr
    rw [Nat.mul_div_cancel_leftₓ k (Nat.pos_of_ne_zeroₓ a_split), pr,
      Nat.mul_div_cancel_leftₓ k2 (Nat.pos_of_ne_zeroₓ c_split), Nat.mul_comm ((c + 1) * k2) k, ←
      Nat.mul_assoc k (c + 1) k2, Nat.mul_div_cancelₓ _ (Nat.pos_of_ne_zeroₓ k2_nonzero),
      Nat.mul_div_cancelₓ _ (Nat.pos_of_ne_zeroₓ c_split)]

theorem eq_of_dvd_of_div_eq_one {a b : ℕ} (w : a ∣ b) (h : b / a = 1) : a = b := by
  rw [← Nat.div_mul_cancelₓ w, h, one_mulₓ]

theorem eq_zero_of_dvd_of_div_eq_zero {a b : ℕ} (w : a ∣ b) (h : b / a = 0) : b = 0 := by
  rw [← Nat.div_mul_cancelₓ w, h, zero_mul]

/-- If a small natural number is divisible by a larger natural number,
the small number is zero. -/
theorem eq_zero_of_dvd_of_lt {a b : ℕ} (w : a ∣ b) (h : b < a) : b = 0 :=
  Nat.eq_zero_of_dvd_of_div_eq_zero w ((Nat.div_eq_zero_iff (lt_of_le_of_ltₓ (zero_le b) h)).elim_right h)

theorem div_le_div_left {a b c : ℕ} (h₁ : c ≤ b) (h₂ : 0 < c) : a / b ≤ a / c :=
  (Nat.le_div_iff_mul_leₓ h₂).2 <| le_transₓ (Nat.mul_le_mul_leftₓ _ h₁) (div_mul_le_selfₓ _ _)

theorem div_eq_self {a b : ℕ} : a / b = a ↔ a = 0 ∨ b = 1 := by
  constructor
  · intro
    cases b
    · simp_all
      
    · cases b
      · right
        rfl
        
      · left
        have : a / (b + 2) ≤ a / 2 :=
          div_le_div_left
            (by
              simp )
            (by
              decide)
        refine' eq_zero_of_le_half _
        simp_all
        
      
    
  · rintro (rfl | rfl) <;> simp
    

theorem lt_iff_le_pred : ∀ {m n : ℕ}, 0 < n → (m < n ↔ m ≤ n - 1)
  | m, n + 1, _ => lt_succ_iffₓ

-- ./././Mathport/Syntax/Translate/Tactic/Lean3.lean:92:4: warning: unsupported: rw with cfg: { occs := occurrences.pos «expr[ ,]»([2]) }
theorem div_eq_sub_mod_div {m n : ℕ} : m / n = (m - m % n) / n := by
  by_cases' n0 : n = 0
  · rw [n0, Nat.div_zeroₓ, Nat.div_zeroₓ]
    
  · rw [← mod_add_div m n]
    rw [add_tsub_cancel_left, mul_div_right _ (Nat.pos_of_ne_zeroₓ n0)]
    

theorem mul_div_leₓ (m n : ℕ) : n * (m / n) ≤ m := by
  cases' Nat.eq_zero_or_posₓ n with n0 h
  · rw [n0, zero_mul]
    exact m.zero_le
    
  · rw [mul_comm, ← Nat.le_div_iff_mul_le' h]
    

theorem lt_mul_div_succ (m : ℕ) {n : ℕ} (n0 : 0 < n) : m < n * (m / n + 1) := by
  rw [mul_comm, ← Nat.div_lt_iff_lt_mul' n0]
  exact lt_succ_self _

@[simp]
theorem mod_div_self (m n : ℕ) : m % n / n = 0 := by
  cases n
  · exact (m % 0).div_zero
    
  · exact Nat.div_eq_zero (m.mod_lt n.succ_pos)
    

/-- `n` is not divisible by `a` if it is between `a * k` and `a * (k + 1)` for some `k`. -/
theorem not_dvd_of_between_consec_multiples {n a k : ℕ} (h1 : a * k < n) (h2 : n < a * (k + 1)) : ¬a ∣ n := by
  rintro ⟨d, rfl⟩
  exact Monotone.ne_of_lt_of_lt_nat (Covariant.monotone_of_const a) k h1 h2 d rfl

/-- `n` is not divisible by `a` iff it is between `a * k` and `a * (k + 1)` for some `k`. -/
theorem not_dvd_iff_between_consec_multiples (n : ℕ) {a : ℕ} (ha : 0 < a) :
    (∃ k : ℕ, a * k < n ∧ n < a * (k + 1)) ↔ ¬a ∣ n := by
  refine'
    ⟨fun ⟨k, hk1, hk2⟩ => not_dvd_of_between_consec_multiples hk1 hk2, fun han =>
      ⟨n / a, ⟨lt_of_le_of_neₓ (mul_div_le n a) _, lt_mul_div_succ _ ha⟩⟩⟩
  exact mt (Dvd.intro (n / a)) han

/-- Two natural numbers are equal if and only if they have the same multiples. -/
theorem dvd_right_iff_eq {m n : ℕ} : (∀ a : ℕ, m ∣ a ↔ n ∣ a) ↔ m = n :=
  ⟨fun h => dvd_antisymm ((h _).mpr dvd_rfl) ((h _).mp dvd_rfl), fun h n => by
    rw [h]⟩

/-- Two natural numbers are equal if and only if they have the same divisors. -/
theorem dvd_left_iff_eq {m n : ℕ} : (∀ a : ℕ, a ∣ m ↔ a ∣ n) ↔ m = n :=
  ⟨fun h => dvd_antisymm ((h _).mp dvd_rfl) ((h _).mpr dvd_rfl), fun h n => by
    rw [h]⟩

/-- `dvd` is injective in the left argument -/
theorem dvd_left_injective : Function.Injective ((· ∣ ·) : ℕ → ℕ → Prop) := fun m n h =>
  dvd_right_iff_eq.mp fun a => iff_of_eq (congr_fun h a)

theorem div_lt_div_of_lt_of_dvd {a b d : ℕ} (hdb : d ∣ b) (h : a < b) : a / d < b / d := by
  rw [Nat.lt_div_iff_mul_lt hdb]
  exact lt_of_le_of_ltₓ (mul_div_le a d) h

theorem mul_add_mod (a b c : ℕ) : (a * b + c) % b = c % b := by
  simp [← Nat.add_modₓ]

theorem mul_add_mod_of_lt {a b c : ℕ} (h : c < b) : (a * b + c) % b = c := by
  rw [Nat.mul_add_mod, Nat.mod_eq_of_ltₓ h]

theorem pred_eq_self_iff {n : ℕ} : n.pred = n ↔ n = 0 := by
  cases n <;> simp [← (Nat.succ_ne_self _).symm]

/-! ### `find` -/


section Find

variable {p q : ℕ → Prop} [DecidablePred p] [DecidablePred q]

theorem find_eq_iff (h : ∃ n : ℕ, p n) : Nat.findₓ h = m ↔ p m ∧ ∀, ∀ n < m, ∀, ¬p n := by
  constructor
  · rintro rfl
    exact ⟨Nat.find_specₓ h, fun _ => Nat.find_minₓ h⟩
    
  · rintro ⟨hm, hlt⟩
    exact le_antisymmₓ (Nat.find_min'ₓ h hm) (not_ltₓ.1 <| imp_not_comm.1 (hlt _) <| Nat.find_specₓ h)
    

@[simp]
theorem find_lt_iff (h : ∃ n : ℕ, p n) (n : ℕ) : Nat.findₓ h < n ↔ ∃ m < n, p m :=
  ⟨fun h2 => ⟨Nat.findₓ h, h2, Nat.find_specₓ h⟩, fun ⟨m, hmn, hm⟩ => (Nat.find_min'ₓ h hm).trans_lt hmn⟩

@[simp]
theorem find_le_iff (h : ∃ n : ℕ, p n) (n : ℕ) : Nat.findₓ h ≤ n ↔ ∃ m ≤ n, p m := by
  simp only [← exists_prop, lt_succ_iff, ← find_lt_iff]

@[simp]
theorem le_find_iff (h : ∃ n : ℕ, p n) (n : ℕ) : n ≤ Nat.findₓ h ↔ ∀, ∀ m < n, ∀, ¬p m := by
  simp_rw [← not_ltₓ, find_lt_iff, not_exists]

@[simp]
theorem lt_find_iff (h : ∃ n : ℕ, p n) (n : ℕ) : n < Nat.findₓ h ↔ ∀, ∀ m ≤ n, ∀, ¬p m := by
  simp only [succ_le_iff, ← le_find_iff, ← succ_le_succ_iff]

@[simp]
theorem find_eq_zero (h : ∃ n : ℕ, p n) : Nat.findₓ h = 0 ↔ p 0 := by
  simp [← find_eq_iff]

@[simp]
theorem find_pos (h : ∃ n : ℕ, p n) : 0 < Nat.findₓ h ↔ ¬p 0 := by
  rw [pos_iff_ne_zero, Ne, Nat.find_eq_zero]

theorem find_mono (h : ∀ n, q n → p n) {hp : ∃ n, p n} {hq : ∃ n, q n} : Nat.findₓ hp ≤ Nat.findₓ hq :=
  Nat.find_min'ₓ _ (h _ (Nat.find_specₓ hq))

theorem find_le {h : ∃ n, p n} (hn : p n) : Nat.findₓ h ≤ n :=
  (Nat.find_le_iff _ _).2 ⟨n, le_rfl, hn⟩

theorem find_add {hₘ : ∃ m, p (m + n)} {hₙ : ∃ n, p n} (hn : n ≤ Nat.findₓ hₙ) : Nat.findₓ hₘ + n = Nat.findₓ hₙ := by
  refine' ((le_find_iff _ _).2 fun m hm hpm => hm.not_le _).antisymm _
  · have hnm : n ≤ m := hn.trans (find_le hpm)
    refine' add_le_of_le_tsub_right_of_le hnm (find_le _)
    rwa [tsub_add_cancel_of_le hnm]
    
  · rw [← tsub_le_iff_right]
    refine' (le_find_iff _ _).2 fun m hm hpm => hm.not_le _
    rw [tsub_le_iff_right]
    exact find_le hpm
    

theorem find_comp_succ (h₁ : ∃ n, p n) (h₂ : ∃ n, p (n + 1)) (h0 : ¬p 0) : Nat.findₓ h₁ = Nat.findₓ h₂ + 1 := by
  refine' (find_eq_iff _).2 ⟨Nat.find_specₓ h₂, fun n hn => _⟩
  cases' n with n
  exacts[h0, @Nat.find_minₓ (fun n => p (n + 1)) _ h₂ _ (succ_lt_succ_iff.1 hn)]

end Find

/-! ### `find_greatest` -/


section FindGreatest

/-- `find_greatest P b` is the largest `i ≤ bound` such that `P i` holds, or `0` if no such `i`
exists -/
protected def findGreatest (P : ℕ → Prop) [DecidablePred P] : ℕ → ℕ
  | 0 => 0
  | n + 1 => if P (n + 1) then n + 1 else find_greatest n

variable {P Q : ℕ → Prop} [DecidablePred P] {b : ℕ}

@[simp]
theorem find_greatest_zero : Nat.findGreatest P 0 = 0 :=
  rfl

theorem find_greatest_succ (n : ℕ) : Nat.findGreatest P (n + 1) = if P (n + 1) then n + 1 else Nat.findGreatest P n :=
  rfl

@[simp]
theorem find_greatest_eq : ∀ {b}, P b → Nat.findGreatest P b = b
  | 0, h => rfl
  | n + 1, h => by
    simp [← Nat.findGreatest, ← h]

@[simp]
theorem find_greatest_of_not (h : ¬P (b + 1)) : Nat.findGreatest P (b + 1) = Nat.findGreatest P b := by
  simp [← Nat.findGreatest, ← h]

theorem find_greatest_eq_iff : Nat.findGreatest P b = m ↔ m ≤ b ∧ (m ≠ 0 → P m) ∧ ∀ ⦃n⦄, m < n → n ≤ b → ¬P n := by
  induction' b with b ihb generalizing m
  · rw [eq_comm, Iff.comm]
    simp only [← nonpos_iff_eq_zero, ← Ne.def, ← and_iff_left_iff_imp, ← find_greatest_zero]
    rintro rfl
    exact ⟨fun h => (h rfl).elim, fun n hlt heq => (hlt.Ne HEq.symm).elim⟩
    
  · by_cases' hb : P (b + 1)
    · rw [find_greatest_eq hb]
      constructor
      · rintro rfl
        exact ⟨le_rfl, fun _ => hb, fun n hlt hle => (hlt.not_le hle).elim⟩
        
      · rintro ⟨hle, h0, hm⟩
        rcases Decidable.eq_or_lt_of_leₓ hle with (rfl | hlt)
        exacts[rfl, (hm hlt le_rfl hb).elim]
        
      
    · rw [find_greatest_of_not hb, ihb]
      constructor
      · rintro ⟨hle, hP, hm⟩
        refine' ⟨hle.trans b.le_succ, hP, fun n hlt hle => _⟩
        rcases Decidable.eq_or_lt_of_leₓ hle with (rfl | hlt')
        exacts[hb, hm hlt <| lt_succ_iff.1 hlt']
        
      · rintro ⟨hle, hP, hm⟩
        refine' ⟨lt_succ_iff.1 (hle.lt_of_ne _), hP, fun n hlt hle => hm hlt (hle.trans b.le_succ)⟩
        rintro rfl
        exact hb (hP b.succ_ne_zero)
        
      
    

theorem find_greatest_eq_zero_iff : Nat.findGreatest P b = 0 ↔ ∀ ⦃n⦄, 0 < n → n ≤ b → ¬P n := by
  simp [← find_greatest_eq_iff]

theorem find_greatest_spec (hmb : m ≤ b) (hm : P m) : P (Nat.findGreatest P b) := by
  by_cases' h : Nat.findGreatest P b = 0
  · cases m
    · rwa [h]
      
    exact ((find_greatest_eq_zero_iff.1 h) m.zero_lt_succ hmb hm).elim
    
  · exact (find_greatest_eq_iff.1 rfl).2.1 h
    

theorem find_greatest_le (n : ℕ) : Nat.findGreatest P n ≤ n :=
  (find_greatest_eq_iff.1 rfl).1

theorem le_find_greatest (hmb : m ≤ b) (hm : P m) : m ≤ Nat.findGreatest P b :=
  le_of_not_ltₓ fun hlt => (find_greatest_eq_iff.1 rfl).2.2 hlt hmb hm

theorem find_greatest_mono_right (P : ℕ → Prop) [DecidablePred P] : Monotone (Nat.findGreatest P) := by
  refine' monotone_nat_of_le_succ fun n => _
  rw [find_greatest_succ]
  split_ifs
  · exact (find_greatest_le n).trans (le_succ _)
    
  · rfl
    

theorem find_greatest_mono_left [DecidablePred Q] (hPQ : P ≤ Q) : Nat.findGreatest P ≤ Nat.findGreatest Q := by
  intro n
  induction' n with n hn
  · rfl
    
  by_cases' P (n + 1)
  · rw [find_greatest_eq h, find_greatest_eq (hPQ _ h)]
    
  · rw [find_greatest_of_not h]
    exact hn.trans (Nat.find_greatest_mono_right _ <| le_succ _)
    

theorem find_greatest_mono {a b : ℕ} [DecidablePred Q] (hPQ : P ≤ Q) (hab : a ≤ b) :
    Nat.findGreatest P a ≤ Nat.findGreatest Q b :=
  (Nat.find_greatest_mono_right _ hab).trans <| find_greatest_mono_left hPQ _

theorem find_greatest_is_greatest (hk : Nat.findGreatest P b < k) (hkb : k ≤ b) : ¬P k :=
  (find_greatest_eq_iff.1 rfl).2.2 hk hkb

theorem find_greatest_of_ne_zero (h : Nat.findGreatest P b = m) (h0 : m ≠ 0) : P m :=
  (find_greatest_eq_iff.1 h).2.1 h0

end FindGreatest

/-! ### `bodd_div2` and `bodd` -/


@[simp]
theorem bodd_div2_eq (n : ℕ) : boddDiv2 n = (bodd n, div2 n) := by
  unfold bodd div2 <;> cases bodd_div2 n <;> rfl

@[simp]
theorem bodd_bit0 (n) : bodd (bit0 n) = ff :=
  bodd_bit false n

@[simp]
theorem bodd_bit1 (n) : bodd (bit1 n) = tt :=
  bodd_bit true n

@[simp]
theorem div2_bit0 (n) : div2 (bit0 n) = n :=
  div2_bit false n

@[simp]
theorem div2_bit1 (n) : div2 (bit1 n) = n :=
  div2_bit true n

/-! ### `bit0` and `bit1` -/


-- There is no need to prove `bit0_eq_zero : bit0 n = 0 ↔ n = 0`
-- as this is true for any `[semiring R] [no_zero_divisors R] [char_zero R]`
-- However the lemmas `bit0_eq_bit0`, `bit1_eq_bit1`, `bit1_eq_one`, `one_eq_bit1`
-- need `[ring R] [no_zero_divisors R] [char_zero R]` in general,
-- so we prove `ℕ` specialized versions here.
@[simp]
theorem bit0_eq_bit0 {m n : ℕ} : bit0 m = bit0 n ↔ m = n :=
  ⟨Nat.bit0_inj, fun h => by
    subst h⟩

@[simp]
theorem bit1_eq_bit1 {m n : ℕ} : bit1 m = bit1 n ↔ m = n :=
  ⟨Nat.bit1_inj, fun h => by
    subst h⟩

@[simp]
theorem bit1_eq_one {n : ℕ} : bit1 n = 1 ↔ n = 0 :=
  ⟨@Nat.bit1_inj n 0, fun h => by
    subst h⟩

@[simp]
theorem one_eq_bit1 {n : ℕ} : 1 = bit1 n ↔ n = 0 :=
  ⟨fun h => (@Nat.bit1_inj 0 n h).symm, fun h => by
    subst h⟩

theorem bit_add : ∀ (b : Bool) (n m : ℕ), bit b (n + m) = bit false n + bit b m
  | tt => bit1_add
  | ff => bit0_add

theorem bit_add' : ∀ (b : Bool) (n m : ℕ), bit b (n + m) = bit b n + bit false m
  | tt => bit1_add'
  | ff => bit0_add

protected theorem bit0_le {n m : ℕ} (h : n ≤ m) : bit0 n ≤ bit0 m :=
  add_le_add h h

protected theorem bit1_le {n m : ℕ} (h : n ≤ m) : bit1 n ≤ bit1 m :=
  succ_le_succₓ (add_le_add h h)

theorem bit_le : ∀ (b : Bool) {n m : ℕ}, n ≤ m → bit b n ≤ bit b m
  | tt, n, m, h => Nat.bit1_le h
  | ff, n, m, h => Nat.bit0_le h

theorem bit_ne_zero (b) {n} (h : n ≠ 0) : bit b n ≠ 0 := by
  cases b <;> [exact Nat.bit0_ne_zero h, exact Nat.bit1_ne_zero _]

theorem bit0_le_bit : ∀ (b) {m n : ℕ}, m ≤ n → bit0 m ≤ bit b n
  | tt, m, n, h => le_of_ltₓ <| Nat.bit0_lt_bit1 h
  | ff, m, n, h => Nat.bit0_le h

theorem bit_le_bit1 : ∀ (b) {m n : ℕ}, m ≤ n → bit b m ≤ bit1 n
  | ff, m, n, h => le_of_ltₓ <| Nat.bit0_lt_bit1 h
  | tt, m, n, h => Nat.bit1_le h

theorem bit_lt_bit0 : ∀ (b) {n m : ℕ}, n < m → bit b n < bit0 m
  | tt, n, m, h => Nat.bit1_lt_bit0 h
  | ff, n, m, h => Nat.bit0_lt h

theorem bit_lt_bit (a b) {n m : ℕ} (h : n < m) : bit a n < bit b m :=
  lt_of_lt_of_leₓ (bit_lt_bit0 _ h) (bit0_le_bit _ le_rfl)

@[simp]
theorem bit0_le_bit1_iff : bit0 k ≤ bit1 n ↔ k ≤ n :=
  ⟨fun h => by
    rwa [← Nat.lt_succ_iffₓ, n.bit1_eq_succ_bit0, ← n.bit0_succ_eq, bit0_lt_bit0, Nat.lt_succ_iffₓ] at h, fun h =>
    le_of_ltₓ (Nat.bit0_lt_bit1 h)⟩

@[simp]
theorem bit0_lt_bit1_iff : bit0 k < bit1 n ↔ k ≤ n :=
  ⟨fun h => bit0_le_bit1_iff.1 (le_of_ltₓ h), Nat.bit0_lt_bit1⟩

@[simp]
theorem bit1_le_bit0_iff : bit1 k ≤ bit0 n ↔ k < n :=
  ⟨fun h => by
    rwa [k.bit1_eq_succ_bit0, succ_le_iff, bit0_lt_bit0] at h, fun h => le_of_ltₓ (Nat.bit1_lt_bit0 h)⟩

@[simp]
theorem bit1_lt_bit0_iff : bit1 k < bit0 n ↔ k < n :=
  ⟨fun h => bit1_le_bit0_iff.1 (le_of_ltₓ h), Nat.bit1_lt_bit0⟩

@[simp]
theorem one_le_bit0_iff : 1 ≤ bit0 n ↔ 0 < n := by
  convert bit1_le_bit0_iff
  rfl

@[simp]
theorem one_lt_bit0_iff : 1 < bit0 n ↔ 1 ≤ n := by
  convert bit1_lt_bit0_iff
  rfl

@[simp]
theorem bit_le_bit_iff : ∀ {b : Bool}, bit b k ≤ bit b n ↔ k ≤ n
  | ff => bit0_le_bit0
  | tt => bit1_le_bit1

@[simp]
theorem bit_lt_bit_iff : ∀ {b : Bool}, bit b k < bit b n ↔ k < n
  | ff => bit0_lt_bit0
  | tt => bit1_lt_bit1

@[simp]
theorem bit_le_bit1_iff : ∀ {b : Bool}, bit b k ≤ bit1 n ↔ k ≤ n
  | ff => bit0_le_bit1_iff
  | tt => bit1_le_bit1

@[simp]
theorem bit0_mod_two : bit0 n % 2 = 0 := by
  rw [Nat.mod_two_of_bodd]
  simp

@[simp]
theorem bit1_mod_two : bit1 n % 2 = 1 := by
  rw [Nat.mod_two_of_bodd]
  simp

theorem pos_of_bit0_pos {n : ℕ} (h : 0 < bit0 n) : 0 < n := by
  cases n
  cases h
  apply succ_pos

@[simp]
theorem bit_cases_on_bit {C : ℕ → Sort u} (H : ∀ b n, C (bit b n)) (b : Bool) (n : ℕ) :
    bitCasesOn (bit b n) H = H b n :=
  eq_of_heq <|
    (eq_rec_heq _ _).trans <| by
      rw [bodd_bit, div2_bit]

@[simp]
theorem bit_cases_on_bit0 {C : ℕ → Sort u} (H : ∀ b n, C (bit b n)) (n : ℕ) : bitCasesOn (bit0 n) H = H false n :=
  bit_cases_on_bit H false n

@[simp]
theorem bit_cases_on_bit1 {C : ℕ → Sort u} (H : ∀ b n, C (bit b n)) (n : ℕ) : bitCasesOn (bit1 n) H = H true n :=
  bit_cases_on_bit H true n

theorem bit_cases_on_injective {C : ℕ → Sort u} :
    Function.Injective fun H : ∀ b n, C (bit b n) => fun n => bitCasesOn n H := by
  intro H₁ H₂ h
  ext b n
  simpa only [← bit_cases_on_bit] using congr_fun h (bit b n)

@[simp]
theorem bit_cases_on_inj {C : ℕ → Sort u} (H₁ H₂ : ∀ b n, C (bit b n)) :
    ((fun n => bitCasesOn n H₁) = fun n => bitCasesOn n H₂) ↔ H₁ = H₂ :=
  bit_cases_on_injective.eq_iff

/-! ### decidability of predicates -/


instance decidableBallLt (n : Nat) (P : ∀, ∀ k < n, ∀, Prop) :
    ∀ [H : ∀ n h, Decidable (P n h)], Decidable (∀ n h, P n h) := by
  induction' n with n IH <;> intro <;> skip
  · exact
      is_true fun n => by
        decide
    
  cases' IH fun k h => P k (lt_succ_of_lt h) with h
  · refine' is_false (mt _ h)
    intro hn k h
    apply hn
    
  by_cases' p : P n (lt_succ_self n)
  · exact
      is_true fun k h' =>
        (le_of_lt_succ h').lt_or_eq_dec.elim (h _) fun e =>
          match k, e, h' with
          | _, rfl, h => p
    
  · exact is_false (mt (fun hn => hn _ _) p)
    

instance decidableForallFin {n : ℕ} (P : Finₓ n → Prop) [H : DecidablePred P] : Decidable (∀ i, P i) :=
  decidableOfIff (∀ k h, P ⟨k, h⟩) ⟨fun a ⟨k, h⟩ => a k h, fun a k h => a ⟨k, h⟩⟩

instance decidableBallLe (n : ℕ) (P : ∀, ∀ k ≤ n, ∀, Prop) [H : ∀ n h, Decidable (P n h)] : Decidable (∀ n h, P n h) :=
  decidableOfIff (∀ (k) (h : k < succ n), P k (le_of_lt_succₓ h))
    ⟨fun a k h => a k (lt_succ_of_leₓ h), fun a k h => a k _⟩

instance decidableLoHi (lo hi : ℕ) (P : ℕ → Prop) [H : DecidablePred P] : Decidable (∀ x, lo ≤ x → x < hi → P x) :=
  decidableOfIff (∀, ∀ x < hi - lo, ∀, P (lo + x))
    ⟨fun al x hl hh => by
      have := al (x - lo) ((tsub_lt_tsub_iff_right hl).mpr hh)
      rwa [add_tsub_cancel_of_le hl] at this, fun al x h => al _ (Nat.le_add_rightₓ _ _) (lt_tsub_iff_left.mp h)⟩

instance decidableLoHiLe (lo hi : ℕ) (P : ℕ → Prop) [H : DecidablePred P] : Decidable (∀ x, lo ≤ x → x ≤ hi → P x) :=
  decidableOfIff (∀ x, lo ≤ x → x < hi + 1 → P x) <| ball_congr fun x hl => imp_congr lt_succ_iffₓ Iff.rfl

instance decidableExistsLt {P : ℕ → Prop} [h : DecidablePred P] : DecidablePred fun n => ∃ m : ℕ, m < n ∧ P m
  | 0 =>
    isFalse
      (by
        simp )
  | n + 1 =>
    decidableOfDecidableOfIff (@Or.decidable _ _ (decidable_exists_lt n) (h n))
      (by
        simp only [← lt_succ_iff_lt_or_eq, ← or_and_distrib_right, ← exists_or_distrib, ← exists_eq_left])

instance decidableExistsLe {P : ℕ → Prop} [h : DecidablePred P] : DecidablePred fun n => ∃ m : ℕ, m ≤ n ∧ P m :=
  fun n => decidableOfIff (∃ m, m < n + 1 ∧ P m) (exists_congr fun x => and_congr_left' lt_succ_iffₓ)

end Nat

