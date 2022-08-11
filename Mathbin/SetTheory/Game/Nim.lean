/-
Copyright (c) 2020 Fox Thomson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fox Thomson, Markus Himmel
-/
import Mathbin.Data.Nat.Bitwise
import Mathbin.SetTheory.Game.Birthday
import Mathbin.SetTheory.Game.Impartial

/-!
# Nim and the Sprague-Grundy theorem

This file contains the definition for nim for any ordinal `o`. In the game of `nim o₁` both players
may move to `nim o₂` for any `o₂ < o₁`.
We also define a Grundy value for an impartial game `G` and prove the Sprague-Grundy theorem, that
`G` is equivalent to `nim (grundy_value G)`.
Finally, we compute the sum of finite Grundy numbers: if `G` and `H` have Grundy values `n` and `m`,
where `n` and `m` are natural numbers, then `G + H` has the Grundy value `n xor m`.

## Implementation details

The pen-and-paper definition of nim defines the possible moves of `nim o` to be `{o' | o' < o}`.
However, this definition does not work for us because it would make the type of nim
`ordinal.{u} → pgame.{u + 1}`, which would make it impossible for us to state the Sprague-Grundy
theorem, since that requires the type of `nim` to be `ordinal.{u} → pgame.{u}`. For this reason, we
instead use `o.out.α` for the possible moves, which makes proofs significantly more messy and
tedious, but avoids the universe bump.

The lemma `nim_def` is somewhat prone to produce "motive is not type correct" errors. If you run
into this problem, you may find the lemmas `exists_ordinal_move_left_eq` and `exists_move_left_eq`
useful.

-/


universe u

/-- `ordinal.out'` has the sole purpose of making `nim` computable. It performs the same job as
  `quotient.out` but is specific to ordinals. -/
def Ordinal.out' (o : Ordinal) : WellOrder :=
  ⟨o.out.α, (· < ·), o.out.wo⟩

/-- The definition of single-heap nim, which can be viewed as a pile of stones where each player can
  take a positive number of stones from it on their turn. -/
def nim : Ordinal → Pgame
  | o₁ =>
    let f := fun o₂ =>
      have hwf : Ordinal.typein o₁.out'.R o₂ < o₁ := Ordinal.typein_lt_self o₂
      nim (Ordinal.typein o₁.out'.R o₂)
    ⟨o₁.out'.α, o₁.out'.α, f, f⟩

namespace Pgame

-- mathport name: «expr ⧏ »
local infixl:50 " ⧏ " => Lf

-- mathport name: «expr ≈ »
local infixl:0 " ≈ " => Equiv

-- mathport name: «expr ∥ »
local infixl:50 " ∥ " => Fuzzy

-- mathport name: «expr ≡r »
local infixl:50 " ≡r " => Relabelling

namespace nim

open Ordinal

theorem nim_def (o : Ordinal) :
    nim o =
      Pgame.mk o.out.α o.out.α (fun o₂ => nim (Ordinal.typein (· < ·) o₂)) fun o₂ => nim (Ordinal.typein (· < ·) o₂) :=
  by
  rw [nim]
  rfl

instance : IsEmpty (nim 0).LeftMoves := by
  rw [nim_def]
  exact Ordinal.is_empty_out_zero

instance : IsEmpty (nim 0).RightMoves := by
  rw [nim_def]
  exact Ordinal.is_empty_out_zero

noncomputable instance : Unique (nim 1).LeftMoves := by
  rw [nim_def]
  exact Ordinal.uniqueOutOne

noncomputable instance : Unique (nim 1).RightMoves := by
  rw [nim_def]
  exact Ordinal.uniqueOutOne

/-- `nim 0` has exactly the same moves as `0`. -/
def nimZeroRelabelling : nim 0 ≡r 0 :=
  Relabelling.isEmpty _

@[simp]
theorem nim_zero_equiv : nim 0 ≈ 0 :=
  Equiv.is_empty _

-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:51:50: missing argument
/-- `nim 1` has exactly the same moves as `star`. -/
noncomputable def nimOneRelabelling : nim 1 ≡r star := by
  rw [nim_def]
  refine' ⟨_, _, fun i => _, fun j => _⟩
  any_goals {
  }
  all_goals
    simp
    exact nim_zero_relabelling

@[simp]
theorem nim_one_equiv : nim 1 ≈ star :=
  nimOneRelabelling.Equiv

@[simp]
theorem nim_birthday (o : Ordinal) : (nim o).birthday = o := by
  induction' o using Ordinal.induction with o IH
  rw [nim_def, birthday_def]
  dsimp'
  rw [max_eq_rightₓ le_rfl]
  convert lsub_typein o
  exact funext fun i => IH _ (typein_lt_self i)

theorem left_moves_nim (o : Ordinal) : (nim o).LeftMoves = o.out.α := by
  rw [nim_def]
  rfl

theorem right_moves_nim (o : Ordinal) : (nim o).RightMoves = o.out.α := by
  rw [nim_def]
  rfl

theorem move_left_nim_heq (o : Ordinal) : HEq (nim o).moveLeft fun i : o.out.α => nim (typein (· < ·) i) := by
  rw [nim_def]
  rfl

theorem move_right_nim_heq (o : Ordinal) : HEq (nim o).moveRight fun i : o.out.α => nim (typein (· < ·) i) := by
  rw [nim_def]
  rfl

/-- Turns an ordinal less than `o` into a left move for `nim o` and viceversa. -/
noncomputable def toLeftMovesNim {o : Ordinal} : Set.Iio o ≃ (nim o).LeftMoves :=
  (enumIsoOut o).toEquiv.trans (Equivₓ.cast (left_moves_nim o).symm)

/-- Turns an ordinal less than `o` into a right move for `nim o` and viceversa. -/
noncomputable def toRightMovesNim {o : Ordinal} : Set.Iio o ≃ (nim o).RightMoves :=
  (enumIsoOut o).toEquiv.trans (Equivₓ.cast (right_moves_nim o).symm)

@[simp]
theorem to_left_moves_nim_symm_lt {o : Ordinal} (i : (nim o).LeftMoves) : ↑(toLeftMovesNim.symm i) < o :=
  (toLeftMovesNim.symm i).Prop

@[simp]
theorem to_right_moves_nim_symm_lt {o : Ordinal} (i : (nim o).RightMoves) : ↑(toRightMovesNim.symm i) < o :=
  (toRightMovesNim.symm i).Prop

@[simp]
theorem move_left_nim' {o : Ordinal.{u}} (i) : (nim o).moveLeft i = nim (toLeftMovesNim.symm i).val :=
  (congr_heq (move_left_nim_heq o).symm (cast_heq _ i)).symm

theorem move_left_nim {o : Ordinal} (i) : (nim o).moveLeft (toLeftMovesNim i) = nim i := by
  simp

@[simp]
theorem move_right_nim' {o : Ordinal} (i) : (nim o).moveRight i = nim (toRightMovesNim.symm i).val :=
  (congr_heq (move_right_nim_heq o).symm (cast_heq _ i)).symm

theorem move_right_nim {o : Ordinal} (i) : (nim o).moveRight (toRightMovesNim i) = nim i := by
  simp

@[simp]
theorem neg_nim (o : Ordinal) : -nim o = nim o := by
  induction' o using Ordinal.induction with o IH
  rw [nim_def]
  dsimp' <;> congr <;> funext i <;> exact IH _ (Ordinal.typein_lt_self i)

instance nim_impartial (o : Ordinal) : Impartial (nim o) := by
  induction' o using Ordinal.induction with o IH
  rw [impartial_def, neg_nim]
  refine' ⟨equiv_rfl, fun i => _, fun i => _⟩ <;> simpa using IH _ (typein_lt_self _)

theorem exists_ordinal_move_left_eq {o : Ordinal} (i) : ∃ o' < o, (nim o).moveLeft i = nim o' :=
  ⟨_, typein_lt_self _, move_left_nim' i⟩

theorem exists_move_left_eq {o o' : Ordinal} (h : o' < o) : ∃ i, (nim o).moveLeft i = nim o' :=
  ⟨toLeftMovesNim ⟨o', h⟩, by
    simp ⟩

theorem non_zero_first_wins {o : Ordinal} (ho : o ≠ 0) : nim o ∥ 0 := by
  rw [impartial.fuzzy_zero_iff_lf, nim_def, lf_zero_le]
  rw [← Ordinal.pos_iff_ne_zero] at ho
  exact
    ⟨(Ordinal.principalSegOut ho).top, by
      simp ⟩

@[simp]
theorem add_equiv_zero_iff_eq (o₁ o₂ : Ordinal) : (nim o₁ + nim o₂ ≈ 0) ↔ o₁ = o₂ := by
  constructor
  · contrapose
    intro h
    rw [impartial.not_equiv_zero_iff]
    wlog h' : o₁ ≤ o₂ using o₁ o₂, o₂ o₁
    · exact le_totalₓ o₁ o₂
      
    · have h : o₁ < o₂ := lt_of_le_of_neₓ h' h
      rw [impartial.fuzzy_zero_iff_gf, zero_lf_le, nim_def o₂]
      refine' ⟨to_left_moves_add (Sum.inr _), _⟩
      · exact (Ordinal.principalSegOut h).top
        
      · simpa using (impartial.add_self (nim o₁)).2
        
      
    · exact (fuzzy_congr_left add_comm_equiv).1 (this (Ne.symm h))
      
    
  · rintro rfl
    exact impartial.add_self (nim o₁)
    

@[simp]
theorem add_fuzzy_zero_iff_ne (o₁ o₂ : Ordinal) : nim o₁ + nim o₂ ∥ 0 ↔ o₁ ≠ o₂ := by
  rw [iff_not_comm, impartial.not_fuzzy_zero_iff, add_equiv_zero_iff_eq]

@[simp]
theorem equiv_iff_eq (o₁ o₂ : Ordinal) : (nim o₁ ≈ nim o₂) ↔ o₁ = o₂ := by
  rw [impartial.equiv_iff_add_equiv_zero, add_equiv_zero_iff_eq]

end nim

/-- The Grundy value of an impartial game, the ordinal which corresponds to the game of nim that the
 game is equivalent to -/
noncomputable def grundyValue : ∀ G : Pgame.{u}, Ordinal.{u}
  | G => Ordinal.mex.{u, u} fun i => grundy_value (G.moveLeft i)

theorem grundy_value_def (G : Pgame) : grundyValue G = Ordinal.mex.{u, u} fun i => grundyValue (G.moveLeft i) := by
  rw [grundy_value]

/-- The Sprague-Grundy theorem which states that every impartial game is equivalent to a game of
 nim, namely the game of nim corresponding to the games Grundy value -/
theorem equiv_nim_grundy_value : ∀ (G : Pgame.{u}) [G.Impartial], G ≈ nim (grundyValue G)
  | G => by
    intro hG
    rw [impartial.equiv_iff_add_equiv_zero, ← impartial.forall_left_moves_fuzzy_iff_equiv_zero]
    intro i
    apply left_moves_add_cases i
    · intro i₁
      rw [add_move_left_inl]
      apply (fuzzy_congr_left (add_congr_left (equiv_nim_grundy_value (G.move_left i₁)).symm)).1
      rw [nim.add_fuzzy_zero_iff_ne]
      intro heq
      rw [eq_comm, grundy_value_def G] at heq
      have h := Ordinal.ne_mex _
      rw [HEq] at h
      exact (h i₁).irrefl
      
    · intro i₂
      rw [add_move_left_inr, ← impartial.exists_left_move_equiv_iff_fuzzy_zero]
      revert i₂
      rw [nim.nim_def]
      intro i₂
      have h' :
        ∃ i : G.left_moves, grundy_value (G.move_left i) = Ordinal.typein (Quotientₓ.out (grundy_value G)).R i₂ := by
        revert i₂
        rw [grundy_value_def]
        intro i₂
        have hnotin : _ ∉ _ := fun hin => (le_not_le_of_ltₓ (Ordinal.typein_lt_self i₂)).2 (cInf_le' hin)
        simpa using hnotin
      cases' h' with i hi
      use to_left_moves_add (Sum.inl i)
      rw [add_move_left_inl, move_left_mk]
      apply (add_congr_left (equiv_nim_grundy_value (G.move_left i))).trans
      simpa only [← hi] using impartial.add_self (nim (grundy_value (G.move_left i)))
      

@[simp]
theorem grundy_value_eq_iff_equiv_nim (G : Pgame) [G.Impartial] (o : Ordinal) : grundyValue G = o ↔ (G ≈ nim o) :=
  ⟨by
    rintro rfl
    exact equiv_nim_grundy_value G, by
    intro h
    rw [← nim.equiv_iff_eq]
    exact (equiv_nim_grundy_value G).symm.trans h⟩

theorem Nim.grundy_value (o : Ordinal.{u}) : grundyValue (nim o) = o := by
  simp

@[simp]
theorem grundy_value_eq_iff_equiv (G H : Pgame) [G.Impartial] [H.Impartial] : grundyValue G = grundyValue H ↔ (G ≈ H) :=
  (grundy_value_eq_iff_equiv_nim _ _).trans (equiv_congr_left.1 (equiv_nim_grundy_value H) _).symm

@[simp]
theorem grundy_value_zero : grundyValue 0 = 0 := by
  simp [← nim.nim_zero_equiv.symm]

@[simp]
theorem grundy_value_iff_equiv_zero (G : Pgame) [G.Impartial] : grundyValue G = 0 ↔ (G ≈ 0) := by
  rw [← grundy_value_eq_iff_equiv, grundy_value_zero]

theorem grundy_value_star : grundyValue star = 1 := by
  simp [← nim.nim_one_equiv.symm]

@[simp]
theorem grundy_value_nim_add_nim (n m : ℕ) : grundyValue (nim.{u} n + nim.{u} m) = Nat.lxor n m := by
  induction' n using Nat.strong_induction_onₓ with n hn generalizing m
  induction' m using Nat.strong_induction_onₓ with m hm
  rw [grundy_value_def]
  -- We want to show that `n xor m` is the smallest unreachable Grundy value. We will do this in two
  -- steps:
  -- h₀: `n xor m` is not a reachable grundy number.
  -- h₁: every Grundy number strictly smaller than `n xor m` is reachable.
  have h₀ : ∀ i, grundy_value ((nim n + nim m).moveLeft i) ≠ (Nat.lxor n m : Ordinal) := by
    -- To show that `n xor m` is unreachable, we show that every move produces a Grundy number
    -- different from `n xor m`.
    intro i
    -- The move operates either on the left pile or on the right pile.
    apply left_moves_add_cases i
    all_goals
      -- One of the piles is reduced to `k` stones, with `k < n` or `k < m`.
      intro a
      obtain ⟨ok, hk, hk'⟩ := nim.exists_ordinal_move_left_eq a
      obtain ⟨k, rfl⟩ := Ordinal.lt_omega.1 (lt_transₓ hk (Ordinal.nat_lt_omega _))
      replace hk := Ordinal.nat_cast_lt.1 hk
      -- Thus, the problem is reduced to computing the Grundy value of `nim n + nim k` or
      -- `nim k + nim m`, both of which can be dealt with using an inductive hypothesis.
      simp only [← hk', ← add_move_left_inl, ← add_move_left_inr, ← id]
      first |
        rw [hn _ hk]|
        rw [hm _ hk]
      -- But of course xor is injective, so if we change one of the arguments, we will not get the
      -- same value again.
      intro h
      rw [Ordinal.nat_cast_inj] at h
      try
        rw [Nat.lxor_comm n k, Nat.lxor_comm n m] at h
      exact hk.ne (Nat.lxor_left_injective h)
  have h₁ : ∀ u : Ordinal, u < Nat.lxor n m → u ∈ Set.Range fun i => grundy_value ((nim n + nim m).moveLeft i) := by
    -- Take any natural number `u` less than `n xor m`.
    intro ou hu
    obtain ⟨u, rfl⟩ := Ordinal.lt_omega.1 (lt_transₓ hu (Ordinal.nat_lt_omega _))
    replace hu := Ordinal.nat_cast_lt.1 hu
    -- Our goal is to produce a move that gives the Grundy value `u`.
    rw [Set.mem_range]
    -- By a lemma about xor, either `u xor m < n` or `u xor n < m`.
    cases' Nat.lt_lxor_cases hu with h h
    -- Therefore, we can play the corresponding move, and by the inductive hypothesis the new state
    -- is `(u xor m) xor m = u` or `n xor (u xor n) = u` as required.
    · obtain ⟨i, hi⟩ := nim.exists_move_left_eq (Ordinal.nat_cast_lt.2 h)
      refine' ⟨to_left_moves_add (Sum.inl i), _⟩
      simp only [← hi, ← add_move_left_inl]
      rw [hn _ h, Nat.lxor_assoc, Nat.lxor_self, Nat.lxor_zero]
      
    · obtain ⟨i, hi⟩ := nim.exists_move_left_eq (Ordinal.nat_cast_lt.2 h)
      refine' ⟨to_left_moves_add (Sum.inr i), _⟩
      simp only [← hi, ← add_move_left_inr]
      rw [hm _ h, Nat.lxor_comm, Nat.lxor_assoc, Nat.lxor_self, Nat.lxor_zero]
      
  -- We are done!
  apply (Ordinal.mex_le_of_ne.{u, u} h₀).antisymm
  contrapose! h₁
  exact ⟨_, ⟨h₁, Ordinal.mex_not_mem_range _⟩⟩

theorem nim_add_nim_equiv {n m : ℕ} : nim n + nim m ≈ nim (Nat.lxor n m) := by
  rw [← grundy_value_eq_iff_equiv_nim, grundy_value_nim_add_nim]

theorem grundy_value_add (G H : Pgame) [G.Impartial] [H.Impartial] {n m : ℕ} (hG : grundyValue G = n)
    (hH : grundyValue H = m) : grundyValue (G + H) = Nat.lxor n m := by
  rw [← nim.grundy_value (Nat.lxor n m), grundy_value_eq_iff_equiv]
  refine' Equivₓ.trans _ nim_add_nim_equiv
  convert add_congr (equiv_nim_grundy_value G) (equiv_nim_grundy_value H) <;> simp only [← hG, ← hH]

end Pgame

