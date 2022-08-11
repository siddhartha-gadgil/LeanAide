/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.SetTheory.Game.Short

/-!
# Games described via "the state of the board".

We provide a simple mechanism for constructing combinatorial (pre-)games, by describing
"the state of the board", and providing an upper bound on the number of turns remaining.


## Implementation notes

We're very careful to produce a computable definition, so small games can be evaluated
using `dec_trivial`. To achieve this, I've had to rely solely on induction on natural numbers:
relying on general well-foundedness seems to be poisonous to computation?

See `set_theory/game/domineering` for an example using this construction.
-/


universe u

namespace Pgame

/-- `pgame_state S` describes how to interpret `s : S` as a state of a combinatorial game.
Use `pgame.of_state s` or `game.of_state s` to construct the game.

`pgame_state.L : S → finset S` and `pgame_state.R : S → finset S` describe the states reachable
by a move by Left or Right. `pgame_state.turn_bound : S → ℕ` gives an upper bound on the number of
possible turns remaining from this state.
-/
class State (S : Type u) where
  turnBound : S → ℕ
  l : S → Finset S
  r : S → Finset S
  left_bound : ∀ {s t : S} (m : t ∈ L s), turn_bound t < turn_bound s
  right_bound : ∀ {s t : S} (m : t ∈ R s), turn_bound t < turn_bound s

open State

variable {S : Type u} [State S]

theorem turn_bound_ne_zero_of_left_move {s t : S} (m : t ∈ l s) : turnBound s ≠ 0 := by
  intro h
  have t := state.left_bound m
  rw [h] at t
  exact Nat.not_succ_le_zeroₓ _ t

theorem turn_bound_ne_zero_of_right_move {s t : S} (m : t ∈ r s) : turnBound s ≠ 0 := by
  intro h
  have t := state.right_bound m
  rw [h] at t
  exact Nat.not_succ_le_zeroₓ _ t

theorem turn_bound_of_left {s t : S} (m : t ∈ l s) (n : ℕ) (h : turnBound s ≤ n + 1) : turnBound t ≤ n :=
  Nat.le_of_lt_succₓ (Nat.lt_of_lt_of_leₓ (left_bound m) h)

theorem turn_bound_of_right {s t : S} (m : t ∈ r s) (n : ℕ) (h : turnBound s ≤ n + 1) : turnBound t ≤ n :=
  Nat.le_of_lt_succₓ (Nat.lt_of_lt_of_leₓ (right_bound m) h)

/-- Construct a `pgame` from a state and a (not necessarily optimal) bound on the number of
turns remaining.
-/
def ofStateAux : ∀ (n : ℕ) (s : S) (h : turnBound s ≤ n), Pgame
  | 0, s, h =>
    Pgame.mk { t // t ∈ l s } { t // t ∈ r s }
      (fun t => by
        exfalso
        exact turn_bound_ne_zero_of_left_move t.2 (nonpos_iff_eq_zero.mp h))
      fun t => by
      exfalso
      exact turn_bound_ne_zero_of_right_move t.2 (nonpos_iff_eq_zero.mp h)
  | n + 1, s, h =>
    Pgame.mk { t // t ∈ l s } { t // t ∈ r s } (fun t => of_state_aux n t (turn_bound_of_left t.2 n h)) fun t =>
      of_state_aux n t (turn_bound_of_right t.2 n h)

/-- Two different (valid) turn bounds give equivalent games. -/
def ofStateAuxRelabelling :
    ∀ (s : S) (n m : ℕ) (hn : turnBound s ≤ n) (hm : turnBound s ≤ m),
      Relabelling (ofStateAux n s hn) (ofStateAux m s hm)
  | s, 0, 0, hn, hm => by
    dsimp' [← Pgame.ofStateAux]
    fconstructor
    rfl
    rfl
    · intro i
      dsimp'  at i
      exfalso
      exact turn_bound_ne_zero_of_left_move i.2 (nonpos_iff_eq_zero.mp hn)
      
    · intro j
      dsimp'  at j
      exfalso
      exact turn_bound_ne_zero_of_right_move j.2 (nonpos_iff_eq_zero.mp hm)
      
  | s, 0, m + 1, hn, hm => by
    dsimp' [← Pgame.ofStateAux]
    fconstructor
    rfl
    rfl
    · intro i
      dsimp'  at i
      exfalso
      exact turn_bound_ne_zero_of_left_move i.2 (nonpos_iff_eq_zero.mp hn)
      
    · intro j
      dsimp'  at j
      exfalso
      exact turn_bound_ne_zero_of_right_move j.2 (nonpos_iff_eq_zero.mp hn)
      
  | s, n + 1, 0, hn, hm => by
    dsimp' [← Pgame.ofStateAux]
    fconstructor
    rfl
    rfl
    · intro i
      dsimp'  at i
      exfalso
      exact turn_bound_ne_zero_of_left_move i.2 (nonpos_iff_eq_zero.mp hm)
      
    · intro j
      dsimp'  at j
      exfalso
      exact turn_bound_ne_zero_of_right_move j.2 (nonpos_iff_eq_zero.mp hm)
      
  | s, n + 1, m + 1, hn, hm => by
    dsimp' [← Pgame.ofStateAux]
    fconstructor
    rfl
    rfl
    · intro i
      apply of_state_aux_relabelling
      
    · intro j
      apply of_state_aux_relabelling
      

/-- Construct a combinatorial `pgame` from a state. -/
def ofState (s : S) : Pgame :=
  ofStateAux (turnBound s) s (refl _)

/-- The equivalence between `left_moves` for a `pgame` constructed using `of_state_aux _ s _`, and
`L s`. -/
def leftMovesOfStateAux (n : ℕ) {s : S} (h : turnBound s ≤ n) : LeftMoves (ofStateAux n s h) ≃ { t // t ∈ l s } := by
  induction n <;> rfl

/-- The equivalence between `left_moves` for a `pgame` constructed using `of_state s`, and `L s`. -/
def leftMovesOfState (s : S) : LeftMoves (ofState s) ≃ { t // t ∈ l s } :=
  leftMovesOfStateAux _ _

/-- The equivalence between `right_moves` for a `pgame` constructed using `of_state_aux _ s _`, and
`R s`. -/
def rightMovesOfStateAux (n : ℕ) {s : S} (h : turnBound s ≤ n) : RightMoves (ofStateAux n s h) ≃ { t // t ∈ r s } := by
  induction n <;> rfl

/-- The equivalence between `right_moves` for a `pgame` constructed using `of_state s`, and
`R s`. -/
def rightMovesOfState (s : S) : RightMoves (ofState s) ≃ { t // t ∈ r s } :=
  rightMovesOfStateAux _ _

/-- The relabelling showing `move_left` applied to a game constructed using `of_state_aux`
has itself been constructed using `of_state_aux`.
-/
def relabellingMoveLeftAux (n : ℕ) {s : S} (h : turnBound s ≤ n) (t : LeftMoves (ofStateAux n s h)) :
    Relabelling (moveLeft (ofStateAux n s h) t)
      (ofStateAux (n - 1) ((leftMovesOfStateAux n h) t : S)
        (turn_bound_of_left ((leftMovesOfStateAux n h) t).2 (n - 1) (Nat.le_transₓ h le_tsub_add))) :=
  by
  induction n
  · have t' := (left_moves_of_state_aux 0 h) t
    exfalso
    exact turn_bound_ne_zero_of_left_move t'.2 (nonpos_iff_eq_zero.mp h)
    
  · rfl
    

/-- The relabelling showing `move_left` applied to a game constructed using `of`
has itself been constructed using `of`.
-/
def relabellingMoveLeft (s : S) (t : LeftMoves (ofState s)) :
    Relabelling (moveLeft (ofState s) t) (ofState ((leftMovesOfState s).toFun t : S)) := by
  trans
  apply relabelling_move_left_aux
  apply of_state_aux_relabelling

/-- The relabelling showing `move_right` applied to a game constructed using `of_state_aux`
has itself been constructed using `of_state_aux`.
-/
def relabellingMoveRightAux (n : ℕ) {s : S} (h : turnBound s ≤ n) (t : RightMoves (ofStateAux n s h)) :
    Relabelling (moveRight (ofStateAux n s h) t)
      (ofStateAux (n - 1) ((rightMovesOfStateAux n h) t : S)
        (turn_bound_of_right ((rightMovesOfStateAux n h) t).2 (n - 1) (Nat.le_transₓ h le_tsub_add))) :=
  by
  induction n
  · have t' := (right_moves_of_state_aux 0 h) t
    exfalso
    exact turn_bound_ne_zero_of_right_move t'.2 (nonpos_iff_eq_zero.mp h)
    
  · rfl
    

/-- The relabelling showing `move_right` applied to a game constructed using `of`
has itself been constructed using `of`.
-/
def relabellingMoveRight (s : S) (t : RightMoves (ofState s)) :
    Relabelling (moveRight (ofState s) t) (ofState ((rightMovesOfState s).toFun t : S)) := by
  trans
  apply relabelling_move_right_aux
  apply of_state_aux_relabelling

instance fintypeLeftMovesOfStateAux (n : ℕ) (s : S) (h : turnBound s ≤ n) : Fintype (LeftMoves (ofStateAux n s h)) := by
  apply Fintype.ofEquiv _ (left_moves_of_state_aux _ _).symm
  infer_instance

instance fintypeRightMovesOfStateAux (n : ℕ) (s : S) (h : turnBound s ≤ n) : Fintype (RightMoves (ofStateAux n s h)) :=
  by
  apply Fintype.ofEquiv _ (right_moves_of_state_aux _ _).symm
  infer_instance

instance shortOfStateAux : ∀ (n : ℕ) {s : S} (h : turnBound s ≤ n), Short (ofStateAux n s h)
  | 0, s, h =>
    Short.mk'
      (fun i => by
        have i := (left_moves_of_state_aux _ _).toFun i
        exfalso
        exact turn_bound_ne_zero_of_left_move i.2 (nonpos_iff_eq_zero.mp h))
      fun j => by
      have j := (right_moves_of_state_aux _ _).toFun j
      exfalso
      exact turn_bound_ne_zero_of_right_move j.2 (nonpos_iff_eq_zero.mp h)
  | n + 1, s, h =>
    Short.mk' (fun i => shortOfRelabelling (relabellingMoveLeftAux (n + 1) h i).symm (short_of_state_aux n _)) fun j =>
      shortOfRelabelling (relabellingMoveRightAux (n + 1) h j).symm (short_of_state_aux n _)

instance shortOfState (s : S) : Short (ofState s) := by
  dsimp' [← Pgame.ofState]
  infer_instance

end Pgame

namespace Game

/-- Construct a combinatorial `game` from a state. -/
def ofState {S : Type u} [Pgame.State S] (s : S) : Game :=
  ⟦Pgame.ofState s⟧

end Game

