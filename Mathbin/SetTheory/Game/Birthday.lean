/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import Mathbin.SetTheory.Game.Ordinal

/-!
# Birthdays of games

The birthday of a game is an ordinal that represents at which "step" the game was constructed. We
define it recursively as the least ordinal larger than the birthdays of its left and right games. We
prove the basic properties about these.

# Main declarations

- `pgame.birthday`: The birthday of a pre-game.

# Todo

- Define the birthdays of `game`s and `surreal`s.
- Characterize the birthdays of basic arithmetical operations.
-/


universe u

open Ordinal

open Pgame

namespace Pgame

/-- The birthday of a pre-game is inductively defined as the least strict upper bound of the
birthdays of its left and right games. It may be thought as the "step" in which a certain game is
constructed. -/
noncomputable def birthday : Pgame.{u} → Ordinal.{u}
  | ⟨xl, xr, xL, xR⟩ => max (lsub.{u, u} fun i => birthday (xL i)) (lsub.{u, u} fun i => birthday (xR i))

theorem birthday_def (x : Pgame) :
    birthday x = max (lsub.{u, u} fun i => birthday (x.moveLeft i)) (lsub.{u, u} fun i => birthday (x.moveRight i)) :=
  by
  cases x
  rw [birthday]
  rfl

theorem birthday_move_left_lt {x : Pgame} (i : x.LeftMoves) : (x.moveLeft i).birthday < x.birthday := by
  cases x
  rw [birthday]
  exact lt_max_of_lt_left (lt_lsub _ i)

theorem birthday_move_right_lt {x : Pgame} (i : x.RightMoves) : (x.moveRight i).birthday < x.birthday := by
  cases x
  rw [birthday]
  exact lt_max_of_lt_right (lt_lsub _ i)

theorem lt_birthday_iff {x : Pgame} {o : Ordinal} :
    o < x.birthday ↔
      (∃ i : x.LeftMoves, o ≤ (x.moveLeft i).birthday) ∨ ∃ i : x.RightMoves, o ≤ (x.moveRight i).birthday :=
  by
  constructor
  · rw [birthday_def]
    intro h
    cases' lt_max_iff.1 h with h' h'
    · left
      rwa [lt_lsub_iff] at h'
      
    · right
      rwa [lt_lsub_iff] at h'
      
    
  · rintro (⟨i, hi⟩ | ⟨i, hi⟩)
    · exact hi.trans_lt (birthday_move_left_lt i)
      
    · exact hi.trans_lt (birthday_move_right_lt i)
      
    

theorem Relabelling.birthday_congr : ∀ {x y : Pgame.{u}}, x ≡r y → birthday x = birthday y
  | ⟨xl, xr, xL, xR⟩, ⟨yl, yr, yL, yR⟩, ⟨L, R, hL, hR⟩ => by
    rw [birthday, birthday]
    congr 1
    all_goals
      apply lsub_eq_of_range_eq.{u, u, u}
      ext i
      constructor
    · rintro ⟨j, rfl⟩
      exact ⟨L j, (hL j).birthday_congr.symm⟩
      
    · rintro ⟨j, rfl⟩
      refine' ⟨L.symm j, relabelling.birthday_congr _⟩
      convert hL (L.symm j)
      rw [L.apply_symm_apply]
      
    · rintro ⟨j, rfl⟩
      refine' ⟨R j, (relabelling.birthday_congr _).symm⟩
      convert hR (R j)
      rw [R.symm_apply_apply]
      
    · rintro ⟨j, rfl⟩
      exact ⟨R.symm j, (hR j).birthday_congr⟩
      

@[simp]
theorem birthday_add_zero (x : Pgame) : birthday (x + 0) = birthday x :=
  (addZeroRelabelling x).birthday_congr

@[simp]
theorem birthday_zero_add (x : Pgame) : birthday (0 + x) = birthday x :=
  (zeroAddRelabelling x).birthday_congr

@[simp]
theorem birthday_eq_zero (x : Pgame) : birthday x = 0 ↔ IsEmpty x.LeftMoves ∧ IsEmpty x.RightMoves := by
  rw [birthday_def, max_eq_zero, lsub_eq_zero_iff, lsub_eq_zero_iff]

@[simp]
theorem birthday_zero : birthday 0 = 0 := by
  simp [← Pempty.is_empty]

@[simp]
theorem birthday_one : birthday 1 = 1 := by
  rw [birthday_def]
  simp

@[simp]
theorem birthday_star : birthday star = 1 := by
  rw [birthday_def]
  simp

@[simp]
theorem neg_birthday : ∀ x : Pgame, (-x).birthday = x.birthday
  | ⟨xl, xr, xL, xR⟩ => by
    rw [birthday_def, birthday_def, max_commₓ]
    congr <;> funext <;> apply neg_birthday

@[simp]
theorem to_pgame_birthday (o : Ordinal) : o.toPgame.birthday = o := by
  induction' o using Ordinal.induction with o IH
  rw [to_pgame_def, Pgame.birthday]
  simp only [← lsub_empty, ← max_zero_right]
  nth_rw 0[← lsub_typein o]
  congr with x
  exact IH _ (typein_lt_self x)

theorem le_birthday : ∀ x : Pgame, x ≤ x.birthday.toPgame
  | ⟨xl, _, xL, _⟩ =>
    le_def.2
      ⟨fun i =>
        Or.inl
          ⟨toLeftMovesToPgame ⟨_, birthday_move_left_lt i⟩, by
            simp [← le_birthday (xL i)]⟩,
        isEmptyElim⟩

theorem neg_birthday_le (x : Pgame) : -x.birthday.toPgame ≤ x := by
  let h := le_birthday (-x)
  rwa [neg_birthday, neg_le_iff] at h

end Pgame

