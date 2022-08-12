/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.SetTheory.Game.State

/-!
# Domineering as a combinatorial game.

We define the game of Domineering, played on a chessboard of arbitrary shape
(possibly even disconnected).
Left moves by placing a domino vertically, while Right moves by placing a domino horizontally.

This is only a fragment of a full development;
in order to successfully analyse positions we would need some more theorems.
Most importantly, we need a general statement that allows us to discard irrelevant moves.
Specifically to domineering, we need the fact that
disjoint parts of the chessboard give sums of games.
-/


namespace Pgame

namespace Domineering

open Function

/-- The equivalence `(x, y) ↦ (x, y+1)`. -/
@[simps]
def shiftUp : ℤ × ℤ ≃ ℤ × ℤ :=
  (Equivₓ.refl ℤ).prodCongr (Equivₓ.addRight (1 : ℤ))

/-- The equivalence `(x, y) ↦ (x+1, y)`. -/
@[simps]
def shiftRight : ℤ × ℤ ≃ ℤ × ℤ :=
  (Equivₓ.addRight (1 : ℤ)).prodCongr (Equivₓ.refl ℤ)

/-- A Domineering board is an arbitrary finite subset of `ℤ × ℤ`. -/
def Board :=
  Finset (ℤ × ℤ)deriving Inhabited

attribute [local reducible] board

/-- Left can play anywhere that a square and the square below it are open. -/
def left (b : Board) : Finset (ℤ × ℤ) :=
  b ∩ b.map shiftUp

/-- Right can play anywhere that a square and the square to the left are open. -/
def right (b : Board) : Finset (ℤ × ℤ) :=
  b ∩ b.map shiftRight

theorem mem_left {b : Board} (x : ℤ × ℤ) : x ∈ left b ↔ x ∈ b ∧ (x.1, x.2 - 1) ∈ b :=
  Finset.mem_inter.trans (and_congr Iff.rfl Finset.mem_map_equiv)

theorem mem_right {b : Board} (x : ℤ × ℤ) : x ∈ right b ↔ x ∈ b ∧ (x.1 - 1, x.2) ∈ b :=
  Finset.mem_inter.trans (and_congr Iff.rfl Finset.mem_map_equiv)

/-- After Left moves, two vertically adjacent squares are removed from the board. -/
def moveLeft (b : Board) (m : ℤ × ℤ) : Board :=
  (b.erase m).erase (m.1, m.2 - 1)

/-- After Left moves, two horizontally adjacent squares are removed from the board. -/
def moveRight (b : Board) (m : ℤ × ℤ) : Board :=
  (b.erase m).erase (m.1 - 1, m.2)

theorem fst_pred_mem_erase_of_mem_right {b : Board} {m : ℤ × ℤ} (h : m ∈ right b) : (m.1 - 1, m.2) ∈ b.erase m := by
  rw [mem_right] at h
  apply Finset.mem_erase_of_ne_of_mem _ h.2
  exact ne_of_apply_ne Prod.fst (pred_ne_self m.1)

theorem snd_pred_mem_erase_of_mem_left {b : Board} {m : ℤ × ℤ} (h : m ∈ left b) : (m.1, m.2 - 1) ∈ b.erase m := by
  rw [mem_left] at h
  apply Finset.mem_erase_of_ne_of_mem _ h.2
  exact ne_of_apply_ne Prod.snd (pred_ne_self m.2)

theorem card_of_mem_left {b : Board} {m : ℤ × ℤ} (h : m ∈ left b) : 2 ≤ Finset.card b := by
  have w₁ : m ∈ b := (Finset.mem_inter.1 h).1
  have w₂ : (m.1, m.2 - 1) ∈ b.erase m := snd_pred_mem_erase_of_mem_left h
  have i₁ := Finset.card_erase_lt_of_mem w₁
  have i₂ := Nat.lt_of_le_of_ltₓ (Nat.zero_leₓ _) (Finset.card_erase_lt_of_mem w₂)
  exact Nat.lt_of_le_of_ltₓ i₂ i₁

theorem card_of_mem_right {b : Board} {m : ℤ × ℤ} (h : m ∈ right b) : 2 ≤ Finset.card b := by
  have w₁ : m ∈ b := (Finset.mem_inter.1 h).1
  have w₂ := fst_pred_mem_erase_of_mem_right h
  have i₁ := Finset.card_erase_lt_of_mem w₁
  have i₂ := Nat.lt_of_le_of_ltₓ (Nat.zero_leₓ _) (Finset.card_erase_lt_of_mem w₂)
  exact Nat.lt_of_le_of_ltₓ i₂ i₁

theorem move_left_card {b : Board} {m : ℤ × ℤ} (h : m ∈ left b) : Finset.card (moveLeft b m) + 2 = Finset.card b := by
  dsimp' [← move_left]
  rw [Finset.card_erase_of_mem (snd_pred_mem_erase_of_mem_left h)]
  rw [Finset.card_erase_of_mem (Finset.mem_of_mem_inter_left h)]
  exact tsub_add_cancel_of_le (card_of_mem_left h)

theorem move_right_card {b : Board} {m : ℤ × ℤ} (h : m ∈ right b) : Finset.card (moveRight b m) + 2 = Finset.card b :=
  by
  dsimp' [← move_right]
  rw [Finset.card_erase_of_mem (fst_pred_mem_erase_of_mem_right h)]
  rw [Finset.card_erase_of_mem (Finset.mem_of_mem_inter_left h)]
  exact tsub_add_cancel_of_le (card_of_mem_right h)

theorem move_left_smaller {b : Board} {m : ℤ × ℤ} (h : m ∈ left b) :
    Finset.card (moveLeft b m) / 2 < Finset.card b / 2 := by
  simp [move_left_card h, ← lt_add_one]

theorem move_right_smaller {b : Board} {m : ℤ × ℤ} (h : m ∈ right b) :
    Finset.card (moveRight b m) / 2 < Finset.card b / 2 := by
  simp [move_right_card h, ← lt_add_one]

/-- The instance describing allowed moves on a Domineering board. -/
instance state : State Board where
  turnBound := fun s => s.card / 2
  l := fun s => (left s).Image (moveLeft s)
  r := fun s => (right s).Image (moveRight s)
  left_bound := fun s t m => by
    simp only [← Finset.mem_image, ← Prod.exists] at m
    rcases m with ⟨_, _, ⟨h, rfl⟩⟩
    exact move_left_smaller h
  right_bound := fun s t m => by
    simp only [← Finset.mem_image, ← Prod.exists] at m
    rcases m with ⟨_, _, ⟨h, rfl⟩⟩
    exact move_right_smaller h

end Domineering

/-- Construct a pre-game from a Domineering board. -/
def domineering (b : Domineering.Board) : Pgame :=
  Pgame.ofState b

/-- All games of Domineering are short, because each move removes two squares. -/
instance shortDomineering (b : Domineering.Board) : Short (domineering b) := by
  dsimp' [← domineering]
  infer_instance

/-- The Domineering board with two squares arranged vertically, in which Left has the only move. -/
def domineering.one :=
  domineering [(0, 0), (0, 1)].toFinset

/-- The `L` shaped Domineering board, in which Left is exactly half a move ahead. -/
def domineering.l :=
  domineering [(0, 2), (0, 1), (0, 0), (1, 0)].toFinset

instance shortOne : Short domineering.one := by
  dsimp' [← domineering.one]
  infer_instance

instance shortL : Short domineering.l := by
  dsimp' [← domineering.L]
  infer_instance

-- The VM can play small games successfully:
-- #eval to_bool (domineering.one ≈ 1)
-- #eval to_bool (domineering.L + domineering.L ≈ 1)
-- The following no longer works since Lean 3.29, since definitions by well-founded
-- recursion no longer reduce definitionally.
-- We can check that `decidable` instances reduce as expected,
-- and so our implementation of domineering is computable.
-- run_cmd tactic.whnf `(by apply_instance : decidable (domineering.one ≤ 1)) >>= tactic.trace
-- dec_trivial can handle most of the dictionary of small games described in [conway2001]
-- example : domineering.one ≈ 1 := dec_trivial
-- example : domineering.L + domineering.L ≈ 1 := dec_trivial
-- example : domineering.L ≈ pgame.of_lists [0] [1] := dec_trivial
-- example : (domineering ([(0,0), (0,1), (0,2), (0,3)].to_finset) ≈ 2) := dec_trivial
-- example : (domineering ([(0,0), (0,1), (1,0), (1,1)].to_finset) ≈ pgame.of_lists [1] [-1]) :=
--   dec_trivial.
-- The 3x3 grid is doable, but takes a minute...
-- example :
--   (domineering ([(0,0), (0,1), (0,2), (1,0), (1,1), (1,2), (2,0), (2,1), (2,2)].to_finset) ≈
--     pgame.of_lists [1] [-1]) := dec_trivial
-- The 5x5 grid is actually 0, but brute-forcing this is too challenging even for the VM.
-- #eval to_bool (domineering ([
--   (0,0), (0,1), (0,2), (0,3), (0,4),
--   (1,0), (1,1), (1,2), (1,3), (1,4),
--   (2,0), (2,1), (2,2), (2,3), (2,4),
--   (3,0), (3,1), (3,2), (3,3), (3,4),
--   (4,0), (4,1), (4,2), (4,3), (4,4)
--   ].to_finset) ≈ 0)
end Pgame

