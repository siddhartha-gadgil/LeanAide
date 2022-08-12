/-
Copyright (c) 2020 Fox Thomson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fox Thomson
-/
import Mathbin.SetTheory.Game.Basic
import Mathbin.Tactic.NthRewrite.Default

/-!
# Basic definitions about impartial (pre-)games

We will define an impartial game, one in which left and right can make exactly the same moves.
Our definition differs slightly by saying that the game is always equivalent to its negative,
no matter what moves are played. This allows for games such as poker-nim to be classifed as
impartial.
-/


universe u

open Pgame

namespace Pgame

/-- The definition for a impartial game, defined using Conway induction. -/
def ImpartialAux : Pgame → Prop
  | G => G ≈ -G ∧ (∀ i, impartial_aux (G.moveLeft i)) ∧ ∀ j, impartial_aux (G.moveRight j)

theorem impartial_aux_def {G : Pgame} :
    G.ImpartialAux ↔ G ≈ -G ∧ (∀ i, ImpartialAux (G.moveLeft i)) ∧ ∀ j, ImpartialAux (G.moveRight j) := by
  rw [impartial_aux]

/-- A typeclass on impartial games. -/
class Impartial (G : Pgame) : Prop where
  out : ImpartialAux G

theorem impartial_iff_aux {G : Pgame} : G.Impartial ↔ G.ImpartialAux :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩

theorem impartial_def {G : Pgame} :
    G.Impartial ↔ G ≈ -G ∧ (∀ i, Impartial (G.moveLeft i)) ∧ ∀ j, Impartial (G.moveRight j) := by
  simpa only [← impartial_iff_aux] using impartial_aux_def

namespace Impartial

instance impartial_zero : Impartial 0 := by
  rw [impartial_def]
  dsimp'
  simp

instance impartial_star : Impartial star := by
  rw [impartial_def]
  simpa using impartial.impartial_zero

theorem neg_equiv_self (G : Pgame) [h : G.Impartial] : G ≈ -G :=
  (impartial_def.1 h).1

@[simp]
theorem mk_neg_equiv_self (G : Pgame) [h : G.Impartial] : -⟦G⟧ = ⟦G⟧ :=
  Quot.sound (neg_equiv_self G).symm

instance move_left_impartial {G : Pgame} [h : G.Impartial] (i : G.LeftMoves) : (G.moveLeft i).Impartial :=
  (impartial_def.1 h).2.1 i

instance move_right_impartial {G : Pgame} [h : G.Impartial] (j : G.RightMoves) : (G.moveRight j).Impartial :=
  (impartial_def.1 h).2.2 j

theorem impartial_congr : ∀ {G H : Pgame} (e : G ≡r H) [G.Impartial], H.Impartial
  | G, H, e => by
    intro h
    rw [impartial_def]
    refine' ⟨e.symm.equiv.trans ((neg_equiv_self G).trans (neg_equiv_neg_iff.2 e.equiv)), fun i => _, fun j => _⟩ <;>
      cases' e with _ _ L R hL hR
    · convert impartial_congr (hL (L.symm i))
      rw [Equivₓ.apply_symm_apply]
      
    · exact impartial_congr (hR j)
      

instance impartial_add : ∀ (G H : Pgame) [G.Impartial] [H.Impartial], (G + H).Impartial
  | G, H => by
    intro hG hH
    rw [impartial_def]
    refine'
      ⟨(add_congr (neg_equiv_self _) (neg_equiv_self _)).trans (neg_add_relabelling _ _).Equiv.symm, fun k => _,
        fun k => _⟩
    · apply left_moves_add_cases k
      all_goals
        intro i
        simp only [← add_move_left_inl, ← add_move_left_inr]
        apply impartial_add
      
    · apply right_moves_add_cases k
      all_goals
        intro i
        simp only [← add_move_right_inl, ← add_move_right_inr]
        apply impartial_add
      

instance impartial_neg : ∀ (G : Pgame) [G.Impartial], (-G).Impartial
  | G => by
    intro hG
    rw [impartial_def]
    refine' ⟨_, fun i => _, fun i => _⟩
    · rw [neg_negₓ]
      exact (neg_equiv_self G).symm
      
    · rw [move_left_neg']
      apply impartial_neg
      
    · rw [move_right_neg']
      apply impartial_neg
      

variable (G : Pgame) [Impartial G]

theorem nonpos : ¬0 < G := fun h => by
  have h' := neg_lt_neg_iff.2 h
  rw [Pgame.neg_zero, lt_congr_left (neg_equiv_self G).symm] at h'
  exact (h.trans h').False

theorem nonneg : ¬G < 0 := fun h => by
  have h' := neg_lt_neg_iff.2 h
  rw [Pgame.neg_zero, lt_congr_right (neg_equiv_self G).symm] at h'
  exact (h.trans h').False

/-- In an impartial game, either the first player always wins, or the second player always wins. -/
theorem equiv_or_fuzzy_zero : G ≈ 0 ∨ G ∥ 0 := by
  rcases lt_or_equiv_or_gt_or_fuzzy G 0 with (h | h | h | h)
  · exact ((nonneg G) h).elim
    
  · exact Or.inl h
    
  · exact ((nonpos G) h).elim
    
  · exact Or.inr h
    

@[simp]
theorem not_equiv_zero_iff : ¬G ≈ 0 ↔ G ∥ 0 :=
  ⟨(equiv_or_fuzzy_zero G).resolve_left, Fuzzy.not_equiv⟩

@[simp]
theorem not_fuzzy_zero_iff : ¬G ∥ 0 ↔ G ≈ 0 :=
  ⟨(equiv_or_fuzzy_zero G).resolve_right, Equiv.not_fuzzy⟩

theorem add_self : G + G ≈ 0 :=
  (add_congr_left (neg_equiv_self G)).trans (add_left_neg_equiv G)

@[simp]
theorem mk_add_self : ⟦G⟧ + ⟦G⟧ = 0 :=
  Quot.sound (add_self G)

/-- This lemma doesn't require `H` to be impartial. -/
theorem equiv_iff_add_equiv_zero (H : Pgame) : H ≈ G ↔ H + G ≈ 0 := by
  rw [equiv_iff_game_eq, equiv_iff_game_eq, ← @add_right_cancel_iffₓ _ _ (-⟦G⟧)]
  simpa

/-- This lemma doesn't require `H` to be impartial. -/
theorem equiv_iff_add_equiv_zero' (H : Pgame) : G ≈ H ↔ G + H ≈ 0 := by
  rw [equiv_iff_game_eq, equiv_iff_game_eq, ← @add_left_cancel_iffₓ _ _ (-⟦G⟧), eq_comm]
  simpa

theorem le_zero_iff {G : Pgame} [G.Impartial] : G ≤ 0 ↔ 0 ≤ G := by
  rw [← zero_le_neg_iff, le_congr_right (neg_equiv_self G)]

theorem lf_zero_iff {G : Pgame} [G.Impartial] : G ⧏ 0 ↔ 0 ⧏ G := by
  rw [← zero_lf_neg_iff, lf_congr_right (neg_equiv_self G)]

theorem equiv_zero_iff_le : G ≈ 0 ↔ G ≤ 0 :=
  ⟨And.left, fun h => ⟨h, le_zero_iff.1 h⟩⟩

theorem fuzzy_zero_iff_lf : G ∥ 0 ↔ G ⧏ 0 :=
  ⟨And.left, fun h => ⟨h, lf_zero_iff.1 h⟩⟩

theorem equiv_zero_iff_ge : G ≈ 0 ↔ 0 ≤ G :=
  ⟨And.right, fun h => ⟨le_zero_iff.2 h, h⟩⟩

theorem fuzzy_zero_iff_gf : G ∥ 0 ↔ 0 ⧏ G :=
  ⟨And.right, fun h => ⟨lf_zero_iff.2 h, h⟩⟩

theorem forall_left_moves_fuzzy_iff_equiv_zero : (∀ i, G.moveLeft i ∥ 0) ↔ G ≈ 0 := by
  refine' ⟨fun hb => _, fun hp i => _⟩
  · rw [equiv_zero_iff_le G, le_zero_lf]
    exact fun i => (hb i).1
    
  · rw [fuzzy_zero_iff_lf]
    exact hp.1.move_left_lf i
    

theorem forall_right_moves_fuzzy_iff_equiv_zero : (∀ j, G.moveRight j ∥ 0) ↔ G ≈ 0 := by
  refine' ⟨fun hb => _, fun hp i => _⟩
  · rw [equiv_zero_iff_ge G, zero_le_lf]
    exact fun i => (hb i).2
    
  · rw [fuzzy_zero_iff_gf]
    exact hp.2.lf_move_right i
    

theorem exists_left_move_equiv_iff_fuzzy_zero : (∃ i, G.moveLeft i ≈ 0) ↔ G ∥ 0 := by
  refine' ⟨fun ⟨i, hi⟩ => (fuzzy_zero_iff_gf G).2 (lf_of_le_move_left hi.2), fun hn => _⟩
  rw [fuzzy_zero_iff_gf G, zero_lf_le] at hn
  cases' hn with i hi
  exact ⟨i, (equiv_zero_iff_ge _).2 hi⟩

theorem exists_right_move_equiv_iff_fuzzy_zero : (∃ j, G.moveRight j ≈ 0) ↔ G ∥ 0 := by
  refine' ⟨fun ⟨i, hi⟩ => (fuzzy_zero_iff_lf G).2 (lf_of_move_right_le hi.1), fun hn => _⟩
  rw [fuzzy_zero_iff_lf G, lf_zero_le] at hn
  cases' hn with i hi
  exact ⟨i, (equiv_zero_iff_le _).2 hi⟩

end Impartial

end Pgame

