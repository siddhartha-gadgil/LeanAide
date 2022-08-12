/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import Mathbin.SetTheory.Game.Basic
import Mathbin.SetTheory.Ordinal.NaturalOps

/-!
# Ordinals as games

We define the canonical map `ordinal → pgame`, where every ordinal is mapped to the game whose left
set consists of all previous ordinals.

The map to surreals is defined in `ordinal.to_surreal`.

# Main declarations

- `ordinal.to_pgame`: The canonical map between ordinals and pre-games.
- `ordinal.to_pgame_embedding`: The order embedding version of the previous map.
-/


universe u

open Pgame

open NaturalOps Pgame

namespace Ordinal

/-- Converts an ordinal into the corresponding pre-game. -/
noncomputable def toPgame : Ordinal.{u} → Pgame.{u}
  | o =>
    ⟨o.out.α, Pempty, fun x =>
      let hwf := Ordinal.typein_lt_self x
      (typein (· < ·) x).toPgame,
      Pempty.elimₓ⟩

theorem to_pgame_def (o : Ordinal) : o.toPgame = ⟨o.out.α, Pempty, fun x => (typein (· < ·) x).toPgame, Pempty.elimₓ⟩ :=
  by
  rw [to_pgame]

@[simp]
theorem to_pgame_left_moves (o : Ordinal) : o.toPgame.LeftMoves = o.out.α := by
  rw [to_pgame, left_moves]

@[simp]
theorem to_pgame_right_moves (o : Ordinal) : o.toPgame.RightMoves = Pempty := by
  rw [to_pgame, right_moves]

instance : IsEmpty (toPgame 0).LeftMoves := by
  rw [to_pgame_left_moves]
  infer_instance

instance (o : Ordinal) : IsEmpty o.toPgame.RightMoves := by
  rw [to_pgame_right_moves]
  infer_instance

/-- Converts an ordinal less than `o` into a move for the `pgame` corresponding to `o`, and vice
versa. -/
noncomputable def toLeftMovesToPgame {o : Ordinal} : Set.Iio o ≃ o.toPgame.LeftMoves :=
  (enumIsoOut o).toEquiv.trans (Equivₓ.cast (to_pgame_left_moves o).symm)

@[simp]
theorem to_left_moves_to_pgame_symm_lt {o : Ordinal} (i : o.toPgame.LeftMoves) : ↑(toLeftMovesToPgame.symm i) < o :=
  (toLeftMovesToPgame.symm i).Prop

theorem to_pgame_move_left_heq {o : Ordinal} : HEq o.toPgame.moveLeft fun x : o.out.α => (typein (· < ·) x).toPgame :=
  by
  rw [to_pgame]
  rfl

@[simp]
theorem to_pgame_move_left' {o : Ordinal} (i) : o.toPgame.moveLeft i = (toLeftMovesToPgame.symm i).val.toPgame :=
  (congr_heq to_pgame_move_left_heq.symm (cast_heq _ i)).symm

theorem to_pgame_move_left {o : Ordinal} (i) : o.toPgame.moveLeft (toLeftMovesToPgame i) = i.val.toPgame := by
  simp

theorem to_pgame_lf {a b : Ordinal} (h : a < b) : a.toPgame ⧏ b.toPgame := by
  convert move_left_lf (to_left_moves_to_pgame ⟨a, h⟩)
  rw [to_pgame_move_left]

theorem to_pgame_le {a b : Ordinal} (h : a ≤ b) : a.toPgame ≤ b.toPgame := by
  refine' le_iff_forall_lf.2 ⟨fun i => _, isEmptyElim⟩
  rw [to_pgame_move_left']
  exact to_pgame_lf ((to_left_moves_to_pgame_symm_lt i).trans_le h)

theorem to_pgame_lt {a b : Ordinal} (h : a < b) : a.toPgame < b.toPgame :=
  ⟨to_pgame_le h.le, to_pgame_lf h⟩

@[simp]
theorem to_pgame_lf_iff {a b : Ordinal} : a.toPgame ⧏ b.toPgame ↔ a < b :=
  ⟨by
    contrapose
    rw [not_ltₓ, not_lf]
    exact to_pgame_le, to_pgame_lf⟩

@[simp]
theorem to_pgame_le_iff {a b : Ordinal} : a.toPgame ≤ b.toPgame ↔ a ≤ b :=
  ⟨by
    contrapose
    rw [not_leₓ, Pgame.not_le]
    exact to_pgame_lf, to_pgame_le⟩

@[simp]
theorem to_pgame_lt_iff {a b : Ordinal} : a.toPgame < b.toPgame ↔ a < b :=
  ⟨by
    contrapose
    rw [not_ltₓ]
    exact fun h => not_lt_of_le (to_pgame_le h), to_pgame_lt⟩

@[simp]
theorem to_pgame_equiv_iff {a b : Ordinal} : a.toPgame ≈ b.toPgame ↔ a = b := by
  rw [Pgame.Equiv, le_antisymm_iffₓ, to_pgame_le_iff, to_pgame_le_iff]

theorem to_pgame_injective : Function.Injective Ordinal.toPgame := fun a b h => to_pgame_equiv_iff.1 <| equiv_of_eq h

@[simp]
theorem to_pgame_eq_iff {a b : Ordinal} : a.toPgame = b.toPgame ↔ a = b :=
  to_pgame_injective.eq_iff

/-- The order embedding version of `to_pgame`. -/
@[simps]
noncomputable def toPgameEmbedding : Ordinal.{u} ↪o Pgame.{u} where
  toFun := Ordinal.toPgame
  inj' := to_pgame_injective
  map_rel_iff' := @to_pgame_le_iff

/-- The sum of ordinals as games corresponds to natural addition of ordinals. -/
theorem to_pgame_add : ∀ a b : Ordinal.{u}, a.toPgame + b.toPgame ≈ (a ♯ b).toPgame
  | a, b => by
    refine' ⟨le_of_forall_lf (fun i => _) isEmptyElim, le_of_forall_lf (fun i => _) isEmptyElim⟩
    · apply left_moves_add_cases i <;>
        intro i <;>
          let wf := to_left_moves_to_pgame_symm_lt i <;>
            try
                rw [add_move_left_inl] <;>
              try
                  rw [add_move_left_inr] <;>
                rw [to_pgame_move_left', lf_congr_left (to_pgame_add _ _), to_pgame_lf_iff]
      · exact nadd_lt_nadd_right wf _
        
      · exact nadd_lt_nadd_left wf _
        
      
    · rw [to_pgame_move_left']
      rcases lt_nadd_iff.1 (to_left_moves_to_pgame_symm_lt i) with (⟨c, hc, hc'⟩ | ⟨c, hc, hc'⟩) <;>
        rw [← to_pgame_le_iff, ← le_congr_right (to_pgame_add _ _)] at hc' <;> apply lf_of_le_of_lf hc'
      · apply add_lf_add_right
        rwa [to_pgame_lf_iff]
        
      · apply add_lf_add_left
        rwa [to_pgame_lf_iff]
        
      

@[simp]
theorem to_pgame_add_mk (a b : Ordinal) : ⟦a.toPgame⟧ + ⟦b.toPgame⟧ = ⟦(a ♯ b).toPgame⟧ :=
  Quot.sound (to_pgame_add a b)

end Ordinal

