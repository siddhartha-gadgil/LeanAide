/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.Data.Fintype.Basic
import Mathbin.SetTheory.Cardinal.Cofinality
import Mathbin.SetTheory.Game.Basic
import Mathbin.SetTheory.Game.Birthday

/-!
# Short games

A combinatorial game is `short` [Conway, ch.9][conway2001] if it has only finitely many positions.
In particular, this means there is a finite set of moves at every point.

We prove that the order relations `≤` and `<`, and the equivalence relation `≈`, are decidable on
short games, although unfortunately in practice `dec_trivial` doesn't seem to be able to
prove anything using these instances.
-/


universe u

open Pgame

namespace Pgame

/-- A short game is a game with a finite set of moves at every turn. -/
inductive Short : Pgame.{u} → Type (u + 1)
  | mk :
    ∀ {α β : Type u} {L : α → Pgame.{u}} {R : β → Pgame.{u}} (sL : ∀ i : α, short (L i)) (sR : ∀ j : β, short (R j))
      [Fintype α] [Fintype β], short ⟨α, β, L, R⟩

instance subsingleton_short : ∀ x : Pgame, Subsingleton (Short x)
  | mk xl xr xL xR =>
    ⟨fun a b => by
      cases a
      cases b
      congr
      · funext
        apply @Subsingleton.elimₓ _ (subsingleton_short (xL x))
        
      · funext
        apply @Subsingleton.elimₓ _ (subsingleton_short (xR x))
        ⟩

/-- A synonym for `short.mk` that specifies the pgame in an implicit argument. -/
def Short.mk' {x : Pgame} [Fintype x.LeftMoves] [Fintype x.RightMoves] (sL : ∀ i : x.LeftMoves, Short (x.moveLeft i))
    (sR : ∀ j : x.RightMoves, Short (x.moveRight j)) : Short x := by
  (
      cases x
      dsimp'  at *) <;>
    exact short.mk sL sR

attribute [class] short

/-- Extracting the `fintype` instance for the indexing type for Left's moves in a short game.
This is an unindexed typeclass, so it can't be made a global instance.
-/
def fintypeLeft {α β : Type u} {L : α → Pgame.{u}} {R : β → Pgame.{u}} [S : Short ⟨α, β, L, R⟩] : Fintype α := by
  cases' S with _ _ _ _ _ _ F _
  exact F

attribute [local instance] fintype_left

instance fintypeLeftMoves (x : Pgame) [S : Short x] : Fintype x.LeftMoves := by
  cases x
  dsimp'
  infer_instance

/-- Extracting the `fintype` instance for the indexing type for Right's moves in a short game.
This is an unindexed typeclass, so it can't be made a global instance.
-/
def fintypeRight {α β : Type u} {L : α → Pgame.{u}} {R : β → Pgame.{u}} [S : Short ⟨α, β, L, R⟩] : Fintype β := by
  cases' S with _ _ _ _ _ _ _ F
  exact F

attribute [local instance] fintype_right

instance fintypeRightMoves (x : Pgame) [S : Short x] : Fintype x.RightMoves := by
  cases x
  dsimp'
  infer_instance

instance moveLeftShort (x : Pgame) [S : Short x] (i : x.LeftMoves) : Short (x.moveLeft i) := by
  cases' S with _ _ _ _ L _ _ _
  apply L

/-- Extracting the `short` instance for a move by Left.
This would be a dangerous instance potentially introducing new metavariables
in typeclass search, so we only make it an instance locally.
-/
def moveLeftShort' {xl xr} (xL xR) [S : Short (mk xl xr xL xR)] (i : xl) : Short (xL i) := by
  cases' S with _ _ _ _ L _ _ _
  apply L

attribute [local instance] move_left_short'

instance moveRightShort (x : Pgame) [S : Short x] (j : x.RightMoves) : Short (x.moveRight j) := by
  cases' S with _ _ _ _ _ R _ _
  apply R

/-- Extracting the `short` instance for a move by Right.
This would be a dangerous instance potentially introducing new metavariables
in typeclass search, so we only make it an instance locally.
-/
def moveRightShort' {xl xr} (xL xR) [S : Short (mk xl xr xL xR)] (j : xr) : Short (xR j) := by
  cases' S with _ _ _ _ _ R _ _
  apply R

attribute [local instance] move_right_short'

theorem short_birthday : ∀ (x : Pgame.{u}) [Short x], x.birthday < Ordinal.omega
  | ⟨xl, xr, xL, xR⟩, hs => by
    have := hs
    rcases hs with ⟨_, _, _, _, sL, sR, hl, hr⟩
    rw [birthday, max_lt_iff]
    constructor
    all_goals
      rw [← Cardinal.ord_aleph_0]
      refine'
        Cardinal.lsub_lt_ord_of_is_regular.{u, u} Cardinal.is_regular_aleph_0 (Cardinal.lt_aleph_0_of_finite _) fun i =>
          _
      rw [Cardinal.ord_aleph_0]
      apply short_birthday _
    · exact move_left_short' xL xR i
      
    · exact move_right_short' xL xR i
      

/-- This leads to infinite loops if made into an instance. -/
def Short.ofIsEmpty {l r xL xR} [IsEmpty l] [IsEmpty r] : Short (mk l r xL xR) :=
  Short.mk isEmptyElim isEmptyElim

instance short0 : Short 0 :=
  short.of_is_empty

instance short1 : Short 1 :=
  Short.mk
    (fun i => by
      cases i
      infer_instance)
    fun j => by
    cases j

/-- Evidence that every `pgame` in a list is `short`. -/
inductive ListShort : List Pgame.{u} → Type (u + 1)
  | nil : list_short []
  | cons : ∀ (hd : Pgame.{u}) [Short hd] (tl : List Pgame.{u}) [list_short tl], list_short (hd :: tl)

attribute [class] list_short

attribute [instance] list_short.nil list_short.cons

instance listShortNthLe :
    ∀ (L : List Pgame.{u}) [ListShort L] (i : Finₓ (List.length L)), Short (List.nthLe L i i.is_lt)
  | [], _, n => by
    exfalso
    rcases n with ⟨_, ⟨⟩⟩
  | hd :: tl, @list_short.cons _ S _ _, ⟨0, _⟩ => S
  | hd :: tl, @list_short.cons _ _ _ S, ⟨n + 1, h⟩ => @list_short_nth_le tl S ⟨n, (add_lt_add_iff_right 1).mp h⟩

instance shortOfLists : ∀ (L R : List Pgame) [ListShort L] [ListShort R], Short (Pgame.ofLists L R)
  | L, R, _, _ => by
    skip
    apply short.mk
    · intros
      infer_instance
      
    · intros
      apply Pgame.listShortNthLe
      

/-- If `x` is a short game, and `y` is a relabelling of `x`, then `y` is also short. -/
-- where does the subtype.val come from?
def shortOfRelabelling : ∀ {x y : Pgame.{u}} (R : Relabelling x y) (S : Short x), Short y
  | x, y, ⟨L, R, rL, rR⟩, S => by
    skip
    have := Fintype.ofEquiv _ L
    have := Fintype.ofEquiv _ R
    exact
      short.mk'
        (fun i => by
          rw [← L.right_inv i]
          apply short_of_relabelling (rL (L.symm i)) inferInstance)
        fun j => short_of_relabelling (rR j) inferInstance

instance shortNeg : ∀ (x : Pgame.{u}) [Short x], Short (-x)
  | mk xl xr xL xR, _ => by
    skip
    exact short.mk (fun i => short_neg _) fun i => short_neg _

instance shortAdd : ∀ (x y : Pgame.{u}) [Short x] [Short y], Short (x + y)
  | mk xl xr xL xR, mk yl yr yL yR, _, _ => by
    skip
    apply short.mk
    all_goals
      rintro ⟨i⟩
      · apply short_add
        
      · change short (mk xl xr xL xR + _)
        apply short_add
        

instance shortNat : ∀ n : ℕ, Short n
  | 0 => Pgame.short0
  | n + 1 => @Pgame.shortAdd _ _ (short_nat n) Pgame.short1

instance shortBit0 (x : Pgame.{u}) [Short x] : Short (bit0 x) := by
  dsimp' [← bit0]
  infer_instance

instance shortBit1 (x : Pgame.{u}) [Short x] : Short (bit1 x) := by
  dsimp' [← bit1]
  infer_instance

/-- Auxiliary construction of decidability instances.
We build `decidable (x ≤ y)` and `decidable (x ⧏ y)` in a simultaneous induction.
Instances for the two projections separately are provided below.
-/
def leLfDecidable : ∀ (x y : Pgame.{u}) [Short x] [Short y], Decidable (x ≤ y) × Decidable (x ⧏ y)
  | mk xl xr xL xR, mk yl yr yL yR, shortx, shorty => by
    skip
    constructor
    · refine' @decidableOfIff' _ _ mk_le_mk (id _)
      apply @And.decidable _ _ _ _
      · apply
          @Fintype.decidableForallFintype xl _ _
            (by
              infer_instance)
        intro i
        apply (@le_lf_decidable _ _ _ _).2 <;> infer_instance
        
      · apply
          @Fintype.decidableForallFintype yr _ _
            (by
              infer_instance)
        intro i
        apply (@le_lf_decidable _ _ _ _).2 <;> infer_instance
        
      
    · refine' @decidableOfIff' _ _ mk_lf_mk (id _)
      apply @Or.decidable _ _ _ _
      · apply
          @Fintype.decidableExistsFintype yl _ _
            (by
              infer_instance)
        intro i
        apply (@le_lf_decidable _ _ _ _).1 <;> infer_instance
        
      · apply
          @Fintype.decidableExistsFintype xr _ _
            (by
              infer_instance)
        intro i
        apply (@le_lf_decidable _ _ _ _).1 <;> infer_instance
        
      

instance leDecidable (x y : Pgame.{u}) [Short x] [Short y] : Decidable (x ≤ y) :=
  (leLfDecidable x y).1

instance lfDecidable (x y : Pgame.{u}) [Short x] [Short y] : Decidable (x ⧏ y) :=
  (leLfDecidable x y).2

instance ltDecidable (x y : Pgame.{u}) [Short x] [Short y] : Decidable (x < y) :=
  And.decidable

instance equivDecidable (x y : Pgame.{u}) [Short x] [Short y] : Decidable (x ≈ y) :=
  And.decidable

example : Short 0 := by
  infer_instance

example : Short 1 := by
  infer_instance

example : Short 2 := by
  infer_instance

example : Short (-2) := by
  infer_instance

example : Short (ofLists [0] [1]) := by
  infer_instance

example : Short (ofLists [-2, -1] [1]) := by
  infer_instance

example : Short (0 + 0) := by
  infer_instance

example : Decidable ((1 : Pgame) ≤ 1) := by
  infer_instance

-- No longer works since definitional reduction of well-founded definitions has been restricted.
-- example : (0 : pgame) ≤ 0 := dec_trivial
-- example : (1 : pgame) ≤ 1 := dec_trivial
end Pgame

