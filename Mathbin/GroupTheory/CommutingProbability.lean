/-
Copyright (c) 2022 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
import Mathbin.GroupTheory.Abelianization
import Mathbin.GroupTheory.GroupAction.ConjAct
import Mathbin.GroupTheory.GroupAction.Quotient
import Mathbin.GroupTheory.Index

/-!
# Commuting Probability
This file introduces the commuting probability of finite groups.

## Main definitions
* `comm_prob`: The commuting probability of a finite type with a multiplication operation.

## Todo
* Neumann's theorem.
-/


noncomputable section

open Classical

open BigOperators

open Fintype

variable (M : Type _) [Fintype M] [Mul M]

/-- The commuting probability of a finite type with a multiplication operation -/
def commProb : ℚ :=
  card { p : M × M // p.1 * p.2 = p.2 * p.1 } / card M ^ 2

theorem comm_prob_def : commProb M = card { p : M × M // p.1 * p.2 = p.2 * p.1 } / card M ^ 2 :=
  rfl

theorem comm_prob_pos [h : Nonempty M] : 0 < commProb M :=
  h.elim fun x => div_pos (Nat.cast_pos.mpr (card_pos_iff.mpr ⟨⟨(x, x), rfl⟩⟩)) (pow_pos (Nat.cast_pos.mpr card_pos) 2)

theorem comm_prob_le_one : commProb M ≤ 1 := by
  refine' div_le_one_of_le _ (sq_nonneg (card M))
  rw [← Nat.cast_powₓ, Nat.cast_le, sq, ← card_prod]
  apply set_fintype_card_le_univ

variable {M}

theorem comm_prob_eq_one_iff [h : Nonempty M] : commProb M = 1 ↔ Commutative ((· * ·) : M → M → M) := by
  change (card { p : M × M | p.1 * p.2 = p.2 * p.1 } : ℚ) / _ = 1 ↔ _
  rw [div_eq_one_iff_eq, ← Nat.cast_powₓ, Nat.cast_inj, sq, ← card_prod, set_fintype_card_eq_univ_iff,
    Set.eq_univ_iff_forall]
  · exact ⟨fun h x y => h (x, y), fun h x => h x.1 x.2⟩
    
  · exact pow_ne_zero 2 (nat.cast_ne_zero.mpr card_ne_zero)
    

variable (G : Type _) [Groupₓ G] [Fintype G]

theorem card_comm_eq_card_conj_classes_mul_card [h : Fintype (ConjClasses G)] :
    card { p : G × G // p.1 * p.2 = p.2 * p.1 } = @card (ConjClasses G) h * card G := by
  convert
    calc
      card { p : G × G // p.1 * p.2 = p.2 * p.1 } = card (Σg, { h // g * h = h * g }) :=
        card_congr (Equivₓ.subtypeProdEquivSigmaSubtype fun g h : G => g * h = h * g)
      _ = ∑ g, card { h // g * h = h * g } := card_sigma _
      _ = ∑ g, card (MulAction.FixedBy (ConjAct G) G g) :=
        sum_equiv conj_act.to_conj_act.to_equiv _ _ fun g =>
          card_congr' <| congr_arg _ <| funext fun h => mul_inv_eq_iff_eq_mul.symm.to_eq
      _ = card (Quotientₓ (MulAction.orbitRel (ConjAct G) G)) * card G :=
        MulAction.sum_card_fixed_by_eq_card_orbits_mul_card_group (ConjAct G) G
      _ = card (Quotientₓ (IsConj.setoid G)) * card G := by
        have this : MulAction.orbitRel (ConjAct G) G = IsConj.setoid G :=
          Setoidₓ.ext fun g h => (Setoidₓ.comm' _).trans is_conj_iff.symm
        cc
      

theorem comm_prob_def' : commProb G = card (ConjClasses G) / card G := by
  rw [commProb, card_comm_eq_card_conj_classes_mul_card, Nat.cast_mulₓ, sq]
  exact mul_div_mul_right (card (ConjClasses G)) (card G) (nat.cast_ne_zero.mpr card_ne_zero)

variable {G} (H : Subgroup G)

theorem Subgroup.comm_prob_subgroup_le : commProb H ≤ commProb G * H.index ^ 2 := by
  /- After rewriting with `comm_prob_def`, we reduce to showing that `G` has at least as many
      commuting pairs as `H`. -/
  rw [comm_prob_def, comm_prob_def, div_le_iff, mul_assoc, ← mul_powₓ, ← Nat.cast_mulₓ, H.index_mul_card,
    div_mul_cancel, Nat.cast_le]
  · apply card_le_of_injective _ _
    exact fun p => ⟨⟨p.1.1, p.1.2⟩, subtype.ext_iff.mp p.2⟩
    exact fun p q h => by
      simpa only [← Subtype.ext_iff, ← Prod.ext_iff] using h
    
  · exact pow_ne_zero 2 (nat.cast_ne_zero.mpr card_ne_zero)
    
  · exact pow_pos (nat.cast_pos.mpr card_pos) 2
    

theorem Subgroup.comm_prob_quotient_le [H.Normal] : commProb (G ⧸ H) ≤ commProb G * card H := by
  /- After rewriting with `comm_prob_def'`, we reduce to showing that `G` has at least as many
      conjugacy classes as `G ⧸ H`. -/
  rw [comm_prob_def', comm_prob_def', div_le_iff, mul_assoc, ← Nat.cast_mulₓ, mul_comm (card H), ←
    Subgroup.card_eq_card_quotient_mul_card_subgroup, div_mul_cancel, Nat.cast_le]
  · apply card_le_of_surjective
    show Function.Surjective (ConjClasses.map (QuotientGroup.mk' H))
    exact ConjClasses.map_surjective Quotientₓ.surjective_quotient_mk'
    
  · exact nat.cast_ne_zero.mpr card_ne_zero
    
  · exact nat.cast_pos.mpr card_pos
    

variable (G)

theorem inv_card_commutator_le_comm_prob : (↑(card (commutator G)))⁻¹ ≤ commProb G :=
  (inv_pos_le_iff_one_le_mul (nat.cast_pos.mpr card_pos)).mpr
    (le_transₓ (ge_of_eq (comm_prob_eq_one_iff.mpr (Abelianization.commGroup G).mul_comm))
      (commutator G).comm_prob_quotient_le)

