/-
Copyright (c) 2021 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
import Mathbin.GroupTheory.Sylow
import Mathbin.GroupTheory.Transfer

/-!
# The Schur-Zassenhaus Theorem

In this file we prove the Schur-Zassenhaus theorem.

## Main results

- `exists_right_complement'_of_coprime` : The **Schur-Zassenhaus** theorem:
  If `H : subgroup G` is normal and has order coprime to its index,
  then there exists a subgroup `K` which is a (right) complement of `H`.
- `exists_left_complement'_of_coprime`  The **Schur-Zassenhaus** theorem:
  If `H : subgroup G` is normal and has order coprime to its index,
  then there exists a subgroup `K` which is a (left) complement of `H`.
-/


open BigOperators

namespace Subgroup

section SchurZassenhausAbelian

open MulOpposite MulAction Subgroup.LeftTransversals MemLeftTransversals

variable {G : Type _} [Groupₓ G] (H : Subgroup G) [IsCommutative H] [Fintype (G ⧸ H)]
  (α β : LeftTransversals (H : Set G))

/-- The quotient of the transversals of an abelian normal `N` by the `diff` relation. -/
def QuotientDiff :=
  Quotientₓ
    (Setoidₓ.mk (fun α β => diff (MonoidHom.id H) α β = 1)
      ⟨fun α => diff_self (MonoidHom.id H) α, fun α β h => by
        rw [← diff_inv, h, inv_one], fun α β γ h h' => by
        rw [← diff_mul_diff, h, h', one_mulₓ]⟩)

instance : Inhabited H.QuotientDiff :=
  Quotientₓ.inhabited _

theorem smul_diff_smul' [hH : Normal H] (g : Gᵐᵒᵖ) :
    diff (MonoidHom.id H) (g • α) (g • β) =
      ⟨g.unop⁻¹ * (diff (MonoidHom.id H) α β : H) * g.unop,
        hH.mem_comm ((congr_arg (· ∈ H) (mul_inv_cancel_left _ _)).mpr (SetLike.coe_mem _))⟩ :=
  by
  let ϕ : H →* H :=
    { toFun := fun h =>
        ⟨g.unop⁻¹ * h * g.unop, hH.mem_comm ((congr_arg (· ∈ H) (mul_inv_cancel_left _ _)).mpr (SetLike.coe_mem _))⟩,
      map_one' := by
        rw [Subtype.ext_iff, coe_mk, coe_one, mul_oneₓ, inv_mul_selfₓ],
      map_mul' := fun h₁ h₂ => by
        rw [Subtype.ext_iff, coe_mk, coe_mul, coe_mul, coe_mk, coe_mk, mul_assoc, mul_assoc, mul_assoc, mul_assoc,
          mul_assoc, mul_inv_cancel_left] }
  refine'
    Eq.trans
      (Finset.prod_bij' (fun q _ => g⁻¹ • q) (fun q _ => Finset.mem_univ _) (fun q _ => Subtype.ext _)
        (fun q _ => g • q) (fun q _ => Finset.mem_univ _) (fun q _ => smul_inv_smul g q) fun q _ => inv_smul_smul g q)
      (map_prod ϕ _ _).symm
  simp_rw [MonoidHom.id_apply, MonoidHom.coe_mk, coe_mk, smul_apply_eq_smul_apply_inv_smul, smul_eq_mul_unop,
    mul_inv_rev, mul_assoc]

variable {H} [Normal H]

instance : MulAction G H.QuotientDiff where
  smul := fun g =>
    Quotientₓ.map' (fun α => op g⁻¹ • α) fun α β h =>
      Subtype.ext
        (by
          rwa [smul_diff_smul', coe_mk, coe_one, mul_eq_one_iff_eq_inv, mul_right_eq_self, ← coe_one, ←
            Subtype.ext_iff])
  mul_smul := fun g₁ g₂ q =>
    Quotientₓ.induction_on' q fun T =>
      congr_arg Quotientₓ.mk'
        (by
          rw [mul_inv_rev] <;> exact mul_smul (op g₁⁻¹) (op g₂⁻¹) T)
  one_smul := fun q =>
    Quotientₓ.induction_on' q fun T =>
      congr_arg Quotientₓ.mk'
        (by
          rw [inv_one] <;> apply one_smul Gᵐᵒᵖ T)

theorem smul_diff' (h : H) : diff (MonoidHom.id H) α (op (h : G) • β) = diff (MonoidHom.id H) α β * h ^ H.index := by
  rw [diff, diff, index_eq_card, ← Finset.card_univ, ← Finset.prod_const, ← Finset.prod_mul_distrib]
  refine' Finset.prod_congr rfl fun q _ => _
  simp_rw [Subtype.ext_iff, MonoidHom.id_apply, coe_mul, coe_mk, mul_assoc, mul_right_injₓ]
  rw [smul_apply_eq_smul_apply_inv_smul, smul_eq_mul_unop, unop_op, mul_left_injₓ, ← Subtype.ext_iff,
    Equivₓ.apply_eq_iff_eq, inv_smul_eq_iff]
  exact self_eq_mul_right.mpr ((QuotientGroup.eq_one_iff _).mpr h.2)

variable [Fintype H]

theorem eq_one_of_smul_eq_one (hH : Nat.Coprime (Fintype.card H) H.index) (α : H.QuotientDiff) (h : H) :
    h • α = α → h = 1 :=
  (Quotientₓ.induction_on' α) fun α hα =>
    (powCoprime hH).Injective <|
      calc
        h ^ H.index = diff (MonoidHom.id H) (op ((h⁻¹ : H) : G) • α) α := by
          rw [← diff_inv, smul_diff', diff_self, one_mulₓ, inv_pow, inv_invₓ]
        _ = 1 ^ H.index := (Quotientₓ.exact' hα).trans (one_pow H.index).symm
        

theorem exists_smul_eq (hH : Nat.Coprime (Fintype.card H) H.index) (α β : H.QuotientDiff) : ∃ h : H, h • α = β :=
  Quotientₓ.induction_on' α
    (Quotientₓ.induction_on' β fun β α =>
      exists_imp_exists (fun n => Quotientₓ.sound')
        ⟨(powCoprime hH).symm (diff (MonoidHom.id H) β α),
          (diff_inv _ _ _).symm.trans
            (inv_eq_one.mpr
              ((smul_diff' β α ((powCoprime hH).symm (diff (MonoidHom.id H) β α))⁻¹).trans
                (by
                  rw [inv_pow, ← pow_coprime_apply hH, Equivₓ.apply_symm_apply, mul_inv_selfₓ])))⟩)

theorem is_complement'_stabilizer_of_coprime {α : H.QuotientDiff} (hH : Nat.Coprime (Fintype.card H) H.index) :
    IsComplement' H (stabilizer G α) :=
  is_complement'_stabilizer α (eq_one_of_smul_eq_one hH α) fun g => exists_smul_eq hH (g • α) α

/-- Do not use this lemma: It is made obsolete by `exists_right_complement'_of_coprime` -/
private theorem exists_right_complement'_of_coprime_aux (hH : Nat.Coprime (Fintype.card H) H.index) :
    ∃ K : Subgroup G, IsComplement' H K :=
  nonempty_of_inhabited.elim fun α => ⟨stabilizer G α, is_complement'_stabilizer_of_coprime hH⟩

end SchurZassenhausAbelian

open Classical

universe u

namespace SchurZassenhausInduction

/-! ## Proof of the Schur-Zassenhaus theorem

In this section, we prove the Schur-Zassenhaus theorem.
The proof is by contradiction. We assume that `G` is a minimal counterexample to the theorem.
-/


variable {G : Type u} [Groupₓ G] [Fintype G] {N : Subgroup G} [Normal N] (h1 : Nat.Coprime (Fintype.card N) N.index)
  (h2 :
    ∀ (G' : Type u) [Groupₓ G'] [Fintype G'],
      ∀ (hG'3 : Fintype.card G' < Fintype.card G) {N' : Subgroup G'} [N'.Normal]
        (hN : Nat.Coprime (Fintype.card N') N'.index), ∃ H' : Subgroup G', is_complement' N' H')
  (h3 : ∀ H : Subgroup G, ¬IsComplement' N H)

include h1 h2 h3

/-! We will arrive at a contradiction via the following steps:
 * step 0: `N` (the normal Hall subgroup) is nontrivial.
 * step 1: If `K` is a subgroup of `G` with `K ⊔ N = ⊤`, then `K = ⊤`.
 * step 2: `N` is a minimal normal subgroup, phrased in terms of subgroups of `G`.
 * step 3: `N` is a minimal normal subgroup, phrased in terms of subgroups of `N`.
 * step 4: `p` (`min_fact (fintype.card N)`) is prime (follows from step0).
 * step 5: `P` (a Sylow `p`-subgroup of `N`) is nontrivial.
 * step 6: `N` is a `p`-group (applies step 1 to the normalizer of `P` in `G`).
 * step 7: `N` is abelian (applies step 3 to the center of `N`).
-/


/-- Do not use this lemma: It is made obsolete by `exists_right_complement'_of_coprime` -/
@[nolint unused_arguments]
private theorem step0 : N ≠ ⊥ := by
  rintro rfl
  exact h3 ⊤ is_complement'_bot_top

/-- Do not use this lemma: It is made obsolete by `exists_right_complement'_of_coprime` -/
private theorem step1 (K : Subgroup G) (hK : K⊔N = ⊤) : K = ⊤ := by
  contrapose! h3
  have h4 : (N.comap K.subtype).index = N.index := by
    rw [← N.relindex_top_right, ← hK]
    exact relindex_eq_relindex_sup K N
  have h5 : Fintype.card K < Fintype.card G := by
    rw [← K.index_mul_card]
    exact lt_mul_of_one_lt_left Fintype.card_pos (one_lt_index_of_ne_top h3)
  have h6 : Nat.Coprime (Fintype.card (N.comap K.subtype)) (N.comap K.subtype).index := by
    rw [h4]
    exact h1.coprime_dvd_left (card_comap_dvd_of_injective N K.subtype Subtype.coe_injective)
  obtain ⟨H, hH⟩ := h2 K h5 h6
  replace hH : Fintype.card (H.map K.subtype) = N.index :=
    ((Set.card_image_of_injective _ Subtype.coe_injective).trans
          (Nat.mul_left_injective Fintype.card_pos
            (hH.symm.card_mul.trans (N.comap K.subtype).index_mul_card.symm))).trans
      h4
  have h7 : Fintype.card N * Fintype.card (H.map K.subtype) = Fintype.card G := by
    rw [hH, ← N.index_mul_card, mul_comm]
  have h8 : (Fintype.card N).Coprime (Fintype.card (H.map K.subtype)) := by
    rwa [hH]
  exact ⟨H.map K.subtype, is_complement'_of_coprime h7 h8⟩

/-- Do not use this lemma: It is made obsolete by `exists_right_complement'_of_coprime` -/
private theorem step2 (K : Subgroup G) [K.Normal] (hK : K ≤ N) : K = ⊥ ∨ K = N := by
  have : Function.Surjective (QuotientGroup.mk' K) := Quotientₓ.surjective_quotient_mk'
  have h4 := step1 h1 h2 h3
  contrapose! h4
  have h5 : Fintype.card (G ⧸ K) < Fintype.card G := by
    rw [← index_eq_card, ← K.index_mul_card]
    refine' lt_mul_of_one_lt_right (Nat.pos_of_ne_zeroₓ index_ne_zero_of_fintype) (K.one_lt_card_iff_ne_bot.mpr h4.1)
  have h6 : Nat.Coprime (Fintype.card (N.map (QuotientGroup.mk' K))) (N.map (QuotientGroup.mk' K)).index := by
    have index_map :=
      N.index_map_eq this
        (by
          rwa [QuotientGroup.ker_mk])
    have index_pos : 0 < N.index := Nat.pos_of_ne_zeroₓ index_ne_zero_of_fintype
    rw [index_map]
    refine' h1.coprime_dvd_left _
    rw [← Nat.mul_dvd_mul_iff_left index_pos, index_mul_card, ← index_map, index_mul_card]
    exact K.card_quotient_dvd_card
  obtain ⟨H, hH⟩ := h2 (G ⧸ K) h5 h6
  refine' ⟨H.comap (QuotientGroup.mk' K), _, _⟩
  · have key : (N.map (QuotientGroup.mk' K)).comap (QuotientGroup.mk' K) = N := by
      refine' comap_map_eq_self _
      rwa [QuotientGroup.ker_mk]
    rwa [← key, comap_sup_eq, hH.symm.sup_eq_top, comap_top]
    
  · rw [← comap_top (QuotientGroup.mk' K)]
    intro hH'
    rw [comap_injective this hH', is_complement'_top_right, map_eq_bot_iff, QuotientGroup.ker_mk] at hH
    · exact h4.2 (le_antisymmₓ hK hH)
      
    

/-- Do not use this lemma: It is made obsolete by `exists_right_complement'_of_coprime` -/
private theorem step3 (K : Subgroup N) [(K.map N.Subtype).Normal] : K = ⊥ ∨ K = ⊤ := by
  have key := step2 h1 h2 h3 (K.map N.subtype) K.map_subtype_le
  rw [← map_bot N.subtype] at key
  conv at key => congr skip rhs rw [← N.subtype_range, N.subtype.range_eq_map]
  have inj := map_injective (show Function.Injective N.subtype from Subtype.coe_injective)
  rwa [inj.eq_iff, inj.eq_iff] at key

/-- Do not use this lemma: It is made obsolete by `exists_right_complement'_of_coprime` -/
private theorem step4 : (Fintype.card N).minFac.Prime :=
  Nat.min_fac_prime (N.one_lt_card_iff_ne_bot.mpr (step0 h1 h2 h3)).ne'

/-- Do not use this lemma: It is made obsolete by `exists_right_complement'_of_coprime` -/
private theorem step5 {P : Sylow (Fintype.card N).minFac N} : P.1 ≠ ⊥ := by
  have : Fact (Fintype.card N).minFac.Prime := ⟨step4 h1 h2 h3⟩
  exact P.ne_bot_of_dvd_card (Fintype.card N).min_fac_dvd

/-- Do not use this lemma: It is made obsolete by `exists_right_complement'_of_coprime` -/
private theorem step6 : IsPGroup (Fintype.card N).minFac N := by
  have : Fact (Fintype.card N).minFac.Prime := ⟨step4 h1 h2 h3⟩
  refine' sylow.nonempty.elim fun P => P.2.ofSurjective P.1.Subtype _
  rw [← MonoidHom.range_top_iff_surjective, subtype_range]
  have : (P.1.map N.subtype).Normal :=
    normalizer_eq_top.mp (step1 h1 h2 h3 (P.1.map N.subtype).normalizer P.normalizer_sup_eq_top)
  exact (step3 h1 h2 h3 P.1).resolve_left (step5 h1 h2 h3)

/-- Do not use this lemma: It is made obsolete by `exists_right_complement'_of_coprime` -/
theorem step7 : IsCommutative N := by
  have := N.bot_or_nontrivial.resolve_left (step0 h1 h2 h3)
  have : Fact (Fintype.card N).minFac.Prime := ⟨step4 h1 h2 h3⟩
  exact
    ⟨⟨fun g h =>
        eq_top_iff.mp ((step3 h1 h2 h3 N.center).resolve_left (step6 h1 h2 h3).bot_lt_center.ne') (mem_top h) g⟩⟩

end SchurZassenhausInduction

variable {n : ℕ} {G : Type u} [Groupₓ G]

/-- Do not use this lemma: It is made obsolete by `exists_right_complement'_of_coprime` -/
private theorem exists_right_complement'_of_coprime_aux' [Fintype G] (hG : Fintype.card G = n) {N : Subgroup G}
    [N.Normal] (hN : Nat.Coprime (Fintype.card N) N.index) : ∃ H : Subgroup G, IsComplement' N H := by
  revert G
  apply Nat.strong_induction_onₓ n
  rintro n ih G _ _ rfl N _ hN
  refine' not_forall_not.mp fun h3 => _
  have :=
    schur_zassenhaus_induction.step7 hN
      (fun G' _ _ hG' => by
        apply ih _ hG'
        rfl)
      h3
  exact not_exists_of_forall_not h3 (exists_right_complement'_of_coprime_aux hN)

/-- **Schur-Zassenhaus** for normal subgroups:
  If `H : subgroup G` is normal, and has order coprime to its index, then there exists a
  subgroup `K` which is a (right) complement of `H`. -/
theorem exists_right_complement'_of_coprime_of_fintype [Fintype G] {N : Subgroup G} [N.Normal]
    (hN : Nat.Coprime (Fintype.card N) N.index) : ∃ H : Subgroup G, IsComplement' N H :=
  exists_right_complement'_of_coprime_aux' rfl hN

/-- **Schur-Zassenhaus** for normal subgroups:
  If `H : subgroup G` is normal, and has order coprime to its index, then there exists a
  subgroup `K` which is a (right) complement of `H`. -/
theorem exists_right_complement'_of_coprime {N : Subgroup G} [N.Normal] (hN : Nat.Coprime (Nat.card N) N.index) :
    ∃ H : Subgroup G, IsComplement' N H := by
  by_cases' hN1 : Nat.card N = 0
  · rw [hN1, Nat.coprime_zero_leftₓ, index_eq_one] at hN
    rw [hN]
    exact ⟨⊥, is_complement'_top_bot⟩
    
  by_cases' hN2 : N.index = 0
  · rw [hN2, Nat.coprime_zero_rightₓ] at hN
    have := (cardinal.to_nat_eq_one_iff_unique.mp hN).1
    rw [N.eq_bot_of_subsingleton]
    exact ⟨⊤, is_complement'_bot_top⟩
    
  have hN3 : Nat.card G ≠ 0 := by
    rw [← N.card_mul_index]
    exact mul_ne_zero hN1 hN2
  have := (cardinal.lt_aleph_0_iff_fintype.mp (lt_of_not_geₓ (mt Cardinal.to_nat_apply_of_aleph_0_le hN3))).some
  rw [Nat.card_eq_fintype_card] at hN
  exact exists_right_complement'_of_coprime_of_fintype hN

/-- **Schur-Zassenhaus** for normal subgroups:
  If `H : subgroup G` is normal, and has order coprime to its index, then there exists a
  subgroup `K` which is a (left) complement of `H`. -/
theorem exists_left_complement'_of_coprime_of_fintype [Fintype G] {N : Subgroup G} [N.Normal]
    (hN : Nat.Coprime (Fintype.card N) N.index) : ∃ H : Subgroup G, IsComplement' H N :=
  Exists.imp (fun _ => IsComplement'.symm) (exists_right_complement'_of_coprime_of_fintype hN)

/-- **Schur-Zassenhaus** for normal subgroups:
  If `H : subgroup G` is normal, and has order coprime to its index, then there exists a
  subgroup `K` which is a (left) complement of `H`. -/
theorem exists_left_complement'_of_coprime {N : Subgroup G} [N.Normal] (hN : Nat.Coprime (Nat.card N) N.index) :
    ∃ H : Subgroup G, IsComplement' H N :=
  Exists.imp (fun _ => IsComplement'.symm) (exists_right_complement'_of_coprime hN)

end Subgroup

