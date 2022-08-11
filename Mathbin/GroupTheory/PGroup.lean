/-
Copyright (c) 2018 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Thomas Browning
-/
import Mathbin.Data.Zmod.Basic
import Mathbin.GroupTheory.Index
import Mathbin.GroupTheory.GroupAction.ConjAct
import Mathbin.GroupTheory.GroupAction.Quotient
import Mathbin.GroupTheory.Perm.Cycle.Type

/-!
# p-groups

This file contains a proof that if `G` is a `p`-group acting on a finite set `α`,
then the number of fixed points of the action is congruent mod `p` to the cardinality of `α`.
It also contains proofs of some corollaries of this lemma about existence of fixed points.
-/


open BigOperators

open Fintype MulAction

variable (p : ℕ) (G : Type _) [Groupₓ G]

/-- A p-group is a group in which every element has prime power order -/
def IsPGroup : Prop :=
  ∀ g : G, ∃ k : ℕ, g ^ p ^ k = 1

variable {p} {G}

namespace IsPGroup

theorem iff_order_of [hp : Fact p.Prime] : IsPGroup p G ↔ ∀ g : G, ∃ k : ℕ, orderOf g = p ^ k :=
  forall_congrₓ fun g =>
    ⟨fun ⟨k, hk⟩ =>
      exists_imp_exists (fun j => Exists.snd) ((Nat.dvd_prime_pow hp.out).mp (order_of_dvd_of_pow_eq_one hk)),
      exists_imp_exists fun k hk => by
        rw [← hk, pow_order_of_eq_one]⟩

theorem of_card [Fintype G] {n : ℕ} (hG : card G = p ^ n) : IsPGroup p G := fun g =>
  ⟨n, by
    rw [← hG, pow_card_eq_one]⟩

theorem of_bot : IsPGroup p (⊥ : Subgroup G) :=
  of_card (Subgroup.card_bot.trans (pow_zeroₓ p).symm)

theorem iff_card [Fact p.Prime] [Fintype G] : IsPGroup p G ↔ ∃ n : ℕ, card G = p ^ n := by
  have hG : card G ≠ 0 := card_ne_zero
  refine' ⟨fun h => _, fun ⟨n, hn⟩ => of_card hn⟩
  suffices ∀, ∀ q ∈ Nat.factors (card G), ∀, q = p by
    use (card G).factors.length
    rw [← List.prod_repeat, ← List.eq_repeat_of_mem this, Nat.prod_factors hG]
  intro q hq
  obtain ⟨hq1, hq2⟩ := (Nat.mem_factors hG).mp hq
  have : Fact q.prime := ⟨hq1⟩
  obtain ⟨g, hg⟩ := exists_prime_order_of_dvd_card q hq2
  obtain ⟨k, hk⟩ := (iff_order_of.mp h) g
  exact (hq1.pow_eq_iff.mp (hg.symm.trans hk).symm).1.symm

section GIsPGroup

variable (hG : IsPGroup p G)

include hG

theorem of_injective {H : Type _} [Groupₓ H] (ϕ : H →* G) (hϕ : Function.Injective ϕ) : IsPGroup p H := by
  simp_rw [IsPGroup, ← hϕ.eq_iff, ϕ.map_pow, ϕ.map_one]
  exact fun h => hG (ϕ h)

theorem to_subgroup (H : Subgroup G) : IsPGroup p H :=
  hG.ofInjective H.Subtype Subtype.coe_injective

theorem of_surjective {H : Type _} [Groupₓ H] (ϕ : G →* H) (hϕ : Function.Surjective ϕ) : IsPGroup p H := by
  refine' fun h => Exists.elim (hϕ h) fun g hg => exists_imp_exists (fun k hk => _) (hG g)
  rw [← hg, ← ϕ.map_pow, hk, ϕ.map_one]

theorem to_quotient (H : Subgroup G) [H.Normal] : IsPGroup p (G ⧸ H) :=
  hG.ofSurjective (QuotientGroup.mk' H) Quotientₓ.surjective_quotient_mk'

theorem of_equiv {H : Type _} [Groupₓ H] (ϕ : G ≃* H) : IsPGroup p H :=
  hG.ofSurjective ϕ.toMonoidHom ϕ.Surjective

variable [hp : Fact p.Prime]

include hp

theorem index (H : Subgroup G) [Fintype (G ⧸ H)] : ∃ n : ℕ, H.index = p ^ n := by
  obtain ⟨n, hn⟩ := iff_card.mp (hG.to_quotient H.normal_core)
  obtain ⟨k, hk1, hk2⟩ :=
    (Nat.dvd_prime_pow hp.out).mp
      ((congr_arg _ (H.normal_core.index_eq_card.trans hn)).mp (Subgroup.index_dvd_of_le H.normal_core_le))
  exact ⟨k, hk2⟩

variable {α : Type _} [MulAction G α]

theorem card_orbit (a : α) [Fintype (Orbit G a)] : ∃ n : ℕ, card (Orbit G a) = p ^ n := by
  let ϕ := orbit_equiv_quotient_stabilizer G a
  have := Fintype.ofEquiv (orbit G a) ϕ
  rw [card_congr ϕ, ← Subgroup.index_eq_card]
  exact hG.index (stabilizer G a)

variable (α) [Fintype α] [Fintype (FixedPoints G α)]

/-- If `G` is a `p`-group acting on a finite set `α`, then the number of fixed points
  of the action is congruent mod `p` to the cardinality of `α` -/
theorem card_modeq_card_fixed_points : card α ≡ card (FixedPoints G α) [MOD p] := by
  classical
  calc card α = card (Σy : Quotientₓ (orbit_rel G α), { x // Quotientₓ.mk' x = y }) :=
      card_congr
        (Equivₓ.sigmaFiberEquiv
            (@Quotientₓ.mk' _
              (orbit_rel G α))).symm _ = ∑ a : Quotientₓ (orbit_rel G α), card { x // Quotientₓ.mk' x = a } :=
      card_sigma _ _ ≡ ∑ a : fixed_points G α, 1 [MOD p] := _ _ = _ := by
      simp <;> rfl
  rw [← Zmod.eq_iff_modeq_nat p, Nat.cast_sum, Nat.cast_sum]
  have key : ∀ x, card { y // (Quotientₓ.mk' y : Quotientₓ (orbit_rel G α)) = Quotientₓ.mk' x } = card (orbit G x) :=
    fun x => by
    simp only [← Quotientₓ.eq'] <;> congr
  refine'
    Eq.symm
      (Finset.sum_bij_ne_zero (fun a _ _ => Quotientₓ.mk' a.1) (fun _ _ _ => Finset.mem_univ _)
        (fun a₁ a₂ _ _ _ _ h => Subtype.eq ((mem_fixed_points' α).mp a₂.2 a₁.1 (Quotientₓ.exact' h)))
        (fun b => Quotientₓ.induction_on' b fun b _ hb => _) fun a ha _ => by
        rw [key, mem_fixed_points_iff_card_orbit_eq_one.mp a.2])
  obtain ⟨k, hk⟩ := hG.card_orbit b
  have : k = 0 :=
    Nat.le_zero_iffₓ.1
      (Nat.le_of_lt_succₓ
        (lt_of_not_geₓ
          (mt (pow_dvd_pow p)
            (by
              rwa [pow_oneₓ, ← hk, ← Nat.modeq_zero_iff_dvd, ← Zmod.eq_iff_modeq_nat, ← key, Nat.cast_zeroₓ]))))
  exact
    ⟨⟨b,
        mem_fixed_points_iff_card_orbit_eq_one.2 <| by
          rw [hk, this, pow_zeroₓ]⟩,
      Finset.mem_univ _, ne_of_eq_of_ne Nat.cast_oneₓ one_ne_zero, rfl⟩

/-- If a p-group acts on `α` and the cardinality of `α` is not a multiple
  of `p` then the action has a fixed point. -/
theorem nonempty_fixed_point_of_prime_not_dvd_card (hpα : ¬p ∣ card α) : (FixedPoints G α).Nonempty :=
  @Set.nonempty_of_nonempty_subtype _ _
    (by
      rw [← card_pos_iff, pos_iff_ne_zero]
      contrapose! hpα
      rw [← Nat.modeq_zero_iff_dvd, ← hpα]
      exact hG.card_modeq_card_fixed_points α)

/-- If a p-group acts on `α` and the cardinality of `α` is a multiple
  of `p`, and the action has one fixed point, then it has another fixed point. -/
theorem exists_fixed_point_of_prime_dvd_card_of_fixed_point (hpα : p ∣ card α) {a : α} (ha : a ∈ FixedPoints G α) :
    ∃ b, b ∈ FixedPoints G α ∧ a ≠ b :=
  have hpf : p ∣ card (FixedPoints G α) :=
    Nat.modeq_zero_iff_dvd.mp ((hG.card_modeq_card_fixed_points α).symm.trans hpα.modeq_zero_nat)
  have hα : 1 < card (FixedPoints G α) :=
    (Fact.out p.Prime).one_lt.trans_le (Nat.le_of_dvdₓ (card_pos_iff.2 ⟨⟨a, ha⟩⟩) hpf)
  let ⟨⟨b, hb⟩, hba⟩ := exists_ne_of_one_lt_card hα ⟨a, ha⟩
  ⟨b, hb, fun hab =>
    hba
      (by
        simp_rw [hab])⟩

theorem center_nontrivial [Nontrivial G] [Fintype G] : Nontrivial (Subgroup.center G) := by
  classical
  have := (hG.of_equiv ConjAct.toConjAct).exists_fixed_point_of_prime_dvd_card_of_fixed_point G
  rw [ConjAct.fixed_points_eq_center] at this
  obtain ⟨g, hg⟩ := this _ (Subgroup.center G).one_mem
  · exact ⟨⟨1, ⟨g, hg.1⟩, mt subtype.ext_iff.mp hg.2⟩⟩
    
  · obtain ⟨n, hn⟩ := is_p_group.iff_card.mp hG
    rw [hn]
    apply dvd_pow_self
    rintro rfl
    exact Fintype.one_lt_card.ne' hn
    

theorem bot_lt_center [Nontrivial G] [Fintype G] : ⊥ < Subgroup.center G := by
  have := center_nontrivial hG
  classical
  exact bot_lt_iff_ne_bot.mpr ((Subgroup.center G).one_lt_card_iff_ne_bot.mp Fintype.one_lt_card)

end GIsPGroup

theorem to_le {H K : Subgroup G} (hK : IsPGroup p K) (hHK : H ≤ K) : IsPGroup p H :=
  hK.ofInjective (Subgroup.inclusion hHK) fun a b h => Subtype.ext (show _ from Subtype.ext_iff.mp h)

theorem to_inf_left {H K : Subgroup G} (hH : IsPGroup p H) : IsPGroup p (H⊓K : Subgroup G) :=
  hH.to_le inf_le_left

theorem to_inf_right {H K : Subgroup G} (hK : IsPGroup p K) : IsPGroup p (H⊓K : Subgroup G) :=
  hK.to_le inf_le_right

theorem map {H : Subgroup G} (hH : IsPGroup p H) {K : Type _} [Groupₓ K] (ϕ : G →* K) : IsPGroup p (H.map ϕ) := by
  rw [← H.subtype_range, MonoidHom.map_range]
  exact hH.of_surjective (ϕ.restrict H).range_restrict (ϕ.restrict H).range_restrict_surjective

theorem comap_of_ker_is_p_group {H : Subgroup G} (hH : IsPGroup p H) {K : Type _} [Groupₓ K] (ϕ : K →* G)
    (hϕ : IsPGroup p ϕ.ker) : IsPGroup p (H.comap ϕ) := by
  intro g
  obtain ⟨j, hj⟩ := hH ⟨ϕ g.1, g.2⟩
  rw [Subtype.ext_iff, H.coe_pow, Subtype.coe_mk, ← ϕ.map_pow] at hj
  obtain ⟨k, hk⟩ := hϕ ⟨g.1 ^ p ^ j, hj⟩
  rwa [Subtype.ext_iff, ϕ.ker.coe_pow, Subtype.coe_mk, ← pow_mulₓ, ← pow_addₓ] at hk
  exact
    ⟨j + k, by
      rwa [Subtype.ext_iff, (H.comap ϕ).coe_pow]⟩

theorem ker_is_p_group_of_injective {K : Type _} [Groupₓ K] {ϕ : K →* G} (hϕ : Function.Injective ϕ) :
    IsPGroup p ϕ.ker :=
  (congr_arg (fun Q : Subgroup K => IsPGroup p Q) (ϕ.ker_eq_bot_iff.mpr hϕ)).mpr IsPGroup.of_bot

theorem comap_of_injective {H : Subgroup G} (hH : IsPGroup p H) {K : Type _} [Groupₓ K] (ϕ : K →* G)
    (hϕ : Function.Injective ϕ) : IsPGroup p (H.comap ϕ) :=
  hH.comap_of_ker_is_p_group ϕ (ker_is_p_group_of_injective hϕ)

theorem comap_subtype {H : Subgroup G} (hH : IsPGroup p H) {K : Subgroup G} : IsPGroup p (H.comap K.Subtype) :=
  hH.comap_of_injective K.Subtype Subtype.coe_injective

theorem to_sup_of_normal_right {H K : Subgroup G} (hH : IsPGroup p H) (hK : IsPGroup p K) [K.Normal] :
    IsPGroup p (H⊔K : Subgroup G) := by
  rw [← QuotientGroup.ker_mk K, ← Subgroup.comap_map_eq]
  apply (hH.map (QuotientGroup.mk' K)).comap_of_ker_is_p_group
  rwa [QuotientGroup.ker_mk]

theorem to_sup_of_normal_left {H K : Subgroup G} (hH : IsPGroup p H) (hK : IsPGroup p K) [H.Normal] :
    IsPGroup p (H⊔K : Subgroup G) :=
  (congr_arg (fun H : Subgroup G => IsPGroup p H) sup_comm).mp (to_sup_of_normal_right hK hH)

theorem to_sup_of_normal_right' {H K : Subgroup G} (hH : IsPGroup p H) (hK : IsPGroup p K) (hHK : H ≤ K.normalizer) :
    IsPGroup p (H⊔K : Subgroup G) :=
  let hHK' :=
    to_sup_of_normal_right (hH.ofEquiv (Subgroup.comapSubtypeEquivOfLe hHK).symm)
      (hK.ofEquiv (Subgroup.comapSubtypeEquivOfLe Subgroup.le_normalizer).symm)
  ((congr_arg (fun H : Subgroup K.normalizer => IsPGroup p H)
            (Subgroup.sup_subgroup_of_eq hHK Subgroup.le_normalizer)).mp
        hHK').ofEquiv
    (Subgroup.comapSubtypeEquivOfLe (sup_le hHK Subgroup.le_normalizer))

theorem to_sup_of_normal_left' {H K : Subgroup G} (hH : IsPGroup p H) (hK : IsPGroup p K) (hHK : K ≤ H.normalizer) :
    IsPGroup p (H⊔K : Subgroup G) :=
  (congr_arg (fun H : Subgroup G => IsPGroup p H) sup_comm).mp (to_sup_of_normal_right' hK hH hHK)

/-- finite p-groups with different p have coprime orders -/
theorem coprime_card_of_ne {G₂ : Type _} [Groupₓ G₂] (p₁ p₂ : ℕ) [hp₁ : Fact p₁.Prime] [hp₂ : Fact p₂.Prime]
    (hne : p₁ ≠ p₂) (H₁ : Subgroup G) (H₂ : Subgroup G₂) [Fintype H₁] [Fintype H₂] (hH₁ : IsPGroup p₁ H₁)
    (hH₂ : IsPGroup p₂ H₂) : Nat.Coprime (Fintype.card H₁) (Fintype.card H₂) := by
  obtain ⟨n₁, heq₁⟩ := iff_card.mp hH₁
  rw [heq₁]
  clear heq₁
  obtain ⟨n₂, heq₂⟩ := iff_card.mp hH₂
  rw [heq₂]
  clear heq₂
  exact Nat.coprime_pow_primes _ _ hp₁.elim hp₂.elim hne

/-- p-groups with different p are disjoint -/
theorem disjoint_of_ne (p₁ p₂ : ℕ) [hp₁ : Fact p₁.Prime] [hp₂ : Fact p₂.Prime] (hne : p₁ ≠ p₂) (H₁ H₂ : Subgroup G)
    (hH₁ : IsPGroup p₁ H₁) (hH₂ : IsPGroup p₂ H₂) : Disjoint H₁ H₂ := by
  rintro x ⟨hx₁, hx₂⟩
  rw [Subgroup.mem_bot]
  obtain ⟨n₁, hn₁⟩ := iff_order_of.mp hH₁ ⟨x, hx₁⟩
  obtain ⟨n₂, hn₂⟩ := iff_order_of.mp hH₂ ⟨x, hx₂⟩
  rw [← order_of_subgroup, Subgroup.coe_mk] at hn₁ hn₂
  have : p₁ ^ n₁ = p₂ ^ n₂ := by
    rw [← hn₁, ← hn₂]
  have : n₁ = 0 := by
    contrapose! hne with h
    rw [← associated_iff_eq] at this⊢
    exact
      Associated.of_pow_associated_of_prime (nat.prime_iff.mp hp₁.elim) (nat.prime_iff.mp hp₂.elim) (Ne.bot_lt h) this
  simpa [← this] using hn₁

end IsPGroup

