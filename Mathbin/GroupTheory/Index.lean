/-
Copyright (c) 2021 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
import Mathbin.GroupTheory.QuotientGroup
import Mathbin.SetTheory.Cardinal.Finite

/-!
# Index of a Subgroup

In this file we define the index of a subgroup, and prove several divisibility properties.
Several theorems proved in this file are known as Lagrange's theorem.

## Main definitions

- `H.index` : the index of `H : subgroup G` as a natural number,
  and returns 0 if the index is infinite.
- `H.relindex K` : the relative index of `H : subgroup G` in `K : subgroup G` as a natural number,
  and returns 0 if the relative index is infinite.

# Main results

- `card_mul_index` : `nat.card H * H.index = nat.card G`
- `index_mul_card` : `H.index * fintype.card H = fintype.card G`
- `index_dvd_card` : `H.index ∣ fintype.card G`
- `index_eq_mul_of_le` : If `H ≤ K`, then `H.index = K.index * (H.subgroup_of K).index`
- `index_dvd_of_le` : If `H ≤ K`, then `K.index ∣ H.index`
- `relindex_mul_relindex` : `relindex` is multiplicative in towers

-/


namespace Subgroup

open Cardinal

variable {G : Type _} [Groupₓ G] (H K L : Subgroup G)

/-- The index of a subgroup as a natural number, and returns 0 if the index is infinite. -/
@[to_additive "The index of a subgroup as a natural number,\nand returns 0 if the index is infinite."]
noncomputable def index : ℕ :=
  Nat.card (G ⧸ H)

/-- The relative index of a subgroup as a natural number,
  and returns 0 if the relative index is infinite. -/
@[to_additive
      "The relative index of a subgroup as a natural number,\n  and returns 0 if the relative index is infinite."]
noncomputable def relindex : ℕ :=
  (H.subgroupOf K).index

@[to_additive]
theorem index_comap_of_surjective {G' : Type _} [Groupₓ G'] {f : G' →* G} (hf : Function.Surjective f) :
    (H.comap f).index = H.index := by
  let this := QuotientGroup.leftRel H
  let this := QuotientGroup.leftRel (H.comap f)
  have key : ∀ x y : G', Setoidₓ.R x y ↔ Setoidₓ.R (f x) (f y) := by
    simp only [← QuotientGroup.left_rel_apply]
    exact fun x y =>
      iff_of_eq
        (congr_arg (· ∈ H)
          (by
            rw [f.map_mul, f.map_inv]))
  refine' Cardinal.to_nat_congr (Equivₓ.ofBijective (Quotientₓ.map' f fun x y => (key x y).mp) ⟨_, _⟩)
  · simp_rw [← Quotientₓ.eq'] at key
    refine' Quotientₓ.ind' fun x => _
    refine' Quotientₓ.ind' fun y => _
    exact (key x y).mpr
    
  · refine' Quotientₓ.ind' fun x => _
    obtain ⟨y, hy⟩ := hf x
    exact ⟨y, (Quotientₓ.map'_mk' f _ y).trans (congr_arg Quotientₓ.mk' hy)⟩
    

@[to_additive]
theorem index_comap {G' : Type _} [Groupₓ G'] (f : G' →* G) : (H.comap f).index = H.relindex f.range :=
  Eq.trans
    (congr_arg index
      (by
        rfl))
    ((H.subgroupOf f.range).index_comap_of_surjective f.range_restrict_surjective)

variable {H K L}

@[to_additive relindex_mul_index]
theorem relindex_mul_index (h : H ≤ K) : H.relindex K * K.index = H.index :=
  ((mul_comm _ _).trans (Cardinal.to_nat_mul _ _).symm).trans
    (congr_arg Cardinal.toNat (Equivₓ.cardinal_eq (quotientEquivProdOfLe h))).symm

@[to_additive]
theorem index_dvd_of_le (h : H ≤ K) : K.index ∣ H.index :=
  dvd_of_mul_left_eq (H.relindex K) (relindex_mul_index h)

@[to_additive]
theorem relindex_dvd_index_of_le (h : H ≤ K) : H.relindex K ∣ H.index :=
  dvd_of_mul_right_eq K.index (relindex_mul_index h)

@[to_additive]
theorem relindex_subgroup_of (hKL : K ≤ L) : (H.subgroupOf L).relindex (K.subgroupOf L) = H.relindex K :=
  ((index_comap (H.subgroupOf L) (inclusion hKL)).trans (congr_arg _ (inclusion_range hKL))).symm

variable (H K L)

@[to_additive relindex_mul_relindex]
theorem relindex_mul_relindex (hHK : H ≤ K) (hKL : K ≤ L) : H.relindex K * K.relindex L = H.relindex L := by
  rw [← relindex_subgroup_of hKL]
  exact relindex_mul_index fun x hx => hHK hx

@[to_additive]
theorem inf_relindex_right : (H⊓K).relindex K = H.relindex K := by
  rw [← subgroup_of_map_subtype, relindex, relindex, subgroup_of, comap_map_eq_self_of_injective]
  exact Subtype.coe_injective

@[to_additive]
theorem inf_relindex_left : (H⊓K).relindex H = K.relindex H := by
  rw [inf_comm, inf_relindex_right]

@[to_additive relindex_inf_mul_relindex]
theorem relindex_inf_mul_relindex : H.relindex (K⊓L) * K.relindex L = (H⊓K).relindex L := by
  rw [← inf_relindex_right H (K⊓L), ← inf_relindex_right K L, ← inf_relindex_right (H⊓K) L, inf_assoc,
    relindex_mul_relindex (H⊓(K⊓L)) (K⊓L) L inf_le_right inf_le_right]

@[to_additive]
theorem inf_relindex_eq_relindex_sup [K.Normal] : (H⊓K).relindex H = K.relindex (H⊔K) :=
  Cardinal.to_nat_congr (QuotientGroup.quotientInfEquivProdNormalQuotient H K).toEquiv

@[to_additive]
theorem relindex_eq_relindex_sup [K.Normal] : K.relindex H = K.relindex (H⊔K) := by
  rw [← inf_relindex_left, inf_relindex_eq_relindex_sup]

@[to_additive]
theorem relindex_dvd_index_of_normal [H.Normal] : H.relindex K ∣ H.index :=
  (relindex_eq_relindex_sup K H).symm ▸ relindex_dvd_index_of_le le_sup_right

variable {H K}

@[to_additive]
theorem relindex_dvd_of_le_left (hHK : H ≤ K) : K.relindex L ∣ H.relindex L := by
  apply dvd_of_mul_left_eq ((H⊓L).relindex (K⊓L))
  rw [← inf_relindex_right H L, ← inf_relindex_right K L]
  exact relindex_mul_relindex (H⊓L) (K⊓L) L (inf_le_inf_right L hHK) inf_le_right

variable (H K)

@[simp, to_additive]
theorem index_top : (⊤ : Subgroup G).index = 1 :=
  Cardinal.to_nat_eq_one_iff_unique.mpr ⟨QuotientGroup.subsingleton_quotient_top, ⟨1⟩⟩

@[simp, to_additive]
theorem index_bot : (⊥ : Subgroup G).index = Nat.card G :=
  Cardinal.to_nat_congr QuotientGroup.quotientBot.toEquiv

@[to_additive]
theorem index_bot_eq_card [Fintype G] : (⊥ : Subgroup G).index = Fintype.card G :=
  index_bot.trans Nat.card_eq_fintype_card

@[simp, to_additive]
theorem relindex_top_left : (⊤ : Subgroup G).relindex H = 1 :=
  index_top

@[simp, to_additive]
theorem relindex_top_right : H.relindex ⊤ = H.index := by
  rw [← relindex_mul_index (show H ≤ ⊤ from le_top), index_top, mul_oneₓ]

@[simp, to_additive]
theorem relindex_bot_left : (⊥ : Subgroup G).relindex H = Nat.card H := by
  rw [relindex, bot_subgroup_of, index_bot]

@[to_additive]
theorem relindex_bot_left_eq_card [Fintype H] : (⊥ : Subgroup G).relindex H = Fintype.card H :=
  H.relindex_bot_left.trans Nat.card_eq_fintype_card

@[simp, to_additive]
theorem relindex_bot_right : H.relindex ⊥ = 1 := by
  rw [relindex, subgroup_of_bot_eq_top, index_top]

@[simp, to_additive]
theorem relindex_self : H.relindex H = 1 := by
  rw [relindex, subgroup_of_self, index_top]

@[simp, to_additive card_mul_index]
theorem card_mul_index : Nat.card H * H.index = Nat.card G := by
  rw [← relindex_bot_left, ← index_bot]
  exact relindex_mul_index bot_le

@[to_additive]
theorem index_map {G' : Type _} [Groupₓ G'] (f : G →* G') : (H.map f).index = (H⊔f.ker).index * f.range.index := by
  rw [← comap_map_eq, index_comap, relindex_mul_index (H.map_le_range f)]

@[to_additive]
theorem index_map_dvd {G' : Type _} [Groupₓ G'] {f : G →* G'} (hf : Function.Surjective f) :
    (H.map f).index ∣ H.index := by
  rw [index_map, f.range_top_of_surjective hf, index_top, mul_oneₓ]
  exact index_dvd_of_le le_sup_left

@[to_additive]
theorem dvd_index_map {G' : Type _} [Groupₓ G'] {f : G →* G'} (hf : f.ker ≤ H) : H.index ∣ (H.map f).index := by
  rw [index_map, sup_of_le_left hf]
  apply dvd_mul_right

@[to_additive]
theorem index_map_eq {G' : Type _} [Groupₓ G'] {f : G →* G'} (hf1 : Function.Surjective f) (hf2 : f.ker ≤ H) :
    (H.map f).index = H.index :=
  Nat.dvd_antisymm (H.index_map_dvd hf1) (H.dvd_index_map hf2)

@[to_additive]
theorem index_eq_card [Fintype (G ⧸ H)] : H.index = Fintype.card (G ⧸ H) :=
  Nat.card_eq_fintype_card

@[to_additive index_mul_card]
theorem index_mul_card [Fintype G] [hH : Fintype H] : H.index * Fintype.card H = Fintype.card G := by
  rw [← relindex_bot_left_eq_card, ← index_bot_eq_card, mul_comm] <;> exact relindex_mul_index bot_le

@[to_additive]
theorem index_dvd_card [Fintype G] : H.index ∣ Fintype.card G := by
  classical
  exact ⟨Fintype.card H, H.index_mul_card.symm⟩

variable {H K L}

@[to_additive]
theorem relindex_eq_zero_of_le_left (hHK : H ≤ K) (hKL : K.relindex L = 0) : H.relindex L = 0 :=
  eq_zero_of_zero_dvd (hKL ▸ relindex_dvd_of_le_left L hHK)

@[to_additive]
theorem relindex_eq_zero_of_le_right (hKL : K ≤ L) (hHK : H.relindex K = 0) : H.relindex L = 0 :=
  Cardinal.to_nat_apply_of_aleph_0_le
    (le_transₓ
      (le_of_not_ltₓ fun h =>
        Cardinal.mk_ne_zero _ ((Cardinal.cast_to_nat_of_lt_aleph_0 h).symm.trans (Cardinal.nat_cast_inj.mpr hHK)))
      (quotientSubgroupOfEmbeddingOfLe H hKL).cardinal_le)

@[to_additive]
theorem relindex_le_of_le_left (hHK : H ≤ K) (hHL : H.relindex L ≠ 0) : K.relindex L ≤ H.relindex L :=
  Nat.le_of_dvdₓ (Nat.pos_of_ne_zeroₓ hHL) (relindex_dvd_of_le_left L hHK)

@[to_additive]
theorem relindex_le_of_le_right (hKL : K ≤ L) (hHL : H.relindex L ≠ 0) : H.relindex K ≤ H.relindex L :=
  Cardinal.to_nat_le_of_le_of_lt_aleph_0 (lt_of_not_geₓ (mt Cardinal.to_nat_apply_of_aleph_0_le hHL))
    (Cardinal.mk_le_of_injective (quotientSubgroupOfEmbeddingOfLe H hKL).2)

@[to_additive]
theorem relindex_ne_zero_trans (hHK : H.relindex K ≠ 0) (hKL : K.relindex L ≠ 0) : H.relindex L ≠ 0 := fun h =>
  mul_ne_zero (mt (relindex_eq_zero_of_le_right (show K⊓L ≤ K from inf_le_left)) hHK) hKL
    ((relindex_inf_mul_relindex H K L).trans (relindex_eq_zero_of_le_left inf_le_left h))

@[to_additive]
theorem relindex_inf_ne_zero (hH : H.relindex L ≠ 0) (hK : K.relindex L ≠ 0) : (H⊓K).relindex L ≠ 0 := by
  replace hH : H.relindex (K⊓L) ≠ 0 := mt (relindex_eq_zero_of_le_right inf_le_right) hH
  rw [← inf_relindex_right] at hH hK⊢
  rw [inf_assoc]
  exact relindex_ne_zero_trans hH hK

@[to_additive]
theorem index_inf_ne_zero (hH : H.index ≠ 0) (hK : K.index ≠ 0) : (H⊓K).index ≠ 0 := by
  rw [← relindex_top_right] at hH hK⊢
  exact relindex_inf_ne_zero hH hK

@[to_additive]
theorem relindex_inf_le : (H⊓K).relindex L ≤ H.relindex L * K.relindex L := by
  by_cases' h : H.relindex L = 0
  · exact (le_of_eqₓ (relindex_eq_zero_of_le_left inf_le_left h)).trans (zero_le _)
    
  rw [← inf_relindex_right, inf_assoc, ← relindex_mul_relindex _ _ L inf_le_right inf_le_right, inf_relindex_right,
    inf_relindex_right]
  exact mul_le_mul_right' (relindex_le_of_le_right inf_le_right h) (K.relindex L)

@[to_additive]
theorem index_inf_le : (H⊓K).index ≤ H.index * K.index := by
  simp_rw [← relindex_top_right, relindex_inf_le]

@[simp, to_additive index_eq_one]
theorem index_eq_one : H.index = 1 ↔ H = ⊤ :=
  ⟨fun h => QuotientGroup.subgroup_eq_top_of_subsingleton H (Cardinal.to_nat_eq_one_iff_unique.mp h).1, fun h =>
    (congr_arg index h).trans index_top⟩

@[to_additive]
theorem index_ne_zero_of_fintype [hH : Fintype (G ⧸ H)] : H.index ≠ 0 := by
  rw [index_eq_card]
  exact Fintype.card_ne_zero

/-- Finite index implies finite quotient. -/
@[to_additive "Finite index implies finite quotient."]
noncomputable def fintypeOfIndexNeZero (hH : H.index ≠ 0) : Fintype (G ⧸ H) :=
  (Cardinal.lt_aleph_0_iff_fintype.mp (lt_of_not_geₓ (mt Cardinal.to_nat_apply_of_aleph_0_le hH))).some

@[to_additive one_lt_index_of_ne_top]
theorem one_lt_index_of_ne_top [Fintype (G ⧸ H)] (hH : H ≠ ⊤) : 1 < H.index :=
  Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨index_ne_zero_of_fintype, mt index_eq_one.mp hH⟩

end Subgroup

