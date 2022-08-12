/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Thomas Browning
-/
import Mathbin.Data.Nat.Factorization.Basic
import Mathbin.Data.SetLike.Fintype
import Mathbin.GroupTheory.GroupAction.ConjAct
import Mathbin.GroupTheory.PGroup
import Mathbin.GroupTheory.NoncommPiCoprod

/-!
# Sylow theorems

The Sylow theorems are the following results for every finite group `G` and every prime number `p`.

* There exists a Sylow `p`-subgroup of `G`.
* All Sylow `p`-subgroups of `G` are conjugate to each other.
* Let `nₚ` be the number of Sylow `p`-subgroups of `G`, then `nₚ` divides the index of the Sylow
  `p`-subgroup, `nₚ ≡ 1 [MOD p]`, and `nₚ` is equal to the index of the normalizer of the Sylow
  `p`-subgroup in `G`.

## Main definitions

* `sylow p G` : The type of Sylow `p`-subgroups of `G`.

## Main statements

* `exists_subgroup_card_pow_prime`: A generalization of Sylow's first theorem:
  For every prime power `pⁿ` dividing the cardinality of `G`,
  there exists a subgroup of `G` of order `pⁿ`.
* `is_p_group.exists_le_sylow`: A generalization of Sylow's first theorem:
  Every `p`-subgroup is contained in a Sylow `p`-subgroup.
* `sylow_conjugate`: A generalization of Sylow's second theorem:
  If the number of Sylow `p`-subgroups is finite, then all Sylow `p`-subgroups are conjugate.
* `card_sylow_modeq_one`: A generalization of Sylow's third theorem:
  If the number of Sylow `p`-subgroups is finite, then it is congruent to `1` modulo `p`.
-/


open Fintype MulAction Subgroup

section InfiniteSylow

variable (p : ℕ) (G : Type _) [Groupₓ G]

/-- A Sylow `p`-subgroup is a maximal `p`-subgroup. -/
structure Sylow extends Subgroup G where
  is_p_group' : IsPGroup p to_subgroup
  is_maximal' : ∀ {Q : Subgroup G}, IsPGroup p Q → to_subgroup ≤ Q → Q = to_subgroup

variable {p} {G}

namespace Sylow

instance : Coe (Sylow p G) (Subgroup G) :=
  ⟨Sylow.toSubgroup⟩

@[simp]
theorem to_subgroup_eq_coe {P : Sylow p G} : P.toSubgroup = ↑P :=
  rfl

@[ext]
theorem ext {P Q : Sylow p G} (h : (P : Subgroup G) = Q) : P = Q := by
  cases P <;> cases Q <;> congr

theorem ext_iff {P Q : Sylow p G} : P = Q ↔ (P : Subgroup G) = Q :=
  ⟨congr_arg coe, ext⟩

instance : SetLike (Sylow p G) G where
  coe := coe
  coe_injective' := fun P Q h => ext (SetLike.coe_injective h)

instance : SubgroupClass (Sylow p G) G where
  mul_mem := fun s => s.mul_mem'
  one_mem := fun s => s.one_mem'
  inv_mem := fun s => s.inv_mem'

variable (P : Sylow p G) {K : Type _} [Groupₓ K] (ϕ : K →* G) {N : Subgroup G}

/-- The preimage of a Sylow subgroup under a p-group-kernel homomorphism is a Sylow subgroup. -/
def comapOfKerIsPGroup (hϕ : IsPGroup p ϕ.ker) (h : ↑P ≤ ϕ.range) : Sylow p K :=
  { P.1.comap ϕ with is_p_group' := P.2.comap_of_ker_is_p_group ϕ hϕ,
    is_maximal' := fun Q hQ hle => by
      rw [← P.3 (hQ.map ϕ) (le_transₓ (ge_of_eq (map_comap_eq_self h)) (map_mono hle))]
      exact (comap_map_eq_self ((P.1.ker_le_comap ϕ).trans hle)).symm }

@[simp]
theorem coe_comap_of_ker_is_p_group (hϕ : IsPGroup p ϕ.ker) (h : ↑P ≤ ϕ.range) :
    ↑(P.comap_of_ker_is_p_group ϕ hϕ h) = Subgroup.comap ϕ ↑P :=
  rfl

/-- The preimage of a Sylow subgroup under an injective homomorphism is a Sylow subgroup. -/
def comapOfInjective (hϕ : Function.Injective ϕ) (h : ↑P ≤ ϕ.range) : Sylow p K :=
  P.comap_of_ker_is_p_group ϕ (IsPGroup.ker_is_p_group_of_injective hϕ) h

@[simp]
theorem coe_comap_of_injective (hϕ : Function.Injective ϕ) (h : ↑P ≤ ϕ.range) :
    ↑(P.comap_of_injective ϕ hϕ h) = Subgroup.comap ϕ ↑P :=
  rfl

/-- A sylow subgroup of G is also a sylow subgroup of a subgroup of G. -/
def subtype (h : ↑P ≤ N) : Sylow p N :=
  P.comap_of_injective N.Subtype Subtype.coe_injective
    (by
      simp [← h])

@[simp]
theorem coe_subtype (h : ↑P ≤ N) : ↑(P.Subtype h) = Subgroup.comap N.Subtype ↑P :=
  rfl

end Sylow

/-- A generalization of **Sylow's first theorem**.
  Every `p`-subgroup is contained in a Sylow `p`-subgroup. -/
theorem IsPGroup.exists_le_sylow {P : Subgroup G} (hP : IsPGroup p P) : ∃ Q : Sylow p G, P ≤ Q :=
  Exists.elim
    (zorn_nonempty_partial_order₀ { Q : Subgroup G | IsPGroup p Q }
      (fun c hc1 hc2 Q hQ =>
        ⟨{ Carrier := ⋃ R : c, R, one_mem' := ⟨Q, ⟨⟨Q, hQ⟩, rfl⟩, Q.one_mem⟩,
            inv_mem' := fun g ⟨_, ⟨R, rfl⟩, hg⟩ => ⟨R, ⟨R, rfl⟩, R.1.inv_mem hg⟩,
            mul_mem' := fun g h ⟨_, ⟨R, rfl⟩, hg⟩ ⟨_, ⟨S, rfl⟩, hh⟩ =>
              (hc2.Total R.2 S.2).elim (fun T => ⟨S, ⟨S, rfl⟩, S.1.mul_mem (T hg) hh⟩) fun T =>
                ⟨R, ⟨R, rfl⟩, R.1.mul_mem hg (T hh)⟩ },
          fun ⟨g, _, ⟨S, rfl⟩, hg⟩ => by
          refine' exists_imp_exists (fun k hk => _) (hc1 S.2 ⟨g, hg⟩)
          rwa [Subtype.ext_iff, coe_pow] at hk⊢, fun M hM g hg => ⟨M, ⟨⟨M, hM⟩, rfl⟩, hg⟩⟩)
      P hP)
    fun Q ⟨hQ1, hQ2, hQ3⟩ => ⟨⟨Q, hQ1, hQ3⟩, hQ2⟩

instance Sylow.nonempty : Nonempty (Sylow p G) :=
  nonempty_of_exists IsPGroup.of_bot.exists_le_sylow

noncomputable instance Sylow.inhabited : Inhabited (Sylow p G) :=
  Classical.inhabitedOfNonempty Sylow.nonempty

theorem Sylow.exists_comap_eq_of_ker_is_p_group {H : Type _} [Groupₓ H] (P : Sylow p H) {f : H →* G}
    (hf : IsPGroup p f.ker) : ∃ Q : Sylow p G, (Q : Subgroup G).comap f = P :=
  exists_imp_exists (fun Q hQ => P.3 (Q.2.comap_of_ker_is_p_group f hf) (map_le_iff_le_comap.mp hQ))
    (P.2.map f).exists_le_sylow

theorem Sylow.exists_comap_eq_of_injective {H : Type _} [Groupₓ H] (P : Sylow p H) {f : H →* G}
    (hf : Function.Injective f) : ∃ Q : Sylow p G, (Q : Subgroup G).comap f = P :=
  P.exists_comap_eq_of_ker_is_p_group (IsPGroup.ker_is_p_group_of_injective hf)

theorem Sylow.exists_comap_subtype_eq {H : Subgroup G} (P : Sylow p H) :
    ∃ Q : Sylow p G, (Q : Subgroup G).comap H.Subtype = P :=
  P.exists_comap_eq_of_injective Subtype.coe_injective

/-- If the kernel of `f : H →* G` is a `p`-group,
  then `fintype (sylow p G)` implies `fintype (sylow p H)`. -/
noncomputable def Sylow.fintypeOfKerIsPGroup {H : Type _} [Groupₓ H] {f : H →* G} (hf : IsPGroup p f.ker)
    [Fintype (Sylow p G)] : Fintype (Sylow p H) :=
  let h_exists := fun P : Sylow p H => P.exists_comap_eq_of_ker_is_p_group hf
  let g : Sylow p H → Sylow p G := fun P => Classical.some (h_exists P)
  let hg : ∀ P : Sylow p H, (g P).1.comap f = P := fun P => Classical.some_spec (h_exists P)
  Fintype.ofInjective g fun P Q h =>
    Sylow.ext
      (by
        simp only [hg, ← h])

/-- If `f : H →* G` is injective, then `fintype (sylow p G)` implies `fintype (sylow p H)`. -/
noncomputable def Sylow.fintypeOfInjective {H : Type _} [Groupₓ H] {f : H →* G} (hf : Function.Injective f)
    [Fintype (Sylow p G)] : Fintype (Sylow p H) :=
  Sylow.fintypeOfKerIsPGroup (IsPGroup.ker_is_p_group_of_injective hf)

/-- If `H` is a subgroup of `G`, then `fintype (sylow p G)` implies `fintype (sylow p H)`. -/
noncomputable instance (H : Subgroup G) [Fintype (Sylow p G)] : Fintype (Sylow p H) :=
  Sylow.fintypeOfInjective (show Function.Injective H.Subtype from Subtype.coe_injective)

open Pointwise

/-- `subgroup.pointwise_mul_action` preserves Sylow subgroups. -/
instance Sylow.pointwiseMulAction {α : Type _} [Groupₓ α] [MulDistribMulAction α G] : MulAction α (Sylow p G) where
  smul := fun g P =>
    ⟨g • P, P.2.map _, fun Q hQ hS =>
      inv_smul_eq_iff.mp
        (P.3 (hQ.map _) fun s hs =>
          (congr_arg (· ∈ g⁻¹ • Q) (inv_smul_smul g s)).mp
            (smul_mem_pointwise_smul (g • s) g⁻¹ Q (hS (smul_mem_pointwise_smul s g P hs))))⟩
  one_smul := fun P => Sylow.ext (one_smul α P)
  mul_smul := fun g h P => Sylow.ext (mul_smul g h P)

theorem Sylow.pointwise_smul_def {α : Type _} [Groupₓ α] [MulDistribMulAction α G] {g : α} {P : Sylow p G} :
    ↑(g • P) = g • (P : Subgroup G) :=
  rfl

instance Sylow.mulAction : MulAction G (Sylow p G) :=
  compHom _ MulAut.conj

theorem Sylow.smul_def {g : G} {P : Sylow p G} : g • P = MulAut.conj g • P :=
  rfl

theorem Sylow.coe_subgroup_smul {g : G} {P : Sylow p G} : ↑(g • P) = MulAut.conj g • (P : Subgroup G) :=
  rfl

theorem Sylow.coe_smul {g : G} {P : Sylow p G} : ↑(g • P) = MulAut.conj g • (P : Set G) :=
  rfl

theorem Sylow.smul_le {P : Sylow p G} {H : Subgroup G} (hP : ↑P ≤ H) (h : H) : ↑(h • P) ≤ H :=
  Subgroup.conj_smul_le_of_le hP h

theorem Sylow.smul_subtype {P : Sylow p G} {H : Subgroup G} (hP : ↑P ≤ H) (h : H) :
    h • P.Subtype hP = (h • P).Subtype (Sylow.smul_le hP h) :=
  Sylow.ext (Subgroup.conj_smul_subgroup_of hP h)

theorem Sylow.smul_eq_iff_mem_normalizer {g : G} {P : Sylow p G} : g • P = P ↔ g ∈ (P : Subgroup G).normalizer := by
  rw [eq_comm, SetLike.ext_iff, ← inv_mem_iff, mem_normalizer_iff, inv_invₓ]
  exact
    forall_congrₓ fun h =>
      iff_congr Iff.rfl
        ⟨fun ⟨a, b, c⟩ => (congr_arg _ c).mp ((congr_arg (· ∈ P.1) (MulAut.inv_apply_self G (MulAut.conj g) a)).mpr b),
          fun hh => ⟨(MulAut.conj g)⁻¹ h, hh, MulAut.apply_inv_self G (MulAut.conj g) h⟩⟩

theorem Sylow.smul_eq_of_normal {g : G} {P : Sylow p G} [h : (P : Subgroup G).Normal] : g • P = P := by
  simp only [← Sylow.smul_eq_iff_mem_normalizer, ← normalizer_eq_top.mpr h, ← mem_top]

theorem Subgroup.sylow_mem_fixed_points_iff (H : Subgroup G) {P : Sylow p G} :
    P ∈ FixedPoints H (Sylow p G) ↔ H ≤ (P : Subgroup G).normalizer := by
  simp_rw [SetLike.le_def, ← Sylow.smul_eq_iff_mem_normalizer] <;> exact Subtype.forall

theorem IsPGroup.inf_normalizer_sylow {P : Subgroup G} (hP : IsPGroup p P) (Q : Sylow p G) :
    P⊓(Q : Subgroup G).normalizer = P⊓Q :=
  le_antisymmₓ
    (le_inf inf_le_left (sup_eq_right.mp (Q.3 (hP.to_inf_left.to_sup_of_normal_right' Q.2 inf_le_right) le_sup_right)))
    (inf_le_inf_left P le_normalizer)

theorem IsPGroup.sylow_mem_fixed_points_iff {P : Subgroup G} (hP : IsPGroup p P) {Q : Sylow p G} :
    Q ∈ FixedPoints P (Sylow p G) ↔ P ≤ Q := by
  rw [P.sylow_mem_fixed_points_iff, ← inf_eq_left, hP.inf_normalizer_sylow, inf_eq_left]

/-- A generalization of **Sylow's second theorem**.
  If the number of Sylow `p`-subgroups is finite, then all Sylow `p`-subgroups are conjugate. -/
instance [hp : Fact p.Prime] [Fintype (Sylow p G)] : IsPretransitive G (Sylow p G) :=
  ⟨fun P Q => by
    classical
    have H := fun {R : Sylow p G} {S : orbit G P} =>
      calc
        S ∈ fixed_points R (orbit G P) ↔ S.1 ∈ fixed_points R (Sylow p G) := forall_congrₓ fun a => Subtype.ext_iff
        _ ↔ R.1 ≤ S := R.2.sylow_mem_fixed_points_iff
        _ ↔ S.1.1 = R := ⟨fun h => R.3 S.1.2 h, ge_of_eq⟩
        
    suffices Set.Nonempty (fixed_points Q (orbit G P)) by
      exact Exists.elim this fun R hR => (congr_arg _ (Sylow.ext (H.mp hR))).mp R.2
    apply Q.2.nonempty_fixed_point_of_prime_not_dvd_card
    refine' fun h => hp.out.not_dvd_one (nat.modeq_zero_iff_dvd.mp _)
    calc 1 = card (fixed_points P (orbit G P)) := _ _ ≡ card (orbit G P) [MOD p] :=
        (P.2.card_modeq_card_fixed_points (orbit G P)).symm _ ≡ 0 [MOD p] := nat.modeq_zero_iff_dvd.mpr h
    rw [← Set.card_singleton (⟨P, mem_orbit_self P⟩ : orbit G P)]
    refine' card_congr' (congr_arg _ (Eq.symm _))
    rw [Set.eq_singleton_iff_unique_mem]
    exact ⟨H.mpr rfl, fun R h => Subtype.ext (Sylow.ext (H.mp h))⟩⟩

variable (p) (G)

/-- A generalization of **Sylow's third theorem**.
  If the number of Sylow `p`-subgroups is finite, then it is congruent to `1` modulo `p`. -/
theorem card_sylow_modeq_one [Fact p.Prime] [Fintype (Sylow p G)] : card (Sylow p G) ≡ 1 [MOD p] := by
  refine' sylow.nonempty.elim fun P : Sylow p G => _
  have : fixed_points P.1 (Sylow p G) = {P} :=
    Set.ext fun Q : Sylow p G =>
      calc
        Q ∈ fixed_points P (Sylow p G) ↔ P.1 ≤ Q := P.2.sylow_mem_fixed_points_iff
        _ ↔ Q.1 = P.1 := ⟨P.3 Q.2, ge_of_eq⟩
        _ ↔ Q ∈ {P} := sylow.ext_iff.symm.trans set.mem_singleton_iff.symm
        
  have : Fintype (fixed_points P.1 (Sylow p G)) := by
    rw [this]
    infer_instance
  have : card (fixed_points P.1 (Sylow p G)) = 1 := by
    simp [← this]
  exact
    (P.2.card_modeq_card_fixed_points (Sylow p G)).trans
      (by
        rw [this])

theorem not_dvd_card_sylow [hp : Fact p.Prime] [Fintype (Sylow p G)] : ¬p ∣ card (Sylow p G) := fun h =>
  hp.1.ne_one
    (Nat.dvd_one.mp
      ((Nat.modeq_iff_dvd' zero_le_one).mp ((Nat.modeq_zero_iff_dvd.mpr h).symm.trans (card_sylow_modeq_one p G))))

variable {p} {G}

/-- Sylow subgroups are isomorphic -/
def Sylow.equivSmul (P : Sylow p G) (g : G) : P ≃* (g • P : Sylow p G) :=
  equivSmul (MulAut.conj g) ↑P

/-- Sylow subgroups are isomorphic -/
noncomputable def Sylow.equiv [Fact p.Prime] [Fintype (Sylow p G)] (P Q : Sylow p G) : P ≃* Q := by
  rw [← Classical.some_spec (exists_smul_eq G P Q)]
  exact P.equiv_smul (Classical.some (exists_smul_eq G P Q))

@[simp]
theorem Sylow.orbit_eq_top [Fact p.Prime] [Fintype (Sylow p G)] (P : Sylow p G) : Orbit G P = ⊤ :=
  top_le_iff.mp fun Q hQ => exists_smul_eq G P Q

theorem Sylow.stabilizer_eq_normalizer (P : Sylow p G) : stabilizer G P = (P : Subgroup G).normalizer :=
  ext fun g => Sylow.smul_eq_iff_mem_normalizer

/-- Sylow `p`-subgroups are in bijection with cosets of the normalizer of a Sylow `p`-subgroup -/
noncomputable def Sylow.equivQuotientNormalizer [Fact p.Prime] [Fintype (Sylow p G)] (P : Sylow p G) :
    Sylow p G ≃ G ⧸ (P : Subgroup G).normalizer :=
  calc
    Sylow p G ≃ (⊤ : Set (Sylow p G)) := (Equivₓ.Set.univ (Sylow p G)).symm
    _ ≃ Orbit G P := by
      rw [P.orbit_eq_top]
    _ ≃ G ⧸ stabilizer G P := orbitEquivQuotientStabilizer G P
    _ ≃ G ⧸ (P : Subgroup G).normalizer := by
      rw [P.stabilizer_eq_normalizer]
    

noncomputable instance [Fact p.Prime] [Fintype (Sylow p G)] (P : Sylow p G) :
    Fintype (G ⧸ (P : Subgroup G).normalizer) :=
  ofEquiv (Sylow p G) P.equivQuotientNormalizer

theorem card_sylow_eq_card_quotient_normalizer [Fact p.Prime] [Fintype (Sylow p G)] (P : Sylow p G) :
    card (Sylow p G) = card (G ⧸ (P : Subgroup G).normalizer) :=
  card_congr P.equivQuotientNormalizer

theorem card_sylow_eq_index_normalizer [Fact p.Prime] [Fintype (Sylow p G)] (P : Sylow p G) :
    card (Sylow p G) = (P : Subgroup G).normalizer.index :=
  (card_sylow_eq_card_quotient_normalizer P).trans (P : Subgroup G).normalizer.index_eq_card.symm

theorem card_sylow_dvd_index [Fact p.Prime] [Fintype (Sylow p G)] (P : Sylow p G) :
    card (Sylow p G) ∣ (P : Subgroup G).index :=
  ((congr_arg _ (card_sylow_eq_index_normalizer P)).mp dvd_rfl).trans (index_dvd_of_le le_normalizer)

theorem not_dvd_index_sylow' [hp : Fact p.Prime] (P : Sylow p G) [(P : Subgroup G).Normal]
    (hP : (P : Subgroup G).index ≠ 0) : ¬p ∣ (P : Subgroup G).index := by
  intro h
  have : Fintype (G ⧸ (P : Subgroup G)) := fintype_of_index_ne_zero hP
  rw [index_eq_card] at h
  obtain ⟨x, hx⟩ := exists_prime_order_of_dvd_card p h
  have h := IsPGroup.of_card ((order_eq_card_zpowers.symm.trans hx).trans (pow_oneₓ p).symm)
  let Q := (zpowers x).comap (QuotientGroup.mk' (P : Subgroup G))
  have hQ : IsPGroup p Q := by
    apply h.comap_of_ker_is_p_group
    rw [QuotientGroup.ker_mk]
    exact P.2
  replace hp := mt order_of_eq_one_iff.mpr (ne_of_eq_of_ne hx hp.1.ne_one)
  rw [← zpowers_eq_bot, ← Ne, ← bot_lt_iff_ne_bot, ← comap_lt_comap_of_surjective (QuotientGroup.mk'_surjective _),
    MonoidHom.comap_bot, QuotientGroup.ker_mk] at hp
  exact hp.ne' (P.3 hQ hp.le)

theorem not_dvd_index_sylow [hp : Fact p.Prime] [Fintype (Sylow p G)] (P : Sylow p G)
    (hP : relindex ↑P (P : Subgroup G).normalizer ≠ 0) : ¬p ∣ (P : Subgroup G).index := by
  rw [← relindex_mul_index le_normalizer, ← card_sylow_eq_index_normalizer]
  have : (P.subtype le_normalizer : Subgroup (P : Subgroup G).normalizer).Normal := Subgroup.normal_in_normalizer
  replace hP := not_dvd_index_sylow' (P.subtype le_normalizer) hP
  exact hp.1.not_dvd_mul hP (not_dvd_card_sylow p G)

/-- Frattini's Argument: If `N` is a normal subgroup of `G`, and if `P` is a Sylow `p`-subgroup
  of `N`, then `N_G(P) ⊔ N = G`. -/
theorem Sylow.normalizer_sup_eq_top {p : ℕ} [Fact p.Prime] {N : Subgroup G} [N.Normal] [Fintype (Sylow p N)]
    (P : Sylow p N) : ((↑P : Subgroup N).map N.Subtype).normalizer⊔N = ⊤ := by
  refine' top_le_iff.mp fun g hg => _
  obtain ⟨n, hn⟩ := exists_smul_eq N ((MulAut.conjNormal g : MulAut N) • P) P
  rw [← inv_mul_cancel_leftₓ (↑n) g, sup_comm]
  apply mul_mem_sup (N.inv_mem n.2)
  rw [Sylow.smul_def, ← mul_smul, ← MulAut.conj_normal_coe, ← mul_aut.conj_normal.map_mul, Sylow.ext_iff,
    Sylow.pointwise_smul_def, pointwise_smul_def] at hn
  refine' fun x =>
    (mem_map_iff_mem
            (show Function.Injective (MulAut.conj (↑n * g)).toMonoidHom from
              (MulAut.conj (↑n * g)).Injective)).symm.trans
      _
  rw [map_map, ← congr_arg (map N.subtype) hn, map_map]
  rfl

end InfiniteSylow

open Equivₓ Equivₓ.Perm Finset Function List QuotientGroup

open BigOperators

universe u v w

variable {G : Type u} {α : Type v} {β : Type w} [Groupₓ G]

attribute [local instance] Subtype.fintype setFintype Classical.propDecidable

theorem QuotientGroup.card_preimage_mk [Fintype G] (s : Subgroup G) (t : Set (G ⧸ s)) :
    Fintype.card (QuotientGroup.mk ⁻¹' t) = Fintype.card s * Fintype.card t := by
  rw [← Fintype.card_prod, Fintype.card_congr (preimage_mk_equiv_subgroup_times_set _ _)]

namespace Sylow

open Subgroup Submonoid MulAction

theorem mem_fixed_points_mul_left_cosets_iff_mem_normalizer {H : Subgroup G} [Fintype ((H : Set G) : Type u)] {x : G} :
    (x : G ⧸ H) ∈ FixedPoints H (G ⧸ H) ↔ x ∈ normalizer H :=
  ⟨fun hx =>
    have ha : ∀ {y : G ⧸ H}, y ∈ Orbit H (x : G ⧸ H) → y = x := fun _ => (mem_fixed_points' _).1 hx _
    inv_mem_iff.1
      (@mem_normalizer_fintype _ _ _ _inst_2 _ fun n (hn : n ∈ H) =>
        have : (n⁻¹ * x)⁻¹ * x ∈ H := QuotientGroup.eq.1 (ha (mem_orbit _ ⟨n⁻¹, H.inv_mem hn⟩))
        show _ ∈ H by
          rw [mul_inv_rev, inv_invₓ] at this
          convert this
          rw [inv_invₓ]),
    fun hx : ∀ n : G, n ∈ H ↔ x * n * x⁻¹ ∈ H =>
    (mem_fixed_points' _).2 fun y =>
      (Quotientₓ.induction_on' y) fun y hy =>
        QuotientGroup.eq.2
          (let ⟨⟨b, hb₁⟩, hb₂⟩ := hy
          have hb₂ : (b * x)⁻¹ * y ∈ H := QuotientGroup.eq.1 hb₂
          inv_mem_iff.1 <|
            (hx _).2 <|
              (mul_mem_cancel_left (inv_mem hb₁)).1 <| by
                rw [hx] at hb₂ <;> simpa [← mul_inv_rev, ← mul_assoc] using hb₂)⟩

def fixedPointsMulLeftCosetsEquivQuotient (H : Subgroup G) [Fintype (H : Set G)] :
    MulAction.FixedPoints H (G ⧸ H) ≃ normalizer H ⧸ Subgroup.comap ((normalizer H).Subtype : normalizer H →* G) H :=
  @subtypeQuotientEquivQuotientSubtype G (normalizer H : Set G) (id _) (id _) (FixedPoints _ _)
    (fun a => (@mem_fixed_points_mul_left_cosets_iff_mem_normalizer _ _ _ _inst_2 _).symm)
    (by
      intros
      rw [setoidHasEquiv]
      simp only [← left_rel_apply]
      rfl)

/-- If `H` is a `p`-subgroup of `G`, then the index of `H` inside its normalizer is congruent
  mod `p` to the index of `H`.  -/
theorem card_quotient_normalizer_modeq_card_quotient [Fintype G] {p : ℕ} {n : ℕ} [hp : Fact p.Prime] {H : Subgroup G}
    (hH : Fintype.card H = p ^ n) :
    card (normalizer H ⧸ Subgroup.comap ((normalizer H).Subtype : normalizer H →* G) H) ≡ card (G ⧸ H) [MOD p] := by
  rw [← Fintype.card_congr (fixed_points_mul_left_cosets_equiv_quotient H)]
  exact ((IsPGroup.of_card hH).card_modeq_card_fixed_points _).symm

/-- If `H` is a subgroup of `G` of cardinality `p ^ n`, then the cardinality of the
  normalizer of `H` is congruent mod `p ^ (n + 1)` to the cardinality of `G`.  -/
theorem card_normalizer_modeq_card [Fintype G] {p : ℕ} {n : ℕ} [hp : Fact p.Prime] {H : Subgroup G}
    (hH : Fintype.card H = p ^ n) : card (normalizer H) ≡ card G [MOD p ^ (n + 1)] := by
  have : Subgroup.comap ((normalizer H).Subtype : normalizer H →* G) H ≃ H :=
    Set.BijOn.equiv (normalizer H).Subtype
      ⟨fun _ => id, fun _ _ _ _ h => Subtype.val_injective h, fun x hx => ⟨⟨x, le_normalizer hx⟩, hx, rfl⟩⟩
  rw [card_eq_card_quotient_mul_card_subgroup H,
    card_eq_card_quotient_mul_card_subgroup (Subgroup.comap ((normalizer H).Subtype : normalizer H →* G) H),
    Fintype.card_congr this, hH, pow_succₓ]
  exact (card_quotient_normalizer_modeq_card_quotient hH).mul_right' _

/-- If `H` is a `p`-subgroup but not a Sylow `p`-subgroup, then `p` divides the
  index of `H` inside its normalizer. -/
theorem prime_dvd_card_quotient_normalizer [Fintype G] {p : ℕ} {n : ℕ} [hp : Fact p.Prime] (hdvd : p ^ (n + 1) ∣ card G)
    {H : Subgroup G} (hH : Fintype.card H = p ^ n) :
    p ∣ card (normalizer H ⧸ Subgroup.comap ((normalizer H).Subtype : normalizer H →* G) H) :=
  let ⟨s, hs⟩ := exists_eq_mul_left_of_dvd hdvd
  have hcard : card (G ⧸ H) = s * p :=
    (Nat.mul_left_inj (show card H > 0 from Fintype.card_pos_iff.2 ⟨⟨1, H.one_mem⟩⟩)).1
      (by
        rwa [← card_eq_card_quotient_mul_card_subgroup H, hH, hs, pow_succ'ₓ, mul_assoc, mul_comm p])
  have hm : s * p % p = card (normalizer H ⧸ Subgroup.comap ((normalizer H).Subtype : normalizer H →* G) H) % p :=
    hcard ▸ (card_quotient_normalizer_modeq_card_quotient hH).symm
  Nat.dvd_of_mod_eq_zeroₓ
    (by
      rwa [Nat.mod_eq_zero_of_dvdₓ (dvd_mul_left _ _), eq_comm] at hm)

/-- If `H` is a `p`-subgroup but not a Sylow `p`-subgroup of cardinality `p ^ n`,
  then `p ^ (n + 1)` divides the cardinality of the normalizer of `H`. -/
theorem prime_pow_dvd_card_normalizer [Fintype G] {p : ℕ} {n : ℕ} [hp : Fact p.Prime] (hdvd : p ^ (n + 1) ∣ card G)
    {H : Subgroup G} (hH : Fintype.card H = p ^ n) : p ^ (n + 1) ∣ card (normalizer H) :=
  Nat.modeq_zero_iff_dvd.1 ((card_normalizer_modeq_card hH).trans hdvd.modeq_zero_nat)

/-- If `H` is a subgroup of `G` of cardinality `p ^ n`,
  then `H` is contained in a subgroup of cardinality `p ^ (n + 1)`
  if `p ^ (n + 1)` divides the cardinality of `G` -/
theorem exists_subgroup_card_pow_succ [Fintype G] {p : ℕ} {n : ℕ} [hp : Fact p.Prime] (hdvd : p ^ (n + 1) ∣ card G)
    {H : Subgroup G} (hH : Fintype.card H = p ^ n) : ∃ K : Subgroup G, Fintype.card K = p ^ (n + 1) ∧ H ≤ K :=
  let ⟨s, hs⟩ := exists_eq_mul_left_of_dvd hdvd
  have hcard : card (G ⧸ H) = s * p :=
    (Nat.mul_left_inj (show card H > 0 from Fintype.card_pos_iff.2 ⟨⟨1, H.one_mem⟩⟩)).1
      (by
        rwa [← card_eq_card_quotient_mul_card_subgroup H, hH, hs, pow_succ'ₓ, mul_assoc, mul_comm p])
  have hm : s * p % p = card (normalizer H ⧸ Subgroup.comap (normalizer H).Subtype H) % p :=
    card_congr (fixedPointsMulLeftCosetsEquivQuotient H) ▸ hcard ▸ (IsPGroup.of_card hH).card_modeq_card_fixed_points _
  have hm' : p ∣ card (normalizer H ⧸ Subgroup.comap (normalizer H).Subtype H) :=
    Nat.dvd_of_mod_eq_zeroₓ
      (by
        rwa [Nat.mod_eq_zero_of_dvdₓ (dvd_mul_left _ _), eq_comm] at hm)
  let ⟨x, hx⟩ := @exists_prime_order_of_dvd_card _ (QuotientGroup.Quotient.group _) _ _ hp hm'
  have hequiv : H ≃ Subgroup.comap ((normalizer H).Subtype : normalizer H →* G) H :=
    ⟨fun a => ⟨⟨a.1, le_normalizer a.2⟩, a.2⟩, fun a => ⟨a.1.1, a.2⟩, fun ⟨_, _⟩ => rfl, fun ⟨⟨_, _⟩, _⟩ => rfl⟩
  ⟨Subgroup.map (normalizer H).Subtype (Subgroup.comap (QuotientGroup.mk' (comap H.normalizer.Subtype H)) (zpowers x)),
    by
    show
      card ↥(map H.normalizer.subtype (comap (mk' (comap H.normalizer.subtype H)) (Subgroup.zpowers x))) = p ^ (n + 1)
    suffices
      card ↥(Subtype.val '' (Subgroup.comap (mk' (comap H.normalizer.subtype H)) (zpowers x) : Set ↥H.normalizer)) =
        p ^ (n + 1)
      by
      convert this using 2
    rw
      [Set.card_image_of_injective (Subgroup.comap (mk' (comap H.normalizer.subtype H)) (zpowers x) : Set H.normalizer)
        Subtype.val_injective,
      pow_succ'ₓ, ← hH, Fintype.card_congr hequiv, ← hx, order_eq_card_zpowers, ← Fintype.card_prod]
    exact @Fintype.card_congr _ _ (id _) (id _) (preimage_mk_equiv_subgroup_times_set _ _), by
    intro y hy
    simp only [← exists_prop, ← Subgroup.coe_subtype, ← mk'_apply, ← Subgroup.mem_map, ← Subgroup.mem_comap]
    refine' ⟨⟨y, le_normalizer hy⟩, ⟨0, _⟩, rfl⟩
    rw [zpow_zero, eq_comm, QuotientGroup.eq_one_iff]
    simpa using hy⟩

/-- If `H` is a subgroup of `G` of cardinality `p ^ n`,
  then `H` is contained in a subgroup of cardinality `p ^ m`
  if `n ≤ m` and `p ^ m` divides the cardinality of `G` -/
theorem exists_subgroup_card_pow_prime_le [Fintype G] (p : ℕ) :
    ∀ {n m : ℕ} [hp : Fact p.Prime] (hdvd : p ^ m ∣ card G) (H : Subgroup G) (hH : card H = p ^ n) (hnm : n ≤ m),
      ∃ K : Subgroup G, card K = p ^ m ∧ H ≤ K
  | n, m => fun hp hdvd H hH hnm =>
    (lt_or_eq_of_leₓ hnm).elim
      (fun hnm : n < m =>
        have h0m : 0 < m := lt_of_le_of_ltₓ n.zero_le hnm
        have wf : m - 1 < m := Nat.sub_ltₓ h0m zero_lt_one
        have hnm1 : n ≤ m - 1 := le_tsub_of_add_le_right hnm
        let ⟨K, hK⟩ :=
          @exists_subgroup_card_pow_prime_le n (m - 1) hp (Nat.pow_dvd_of_le_of_pow_dvd tsub_le_self hdvd) H hH hnm1
        have hdvd' : p ^ (m - 1 + 1) ∣ card G := by
          rwa [tsub_add_cancel_of_le h0m.nat_succ_le]
        let ⟨K', hK'⟩ := @exists_subgroup_card_pow_succ _ _ _ _ _ hp hdvd' K hK.1
        ⟨K', by
          rw [hK'.1, tsub_add_cancel_of_le h0m.nat_succ_le], le_transₓ hK.2 hK'.2⟩)
      fun hnm : n = m =>
      ⟨H, by
        simp [← hH, ← hnm]⟩

/-- A generalisation of **Sylow's first theorem**. If `p ^ n` divides
  the cardinality of `G`, then there is a subgroup of cardinality `p ^ n` -/
theorem exists_subgroup_card_pow_prime [Fintype G] (p : ℕ) {n : ℕ} [Fact p.Prime] (hdvd : p ^ n ∣ card G) :
    ∃ K : Subgroup G, Fintype.card K = p ^ n :=
  let ⟨K, hK⟩ :=
    exists_subgroup_card_pow_prime_le p hdvd ⊥
      (by
        simp )
      n.zero_le
  ⟨K, hK.1⟩

theorem pow_dvd_card_of_pow_dvd_card [Fintype G] {p n : ℕ} [hp : Fact p.Prime] (P : Sylow p G) (hdvd : p ^ n ∣ card G) :
    p ^ n ∣ card P :=
  (hp.1.coprime_pow_of_not_dvd (not_dvd_index_sylow P index_ne_zero_of_fintype)).symm.dvd_of_dvd_mul_left
    ((index_mul_card P.1).symm ▸ hdvd)

theorem dvd_card_of_dvd_card [Fintype G] {p : ℕ} [Fact p.Prime] (P : Sylow p G) (hdvd : p ∣ card G) : p ∣ card P := by
  rw [← pow_oneₓ p] at hdvd
  have key := P.pow_dvd_card_of_pow_dvd_card hdvd
  rwa [pow_oneₓ] at key

/-- Sylow subgroups are Hall subgroups. -/
theorem card_coprime_index [Fintype G] {p : ℕ} [hp : Fact p.Prime] (P : Sylow p G) :
    (card P).Coprime (index (P : Subgroup G)) :=
  let ⟨n, hn⟩ := IsPGroup.iff_card.mp P.2
  hn.symm ▸ (hp.1.coprime_pow_of_not_dvd (not_dvd_index_sylow P index_ne_zero_of_fintype)).symm

theorem ne_bot_of_dvd_card [Fintype G] {p : ℕ} [hp : Fact p.Prime] (P : Sylow p G) (hdvd : p ∣ card G) :
    (P : Subgroup G) ≠ ⊥ := by
  refine' fun h => hp.out.not_dvd_one _
  have key : p ∣ card (P : Subgroup G) := P.dvd_card_of_dvd_card hdvd
  rwa [h, card_bot] at key

/-- The cardinality of a Sylow group is `p ^ n`
 where `n` is the multiplicity of `p` in the group order. -/
theorem card_eq_multiplicity [Fintype G] {p : ℕ} [hp : Fact p.Prime] (P : Sylow p G) :
    card P = p ^ Nat.factorization (card G) p := by
  obtain ⟨n, heq : card P = _⟩ := is_p_group.iff_card.mp P.is_p_group'
  refine' Nat.dvd_antisymm _ (P.pow_dvd_card_of_pow_dvd_card (Nat.pow_factorization_dvd _ p))
  rw [HEq, ← hp.out.pow_dvd_iff_dvd_pow_factorization (show card G ≠ 0 from card_ne_zero), ← HEq]
  exact P.1.card_subgroup_dvd_card

theorem subsingleton_of_normal {p : ℕ} [Fact p.Prime] [Fintype (Sylow p G)] (P : Sylow p G)
    (h : (P : Subgroup G).Normal) : Subsingleton (Sylow p G) := by
  apply Subsingleton.intro
  intro Q R
  obtain ⟨x, h1⟩ := exists_smul_eq G P Q
  obtain ⟨x, h2⟩ := exists_smul_eq G P R
  rw [Sylow.smul_eq_of_normal] at h1 h2
  rw [← h1, ← h2]

section Pointwise

open Pointwise

theorem characteristic_of_normal {p : ℕ} [Fact p.Prime] [Fintype (Sylow p G)] (P : Sylow p G)
    (h : (P : Subgroup G).Normal) : (P : Subgroup G).Characteristic := by
  have := Sylow.subsingleton_of_normal P h
  rw [characteristic_iff_map_eq]
  intro Φ
  show (Φ • P).toSubgroup = P.to_subgroup
  congr

end Pointwise

theorem normal_of_normalizer_normal {p : ℕ} [Fact p.Prime] [Fintype (Sylow p G)] (P : Sylow p G)
    (hn : (↑P : Subgroup G).normalizer.Normal) : (↑P : Subgroup G).Normal := by
  rw [← normalizer_eq_top, ← normalizer_sup_eq_top (P.subtype le_normalizer), coeSubtype,
    map_comap_eq_self (le_normalizer.trans (ge_of_eq (subtype_range _))), sup_idem]

@[simp]
theorem normalizer_normalizer {p : ℕ} [Fact p.Prime] [Fintype (Sylow p G)] (P : Sylow p G) :
    (↑P : Subgroup G).normalizer.normalizer = (↑P : Subgroup G).normalizer := by
  have := normal_of_normalizer_normal (P.subtype (le_normalizer.trans le_normalizer))
  simp_rw [← normalizer_eq_top, coeSubtype, ← comap_subtype_normalizer_eq le_normalizer, ←
    comap_subtype_normalizer_eq le_rfl, comap_subtype_self_eq_top] at this
  rw [← subtype_range (P : Subgroup G).normalizer.normalizer, MonoidHom.range_eq_map, ← this rfl]
  exact map_comap_eq_self (le_normalizer.trans (ge_of_eq (subtype_range _)))

theorem normal_of_all_max_subgroups_normal [Fintype G] (hnc : ∀ H : Subgroup G, IsCoatom H → H.Normal) {p : ℕ}
    [Fact p.Prime] [Fintype (Sylow p G)] (P : Sylow p G) : (↑P : Subgroup G).Normal :=
  normalizer_eq_top.mp
    (by
      rcases eq_top_or_exists_le_coatom (↑P : Subgroup G).normalizer with (heq | ⟨K, hK, hNK⟩)
      · exact HEq
        
      · have := hnc _ hK
        have hPK := le_transₓ le_normalizer hNK
        let P' := P.subtype hPK
        exfalso
        apply hK.1
        calc K = (↑P : Subgroup G).normalizer⊔K := by
            rw [sup_eq_right.mpr]
            exact hNK _ = (map K.subtype (↑P' : Subgroup K)).normalizer⊔K := by
            simp [← map_comap_eq_self, ← hPK]_ = ⊤ := normalizer_sup_eq_top P'
        )

theorem normal_of_normalizer_condition (hnc : NormalizerCondition G) {p : ℕ} [Fact p.Prime] [Fintype (Sylow p G)]
    (P : Sylow p G) : (↑P : Subgroup G).Normal :=
  normalizer_eq_top.mp <| normalizer_condition_iff_only_full_group_self_normalizing.mp hnc _ <| normalizer_normalizer _

open BigOperators

/-- If all its sylow groups are normal, then a finite group is isomorphic to the direct product
of these sylow groups.
-/
noncomputable def directProductOfNormal [Fintype G]
    (hn : ∀ {p : ℕ} [Fact p.Prime] (P : Sylow p G), (↑P : Subgroup G).Normal) :
    (∀ p : (card G).factorization.support, ∀ P : Sylow p G, (↑P : Subgroup G)) ≃* G := by
  set ps := (Fintype.card G).factorization.support
  -- “The” sylow group for p
  let P : ∀ p, Sylow p G := default
  have hcomm : Pairwise fun p₁ p₂ : ps => ∀ x y : G, x ∈ P p₁ → y ∈ P p₂ → Commute x y := by
    rintro ⟨p₁, hp₁⟩ ⟨p₂, hp₂⟩ hne
    have hp₁' := Fact.mk (Nat.prime_of_mem_factorization hp₁)
    have hp₂' := Fact.mk (Nat.prime_of_mem_factorization hp₂)
    have hne' : p₁ ≠ p₂ := by
      simpa using hne
    apply Subgroup.commute_of_normal_of_disjoint _ _ (hn (P p₁)) (hn (P p₂))
    apply IsPGroup.disjoint_of_ne p₁ p₂ hne' _ _ (P p₁).is_p_group' (P p₂).is_p_group'
  refine' MulEquiv.trans _ _
  -- There is only one sylow group for each p, so the inner product is trivial
  show (∀ p : ps, ∀ P : Sylow p G, P) ≃* ∀ p : ps, P p
  · -- here we need to help the elaborator with an explicit instantiation
    apply @MulEquiv.piCongrRight ps (fun p => ∀ P : Sylow p G, P) (fun p => P p) _ _
    rintro ⟨p, hp⟩
    have hp' := Fact.mk (Nat.prime_of_mem_factorization hp)
    have := subsingleton_of_normal _ (hn (P p))
    change (∀ P : Sylow p G, P) ≃* P p
    exact MulEquiv.piSubsingleton _ _
    
  show (∀ p : ps, P p) ≃* G
  apply MulEquiv.ofBijective (Subgroup.noncommPiCoprod hcomm)
  apply (bijective_iff_injective_and_card _).mpr
  constructor
  show injective _
  · apply Subgroup.injective_noncomm_pi_coprod_of_independent
    apply independent_of_coprime_order hcomm
    rintro ⟨p₁, hp₁⟩ ⟨p₂, hp₂⟩ hne
    have hp₁' := Fact.mk (Nat.prime_of_mem_factorization hp₁)
    have hp₂' := Fact.mk (Nat.prime_of_mem_factorization hp₂)
    have hne' : p₁ ≠ p₂ := by
      simpa using hne
    apply IsPGroup.coprime_card_of_ne p₁ p₂ hne' _ _ (P p₁).is_p_group' (P p₂).is_p_group'
    
  show card (∀ p : ps, P p) = card G
  · calc card (∀ p : ps, P p) = ∏ p : ps, card ↥(P p) :=
        Fintype.card_pi _ = ∏ p : ps, p.1 ^ (card G).factorization p.1 := by
        congr 1 with ⟨p, hp⟩
        exact
          @card_eq_multiplicity _ _ _ p ⟨Nat.prime_of_mem_factorization hp⟩
            (P p)_ = ∏ p in ps, p ^ (card G).factorization p :=
        Finset.prod_finset_coe (fun p => p ^ (card G).factorization p) _ _ = (card G).factorization.Prod pow :=
        rfl _ = card G := Nat.factorization_prod_pow_eq_self Fintype.card_ne_zero
    

end Sylow

