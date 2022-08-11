/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Mathbin.FieldTheory.Finite.Basic
import Mathbin.Data.Zmod.Basic

/-!
# Lemmas of Gauss and Eisenstein

This file contains code for the proof of the Lemmas of Gauss and Eisenstein
on the Legendre symbol. The main results are `gauss_lemma_aux` and
`eisenstein_lemma_aux`; they are used in `quadratic_reciprocity.lean`
to prove `gauss_lemma` and `eisenstein_lemma`, respectively.
-/


open Function Finset Nat FiniteField Zmod

open BigOperators Nat

namespace Zmod

section Wilson

variable (p : ℕ) [Fact p.Prime]

/-- **Wilson's Lemma**: the product of `1`, ..., `p-1` is `-1` modulo `p`. -/
-- One can probably deduce the following from `finite_field.prod_univ_units_id_eq_neg_one`
@[simp]
theorem wilsons_lemma : ((p - 1)! : Zmod p) = -1 := by
  refine'
    calc
      ((p - 1)! : Zmod p) = ∏ x in Ico 1 (succ (p - 1)), x := by
        rw [← Finset.prod_Ico_id_eq_factorial, prod_nat_cast]
      _ = ∏ x : (Zmod p)ˣ, x := _
      _ = -1 := by
        simp_rw [← Units.coe_hom_apply, ← (Units.coeHom (Zmod p)).map_prod, prod_univ_units_id_eq_neg_one,
          Units.coe_hom_apply, Units.coe_neg, Units.coe_one]
      
  have hp : 0 < p := (Fact.out p.prime).Pos
  symm
  refine' prod_bij (fun a _ => (a : Zmod p).val) _ _ _ _
  · intro a ha
    rw [mem_Ico, ← Nat.succ_subₓ hp, Nat.succ_sub_one]
    constructor
    · apply Nat.pos_of_ne_zeroₓ
      rw [← @val_zero p]
      intro h
      apply Units.ne_zero a (val_injective p h)
      
    · exact val_lt _
      
    
  · intro a ha
    simp only [← cast_id, ← nat_cast_val]
    
  · intro _ _ _ _ h
    rw [Units.ext_iff]
    exact val_injective p h
    
  · intro b hb
    rw [mem_Ico, Nat.succ_le_iff, ← succ_sub hp, succ_sub_one, pos_iff_ne_zero] at hb
    refine' ⟨Units.mk0 b _, Finset.mem_univ _, _⟩
    · intro h
      apply hb.1
      apply_fun val  at h
      simpa only [← val_cast_of_lt hb.right, ← val_zero] using h
      
    · simp only [← val_cast_of_lt hb.right, ← Units.coe_mk0]
      
    

@[simp]
theorem prod_Ico_one_prime : (∏ x in ico 1 p, (x : Zmod p)) = -1 := by
  conv in Ico 1 p => rw [← succ_sub_one p, succ_sub (Fact.out p.prime).Pos]
  rw [← prod_nat_cast, Finset.prod_Ico_id_eq_factorial, wilsons_lemma]

end Wilson

end Zmod

section GaussEisenstein

namespace LegendreSymbol

/-- The image of the map sending a non zero natural number `x ≤ p / 2` to the absolute value
  of the element of interger in the interval `(-p/2, p/2]` congruent to `a * x` mod p is the set
  of non zero natural numbers `x` such that `x ≤ p / 2` -/
theorem Ico_map_val_min_abs_nat_abs_eq_Ico_map_id (p : ℕ) [hp : Fact p.Prime] (a : Zmod p) (hap : a ≠ 0) :
    ((ico 1 (p / 2).succ).1.map fun x => (a * x).valMinAbs.natAbs) = (ico 1 (p / 2).succ).1.map fun a => a := by
  have he : ∀ {x}, x ∈ Ico 1 (p / 2).succ → x ≠ 0 ∧ x ≤ p / 2 := by
    simp (config := { contextual := true })[← Nat.lt_succ_iffₓ, ← Nat.succ_le_iff, ← pos_iff_ne_zero]
  have hep : ∀ {x}, x ∈ Ico 1 (p / 2).succ → x < p := fun x hx =>
    lt_of_le_of_ltₓ (he hx).2
      (Nat.div_lt_selfₓ hp.1.Pos
        (by
          decide))
  have hpe : ∀ {x}, x ∈ Ico 1 (p / 2).succ → ¬p ∣ x := fun x hx hpx =>
    not_lt_of_geₓ (le_of_dvd (Nat.pos_of_ne_zeroₓ (he hx).1) hpx) (hep hx)
  have hmem : ∀ (x : ℕ) (hx : x ∈ Ico 1 (p / 2).succ), (a * x : Zmod p).valMinAbs.natAbs ∈ Ico 1 (p / 2).succ := by
    intro x hx
    simp [← hap, ← CharP.cast_eq_zero_iff (Zmod p) p, ← hpe hx, ← lt_succ_iff, ← succ_le_iff, ← pos_iff_ne_zero, ←
      nat_abs_val_min_abs_le _]
  have hsurj :
    ∀ (b : ℕ) (hb : b ∈ Ico 1 (p / 2).succ), ∃ x ∈ Ico 1 (p / 2).succ, b = (a * x : Zmod p).valMinAbs.natAbs := by
    intro b hb
    refine' ⟨(b / a : Zmod p).valMinAbs.natAbs, mem_Ico.mpr ⟨_, _⟩, _⟩
    · apply Nat.pos_of_ne_zeroₓ
      simp only [← div_eq_mul_inv, ← hap, ← CharP.cast_eq_zero_iff (Zmod p) p, ← hpe hb, ← not_false_iff, ←
        val_min_abs_eq_zero, ← inv_eq_zero, ← Int.nat_abs_eq_zero, ← Ne.def, ← mul_eq_zero, ← or_selfₓ]
      
    · apply lt_succ_of_le
      apply nat_abs_val_min_abs_le
      
    · rw [nat_cast_nat_abs_val_min_abs]
      split_ifs
      · erw [mul_div_cancel' _ hap, val_min_abs_def_pos, val_cast_of_lt (hep hb),
          if_pos (le_of_lt_succ (mem_Ico.1 hb).2), Int.nat_abs_of_nat]
        
      · erw [mul_neg, mul_div_cancel' _ hap, nat_abs_val_min_abs_neg, val_min_abs_def_pos, val_cast_of_lt (hep hb),
          if_pos (le_of_lt_succ (mem_Ico.1 hb).2), Int.nat_abs_of_nat]
        
      
  exact
    Multiset.map_eq_map_of_bij_of_nodup _ _ (Finset.nodup _) (Finset.nodup _)
      (fun x _ => (a * x : Zmod p).valMinAbs.natAbs) hmem (fun _ _ => rfl)
      (inj_on_of_surj_on_of_card_le _ hmem hsurj le_rfl) hsurj

private theorem gauss_lemma_aux₁ (p : ℕ) [Fact p.Prime] [Fact (p % 2 = 1)] {a : ℤ} (hap : (a : Zmod p) ≠ 0) :
    (a ^ (p / 2) * (p / 2)! : Zmod p) =
      -1 ^ ((ico 1 (p / 2).succ).filter fun x : ℕ => ¬(a * x : Zmod p).val ≤ p / 2).card * (p / 2)! :=
  calc
    (a ^ (p / 2) * (p / 2)! : Zmod p) = ∏ x in ico 1 (p / 2).succ, a * x := by
      rw [prod_mul_distrib, ← prod_nat_cast, prod_Ico_id_eq_factorial, prod_const, card_Ico, succ_sub_one] <;> simp
    _ = ∏ x in ico 1 (p / 2).succ, (a * x : Zmod p).val := by
      simp
    _ =
        ∏ x in ico 1 (p / 2).succ,
          (if (a * x : Zmod p).val ≤ p / 2 then 1 else -1) * (a * x : Zmod p).valMinAbs.natAbs :=
      (prod_congr rfl) fun _ _ => by
        simp only [← nat_cast_nat_abs_val_min_abs]
        split_ifs <;> simp
    _ =
        -1 ^ ((ico 1 (p / 2).succ).filter fun x : ℕ => ¬(a * x : Zmod p).val ≤ p / 2).card *
          ∏ x in ico 1 (p / 2).succ, (a * x : Zmod p).valMinAbs.natAbs :=
      by
      have :
        (∏ x in ico 1 (p / 2).succ, if (a * x : Zmod p).val ≤ p / 2 then (1 : Zmod p) else -1) =
          ∏ x in (ico 1 (p / 2).succ).filter fun x : ℕ => ¬(a * x : Zmod p).val ≤ p / 2, -1 :=
        prod_bij_ne_one (fun x _ _ => x)
          (fun x => by
            split_ifs <;> simp_all (config := { contextual := true }))
          (fun _ _ _ _ _ _ => id)
          (fun b h _ =>
            ⟨b, by
              simp_all [-not_leₓ]⟩)
          (by
            intros <;> split_ifs  at * <;> simp_all )
      rw [prod_mul_distrib, this] <;> simp
    _ = -1 ^ ((ico 1 (p / 2).succ).filter fun x : ℕ => ¬(a * x : Zmod p).val ≤ p / 2).card * (p / 2)! := by
      rw [← prod_nat_cast, Finset.prod_eq_multiset_prod, Ico_map_val_min_abs_nat_abs_eq_Ico_map_id p a hap, ←
        Finset.prod_eq_multiset_prod, prod_Ico_id_eq_factorial]
    

theorem gauss_lemma_aux (p : ℕ) [hp : Fact p.Prime] [Fact (p % 2 = 1)] {a : ℤ} (hap : (a : Zmod p) ≠ 0) :
    (a ^ (p / 2) : Zmod p) = -1 ^ ((ico 1 (p / 2).succ).filter fun x : ℕ => p / 2 < (a * x : Zmod p).val).card :=
  (mul_left_inj'
        (show ((p / 2)! : Zmod p) ≠ 0 by
          rw [Ne.def, CharP.cast_eq_zero_iff (Zmod p) p, hp.1.dvd_factorial, not_leₓ] <;>
            exact
              Nat.div_lt_selfₓ hp.1.Pos
                (by
                  decide))).1 <|
    by
    simpa using gauss_lemma_aux₁ p hap

private theorem eisenstein_lemma_aux₁ (p : ℕ) [Fact p.Prime] [hp2 : Fact (p % 2 = 1)] {a : ℕ} (hap : (a : Zmod p) ≠ 0) :
    ((∑ x in ico 1 (p / 2).succ, a * x : ℕ) : Zmod 2) =
      (((ico 1 (p / 2).succ).filter fun x : ℕ => p / 2 < (a * x : Zmod p).val).card + ∑ x in ico 1 (p / 2).succ, x) +
        (∑ x in ico 1 (p / 2).succ, a * x / p : ℕ) :=
  have hp2 : (p : Zmod 2) = (1 : ℕ) := (eq_iff_modeq_nat _).2 hp2.1
  calc
    ((∑ x in ico 1 (p / 2).succ, a * x : ℕ) : Zmod 2) =
        ((∑ x in ico 1 (p / 2).succ, a * x % p + p * (a * x / p) : ℕ) : Zmod 2) :=
      by
      simp only [← mod_add_div]
    _ = (∑ x in ico 1 (p / 2).succ, ((a * x : ℕ) : Zmod p).val : ℕ) + (∑ x in ico 1 (p / 2).succ, a * x / p : ℕ) := by
      simp only [← val_nat_cast] <;>
        simp [← sum_add_distrib, ← mul_sum.symm, ← Nat.cast_addₓ, ← Nat.cast_mulₓ, ← Nat.cast_sum, ← hp2]
    _ = _ :=
      congr_arg2ₓ (· + ·)
        (calc
          ((∑ x in ico 1 (p / 2).succ, ((a * x : ℕ) : Zmod p).val : ℕ) : Zmod 2) =
              ∑ x in ico 1 (p / 2).succ,
                (((a * x : Zmod p).valMinAbs + if (a * x : Zmod p).val ≤ p / 2 then 0 else p : ℤ) : Zmod 2) :=
            by
            simp only [← (val_eq_ite_val_min_abs _).symm] <;> simp [← Nat.cast_sum]
          _ =
              ((ico 1 (p / 2).succ).filter fun x : ℕ => p / 2 < (a * x : Zmod p).val).card +
                (∑ x in ico 1 (p / 2).succ, (a * x : Zmod p).valMinAbs.natAbs : ℕ) :=
            by
            simp [← ite_cast, ← add_commₓ, ← sum_add_distrib, ← Finset.sum_ite, ← hp2, ← Nat.cast_sum]
          _ = _ := by
            rw [Finset.sum_eq_multiset_sum, Ico_map_val_min_abs_nat_abs_eq_Ico_map_id p a hap, ←
                Finset.sum_eq_multiset_sum] <;>
              simp [← Nat.cast_sum]
          )
        rfl
    

theorem eisenstein_lemma_aux (p : ℕ) [Fact p.Prime] [Fact (p % 2 = 1)] {a : ℕ} (ha2 : a % 2 = 1)
    (hap : (a : Zmod p) ≠ 0) :
    ((ico 1 (p / 2).succ).filter fun x : ℕ => p / 2 < (a * x : Zmod p).val).card ≡
      ∑ x in ico 1 (p / 2).succ, x * a / p [MOD 2] :=
  have ha2 : (a : Zmod 2) = (1 : ℕ) := (eq_iff_modeq_nat _).2 ha2
  (eq_iff_modeq_nat 2).1 <|
    sub_eq_zero.1 <| by
      simpa [← add_left_commₓ, ← sub_eq_add_neg, ← finset.mul_sum.symm, ← mul_comm, ← ha2, ← Nat.cast_sum, ←
        add_neg_eq_iff_eq_add.symm, ← neg_eq_self_mod_two, ← add_assocₓ] using Eq.symm (eisenstein_lemma_aux₁ p hap)

theorem div_eq_filter_card {a b c : ℕ} (hb0 : 0 < b) (hc : a / b ≤ c) :
    a / b = ((ico 1 c.succ).filter fun x => x * b ≤ a).card :=
  calc
    a / b = (ico 1 (a / b).succ).card := by
      simp
    _ = ((ico 1 c.succ).filter fun x => x * b ≤ a).card :=
      congr_arg _ <|
        Finset.ext fun x => by
          have : x * b ≤ a → x ≤ c := fun h =>
            le_transₓ
              (by
                rwa [le_div_iff_mul_le hb0])
              hc
          simp [← lt_succ_iff, ← le_div_iff_mul_le hb0] <;> tauto
    

/-- The given sum is the number of integer points in the triangle formed by the diagonal of the
  rectangle `(0, p/2) × (0, q/2)`  -/
private theorem sum_Ico_eq_card_lt {p q : ℕ} :
    (∑ a in ico 1 (p / 2).succ, a * q / p) =
      (((ico 1 (p / 2).succ).product (ico 1 (q / 2).succ)).filter fun x : ℕ × ℕ => x.2 * p ≤ x.1 * q).card :=
  if hp0 : p = 0 then by
    simp [← hp0, ← Finset.ext_iff]
  else
    calc
      (∑ a in ico 1 (p / 2).succ, a * q / p) =
          ∑ a in ico 1 (p / 2).succ, ((ico 1 (q / 2).succ).filter fun x => x * p ≤ a * q).card :=
        (Finset.sum_congr rfl) fun x hx =>
          div_eq_filter_card (Nat.pos_of_ne_zeroₓ hp0)
            (calc
              x * q / p ≤ p / 2 * q / p :=
                Nat.div_le_div_right (mul_le_mul_of_nonneg_right (le_of_lt_succ <| (mem_Ico.mp hx).2) (Nat.zero_leₓ _))
              _ ≤ _ := Nat.div_mul_div_le_div _ _ _
              )
      _ = _ := by
        rw [← card_sigma] <;>
          exact
            card_congr (fun a _ => ⟨a.1, a.2⟩)
              (by
                simp (config := { contextual := true })only [← mem_filter, ← mem_sigma, ← and_selfₓ, ← forall_true_iff,
                  ← mem_product])
              (fun ⟨_, _⟩ ⟨_, _⟩ => by
                simp (config := { contextual := true })only [← Prod.mk.inj_iff, ← eq_self_iff_true, ← and_selfₓ, ←
                  heq_iff_eq, ← forall_true_iff])
              fun ⟨b₁, b₂⟩ h =>
              ⟨⟨b₁, b₂⟩, by
                revert h <;>
                  simp (config := { contextual := true })only [← mem_filter, ← eq_self_iff_true, ← exists_prop_of_true,
                    ← mem_sigma, ← and_selfₓ, ← forall_true_iff, ← mem_product]⟩
      

/-- Each of the sums in this lemma is the cardinality of the set integer points in each of the
  two triangles formed by the diagonal of the rectangle `(0, p/2) × (0, q/2)`. Adding them
  gives the number of points in the rectangle. -/
theorem sum_mul_div_add_sum_mul_div_eq_mul (p q : ℕ) [hp : Fact p.Prime] (hq0 : (q : Zmod p) ≠ 0) :
    ((∑ a in ico 1 (p / 2).succ, a * q / p) + ∑ a in ico 1 (q / 2).succ, a * p / q) = p / 2 * (q / 2) := by
  have hswap :
    (((Ico 1 (q / 2).succ).product (Ico 1 (p / 2).succ)).filter fun x : ℕ × ℕ => x.2 * q ≤ x.1 * p).card =
      (((Ico 1 (p / 2).succ).product (Ico 1 (q / 2).succ)).filter fun x : ℕ × ℕ => x.1 * q ≤ x.2 * p).card :=
    card_congr (fun x _ => Prod.swap x)
      (fun ⟨_, _⟩ => by
        simp (config := { contextual := true })only [← mem_filter, ← and_selfₓ, ← Prod.swap_prod_mk, ← forall_true_iff,
          ← mem_product])
      (fun ⟨_, _⟩ ⟨_, _⟩ => by
        simp (config := { contextual := true })only [← Prod.mk.inj_iff, ← eq_self_iff_true, ← and_selfₓ, ←
          Prod.swap_prod_mk, ← forall_true_iff])
      fun ⟨x₁, x₂⟩ h =>
      ⟨⟨x₂, x₁⟩, by
        revert h <;>
          simp (config := { contextual := true })only [← mem_filter, ← eq_self_iff_true, ← and_selfₓ, ←
            exists_prop_of_true, ← Prod.swap_prod_mk, ← forall_true_iff, ← mem_product]⟩
  have hdisj :
    Disjoint (((Ico 1 (p / 2).succ).product (Ico 1 (q / 2).succ)).filter fun x : ℕ × ℕ => x.2 * p ≤ x.1 * q)
      (((Ico 1 (p / 2).succ).product (Ico 1 (q / 2).succ)).filter fun x : ℕ × ℕ => x.1 * q ≤ x.2 * p) :=
    by
    apply disjoint_filter.2 fun x hx hpq hqp => _
    have hxp : x.1 < p :=
      lt_of_le_of_ltₓ
        (show x.1 ≤ p / 2 by
          simp_all only [← lt_succ_iff, ← mem_Ico, ← mem_product] <;> tauto)
        (Nat.div_lt_selfₓ hp.1.Pos
          (by
            decide))
    have : (x.1 : Zmod p) = 0 := by
      simpa [← hq0] using congr_arg (coe : ℕ → Zmod p) (le_antisymmₓ hpq hqp)
    apply_fun Zmod.val  at this
    rw [val_cast_of_lt hxp, val_zero] at this
    simpa only [← this, ← nonpos_iff_eq_zero, ← mem_Ico, ← one_ne_zero, ← false_andₓ, ← mem_product] using hx
  have hunion :
    ((((Ico 1 (p / 2).succ).product (Ico 1 (q / 2).succ)).filter fun x : ℕ × ℕ => x.2 * p ≤ x.1 * q) ∪
        ((Ico 1 (p / 2).succ).product (Ico 1 (q / 2).succ)).filter fun x : ℕ × ℕ => x.1 * q ≤ x.2 * p) =
      (Ico 1 (p / 2).succ).product (Ico 1 (q / 2).succ) :=
    Finset.ext fun x => by
      have := le_totalₓ (x.2 * p) (x.1 * q) <;>
        simp only [← mem_union, ← mem_filter, ← mem_Ico, ← mem_product] <;> tauto
  rw [sum_Ico_eq_card_lt, sum_Ico_eq_card_lt, hswap, ← card_disjoint_union hdisj, hunion, card_product]
  simp only [← card_Ico, ← tsub_zero, ← succ_sub_succ_eq_sub]

end LegendreSymbol

end GaussEisenstein

