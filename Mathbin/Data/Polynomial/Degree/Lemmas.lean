/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Scott Morrison, Jens Wagemaker
-/
import Mathbin.Data.Polynomial.Eval
import Mathbin.Tactic.IntervalCases

/-!
# Theory of degrees of polynomials

Some of the main results include
- `nat_degree_comp_le` : The degree of the composition is at most the product of degrees

-/


noncomputable section

open Classical Polynomial

open Finsupp Finset

namespace Polynomial

universe u v w

variable {R : Type u} {S : Type v} {ι : Type w} {a b : R} {m n : ℕ}

section Semiringₓ

variable [Semiringₓ R] {p q r : R[X]}

section Degree

theorem nat_degree_comp_le : natDegree (p.comp q) ≤ natDegree p * natDegree q :=
  if h0 : p.comp q = 0 then by
    rw [h0, nat_degree_zero] <;> exact Nat.zero_leₓ _
  else
    WithBot.coe_le_coe.1 <|
      calc
        ↑(natDegree (p.comp q)) = degree (p.comp q) := (degree_eq_nat_degree h0).symm
        _ = _ := congr_arg degree comp_eq_sum_left
        _ ≤ _ := degree_sum_le _ _
        _ ≤ _ :=
          sup_le fun n hn =>
            calc
              degree (c (coeff p n) * q ^ n) ≤ degree (c (coeff p n)) + degree (q ^ n) := degree_mul_le _ _
              _ ≤ natDegree (c (coeff p n)) + n • degree q := add_le_add degree_le_nat_degree (degree_pow_le _ _)
              _ ≤ natDegree (c (coeff p n)) + n • natDegree q :=
                add_le_add_left (nsmul_le_nsmul_of_le_right (@degree_le_nat_degree _ _ q) n) _
              _ = (n * natDegree q : ℕ) := by
                rw [nat_degree_C, WithBot.coe_zero, zero_addₓ, ← WithBot.coe_nsmul, nsmul_eq_mul] <;> simp
              _ ≤ (natDegree p * natDegree q : ℕ) :=
                WithBot.coe_le_coe.2 <|
                  mul_le_mul_of_nonneg_right (le_nat_degree_of_ne_zero (mem_support_iff.1 hn)) (Nat.zero_leₓ _)
              
        

theorem degree_pos_of_root {p : R[X]} (hp : p ≠ 0) (h : IsRoot p a) : 0 < degree p :=
  lt_of_not_geₓ fun hlt => by
    have := eq_C_of_degree_le_zero hlt
    rw [is_root, this, eval_C] at h
    simp only [← h, ← RingHom.map_zero] at this
    exact hp this

theorem nat_degree_le_iff_coeff_eq_zero : p.natDegree ≤ n ↔ ∀ N : ℕ, n < N → p.coeff N = 0 := by
  simp_rw [nat_degree_le_iff_degree_le, degree_le_iff_coeff_zero, WithBot.coe_lt_coe]

theorem nat_degree_add_le_iff_left {n : ℕ} (p q : R[X]) (qn : q.natDegree ≤ n) :
    (p + q).natDegree ≤ n ↔ p.natDegree ≤ n := by
  refine' ⟨fun h => _, fun h => nat_degree_add_le_of_degree_le h qn⟩
  refine' nat_degree_le_iff_coeff_eq_zero.mpr fun m hm => _
  convert nat_degree_le_iff_coeff_eq_zero.mp h m hm using 1
  rw [coeff_add, nat_degree_le_iff_coeff_eq_zero.mp qn _ hm, add_zeroₓ]

theorem nat_degree_add_le_iff_right {n : ℕ} (p q : R[X]) (pn : p.natDegree ≤ n) :
    (p + q).natDegree ≤ n ↔ q.natDegree ≤ n := by
  rw [add_commₓ]
  exact nat_degree_add_le_iff_left _ _ pn

theorem nat_degree_C_mul_le (a : R) (f : R[X]) : (c a * f).natDegree ≤ f.natDegree :=
  calc
    (c a * f).natDegree ≤ (c a).natDegree + f.natDegree := nat_degree_mul_le
    _ = 0 + f.natDegree := by
      rw [nat_degree_C a]
    _ = f.natDegree := zero_addₓ _
    

theorem nat_degree_mul_C_le (f : R[X]) (a : R) : (f * c a).natDegree ≤ f.natDegree :=
  calc
    (f * c a).natDegree ≤ f.natDegree + (c a).natDegree := nat_degree_mul_le
    _ = f.natDegree + 0 := by
      rw [nat_degree_C a]
    _ = f.natDegree := add_zeroₓ _
    

theorem eq_nat_degree_of_le_mem_support (pn : p.natDegree ≤ n) (ns : n ∈ p.Support) : p.natDegree = n :=
  le_antisymmₓ pn (le_nat_degree_of_mem_supp _ ns)

theorem nat_degree_C_mul_eq_of_mul_eq_one {ai : R} (au : ai * a = 1) : (c a * p).natDegree = p.natDegree :=
  le_antisymmₓ (nat_degree_C_mul_le a p)
    (calc
      p.natDegree = (1 * p).natDegree := by
        nth_rw 0[← one_mulₓ p]
      _ = (c ai * (c a * p)).natDegree := by
        rw [← C_1, ← au, RingHom.map_mul, ← mul_assoc]
      _ ≤ (c a * p).natDegree := nat_degree_C_mul_le ai (c a * p)
      )

theorem nat_degree_mul_C_eq_of_mul_eq_one {ai : R} (au : a * ai = 1) : (p * c a).natDegree = p.natDegree :=
  le_antisymmₓ (nat_degree_mul_C_le p a)
    (calc
      p.natDegree = (p * 1).natDegree := by
        nth_rw 0[← mul_oneₓ p]
      _ = (p * c a * c ai).natDegree := by
        rw [← C_1, ← au, RingHom.map_mul, ← mul_assoc]
      _ ≤ (p * c a).natDegree := nat_degree_mul_C_le (p * c a) ai
      )

/-- Although not explicitly stated, the assumptions of lemma `nat_degree_mul_C_eq_of_mul_ne_zero`
force the polynomial `p` to be non-zero, via `p.leading_coeff ≠ 0`.
-/
theorem nat_degree_mul_C_eq_of_mul_ne_zero (h : p.leadingCoeff * a ≠ 0) : (p * c a).natDegree = p.natDegree := by
  refine' eq_nat_degree_of_le_mem_support (nat_degree_mul_C_le p a) _
  refine' mem_support_iff.mpr _
  rwa [coeff_mul_C]

/-- Although not explicitly stated, the assumptions of lemma `nat_degree_C_mul_eq_of_mul_ne_zero`
force the polynomial `p` to be non-zero, via `p.leading_coeff ≠ 0`.
-/
theorem nat_degree_C_mul_eq_of_mul_ne_zero (h : a * p.leadingCoeff ≠ 0) : (c a * p).natDegree = p.natDegree := by
  refine' eq_nat_degree_of_le_mem_support (nat_degree_C_mul_le a p) _
  refine' mem_support_iff.mpr _
  rwa [coeff_C_mul]

theorem nat_degree_add_coeff_mul (f g : R[X]) :
    (f * g).coeff (f.natDegree + g.natDegree) = f.coeff f.natDegree * g.coeff g.natDegree := by
  simp only [← coeff_nat_degree, ← coeff_mul_degree_add_degree]

theorem nat_degree_lt_coeff_mul (h : p.natDegree + q.natDegree < m + n) : (p * q).coeff (m + n) = 0 :=
  coeff_eq_zero_of_nat_degree_lt (nat_degree_mul_le.trans_lt h)

theorem degree_sum_eq_of_disjoint (f : S → R[X]) (s : Finset S)
    (h : Set.Pairwise { i | i ∈ s ∧ f i ≠ 0 } (Ne on degree ∘ f)) : degree (s.Sum f) = s.sup fun i => degree (f i) := by
  induction' s using Finset.induction_on with x s hx IH
  · simp
    
  · simp only [← hx, ← Finset.sum_insert, ← not_false_iff, ← Finset.sup_insert]
    specialize
      IH
        (h.mono fun _ => by
          simp (config := { contextual := true }))
    rcases lt_trichotomyₓ (degree (f x)) (degree (s.sum f)) with (H | H | H)
    · rw [← IH, sup_eq_right.mpr H.le, degree_add_eq_right_of_degree_lt H]
      
    · rcases s.eq_empty_or_nonempty with (rfl | hs)
      · simp
        
      obtain ⟨y, hy, hy'⟩ := Finset.exists_mem_eq_sup s hs fun i => degree (f i)
      rw [IH, hy'] at H
      by_cases' hx0 : f x = 0
      · simp [← hx0, ← IH]
        
      have hy0 : f y ≠ 0 := by
        contrapose! H
        simpa [← H, ← degree_eq_bot] using hx0
      refine' absurd H (h _ _ fun H => hx _)
      · simp [← hx0]
        
      · simp [← hy, ← hy0]
        
      · exact H.symm ▸ hy
        
      
    · rw [← IH, sup_eq_left.mpr H.le, degree_add_eq_left_of_degree_lt H]
      
    

theorem nat_degree_sum_eq_of_disjoint (f : S → R[X]) (s : Finset S)
    (h : Set.Pairwise { i | i ∈ s ∧ f i ≠ 0 } (Ne on nat_degree ∘ f)) :
    natDegree (s.Sum f) = s.sup fun i => natDegree (f i) := by
  by_cases' H : ∃ x ∈ s, f x ≠ 0
  · obtain ⟨x, hx, hx'⟩ := H
    have hs : s.nonempty := ⟨x, hx⟩
    refine' nat_degree_eq_of_degree_eq_some _
    rw [degree_sum_eq_of_disjoint]
    · rw [← Finset.sup'_eq_sup hs, ← Finset.sup'_eq_sup hs, Finset.coe_sup', ← Finset.sup'_eq_sup hs]
      refine' le_antisymmₓ _ _
      · rw [Finset.sup'_le_iff]
        intro b hb
        by_cases' hb' : f b = 0
        · simpa [← hb'] using hs
          
        rw [degree_eq_nat_degree hb']
        exact Finset.le_sup' _ hb
        
      · rw [Finset.sup'_le_iff]
        intro b hb
        simp only [← Finset.le_sup'_iff, ← exists_prop, ← Function.comp_app]
        by_cases' hb' : f b = 0
        · refine' ⟨x, hx, _⟩
          contrapose! hx'
          simpa [← hb', ← degree_eq_bot] using hx'
          
        exact ⟨b, hb, (degree_eq_nat_degree hb').Ge⟩
        
      
    · exact h.imp fun x y hxy hxy' => hxy (nat_degree_eq_of_degree_eq hxy')
      
    
  · push_neg  at H
    rw [Finset.sum_eq_zero H, nat_degree_zero, eq_comm, show 0 = ⊥ from rfl, Finset.sup_eq_bot_iff]
    intro x hx
    simp [← H x hx]
    

variable [Semiringₓ S]

theorem nat_degree_pos_of_eval₂_root {p : R[X]} (hp : p ≠ 0) (f : R →+* S) {z : S} (hz : eval₂ f z p = 0)
    (inj : ∀ x : R, f x = 0 → x = 0) : 0 < natDegree p :=
  lt_of_not_geₓ fun hlt => by
    have A : p = C (p.coeff 0) := eq_C_of_nat_degree_le_zero hlt
    rw [A, eval₂_C] at hz
    simp only [← inj (p.coeff 0) hz, ← RingHom.map_zero] at A
    exact hp A

theorem degree_pos_of_eval₂_root {p : R[X]} (hp : p ≠ 0) (f : R →+* S) {z : S} (hz : eval₂ f z p = 0)
    (inj : ∀ x : R, f x = 0 → x = 0) : 0 < degree p :=
  nat_degree_pos_iff_degree_pos.mp (nat_degree_pos_of_eval₂_root hp f hz inj)

@[simp]
theorem coe_lt_degree {p : R[X]} {n : ℕ} : (n : WithBot ℕ) < degree p ↔ n < natDegree p := by
  by_cases' h : p = 0
  · simp [← h]
    
  rw [degree_eq_nat_degree h, WithBot.coe_lt_coe]

end Degree

end Semiringₓ

section NoZeroDivisors

variable [Semiringₓ R] [NoZeroDivisors R] {p q : R[X]}

theorem degree_mul_C (a0 : a ≠ 0) : (p * c a).degree = p.degree := by
  rw [degree_mul, degree_C a0, add_zeroₓ]

theorem degree_C_mul (a0 : a ≠ 0) : (c a * p).degree = p.degree := by
  rw [degree_mul, degree_C a0, zero_addₓ]

theorem nat_degree_mul_C (a0 : a ≠ 0) : (p * c a).natDegree = p.natDegree := by
  simp only [← nat_degree, ← degree_mul_C a0]

theorem nat_degree_C_mul (a0 : a ≠ 0) : (c a * p).natDegree = p.natDegree := by
  simp only [← nat_degree, ← degree_C_mul a0]

theorem nat_degree_comp : natDegree (p.comp q) = natDegree p * natDegree q := by
  by_cases' q0 : q.nat_degree = 0
  · rw [degree_le_zero_iff.mp (nat_degree_eq_zero_iff_degree_le_zero.mp q0), comp_C, nat_degree_C, nat_degree_C,
      mul_zero]
    
  · by_cases' p0 : p = 0
    · simp only [← p0, ← zero_comp, ← nat_degree_zero, ← zero_mul]
      
    refine' le_antisymmₓ nat_degree_comp_le (le_nat_degree_of_ne_zero _)
    simp only [← coeff_comp_degree_mul_degree q0, ← p0, ← mul_eq_zero, ← leading_coeff_eq_zero, ← or_selfₓ, ←
      ne_zero_of_nat_degree_gt (Nat.pos_of_ne_zeroₓ q0), ← pow_ne_zero, ← Ne.def, ← not_false_iff]
    

theorem leading_coeff_comp (hq : natDegree q ≠ 0) :
    leadingCoeff (p.comp q) = leadingCoeff p * leadingCoeff q ^ natDegree p := by
  rw [← coeff_comp_degree_mul_degree hq, ← nat_degree_comp, coeff_nat_degree]

end NoZeroDivisors

end Polynomial

