/-
Copyright (c) 2020 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Mathbin.Algebra.BigOperators.Fin
import Mathbin.Data.Polynomial.Degree.Definitions

/-!
# Erase the leading term of a univariate polynomial

## Definition

* `erase_lead f`: the polynomial `f - leading term of f`

`erase_lead` serves as reduction step in an induction, shaving off one monomial from a polynomial.
The definition is set up so that it does not mention subtraction in the definition,
and thus works for polynomials over semirings as well as rings.
-/


noncomputable section

open Classical Polynomial

open Polynomial Finset

namespace Polynomial

variable {R : Type _} [Semiringₓ R] {f : R[X]}

/-- `erase_lead f` for a polynomial `f` is the polynomial obtained by
subtracting from `f` the leading term of `f`. -/
def eraseLead (f : R[X]) : R[X] :=
  Polynomial.erase f.natDegree f

section EraseLead

theorem erase_lead_support (f : R[X]) : f.eraseLead.Support = f.Support.erase f.natDegree := by
  simp only [← erase_lead, ← support_erase]

theorem erase_lead_coeff (i : ℕ) : f.eraseLead.coeff i = if i = f.natDegree then 0 else f.coeff i := by
  simp only [← erase_lead, ← coeff_erase]

@[simp]
theorem erase_lead_coeff_nat_degree : f.eraseLead.coeff f.natDegree = 0 := by
  simp [← erase_lead_coeff]

theorem erase_lead_coeff_of_ne (i : ℕ) (hi : i ≠ f.natDegree) : f.eraseLead.coeff i = f.coeff i := by
  simp [← erase_lead_coeff, ← hi]

@[simp]
theorem erase_lead_zero : eraseLead (0 : R[X]) = 0 := by
  simp only [← erase_lead, ← erase_zero]

@[simp]
theorem erase_lead_add_monomial_nat_degree_leading_coeff (f : R[X]) :
    f.eraseLead + monomial f.natDegree f.leadingCoeff = f := by
  ext i
  simp only [← erase_lead_coeff, ← coeff_monomial, ← coeff_add, ← @eq_comm _ _ i]
  split_ifs with h
  · subst i
    simp only [← leading_coeff, ← zero_addₓ]
    
  · exact add_zeroₓ _
    

@[simp]
theorem erase_lead_add_C_mul_X_pow (f : R[X]) : f.eraseLead + c f.leadingCoeff * X ^ f.natDegree = f := by
  rw [C_mul_X_pow_eq_monomial, erase_lead_add_monomial_nat_degree_leading_coeff]

@[simp]
theorem self_sub_monomial_nat_degree_leading_coeff {R : Type _} [Ringₓ R] (f : R[X]) :
    f - monomial f.natDegree f.leadingCoeff = f.eraseLead :=
  (eq_sub_iff_add_eq.mpr (erase_lead_add_monomial_nat_degree_leading_coeff f)).symm

@[simp]
theorem self_sub_C_mul_X_pow {R : Type _} [Ringₓ R] (f : R[X]) : f - c f.leadingCoeff * X ^ f.natDegree = f.eraseLead :=
  by
  rw [C_mul_X_pow_eq_monomial, self_sub_monomial_nat_degree_leading_coeff]

theorem erase_lead_ne_zero (f0 : 2 ≤ f.Support.card) : eraseLead f ≠ 0 := by
  rw [Ne.def, ← card_support_eq_zero, erase_lead_support]
  exact (zero_lt_one.trans_le <| (tsub_le_tsub_right f0 1).trans Finset.pred_card_le_card_erase).Ne.symm

theorem lt_nat_degree_of_mem_erase_lead_support {a : ℕ} (h : a ∈ (eraseLead f).Support) : a < f.natDegree := by
  rw [erase_lead_support, mem_erase] at h
  exact lt_of_le_of_neₓ (le_nat_degree_of_mem_supp a h.2) h.1

theorem ne_nat_degree_of_mem_erase_lead_support {a : ℕ} (h : a ∈ (eraseLead f).Support) : a ≠ f.natDegree :=
  (lt_nat_degree_of_mem_erase_lead_support h).Ne

theorem nat_degree_not_mem_erase_lead_support : f.natDegree ∉ (eraseLead f).Support := fun h =>
  ne_nat_degree_of_mem_erase_lead_support h rfl

theorem erase_lead_support_card_lt (h : f ≠ 0) : (eraseLead f).Support.card < f.Support.card := by
  rw [erase_lead_support]
  exact card_lt_card (erase_ssubset <| nat_degree_mem_support_of_nonzero h)

theorem erase_lead_card_support {c : ℕ} (fc : f.Support.card = c) : f.eraseLead.Support.card = c - 1 := by
  by_cases' f0 : f = 0
  · rw [← fc, f0, erase_lead_zero, support_zero, card_empty]
    
  · rw [erase_lead_support, card_erase_of_mem (nat_degree_mem_support_of_nonzero f0), fc]
    

theorem erase_lead_card_support' {c : ℕ} (fc : f.Support.card = c + 1) : f.eraseLead.Support.card = c :=
  erase_lead_card_support fc

@[simp]
theorem erase_lead_monomial (i : ℕ) (r : R) : eraseLead (monomial i r) = 0 := by
  by_cases' hr : r = 0
  · subst r
    simp only [← monomial_zero_right, ← erase_lead_zero]
    
  · rw [erase_lead, nat_degree_monomial, if_neg hr, erase_monomial]
    

@[simp]
theorem erase_lead_C (r : R) : eraseLead (c r) = 0 :=
  erase_lead_monomial _ _

@[simp]
theorem erase_lead_X : eraseLead (x : R[X]) = 0 :=
  erase_lead_monomial _ _

@[simp]
theorem erase_lead_X_pow (n : ℕ) : eraseLead (X ^ n : R[X]) = 0 := by
  rw [X_pow_eq_monomial, erase_lead_monomial]

@[simp]
theorem erase_lead_C_mul_X_pow (r : R) (n : ℕ) : eraseLead (c r * X ^ n) = 0 := by
  rw [C_mul_X_pow_eq_monomial, erase_lead_monomial]

theorem erase_lead_add_of_nat_degree_lt_left {p q : R[X]} (pq : q.natDegree < p.natDegree) :
    (p + q).eraseLead = p.eraseLead + q := by
  ext n
  by_cases' nd : n = p.nat_degree
  · rw [nd, erase_lead_coeff, if_pos (nat_degree_add_eq_left_of_nat_degree_lt pq).symm]
    simpa using (coeff_eq_zero_of_nat_degree_lt pq).symm
    
  · rw [erase_lead_coeff, coeff_add, coeff_add, erase_lead_coeff, if_neg, if_neg nd]
    rintro rfl
    exact nd (nat_degree_add_eq_left_of_nat_degree_lt pq)
    

theorem erase_lead_add_of_nat_degree_lt_right {p q : R[X]} (pq : p.natDegree < q.natDegree) :
    (p + q).eraseLead = p + q.eraseLead := by
  ext n
  by_cases' nd : n = q.nat_degree
  · rw [nd, erase_lead_coeff, if_pos (nat_degree_add_eq_right_of_nat_degree_lt pq).symm]
    simpa using (coeff_eq_zero_of_nat_degree_lt pq).symm
    
  · rw [erase_lead_coeff, coeff_add, coeff_add, erase_lead_coeff, if_neg, if_neg nd]
    rintro rfl
    exact nd (nat_degree_add_eq_right_of_nat_degree_lt pq)
    

theorem erase_lead_degree_le : (eraseLead f).degree ≤ f.degree := by
  rw [degree_le_iff_coeff_zero]
  intro i hi
  rw [erase_lead_coeff]
  split_ifs with h
  · rfl
    
  apply coeff_eq_zero_of_degree_lt hi

theorem erase_lead_nat_degree_le_aux : (eraseLead f).natDegree ≤ f.natDegree :=
  nat_degree_le_nat_degree erase_lead_degree_le

theorem erase_lead_nat_degree_lt (f0 : 2 ≤ f.Support.card) : (eraseLead f).natDegree < f.natDegree :=
  lt_of_le_of_neₓ erase_lead_nat_degree_le_aux <|
    ne_nat_degree_of_mem_erase_lead_support <| nat_degree_mem_support_of_nonzero <| erase_lead_ne_zero f0

theorem erase_lead_nat_degree_lt_or_erase_lead_eq_zero (f : R[X]) :
    (eraseLead f).natDegree < f.natDegree ∨ f.eraseLead = 0 := by
  by_cases' h : f.support.card ≤ 1
  · right
    rw [← C_mul_X_pow_eq_self h]
    simp
    
  · left
    apply erase_lead_nat_degree_lt (lt_of_not_geₓ h)
    

theorem erase_lead_nat_degree_le (f : R[X]) : (eraseLead f).natDegree ≤ f.natDegree - 1 := by
  rcases f.erase_lead_nat_degree_lt_or_erase_lead_eq_zero with (h | h)
  · exact Nat.le_pred_of_ltₓ h
    
  · simp only [← h, ← nat_degree_zero, ← zero_le]
    

end EraseLead

/-- An induction lemma for polynomials. It takes a natural number `N` as a parameter, that is
required to be at least as big as the `nat_degree` of the polynomial.  This is useful to prove
results where you want to change each term in a polynomial to something else depending on the
`nat_degree` of the polynomial itself and not on the specific `nat_degree` of each term. -/
theorem induction_with_nat_degree_le (P : R[X] → Prop) (N : ℕ) (P_0 : P 0)
    (P_C_mul_pow : ∀ n : ℕ, ∀ r : R, r ≠ 0 → n ≤ N → P (c r * X ^ n))
    (P_C_add : ∀ f g : R[X], f.natDegree < g.natDegree → g.natDegree ≤ N → P f → P g → P (f + g)) :
    ∀ f : R[X], f.natDegree ≤ N → P f := by
  intro f df
  generalize hd : card f.support = c
  revert f
  induction' c with c hc
  · intro f df f0
    convert P_0
    simpa only [← support_eq_empty, ← card_eq_zero] using f0
    
  · intro f df f0
    rw [← erase_lead_add_C_mul_X_pow f]
    cases c
    · convert P_C_mul_pow f.nat_degree f.leading_coeff _ df
      · convert zero_addₓ _
        rw [← card_support_eq_zero, erase_lead_card_support f0]
        
      · rw [leading_coeff_ne_zero, Ne.def, ← card_support_eq_zero, f0]
        exact zero_ne_one.symm
        
      
    refine' P_C_add f.erase_lead _ _ _ _ _
    · refine' (erase_lead_nat_degree_lt _).trans_le (le_of_eqₓ _)
      · exact (Nat.succ_le_succₓ (Nat.succ_le_succₓ (Nat.zero_leₓ _))).trans f0.ge
        
      · rw [nat_degree_C_mul_X_pow _ _ (leading_coeff_ne_zero.mpr _)]
        rintro rfl
        simpa using f0
        
      
    · exact (nat_degree_C_mul_X_pow_le f.leading_coeff f.nat_degree).trans df
      
    · exact hc _ (erase_lead_nat_degree_le_aux.trans df) (erase_lead_card_support f0)
      
    · refine' P_C_mul_pow _ _ _ df
      rw [Ne.def, leading_coeff_eq_zero, ← card_support_eq_zero, f0]
      exact Nat.succ_ne_zero _
      
    

/-- Let `φ : R[x] → S[x]` be an additive map, `k : ℕ` a bound, and `fu : ℕ → ℕ` a
"sufficiently monotone" map.  Assume also that
* `φ` maps to `0` all monomials of degree less than `k`,
* `φ` maps each monomial `m` in `R[x]` to a polynomial `φ m` of degree `fu (deg m)`.
Then, `φ` maps each polynomial `p` in `R[x]` to a polynomial of degree `fu (deg p)`. -/
theorem mono_map_nat_degree_eq {S F : Type _} [Semiringₓ S] [AddMonoidHomClass F R[X] S[X]] {φ : F} {p : R[X]} (k : ℕ)
    (fu : ℕ → ℕ) (fu0 : ∀ {n}, n ≤ k → fu n = 0) (fc : ∀ {n m}, k ≤ n → n < m → fu n < fu m)
    (φ_k : ∀ {f : R[X]}, f.natDegree < k → φ f = 0) (φ_mon_nat : ∀ n c, c ≠ 0 → (φ (monomial n c)).natDegree = fu n) :
    (φ p).natDegree = fu p.natDegree := by
  refine'
    induction_with_nat_degree_le (fun p => _ = fu _) p.nat_degree
      (by
        simp [← fu0])
      _ _ _ rfl.le
  · intro n r r0 np
    rw [nat_degree_C_mul_X_pow _ _ r0, ← monomial_eq_C_mul_X, φ_mon_nat _ _ r0]
    
  · intro f g fg gp fk gk
    rw [nat_degree_add_eq_right_of_nat_degree_lt fg, _root_.map_add]
    by_cases' FG : k ≤ f.nat_degree
    · rw [nat_degree_add_eq_right_of_nat_degree_lt, gk]
      rw [fk, gk]
      exact fc FG fg
      
    · cases k
      · exact (FG (Nat.zero_leₓ _)).elim
        
      · rwa [φ_k (not_le.mp FG), zero_addₓ]
        
      
    

theorem map_nat_degree_eq_sub {S F : Type _} [Semiringₓ S] [AddMonoidHomClass F R[X] S[X]] {φ : F} {p : R[X]} {k : ℕ}
    (φ_k : ∀ f : R[X], f.natDegree < k → φ f = 0) (φ_mon : ∀ n c, c ≠ 0 → (φ (monomial n c)).natDegree = n - k) :
    (φ p).natDegree = p.natDegree - k :=
  mono_map_nat_degree_eq k (fun j => j - k)
    (by
      simp )
    (fun m n h => (tsub_lt_tsub_iff_right h).mpr) φ_k φ_mon

theorem map_nat_degree_eq_nat_degree {S F : Type _} [Semiringₓ S] [AddMonoidHomClass F R[X] S[X]] {φ : F} (p)
    (φ_mon_nat : ∀ n c, c ≠ 0 → (φ (monomial n c)).natDegree = n) : (φ p).natDegree = p.natDegree :=
  (map_nat_degree_eq_sub (fun f h => (Nat.not_lt_zeroₓ _ h).elim)
        (by
          simpa)).trans
    p.natDegree.sub_zero

open BigOperators

theorem card_support_eq' {n : ℕ} (k : Finₓ n → ℕ) (x : Finₓ n → R) (hk : Function.Injective k) (hx : ∀ i, x i ≠ 0) :
    (∑ i, c (x i) * X ^ k i).Support.card = n := by
  suffices (∑ i, C (x i) * X ^ k i).Support = image k univ by
    rw [this, univ.card_image_of_injective hk, card_fin]
  simp_rw [Finset.ext_iff, mem_support_iff, finset_sum_coeff, coeff_C_mul_X_pow, mem_image, mem_univ, exists_true_left]
  refine' fun i => ⟨fun h => _, _⟩
  · obtain ⟨j, hj, h⟩ := exists_ne_zero_of_sum_ne_zero h
    exact ⟨j, (ite_ne_right_iff.mp h).1.symm⟩
    
  · rintro ⟨j, rfl⟩
    rw [sum_eq_single_of_mem j (mem_univ j), if_pos rfl]
    · exact hx j
      
    · exact fun m hm hmj => if_neg fun h => hmj.symm (hk h)
      
    

theorem card_support_eq {n : ℕ} :
    f.Support.card = n ↔
      ∃ (k : Finₓ n → ℕ)(x : Finₓ n → R)(hk : StrictMono k)(hx : ∀ i, x i ≠ 0), f = ∑ i, c (x i) * X ^ k i :=
  by
  refine' ⟨_, fun ⟨k, x, hk, hx, hf⟩ => hf.symm ▸ card_support_eq' k x hk.Injective hx⟩
  induction' n with n hn generalizing f
  · exact fun hf => ⟨0, 0, isEmptyElim, isEmptyElim, card_support_eq_zero.mp hf⟩
    
  · intro h
    obtain ⟨k, x, hk, hx, hf⟩ := hn (erase_lead_card_support' h)
    have H : ¬∃ k : Finₓ n, k.cast_succ = Finₓ.last n := by
      rintro ⟨i, hi⟩
      exact i.cast_succ_lt_last.Ne hi
    refine'
      ⟨Function.extendₓ Finₓ.castSucc k fun _ => f.nat_degree,
        Function.extendₓ Finₓ.castSucc x fun _ => f.leading_coeff, _, _, _⟩
    · intro i j hij
      have hi : i ∈ Set.Range (Finₓ.castSucc : Finₓ n ↪o Finₓ (n + 1)) := by
        rw [Finₓ.range_cast_succ, Set.mem_def]
        exact lt_of_lt_of_leₓ hij (nat.lt_succ_iff.mp j.2)
      obtain ⟨i, rfl⟩ := hi
      rw [Function.extend_applyₓ fin.cast_succ.injective]
      by_cases' hj : ∃ j₀, Finₓ.castSucc j₀ = j
      · obtain ⟨j, rfl⟩ := hj
        rwa [Function.extend_applyₓ fin.cast_succ.injective, hk.lt_iff_lt, ← Finₓ.cast_succ_lt_cast_succ_iff]
        
      · rw [Function.extend_apply' _ _ _ hj]
        apply lt_nat_degree_of_mem_erase_lead_support
        rw [mem_support_iff, hf, finset_sum_coeff]
        rw [sum_eq_single, coeff_C_mul, coeff_X_pow_self, mul_oneₓ]
        · exact hx i
          
        · intro j hj hji
          rw [coeff_C_mul, coeff_X_pow, if_neg (hk.injective.ne hji.symm), mul_zero]
          
        · exact fun hi => (hi (mem_univ i)).elim
          
        
      
    · intro i
      by_cases' hi : ∃ i₀, Finₓ.castSucc i₀ = i
      · obtain ⟨i, rfl⟩ := hi
        rw [Function.extend_applyₓ fin.cast_succ.injective]
        exact hx i
        
      · rw [Function.extend_apply' _ _ _ hi, Ne, leading_coeff_eq_zero, ← card_support_eq_zero, h]
        exact n.succ_ne_zero
        
      
    · rw [Finₓ.sum_univ_cast_succ]
      simp only [← Function.extend_applyₓ fin.cast_succ.injective]
      rw [← hf, Function.extend_apply', Function.extend_apply', erase_lead_add_C_mul_X_pow]
      all_goals
        exact H
      
    

theorem card_support_eq_one : f.Support.card = 1 ↔ ∃ (k : ℕ)(x : R)(hx : x ≠ 0), f = c x * X ^ k := by
  refine' ⟨fun h => _, _⟩
  · obtain ⟨k, x, hk, hx, rfl⟩ := card_support_eq.mp h
    exact ⟨k 0, x 0, hx 0, Finₓ.sum_univ_one _⟩
    
  · rintro ⟨k, x, hx, rfl⟩
    rw [support_C_mul_X_pow k hx, card_singleton]
    

theorem card_support_eq_two :
    f.Support.card = 2 ↔ ∃ (k m : ℕ)(hkm : k < m)(x y : R)(hx : x ≠ 0)(hy : y ≠ 0), f = c x * X ^ k + c y * X ^ m := by
  refine' ⟨fun h => _, _⟩
  · obtain ⟨k, x, hk, hx, rfl⟩ := card_support_eq.mp h
    refine' ⟨k 0, k 1, hk Nat.zero_lt_oneₓ, x 0, x 1, hx 0, hx 1, _⟩
    rw [Finₓ.sum_univ_cast_succ, Finₓ.sum_univ_one]
    rfl
    
  · rintro ⟨k, m, hkm, x, y, hx, hy, rfl⟩
    exact card_support_binomial hkm.ne hx hy
    

theorem card_support_eq_three :
    f.Support.card = 3 ↔
      ∃ (k m n : ℕ)(hkm : k < m)(hmn : m < n)(x y z : R)(hx : x ≠ 0)(hy : y ≠ 0)(hz : z ≠ 0),
        f = c x * X ^ k + c y * X ^ m + c z * X ^ n :=
  by
  refine' ⟨fun h => _, _⟩
  · obtain ⟨k, x, hk, hx, rfl⟩ := card_support_eq.mp h
    refine' ⟨k 0, k 1, k 2, hk Nat.zero_lt_oneₓ, hk (Nat.lt_succ_selfₓ 1), x 0, x 1, x 2, hx 0, hx 1, hx 2, _⟩
    rw [Finₓ.sum_univ_cast_succ, Finₓ.sum_univ_cast_succ, Finₓ.sum_univ_one]
    rfl
    
  · rintro ⟨k, m, n, hkm, hmn, x, y, z, hx, hy, hz, rfl⟩
    exact card_support_trinomial hkm hmn hx hy hz
    

end Polynomial

