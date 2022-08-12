/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathbin.Algebra.GcdMonoid.Finset
import Mathbin.Data.Polynomial.FieldDivision
import Mathbin.Data.Polynomial.EraseLead
import Mathbin.Data.Polynomial.CancelLeads

/-!
# GCD structures on polynomials

Definitions and basic results about polynomials over GCD domains, particularly their contents
and primitive polynomials.

## Main Definitions
Let `p : R[X]`.
 - `p.content` is the `gcd` of the coefficients of `p`.
 - `p.is_primitive` indicates that `p.content = 1`.

## Main Results
 - `polynomial.content_mul`:
  If `p q : R[X]`, then `(p * q).content = p.content * q.content`.
 - `polynomial.normalized_gcd_monoid`:
  The polynomial ring of a GCD domain is itself a GCD domain.

-/


namespace Polynomial

open Polynomial

section Primitive

variable {R : Type _} [CommSemiringₓ R]

/-- A polynomial is primitive when the only constant polynomials dividing it are units -/
def IsPrimitive (p : R[X]) : Prop :=
  ∀ r : R, c r ∣ p → IsUnit r

theorem is_primitive_iff_is_unit_of_C_dvd {p : R[X]} : p.IsPrimitive ↔ ∀ r : R, c r ∣ p → IsUnit r :=
  Iff.rfl

@[simp]
theorem is_primitive_one : IsPrimitive (1 : R[X]) := fun r h => is_unit_C.mp (is_unit_of_dvd_one (c r) h)

theorem Monic.is_primitive {p : R[X]} (hp : p.Monic) : p.IsPrimitive := by
  rintro r ⟨q, h⟩
  exact
    is_unit_of_mul_eq_one r (q.coeff p.nat_degree)
      (by
        rwa [← coeff_C_mul, ← h])

theorem IsPrimitive.ne_zero [Nontrivial R] {p : R[X]} (hp : p.IsPrimitive) : p ≠ 0 := by
  rintro rfl
  exact (hp 0 (dvd_zero (C 0))).ne_zero rfl

end Primitive

variable {R : Type _} [CommRingₓ R] [IsDomain R]

section NormalizedGcdMonoid

variable [NormalizedGcdMonoid R]

/-- `p.content` is the `gcd` of the coefficients of `p`. -/
def content (p : R[X]) : R :=
  p.Support.gcd p.coeff

theorem content_dvd_coeff {p : R[X]} (n : ℕ) : p.content ∣ p.coeff n := by
  by_cases' h : n ∈ p.support
  · apply Finset.gcd_dvd h
    
  rw [mem_support_iff, not_not] at h
  rw [h]
  apply dvd_zero

@[simp]
theorem content_C {r : R} : (c r).content = normalize r := by
  rw [content]
  by_cases' h0 : r = 0
  · simp [← h0]
    
  have h : (C r).Support = {0} := support_monomial _ h0
  simp [← h]

@[simp]
theorem content_zero : content (0 : R[X]) = 0 := by
  rw [← C_0, content_C, normalize_zero]

@[simp]
theorem content_one : content (1 : R[X]) = 1 := by
  rw [← C_1, content_C, normalize_one]

theorem content_X_mul {p : R[X]} : content (X * p) = content p := by
  rw [content, content, Finset.gcd_def, Finset.gcd_def]
  refine' congr rfl _
  have h : (X * p).Support = p.support.map ⟨Nat.succ, Nat.succ_injective⟩ := by
    ext a
    simp only [← exists_prop, ← Finset.mem_map, ← Function.Embedding.coe_fn_mk, ← Ne.def, ← mem_support_iff]
    cases a
    · simp [← coeff_X_mul_zero, ← Nat.succ_ne_zero]
      
    rw [mul_comm, coeff_mul_X]
    constructor
    · intro h
      use a
      simp [← h]
      
    · rintro ⟨b, ⟨h1, h2⟩⟩
      rw [← Nat.succ_injective h2]
      apply h1
      
  rw [h]
  simp only [← Finset.map_val, ← Function.comp_app, ← Function.Embedding.coe_fn_mk, ← Multiset.map_map]
  refine' congr (congr rfl _) rfl
  ext a
  rw [mul_comm]
  simp [← coeff_mul_X]

@[simp]
theorem content_X_pow {k : ℕ} : content ((x : R[X]) ^ k) = 1 := by
  induction' k with k hi
  · simp
    
  rw [pow_succₓ, content_X_mul, hi]

@[simp]
theorem content_X : content (x : R[X]) = 1 := by
  rw [← mul_oneₓ X, content_X_mul, content_one]

theorem content_C_mul (r : R) (p : R[X]) : (c r * p).content = normalize r * p.content := by
  by_cases' h0 : r = 0
  · simp [← h0]
    
  rw [content]
  rw [content]
  rw [← Finset.gcd_mul_left]
  refine' congr (congr rfl _) _ <;> ext <;> simp [← h0, ← mem_support_iff]

@[simp]
theorem content_monomial {r : R} {k : ℕ} : content (monomial k r) = normalize r := by
  rw [monomial_eq_C_mul_X, content_C_mul, content_X_pow, mul_oneₓ]

theorem content_eq_zero_iff {p : R[X]} : content p = 0 ↔ p = 0 := by
  rw [content, Finset.gcd_eq_zero_iff]
  constructor <;> intro h
  · ext n
    by_cases' h0 : n ∈ p.support
    · rw [h n h0, coeff_zero]
      
    · rw [mem_support_iff] at h0
      push_neg  at h0
      simp [← h0]
      
    
  · intro x h0
    simp [← h]
    

@[simp]
theorem normalize_content {p : R[X]} : normalize p.content = p.content :=
  Finset.normalize_gcd

theorem content_eq_gcd_range_of_lt (p : R[X]) (n : ℕ) (h : p.natDegree < n) :
    p.content = (Finset.range n).gcd p.coeff := by
  apply dvd_antisymm_of_normalize_eq normalize_content Finset.normalize_gcd
  · rw [Finset.dvd_gcd_iff]
    intro i hi
    apply content_dvd_coeff _
    
  · apply Finset.gcd_mono
    intro i
    simp only [← Nat.lt_succ_iffₓ, ← mem_support_iff, ← Ne.def, ← Finset.mem_range]
    contrapose!
    intro h1
    apply coeff_eq_zero_of_nat_degree_lt (lt_of_lt_of_leₓ h h1)
    

theorem content_eq_gcd_range_succ (p : R[X]) : p.content = (Finset.range p.natDegree.succ).gcd p.coeff :=
  content_eq_gcd_range_of_lt _ _ (Nat.lt_succ_selfₓ _)

theorem content_eq_gcd_leading_coeff_content_erase_lead (p : R[X]) :
    p.content = GcdMonoid.gcd p.leadingCoeff (eraseLead p).content := by
  by_cases' h : p = 0
  · simp [← h]
    
  rw [← leading_coeff_eq_zero, leading_coeff, ← Ne.def, ← mem_support_iff] at h
  rw [content, ← Finset.insert_erase h, Finset.gcd_insert, leading_coeff, content, erase_lead_support]
  refine' congr rfl (Finset.gcd_congr rfl fun i hi => _)
  rw [Finset.mem_erase] at hi
  rw [erase_lead_coeff, if_neg hi.1]

theorem dvd_content_iff_C_dvd {p : R[X]} {r : R} : r ∣ p.content ↔ c r ∣ p := by
  rw [C_dvd_iff_dvd_coeff]
  constructor
  · intro h i
    apply h.trans (content_dvd_coeff _)
    
  · intro h
    rw [content, Finset.dvd_gcd_iff]
    intro i hi
    apply h i
    

theorem C_content_dvd (p : R[X]) : c p.content ∣ p :=
  dvd_content_iff_C_dvd.1 dvd_rfl

theorem is_primitive_iff_content_eq_one {p : R[X]} : p.IsPrimitive ↔ p.content = 1 := by
  rw [← normalize_content, normalize_eq_one, is_primitive]
  simp_rw [← dvd_content_iff_C_dvd]
  exact ⟨fun h => h p.content (dvd_refl p.content), fun h r hdvd => is_unit_of_dvd_unit hdvd h⟩

theorem IsPrimitive.content_eq_one {p : R[X]} (hp : p.IsPrimitive) : p.content = 1 :=
  is_primitive_iff_content_eq_one.mp hp

open Classical

noncomputable section

section PrimPart

/-- The primitive part of a polynomial `p` is the primitive polynomial gained by dividing `p` by
  `p.content`. If `p = 0`, then `p.prim_part = 1`.  -/
def primPart (p : R[X]) : R[X] :=
  if p = 0 then 1 else Classical.some (C_content_dvd p)

theorem eq_C_content_mul_prim_part (p : R[X]) : p = c p.content * p.primPart := by
  by_cases' h : p = 0
  · simp [← h]
    
  rw [prim_part, if_neg h, ← Classical.some_spec (C_content_dvd p)]

@[simp]
theorem prim_part_zero : primPart (0 : R[X]) = 1 :=
  if_pos rfl

theorem is_primitive_prim_part (p : R[X]) : p.primPart.IsPrimitive := by
  by_cases' h : p = 0
  · simp [← h]
    
  rw [← content_eq_zero_iff] at h
  rw [is_primitive_iff_content_eq_one]
  apply mul_left_cancel₀ h
  conv_rhs => rw [p.eq_C_content_mul_prim_part, mul_oneₓ, content_C_mul, normalize_content]

theorem content_prim_part (p : R[X]) : p.primPart.content = 1 :=
  p.is_primitive_prim_part.content_eq_one

theorem prim_part_ne_zero (p : R[X]) : p.primPart ≠ 0 :=
  p.is_primitive_prim_part.ne_zero

theorem nat_degree_prim_part (p : R[X]) : p.primPart.natDegree = p.natDegree := by
  by_cases' h : C p.content = 0
  · rw [C_eq_zero, content_eq_zero_iff] at h
    simp [← h]
    
  conv_rhs => rw [p.eq_C_content_mul_prim_part, nat_degree_mul h p.prim_part_ne_zero, nat_degree_C, zero_addₓ]

@[simp]
theorem IsPrimitive.prim_part_eq {p : R[X]} (hp : p.IsPrimitive) : p.primPart = p := by
  rw [← one_mulₓ p.prim_part, ← C_1, ← hp.content_eq_one, ← p.eq_C_content_mul_prim_part]

theorem is_unit_prim_part_C (r : R) : IsUnit (c r).primPart := by
  by_cases' h0 : r = 0
  · simp [← h0]
    
  unfold IsUnit
  refine'
    ⟨⟨C ↑(norm_unit r)⁻¹, C ↑(norm_unit r), by
        rw [← RingHom.map_mul, Units.inv_mul, C_1], by
        rw [← RingHom.map_mul, Units.mul_inv, C_1]⟩,
      _⟩
  rw [← normalize_eq_zero, ← C_eq_zero] at h0
  apply mul_left_cancel₀ h0
  conv_rhs => rw [← content_C, ← (C r).eq_C_content_mul_prim_part]
  simp only [← Units.coe_mk, ← normalize_apply, ← RingHom.map_mul]
  rw [mul_assoc, ← RingHom.map_mul, Units.mul_inv, C_1, mul_oneₓ]

theorem prim_part_dvd (p : R[X]) : p.primPart ∣ p :=
  Dvd.intro_left (c p.content) p.eq_C_content_mul_prim_part.symm

theorem aeval_prim_part_eq_zero {S : Type _} [Ringₓ S] [IsDomain S] [Algebra R S] [NoZeroSmulDivisors R S] {p : R[X]}
    {s : S} (hpzero : p ≠ 0) (hp : aeval s p = 0) : aeval s p.primPart = 0 := by
  rw [eq_C_content_mul_prim_part p, map_mul, aeval_C] at hp
  have hcont : p.content ≠ 0 := fun h => hpzero (content_eq_zero_iff.1 h)
  replace hcont := Function.Injective.ne (NoZeroSmulDivisors.algebra_map_injective R S) hcont
  rw [map_zero] at hcont
  exact eq_zero_of_ne_zero_of_mul_left_eq_zero hcont hp

theorem eval₂_prim_part_eq_zero {S : Type _} [CommRingₓ S] [IsDomain S] {f : R →+* S} (hinj : Function.Injective f)
    {p : R[X]} {s : S} (hpzero : p ≠ 0) (hp : eval₂ f s p = 0) : eval₂ f s p.primPart = 0 := by
  rw [eq_C_content_mul_prim_part p, eval₂_mul, eval₂_C] at hp
  have hcont : p.content ≠ 0 := fun h => hpzero (content_eq_zero_iff.1 h)
  replace hcont := Function.Injective.ne hinj hcont
  rw [map_zero] at hcont
  exact eq_zero_of_ne_zero_of_mul_left_eq_zero hcont hp

end PrimPart

theorem gcd_content_eq_of_dvd_sub {a : R} {p q : R[X]} (h : c a ∣ p - q) :
    GcdMonoid.gcd a p.content = GcdMonoid.gcd a q.content := by
  rw
    [content_eq_gcd_range_of_lt p (max p.nat_degree q.nat_degree).succ
      (lt_of_le_of_ltₓ (le_max_leftₓ _ _) (Nat.lt_succ_selfₓ _))]
  rw
    [content_eq_gcd_range_of_lt q (max p.nat_degree q.nat_degree).succ
      (lt_of_le_of_ltₓ (le_max_rightₓ _ _) (Nat.lt_succ_selfₓ _))]
  apply Finset.gcd_eq_of_dvd_sub
  intro x hx
  cases' h with w hw
  use w.coeff x
  rw [← coeff_sub, hw, coeff_C_mul]

theorem content_mul_aux {p q : R[X]} :
    GcdMonoid.gcd (p * q).eraseLead.content p.leadingCoeff = GcdMonoid.gcd (p.eraseLead * q).content p.leadingCoeff :=
  by
  rw [gcd_comm (content _) _, gcd_comm (content _) _]
  apply gcd_content_eq_of_dvd_sub
  rw [← self_sub_C_mul_X_pow, ← self_sub_C_mul_X_pow, sub_mul, sub_sub, add_commₓ, sub_add, sub_sub_cancel,
    leading_coeff_mul, RingHom.map_mul, mul_assoc, mul_assoc]
  apply dvd_sub (Dvd.intro _ rfl) (Dvd.intro _ rfl)

@[simp]
theorem content_mul {p q : R[X]} : (p * q).content = p.content * q.content := by
  classical
  suffices h : ∀ (n : ℕ) (p q : R[X]), (p * q).degree < n → (p * q).content = p.content * q.content
  · apply h
    apply lt_of_le_of_ltₓ degree_le_nat_degree (WithBot.coe_lt_coe.2 (Nat.lt_succ_selfₓ _))
    
  intro n
  induction' n with n ih
  · intro p q hpq
    rw [WithBot.coe_zero, Nat.WithBot.lt_zero_iff, degree_eq_bot, mul_eq_zero] at hpq
    rcases hpq with (rfl | rfl) <;> simp
    
  intro p q hpq
  by_cases' p0 : p = 0
  · simp [← p0]
    
  by_cases' q0 : q = 0
  · simp [← q0]
    
  rw [degree_eq_nat_degree (mul_ne_zero p0 q0), WithBot.coe_lt_coe, Nat.lt_succ_iff_lt_or_eq, ← WithBot.coe_lt_coe, ←
    degree_eq_nat_degree (mul_ne_zero p0 q0), nat_degree_mul p0 q0] at hpq
  rcases hpq with (hlt | heq)
  · apply ih _ _ hlt
    
  rw [← p.nat_degree_prim_part, ← q.nat_degree_prim_part, ← WithBot.coe_eq_coe, WithBot.coe_add, ←
    degree_eq_nat_degree p.prim_part_ne_zero, ← degree_eq_nat_degree q.prim_part_ne_zero] at heq
  rw [p.eq_C_content_mul_prim_part, q.eq_C_content_mul_prim_part]
  suffices h : (q.prim_part * p.prim_part).content = 1
  · rw [mul_assoc, content_C_mul, content_C_mul, mul_comm p.prim_part, mul_assoc, content_C_mul, content_C_mul, h,
      mul_oneₓ, content_prim_part, content_prim_part, mul_oneₓ, mul_oneₓ]
    
  rw [← normalize_content, normalize_eq_one, is_unit_iff_dvd_one, content_eq_gcd_leading_coeff_content_erase_lead,
    leading_coeff_mul, gcd_comm]
  apply (gcd_mul_dvd_mul_gcd _ _ _).trans
  rw [content_mul_aux, ih, content_prim_part, mul_oneₓ, gcd_comm, ← content_eq_gcd_leading_coeff_content_erase_lead,
    content_prim_part, one_mulₓ, mul_comm q.prim_part, content_mul_aux, ih, content_prim_part, mul_oneₓ, gcd_comm, ←
    content_eq_gcd_leading_coeff_content_erase_lead, content_prim_part]
  · rw [← HEq, degree_mul, WithBot.add_lt_add_iff_right]
    · apply degree_erase_lt p.prim_part_ne_zero
      
    · rw [Ne.def, degree_eq_bot]
      apply q.prim_part_ne_zero
      
    
  · rw [mul_comm, ← HEq, degree_mul, WithBot.add_lt_add_iff_left]
    · apply degree_erase_lt q.prim_part_ne_zero
      
    · rw [Ne.def, degree_eq_bot]
      apply p.prim_part_ne_zero
      
    

theorem IsPrimitive.mul {p q : R[X]} (hp : p.IsPrimitive) (hq : q.IsPrimitive) : (p * q).IsPrimitive := by
  rw [is_primitive_iff_content_eq_one, content_mul, hp.content_eq_one, hq.content_eq_one, mul_oneₓ]

@[simp]
theorem prim_part_mul {p q : R[X]} (h0 : p * q ≠ 0) : (p * q).primPart = p.primPart * q.primPart := by
  rw [Ne.def, ← content_eq_zero_iff, ← C_eq_zero] at h0
  apply mul_left_cancel₀ h0
  conv_lhs => rw [← (p * q).eq_C_content_mul_prim_part, p.eq_C_content_mul_prim_part, q.eq_C_content_mul_prim_part]
  rw [content_mul, RingHom.map_mul]
  ring

theorem IsPrimitive.is_primitive_of_dvd {p q : R[X]} (hp : p.IsPrimitive) (hdvd : q ∣ p) : q.IsPrimitive := by
  rcases hdvd with ⟨r, rfl⟩
  rw [is_primitive_iff_content_eq_one, ← normalize_content, normalize_eq_one, is_unit_iff_dvd_one]
  apply Dvd.intro r.content
  rwa [is_primitive_iff_content_eq_one, content_mul] at hp

theorem IsPrimitive.dvd_prim_part_iff_dvd {p q : R[X]} (hp : p.IsPrimitive) (hq : q ≠ 0) : p ∣ q.primPart ↔ p ∣ q := by
  refine' ⟨fun h => h.trans (Dvd.intro_left _ q.eq_C_content_mul_prim_part.symm), fun h => _⟩
  rcases h with ⟨r, rfl⟩
  apply Dvd.intro _
  rw [prim_part_mul hq, hp.prim_part_eq]

theorem exists_primitive_lcm_of_is_primitive {p q : R[X]} (hp : p.IsPrimitive) (hq : q.IsPrimitive) :
    ∃ r : R[X], r.IsPrimitive ∧ ∀ s : R[X], p ∣ s ∧ q ∣ s ↔ r ∣ s := by
  classical
  have h : ∃ (n : ℕ)(r : R[X]), r.natDegree = n ∧ r.IsPrimitive ∧ p ∣ r ∧ q ∣ r :=
    ⟨(p * q).natDegree, p * q, rfl, hp.mul hq, dvd_mul_right _ _, dvd_mul_left _ _⟩
  rcases Nat.find_specₓ h with ⟨r, rdeg, rprim, pr, qr⟩
  refine' ⟨r, rprim, fun s => ⟨_, fun rs => ⟨pr.trans rs, qr.trans rs⟩⟩⟩
  suffices hs : ∀ (n : ℕ) (s : R[X]), s.natDegree = n → p ∣ s ∧ q ∣ s → r ∣ s
  · apply hs s.nat_degree s rfl
    
  clear s
  by_contra' con
  rcases Nat.find_specₓ Con with ⟨s, sdeg, ⟨ps, qs⟩, rs⟩
  have s0 : s ≠ 0 := by
    contrapose! rs
    simp [← rs]
  have hs :=
    Nat.find_min'ₓ h
      ⟨_, s.nat_degree_prim_part, s.is_primitive_prim_part, (hp.dvd_prim_part_iff_dvd s0).2 ps,
        (hq.dvd_prim_part_iff_dvd s0).2 qs⟩
  rw [← rdeg] at hs
  by_cases' sC : s.nat_degree ≤ 0
  · rw [eq_C_of_nat_degree_le_zero (le_transₓ hs sC), is_primitive_iff_content_eq_one, content_C, normalize_eq_one] at
      rprim
    rw [eq_C_of_nat_degree_le_zero (le_transₓ hs sC), ← dvd_content_iff_C_dvd] at rs
    apply rs rprim.dvd
    
  have hcancel := nat_degree_cancel_leads_lt_of_nat_degree_le_nat_degree hs (lt_of_not_geₓ sC)
  rw [sdeg] at hcancel
  apply Nat.find_minₓ Con hcancel
  refine' ⟨_, rfl, ⟨dvd_cancel_leads_of_dvd_of_dvd pr ps, dvd_cancel_leads_of_dvd_of_dvd qr qs⟩, fun rcs => rs _⟩
  rw [← rprim.dvd_prim_part_iff_dvd s0]
  rw [cancel_leads, tsub_eq_zero_iff_le.mpr hs, pow_zeroₓ, mul_oneₓ] at rcs
  have h := dvd_add rcs (Dvd.intro_left _ rfl)
  have hC0 := rprim.ne_zero
  rw [Ne.def, ← leading_coeff_eq_zero, ← C_eq_zero] at hC0
  rw [sub_add_cancel, ← rprim.dvd_prim_part_iff_dvd (mul_ne_zero hC0 s0)] at h
  rcases is_unit_prim_part_C r.leading_coeff with ⟨u, hu⟩
  apply h.trans (Associated.symm ⟨u, _⟩).Dvd
  rw [prim_part_mul (mul_ne_zero hC0 s0), hu, mul_comm]

theorem dvd_iff_content_dvd_content_and_prim_part_dvd_prim_part {p q : R[X]} (hq : q ≠ 0) :
    p ∣ q ↔ p.content ∣ q.content ∧ p.primPart ∣ q.primPart := by
  constructor <;> intro h
  · rcases h with ⟨r, rfl⟩
    rw [content_mul, p.is_primitive_prim_part.dvd_prim_part_iff_dvd hq]
    exact ⟨Dvd.intro _ rfl, p.prim_part_dvd.trans (Dvd.intro _ rfl)⟩
    
  · rw [p.eq_C_content_mul_prim_part, q.eq_C_content_mul_prim_part]
    exact mul_dvd_mul (RingHom.map_dvd C h.1) h.2
    

instance (priority := 100) normalizedGcdMonoid : NormalizedGcdMonoid R[X] :=
  normalizedGcdMonoidOfExistsLcm fun p q => by
    rcases exists_primitive_lcm_of_is_primitive p.is_primitive_prim_part q.is_primitive_prim_part with ⟨r, rprim, hr⟩
    refine' ⟨C (lcm p.content q.content) * r, fun s => _⟩
    by_cases' hs : s = 0
    · simp [← hs]
      
    by_cases' hpq : C (lcm p.content q.content) = 0
    · rw [C_eq_zero, lcm_eq_zero_iff, content_eq_zero_iff, content_eq_zero_iff] at hpq
      rcases hpq with (hpq | hpq) <;> simp [← hpq, ← hs]
      
    iterate 3 
      rw [dvd_iff_content_dvd_content_and_prim_part_dvd_prim_part hs]
    rw [content_mul, rprim.content_eq_one, mul_oneₓ, content_C, normalize_lcm, lcm_dvd_iff,
      prim_part_mul (mul_ne_zero hpq rprim.ne_zero), rprim.prim_part_eq,
      IsUnit.mul_left_dvd _ _ _ (is_unit_prim_part_C (lcm p.content q.content)), ← hr s.prim_part]
    tauto

theorem degree_gcd_le_left {p : R[X]} (hp : p ≠ 0) (q) : (gcd p q).degree ≤ p.degree := by
  have := nat_degree_le_iff_degree_le.mp (nat_degree_le_of_dvd (gcd_dvd_left p q) hp)
  rwa [degree_eq_nat_degree hp]

theorem degree_gcd_le_right (p) {q : R[X]} (hq : q ≠ 0) : (gcd p q).degree ≤ q.degree := by
  rw [gcd_comm]
  exact degree_gcd_le_left hq p

end NormalizedGcdMonoid

end Polynomial

