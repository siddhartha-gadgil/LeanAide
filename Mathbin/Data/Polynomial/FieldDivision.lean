/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Scott Morrison, Jens Wagemaker
-/
import Mathbin.Data.Polynomial.Derivative
import Mathbin.Data.Polynomial.RingDivision
import Mathbin.RingTheory.EuclideanDomain

/-!
# Theory of univariate polynomials

This file starts looking like the ring theory of $ R[X] $

-/


noncomputable section

open Classical BigOperators Polynomial

namespace Polynomial

universe u v w y z

variable {R : Type u} {S : Type v} {k : Type y} {A : Type z} {a b : R} {n : ℕ}

section IsDomain

variable [CommRingₓ R] [IsDomain R]

theorem roots_C_mul (p : R[X]) {a : R} (hzero : a ≠ 0) : (c a * p).roots = p.roots := by
  by_cases' hpzero : p = 0
  · simp only [← hpzero, ← mul_zero]
    
  rw [Multiset.ext]
  intro b
  have prodzero : C a * p ≠ 0 := by
    simp only [← hpzero, ← or_falseₓ, ← Ne.def, ← mul_eq_zero, ← C_eq_zero, ← hzero, ← not_false_iff]
  rw [count_roots, count_roots, root_multiplicity_mul prodzero]
  have mulzero : root_multiplicity b (C a) = 0 := by
    simp only [← hzero, ← root_multiplicity_eq_zero, ← eval_C, ← is_root.def, ← not_false_iff]
  simp only [← mulzero, ← zero_addₓ]

theorem derivative_root_multiplicity_of_root [CharZero R] {p : R[X]} {t : R} (hpt : p.IsRoot t) :
    p.derivative.rootMultiplicity t = p.rootMultiplicity t - 1 := by
  rcases eq_or_ne p 0 with (rfl | hp)
  · simp
    
  nth_rw 0[← p.div_by_monic_mul_pow_root_multiplicity_eq t]
  simp only [← derivative_pow, ← derivative_mul, ← derivative_sub, ← derivative_X, ← derivative_C, ← sub_zero, ←
    mul_oneₓ]
  set n := p.root_multiplicity t - 1
  have hn : n + 1 = _ := tsub_add_cancel_of_le ((root_multiplicity_pos hp).mpr hpt)
  rw [← hn]
  set q := p /ₘ (X - C t) ^ (n + 1) with hq
  convert_to root_multiplicity t ((X - C t) ^ n * (derivative q * (X - C t) + q * ↑(n + 1))) = n
  · congr
    rw [mul_addₓ, mul_left_commₓ <| (X - C t) ^ n, ← pow_succ'ₓ]
    congr 1
    rw [mul_left_commₓ <| (X - C t) ^ n, mul_comm <| (X - C t) ^ n]
    
  have h : (derivative q * (X - C t) + q * ↑(n + 1)).eval t ≠ 0 := by
    suffices eval t q * ↑(n + 1) ≠ 0 by
      simpa
    refine' mul_ne_zero _ (nat.cast_ne_zero.mpr n.succ_ne_zero)
    convert eval_div_by_monic_pow_root_multiplicity_ne_zero t hp
    exact hn ▸ hq
  rw [root_multiplicity_mul, root_multiplicity_X_sub_C_pow, root_multiplicity_eq_zero h, add_zeroₓ]
  refine' mul_ne_zero (pow_ne_zero n <| X_sub_C_ne_zero t) _
  contrapose! h
  rw [h, eval_zero]

theorem root_multiplicity_sub_one_le_derivative_root_multiplicity [CharZero R] (p : R[X]) (t : R) :
    p.rootMultiplicity t - 1 ≤ p.derivative.rootMultiplicity t := by
  by_cases' p.is_root t
  · exact (derivative_root_multiplicity_of_root h).symm.le
    
  · rw [root_multiplicity_eq_zero h, zero_tsub]
    exact zero_le _
    

section NormalizationMonoid

variable [NormalizationMonoid R]

instance : NormalizationMonoid R[X] where
  normUnit := fun p =>
    ⟨c ↑(normUnit p.leadingCoeff), c ↑(normUnit p.leadingCoeff)⁻¹, by
      rw [← RingHom.map_mul, Units.mul_inv, C_1], by
      rw [← RingHom.map_mul, Units.inv_mul, C_1]⟩
  norm_unit_zero :=
    Units.ext
      (by
        simp )
  norm_unit_mul := fun p q hp0 hq0 =>
    Units.ext
      (by
        dsimp'
        rw [Ne.def, ← leading_coeff_eq_zero] at *
        rw [leading_coeff_mul, norm_unit_mul hp0 hq0, Units.coe_mul, C_mul])
  norm_unit_coe_units := fun u =>
    Units.ext
      (by
        rw [← mul_oneₓ u⁻¹, Units.coe_mul, Units.eq_inv_mul_iff_mul_eq]
        dsimp'
        rcases Polynomial.is_unit_iff.1 ⟨u, rfl⟩ with ⟨_, ⟨w, rfl⟩, h2⟩
        rw [← h2, leading_coeff_C, norm_unit_coe_units, ← C_mul, Units.mul_inv, C_1])

@[simp]
theorem coe_norm_unit {p : R[X]} : (normUnit p : R[X]) = c ↑(normUnit p.leadingCoeff) := by
  simp [← norm_unit]

theorem leading_coeff_normalize (p : R[X]) : leadingCoeff (normalize p) = normalize (leadingCoeff p) := by
  simp

theorem Monic.normalize_eq_self {p : R[X]} (hp : p.Monic) : normalize p = p := by
  simp only [← Polynomial.coe_norm_unit, ← normalize_apply, ← hp.leading_coeff, ← norm_unit_one, ← Units.coe_one, ←
    polynomial.C.map_one, ← mul_oneₓ]

theorem roots_normalize {p : R[X]} : (normalize p).roots = p.roots := by
  rw [normalize_apply, mul_comm, coe_norm_unit, roots_C_mul _ (norm_unit (leading_coeff p)).ne_zero]

end NormalizationMonoid

end IsDomain

section DivisionRing

variable [DivisionRing R] {p q : R[X]}

theorem degree_pos_of_ne_zero_of_nonunit (hp0 : p ≠ 0) (hp : ¬IsUnit p) : 0 < degree p :=
  lt_of_not_geₓ fun h => by
    rw [eq_C_of_degree_le_zero h] at hp0 hp
    exact
      hp
        (IsUnit.map C
          (IsUnit.mk0 (coeff p 0)
            (mt C_inj.2
              (by
                simpa using hp0))))

theorem monic_mul_leading_coeff_inv (h : p ≠ 0) : Monic (p * c (leadingCoeff p)⁻¹) := by
  rw [monic, leading_coeff_mul, leading_coeff_C,
    mul_inv_cancel (show leading_coeff p ≠ 0 from mt leading_coeff_eq_zero.1 h)]

theorem degree_mul_leading_coeff_inv (p : R[X]) (h : q ≠ 0) : degree (p * c (leadingCoeff q)⁻¹) = degree p := by
  have h₁ : (leadingCoeff q)⁻¹ ≠ 0 := inv_ne_zero (mt leading_coeff_eq_zero.1 h)
  rw [degree_mul, degree_C h₁, add_zeroₓ]

@[simp]
theorem map_eq_zero [Semiringₓ S] [Nontrivial S] (f : R →+* S) : p.map f = 0 ↔ p = 0 := by
  simp only [← Polynomial.ext_iff, ← f.map_eq_zero, ← coeff_map, ← coeff_zero]

theorem map_ne_zero [Semiringₓ S] [Nontrivial S] {f : R →+* S} (hp : p ≠ 0) : p.map f ≠ 0 :=
  mt (map_eq_zero f).1 hp

end DivisionRing

section Field

variable [Field R] {p q : R[X]}

theorem is_unit_iff_degree_eq_zero : IsUnit p ↔ degree p = 0 :=
  ⟨degree_eq_zero_of_is_unit, fun h =>
    have : degree p ≤ 0 := by
      simp [*, ← le_reflₓ]
    have hc : coeff p 0 ≠ 0 := fun hc => by
      rw [eq_C_of_degree_le_zero this, hc] at h <;> simpa using h
    is_unit_iff_dvd_one.2
      ⟨c (coeff p 0)⁻¹, by
        conv in p => rw [eq_C_of_degree_le_zero this]
        rw [← C_mul, _root_.mul_inv_cancel hc, C_1]⟩⟩

theorem irreducible_of_monic {p : R[X]} (hp1 : p.Monic) (hp2 : p ≠ 1) :
    Irreducible p ↔ ∀ f g : R[X], f.Monic → g.Monic → f * g = p → f = 1 ∨ g = 1 :=
  ⟨fun hp3 f g hf hg hfg =>
    Or.cases_on (hp3.is_unit_or_is_unit hfg.symm) (fun huf : IsUnit f => Or.inl <| eq_one_of_is_unit_of_monic hf huf)
      fun hug : IsUnit g => Or.inr <| eq_one_of_is_unit_of_monic hg hug,
    fun hp3 =>
    ⟨mt (eq_one_of_is_unit_of_monic hp1) hp2, fun f g hp =>
      have hf : f ≠ 0 := fun hf => by
        rw [hp, hf, zero_mul] at hp1
        exact not_monic_zero hp1
      have hg : g ≠ 0 := fun hg => by
        rw [hp, hg, mul_zero] at hp1
        exact not_monic_zero hp1
      (Or.imp (fun hf => is_unit_of_mul_eq_one _ _ hf) fun hg => is_unit_of_mul_eq_one _ _ hg) <|
        hp3 (f * c f.leadingCoeff⁻¹) (g * c g.leadingCoeff⁻¹) (monic_mul_leading_coeff_inv hf)
            (monic_mul_leading_coeff_inv hg) <|
          by
          rw [mul_assoc, mul_left_commₓ _ g, ← mul_assoc, ← C_mul, ← mul_inv, ← leading_coeff_mul, ← hp,
            monic.def.1 hp1, inv_one, C_1, mul_oneₓ]⟩⟩

/-- Division of polynomials. See `polynomial.div_by_monic` for more details.-/
def div (p q : R[X]) :=
  c (leadingCoeff q)⁻¹ * (p /ₘ (q * c (leadingCoeff q)⁻¹))

/-- Remainder of polynomial division. See `polynomial.mod_by_monic` for more details. -/
def mod (p q : R[X]) :=
  p %ₘ (q * c (leadingCoeff q)⁻¹)

private theorem quotient_mul_add_remainder_eq_aux (p q : R[X]) : q * div p q + mod p q = p :=
  if h : q = 0 then by
    simp only [← h, ← zero_mul, ← mod, ← mod_by_monic_zero, ← zero_addₓ]
  else by
    conv => rhs rw [← mod_by_monic_add_div p (monic_mul_leading_coeff_inv h)]
    rw [div, mod, add_commₓ, mul_assoc]

private theorem remainder_lt_aux (p : R[X]) (hq : q ≠ 0) : degree (mod p q) < degree q := by
  rw [← degree_mul_leading_coeff_inv q hq] <;> exact degree_mod_by_monic_lt p (monic_mul_leading_coeff_inv hq)

instance : Div R[X] :=
  ⟨div⟩

instance : Mod R[X] :=
  ⟨mod⟩

theorem div_def : p / q = c (leadingCoeff q)⁻¹ * (p /ₘ (q * c (leadingCoeff q)⁻¹)) :=
  rfl

theorem mod_def : p % q = p %ₘ (q * c (leadingCoeff q)⁻¹) :=
  rfl

theorem mod_by_monic_eq_mod (p : R[X]) (hq : Monic q) : p %ₘ q = p % q :=
  show p %ₘ q = p %ₘ (q * c (leadingCoeff q)⁻¹) by
    simp only [← monic.def.1 hq, ← inv_one, ← mul_oneₓ, ← C_1]

theorem div_by_monic_eq_div (p : R[X]) (hq : Monic q) : p /ₘ q = p / q :=
  show p /ₘ q = c (leadingCoeff q)⁻¹ * (p /ₘ (q * c (leadingCoeff q)⁻¹)) by
    simp only [← monic.def.1 hq, ← inv_one, ← C_1, ← one_mulₓ, ← mul_oneₓ]

theorem mod_X_sub_C_eq_C_eval (p : R[X]) (a : R) : p % (X - c a) = c (p.eval a) :=
  mod_by_monic_eq_mod p (monic_X_sub_C a) ▸ mod_by_monic_X_sub_C_eq_C_eval _ _

theorem mul_div_eq_iff_is_root : (X - c a) * (p / (X - c a)) = p ↔ IsRoot p a :=
  div_by_monic_eq_div p (monic_X_sub_C a) ▸ mul_div_by_monic_eq_iff_is_root

instance : EuclideanDomain R[X] :=
  { Polynomial.commRing, Polynomial.nontrivial with Quotient := (· / ·),
    quotient_zero := by
      simp [← div_def],
    remainder := (· % ·), R := _, r_well_founded := degree_lt_wf,
    quotient_mul_add_remainder_eq := quotient_mul_add_remainder_eq_aux,
    remainder_lt := fun p q hq => remainder_lt_aux _ hq,
    mul_left_not_lt := fun p q hq => not_lt_of_geₓ (degree_le_mul_left _ hq) }

theorem mod_eq_self_iff (hq0 : q ≠ 0) : p % q = p ↔ degree p < degree q :=
  ⟨fun h => h ▸ EuclideanDomain.mod_lt _ hq0, fun h => by
    have : ¬degree (q * c (leadingCoeff q)⁻¹) ≤ degree p :=
      not_le_of_gtₓ <| by
        rwa [degree_mul_leading_coeff_inv q hq0]
    rw [mod_def, mod_by_monic, dif_pos (monic_mul_leading_coeff_inv hq0)]
    unfold div_mod_by_monic_aux
    simp only [← this, ← false_andₓ, ← if_false]⟩

theorem div_eq_zero_iff (hq0 : q ≠ 0) : p / q = 0 ↔ degree p < degree q :=
  ⟨fun h => by
    have := EuclideanDomain.div_add_mod p q <;> rwa [h, mul_zero, zero_addₓ, mod_eq_self_iff hq0] at this, fun h => by
    have hlt : degree p < degree (q * c (leadingCoeff q)⁻¹) := by
      rwa [degree_mul_leading_coeff_inv q hq0]
    have hm : Monic (q * c (leadingCoeff q)⁻¹) := monic_mul_leading_coeff_inv hq0
    rw [div_def, (div_by_monic_eq_zero_iff hm).2 hlt, mul_zero]⟩

theorem degree_add_div (hq0 : q ≠ 0) (hpq : degree q ≤ degree p) : degree q + degree (p / q) = degree p := by
  have : degree (p % q) < degree (q * (p / q)) :=
    calc
      degree (p % q) < degree q := EuclideanDomain.mod_lt _ hq0
      _ ≤ _ := degree_le_mul_left _ (mt (div_eq_zero_iff hq0).1 (not_lt_of_geₓ hpq))
      
  conv_rhs => rw [← EuclideanDomain.div_add_mod p q, degree_add_eq_left_of_degree_lt this, degree_mul]

theorem degree_div_le (p q : R[X]) : degree (p / q) ≤ degree p :=
  if hq : q = 0 then by
    simp [← hq]
  else by
    rw [div_def, mul_comm, degree_mul_leading_coeff_inv _ hq] <;> exact degree_div_by_monic_le _ _

theorem degree_div_lt (hp : p ≠ 0) (hq : 0 < degree q) : degree (p / q) < degree p := by
  have hq0 : q ≠ 0 := fun hq0 => by
    simpa [← hq0] using hq
  rw [div_def, mul_comm, degree_mul_leading_coeff_inv _ hq0] <;>
    exact
      degree_div_by_monic_lt _ (monic_mul_leading_coeff_inv hq0) hp
        (by
          rw [degree_mul_leading_coeff_inv _ hq0] <;> exact hq)

@[simp]
theorem degree_map [DivisionRing k] (p : R[X]) (f : R →+* k) : degree (p.map f) = degree p :=
  p.degree_map_eq_of_injective f.Injective

@[simp]
theorem nat_degree_map [DivisionRing k] (f : R →+* k) : natDegree (p.map f) = natDegree p :=
  nat_degree_eq_of_degree_eq (degree_map _ f)

@[simp]
theorem leading_coeff_map [DivisionRing k] (f : R →+* k) : leadingCoeff (p.map f) = f (leadingCoeff p) := by
  simp only [coeff_nat_degree, ← coeff_map f, ← nat_degree_map]

theorem monic_map_iff [DivisionRing k] {f : R →+* k} {p : R[X]} : (p.map f).Monic ↔ p.Monic := by
  rw [monic, leading_coeff_map, ← f.map_one, Function.Injective.eq_iff f.injective, monic]

theorem is_unit_map [Field k] (f : R →+* k) : IsUnit (p.map f) ↔ IsUnit p := by
  simp_rw [is_unit_iff_degree_eq_zero, degree_map]

theorem map_div [Field k] (f : R →+* k) : (p / q).map f = p.map f / q.map f :=
  if hq0 : q = 0 then by
    simp [← hq0]
  else by
    rw [div_def, div_def, Polynomial.map_mul, map_div_by_monic f (monic_mul_leading_coeff_inv hq0)] <;>
      simp [← f.map_inv, ← coeff_map f]

theorem map_mod [Field k] (f : R →+* k) : (p % q).map f = p.map f % q.map f :=
  if hq0 : q = 0 then by
    simp [← hq0]
  else by
    rw [mod_def, mod_def, leading_coeff_map f, ← f.map_inv, ← map_C f, ← Polynomial.map_mul f,
      map_mod_by_monic f (monic_mul_leading_coeff_inv hq0)]

section

open EuclideanDomain

theorem gcd_map [Field k] (f : R →+* k) : gcd (p.map f) (q.map f) = (gcd p q).map f :=
  (Gcd.induction p q fun x => by
      simp_rw [Polynomial.map_zero, EuclideanDomain.gcd_zero_left])
    fun x y hx ih => by
    rw [gcd_val, ← map_mod, ih, ← gcd_val]

end

theorem eval₂_gcd_eq_zero [CommSemiringₓ k] {ϕ : R →+* k} {f g : R[X]} {α : k} (hf : f.eval₂ ϕ α = 0)
    (hg : g.eval₂ ϕ α = 0) : (EuclideanDomain.gcd f g).eval₂ ϕ α = 0 := by
  rw [EuclideanDomain.gcd_eq_gcd_ab f g, Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_mul, hf, hg,
    zero_mul, zero_mul, zero_addₓ]

theorem eval_gcd_eq_zero {f g : R[X]} {α : R} (hf : f.eval α = 0) (hg : g.eval α = 0) :
    (EuclideanDomain.gcd f g).eval α = 0 :=
  eval₂_gcd_eq_zero hf hg

theorem root_left_of_root_gcd [CommSemiringₓ k] {ϕ : R →+* k} {f g : R[X]} {α : k}
    (hα : (EuclideanDomain.gcd f g).eval₂ ϕ α = 0) : f.eval₂ ϕ α = 0 := by
  cases' EuclideanDomain.gcd_dvd_left f g with p hp
  rw [hp, Polynomial.eval₂_mul, hα, zero_mul]

theorem root_right_of_root_gcd [CommSemiringₓ k] {ϕ : R →+* k} {f g : R[X]} {α : k}
    (hα : (EuclideanDomain.gcd f g).eval₂ ϕ α = 0) : g.eval₂ ϕ α = 0 := by
  cases' EuclideanDomain.gcd_dvd_right f g with p hp
  rw [hp, Polynomial.eval₂_mul, hα, zero_mul]

theorem root_gcd_iff_root_left_right [CommSemiringₓ k] {ϕ : R →+* k} {f g : R[X]} {α : k} :
    (EuclideanDomain.gcd f g).eval₂ ϕ α = 0 ↔ f.eval₂ ϕ α = 0 ∧ g.eval₂ ϕ α = 0 :=
  ⟨fun h => ⟨root_left_of_root_gcd h, root_right_of_root_gcd h⟩, fun h => eval₂_gcd_eq_zero h.1 h.2⟩

theorem is_root_gcd_iff_is_root_left_right {f g : R[X]} {α : R} :
    (EuclideanDomain.gcd f g).IsRoot α ↔ f.IsRoot α ∧ g.IsRoot α :=
  root_gcd_iff_root_left_right

theorem is_coprime_map [Field k] (f : R →+* k) : IsCoprime (p.map f) (q.map f) ↔ IsCoprime p q := by
  rw [← EuclideanDomain.gcd_is_unit_iff, ← EuclideanDomain.gcd_is_unit_iff, gcd_map, is_unit_map]

theorem mem_roots_map [Field k] {f : R →+* k} {x : k} (hp : p ≠ 0) : x ∈ (p.map f).roots ↔ p.eval₂ f x = 0 := by
  rw [mem_roots (show p.map f ≠ 0 from map_ne_zero hp)]
  dsimp' only [← is_root]
  rw [Polynomial.eval_map]

theorem mem_root_set [Field k] [Algebra R k] {x : k} (hp : p ≠ 0) : x ∈ p.RootSet k ↔ aeval x p = 0 :=
  Iff.trans Multiset.mem_to_finset (mem_roots_map hp)

theorem root_set_C_mul_X_pow {R S : Type _} [Field R] [Field S] [Algebra R S] {n : ℕ} (hn : n ≠ 0) {a : R}
    (ha : a ≠ 0) : (c a * X ^ n).RootSet S = {0} := by
  ext x
  rw [Set.mem_singleton_iff, mem_root_set, aeval_mul, aeval_C, aeval_X_pow, mul_eq_zero]
  · simp_rw [RingHom.map_eq_zero, pow_eq_zero_iff (Nat.pos_of_ne_zeroₓ hn), or_iff_right_iff_imp]
    exact fun ha' => (ha ha').elim
    
  · exact mul_ne_zero (mt C_eq_zero.mp ha) (pow_ne_zero n X_ne_zero)
    

theorem root_set_monomial {R S : Type _} [Field R] [Field S] [Algebra R S] {n : ℕ} (hn : n ≠ 0) {a : R} (ha : a ≠ 0) :
    (monomial n a).RootSet S = {0} := by
  rw [← C_mul_X_pow_eq_monomial, root_set_C_mul_X_pow hn ha]

theorem root_set_X_pow {R S : Type _} [Field R] [Field S] [Algebra R S] {n : ℕ} (hn : n ≠ 0) :
    (X ^ n : R[X]).RootSet S = {0} := by
  rw [← one_mulₓ (X ^ n : R[X]), ← C_1, root_set_C_mul_X_pow hn]
  exact one_ne_zero

theorem exists_root_of_degree_eq_one (h : degree p = 1) : ∃ x, IsRoot p x :=
  ⟨-(p.coeff 0 / p.coeff 1), by
    have : p.coeff 1 ≠ 0 := by
      rw [← nat_degree_eq_of_degree_eq_some h] <;>
        exact
          mt leading_coeff_eq_zero.1 fun h0 => by
            simpa [← h0] using h
    conv in p =>
        rw
          [eq_X_add_C_of_degree_le_one
            (show degree p ≤ 1 by
              rw [h] <;> exact le_rfl)] <;>
      simp [← is_root, ← mul_div_cancel' _ this]⟩

theorem coeff_inv_units (u : R[X]ˣ) (n : ℕ) : ((↑u : R[X]).coeff n)⁻¹ = (↑u⁻¹ : R[X]).coeff n := by
  rw [eq_C_of_degree_eq_zero (degree_coe_units u), eq_C_of_degree_eq_zero (degree_coe_units u⁻¹), coeff_C, coeff_C,
    inv_eq_one_div]
  split_ifs
  · rw [div_eq_iff_mul_eq (coeff_coe_units_zero_ne_zero u), coeff_zero_eq_eval_zero, coeff_zero_eq_eval_zero, ←
        eval_mul, ← Units.coe_mul, inv_mul_selfₓ] <;>
      simp
    
  · simp
    

theorem monic_normalize (hp0 : p ≠ 0) : Monic (normalize p) := by
  rw [Ne.def, ← leading_coeff_eq_zero, ← Ne.def, ← is_unit_iff_ne_zero] at hp0
  rw [monic, leading_coeff_normalize, normalize_eq_one]
  apply hp0

theorem leading_coeff_div (hpq : q.degree ≤ p.degree) : (p / q).leadingCoeff = p.leadingCoeff / q.leadingCoeff := by
  by_cases' hq : q = 0
  · simp [← hq]
    
  rw [div_def, leading_coeff_mul, leading_coeff_C,
    leading_coeff_div_by_monic_of_monic (monic_mul_leading_coeff_inv hq) _, mul_comm, div_eq_mul_inv]
  rwa [degree_mul_leading_coeff_inv q hq]

theorem div_C_mul : p / (c a * q) = c a⁻¹ * (p / q) := by
  by_cases' ha : a = 0
  · simp [← ha]
    
  simp only [← div_def, ← leading_coeff_mul, ← mul_inv, ← leading_coeff_C, ← C.map_mul, ← mul_assoc]
  congr 3
  rw [mul_left_commₓ q, ← mul_assoc, ← C.map_mul, mul_inv_cancel ha, C.map_one, one_mulₓ]

theorem C_mul_dvd (ha : a ≠ 0) : c a * p ∣ q ↔ p ∣ q :=
  ⟨fun h => dvd_trans (dvd_mul_left _ _) h, fun ⟨r, hr⟩ =>
    ⟨c a⁻¹ * r, by
      rw [mul_assoc, mul_left_commₓ p, ← mul_assoc, ← C.map_mul, _root_.mul_inv_cancel ha, C.map_one, one_mulₓ, hr]⟩⟩

theorem dvd_C_mul (ha : a ≠ 0) : p ∣ Polynomial.c a * q ↔ p ∣ q :=
  ⟨fun ⟨r, hr⟩ =>
    ⟨c a⁻¹ * r, by
      rw [mul_left_commₓ p, ← hr, ← mul_assoc, ← C.map_mul, _root_.inv_mul_cancel ha, C.map_one, one_mulₓ]⟩,
    fun h => dvd_trans h (dvd_mul_left _ _)⟩

theorem coe_norm_unit_of_ne_zero (hp : p ≠ 0) : (normUnit p : R[X]) = c p.leadingCoeff⁻¹ := by
  have : p.leadingCoeff ≠ 0 := mt leading_coeff_eq_zero.mp hp
  simp [← CommGroupWithZero.coe_norm_unit _ this]

theorem normalize_monic (h : Monic p) : normalize p = p := by
  simp [← h]

theorem map_dvd_map' [Field k] (f : R →+* k) {x y : R[X]} : x.map f ∣ y.map f ↔ x ∣ y :=
  if H : x = 0 then by
    rw [H, Polynomial.map_zero, zero_dvd_iff, zero_dvd_iff, map_eq_zero]
  else by
    rw [← normalize_dvd_iff, ← @normalize_dvd_iff R[X], normalize_apply, normalize_apply, coe_norm_unit_of_ne_zero H,
      coe_norm_unit_of_ne_zero (mt (map_eq_zero f).1 H), leading_coeff_map, ← f.map_inv, ← map_C, ← Polynomial.map_mul,
      map_dvd_map _ f.injective (monic_mul_leading_coeff_inv H)]

theorem degree_normalize : degree (normalize p) = degree p := by
  simp

theorem prime_of_degree_eq_one (hp1 : degree p = 1) : Prime p :=
  have : Prime (normalize p) :=
    Monic.prime_of_degree_eq_one (hp1 ▸ degree_normalize)
      (monic_normalize fun hp0 =>
        absurd hp1
          (hp0.symm ▸ by
            simp <;>
              exact by
                decide))
  (normalize_associated _).Prime this

theorem irreducible_of_degree_eq_one (hp1 : degree p = 1) : Irreducible p :=
  (prime_of_degree_eq_one hp1).Irreducible

theorem not_irreducible_C (x : R) : ¬Irreducible (c x) :=
  if H : x = 0 then by
    rw [H, C_0]
    exact not_irreducible_zero
  else fun hx => Irreducible.not_unit hx <| is_unit_C.2 <| is_unit_iff_ne_zero.2 H

theorem degree_pos_of_irreducible (hp : Irreducible p) : 0 < p.degree :=
  lt_of_not_geₓ fun hp0 =>
    have := eq_C_of_degree_le_zero hp0
    not_irreducible_C (p.coeff 0) <| this ▸ hp

/-- If `f` is a polynomial over a field, and `a : K` satisfies `f' a ≠ 0`,
then `f / (X - a)` is coprime with `X - a`.
Note that we do not assume `f a = 0`, because `f / (X - a) = (f - f a) / (X - a)`. -/
theorem is_coprime_of_is_root_of_eval_derivative_ne_zero {K : Type _} [Field K] (f : K[X]) (a : K)
    (hf' : f.derivative.eval a ≠ 0) : IsCoprime (X - c a : K[X]) (f /ₘ (X - c a)) := by
  refine'
    Or.resolve_left
      (EuclideanDomain.dvd_or_coprime (X - C a) (f /ₘ (X - C a))
        (irreducible_of_degree_eq_one (Polynomial.degree_X_sub_C a)))
      _
  contrapose! hf' with h
  have key : (X - C a) * (f /ₘ (X - C a)) = f - f %ₘ (X - C a) := by
    rw [eq_sub_iff_add_eq, ← eq_sub_iff_add_eq', mod_by_monic_eq_sub_mul_div]
    exact monic_X_sub_C a
  replace key := congr_arg derivative key
  simp only [← derivative_X, ← derivative_mul, ← one_mulₓ, ← sub_zero, ← derivative_sub, ←
    mod_by_monic_X_sub_C_eq_C_eval, ← derivative_C] at key
  have : X - C a ∣ derivative f := key ▸ dvd_add h (dvd_mul_right _ _)
  rw [← dvd_iff_mod_by_monic_eq_zero (monic_X_sub_C _), mod_by_monic_X_sub_C_eq_C_eval] at this
  rw [← C_inj, this, C_0]

end Field

end Polynomial

