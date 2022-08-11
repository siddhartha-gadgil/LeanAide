/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Scott Morrison, Jens Wagemaker, Johan Commelin
-/
import Mathbin.Data.Polynomial.AlgebraMap
import Mathbin.Data.Polynomial.Degree.Lemmas
import Mathbin.Data.Polynomial.Div
import Mathbin.RingTheory.Localization.FractionRing
import Mathbin.Algebra.Polynomial.BigOperators

/-!
# Theory of univariate polynomials

This file starts looking like the ring theory of $ R[X] $

-/


noncomputable section

open Classical Polynomial

open Finset

namespace Polynomial

universe u v w z

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

section CommRingₓ

variable [CommRingₓ R] {p q : R[X]}

section

variable [Semiringₓ S]

theorem nat_degree_pos_of_aeval_root [Algebra R S] {p : R[X]} (hp : p ≠ 0) {z : S} (hz : aeval z p = 0)
    (inj : ∀ x : R, algebraMap R S x = 0 → x = 0) : 0 < p.natDegree :=
  nat_degree_pos_of_eval₂_root hp (algebraMap R S) hz inj

theorem degree_pos_of_aeval_root [Algebra R S] {p : R[X]} (hp : p ≠ 0) {z : S} (hz : aeval z p = 0)
    (inj : ∀ x : R, algebraMap R S x = 0 → x = 0) : 0 < p.degree :=
  nat_degree_pos_iff_degree_pos.mp (nat_degree_pos_of_aeval_root hp hz inj)

theorem mod_by_monic_eq_of_dvd_sub (hq : q.Monic) {p₁ p₂ : R[X]} (h : q ∣ p₁ - p₂) : p₁ %ₘ q = p₂ %ₘ q := by
  nontriviality R
  obtain ⟨f, sub_eq⟩ := h
  refine' (div_mod_by_monic_unique (p₂ /ₘ q + f) _ hq ⟨_, degree_mod_by_monic_lt _ hq⟩).2
  rw [sub_eq_iff_eq_add.mp sub_eq, mul_addₓ, ← add_assocₓ, mod_by_monic_add_div _ hq, add_commₓ]

theorem add_mod_by_monic (p₁ p₂ : R[X]) : (p₁ + p₂) %ₘ q = p₁ %ₘ q + p₂ %ₘ q := by
  by_cases' hq : q.monic
  · nontriviality R
    exact
      (div_mod_by_monic_unique (p₁ /ₘ q + p₂ /ₘ q) _ hq
          ⟨by
            rw [mul_addₓ, add_left_commₓ, add_assocₓ, mod_by_monic_add_div _ hq, ← add_assocₓ, add_commₓ (q * _),
              mod_by_monic_add_div _ hq],
            (degree_add_le _ _).trans_lt (max_ltₓ (degree_mod_by_monic_lt _ hq) (degree_mod_by_monic_lt _ hq))⟩).2
    
  · simp_rw [mod_by_monic_eq_of_not_monic _ hq]
    

theorem smul_mod_by_monic (c : R) (p : R[X]) : c • p %ₘ q = c • (p %ₘ q) := by
  by_cases' hq : q.monic
  · nontriviality R
    exact
      (div_mod_by_monic_unique (c • (p /ₘ q)) (c • (p %ₘ q)) hq
          ⟨by
            rw [mul_smul_comm, ← smul_add, mod_by_monic_add_div p hq],
            (degree_smul_le _ _).trans_lt (degree_mod_by_monic_lt _ hq)⟩).2
    
  · simp_rw [mod_by_monic_eq_of_not_monic _ hq]
    

/-- `_ %ₘ q` as an `R`-linear map. -/
@[simps]
def modByMonicHom (q : R[X]) : R[X] →ₗ[R] R[X] where
  toFun := fun p => p %ₘ q
  map_add' := add_mod_by_monic
  map_smul' := smul_mod_by_monic

end

section

variable [Ringₓ S]

theorem aeval_mod_by_monic_eq_self_of_root [Algebra R S] {p q : R[X]} (hq : q.Monic) {x : S} (hx : aeval x q = 0) :
    aeval x (p %ₘ q) = aeval x p := by
  -- `eval₂_mod_by_monic_eq_self_of_root` doesn't work here as it needs commutativity
  rw [mod_by_monic_eq_sub_mul_div p hq, _root_.map_sub, _root_.map_mul, hx, zero_mul, sub_zero]

end

end CommRingₓ

section NoZeroDivisors

variable [Semiringₓ R] [NoZeroDivisors R] {p q : R[X]}

instance :
    NoZeroDivisors R[X] where eq_zero_or_eq_zero_of_mul_eq_zero := fun a b h => by
    rw [← leading_coeff_eq_zero, ← leading_coeff_eq_zero]
    refine' eq_zero_or_eq_zero_of_mul_eq_zero _
    rw [← leading_coeff_zero, ← leading_coeff_mul, h]

theorem nat_degree_mul (hp : p ≠ 0) (hq : q ≠ 0) : natDegree (p * q) = natDegree p + natDegree q := by
  rw [← WithBot.coe_eq_coe, ← degree_eq_nat_degree (mul_ne_zero hp hq), WithBot.coe_add, ← degree_eq_nat_degree hp, ←
    degree_eq_nat_degree hq, degree_mul]

theorem trailing_degree_mul : (p * q).trailingDegree = p.trailingDegree + q.trailingDegree := by
  by_cases' hp : p = 0
  · rw [hp, zero_mul, trailing_degree_zero, top_add]
    
  by_cases' hq : q = 0
  · rw [hq, mul_zero, trailing_degree_zero, add_top]
    
  rw [trailing_degree_eq_nat_trailing_degree hp, trailing_degree_eq_nat_trailing_degree hq,
    trailing_degree_eq_nat_trailing_degree (mul_ne_zero hp hq), nat_trailing_degree_mul hp hq, WithTop.coe_add]

@[simp]
theorem nat_degree_pow (p : R[X]) (n : ℕ) : natDegree (p ^ n) = n * natDegree p :=
  if hp0 : p = 0 then
    if hn0 : n = 0 then by
      simp [← hp0, ← hn0]
    else by
      rw [hp0, zero_pow (Nat.pos_of_ne_zeroₓ hn0)] <;> simp
  else
    nat_degree_pow'
      (by
        rw [← leading_coeff_pow, Ne.def, leading_coeff_eq_zero] <;> exact pow_ne_zero _ hp0)

theorem degree_le_mul_left (p : R[X]) (hq : q ≠ 0) : degree p ≤ degree (p * q) :=
  if hp : p = 0 then by
    simp only [← hp, ← zero_mul, ← le_reflₓ]
  else by
    rw [degree_mul, degree_eq_nat_degree hp, degree_eq_nat_degree hq] <;>
      exact WithBot.coe_le_coe.2 (Nat.le_add_rightₓ _ _)

theorem nat_degree_le_of_dvd {p q : R[X]} (h1 : p ∣ q) (h2 : q ≠ 0) : p.natDegree ≤ q.natDegree := by
  rcases h1 with ⟨q, rfl⟩
  rw [mul_ne_zero_iff] at h2
  rw [nat_degree_mul h2.1 h2.2]
  exact Nat.le_add_rightₓ _ _

/-- This lemma is useful for working with the `int_degree` of a rational function. -/
theorem nat_degree_sub_eq_of_prod_eq {p₁ p₂ q₁ q₂ : Polynomial R} (hp₁ : p₁ ≠ 0) (hq₁ : q₁ ≠ 0) (hp₂ : p₂ ≠ 0)
    (hq₂ : q₂ ≠ 0) (h_eq : p₁ * q₂ = p₂ * q₁) : (p₁.natDegree : ℤ) - q₁.natDegree = (p₂.natDegree : ℤ) - q₂.natDegree :=
  by
  rw [sub_eq_sub_iff_add_eq_add]
  norm_cast
  rw [← nat_degree_mul hp₁ hq₂, ← nat_degree_mul hp₂ hq₁, h_eq]

end NoZeroDivisors

section NoZeroDivisors

variable [CommSemiringₓ R] [NoZeroDivisors R] {p q : R[X]}

theorem root_mul : IsRoot (p * q) a ↔ IsRoot p a ∨ IsRoot q a := by
  simp_rw [is_root, eval_mul, mul_eq_zero]

theorem root_or_root_of_root_mul (h : IsRoot (p * q) a) : IsRoot p a ∨ IsRoot q a :=
  root_mul.1 h

end NoZeroDivisors

section Ringₓ

variable [Ringₓ R] [IsDomain R] {p q : R[X]}

instance : IsDomain R[X] :=
  { Polynomial.no_zero_divisors, Polynomial.nontrivial with }

end Ringₓ

section CommRingₓ

variable [CommRingₓ R] [IsDomain R] {p q : R[X]}

section Roots

open Multiset

theorem degree_eq_zero_of_is_unit (h : IsUnit p) : degree p = 0 := by
  let ⟨q, hq⟩ := is_unit_iff_dvd_one.1 h
  have hp0 : p ≠ 0 := fun hp0 => by
    simpa [← hp0] using hq
  have hq0 : q ≠ 0 := fun hp0 => by
    simpa [← hp0] using hq
  have : natDegree (1 : R[X]) = natDegree (p * q) := congr_arg _ hq
  rw [nat_degree_one, nat_degree_mul hp0 hq0, eq_comm, _root_.add_eq_zero_iff, ← WithBot.coe_eq_coe, ←
      degree_eq_nat_degree hp0] at this <;>
    exact this.1

@[simp]
theorem degree_coe_units (u : R[X]ˣ) : degree (u : R[X]) = 0 :=
  degree_eq_zero_of_is_unit ⟨u, rfl⟩

theorem prime_X_sub_C (r : R) : Prime (X - c r) :=
  ⟨X_sub_C_ne_zero r, not_is_unit_X_sub_C r, fun _ _ => by
    simp_rw [dvd_iff_is_root, is_root.def, eval_mul, mul_eq_zero]
    exact id⟩

theorem prime_X : Prime (x : R[X]) := by
  convert prime_X_sub_C (0 : R)
  simp

theorem Monic.prime_of_degree_eq_one (hp1 : degree p = 1) (hm : Monic p) : Prime p :=
  have : p = X - c (-p.coeff 0) := by
    simpa [← hm.leading_coeff] using eq_X_add_C_of_degree_eq_one hp1
  this.symm ▸ prime_X_sub_C _

theorem irreducible_X_sub_C (r : R) : Irreducible (X - c r) :=
  (prime_X_sub_C r).Irreducible

theorem irreducible_X : Irreducible (x : R[X]) :=
  Prime.irreducible prime_X

theorem Monic.irreducible_of_degree_eq_one (hp1 : degree p = 1) (hm : Monic p) : Irreducible p :=
  (hm.prime_of_degree_eq_one hp1).Irreducible

theorem eq_of_monic_of_associated (hp : p.Monic) (hq : q.Monic) (hpq : Associated p q) : p = q := by
  obtain ⟨u, hu⟩ := hpq
  unfold monic  at hp hq
  rw [eq_C_of_degree_le_zero (le_of_eqₓ <| degree_coe_units _)] at hu
  rw [← hu, leading_coeff_mul, hp, one_mulₓ, leading_coeff_C] at hq
  rwa [hq, C_1, mul_oneₓ] at hu
  infer_instance

theorem root_multiplicity_mul {p q : R[X]} {x : R} (hpq : p * q ≠ 0) :
    rootMultiplicity x (p * q) = rootMultiplicity x p + rootMultiplicity x q := by
  have hp : p ≠ 0 := left_ne_zero_of_mul hpq
  have hq : q ≠ 0 := right_ne_zero_of_mul hpq
  rw [root_multiplicity_eq_multiplicity (p * q), dif_neg hpq, root_multiplicity_eq_multiplicity p, dif_neg hp,
    root_multiplicity_eq_multiplicity q, dif_neg hq, multiplicity.mul' (prime_X_sub_C x)]

theorem root_multiplicity_X_sub_C_self {x : R} : rootMultiplicity x (X - c x) = 1 := by
  rw [root_multiplicity_eq_multiplicity, dif_neg (X_sub_C_ne_zero x), multiplicity.get_multiplicity_self]

theorem root_multiplicity_X_sub_C {x y : R} : rootMultiplicity x (X - c y) = if x = y then 1 else 0 := by
  split_ifs with hxy
  · rw [hxy]
    exact root_multiplicity_X_sub_C_self
    
  exact root_multiplicity_eq_zero (mt root_X_sub_C.mp (Ne.symm hxy))

/-- The multiplicity of `a` as root of `(X - a) ^ n` is `n`. -/
theorem root_multiplicity_X_sub_C_pow (a : R) (n : ℕ) : rootMultiplicity a ((X - c a) ^ n) = n := by
  induction' n with n hn
  · refine' root_multiplicity_eq_zero _
    simp only [← eval_one, ← is_root.def, ← not_false_iff, ← one_ne_zero, ← pow_zeroₓ]
    
  have hzero := pow_ne_zero n.succ (X_sub_C_ne_zero a)
  rw [pow_succₓ (X - C a) n] at hzero⊢
  simp only [← root_multiplicity_mul hzero, ← root_multiplicity_X_sub_C_self, ← hn, ← Nat.one_add]

/-- If `(X - a) ^ n` divides a polynomial `p` then the multiplicity of `a` as root of `p` is at
least `n`. -/
theorem root_multiplicity_of_dvd {p : R[X]} {a : R} {n : ℕ} (hzero : p ≠ 0) (h : (X - c a) ^ n ∣ p) :
    n ≤ rootMultiplicity a p := by
  obtain ⟨q, hq⟩ := exists_eq_mul_right_of_dvd h
  rw [hq] at hzero
  simp only [← hq, ← root_multiplicity_mul hzero, ← root_multiplicity_X_sub_C_pow, ← ge_iff_le, ← _root_.zero_le, ←
    le_add_iff_nonneg_right]

/-- The multiplicity of `p + q` is at least the minimum of the multiplicities. -/
theorem root_multiplicity_add {p q : R[X]} (a : R) (hzero : p + q ≠ 0) :
    min (rootMultiplicity a p) (rootMultiplicity a q) ≤ rootMultiplicity a (p + q) := by
  refine' root_multiplicity_of_dvd hzero _
  have hdivp : (X - C a) ^ root_multiplicity a p ∣ p := pow_root_multiplicity_dvd p a
  have hdivq : (X - C a) ^ root_multiplicity a q ∣ q := pow_root_multiplicity_dvd q a
  exact min_pow_dvd_add hdivp hdivq

theorem exists_multiset_roots :
    ∀ {p : R[X]} (hp : p ≠ 0), ∃ s : Multiset R, (s.card : WithBot ℕ) ≤ degree p ∧ ∀ a, s.count a = rootMultiplicity a p
  | p => fun hp =>
    have := Classical.propDecidable (∃ x, is_root p x)
    if h : ∃ x, is_root p x then
      let ⟨x, hx⟩ := h
      have hpd : 0 < degree p := degree_pos_of_root hp hx
      have hd0 : p /ₘ (X - C x) ≠ 0 := fun h => by
        rw [← mul_div_by_monic_eq_iff_is_root.2 hx, h, mul_zero] at hp <;> exact hp rfl
      have wf : degree (p /ₘ _) < degree p :=
        degree_div_by_monic_lt _ (monic_X_sub_C x) hp
          ((degree_X_sub_C x).symm ▸ by
            decide)
      let ⟨t, htd, htr⟩ := @exists_multiset_roots (p /ₘ (X - C x)) hd0
      have hdeg : degree (X - C x) ≤ degree p := by
        rw [degree_X_sub_C, degree_eq_nat_degree hp]
        rw [degree_eq_nat_degree hp] at hpd
        exact WithBot.coe_le_coe.2 (WithBot.coe_lt_coe.1 hpd)
      have hdiv0 : p /ₘ (X - C x) ≠ 0 := mt (div_by_monic_eq_zero_iff (monic_X_sub_C x)).1 <| not_ltₓ.2 hdeg
      ⟨x ::ₘ t,
        calc
          (card (x ::ₘ t) : WithBot ℕ) = t.card + 1 := by
            exact_mod_cast card_cons _ _
          _ ≤ degree p := by
            rw [← degree_add_div_by_monic (monic_X_sub_C x) hdeg, degree_X_sub_C, add_commₓ] <;>
              exact add_le_add (le_reflₓ (1 : WithBot ℕ)) htd
          ,
        by
        intro a
        conv_rhs => rw [← mul_div_by_monic_eq_iff_is_root.mpr hx]
        rw [root_multiplicity_mul (mul_ne_zero (X_sub_C_ne_zero x) hdiv0), root_multiplicity_X_sub_C, ← htr a]
        split_ifs with ha
        · rw [ha, count_cons_self, Nat.succ_eq_add_one, add_commₓ]
          
        · rw [count_cons_of_ne ha, zero_addₓ]
          ⟩
    else
      ⟨0, (degree_eq_nat_degree hp).symm ▸ WithBot.coe_le_coe.2 (Nat.zero_leₓ _), by
        intro a
        rw [count_zero, root_multiplicity_eq_zero (not_exists.mp h a)]⟩

/-- `roots p` noncomputably gives a multiset containing all the roots of `p`,
including their multiplicities. -/
noncomputable def roots (p : R[X]) : Multiset R :=
  if h : p = 0 then ∅ else Classical.some (exists_multiset_roots h)

@[simp]
theorem roots_zero : (0 : R[X]).roots = 0 :=
  dif_pos rfl

theorem card_roots (hp0 : p ≠ 0) : ((roots p).card : WithBot ℕ) ≤ degree p := by
  unfold roots
  rw [dif_neg hp0]
  exact (Classical.some_spec (exists_multiset_roots hp0)).1

theorem card_roots' (p : R[X]) : p.roots.card ≤ natDegree p := by
  by_cases' hp0 : p = 0
  · simp [← hp0]
    
  exact WithBot.coe_le_coe.1 (le_transₓ (card_roots hp0) (le_of_eqₓ <| degree_eq_nat_degree hp0))

theorem card_roots_sub_C {p : R[X]} {a : R} (hp0 : 0 < degree p) : ((p - c a).roots.card : WithBot ℕ) ≤ degree p :=
  calc
    ((p - c a).roots.card : WithBot ℕ) ≤ degree (p - c a) :=
      card_roots <| (mt sub_eq_zero.1) fun h => not_le_of_gtₓ hp0 <| h.symm ▸ degree_C_le
    _ = degree p := by
      rw [sub_eq_add_neg, ← C_neg] <;> exact degree_add_C hp0
    

theorem card_roots_sub_C' {p : R[X]} {a : R} (hp0 : 0 < degree p) : (p - c a).roots.card ≤ natDegree p :=
  WithBot.coe_le_coe.1
    (le_transₓ (card_roots_sub_C hp0)
      (le_of_eqₓ <|
        degree_eq_nat_degree fun h => by
          simp_all [← lt_irreflₓ]))

@[simp]
theorem count_roots (p : R[X]) : p.roots.count a = rootMultiplicity a p := by
  by_cases' hp : p = 0
  · simp [← hp]
    
  rw [roots, dif_neg hp]
  exact (Classical.some_spec (exists_multiset_roots hp)).2 a

@[simp]
theorem mem_roots (hp : p ≠ 0) : a ∈ p.roots ↔ IsRoot p a := by
  rw [← count_pos, count_roots p, root_multiplicity_pos hp]

theorem card_le_degree_of_subset_roots {p : R[X]} {Z : Finset R} (h : Z.val ⊆ p.roots) : Z.card ≤ p.natDegree :=
  (Multiset.card_le_of_le (Finset.val_le_iff_val_subset.2 h)).trans (Polynomial.card_roots' p)

theorem finite_set_of_is_root {p : R[X]} (hp : p ≠ 0) : Set.Finite { x | IsRoot p x } := by
  simpa only [Finset.set_of_mem, ← mem_to_finset, ← mem_roots hp] using p.roots.to_finset.finite_to_set

theorem eq_zero_of_infinite_is_root (p : R[X]) (h : Set.Infinite { x | IsRoot p x }) : p = 0 :=
  not_imp_comm.mp finite_set_of_is_root h

theorem exists_max_root [LinearOrderₓ R] (p : R[X]) (hp : p ≠ 0) : ∃ x₀, ∀ x, p.IsRoot x → x ≤ x₀ :=
  Set.exists_upper_bound_image _ _ <| finite_set_of_is_root hp

theorem exists_min_root [LinearOrderₓ R] (p : R[X]) (hp : p ≠ 0) : ∃ x₀, ∀ x, p.IsRoot x → x₀ ≤ x :=
  Set.exists_lower_bound_image _ _ <| finite_set_of_is_root hp

theorem eq_of_infinite_eval_eq (p q : R[X]) (h : Set.Infinite { x | eval x p = eval x q }) : p = q := by
  rw [← sub_eq_zero]
  apply eq_zero_of_infinite_is_root
  simpa only [← is_root, ← eval_sub, ← sub_eq_zero]

theorem roots_mul {p q : R[X]} (hpq : p * q ≠ 0) : (p * q).roots = p.roots + q.roots :=
  Multiset.ext.mpr fun r => by
    rw [count_add, count_roots, count_roots, count_roots, root_multiplicity_mul hpq]

theorem roots.le_of_dvd (h : q ≠ 0) : p ∣ q → roots p ≤ roots q := by
  rintro ⟨k, rfl⟩
  exact multiset.le_iff_exists_add.mpr ⟨k.roots, roots_mul h⟩

@[simp]
theorem mem_roots_sub_C {p : R[X]} {a x : R} (hp0 : 0 < degree p) : x ∈ (p - c a).roots ↔ p.eval x = a :=
  (mem_roots (show p - c a ≠ 0 from (mt sub_eq_zero.1) fun h => not_le_of_gtₓ hp0 <| h.symm ▸ degree_C_le)).trans
    (by
      rw [is_root.def, eval_sub, eval_C, sub_eq_zero])

@[simp]
theorem roots_X_sub_C (r : R) : roots (X - c r) = {r} := by
  ext s
  rw [count_roots, root_multiplicity_X_sub_C]
  split_ifs with h
  · rw [h, count_singleton_self]
    
  · rw [singleton_eq_cons, count_cons_of_ne h, count_zero]
    

@[simp]
theorem roots_C (x : R) : (c x).roots = 0 :=
  if H : x = 0 then by
    rw [H, C_0, roots_zero]
  else
    Multiset.ext.mpr fun r => by
      rw [count_roots, count_zero, root_multiplicity_eq_zero (not_is_root_C _ _ H)]

@[simp]
theorem roots_one : (1 : R[X]).roots = ∅ :=
  roots_C 1

theorem roots_smul_nonzero (p : R[X]) {r : R} (hr : r ≠ 0) : (r • p).roots = p.roots := by
  by_cases' hp : p = 0 <;> simp [← smul_eq_C_mul, ← roots_mul, ← hr, ← hp]

theorem roots_list_prod (L : List R[X]) : (0 : R[X]) ∉ L → L.Prod.roots = (L : Multiset R[X]).bind roots :=
  (List.recOn L fun _ => roots_one) fun hd tl ih H => by
    rw [List.mem_cons_iff, not_or_distrib] at H
    rw [List.prod_cons, roots_mul (mul_ne_zero (Ne.symm H.1) <| List.prod_ne_zero H.2), ← Multiset.cons_coe,
      Multiset.cons_bind, ih H.2]

theorem roots_multiset_prod (m : Multiset R[X]) : (0 : R[X]) ∉ m → m.Prod.roots = m.bind roots := by
  rcases m with ⟨L⟩
  simpa only [← Multiset.coe_prod, ← quot_mk_to_coe''] using roots_list_prod L

theorem roots_prod {ι : Type _} (f : ι → R[X]) (s : Finset ι) :
    s.Prod f ≠ 0 → (s.Prod f).roots = s.val.bind fun i => roots (f i) := by
  rcases s with ⟨m, hm⟩
  simpa [← Multiset.prod_eq_zero_iff, ← bind_map] using roots_multiset_prod (m.map f)

theorem roots_prod_X_sub_C (s : Finset R) : (s.Prod fun a => X - c a).roots = s.val :=
  (roots_prod (fun a => X - c a) s (prod_ne_zero_iff.mpr fun a _ => X_sub_C_ne_zero a)).trans
    (by
      simp_rw [roots_X_sub_C, Multiset.bind_singleton, Multiset.map_id'])

@[simp]
theorem roots_multiset_prod_X_sub_C (s : Multiset R) : (s.map fun a => X - c a).Prod.roots = s := by
  rw [roots_multiset_prod, Multiset.bind_map]
  · simp_rw [roots_X_sub_C, Multiset.bind_singleton, Multiset.map_id']
    
  · rw [Multiset.mem_map]
    rintro ⟨a, -, h⟩
    exact X_sub_C_ne_zero a h
    

@[simp]
theorem nat_degree_multiset_prod_X_sub_C_eq_card (s : Multiset R) : (s.map fun a => X - c a).Prod.natDegree = s.card :=
  by
  rw [nat_degree_multiset_prod_of_monic, Multiset.map_map]
  · convert Multiset.sum_repeat 1 _
    · convert Multiset.map_const _ 1
      ext
      apply nat_degree_X_sub_C
      
    · simp
      
    
  · intro f hf
    obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.1 hf
    exact monic_X_sub_C a
    

theorem card_roots_X_pow_sub_C {n : ℕ} (hn : 0 < n) (a : R) : (roots ((x : R[X]) ^ n - c a)).card ≤ n :=
  WithBot.coe_le_coe.1 <|
    calc
      ((roots ((x : R[X]) ^ n - c a)).card : WithBot ℕ) ≤ degree ((x : R[X]) ^ n - c a) :=
        card_roots (X_pow_sub_C_ne_zero hn a)
      _ = n := degree_X_pow_sub_C hn a
      

section

variable {A B : Type _} [CommRingₓ A] [CommRingₓ B]

theorem le_root_multiplicity_map {p : A[X]} {f : A →+* B} (hmap : map f p ≠ 0) (a : A) :
    rootMultiplicity a p ≤ rootMultiplicity (f a) (map f p) := by
  have hp0 : p ≠ 0 := fun h => hmap (h.symm ▸ Polynomial.map_zero f)
  rw [root_multiplicity, root_multiplicity, dif_neg hp0, dif_neg hmap]
  simp only [← not_not, ← Nat.lt_find_iff, ← Nat.le_find_iff]
  intro m hm
  have := (map_ring_hom f).map_dvd (hm m le_rfl)
  simpa only [← coe_map_ring_hom, ← map_pow, ← map_sub, ← map_X, ← map_C]

theorem eq_root_multiplicity_map {p : A[X]} {f : A →+* B} (hf : Function.Injective f) (a : A) :
    rootMultiplicity a p = rootMultiplicity (f a) (map f p) := by
  by_cases' hp0 : p = 0
  · simp only [← hp0, ← root_multiplicity_zero, ← Polynomial.map_zero]
    
  have hmap : map f p ≠ 0 := by
    simpa only [← Polynomial.map_zero] using (map_injective f hf).Ne hp0
  apply le_antisymmₓ (le_root_multiplicity_map hmap a)
  rw [root_multiplicity, root_multiplicity, dif_neg hp0, dif_neg hmap]
  simp only [← not_not, ← Nat.lt_find_iff, ← Nat.le_find_iff]
  intro m hm
  rw [← map_dvd_map f hf ((monic_X_sub_C a).pow _)]
  convert hm m le_rfl
  simp only [← Polynomial.map_pow, ← Polynomial.map_sub, ← map_pow, ← map_sub, ← map_X, ← map_C]

theorem count_map_roots [IsDomain A] (p : A[X]) {f : A →+* B} (hf : Function.Injective f) (a : B) :
    count a (p.roots.map f) ≤ rootMultiplicity a (map f p) := by
  by_cases' h : ∃ t, f t = a
  · rcases h with ⟨h_w, rfl⟩
    rw [Multiset.count_map_eq_count' f _ hf, count_roots]
    exact (eq_root_multiplicity_map hf h_w).le
    
  · suffices (Multiset.map f p.roots).count a = 0 by
      rw [this]
      exact zero_le _
    rw [Multiset.count_map, Multiset.card_eq_zero, Multiset.filter_eq_nil]
    rintro k hk rfl
    exact h ⟨k, rfl⟩
    

theorem roots_map_of_injective_card_eq_total_degree [IsDomain A] [IsDomain B] {p : A[X]} {f : A →+* B}
    (hf : Function.Injective f) (hroots : p.roots.card = p.natDegree) : p.roots.map f = (map f p).roots := by
  by_cases' hp0 : p = 0
  · simp only [← hp0, ← roots_zero, ← Multiset.map_zero, ← Polynomial.map_zero]
    
  have hmap : map f p ≠ 0 := by
    simpa only [← Polynomial.map_zero] using (map_injective f hf).Ne hp0
  apply Multiset.eq_of_le_of_card_le
  · simpa only [← Multiset.le_iff_count, ← count_roots] using count_map_roots p hf
    
  · simpa only [← Multiset.card_map, ← hroots] using (card_roots' _).trans (nat_degree_map_le f p)
    

end

section NthRoots

/-- `nth_roots n a` noncomputably returns the solutions to `x ^ n = a`-/
def nthRoots (n : ℕ) (a : R) : Multiset R :=
  roots ((x : R[X]) ^ n - c a)

@[simp]
theorem mem_nth_roots {n : ℕ} (hn : 0 < n) {a x : R} : x ∈ nthRoots n a ↔ x ^ n = a := by
  rw [nth_roots, mem_roots (X_pow_sub_C_ne_zero hn a), is_root.def, eval_sub, eval_C, eval_pow, eval_X, sub_eq_zero]

@[simp]
theorem nth_roots_zero (r : R) : nthRoots 0 r = 0 := by
  simp only [← empty_eq_zero, ← pow_zeroₓ, ← nth_roots, C_1, C_sub, ← roots_C]

theorem card_nth_roots (n : ℕ) (a : R) : (nthRoots n a).card ≤ n :=
  if hn : n = 0 then
    if h : (x : R[X]) ^ n - c a = 0 then by
      simp only [← Nat.zero_leₓ, ← nth_roots, ← roots, ← h, ← dif_pos rfl, ← empty_eq_zero, ← card_zero]
    else
      WithBot.coe_le_coe.1
        (le_transₓ (card_roots h)
          (by
            rw [hn, pow_zeroₓ, ← C_1, ← RingHom.map_sub]
            exact degree_C_le))
  else by
    rw [← WithBot.coe_le_coe, ← degree_X_pow_sub_C (Nat.pos_of_ne_zeroₓ hn) a] <;>
      exact card_roots (X_pow_sub_C_ne_zero (Nat.pos_of_ne_zeroₓ hn) a)

/-- The multiset `nth_roots ↑n (1 : R)` as a finset. -/
def nthRootsFinset (n : ℕ) (R : Type _) [CommRingₓ R] [IsDomain R] : Finset R :=
  Multiset.toFinset (nthRoots n (1 : R))

@[simp]
theorem mem_nth_roots_finset {n : ℕ} (h : 0 < n) {x : R} : x ∈ nthRootsFinset n R ↔ x ^ (n : ℕ) = 1 := by
  rw [nth_roots_finset, mem_to_finset, mem_nth_roots h]

@[simp]
theorem nth_roots_finset_zero : nthRootsFinset 0 R = ∅ := by
  simp [← nth_roots_finset]

end NthRoots

theorem Monic.comp (hp : p.Monic) (hq : q.Monic) (h : q.natDegree ≠ 0) : (p.comp q).Monic := by
  rw [monic.def, leading_coeff_comp h, monic.def.1 hp, monic.def.1 hq, one_pow, one_mulₓ]

theorem Monic.comp_X_add_C (hp : p.Monic) (r : R) : (p.comp (X + c r)).Monic := by
  refine' hp.comp (monic_X_add_C _) fun ha => _
  rw [nat_degree_X_add_C] at ha
  exact one_ne_zero ha

theorem Monic.comp_X_sub_C (hp : p.Monic) (r : R) : (p.comp (X - c r)).Monic := by
  simpa using hp.comp_X_add_C (-r)

theorem units_coeff_zero_smul (c : R[X]ˣ) (p : R[X]) : (c : R[X]).coeff 0 • p = c * p := by
  rw [← Polynomial.C_mul', ← Polynomial.eq_C_of_degree_eq_zero (degree_coe_units c)]

@[simp]
theorem nat_degree_coe_units (u : R[X]ˣ) : natDegree (u : R[X]) = 0 :=
  nat_degree_eq_of_degree_eq_some (degree_coe_units u)

theorem comp_eq_zero_iff : p.comp q = 0 ↔ p = 0 ∨ p.eval (q.coeff 0) = 0 ∧ q = c (q.coeff 0) := by
  constructor
  · intro h
    have key : p.nat_degree = 0 ∨ q.nat_degree = 0 := by
      rw [← mul_eq_zero, ← nat_degree_comp, h, nat_degree_zero]
    replace key := Or.imp eq_C_of_nat_degree_eq_zero eq_C_of_nat_degree_eq_zero key
    cases key
    · rw [key, C_comp] at h
      exact Or.inl (key.trans h)
      
    · rw [key, comp_C, C_eq_zero] at h
      exact Or.inr ⟨h, key⟩
      
    
  · exact fun h =>
      Or.ndrec
        (fun h => by
          rw [h, zero_comp])
        (fun h => by
          rw [h.2, comp_C, h.1, C_0])
        h
    

theorem zero_of_eval_zero [Infinite R] (p : R[X]) (h : ∀ x, p.eval x = 0) : p = 0 := by
  classical <;>
    by_contra hp <;>
      exact Fintype.false ⟨p.roots.to_finset, fun x => multiset.mem_to_finset.mpr ((mem_roots hp).mpr (h _))⟩

theorem funext [Infinite R] {p q : R[X]} (ext : ∀ r : R, p.eval r = q.eval r) : p = q := by
  rw [← sub_eq_zero]
  apply zero_of_eval_zero
  intro x
  rw [eval_sub, sub_eq_zero, ext]

variable [CommRingₓ T]

/-- The set of distinct roots of `p` in `E`.

If you have a non-separable polynomial, use `polynomial.roots` for the multiset
where multiple roots have the appropriate multiplicity. -/
def RootSet (p : T[X]) (S) [CommRingₓ S] [IsDomain S] [Algebra T S] : Set S :=
  (p.map (algebraMap T S)).roots.toFinset

theorem root_set_def (p : T[X]) (S) [CommRingₓ S] [IsDomain S] [Algebra T S] :
    p.RootSet S = (p.map (algebraMap T S)).roots.toFinset :=
  rfl

@[simp]
theorem root_set_zero (S) [CommRingₓ S] [IsDomain S] [Algebra T S] : (0 : T[X]).RootSet S = ∅ := by
  rw [root_set_def, Polynomial.map_zero, roots_zero, to_finset_zero, Finset.coe_empty]

@[simp]
theorem root_set_C [CommRingₓ S] [IsDomain S] [Algebra T S] (a : T) : (c a).RootSet S = ∅ := by
  rw [root_set_def, map_C, roots_C, Multiset.to_finset_zero, Finset.coe_empty]

instance rootSetFintype (p : T[X]) (S : Type _) [CommRingₓ S] [IsDomain S] [Algebra T S] : Fintype (p.RootSet S) :=
  FinsetCoe.fintype _

theorem root_set_finite (p : T[X]) (S : Type _) [CommRingₓ S] [IsDomain S] [Algebra T S] : (p.RootSet S).Finite :=
  Set.to_finite _

theorem mem_root_set_iff' {p : T[X]} {S : Type _} [CommRingₓ S] [IsDomain S] [Algebra T S]
    (hp : p.map (algebraMap T S) ≠ 0) (a : S) : a ∈ p.RootSet S ↔ (p.map (algebraMap T S)).eval a = 0 := by
  change a ∈ Multiset.toFinset _ ↔ _
  rw [mem_to_finset, mem_roots hp]
  rfl

theorem mem_root_set_iff {p : T[X]} (hp : p ≠ 0) {S : Type _} [CommRingₓ S] [IsDomain S] [Algebra T S]
    [NoZeroSmulDivisors T S] (a : S) : a ∈ p.RootSet S ↔ aeval a p = 0 := by
  rw [mem_root_set_iff', ← eval₂_eq_eval_map]
  · rfl
    
  intro h
  rw [← Polynomial.map_zero (algebraMap T S)] at h
  exact hp (map_injective _ (NoZeroSmulDivisors.algebra_map_injective T S) h)

end Roots

theorem is_unit_iff {f : R[X]} : IsUnit f ↔ ∃ r : R, IsUnit r ∧ c r = f :=
  ⟨fun hf =>
    ⟨f.coeff 0, is_unit_C.1 <| eq_C_of_degree_eq_zero (degree_eq_zero_of_is_unit hf) ▸ hf,
      (eq_C_of_degree_eq_zero (degree_eq_zero_of_is_unit hf)).symm⟩,
    fun ⟨r, hr, hrf⟩ => hrf ▸ is_unit_C.2 hr⟩

theorem coeff_coe_units_zero_ne_zero (u : R[X]ˣ) : coeff (u : R[X]) 0 ≠ 0 := by
  conv in 0 => rw [← nat_degree_coe_units u]
  rw [← leading_coeff, Ne.def, leading_coeff_eq_zero]
  exact Units.ne_zero _

theorem degree_eq_degree_of_associated (h : Associated p q) : degree p = degree q := by
  let ⟨u, hu⟩ := h
  simp [← hu.symm]

theorem degree_eq_one_of_irreducible_of_root (hi : Irreducible p) {x : R} (hx : IsRoot p x) : degree p = 1 :=
  let ⟨g, hg⟩ := dvd_iff_is_root.2 hx
  have : IsUnit (X - c x) ∨ IsUnit g := hi.is_unit_or_is_unit hg
  this.elim
    (fun h => by
      have h₁ : degree (X - c x) = 1 := degree_X_sub_C x
      have h₂ : degree (X - c x) = 0 := degree_eq_zero_of_is_unit h
      rw [h₁] at h₂ <;>
        exact
          absurd h₂
            (by
              decide))
    fun hgu => by
    rw [hg, degree_mul, degree_X_sub_C, degree_eq_zero_of_is_unit hgu, add_zeroₓ]

/-- Division by a monic polynomial doesn't change the leading coefficient. -/
theorem leading_coeff_div_by_monic_of_monic {R : Type u} [CommRingₓ R] {p q : R[X]} (hmonic : q.Monic)
    (hdegree : q.degree ≤ p.degree) : (p /ₘ q).leadingCoeff = p.leadingCoeff := by
  nontriviality
  have h : q.leading_coeff * (p /ₘ q).leadingCoeff ≠ 0 := by
    simpa [← div_by_monic_eq_zero_iff hmonic, ← hmonic.leading_coeff, ← Nat.WithBot.one_le_iff_zero_lt] using hdegree
  nth_rw_rhs 0[← mod_by_monic_add_div p hmonic]
  rw [leading_coeff_add_of_degree_lt, leading_coeff_monic_mul hmonic]
  rw [degree_mul' h, degree_add_div_by_monic hmonic hdegree]
  exact (degree_mod_by_monic_lt p hmonic).trans_le hdegree

theorem leading_coeff_div_by_monic_X_sub_C (p : R[X]) (hp : degree p ≠ 0) (a : R) :
    leadingCoeff (p /ₘ (X - c a)) = leadingCoeff p := by
  nontriviality
  cases' hp.lt_or_lt with hd hd
  · rw [degree_eq_bot.mp <| (Nat.WithBot.lt_zero_iff _).mp hd, zero_div_by_monic]
    
  refine' leading_coeff_div_by_monic_of_monic (monic_X_sub_C a) _
  rwa [degree_X_sub_C, Nat.WithBot.one_le_iff_zero_lt]

theorem eq_leading_coeff_mul_of_monic_of_dvd_of_nat_degree_le {R} [CommRingₓ R] {p q : R[X]} (hp : p.Monic)
    (hdiv : p ∣ q) (hdeg : q.natDegree ≤ p.natDegree) : q = c q.leadingCoeff * p := by
  obtain ⟨r, hr⟩ := hdiv
  obtain rfl | hq := eq_or_ne q 0
  · simp
    
  have rzero : r ≠ 0 := fun h => by
    simpa [← h, ← hq] using hr
  rw [hr, nat_degree_mul'] at hdeg
  swap
  · rw [hp.leading_coeff, one_mulₓ, leading_coeff_ne_zero]
    exact rzero
    
  rw [mul_comm, @eq_C_of_nat_degree_eq_zero _ _ r] at hr
  · convert hr
    convert leading_coeff_C _ using 1
    rw [hr, leading_coeff_mul_monic hp]
    
  · exact (add_right_injₓ _).1 (le_antisymmₓ hdeg <| Nat.Le.intro rfl)
    

theorem eq_of_monic_of_dvd_of_nat_degree_le {R} [CommRingₓ R] {p q : R[X]} (hp : p.Monic) (hq : q.Monic) (hdiv : p ∣ q)
    (hdeg : q.natDegree ≤ p.natDegree) : q = p := by
  convert eq_leading_coeff_mul_of_monic_of_dvd_of_nat_degree_le hp hdiv hdeg
  rw [hq.leading_coeff, C_1, one_mulₓ]

theorem is_coprime_X_sub_C_of_is_unit_sub {R} [CommRingₓ R] {a b : R} (h : IsUnit (a - b)) :
    IsCoprime (X - c a) (X - c b) :=
  ⟨-c h.Unit⁻¹.val, c h.Unit⁻¹.val, by
    rw [neg_mul_comm, ← left_distrib, neg_add_eq_sub, sub_sub_sub_cancel_left, ← C_sub, ← C_mul]
    convert C_1
    exact h.coe_inv_mul⟩

theorem pairwise_coprime_X_sub_C {K} [Field K] {I : Type v} {s : I → K} (H : Function.Injective s) :
    Pairwise (IsCoprime on fun i : I => X - c (s i)) := fun i j hij =>
  is_coprime_X_sub_C_of_is_unit_sub (sub_ne_zero_of_ne <| H.Ne hij).IsUnit

theorem monic_prod_multiset_X_sub_C : Monic (p.roots.map fun a => X - c a).Prod :=
  monic_multiset_prod_of_monic _ _ fun a _ => monic_X_sub_C a

theorem prod_multiset_root_eq_finset_root :
    (p.roots.map fun a => X - c a).Prod = p.roots.toFinset.Prod fun a => (X - c a) ^ rootMultiplicity a p := by
  simp only [← count_roots, ← Finset.prod_multiset_map_count]

/-- The product `∏ (X - a)` for `a` inside the multiset `p.roots` divides `p`. -/
theorem prod_multiset_X_sub_C_dvd (p : R[X]) : (p.roots.map fun a => X - c a).Prod ∣ p := by
  rw [← map_dvd_map _ (IsFractionRing.injective R <| FractionRing R) monic_prod_multiset_X_sub_C]
  rw [prod_multiset_root_eq_finset_root, Polynomial.map_prod]
  refine' Finset.prod_dvd_of_coprime (fun a _ b _ h => _) fun a _ => _
  · simp_rw [Polynomial.map_pow, Polynomial.map_sub, map_C, map_X]
    exact (pairwise_coprime_X_sub_C (IsFractionRing.injective R <| FractionRing R) _ _ h).pow
    
  · exact Polynomial.map_dvd _ (pow_root_multiplicity_dvd p a)
    

theorem exists_prod_multiset_X_sub_C_mul (p : R[X]) :
    ∃ q, (p.roots.map fun a => X - c a).Prod * q = p ∧ p.roots.card + q.natDegree = p.natDegree ∧ q.roots = 0 := by
  obtain ⟨q, he⟩ := prod_multiset_X_sub_C_dvd p
  use q, he.symm
  obtain rfl | hq := eq_or_ne q 0
  · rw [mul_zero] at he
    subst he
    simp
    
  constructor
  · conv_rhs => rw [he]
    rw [monic_prod_multiset_X_sub_C.nat_degree_mul' hq, nat_degree_multiset_prod_X_sub_C_eq_card]
    
  · replace he := congr_arg roots he.symm
    rw [roots_mul, roots_multiset_prod_X_sub_C] at he
    exacts[add_right_eq_selfₓ.1 he, mul_ne_zero monic_prod_multiset_X_sub_C.ne_zero hq]
    

/-- A polynomial `p` that has as many roots as its degree
can be written `p = p.leading_coeff * ∏(X - a)`, for `a` in `p.roots`. -/
theorem C_leading_coeff_mul_prod_multiset_X_sub_C (hroots : p.roots.card = p.natDegree) :
    c p.leadingCoeff * (p.roots.map fun a => X - c a).Prod = p :=
  (eq_leading_coeff_mul_of_monic_of_dvd_of_nat_degree_le monic_prod_multiset_X_sub_C (prod_multiset_X_sub_C_dvd p) <|
      ((nat_degree_multiset_prod_X_sub_C_eq_card _).trans hroots).Ge).symm

/-- A monic polynomial `p` that has as many roots as its degree
can be written `p = ∏(X - a)`, for `a` in `p.roots`. -/
theorem prod_multiset_X_sub_C_of_monic_of_roots_card_eq (hp : p.Monic) (hroots : p.roots.card = p.natDegree) :
    (p.roots.map fun a => X - c a).Prod = p := by
  convert C_leading_coeff_mul_prod_multiset_X_sub_C hroots
  rw [hp.leading_coeff, C_1, one_mulₓ]

end CommRingₓ

section

variable [Semiringₓ R] [CommRingₓ S] [IsDomain S] (φ : R →+* S)

theorem is_unit_of_is_unit_leading_coeff_of_is_unit_map {f : R[X]} (hf : IsUnit f.leadingCoeff) (H : IsUnit (map φ f)) :
    IsUnit f := by
  have dz := degree_eq_zero_of_is_unit H
  rw [degree_map_eq_of_leading_coeff_ne_zero] at dz
  · rw [eq_C_of_degree_eq_zero dz]
    refine' IsUnit.map C _
    convert hf
    rw [(degree_eq_iff_nat_degree_eq _).1 dz]
    rintro rfl
    simpa using H
    
  · intro h
    have u : IsUnit (φ f.leading_coeff) := IsUnit.map φ hf
    rw [h] at u
    simpa using u
    

end

section

variable [CommRingₓ R] [IsDomain R] [CommRingₓ S] [IsDomain S] (φ : R →+* S)

/-- A polynomial over an integral domain `R` is irreducible if it is monic and
  irreducible after mapping into an integral domain `S`.

A special case of this lemma is that a polynomial over `ℤ` is irreducible if
  it is monic and irreducible over `ℤ/pℤ` for some prime `p`.
-/
theorem Monic.irreducible_of_irreducible_map (f : R[X]) (h_mon : Monic f) (h_irr : Irreducible (map φ f)) :
    Irreducible f := by
  refine' ⟨h_irr.not_unit ∘ IsUnit.map (map_ring_hom φ), fun a b h => _⟩
  dsimp' [← monic]  at h_mon
  have q := (leading_coeff_mul a b).symm
  rw [← h, h_mon] at q
  refine' (h_irr.is_unit_or_is_unit <| (congr_arg (map φ) h).trans (Polynomial.map_mul φ)).imp _ _ <;>
    apply is_unit_of_is_unit_leading_coeff_of_is_unit_map <;> apply is_unit_of_mul_eq_one
  · exact q
    
  · rw [mul_comm]
    exact q
    

end

end Polynomial

