/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Joey van Langen, Casper Putz
-/
import Mathbin.Tactic.ApplyFun
import Mathbin.Algebra.Ring.Equiv
import Mathbin.Data.Zmod.Algebra
import Mathbin.LinearAlgebra.FiniteDimensional
import Mathbin.RingTheory.IntegralDomain
import Mathbin.FieldTheory.Separable

/-!
# Finite fields

This file contains basic results about finite fields.
Throughout most of this file, `K` denotes a finite field
and `q` is notation for the cardinality of `K`.

See `ring_theory.integral_domain` for the fact that the unit group of a finite field is a
cyclic group, as well as the fact that every finite integral domain is a field
(`fintype.field_of_domain`).

## Main results

1. `fintype.card_units`: The unit group of a finite field is has cardinality `q - 1`.
2. `sum_pow_units`: The sum of `x^i`, where `x` ranges over the units of `K`, is
   - `q-1` if `q-1 ∣ i`
   - `0`   otherwise
3. `finite_field.card`: The cardinality `q` is a power of the characteristic of `K`.
   See `card'` for a variant.

## Notation

Throughout most of this file, `K` denotes a finite field
and `q` is notation for the cardinality of `K`.

## Implementation notes

While `fintype Kˣ` can be inferred from `fintype K` in the presence of `decidable_eq K`,
in this file we take the `fintype Kˣ` argument directly to reduce the chance of typeclass
diamonds, as `fintype` carries data.

-/


variable {K : Type _} {R : Type _}

-- mathport name: «exprq»
local notation "q" => Fintype.card K

open BigOperators Polynomial

namespace FiniteField

open Finset Function

section Polynomial

variable [CommRingₓ R] [IsDomain R]

open Polynomial

/-- The cardinality of a field is at most `n` times the cardinality of the image of a degree `n`
  polynomial -/
theorem card_image_polynomial_eval [DecidableEq R] [Fintype R] {p : R[X]} (hp : 0 < p.degree) :
    Fintype.card R ≤ natDegree p * (univ.Image fun x => eval x p).card :=
  Finset.card_le_mul_card_image _ _ fun a _ =>
    calc
      _ = (p - c a).roots.toFinset.card :=
        congr_arg card
          (by
            simp [← Finset.ext_iff, ← mem_roots_sub_C hp])
      _ ≤ (p - c a).roots.card := Multiset.to_finset_card_le _
      _ ≤ _ := card_roots_sub_C' hp
      

/-- If `f` and `g` are quadratic polynomials, then the `f.eval a + g.eval b = 0` has a solution. -/
theorem exists_root_sum_quadratic [Fintype R] {f g : R[X]} (hf2 : degree f = 2) (hg2 : degree g = 2)
    (hR : Fintype.card R % 2 = 1) : ∃ a b, f.eval a + g.eval b = 0 := by
  let this := Classical.decEq R <;>
    exact
      suffices ¬Disjoint (univ.image fun x : R => eval x f) (univ.image fun x : R => eval x (-g)) by
        simp only [← disjoint_left, ← mem_image] at this
        push_neg  at this
        rcases this with ⟨x, ⟨a, _, ha⟩, ⟨b, _, hb⟩⟩
        exact
          ⟨a, b, by
            rw [ha, ← hb, eval_neg, neg_add_selfₓ]⟩
      fun hd : Disjoint _ _ =>
      lt_irreflₓ (2 * ((univ.image fun x : R => eval x f) ∪ univ.image fun x : R => eval x (-g)).card) <|
        calc
          2 * ((univ.image fun x : R => eval x f) ∪ univ.image fun x : R => eval x (-g)).card ≤ 2 * Fintype.card R :=
            Nat.mul_le_mul_leftₓ _ (Finset.card_le_univ _)
          _ = Fintype.card R + Fintype.card R := two_mul _
          _ <
              nat_degree f * (univ.image fun x : R => eval x f).card +
                nat_degree (-g) * (univ.image fun x : R => eval x (-g)).card :=
            add_lt_add_of_lt_of_le
              (lt_of_le_of_neₓ
                (card_image_polynomial_eval
                  (by
                    rw [hf2] <;>
                      exact by
                        decide))
                (mt (congr_arg (· % 2))
                  (by
                    simp [← nat_degree_eq_of_degree_eq_some hf2, ← hR])))
              (card_image_polynomial_eval
                (by
                  rw [degree_neg, hg2] <;>
                    exact by
                      decide))
          _ = 2 * ((univ.image fun x : R => eval x f) ∪ univ.image fun x : R => eval x (-g)).card := by
            rw [card_disjoint_union hd] <;>
              simp [← nat_degree_eq_of_degree_eq_some hf2, ← nat_degree_eq_of_degree_eq_some hg2, ← bit0, ← mul_addₓ]
          

end Polynomial

theorem prod_univ_units_id_eq_neg_one [CommRingₓ K] [IsDomain K] [Fintype Kˣ] : (∏ x : Kˣ, x) = (-1 : Kˣ) := by
  classical
  have : (∏ x in (@univ Kˣ _).erase (-1), x) = 1 :=
    prod_involution (fun x _ => x⁻¹)
      (by
        simp )
      (fun a => by
        simp (config := { contextual := true })[← Units.inv_eq_self_iff])
      (fun a => by
        simp [← @inv_eq_iff_inv_eq _ _ a, ← eq_comm])
      (by
        simp )
  rw [← insert_erase (mem_univ (-1 : Kˣ)), prod_insert (not_mem_erase _ _), this, mul_oneₓ]

section

variable [GroupWithZeroₓ K] [Fintype K]

theorem pow_card_sub_one_eq_one (a : K) (ha : a ≠ 0) : a ^ (q - 1) = 1 :=
  calc
    a ^ (Fintype.card K - 1) = (Units.mk0 a ha ^ (Fintype.card K - 1) : Kˣ) := by
      rw [Units.coe_pow, Units.coe_mk0]
    _ = 1 := by
      classical
      rw [← Fintype.card_units, pow_card_eq_one]
      rfl
    

theorem pow_card (a : K) : a ^ q = a := by
  have hp : 0 < Fintype.card K := lt_transₓ zero_lt_one Fintype.one_lt_card
  by_cases' h : a = 0
  · rw [h]
    apply zero_pow hp
    
  rw [← Nat.succ_pred_eq_of_posₓ hp, pow_succₓ, Nat.pred_eq_sub_one, pow_card_sub_one_eq_one a h, mul_oneₓ]

theorem pow_card_pow (n : ℕ) (a : K) : a ^ q ^ n = a := by
  induction' n with n ih
  · simp
    
  · simp [← pow_succₓ, ← pow_mulₓ, ← ih, ← pow_card]
    

end

variable (K) [Field K] [Fintype K]

theorem card (p : ℕ) [CharP K p] : ∃ n : ℕ+, Nat.Prime p ∧ q = p ^ (n : ℕ) := by
  have hp : Fact p.prime := ⟨CharP.char_is_prime K p⟩
  let this : Module (Zmod p) K := { (Zmod.castHom dvd_rfl K : Zmod p →+* _).toModule with }
  obtain ⟨n, h⟩ := VectorSpace.card_fintype (Zmod p) K
  rw [Zmod.card] at h
  refine' ⟨⟨n, _⟩, hp.1, h⟩
  apply Or.resolve_left (Nat.eq_zero_or_posₓ n)
  rintro rfl
  rw [pow_zeroₓ] at h
  have : (0 : K) = 1 := by
    apply fintype.card_le_one_iff.mp (le_of_eqₓ h)
  exact absurd this zero_ne_one

-- this statement doesn't use `q` because we want `K` to be an explicit parameter
theorem card' : ∃ (p : ℕ)(n : ℕ+), Nat.Prime p ∧ Fintype.card K = p ^ (n : ℕ) :=
  let ⟨p, hc⟩ := CharP.exists K
  ⟨p, @FiniteField.card K _ _ p hc⟩

@[simp]
theorem cast_card_eq_zero : (q : K) = 0 := by
  rcases CharP.exists K with ⟨p, _char_p⟩
  skip
  rcases card K p with ⟨n, hp, hn⟩
  simp only [← CharP.cast_eq_zero_iff K p, ← hn]
  conv => congr rw [← pow_oneₓ p]
  exact pow_dvd_pow _ n.2

theorem forall_pow_eq_one_iff (i : ℕ) : (∀ x : Kˣ, x ^ i = 1) ↔ q - 1 ∣ i := by
  classical
  obtain ⟨x, hx⟩ := IsCyclic.exists_generator Kˣ
  rw [← Fintype.card_units, ← order_of_eq_card_of_forall_mem_zpowers hx, order_of_dvd_iff_pow_eq_one]
  constructor
  · intro h
    apply h
    
  · intro h y
    simp_rw [← mem_powers_iff_mem_zpowers] at hx
    rcases hx y with ⟨j, rfl⟩
    rw [← pow_mulₓ, mul_comm, pow_mulₓ, h, one_pow]
    

/-- The sum of `x ^ i` as `x` ranges over the units of a finite field of cardinality `q`
is equal to `0` unless `(q - 1) ∣ i`, in which case the sum is `q - 1`. -/
theorem sum_pow_units [Fintype Kˣ] (i : ℕ) : (∑ x : Kˣ, (x ^ i : K)) = if q - 1 ∣ i then -1 else 0 := by
  let φ : Kˣ →* K :=
    { toFun := fun x => x ^ i,
      map_one' := by
        rw [Units.coe_one, one_pow],
      map_mul' := by
        intros
        rw [Units.coe_mul, mul_powₓ] }
  have : Decidable (φ = 1) := by
    classical
    infer_instance
  calc (∑ x : Kˣ, φ x) = if φ = 1 then Fintype.card Kˣ else 0 := sum_hom_units φ _ = if q - 1 ∣ i then -1 else 0 := _
  suffices q - 1 ∣ i ↔ φ = 1 by
    simp only [← this]
    split_ifs with h h
    swap
    rfl
    rw [Fintype.card_units, Nat.cast_sub, cast_card_eq_zero, Nat.cast_oneₓ, zero_sub]
    show 1 ≤ q
    exact fintype.card_pos_iff.mpr ⟨0⟩
  rw [← forall_pow_eq_one_iff, MonoidHom.ext_iff]
  apply forall_congrₓ
  intro x
  rw [Units.ext_iff, Units.coe_pow, Units.coe_one, MonoidHom.one_apply]
  rfl

/-- The sum of `x ^ i` as `x` ranges over a finite field of cardinality `q`
is equal to `0` if `i < q - 1`. -/
theorem sum_pow_lt_card_sub_one (i : ℕ) (h : i < q - 1) : (∑ x : K, x ^ i) = 0 := by
  by_cases' hi : i = 0
  · simp only [← hi, ← nsmul_one, ← sum_const, ← pow_zeroₓ, ← card_univ, ← cast_card_eq_zero]
    
  classical
  have hiq : ¬q - 1 ∣ i := by
    contrapose! h
    exact Nat.le_of_dvdₓ (Nat.pos_of_ne_zeroₓ hi) h
  let φ : Kˣ ↪ K := ⟨coe, Units.ext⟩
  have : univ.map φ = univ \ {0} := by
    ext x
    simp only [← true_andₓ, ← embedding.coe_fn_mk, ← mem_sdiff, ← Units.exists_iff_ne_zero, ← mem_univ, ← mem_map, ←
      exists_prop_of_true, ← mem_singleton]
  calc (∑ x : K, x ^ i) = ∑ x in univ \ {(0 : K)}, x ^ i := by
      rw [← sum_sdiff ({0} : Finset K).subset_univ, sum_singleton, zero_pow (Nat.pos_of_ne_zeroₓ hi),
        add_zeroₓ]_ = ∑ x : Kˣ, x ^ i :=
      by
      rw [← this, univ.sum_map φ]
      rfl _ = 0 := by
      rw [sum_pow_units K i, if_neg]
      exact hiq

section IsSplittingField

open Polynomial

section

variable (K' : Type _) [Field K'] {p n : ℕ}

theorem X_pow_card_sub_X_nat_degree_eq (hp : 1 < p) : (X ^ p - X : K'[X]).natDegree = p := by
  have h1 : (X : K'[X]).degree < (X ^ p : K'[X]).degree := by
    rw [degree_X_pow, degree_X]
    exact_mod_cast hp
  rw [nat_degree_eq_of_degree_eq (degree_sub_eq_left_of_degree_lt h1), nat_degree_X_pow]

theorem X_pow_card_pow_sub_X_nat_degree_eq (hn : n ≠ 0) (hp : 1 < p) : (X ^ p ^ n - X : K'[X]).natDegree = p ^ n :=
  X_pow_card_sub_X_nat_degree_eq K' <| Nat.one_lt_pow _ _ (Nat.pos_of_ne_zeroₓ hn) hp

theorem X_pow_card_sub_X_ne_zero (hp : 1 < p) : (X ^ p - X : K'[X]) ≠ 0 :=
  ne_zero_of_nat_degree_gt <|
    calc
      1 < _ := hp
      _ = _ := (X_pow_card_sub_X_nat_degree_eq K' hp).symm
      

theorem X_pow_card_pow_sub_X_ne_zero (hn : n ≠ 0) (hp : 1 < p) : (X ^ p ^ n - X : K'[X]) ≠ 0 :=
  X_pow_card_sub_X_ne_zero K' <| Nat.one_lt_pow _ _ (Nat.pos_of_ne_zeroₓ hn) hp

end

variable (p : ℕ) [Fact p.Prime] [Algebra (Zmod p) K]

theorem roots_X_pow_card_sub_X : roots (X ^ q - X : K[X]) = Finset.univ.val := by
  classical
  have aux : (X ^ q - X : K[X]) ≠ 0 := X_pow_card_sub_X_ne_zero K Fintype.one_lt_card
  have : (roots (X ^ q - X : K[X])).toFinset = Finset.univ := by
    rw [eq_univ_iff_forall]
    intro x
    rw [Multiset.mem_to_finset, mem_roots aux, is_root.def, eval_sub, eval_pow, eval_X, sub_eq_zero, pow_card]
  rw [← this, Multiset.to_finset_val, eq_comm, Multiset.dedup_eq_self]
  apply nodup_roots
  rw [separable_def]
  convert is_coprime_one_right.neg_right using 1
  · rw [derivative_sub, derivative_X, derivative_X_pow, ← C_eq_nat_cast, C_eq_zero.mpr (CharP.cast_card_eq_zero K),
      zero_mul, zero_sub]
    

instance (F : Type _) [Field F] [Algebra F K] : IsSplittingField F K (X ^ q - X) where
  Splits := by
    have h : (X ^ q - X : K[X]).natDegree = q := X_pow_card_sub_X_nat_degree_eq K Fintype.one_lt_card
    rw [← splits_id_iff_splits, splits_iff_card_roots, Polynomial.map_sub, Polynomial.map_pow, map_X, h,
      roots_X_pow_card_sub_X K, ← Finset.card_def, Finset.card_univ]
  adjoin_roots := by
    classical
    trans Algebra.adjoin F ((roots (X ^ q - X : K[X])).toFinset : Set K)
    · simp only [← Polynomial.map_pow, ← map_X, ← Polynomial.map_sub]
      
    · rw [roots_X_pow_card_sub_X, val_to_finset, coe_univ, Algebra.adjoin_univ]
      

end IsSplittingField

variable {K}

theorem frobenius_pow {p : ℕ} [Fact p.Prime] [CharP K p] {n : ℕ} (hcard : q = p ^ n) : frobenius K p ^ n = 1 := by
  ext
  conv_rhs => rw [RingHom.one_def, RingHom.id_apply, ← pow_card x, hcard]
  clear hcard
  induction n
  · simp
    
  rw [pow_succₓ, pow_succ'ₓ, pow_mulₓ, RingHom.mul_def, RingHom.comp_apply, frobenius_def, n_ih]

open Polynomial

theorem expand_card (f : K[X]) : expand K q f = f ^ q := by
  cases' CharP.exists K with p hp
  let this := hp
  rcases FiniteField.card K p with ⟨⟨n, npos⟩, ⟨hp, hn⟩⟩
  have : Fact p.prime := ⟨hp⟩
  dsimp'  at hn
  rw [hn, ← map_expand_pow_char, frobenius_pow hn, RingHom.one_def, map_id]

end FiniteField

namespace Zmod

open FiniteField Polynomial

-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:30:4: unsupported: too many args: fin_cases ... #[[]]
theorem sq_add_sq (p : ℕ) [hp : Fact p.Prime] (x : Zmod p) : ∃ a b : Zmod p, a ^ 2 + b ^ 2 = x := by
  cases' hp.1.eq_two_or_odd with hp2 hp_odd
  · subst p
    change Finₓ 2 at x
    fin_cases x
    · use 0
      simp
      
    · use 0, 1
      simp
      
    
  let f : (Zmod p)[X] := X ^ 2
  let g : (Zmod p)[X] := X ^ 2 - C x
  obtain ⟨a, b, hab⟩ : ∃ a b, f.eval a + g.eval b = 0 :=
    @exists_root_sum_quadratic _ _ _ _ f g (degree_X_pow 2)
      (degree_X_pow_sub_C
        (by
          decide)
        _)
      (by
        rw [Zmod.card, hp_odd])
  refine' ⟨a, b, _⟩
  rw [← sub_eq_zero]
  simpa only [← eval_C, ← eval_X, ← eval_pow, ← eval_sub, add_sub_assoc] using hab

end Zmod

namespace CharP

theorem sq_add_sq (R : Type _) [CommRingₓ R] [IsDomain R] (p : ℕ) [Fact (0 < p)] [CharP R p] (x : ℤ) :
    ∃ a b : ℕ, (a ^ 2 + b ^ 2 : R) = x := by
  have := char_is_prime_of_pos R p
  obtain ⟨a, b, hab⟩ := Zmod.sq_add_sq p x
  refine' ⟨a.val, b.val, _⟩
  simpa using congr_arg (Zmod.castHom dvd_rfl R) hab

end CharP

open Nat

open Zmod

/-- The **Fermat-Euler totient theorem**. `nat.modeq.pow_totient` is an alternative statement
  of the same theorem. -/
@[simp]
theorem Zmod.pow_totient {n : ℕ} [Fact (0 < n)] (x : (Zmod n)ˣ) : x ^ φ n = 1 := by
  rw [← card_units_eq_totient, pow_card_eq_one]

/-- The **Fermat-Euler totient theorem**. `zmod.pow_totient` is an alternative statement
  of the same theorem. -/
theorem Nat.Modeq.pow_totient {x n : ℕ} (h : Nat.Coprime x n) : x ^ φ n ≡ 1 [MOD n] := by
  cases n
  · simp
    
  rw [← Zmod.eq_iff_modeq_nat]
  let x' : Units (Zmod (n + 1)) := Zmod.unitOfCoprime _ h
  have := Zmod.pow_totient x'
  apply_fun (coe : Units (Zmod (n + 1)) → Zmod (n + 1))  at this
  simpa only [-Zmod.pow_totient, ← Nat.succ_eq_add_one, ← Nat.cast_powₓ, ← Units.coe_one, ← Nat.cast_oneₓ, ←
    coe_unit_of_coprime, ← Units.coe_pow]

section

variable {V : Type _} [Fintype K] [DivisionRing K] [AddCommGroupₓ V] [Module K V]

-- should this go in a namespace?
-- finite_dimensional would be natural,
-- but we don't assume it...
theorem card_eq_pow_finrank [Fintype V] : Fintype.card V = q ^ FiniteDimensional.finrank K V := by
  let b := IsNoetherian.finsetBasis K V
  rw [Module.card_fintype b, ← FiniteDimensional.finrank_eq_card_basis b]

end

open FiniteField

namespace Zmod

/-- A variation on Fermat's little theorem. See `zmod.pow_card_sub_one_eq_one` -/
@[simp]
theorem pow_card {p : ℕ} [Fact p.Prime] (x : Zmod p) : x ^ p = x := by
  have h := FiniteField.pow_card x
  rwa [Zmod.card p] at h

@[simp]
theorem pow_card_pow {n p : ℕ} [Fact p.Prime] (x : Zmod p) : x ^ p ^ n = x := by
  induction' n with n ih
  · simp
    
  · simp [← pow_succₓ, ← pow_mulₓ, ← ih, ← pow_card]
    

@[simp]
theorem frobenius_zmod (p : ℕ) [Fact p.Prime] : frobenius (Zmod p) p = RingHom.id _ := by
  ext a
  rw [frobenius_def, Zmod.pow_card, RingHom.id_apply]

@[simp]
theorem card_units (p : ℕ) [Fact p.Prime] : Fintype.card (Zmod p)ˣ = p - 1 := by
  rw [Fintype.card_units, card]

/-- **Fermat's Little Theorem**: for every unit `a` of `zmod p`, we have `a ^ (p - 1) = 1`. -/
theorem units_pow_card_sub_one_eq_one (p : ℕ) [Fact p.Prime] (a : (Zmod p)ˣ) : a ^ (p - 1) = 1 := by
  rw [← card_units p, pow_card_eq_one]

/-- **Fermat's Little Theorem**: for all nonzero `a : zmod p`, we have `a ^ (p - 1) = 1`. -/
theorem pow_card_sub_one_eq_one {p : ℕ} [Fact p.Prime] {a : Zmod p} (ha : a ≠ 0) : a ^ (p - 1) = 1 := by
  have h := pow_card_sub_one_eq_one a ha
  rwa [Zmod.card p] at h

open Polynomial

theorem expand_card {p : ℕ} [Fact p.Prime] (f : Polynomial (Zmod p)) : expand (Zmod p) p f = f ^ p := by
  have h := FiniteField.expand_card f
  rwa [Zmod.card p] at h

end Zmod

/-- **Fermat's Little Theorem**: for all `a : ℤ` coprime to `p`, we have
`a ^ (p - 1) ≡ 1 [ZMOD p]`. -/
theorem Int.Modeq.pow_card_sub_one_eq_one {p : ℕ} (hp : Nat.Prime p) {n : ℤ} (hpn : IsCoprime n p) :
    n ^ (p - 1) ≡ 1 [ZMOD p] := by
  have : Fact p.prime := ⟨hp⟩
  have : ¬(n : Zmod p) = 0 := by
    rw [CharP.int_cast_eq_zero_iff _ p, ← (nat.prime_iff_prime_int.mp hp).coprime_iff_not_dvd]
    · exact hpn.symm
      
    exact Zmod.char_p p
  simpa [Zmod.int_coe_eq_int_coe_iff] using Zmod.pow_card_sub_one_eq_one this

section

namespace FiniteField

variable {F : Type _} [Field F] [Fintype F]

/-- In a finite field of characteristic `2`, all elements are squares. -/
theorem is_square_of_char_two (hF : ringChar F = 2) (a : F) : IsSquare a := by
  have hF' : CharP F 2 := ringChar.of_eq hF
  exact is_square_of_char_two' a

/-- The finite field `F` has even cardinality iff it has characteristic `2`. -/
theorem even_card_iff_char_two : ringChar F = 2 ↔ Fintype.card F % 2 = 0 := by
  rcases FiniteField.card F (ringChar F) with ⟨n, hp, h⟩
  rw [h, Nat.pow_mod]
  constructor
  · intro hF
    rw [hF]
    simp only [← Nat.bit0_mod_two, ← zero_pow', ← Ne.def, ← Pnat.ne_zero, ← not_false_iff, ← Nat.zero_modₓ]
    
  · rw [← Nat.even_iff, Nat.even_pow]
    rintro ⟨hev, hnz⟩
    rw [Nat.even_iff, Nat.mod_modₓ] at hev
    exact (Nat.Prime.eq_two_or_odd hp).resolve_right (ne_of_eq_of_ne hev zero_ne_one)
    

theorem even_card_of_char_two (hF : ringChar F = 2) : Fintype.card F % 2 = 0 :=
  even_card_iff_char_two.mp hF

theorem odd_card_of_char_ne_two (hF : ringChar F ≠ 2) : Fintype.card F % 2 = 1 :=
  Nat.mod_two_ne_zero.mp (mt even_card_iff_char_two.mpr hF)

/-- If `F` has odd characteristic, then for nonzero `a : F`, we have that `a ^ (#F / 2) = ±1`. -/
theorem pow_dichotomy (hF : ringChar F ≠ 2) {a : F} (ha : a ≠ 0) :
    a ^ (Fintype.card F / 2) = 1 ∨ a ^ (Fintype.card F / 2) = -1 := by
  have h₁ := FiniteField.pow_card_sub_one_eq_one a ha
  rw [← Nat.two_mul_odd_div_two (FiniteField.odd_card_of_char_ne_two hF), mul_comm, pow_mulₓ, pow_two] at h₁
  exact mul_self_eq_one_iff.mp h₁

/-- A unit `a` of a finite field `F` of odd characteristic is a square
if and only if `a ^ (#F / 2) = 1`. -/
theorem unit_is_square_iff (hF : ringChar F ≠ 2) (a : Fˣ) : IsSquare a ↔ a ^ (Fintype.card F / 2) = 1 := by
  classical
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator Fˣ
  obtain ⟨n, hn⟩ : a ∈ Submonoid.powers g := by
    rw [mem_powers_iff_mem_zpowers]
    apply hg
  have hodd := Nat.two_mul_odd_div_two (FiniteField.odd_card_of_char_ne_two hF)
  constructor
  · rintro ⟨y, rfl⟩
    rw [← pow_two, ← pow_mulₓ, hodd]
    apply_fun @coe Fˣ F _ using Units.ext
    · push_cast
      exact FiniteField.pow_card_sub_one_eq_one (y : F) (Units.ne_zero y)
      
    
  · subst a
    intro h
    have key : 2 * (Fintype.card F / 2) ∣ n * (Fintype.card F / 2) := by
      rw [← pow_mulₓ] at h
      rw [hodd, ← Fintype.card_units, ← order_of_eq_card_of_forall_mem_zpowers hg]
      apply order_of_dvd_of_pow_eq_one h
    have : 0 < Fintype.card F / 2 :=
      Nat.div_pos Fintype.one_lt_card
        (by
          norm_num)
    obtain ⟨m, rfl⟩ := Nat.dvd_of_mul_dvd_mul_rightₓ this key
    refine' ⟨g ^ m, _⟩
    rw [mul_comm, pow_mulₓ, pow_two]
    

/-- A non-zero `a : F` is a square if and only if `a ^ (#F / 2) = 1`. -/
theorem is_square_iff (hF : ringChar F ≠ 2) {a : F} (ha : a ≠ 0) : IsSquare a ↔ a ^ (Fintype.card F / 2) = 1 := by
  apply
    (iff_congr _
          (by
            simp [← Units.ext_iff])).mp
      (FiniteField.unit_is_square_iff hF (Units.mk0 a ha))
  simp only [← IsSquare, ← Units.ext_iff, ← Units.coe_mk0, ← Units.coe_mul]
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y, hy⟩
    
  · rintro ⟨y, rfl⟩
    have hy : y ≠ 0 := by
      rintro rfl
      simpa [← zero_pow] using ha
    refine' ⟨Units.mk0 y hy, _⟩
    simp
    

/-- In a finite field of odd characteristic, not every element is a square. -/
theorem exists_nonsquare (hF : ringChar F ≠ 2) : ∃ a : F, ¬IsSquare a := by
  -- idea: the squaring map on `F` is not injetive, hence not surjective
  let sq : F → F := fun x => x ^ 2
  have h : ¬Function.Injective sq := by
    simp only [← Function.Injective, ← not_forall, ← exists_prop]
    use -1, 1
    constructor
    · simp only [← sq, ← one_pow, ← neg_one_sq]
      
    · exact Ringₓ.neg_one_ne_one_of_char_ne_two hF
      
  have h₁ := mt fintype.injective_iff_surjective.mpr h
  -- sq not surjective
  push_neg  at h₁
  cases' h₁ with a h₁
  use a
  simp only [← IsSquare, ← sq, ← not_exists, ← Ne.def] at h₁⊢
  intro b hb
  rw [← pow_two] at hb
  exact h₁ b hb.symm

end FiniteField

end

