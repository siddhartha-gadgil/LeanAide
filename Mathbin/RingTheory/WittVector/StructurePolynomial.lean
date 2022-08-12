/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Robert Y. Lewis
-/
import Mathbin.Data.Fin.VecNotation
import Mathbin.FieldTheory.Finite.Polynomial
import Mathbin.NumberTheory.Basic
import Mathbin.RingTheory.WittVector.WittPolynomial

/-!
# Witt structure polynomials

In this file we prove the main theorem that makes the whole theory of Witt vectors work.
Briefly, consider a polynomial `Φ : mv_polynomial idx ℤ` over the integers,
with polynomials variables indexed by an arbitrary type `idx`.

Then there exists a unique family of polynomials `φ : ℕ → mv_polynomial (idx × ℕ) Φ`
such that for all `n : ℕ` we have (`witt_structure_int_exists_unique`)
```
bind₁ φ (witt_polynomial p ℤ n) = bind₁ (λ i, (rename (prod.mk i) (witt_polynomial p ℤ n))) Φ
```
In other words: evaluating the `n`-th Witt polynomial on the family `φ`
is the same as evaluating `Φ` on the (appropriately renamed) `n`-th Witt polynomials.

N.b.: As far as we know, these polynomials do not have a name in the literature,
so we have decided to call them the “Witt structure polynomials”. See `witt_structure_int`.

## Special cases

With the main result of this file in place, we apply it to certain special polynomials.
For example, by taking `Φ = X tt + X ff` resp. `Φ = X tt * X ff`
we obtain families of polynomials `witt_add` resp. `witt_mul`
(with type `ℕ → mv_polynomial (bool × ℕ) ℤ`) that will be used in later files to define the
addition and multiplication on the ring of Witt vectors.

## Outline of the proof

The proof of `witt_structure_int_exists_unique` is rather technical, and takes up most of this file.

We start by proving the analogous version for polynomials with rational coefficients,
instead of integer coefficients.
In this case, the solution is rather easy,
since the Witt polynomials form a faithful change of coordinates
in the polynomial ring `mv_polynomial ℕ ℚ`.
We therefore obtain a family of polynomials `witt_structure_rat Φ`
for every `Φ : mv_polynomial idx ℚ`.

If `Φ` has integer coefficients, then the polynomials `witt_structure_rat Φ n` do so as well.
Proving this claim is the essential core of this file, and culminates in
`map_witt_structure_int`, which proves that upon mapping the coefficients
of `witt_structure_int Φ n` from the integers to the rationals,
one obtains `witt_structure_rat Φ n`.
Ultimately, the proof of `map_witt_structure_int` relies on
```
dvd_sub_pow_of_dvd_sub {R : Type*} [comm_ring R] {p : ℕ} {a b : R} :
    (p : R) ∣ a - b → ∀ (k : ℕ), (p : R) ^ (k + 1) ∣ a ^ p ^ k - b ^ p ^ k
```

## Main results

* `witt_structure_rat Φ`: the family of polynomials `ℕ → mv_polynomial (idx × ℕ) ℚ`
  associated with `Φ : mv_polynomial idx ℚ` and satisfying the property explained above.
* `witt_structure_rat_prop`: the proof that `witt_structure_rat` indeed satisfies the property.
* `witt_structure_int Φ`: the family of polynomials `ℕ → mv_polynomial (idx × ℕ) ℤ`
  associated with `Φ : mv_polynomial idx ℤ` and satisfying the property explained above.
* `map_witt_structure_int`: the proof that the integral polynomials `with_structure_int Φ`
  are equal to `witt_structure_rat Φ` when mapped to polynomials with rational coefficients.
* `witt_structure_int_prop`: the proof that `witt_structure_int` indeed satisfies the property.
* Five families of polynomials that will be used to define the ring structure
  on the ring of Witt vectors:
  - `witt_vector.witt_zero`
  - `witt_vector.witt_one`
  - `witt_vector.witt_add`
  - `witt_vector.witt_mul`
  - `witt_vector.witt_neg`
  (We also define `witt_vector.witt_sub`, and later we will prove that it describes subtraction,
  which is defined as `λ a b, a + -b`. See `witt_vector.sub_coeff` for this proof.)

## References

* [Hazewinkel, *Witt Vectors*][Haze09]

* [Commelin and Lewis, *Formalizing the Ring of Witt Vectors*][CL21]
-/


open MvPolynomial

open Set

open Finset (range)

open Finsupp (single)

-- This lemma reduces a bundled morphism to a "mere" function,
-- and consequently the simplifier cannot use a lot of powerful simp-lemmas.
-- We disable this locally, and probably it should be disabled globally in mathlib.
attribute [-simp] coe_eval₂_hom

variable {p : ℕ} {R : Type _} {idx : Type _} [CommRingₓ R]

open Witt

open BigOperators

section PPrime

variable (p) [hp : Fact p.Prime]

include hp

/-- `witt_structure_rat Φ` is a family of polynomials `ℕ → mv_polynomial (idx × ℕ) ℚ`
that are uniquely characterised by the property that
```
bind₁ (witt_structure_rat p Φ) (witt_polynomial p ℚ n) =
bind₁ (λ i, (rename (prod.mk i) (witt_polynomial p ℚ n))) Φ
```
In other words: evaluating the `n`-th Witt polynomial on the family `witt_structure_rat Φ`
is the same as evaluating `Φ` on the (appropriately renamed) `n`-th Witt polynomials.

See `witt_structure_rat_prop` for this property,
and `witt_structure_rat_exists_unique` for the fact that `witt_structure_rat`
gives the unique family of polynomials with this property.

These polynomials turn out to have integral coefficients,
but it requires some effort to show this.
See `witt_structure_int` for the version with integral coefficients,
and `map_witt_structure_int` for the fact that it is equal to `witt_structure_rat`
when mapped to polynomials over the rationals. -/
noncomputable def wittStructureRat (Φ : MvPolynomial idx ℚ) (n : ℕ) : MvPolynomial (idx × ℕ) ℚ :=
  bind₁ (fun k => bind₁ (fun i => rename (Prod.mk i) (W_ ℚ k)) Φ) (xInTermsOfW p ℚ n)

theorem witt_structure_rat_prop (Φ : MvPolynomial idx ℚ) (n : ℕ) :
    bind₁ (wittStructureRat p Φ) (W_ ℚ n) = bind₁ (fun i => rename (Prod.mk i) (W_ ℚ n)) Φ :=
  calc
    bind₁ (wittStructureRat p Φ) (W_ ℚ n) =
        bind₁ (fun k => bind₁ (fun i => (rename (Prod.mk i)) (W_ ℚ k)) Φ) (bind₁ (xInTermsOfW p ℚ) (W_ ℚ n)) :=
      by
      rw [bind₁_bind₁]
      apply eval₂_hom_congr (RingHom.ext_rat _ _) rfl rfl
    _ = bind₁ (fun i => rename (Prod.mk i) (W_ ℚ n)) Φ := by
      rw [bind₁_X_in_terms_of_W_witt_polynomial p _ n, bind₁_X_right]
    

theorem witt_structure_rat_exists_unique (Φ : MvPolynomial idx ℚ) :
    ∃! φ : ℕ → MvPolynomial (idx × ℕ) ℚ, ∀ n : ℕ, bind₁ φ (W_ ℚ n) = bind₁ (fun i => rename (Prod.mk i) (W_ ℚ n)) Φ :=
  by
  refine' ⟨wittStructureRat p Φ, _, _⟩
  · intro n
    apply witt_structure_rat_prop
    
  · intro φ H
    funext n
    rw
      [show φ n = bind₁ φ (bind₁ (W_ ℚ) (xInTermsOfW p ℚ n)) by
        rw [bind₁_witt_polynomial_X_in_terms_of_W p, bind₁_X_right]]
    rw [bind₁_bind₁]
    exact eval₂_hom_congr (RingHom.ext_rat _ _) (funext H) rfl
    

theorem witt_structure_rat_rec_aux (Φ : MvPolynomial idx ℚ) (n : ℕ) :
    wittStructureRat p Φ n * c (p ^ n : ℚ) =
      bind₁ (fun b => rename (fun i => (b, i)) (W_ ℚ n)) Φ -
        ∑ i in range n, c (p ^ i : ℚ) * wittStructureRat p Φ i ^ p ^ (n - i) :=
  by
  have := X_in_terms_of_W_aux p ℚ n
  replace := congr_arg (bind₁ fun k : ℕ => bind₁ (fun i => rename (Prod.mk i) (W_ ℚ k)) Φ) this
  rw [AlgHom.map_mul, bind₁_C_right] at this
  rw [wittStructureRat, this]
  clear this
  conv_lhs => simp only [← AlgHom.map_sub, ← bind₁_X_right]
  rw [sub_right_inj]
  simp only [← AlgHom.map_sum, ← AlgHom.map_mul, ← bind₁_C_right, ← AlgHom.map_pow]
  rfl

/-- Write `witt_structure_rat p φ n` in terms of `witt_structure_rat p φ i` for `i < n`. -/
theorem witt_structure_rat_rec (Φ : MvPolynomial idx ℚ) (n : ℕ) :
    wittStructureRat p Φ n =
      c (1 / p ^ n : ℚ) *
        (bind₁ (fun b => rename (fun i => (b, i)) (W_ ℚ n)) Φ -
          ∑ i in range n, c (p ^ i : ℚ) * wittStructureRat p Φ i ^ p ^ (n - i)) :=
  by
  calc wittStructureRat p Φ n = C (1 / p ^ n : ℚ) * (wittStructureRat p Φ n * C (p ^ n : ℚ)) := _ _ = _ := by
      rw [witt_structure_rat_rec_aux]
  rw [mul_left_commₓ, ← C_mul, div_mul_cancel, C_1, mul_oneₓ]
  exact pow_ne_zero _ (Nat.cast_ne_zero.2 hp.1.ne_zero)

/-- `witt_structure_int Φ` is a family of polynomials `ℕ → mv_polynomial (idx × ℕ) ℤ`
that are uniquely characterised by the property that
```
bind₁ (witt_structure_int p Φ) (witt_polynomial p ℤ n) =
bind₁ (λ i, (rename (prod.mk i) (witt_polynomial p ℤ n))) Φ
```
In other words: evaluating the `n`-th Witt polynomial on the family `witt_structure_int Φ`
is the same as evaluating `Φ` on the (appropriately renamed) `n`-th Witt polynomials.

See `witt_structure_int_prop` for this property,
and `witt_structure_int_exists_unique` for the fact that `witt_structure_int`
gives the unique family of polynomials with this property. -/
noncomputable def wittStructureInt (Φ : MvPolynomial idx ℤ) (n : ℕ) : MvPolynomial (idx × ℕ) ℤ :=
  Finsupp.mapRange Rat.num (Rat.coe_int_num 0) (wittStructureRat p (map (Int.castRingHom ℚ) Φ) n)

variable {p}

theorem bind₁_rename_expand_witt_polynomial (Φ : MvPolynomial idx ℤ) (n : ℕ)
    (IH :
      ∀ m : ℕ,
        m < n + 1 →
          map (Int.castRingHom ℚ) (wittStructureInt p Φ m) = wittStructureRat p (map (Int.castRingHom ℚ) Φ) m) :
    bind₁ (fun b => rename (fun i => (b, i)) (expand p (W_ ℤ n))) Φ =
      bind₁ (fun i => expand p (wittStructureInt p Φ i)) (W_ ℤ n) :=
  by
  apply MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
  simp only [← map_bind₁, ← map_rename, ← map_expand, ← rename_expand, ← map_witt_polynomial]
  have key := (witt_structure_rat_prop p (map (Int.castRingHom ℚ) Φ) n).symm
  apply_fun expand p  at key
  simp only [← expand_bind₁] at key
  rw [key]
  clear key
  apply eval₂_hom_congr' rfl _ rfl
  rintro i hi -
  rw [witt_polynomial_vars, Finset.mem_range] at hi
  simp only [← IH i hi]

theorem C_p_pow_dvd_bind₁_rename_witt_polynomial_sub_sum (Φ : MvPolynomial idx ℤ) (n : ℕ)
    (IH :
      ∀ m : ℕ,
        m < n → map (Int.castRingHom ℚ) (wittStructureInt p Φ m) = wittStructureRat p (map (Int.castRingHom ℚ) Φ) m) :
    c ↑(p ^ n) ∣
      bind₁ (fun b : idx => rename (fun i => (b, i)) (wittPolynomial p ℤ n)) Φ -
        ∑ i in range n, c (↑p ^ i) * wittStructureInt p Φ i ^ p ^ (n - i) :=
  by
  cases n
  · simp only [← is_unit_one, ← Int.coe_nat_zero, ← Int.coe_nat_succ, ← zero_addₓ, ← pow_zeroₓ, ← C_1, ← IsUnit.dvd]
    
  -- prepare a useful equation for rewriting
  have key := bind₁_rename_expand_witt_polynomial Φ n IH
  apply_fun map (Int.castRingHom (Zmod (p ^ (n + 1))))  at key
  conv_lhs at key => simp only [← map_bind₁, ← map_rename, ← map_expand, ← map_witt_polynomial]
  -- clean up and massage
  rw [Nat.succ_eq_add_one, C_dvd_iff_zmod, RingHom.map_sub, sub_eq_zero, map_bind₁]
  simp only [← map_rename, ← map_witt_polynomial, ← witt_polynomial_zmod_self]
  rw [key]
  clear key IH
  rw [bind₁, aeval_witt_polynomial, RingHom.map_sum, RingHom.map_sum, Finset.sum_congr rfl]
  intro k hk
  rw [Finset.mem_range, Nat.lt_succ_iffₓ] at hk
  simp only [sub_eq_zero, RingHom.map_sub, C_dvd_iff_zmod, ← C_eq_coe_nat, mul_sub, Nat.cast_powₓ]
  rw
    [show p ^ (n + 1) = p ^ k * p ^ (n - k + 1) by
      rw [← pow_addₓ, ← add_assocₓ]
      congr 2
      rw [add_commₓ, ← tsub_eq_iff_eq_add_of_le hk]]
  rw [Nat.cast_mulₓ, Nat.cast_powₓ, Nat.cast_powₓ]
  apply mul_dvd_mul_left
  rw
    [show p ^ (n + 1 - k) = p * p ^ (n - k) by
      rw [← pow_succₓ, ← tsub_add_eq_add_tsub hk]]
  rw [pow_mulₓ]
  -- the machine!
  apply dvd_sub_pow_of_dvd_sub
  rw [← C_eq_coe_nat, C_dvd_iff_zmod, RingHom.map_sub, sub_eq_zero, map_expand, RingHom.map_pow,
    MvPolynomial.expand_zmod]

variable (p)

@[simp]
theorem map_witt_structure_int (Φ : MvPolynomial idx ℤ) (n : ℕ) :
    map (Int.castRingHom ℚ) (wittStructureInt p Φ n) = wittStructureRat p (map (Int.castRingHom ℚ) Φ) n := by
  apply Nat.strong_induction_onₓ n
  clear n
  intro n IH
  rw [wittStructureInt, map_map_range_eq_iff, Int.coe_cast_ring_hom]
  intro c
  rw [witt_structure_rat_rec, coeff_C_mul, mul_comm, mul_div_assoc', mul_oneₓ]
  have sum_induction_steps :
    map (Int.castRingHom ℚ) (∑ i in range n, C (p ^ i : ℤ) * wittStructureInt p Φ i ^ p ^ (n - i)) =
      ∑ i in range n, C (p ^ i : ℚ) * wittStructureRat p (map (Int.castRingHom ℚ) Φ) i ^ p ^ (n - i) :=
    by
    rw [RingHom.map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    simp only [← IH i hi, ← RingHom.map_mul, ← RingHom.map_pow, ← map_C]
    rfl
  simp only [sum_induction_steps, map_witt_polynomial p (Int.castRingHom ℚ), map_rename, map_bind₁, RingHom.map_sub, ←
    coeff_map]
  rw
    [show (p : ℚ) ^ n = ((p ^ n : ℕ) : ℤ) by
      norm_cast]
  rw [← Rat.denom_eq_one_iff, RingHom.eq_int_cast, Rat.denom_div_cast_eq_one_iff]
  swap
  · exact_mod_cast pow_ne_zero n hp.1.ne_zero
    
  revert c
  rw [← C_dvd_iff_dvd_coeff]
  exact C_p_pow_dvd_bind₁_rename_witt_polynomial_sub_sum Φ n IH

variable (p)

theorem witt_structure_int_prop (Φ : MvPolynomial idx ℤ) (n) :
    bind₁ (wittStructureInt p Φ) (wittPolynomial p ℤ n) = bind₁ (fun i => rename (Prod.mk i) (W_ ℤ n)) Φ := by
  apply MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
  have := witt_structure_rat_prop p (map (Int.castRingHom ℚ) Φ) n
  simpa only [← map_bind₁, eval₂_hom_map_hom, ← eval₂_hom_C_left, ← map_rename, ← map_witt_polynomial, ←
    AlgHom.coe_to_ring_hom, ← map_witt_structure_int]

theorem eq_witt_structure_int (Φ : MvPolynomial idx ℤ) (φ : ℕ → MvPolynomial (idx × ℕ) ℤ)
    (h : ∀ n, bind₁ φ (wittPolynomial p ℤ n) = bind₁ (fun i => rename (Prod.mk i) (W_ ℤ n)) Φ) :
    φ = wittStructureInt p Φ := by
  funext k
  apply MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
  rw [map_witt_structure_int]
  refine' congr_fun _ k
  apply unique_of_exists_unique (witt_structure_rat_exists_unique p (map (Int.castRingHom ℚ) Φ))
  · intro n
    specialize h n
    apply_fun map (Int.castRingHom ℚ)  at h
    simpa only [← map_bind₁, eval₂_hom_map_hom, ← eval₂_hom_C_left, ← map_rename, ← map_witt_polynomial, ←
      AlgHom.coe_to_ring_hom] using h
    
  · intro n
    apply witt_structure_rat_prop
    

theorem witt_structure_int_exists_unique (Φ : MvPolynomial idx ℤ) :
    ∃! φ : ℕ → MvPolynomial (idx × ℕ) ℤ,
      ∀ n : ℕ, bind₁ φ (wittPolynomial p ℤ n) = bind₁ (fun i : idx => rename (Prod.mk i) (W_ ℤ n)) Φ :=
  ⟨wittStructureInt p Φ, witt_structure_int_prop _ _, eq_witt_structure_int _ _⟩

theorem witt_structure_prop (Φ : MvPolynomial idx ℤ) (n) :
    aeval (fun i => map (Int.castRingHom R) (wittStructureInt p Φ i)) (wittPolynomial p ℤ n) =
      aeval (fun i => rename (Prod.mk i) (W n)) Φ :=
  by
  convert congr_arg (map (Int.castRingHom R)) (witt_structure_int_prop p Φ n) using 1 <;>
    rw [hom_bind₁] <;> apply eval₂_hom_congr (RingHom.ext_int _ _) _ rfl
  · rfl
    
  · simp only [← map_rename, ← map_witt_polynomial]
    

theorem witt_structure_int_rename {σ : Type _} (Φ : MvPolynomial idx ℤ) (f : idx → σ) (n : ℕ) :
    wittStructureInt p (rename f Φ) n = rename (Prod.map f id) (wittStructureInt p Φ n) := by
  apply MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
  simp only [← map_rename, ← map_witt_structure_int, ← wittStructureRat, ← rename_bind₁, ← rename_rename, ←
    bind₁_rename]
  rfl

@[simp]
theorem constant_coeff_witt_structure_rat_zero (Φ : MvPolynomial idx ℚ) :
    constantCoeff (wittStructureRat p Φ 0) = constantCoeff Φ := by
  simp only [← wittStructureRat, ← bind₁, ← map_aeval, ← X_in_terms_of_W_zero, ← constant_coeff_rename, ←
    constant_coeff_witt_polynomial, ← aeval_X, ← constant_coeff_comp_algebra_map, ← eval₂_hom_zero', ← RingHom.id_apply]

theorem constant_coeff_witt_structure_rat (Φ : MvPolynomial idx ℚ) (h : constantCoeff Φ = 0) (n : ℕ) :
    constantCoeff (wittStructureRat p Φ n) = 0 := by
  simp only [← wittStructureRat, ← eval₂_hom_zero', ← h, ← bind₁, ← map_aeval, ← constant_coeff_rename, ←
    constant_coeff_witt_polynomial, ← constant_coeff_comp_algebra_map, ← RingHom.id_apply, ←
    constant_coeff_X_in_terms_of_W]

@[simp]
theorem constant_coeff_witt_structure_int_zero (Φ : MvPolynomial idx ℤ) :
    constantCoeff (wittStructureInt p Φ 0) = constantCoeff Φ := by
  have inj : Function.Injective (Int.castRingHom ℚ) := by
    intro m n
    exact int.cast_inj.mp
  apply inj
  rw [← constant_coeff_map, map_witt_structure_int, constant_coeff_witt_structure_rat_zero, constant_coeff_map]

theorem constant_coeff_witt_structure_int (Φ : MvPolynomial idx ℤ) (h : constantCoeff Φ = 0) (n : ℕ) :
    constantCoeff (wittStructureInt p Φ n) = 0 := by
  have inj : Function.Injective (Int.castRingHom ℚ) := by
    intro m n
    exact int.cast_inj.mp
  apply inj
  rw [← constant_coeff_map, map_witt_structure_int, constant_coeff_witt_structure_rat, RingHom.map_zero]
  rw [constant_coeff_map, h, RingHom.map_zero]

variable (R)

-- we could relax the fintype on `idx`, but then we need to cast from finset to set.
-- for our applications `idx` is always finite.
theorem witt_structure_rat_vars [Fintype idx] (Φ : MvPolynomial idx ℚ) (n : ℕ) :
    (wittStructureRat p Φ n).vars ⊆ Finset.univ.product (Finset.range (n + 1)) := by
  rw [wittStructureRat]
  intro x hx
  simp only [← Finset.mem_product, ← true_andₓ, ← Finset.mem_univ, ← Finset.mem_range]
  obtain ⟨k, hk, hx'⟩ := mem_vars_bind₁ _ _ hx
  obtain ⟨i, -, hx''⟩ := mem_vars_bind₁ _ _ hx'
  obtain ⟨j, hj, rfl⟩ := mem_vars_rename _ _ hx''
  rw [witt_polynomial_vars, Finset.mem_range] at hj
  replace hk := X_in_terms_of_W_vars_subset p _ hk
  rw [Finset.mem_range] at hk
  exact lt_of_lt_of_leₓ hj hk

-- we could relax the fintype on `idx`, but then we need to cast from finset to set.
-- for our applications `idx` is always finite.
theorem witt_structure_int_vars [Fintype idx] (Φ : MvPolynomial idx ℤ) (n : ℕ) :
    (wittStructureInt p Φ n).vars ⊆ Finset.univ.product (Finset.range (n + 1)) := by
  have : Function.Injective (Int.castRingHom ℚ) := Int.cast_injective
  rw [← vars_map_of_injective _ this, map_witt_structure_int]
  apply witt_structure_rat_vars

end PPrime

