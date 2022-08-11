/-
Copyright (c) 2018 Louis Carlin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Louis Carlin, Mario Carneiro
-/
import Mathbin.Data.Int.Basic
import Mathbin.Algebra.Field.Basic

/-!
# Euclidean domains

This file introduces Euclidean domains and provides the extended Euclidean algorithm. To be precise,
a slightly more general version is provided which is sometimes called a transfinite Euclidean domain
and differs in the fact that the degree function need not take values in `ℕ` but can take values in
any well-ordered set. Transfinite Euclidean domains were introduced by Motzkin and examples which
don't satisfy the classical notion were provided independently by Hiblot and Nagata.

## Main definitions

* `euclidean_domain`: Defines Euclidean domain with functions `quotient` and `remainder`. Instances
  of `has_div` and `has_mod` are provided, so that one can write `a = b * (a / b) + a % b`.
* `gcd`: defines the greatest common divisors of two elements of a Euclidean domain.
* `xgcd`: given two elements `a b : R`, `xgcd a b` defines the pair `(x, y)` such that
  `x * a + y * b = gcd a b`.
* `lcm`: defines the lowest common multiple of two elements `a` and `b` of a Euclidean domain as
  `a * b / (gcd a b)`

## Main statements

* `gcd_eq_gcd_ab`: states Bézout's lemma for Euclidean domains.
* `int.euclidean_domain`: shows that `ℤ` is a Euclidean domain.
* `field.to_euclidean_domain`: shows that any field is a Euclidean domain.

## Notation

`≺` denotes the well founded relation on the Euclidean domain, e.g. in the example of the polynomial
ring over a field, `p ≺ q` for polynomials `p` and `q` if and only if the degree of `p` is less than
the degree of `q`.

## Implementation details

Instead of working with a valuation, `euclidean_domain` is implemented with the existence of a well
founded relation `r` on the integral domain `R`, which in the example of `ℤ` would correspond to
setting `i ≺ j` for integers `i` and `j` if the absolute value of `i` is smaller than the absolute
value of `j`.

## References

* [Th. Motzkin, *The Euclidean algorithm*][MR32592]
* [J.-J. Hiblot, *Des anneaux euclidiens dont le plus petit algorithme n'est pas à valeurs finies*]
  [MR399081]
* [M. Nagata, *On Euclid algorithm*][MR541021]


## Tags

Euclidean domain, transfinite Euclidean domain, Bézout's lemma
-/


universe u

/-- A `euclidean_domain` is an non-trivial commutative ring with a division and a remainder,
  satisfying `b * (a / b) + a % b = a`.
  The definition of a euclidean domain usually includes a valuation function `R → ℕ`.
  This definition is slightly generalised to include a well founded relation
  `r` with the property that `r (a % b) b`, instead of a valuation.  -/
@[protect_proj without mul_left_not_lt r_well_founded]
class EuclideanDomain (R : Type u) extends CommRingₓ R, Nontrivial R where
  Quotient : R → R → R
  quotient_zero : ∀ a, Quotientₓ a 0 = 0
  remainder : R → R → R
  quotient_mul_add_remainder_eq : ∀ a b, b * Quotientₓ a b + remainder a b = a
  R : R → R → Prop
  r_well_founded : WellFounded r
  remainder_lt : ∀ (a) {b}, b ≠ 0 → r (remainder a b) b
  mul_left_not_lt : ∀ (a) {b}, b ≠ 0 → ¬r (a * b) a

namespace EuclideanDomain

variable {R : Type u}

variable [EuclideanDomain R]

-- mathport name: «expr ≺ »
local infixl:50 " ≺ " => EuclideanDomain.R

-- see Note [lower instance priority]
instance (priority := 70) : Div R :=
  ⟨EuclideanDomain.quotient⟩

-- see Note [lower instance priority]
instance (priority := 70) : Mod R :=
  ⟨EuclideanDomain.remainder⟩

theorem div_add_mod (a b : R) : b * (a / b) + a % b = a :=
  EuclideanDomain.quotient_mul_add_remainder_eq _ _

theorem mod_add_div (a b : R) : a % b + b * (a / b) = a :=
  (add_commₓ _ _).trans (div_add_mod _ _)

theorem mod_add_div' (m k : R) : m % k + m / k * k = m := by
  rw [mul_comm]
  exact mod_add_div _ _

theorem div_add_mod' (m k : R) : m / k * k + m % k = m := by
  rw [mul_comm]
  exact div_add_mod _ _

theorem mod_eq_sub_mul_div {R : Type _} [EuclideanDomain R] (a b : R) : a % b = a - b * (a / b) :=
  calc
    a % b = b * (a / b) + a % b - b * (a / b) := (add_sub_cancel' _ _).symm
    _ = a - b * (a / b) := by
      rw [div_add_mod]
    

theorem mod_lt : ∀ (a) {b : R}, b ≠ 0 → a % b ≺ b :=
  EuclideanDomain.remainder_lt

theorem mul_right_not_lt {a : R} (b) (h : a ≠ 0) : ¬a * b ≺ b := by
  rw [mul_comm]
  exact mul_left_not_lt b h

theorem mul_div_cancel_left {a : R} (b) (a0 : a ≠ 0) : a * b / a = b :=
  Eq.symm <|
    eq_of_sub_eq_zero <|
      Classical.by_contradiction fun h => by
        have := mul_left_not_lt a h
        rw [mul_sub, sub_eq_iff_eq_add'.2 (div_add_mod (a * b) a).symm] at this
        exact this (mod_lt _ a0)

theorem mul_div_cancel (a) {b : R} (b0 : b ≠ 0) : a * b / b = a := by
  rw [mul_comm]
  exact mul_div_cancel_left a b0

@[simp]
theorem mod_zero (a : R) : a % 0 = a := by
  simpa only [← zero_mul, ← zero_addₓ] using div_add_mod a 0

@[simp]
theorem mod_eq_zero {a b : R} : a % b = 0 ↔ b ∣ a :=
  ⟨fun h => by
    rw [← div_add_mod a b, h, add_zeroₓ]
    exact dvd_mul_right _ _, fun ⟨c, e⟩ => by
    rw [e, ← add_left_cancel_iffₓ, div_add_mod, add_zeroₓ]
    have := Classical.dec
    by_cases' b0 : b = 0
    · simp only [← b0, ← zero_mul]
      
    · rw [mul_div_cancel_left _ b0]
      ⟩

@[simp]
theorem mod_self (a : R) : a % a = 0 :=
  mod_eq_zero.2 dvd_rfl

theorem dvd_mod_iff {a b c : R} (h : c ∣ b) : c ∣ a % b ↔ c ∣ a := by
  rw [dvd_add_iff_right (h.mul_right _), div_add_mod]

theorem lt_one (a : R) : a ≺ (1 : R) → a = 0 := by
  have := Classical.dec
  exact
    not_imp_not.1 fun h => by
      simpa only [← one_mulₓ] using mul_left_not_lt 1 h

theorem val_dvd_le : ∀ a b : R, b ∣ a → a ≠ 0 → ¬a ≺ b
  | _, b, ⟨d, rfl⟩, ha =>
    mul_left_not_lt b
      (mt
        (by
          rintro rfl
          exact mul_zero _)
        ha)

@[simp]
theorem mod_one (a : R) : a % 1 = 0 :=
  mod_eq_zero.2 (one_dvd _)

@[simp]
theorem zero_mod (b : R) : 0 % b = 0 :=
  mod_eq_zero.2 (dvd_zero _)

@[simp]
theorem div_zero (a : R) : a / 0 = 0 :=
  EuclideanDomain.quotient_zero a

@[simp]
theorem zero_div {a : R} : 0 / a = 0 :=
  Classical.by_cases (fun a0 : a = 0 => a0.symm ▸ div_zero 0) fun a0 => by
    simpa only [← zero_mul] using mul_div_cancel 0 a0

@[simp]
theorem div_self {a : R} (a0 : a ≠ 0) : a / a = 1 := by
  simpa only [← one_mulₓ] using mul_div_cancel 1 a0

theorem eq_div_of_mul_eq_left {a b c : R} (hb : b ≠ 0) (h : a * b = c) : a = c / b := by
  rw [← h, mul_div_cancel _ hb]

theorem eq_div_of_mul_eq_right {a b c : R} (ha : a ≠ 0) (h : a * b = c) : b = c / a := by
  rw [← h, mul_div_cancel_left _ ha]

theorem mul_div_assoc (x : R) {y z : R} (h : z ∣ y) : x * y / z = x * (y / z) := by
  classical
  by_cases' hz : z = 0
  · subst hz
    rw [div_zero, div_zero, mul_zero]
    
  rcases h with ⟨p, rfl⟩
  rw [mul_div_cancel_left _ hz, mul_left_commₓ, mul_div_cancel_left _ hz]

-- This generalizes `int.div_one`, see note [simp-normal form]
@[simp]
theorem div_one (p : R) : p / 1 = p :=
  (EuclideanDomain.eq_div_of_mul_eq_left (@one_ne_zero R _ _) (mul_oneₓ p)).symm

theorem div_dvd_of_dvd {p q : R} (hpq : q ∣ p) : p / q ∣ p := by
  by_cases' hq : q = 0
  · rw [hq, zero_dvd_iff] at hpq
    rw [hpq]
    exact dvd_zero _
    
  use q
  rw [mul_comm, ← EuclideanDomain.mul_div_assoc _ hpq, mul_comm, EuclideanDomain.mul_div_cancel _ hq]

theorem dvd_div_of_mul_dvd {a b c : R} (h : a * b ∣ c) : b ∣ c / a := by
  rcases eq_or_ne a 0 with (rfl | ha)
  · simp only [← div_zero, ← dvd_zero]
    
  rcases h with ⟨d, rfl⟩
  refine' ⟨d, _⟩
  rw [mul_assoc, mul_div_cancel_left _ ha]

section

open Classical

@[elab_as_eliminator]
theorem Gcd.induction {P : R → R → Prop} : ∀ a b : R, (∀ x, P 0 x) → (∀ a b, a ≠ 0 → P (b % a) a → P a b) → P a b
  | a => fun b H0 H1 =>
    if a0 : a = 0 then a0.symm ▸ H0 _
    else
      have h := mod_lt b a0
      H1 _ _ a0 (gcd.induction (b % a) a H0 H1)

end

section Gcd

variable [DecidableEq R]

/-- `gcd a b` is a (non-unique) element such that `gcd a b ∣ a` `gcd a b ∣ b`, and for
  any element `c` such that `c ∣ a` and `c ∣ b`, then `c ∣ gcd a b` -/
def gcd : R → R → R
  | a => fun b =>
    if a0 : a = 0 then b
    else
      have h := mod_lt b a0
      gcd (b % a) a

@[simp]
theorem gcd_zero_left (a : R) : gcd 0 a = a := by
  rw [gcd]
  exact if_pos rfl

@[simp]
theorem gcd_zero_right (a : R) : gcd a 0 = a := by
  rw [gcd]
  split_ifs <;> simp only [← h, ← zero_mod, ← gcd_zero_left]

theorem gcd_val (a b : R) : gcd a b = gcd (b % a) a := by
  rw [gcd]
  split_ifs <;> [simp only [← h, ← mod_zero, ← gcd_zero_right], rfl]

theorem gcd_dvd (a b : R) : gcd a b ∣ a ∧ gcd a b ∣ b :=
  Gcd.induction a b
    (fun b => by
      rw [gcd_zero_left]
      exact ⟨dvd_zero _, dvd_rfl⟩)
    fun a b aneq ⟨IH₁, IH₂⟩ => by
    rw [gcd_val]
    exact ⟨IH₂, (dvd_mod_iff IH₂).1 IH₁⟩

theorem gcd_dvd_left (a b : R) : gcd a b ∣ a :=
  (gcd_dvd a b).left

theorem gcd_dvd_right (a b : R) : gcd a b ∣ b :=
  (gcd_dvd a b).right

protected theorem gcd_eq_zero_iff {a b : R} : gcd a b = 0 ↔ a = 0 ∧ b = 0 :=
  ⟨fun h => by
    simpa [← h] using gcd_dvd a b, by
    rintro ⟨rfl, rfl⟩
    exact gcd_zero_right _⟩

theorem dvd_gcd {a b c : R} : c ∣ a → c ∣ b → c ∣ gcd a b :=
  Gcd.induction a b
    (fun _ _ H => by
      simpa only [← gcd_zero_left] using H)
    fun a b a0 IH ca cb => by
    rw [gcd_val]
    exact IH ((dvd_mod_iff ca).2 cb) ca

theorem gcd_eq_left {a b : R} : gcd a b = a ↔ a ∣ b :=
  ⟨fun h => by
    rw [← h]
    apply gcd_dvd_right, fun h => by
    rw [gcd_val, mod_eq_zero.2 h, gcd_zero_left]⟩

@[simp]
theorem gcd_one_left (a : R) : gcd 1 a = 1 :=
  gcd_eq_left.2 (one_dvd _)

@[simp]
theorem gcd_self (a : R) : gcd a a = a :=
  gcd_eq_left.2 dvd_rfl

/-- An implementation of the extended GCD algorithm.
At each step we are computing a triple `(r, s, t)`, where `r` is the next value of the GCD
algorithm, to compute the greatest common divisor of the input (say `x` and `y`), and `s` and `t`
are the coefficients in front of `x` and `y` to obtain `r` (i.e. `r = s * x + t * y`).
The function `xgcd_aux` takes in two triples, and from these recursively computes the next triple:
```
xgcd_aux (r, s, t) (r', s', t') = xgcd_aux (r' % r, s' - (r' / r) * s, t' - (r' / r) * t) (r, s, t)
```
-/
def xgcdAux : R → R → R → R → R → R → R × R × R
  | r => fun s t r' s' t' =>
    if hr : r = 0 then (r', s', t')
    else
      have : r' % r ≺ r := mod_lt _ hr
      let q := r' / r
      xgcd_aux (r' % r) (s' - q * s) (t' - q * t) r s t

@[simp]
theorem xgcd_zero_left {s t r' s' t' : R} : xgcdAux 0 s t r' s' t' = (r', s', t') := by
  unfold xgcd_aux
  exact if_pos rfl

theorem xgcd_aux_rec {r s t r' s' t' : R} (h : r ≠ 0) :
    xgcdAux r s t r' s' t' = xgcdAux (r' % r) (s' - r' / r * s) (t' - r' / r * t) r s t := by
  conv => lhs rw [xgcd_aux]
  exact if_neg h

/-- Use the extended GCD algorithm to generate the `a` and `b` values
  satisfying `gcd x y = x * a + y * b`. -/
def xgcd (x y : R) : R × R :=
  (xgcdAux x 1 0 y 0 1).2

/-- The extended GCD `a` value in the equation `gcd x y = x * a + y * b`. -/
def gcdA (x y : R) : R :=
  (xgcd x y).1

/-- The extended GCD `b` value in the equation `gcd x y = x * a + y * b`. -/
def gcdB (x y : R) : R :=
  (xgcd x y).2

@[simp]
theorem gcd_a_zero_left {s : R} : gcdA 0 s = 0 := by
  unfold gcd_a
  rw [xgcd, xgcd_zero_left]

@[simp]
theorem gcd_b_zero_left {s : R} : gcdB 0 s = 1 := by
  unfold gcd_b
  rw [xgcd, xgcd_zero_left]

@[simp]
theorem xgcd_aux_fst (x y : R) : ∀ s t s' t', (xgcdAux x s t y s' t').1 = gcd x y :=
  Gcd.induction x y
    (by
      intros
      rw [xgcd_zero_left, gcd_zero_left])
    fun x y h IH s t s' t' => by
    simp only [← xgcd_aux_rec h, ← if_neg h, ← IH]
    rw [← gcd_val]

theorem xgcd_aux_val (x y : R) : xgcdAux x 1 0 y 0 1 = (gcd x y, xgcd x y) := by
  rw [xgcd, ← xgcd_aux_fst x y 1 0 0 1, Prod.mk.eta]

theorem xgcd_val (x y : R) : xgcd x y = (gcdA x y, gcdB x y) :=
  Prod.mk.eta.symm

private def P (a b : R) : R × R × R → Prop
  | (r, s, t) => (r : R) = a * s + b * t

theorem xgcd_aux_P (a b : R) {r r' : R} :
    ∀ {s t s' t'}, Pₓ a b (r, s, t) → Pₓ a b (r', s', t') → Pₓ a b (xgcdAux r s t r' s' t') :=
  (Gcd.induction r r'
      (by
        intros
        simpa only [← xgcd_zero_left] ))
    fun x y h IH s t s' t' p p' => by
    rw [xgcd_aux_rec h]
    refine' IH _ p
    unfold P  at p p'⊢
    rw [mul_sub, mul_sub, add_sub, sub_add_eq_add_sub, ← p', sub_sub, mul_comm _ s, ← mul_assoc, mul_comm _ t, ←
      mul_assoc, ← add_mulₓ, ← p, mod_eq_sub_mul_div]

/-- An explicit version of **Bézout's lemma** for Euclidean domains. -/
theorem gcd_eq_gcd_ab (a b : R) : (gcd a b : R) = a * gcdA a b + b * gcdB a b := by
  have :=
    @xgcd_aux_P _ _ _ a b a b 1 0 0 1
      (by
        rw [P, mul_oneₓ, mul_zero, add_zeroₓ])
      (by
        rw [P, mul_oneₓ, mul_zero, zero_addₓ])
  rwa [xgcd_aux_val, xgcd_val] at this

-- see Note [lower instance priority]
instance (priority := 70) (R : Type _) [e : EuclideanDomain R] : IsDomain R := by
  have := Classical.decEq R
  exact
    { e with
      eq_zero_or_eq_zero_of_mul_eq_zero := fun a b h =>
        or_iff_not_and_not.2 fun h0 =>
          h0.1 <| by
            rw [← mul_div_cancel a h0.2, h, zero_div] }

end Gcd

section Lcm

variable [DecidableEq R]

/-- `lcm a b` is a (non-unique) element such that `a ∣ lcm a b` `b ∣ lcm a b`, and for
  any element `c` such that `a ∣ c` and `b ∣ c`, then `lcm a b ∣ c` -/
def lcm (x y : R) : R :=
  x * y / gcd x y

theorem dvd_lcm_left (x y : R) : x ∣ lcm x y :=
  Classical.by_cases
    (fun hxy : gcd x y = 0 => by
      rw [lcm, hxy, div_zero]
      exact dvd_zero _)
    fun hxy =>
    let ⟨z, hz⟩ := (gcd_dvd x y).2
    ⟨z,
      Eq.symm <|
        eq_div_of_mul_eq_left hxy <| by
          rw [mul_right_commₓ, mul_assoc, ← hz]⟩

theorem dvd_lcm_right (x y : R) : y ∣ lcm x y :=
  Classical.by_cases
    (fun hxy : gcd x y = 0 => by
      rw [lcm, hxy, div_zero]
      exact dvd_zero _)
    fun hxy =>
    let ⟨z, hz⟩ := (gcd_dvd x y).1
    ⟨z,
      Eq.symm <|
        eq_div_of_mul_eq_right hxy <| by
          rw [← mul_assoc, mul_right_commₓ, ← hz]⟩

theorem lcm_dvd {x y z : R} (hxz : x ∣ z) (hyz : y ∣ z) : lcm x y ∣ z := by
  rw [lcm]
  by_cases' hxy : gcd x y = 0
  · rw [hxy, div_zero]
    rw [EuclideanDomain.gcd_eq_zero_iff] at hxy
    rwa [hxy.1] at hxz
    
  rcases gcd_dvd x y with ⟨⟨r, hr⟩, ⟨s, hs⟩⟩
  suffices x * y ∣ z * gcd x y by
    cases' this with p hp
    use p
    generalize gcd x y = g  at hxy hs hp⊢
    subst hs
    rw [mul_left_commₓ, mul_div_cancel_left _ hxy, ← mul_left_inj' hxy, hp]
    rw [← mul_assoc]
    simp only [← mul_right_commₓ]
  rw [gcd_eq_gcd_ab, mul_addₓ]
  apply dvd_add
  · rw [mul_left_commₓ]
    exact mul_dvd_mul_left _ (hyz.mul_right _)
    
  · rw [mul_left_commₓ, mul_comm]
    exact mul_dvd_mul_left _ (hxz.mul_right _)
    

@[simp]
theorem lcm_dvd_iff {x y z : R} : lcm x y ∣ z ↔ x ∣ z ∧ y ∣ z :=
  ⟨fun hz => ⟨(dvd_lcm_left _ _).trans hz, (dvd_lcm_right _ _).trans hz⟩, fun ⟨hxz, hyz⟩ => lcm_dvd hxz hyz⟩

@[simp]
theorem lcm_zero_left (x : R) : lcm 0 x = 0 := by
  rw [lcm, zero_mul, zero_div]

@[simp]
theorem lcm_zero_right (x : R) : lcm x 0 = 0 := by
  rw [lcm, mul_zero, zero_div]

@[simp]
theorem lcm_eq_zero_iff {x y : R} : lcm x y = 0 ↔ x = 0 ∨ y = 0 := by
  constructor
  · intro hxy
    rw [lcm, mul_div_assoc _ (gcd_dvd_right _ _), mul_eq_zero] at hxy
    apply or_of_or_of_imp_right hxy
    intro hy
    by_cases' hgxy : gcd x y = 0
    · rw [EuclideanDomain.gcd_eq_zero_iff] at hgxy
      exact hgxy.2
      
    · rcases gcd_dvd x y with ⟨⟨r, hr⟩, ⟨s, hs⟩⟩
      generalize gcd x y = g  at hr hs hy hgxy⊢
      subst hs
      rw [mul_div_cancel_left _ hgxy] at hy
      rw [hy, mul_zero]
      
    
  rintro (hx | hy)
  · rw [hx, lcm_zero_left]
    
  · rw [hy, lcm_zero_right]
    

@[simp]
theorem gcd_mul_lcm (x y : R) : gcd x y * lcm x y = x * y := by
  rw [lcm]
  by_cases' h : gcd x y = 0
  · rw [h, zero_mul]
    rw [EuclideanDomain.gcd_eq_zero_iff] at h
    rw [h.1, zero_mul]
    
  rcases gcd_dvd x y with ⟨⟨r, hr⟩, ⟨s, hs⟩⟩
  generalize gcd x y = g  at h hr⊢
  subst hr
  rw [mul_assoc, mul_div_cancel_left _ h]

end Lcm

section Div

theorem mul_div_mul_cancel {a b c : R} (ha : a ≠ 0) (hcb : c ∣ b) : a * b / (a * c) = b / c := by
  by_cases' hc : c = 0
  · simp [← hc]
    
  refine' eq_div_of_mul_eq_right hc (mul_left_cancel₀ ha _)
  rw [← mul_assoc, ← mul_div_assoc _ (mul_dvd_mul_left a hcb), mul_div_cancel_left _ (mul_ne_zero ha hc)]

theorem mul_div_mul_comm_of_dvd_dvd {a b c d : R} (hac : c ∣ a) (hbd : d ∣ b) : a * b / (c * d) = a / c * (b / d) := by
  rcases eq_or_ne c 0 with (rfl | hc0)
  · simp
    
  rcases eq_or_ne d 0 with (rfl | hd0)
  · simp
    
  obtain ⟨k1, rfl⟩ := hac
  obtain ⟨k2, rfl⟩ := hbd
  rw [mul_div_cancel_left _ hc0, mul_div_cancel_left _ hd0, mul_mul_mul_commₓ,
    mul_div_cancel_left _ (mul_ne_zero hc0 hd0)]

end Div

end EuclideanDomain

instance Int.euclideanDomain : EuclideanDomain ℤ :=
  { Int.commRing, Int.nontrivial with add := (· + ·), mul := (· * ·), one := 1, zero := 0, neg := Neg.neg,
    Quotient := (· / ·), quotient_zero := Int.div_zero, remainder := (· % ·),
    quotient_mul_add_remainder_eq := fun a b => Int.div_add_mod _ _, R := fun a b => a.natAbs < b.natAbs,
    r_well_founded := measure_wf fun a => Int.natAbs a,
    remainder_lt := fun a b b0 =>
      Int.coe_nat_lt.1 <| by
        rw [Int.nat_abs_of_nonneg (Int.mod_nonneg _ b0), ← Int.abs_eq_nat_abs]
        exact Int.mod_lt _ b0,
    mul_left_not_lt := fun a b b0 =>
      not_lt_of_geₓ <| by
        rw [← mul_oneₓ a.nat_abs, Int.nat_abs_mul]
        exact mul_le_mul_of_nonneg_left (Int.nat_abs_pos_of_ne_zero b0) (Nat.zero_leₓ _) }

-- see Note [lower instance priority]
instance (priority := 100) Field.toEuclideanDomain {K : Type u} [Field K] : EuclideanDomain K :=
  { ‹Field K› with add := (· + ·), mul := (· * ·), one := 1, zero := 0, neg := Neg.neg, Quotient := (· / ·),
    remainder := fun a b => a - a * b / b, quotient_zero := div_zero,
    quotient_mul_add_remainder_eq := fun a b => by
      classical
      by_cases' b = 0 <;> simp [← h, ← mul_div_cancel'],
    R := fun a b => a = 0 ∧ b ≠ 0,
    r_well_founded :=
      WellFounded.intro fun a => (Acc.intro _) fun b ⟨hb, hna⟩ => (Acc.intro _) fun c ⟨hc, hnb⟩ => False.elim <| hnb hb,
    remainder_lt := fun a b hnb => by
      simp [← hnb],
    mul_left_not_lt := fun a b hnb ⟨hab, hna⟩ => Or.cases_on (mul_eq_zero.1 hab) hna hnb }

