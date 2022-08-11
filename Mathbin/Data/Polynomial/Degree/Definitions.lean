/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Scott Morrison, Jens Wagemaker
-/
import Mathbin.Data.Nat.WithBot
import Mathbin.Data.Polynomial.Induction
import Mathbin.Data.Polynomial.Monomial

/-!
# Theory of univariate polynomials

The definitions include
`degree`, `monic`, `leading_coeff`

Results include
- `degree_mul` : The degree of the product is the sum of degrees
- `leading_coeff_add_of_degree_eq` and `leading_coeff_add_of_degree_lt` :
    The leading_coefficient of a sum is determined by the leading coefficients and degrees
-/


noncomputable section

open Finsupp Finset

open BigOperators Classical Polynomial

namespace Polynomial

universe u v

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

section Semiringₓ

variable [Semiringₓ R] {p q r : R[X]}

/-- `degree p` is the degree of the polynomial `p`, i.e. the largest `X`-exponent in `p`.
`degree p = some n` when `p ≠ 0` and `n` is the highest power of `X` that appears in `p`, otherwise
`degree 0 = ⊥`. -/
def degree (p : R[X]) : WithBot ℕ :=
  p.Support.sup coe

theorem degree_lt_wf : WellFounded fun p q : R[X] => degree p < degree q :=
  InvImage.wfₓ degree (WithBot.well_founded_lt Nat.lt_wf)

instance : HasWellFounded R[X] :=
  ⟨_, degree_lt_wf⟩

/-- `nat_degree p` forces `degree p` to ℕ, by defining nat_degree 0 = 0. -/
def natDegree (p : R[X]) : ℕ :=
  (degree p).getOrElse 0

/-- `leading_coeff p` gives the coefficient of the highest power of `X` in `p`-/
def leadingCoeff (p : R[X]) : R :=
  coeff p (natDegree p)

/-- a polynomial is `monic` if its leading coefficient is 1 -/
def Monic (p : R[X]) :=
  leadingCoeff p = (1 : R)

@[nontriviality]
theorem monic_of_subsingleton [Subsingleton R] (p : R[X]) : Monic p :=
  Subsingleton.elimₓ _ _

theorem Monic.def : Monic p ↔ leadingCoeff p = 1 :=
  Iff.rfl

instance Monic.decidable [DecidableEq R] : Decidable (Monic p) := by
  unfold monic <;> infer_instance

@[simp]
theorem Monic.leading_coeff {p : R[X]} (hp : p.Monic) : leadingCoeff p = 1 :=
  hp

theorem Monic.coeff_nat_degree {p : R[X]} (hp : p.Monic) : p.coeff p.natDegree = 1 :=
  hp

@[simp]
theorem degree_zero : degree (0 : R[X]) = ⊥ :=
  rfl

@[simp]
theorem nat_degree_zero : natDegree (0 : R[X]) = 0 :=
  rfl

@[simp]
theorem coeff_nat_degree : coeff p (natDegree p) = leadingCoeff p :=
  rfl

theorem degree_eq_bot : degree p = ⊥ ↔ p = 0 :=
  ⟨fun h => support_eq_empty.1 (Finset.max_eq_bot.1 h), fun h => h.symm ▸ rfl⟩

@[nontriviality]
theorem degree_of_subsingleton [Subsingleton R] : degree p = ⊥ := by
  rw [Subsingleton.elimₓ p 0, degree_zero]

@[nontriviality]
theorem nat_degree_of_subsingleton [Subsingleton R] : natDegree p = 0 := by
  rw [Subsingleton.elimₓ p 0, nat_degree_zero]

theorem degree_eq_nat_degree (hp : p ≠ 0) : degree p = (natDegree p : WithBot ℕ) := by
  let ⟨n, hn⟩ := not_forall.1 (mt Option.eq_none_iff_forall_not_mem.2 (mt degree_eq_bot.1 hp))
  have hn : degree p = some n := not_not.1 hn
  rw [nat_degree, hn] <;> rfl

theorem degree_eq_iff_nat_degree_eq {p : R[X]} {n : ℕ} (hp : p ≠ 0) : p.degree = n ↔ p.natDegree = n := by
  rw [degree_eq_nat_degree hp, WithBot.coe_eq_coe]

theorem degree_eq_iff_nat_degree_eq_of_pos {p : R[X]} {n : ℕ} (hn : 0 < n) : p.degree = n ↔ p.natDegree = n := by
  constructor
  · intro H
    rwa [← degree_eq_iff_nat_degree_eq]
    rintro rfl
    rw [degree_zero] at H
    exact Option.noConfusion H
    
  · intro H
    rwa [degree_eq_iff_nat_degree_eq]
    rintro rfl
    rw [nat_degree_zero] at H
    rw [H] at hn
    exact lt_irreflₓ _ hn
    

theorem nat_degree_eq_of_degree_eq_some {p : R[X]} {n : ℕ} (h : degree p = n) : natDegree p = n :=
  have hp0 : p ≠ 0 := fun hp0 => by
    rw [hp0] at h <;> exact Option.noConfusion h
  Option.some_inj.1 <|
    show (natDegree p : WithBot ℕ) = n by
      rwa [← degree_eq_nat_degree hp0]

@[simp]
theorem degree_le_nat_degree : degree p ≤ natDegree p :=
  WithBot.giGetOrElseBot.gc.le_u_l _

theorem nat_degree_eq_of_degree_eq [Semiringₓ S] {q : S[X]} (h : degree p = degree q) : natDegree p = natDegree q := by
  unfold nat_degree <;> rw [h]

theorem le_degree_of_ne_zero (h : coeff p n ≠ 0) : (n : WithBot ℕ) ≤ degree p :=
  show @LE.le (WithBot ℕ) _ (some n : WithBot ℕ) (p.Support.sup some : WithBot ℕ) from
    Finset.le_sup (mem_support_iff.2 h)

theorem le_nat_degree_of_ne_zero (h : coeff p n ≠ 0) : n ≤ natDegree p := by
  rw [← WithBot.coe_le_coe, ← degree_eq_nat_degree]
  exact le_degree_of_ne_zero h
  · intro h
    subst h
    exact h rfl
    

theorem le_nat_degree_of_mem_supp (a : ℕ) : a ∈ p.Support → a ≤ natDegree p :=
  le_nat_degree_of_ne_zero ∘ mem_support_iff.mp

theorem degree_mono [Semiringₓ S] {f : R[X]} {g : S[X]} (h : f.Support ⊆ g.Support) : f.degree ≤ g.degree :=
  Finset.sup_mono h

theorem supp_subset_range (h : natDegree p < m) : p.Support ⊆ Finset.range m := fun n hn =>
  mem_range.2 <| (le_nat_degree_of_mem_supp _ hn).trans_lt h

theorem supp_subset_range_nat_degree_succ : p.Support ⊆ Finset.range (natDegree p + 1) :=
  supp_subset_range (Nat.lt_succ_selfₓ _)

theorem degree_le_degree (h : coeff q (natDegree p) ≠ 0) : degree p ≤ degree q := by
  by_cases' hp : p = 0
  · rw [hp]
    exact bot_le
    
  · rw [degree_eq_nat_degree hp]
    exact le_degree_of_ne_zero h
    

theorem degree_ne_of_nat_degree_ne {n : ℕ} : p.natDegree ≠ n → degree p ≠ n :=
  mt fun h => by
    rw [nat_degree, h, Option.get_or_else_coe]

theorem nat_degree_le_iff_degree_le {n : ℕ} : natDegree p ≤ n ↔ degree p ≤ n :=
  WithBot.get_or_else_bot_le_iff

theorem nat_degree_lt_iff_degree_lt (hp : p ≠ 0) : p.natDegree < n ↔ p.degree < ↑n :=
  WithBot.get_or_else_bot_lt_iff <| degree_eq_bot.Not.mpr hp

alias nat_degree_le_iff_degree_le ↔ ..

theorem nat_degree_le_nat_degree [Semiringₓ S] {q : S[X]} (hpq : p.degree ≤ q.degree) : p.natDegree ≤ q.natDegree :=
  WithBot.giGetOrElseBot.gc.monotone_l hpq

@[simp]
theorem degree_C (ha : a ≠ 0) : degree (c a) = (0 : WithBot ℕ) := by
  rw [degree, ← monomial_zero_left, support_monomial 0 ha, sup_singleton]
  rfl

theorem degree_C_le : degree (c a) ≤ 0 := by
  by_cases' h : a = 0
  · rw [h, C_0]
    exact bot_le
    
  · rw [degree_C h]
    exact le_rfl
    

theorem degree_C_lt : degree (c a) < 1 :=
  degree_C_le.trans_lt <| WithBot.coe_lt_coe.mpr zero_lt_one

theorem degree_one_le : degree (1 : R[X]) ≤ (0 : WithBot ℕ) := by
  rw [← C_1] <;> exact degree_C_le

@[simp]
theorem nat_degree_C (a : R) : natDegree (c a) = 0 := by
  by_cases' ha : a = 0
  · have : C a = 0 := by
      rw [ha, C_0]
    rw [nat_degree, degree_eq_bot.2 this]
    rfl
    
  · rw [nat_degree, degree_C ha]
    rfl
    

@[simp]
theorem nat_degree_one : natDegree (1 : R[X]) = 0 :=
  nat_degree_C 1

@[simp]
theorem nat_degree_nat_cast (n : ℕ) : natDegree (n : R[X]) = 0 := by
  simp only [C_eq_nat_cast, ← nat_degree_C]

@[simp]
theorem degree_monomial (n : ℕ) (ha : a ≠ 0) : degree (monomial n a) = n := by
  rw [degree, support_monomial n ha] <;> rfl

@[simp]
theorem degree_C_mul_X_pow (n : ℕ) (ha : a ≠ 0) : degree (c a * X ^ n) = n := by
  rw [← monomial_eq_C_mul_X, degree_monomial n ha]

theorem degree_C_mul_X (ha : a ≠ 0) : degree (c a * X) = 1 := by
  simpa only [← pow_oneₓ] using degree_C_mul_X_pow 1 ha

theorem degree_monomial_le (n : ℕ) (a : R) : degree (monomial n a) ≤ n :=
  if h : a = 0 then by
    rw [h, (monomial n).map_zero] <;> exact bot_le
  else le_of_eqₓ (degree_monomial n h)

theorem degree_C_mul_X_pow_le (n : ℕ) (a : R) : degree (c a * X ^ n) ≤ n := by
  rw [C_mul_X_pow_eq_monomial]
  apply degree_monomial_le

theorem degree_C_mul_X_le (a : R) : degree (c a * X) ≤ 1 := by
  simpa only [← pow_oneₓ] using degree_C_mul_X_pow_le 1 a

@[simp]
theorem nat_degree_C_mul_X_pow (n : ℕ) (a : R) (ha : a ≠ 0) : natDegree (c a * X ^ n) = n :=
  nat_degree_eq_of_degree_eq_some (degree_C_mul_X_pow n ha)

@[simp]
theorem nat_degree_C_mul_X (a : R) (ha : a ≠ 0) : natDegree (c a * X) = 1 := by
  simpa only [← pow_oneₓ] using nat_degree_C_mul_X_pow 1 a ha

@[simp]
theorem nat_degree_monomial [DecidableEq R] (i : ℕ) (r : R) : natDegree (monomial i r) = if r = 0 then 0 else i := by
  split_ifs with hr
  · simp [← hr]
    
  · rw [← C_mul_X_pow_eq_monomial, nat_degree_C_mul_X_pow i r hr]
    

theorem nat_degree_monomial_le (a : R) {m : ℕ} : (monomial m a).natDegree ≤ m := by
  rw [Polynomial.nat_degree_monomial]
  split_ifs
  exacts[Nat.zero_leₓ _, rfl.le]

theorem nat_degree_monomial_eq (i : ℕ) {r : R} (r0 : r ≠ 0) : (monomial i r).natDegree = i :=
  Eq.trans (nat_degree_monomial _ _) (if_neg r0)

theorem coeff_eq_zero_of_degree_lt (h : degree p < n) : coeff p n = 0 :=
  not_not.1 (mt le_degree_of_ne_zero (not_le_of_gtₓ h))

theorem coeff_eq_zero_of_nat_degree_lt {p : R[X]} {n : ℕ} (h : p.natDegree < n) : p.coeff n = 0 := by
  apply coeff_eq_zero_of_degree_lt
  by_cases' hp : p = 0
  · subst hp
    exact WithBot.bot_lt_coe n
    
  · rwa [degree_eq_nat_degree hp, WithBot.coe_lt_coe]
    

@[simp]
theorem coeff_nat_degree_succ_eq_zero {p : R[X]} : p.coeff (p.natDegree + 1) = 0 :=
  coeff_eq_zero_of_nat_degree_lt (lt_add_one _)

-- We need the explicit `decidable` argument here because an exotic one shows up in a moment!
theorem ite_le_nat_degree_coeff (p : R[X]) (n : ℕ) (I : Decidable (n < 1 + natDegree p)) :
    @ite _ (n < 1 + natDegree p) I (coeff p n) 0 = coeff p n := by
  split_ifs
  · rfl
    
  · exact (coeff_eq_zero_of_nat_degree_lt (not_leₓ.1 fun w => h (Nat.lt_one_add_iff.2 w))).symm
    

theorem as_sum_support (p : R[X]) : p = ∑ i in p.Support, monomial i (p.coeff i) :=
  (sum_monomial_eq p).symm

theorem as_sum_support_C_mul_X_pow (p : R[X]) : p = ∑ i in p.Support, c (p.coeff i) * X ^ i :=
  trans p.as_sum_support <| by
    simp only [← C_mul_X_pow_eq_monomial]

/-- We can reexpress a sum over `p.support` as a sum over `range n`,
for any `n` satisfying `p.nat_degree < n`.
-/
theorem sum_over_range' [AddCommMonoidₓ S] (p : R[X]) {f : ℕ → R → S} (h : ∀ n, f n 0 = 0) (n : ℕ)
    (w : p.natDegree < n) : p.Sum f = ∑ a : ℕ in range n, f a (coeff p a) := by
  rcases p with ⟨⟩
  have := supp_subset_range w
  simp only [← Polynomial.sum, ← support, ← coeff, ← nat_degree, ← degree] at this⊢
  exact Finsupp.sum_of_support_subset _ this _ fun n hn => h n

/-- We can reexpress a sum over `p.support` as a sum over `range (p.nat_degree + 1)`.
-/
theorem sum_over_range [AddCommMonoidₓ S] (p : R[X]) {f : ℕ → R → S} (h : ∀ n, f n 0 = 0) :
    p.Sum f = ∑ a : ℕ in range (p.natDegree + 1), f a (coeff p a) :=
  sum_over_range' p h (p.natDegree + 1) (lt_add_one _)

-- TODO this is essentially a duplicate of `sum_over_range`, and should be removed.
theorem sum_fin [AddCommMonoidₓ S] (f : ℕ → R → S) (hf : ∀ i, f i 0 = 0) {n : ℕ} {p : R[X]} (hn : p.degree < n) :
    (∑ i : Finₓ n, f i (p.coeff i)) = p.Sum f := by
  by_cases' hp : p = 0
  · rw [hp, sum_zero_index, Finset.sum_eq_zero]
    intro i _
    exact hf i
    
  rw [sum_over_range' _ hf n ((nat_degree_lt_iff_degree_lt hp).mpr hn),
    Finₓ.sum_univ_eq_sum_range fun i => f i (p.coeff i)]

theorem as_sum_range' (p : R[X]) (n : ℕ) (w : p.natDegree < n) : p = ∑ i in range n, monomial i (coeff p i) :=
  p.sum_monomial_eq.symm.trans <| p.sum_over_range' monomial_zero_right _ w

theorem as_sum_range (p : R[X]) : p = ∑ i in range (p.natDegree + 1), monomial i (coeff p i) :=
  p.sum_monomial_eq.symm.trans <| p.sum_over_range <| monomial_zero_right

theorem as_sum_range_C_mul_X_pow (p : R[X]) : p = ∑ i in range (p.natDegree + 1), c (coeff p i) * X ^ i :=
  p.as_sum_range.trans <| by
    simp only [← C_mul_X_pow_eq_monomial]

theorem coeff_ne_zero_of_eq_degree (hn : degree p = n) : coeff p n ≠ 0 := fun h => mem_support_iff.mp (mem_of_max hn) h

theorem eq_X_add_C_of_degree_le_one (h : degree p ≤ 1) : p = c (p.coeff 1) * X + c (p.coeff 0) :=
  ext fun n =>
    Nat.casesOn n
      (by
        simp )
      fun n =>
      Nat.casesOn n
        (by
          simp [← coeff_C])
        fun m => by
        have : degree p < m.succ.succ :=
          lt_of_le_of_ltₓ h
            (by
              decide)
        simp [← coeff_eq_zero_of_degree_lt this, ← coeff_C, ← Nat.succ_ne_zero, ← coeff_X, ← Nat.succ_inj', ←
          @eq_comm ℕ 0]

theorem eq_X_add_C_of_degree_eq_one (h : degree p = 1) : p = c p.leadingCoeff * X + c (p.coeff 0) :=
  (eq_X_add_C_of_degree_le_one (show degree p ≤ 1 from h ▸ le_rfl)).trans
    (by
      simp [← leading_coeff, ← nat_degree_eq_of_degree_eq_some h])

theorem eq_X_add_C_of_nat_degree_le_one (h : natDegree p ≤ 1) : p = c (p.coeff 1) * X + c (p.coeff 0) :=
  eq_X_add_C_of_degree_le_one <| degree_le_of_nat_degree_le h

theorem exists_eq_X_add_C_of_nat_degree_le_one (h : natDegree p ≤ 1) : ∃ a b, p = c a * X + c b :=
  ⟨p.coeff 1, p.coeff 0, eq_X_add_C_of_nat_degree_le_one h⟩

theorem degree_X_pow_le (n : ℕ) : degree (X ^ n : R[X]) ≤ n := by
  simpa only [← C_1, ← one_mulₓ] using degree_C_mul_X_pow_le n (1 : R)

theorem degree_X_le : degree (x : R[X]) ≤ 1 :=
  degree_monomial_le _ _

theorem nat_degree_X_le : (x : R[X]).natDegree ≤ 1 :=
  nat_degree_le_of_degree_le degree_X_le

theorem mem_support_C_mul_X_pow {n a : ℕ} {c : R} (h : a ∈ (c c * X ^ n).Support) : a = n :=
  mem_singleton.1 <| support_C_mul_X_pow' n c h

theorem card_support_C_mul_X_pow_le_one {c : R} {n : ℕ} : (c c * X ^ n).Support.card ≤ 1 := by
  rw [← card_singleton n]
  apply card_le_of_subset (support_C_mul_X_pow' n c)

theorem card_supp_le_succ_nat_degree (p : R[X]) : p.Support.card ≤ p.natDegree + 1 := by
  rw [← Finset.card_range (p.nat_degree + 1)]
  exact Finset.card_le_of_subset supp_subset_range_nat_degree_succ

theorem le_degree_of_mem_supp (a : ℕ) : a ∈ p.Support → ↑a ≤ degree p :=
  le_degree_of_ne_zero ∘ mem_support_iff.mp

theorem nonempty_support_iff : p.Support.Nonempty ↔ p ≠ 0 := by
  rw [Ne.def, nonempty_iff_ne_empty, Ne.def, ← support_eq_empty]

end Semiringₓ

section NonzeroSemiring

variable [Semiringₓ R] [Nontrivial R] {p q : R[X]}

@[simp]
theorem degree_one : degree (1 : R[X]) = (0 : WithBot ℕ) :=
  degree_C (show (1 : R) ≠ 0 from zero_ne_one.symm)

@[simp]
theorem degree_X : degree (x : R[X]) = 1 :=
  degree_monomial _ one_ne_zero

@[simp]
theorem nat_degree_X : (x : R[X]).natDegree = 1 :=
  nat_degree_eq_of_degree_eq_some degree_X

end NonzeroSemiring

section Ringₓ

variable [Ringₓ R]

theorem coeff_mul_X_sub_C {p : R[X]} {r : R} {a : ℕ} :
    coeff (p * (X - c r)) (a + 1) = coeff p a - coeff p (a + 1) * r := by
  simp [← mul_sub]

@[simp]
theorem degree_neg (p : R[X]) : degree (-p) = degree p := by
  unfold degree <;> rw [support_neg]

@[simp]
theorem nat_degree_neg (p : R[X]) : natDegree (-p) = natDegree p := by
  simp [← nat_degree]

@[simp]
theorem nat_degree_int_cast (n : ℤ) : natDegree (n : R[X]) = 0 := by
  simp only [C_eq_int_cast, ← nat_degree_C]

@[simp]
theorem leading_coeff_neg (p : R[X]) : (-p).leadingCoeff = -p.leadingCoeff := by
  rw [leading_coeff, leading_coeff, nat_degree_neg, coeff_neg]

end Ringₓ

section Semiringₓ

variable [Semiringₓ R]

/-- The second-highest coefficient, or 0 for constants -/
def nextCoeff (p : R[X]) : R :=
  if p.natDegree = 0 then 0 else p.coeff (p.natDegree - 1)

@[simp]
theorem next_coeff_C_eq_zero (c : R) : nextCoeff (c c) = 0 := by
  rw [next_coeff]
  simp

theorem next_coeff_of_pos_nat_degree (p : R[X]) (hp : 0 < p.natDegree) : nextCoeff p = p.coeff (p.natDegree - 1) := by
  rw [next_coeff, if_neg]
  contrapose! hp
  simpa

variable {p q : R[X]} {ι : Type _}

theorem coeff_nat_degree_eq_zero_of_degree_lt (h : degree p < degree q) : coeff p (natDegree q) = 0 :=
  coeff_eq_zero_of_degree_lt (lt_of_lt_of_leₓ h degree_le_nat_degree)

theorem ne_zero_of_degree_gt {n : WithBot ℕ} (h : n < degree p) : p ≠ 0 :=
  mt degree_eq_bot.2 (Ne.symm (ne_of_ltₓ (lt_of_le_of_ltₓ bot_le h)))

theorem ne_zero_of_degree_ge_degree (hpq : p.degree ≤ q.degree) (hp : p ≠ 0) : q ≠ 0 :=
  Polynomial.ne_zero_of_degree_gt
    (lt_of_lt_of_leₓ
      (bot_lt_iff_ne_bot.mpr
        (by
          rwa [Ne.def, Polynomial.degree_eq_bot]))
      hpq :
      q.degree > ⊥)

theorem ne_zero_of_nat_degree_gt {n : ℕ} (h : n < natDegree p) : p ≠ 0 := fun H => by
  simpa [← H, ← Nat.not_lt_zeroₓ] using h

theorem degree_lt_degree (h : natDegree p < natDegree q) : degree p < degree q := by
  by_cases' hp : p = 0
  · simp [← hp]
    rw [bot_lt_iff_ne_bot]
    intro hq
    simpa [← hp, ← degree_eq_bot.mp hq, ← lt_irreflₓ] using h
    
  · rw [degree_eq_nat_degree hp, degree_eq_nat_degree <| ne_zero_of_nat_degree_gt h]
    exact_mod_cast h
    

theorem nat_degree_lt_nat_degree_iff (hp : p ≠ 0) : natDegree p < natDegree q ↔ degree p < degree q :=
  ⟨degree_lt_degree, by
    intro h
    have hq : q ≠ 0 := ne_zero_of_degree_gt h
    rw [degree_eq_nat_degree hp, degree_eq_nat_degree hq] at h
    exact_mod_cast h⟩

theorem eq_C_of_degree_le_zero (h : degree p ≤ 0) : p = c (coeff p 0) := by
  ext (_ | n)
  · simp
    
  rw [coeff_C, if_neg (Nat.succ_ne_zero _), coeff_eq_zero_of_degree_lt]
  exact h.trans_lt (WithBot.some_lt_some.2 n.succ_pos)

theorem eq_C_of_degree_eq_zero (h : degree p = 0) : p = c (coeff p 0) :=
  eq_C_of_degree_le_zero (h ▸ le_rfl)

theorem degree_le_zero_iff : degree p ≤ 0 ↔ p = c (coeff p 0) :=
  ⟨eq_C_of_degree_le_zero, fun h => h.symm ▸ degree_C_le⟩

theorem degree_add_le (p q : R[X]) : degree (p + q) ≤ max (degree p) (degree q) :=
  calc
    degree (p + q) = (p + q).Support.sup some := rfl
    _ ≤ (p.Support ∪ q.Support).sup some := sup_mono support_add
    _ = p.Support.sup some⊔q.Support.sup some := sup_union
    

theorem degree_add_le_of_degree_le {p q : R[X]} {n : ℕ} (hp : degree p ≤ n) (hq : degree q ≤ n) : degree (p + q) ≤ n :=
  (degree_add_le p q).trans <| max_leₓ hp hq

theorem nat_degree_add_le (p q : R[X]) : natDegree (p + q) ≤ max (natDegree p) (natDegree q) := by
  cases le_max_iff.1 (degree_add_le p q) <;> simp [← nat_degree_le_nat_degree h]

theorem nat_degree_add_le_of_degree_le {p q : R[X]} {n : ℕ} (hp : natDegree p ≤ n) (hq : natDegree q ≤ n) :
    natDegree (p + q) ≤ n :=
  (nat_degree_add_le p q).trans <| max_leₓ hp hq

@[simp]
theorem leading_coeff_zero : leadingCoeff (0 : R[X]) = 0 :=
  rfl

@[simp]
theorem leading_coeff_eq_zero : leadingCoeff p = 0 ↔ p = 0 :=
  ⟨fun h => by_contradiction fun hp => mt mem_support_iff.1 (not_not.2 h) (mem_of_max (degree_eq_nat_degree hp)),
    fun h => h.symm ▸ leading_coeff_zero⟩

theorem leading_coeff_ne_zero : leadingCoeff p ≠ 0 ↔ p ≠ 0 := by
  rw [Ne.def, leading_coeff_eq_zero]

theorem leading_coeff_eq_zero_iff_deg_eq_bot : leadingCoeff p = 0 ↔ degree p = ⊥ := by
  rw [leading_coeff_eq_zero, degree_eq_bot]

theorem nat_degree_mem_support_of_nonzero (H : p ≠ 0) : p.natDegree ∈ p.Support := by
  rw [mem_support_iff]
  exact (not_congr leading_coeff_eq_zero).mpr H

theorem nat_degree_eq_support_max' (h : p ≠ 0) : p.natDegree = p.Support.max' (nonempty_support_iff.mpr h) :=
  (le_max' _ _ <| nat_degree_mem_support_of_nonzero h).antisymm <| max'_le _ _ _ le_nat_degree_of_mem_supp

theorem nat_degree_C_mul_X_pow_le (a : R) (n : ℕ) : natDegree (c a * X ^ n) ≤ n :=
  nat_degree_le_iff_degree_le.2 <| degree_C_mul_X_pow_le _ _

theorem degree_add_eq_left_of_degree_lt (h : degree q < degree p) : degree (p + q) = degree p :=
  le_antisymmₓ (max_eq_left_of_ltₓ h ▸ degree_add_le _ _) <|
    degree_le_degree <| by
      rw [coeff_add, coeff_nat_degree_eq_zero_of_degree_lt h, add_zeroₓ]
      exact mt leading_coeff_eq_zero.1 (ne_zero_of_degree_gt h)

theorem degree_add_eq_right_of_degree_lt (h : degree p < degree q) : degree (p + q) = degree q := by
  rw [add_commₓ, degree_add_eq_left_of_degree_lt h]

theorem nat_degree_add_eq_left_of_nat_degree_lt (h : natDegree q < natDegree p) : natDegree (p + q) = natDegree p :=
  nat_degree_eq_of_degree_eq (degree_add_eq_left_of_degree_lt (degree_lt_degree h))

theorem nat_degree_add_eq_right_of_nat_degree_lt (h : natDegree p < natDegree q) : natDegree (p + q) = natDegree q :=
  nat_degree_eq_of_degree_eq (degree_add_eq_right_of_degree_lt (degree_lt_degree h))

theorem degree_add_C (hp : 0 < degree p) : degree (p + c a) = degree p :=
  add_commₓ (c a) p ▸ degree_add_eq_right_of_degree_lt <| lt_of_le_of_ltₓ degree_C_le hp

theorem degree_add_eq_of_leading_coeff_add_ne_zero (h : leadingCoeff p + leadingCoeff q ≠ 0) :
    degree (p + q) = max p.degree q.degree :=
  le_antisymmₓ (degree_add_le _ _) <|
    match lt_trichotomyₓ (degree p) (degree q) with
    | Or.inl hlt => by
      rw [degree_add_eq_right_of_degree_lt hlt, max_eq_right_of_ltₓ hlt] <;> exact le_rfl
    | Or.inr (Or.inl HEq) =>
      le_of_not_gtₓ fun hlt : max (degree p) (degree q) > degree (p + q) =>
        h <|
          show leadingCoeff p + leadingCoeff q = 0 by
            rw [HEq, max_selfₓ] at hlt
            rw [leading_coeff, leading_coeff, nat_degree_eq_of_degree_eq HEq, ← coeff_add]
            exact coeff_nat_degree_eq_zero_of_degree_lt hlt
    | Or.inr (Or.inr hlt) => by
      rw [degree_add_eq_left_of_degree_lt hlt, max_eq_left_of_ltₓ hlt] <;> exact le_rfl

theorem degree_erase_le (p : R[X]) (n : ℕ) : degree (p.erase n) ≤ degree p := by
  rcases p with ⟨⟩
  simp only [← erase, ← degree, ← coeff, ← support]
  convert sup_mono (erase_subset _ _)

theorem degree_erase_lt (hp : p ≠ 0) : degree (p.erase (natDegree p)) < degree p := by
  apply lt_of_le_of_neₓ (degree_erase_le _ _)
  rw [degree_eq_nat_degree hp, degree, support_erase]
  exact fun h => not_mem_erase _ _ (mem_of_max h)

theorem degree_update_le (p : R[X]) (n : ℕ) (a : R) : degree (p.update n a) ≤ max (degree p) n := by
  rw [degree, support_update]
  split_ifs
  · exact (Finset.max_mono (erase_subset _ _)).trans (le_max_leftₓ _ _)
    
  · rw [sup_insert, max_commₓ]
    exact le_rfl
    

theorem degree_sum_le (s : Finset ι) (f : ι → R[X]) : degree (∑ i in s, f i) ≤ s.sup fun b => degree (f b) :=
  (Finset.induction_on s
      (by
        simp only [← sum_empty, ← sup_empty, ← degree_zero, ← le_reflₓ]))
    fun a s has ih =>
    calc
      degree (∑ i in insert a s, f i) ≤ max (degree (f a)) (degree (∑ i in s, f i)) := by
        rw [sum_insert has] <;> exact degree_add_le _ _
      _ ≤ _ := by
        rw [sup_insert, sup_eq_max] <;> exact max_le_max le_rfl ih
      

theorem degree_mul_le (p q : R[X]) : degree (p * q) ≤ degree p + degree q :=
  calc
    degree (p * q) ≤ p.Support.sup fun i => degree (sum q fun j a => c (coeff p i * a) * X ^ (i + j)) := by
      simp only [← monomial_eq_C_mul_X.symm]
      convert degree_sum_le _ _
      exact mul_eq_sum_sum
    _ ≤ p.Support.sup fun i => q.Support.sup fun j => degree (c (coeff p i * coeff q j) * X ^ (i + j)) :=
      Finset.sup_mono_fun fun i hi => degree_sum_le _ _
    _ ≤ degree p + degree q := by
      refine' Finset.sup_le fun a ha => Finset.sup_le fun b hb => le_transₓ (degree_C_mul_X_pow_le _ _) _
      rw [WithBot.coe_add]
      rw [mem_support_iff] at ha hb
      exact add_le_add (le_degree_of_ne_zero ha) (le_degree_of_ne_zero hb)
    

theorem degree_pow_le (p : R[X]) : ∀ n : ℕ, degree (p ^ n) ≤ n • degree p
  | 0 => by
    rw [pow_zeroₓ, zero_nsmul] <;> exact degree_one_le
  | n + 1 =>
    calc
      degree (p ^ (n + 1)) ≤ degree p + degree (p ^ n) := by
        rw [pow_succₓ] <;> exact degree_mul_le _ _
      _ ≤ _ := by
        rw [succ_nsmul] <;> exact add_le_add le_rfl (degree_pow_le _)
      

@[simp]
theorem leading_coeff_monomial (a : R) (n : ℕ) : leadingCoeff (monomial n a) = a := by
  by_cases' ha : a = 0
  · simp only [← ha, ← (monomial n).map_zero, ← leading_coeff_zero]
    
  · rw [leading_coeff, nat_degree_monomial, if_neg ha, coeff_monomial]
    simp
    

theorem leading_coeff_C_mul_X_pow (a : R) (n : ℕ) : leadingCoeff (c a * X ^ n) = a := by
  rw [C_mul_X_pow_eq_monomial, leading_coeff_monomial]

theorem leading_coeff_C_mul_X (a : R) : leadingCoeff (c a * X) = a := by
  simpa only [← pow_oneₓ] using leading_coeff_C_mul_X_pow a 1

@[simp]
theorem leading_coeff_C (a : R) : leadingCoeff (c a) = a :=
  leading_coeff_monomial a 0

@[simp]
theorem leading_coeff_X_pow (n : ℕ) : leadingCoeff ((x : R[X]) ^ n) = 1 := by
  simpa only [← C_1, ← one_mulₓ] using leading_coeff_C_mul_X_pow (1 : R) n

@[simp]
theorem leading_coeff_X : leadingCoeff (x : R[X]) = 1 := by
  simpa only [← pow_oneₓ] using @leading_coeff_X_pow R _ 1

@[simp]
theorem monic_X_pow (n : ℕ) : Monic (X ^ n : R[X]) :=
  leading_coeff_X_pow n

@[simp]
theorem monic_X : Monic (x : R[X]) :=
  leading_coeff_X

@[simp]
theorem leading_coeff_one : leadingCoeff (1 : R[X]) = 1 :=
  leading_coeff_C 1

@[simp]
theorem monic_one : Monic (1 : R[X]) :=
  leading_coeff_C _

theorem Monic.ne_zero {R : Type _} [Semiringₓ R] [Nontrivial R] {p : R[X]} (hp : p.Monic) : p ≠ 0 := by
  rintro rfl
  simpa [← monic] using hp

theorem Monic.ne_zero_of_ne (h : (0 : R) ≠ 1) {p : R[X]} (hp : p.Monic) : p ≠ 0 := by
  nontriviality R
  exact hp.ne_zero

theorem Monic.ne_zero_of_polynomial_ne {r} (hp : Monic p) (hne : q ≠ r) : p ≠ 0 := by
  have := nontrivial.of_polynomial_ne hne
  exact hp.ne_zero

theorem leading_coeff_add_of_degree_lt (h : degree p < degree q) : leadingCoeff (p + q) = leadingCoeff q := by
  have : coeff p (natDegree q) = 0 := coeff_nat_degree_eq_zero_of_degree_lt h
  simp only [← leading_coeff, ← nat_degree_eq_of_degree_eq (degree_add_eq_right_of_degree_lt h), ← this, ← coeff_add, ←
    zero_addₓ]

theorem leading_coeff_add_of_degree_eq (h : degree p = degree q) (hlc : leadingCoeff p + leadingCoeff q ≠ 0) :
    leadingCoeff (p + q) = leadingCoeff p + leadingCoeff q := by
  have : natDegree (p + q) = natDegree p := by
    apply nat_degree_eq_of_degree_eq <;> rw [degree_add_eq_of_leading_coeff_add_ne_zero hlc, h, max_selfₓ]
  simp only [← leading_coeff, ← this, ← nat_degree_eq_of_degree_eq h, ← coeff_add]

@[simp]
theorem coeff_mul_degree_add_degree (p q : R[X]) :
    coeff (p * q) (natDegree p + natDegree q) = leadingCoeff p * leadingCoeff q :=
  calc
    coeff (p * q) (natDegree p + natDegree q) =
        ∑ x in Nat.antidiagonal (natDegree p + natDegree q), coeff p x.1 * coeff q x.2 :=
      coeff_mul _ _ _
    _ = coeff p (natDegree p) * coeff q (natDegree q) := by
      refine' Finset.sum_eq_single (nat_degree p, nat_degree q) _ _
      · rintro ⟨i, j⟩ h₁ h₂
        rw [nat.mem_antidiagonal] at h₁
        by_cases' H : nat_degree p < i
        · rw [coeff_eq_zero_of_degree_lt (lt_of_le_of_ltₓ degree_le_nat_degree (WithBot.coe_lt_coe.2 H)), zero_mul]
          
        · rw [not_lt_iff_eq_or_lt] at H
          cases H
          · subst H
            rw [add_left_cancel_iffₓ] at h₁
            dsimp'  at h₁
            subst h₁
            exfalso
            exact h₂ rfl
            
          · suffices nat_degree q < j by
              rw [coeff_eq_zero_of_degree_lt (lt_of_le_of_ltₓ degree_le_nat_degree (WithBot.coe_lt_coe.2 this)),
                mul_zero]
            · by_contra H'
              rw [not_ltₓ] at H'
              exact ne_of_ltₓ (Nat.lt_of_lt_of_leₓ (Nat.add_lt_add_rightₓ H j) (Nat.add_le_add_leftₓ H' _)) h₁
              
            
          
        
      · intro H
        exfalso
        apply H
        rw [nat.mem_antidiagonal]
        
    

theorem degree_mul' (h : leadingCoeff p * leadingCoeff q ≠ 0) : degree (p * q) = degree p + degree q :=
  have hp : p ≠ 0 := by
    refine' mt _ h <;>
      exact fun hp => by
        rw [hp, leading_coeff_zero, zero_mul]
  have hq : q ≠ 0 := by
    refine' mt _ h <;>
      exact fun hq => by
        rw [hq, leading_coeff_zero, mul_zero]
  le_antisymmₓ (degree_mul_le _ _)
    (by
      rw [degree_eq_nat_degree hp, degree_eq_nat_degree hq]
      refine' le_degree_of_ne_zero _
      rwa [coeff_mul_degree_add_degree])

theorem Monic.degree_mul (hq : Monic q) : degree (p * q) = degree p + degree q :=
  if hp : p = 0 then by
    simp [← hp]
  else
    degree_mul' <| by
      rwa [hq.leading_coeff, mul_oneₓ, Ne.def, leading_coeff_eq_zero]

theorem nat_degree_mul' (h : leadingCoeff p * leadingCoeff q ≠ 0) : natDegree (p * q) = natDegree p + natDegree q :=
  have hp : p ≠ 0 :=
    mt leading_coeff_eq_zero.2 fun h₁ =>
      h <| by
        rw [h₁, zero_mul]
  have hq : q ≠ 0 :=
    mt leading_coeff_eq_zero.2 fun h₁ =>
      h <| by
        rw [h₁, mul_zero]
  nat_degree_eq_of_degree_eq_some <| by
    rw [degree_mul' h, WithBot.coe_add, degree_eq_nat_degree hp, degree_eq_nat_degree hq]

theorem leading_coeff_mul' (h : leadingCoeff p * leadingCoeff q ≠ 0) :
    leadingCoeff (p * q) = leadingCoeff p * leadingCoeff q := by
  unfold leading_coeff
  rw [nat_degree_mul' h, coeff_mul_degree_add_degree]
  rfl

theorem monomial_nat_degree_leading_coeff_eq_self (h : p.Support.card ≤ 1) : monomial p.natDegree p.leadingCoeff = p :=
  by
  rcases card_support_le_one_iff_monomial.1 h with ⟨n, a, rfl⟩
  by_cases' ha : a = 0 <;> simp [← ha]

theorem C_mul_X_pow_eq_self (h : p.Support.card ≤ 1) : c p.leadingCoeff * X ^ p.natDegree = p := by
  rw [C_mul_X_pow_eq_monomial, monomial_nat_degree_leading_coeff_eq_self h]

theorem leading_coeff_pow' : leadingCoeff p ^ n ≠ 0 → leadingCoeff (p ^ n) = leadingCoeff p ^ n :=
  (Nat.recOn n
      (by
        simp ))
    fun n ih h => by
    have h₁ : leadingCoeff p ^ n ≠ 0 := fun h₁ =>
      h <| by
        rw [pow_succₓ, h₁, mul_zero]
    have h₂ : leadingCoeff p * leadingCoeff (p ^ n) ≠ 0 := by
      rwa [pow_succₓ, ← ih h₁] at h
    rw [pow_succₓ, pow_succₓ, leading_coeff_mul' h₂, ih h₁]

theorem degree_pow' : ∀ {n : ℕ}, leadingCoeff p ^ n ≠ 0 → degree (p ^ n) = n • degree p
  | 0 => fun h => by
    rw [pow_zeroₓ, ← C_1] at * <;> rw [degree_C h, zero_nsmul]
  | n + 1 => fun h => by
    have h₁ : leadingCoeff p ^ n ≠ 0 := fun h₁ =>
      h <| by
        rw [pow_succₓ, h₁, mul_zero]
    have h₂ : leadingCoeff p * leadingCoeff (p ^ n) ≠ 0 := by
      rwa [pow_succₓ, ← leading_coeff_pow' h₁] at h
    rw [pow_succₓ, degree_mul' h₂, succ_nsmul, degree_pow' h₁]

theorem nat_degree_pow' {n : ℕ} (h : leadingCoeff p ^ n ≠ 0) : natDegree (p ^ n) = n * natDegree p :=
  if hp0 : p = 0 then
    if hn0 : n = 0 then by
      simp [*]
    else by
      rw [hp0, zero_pow (Nat.pos_of_ne_zeroₓ hn0)] <;> simp
  else
    have hpn : p ^ n ≠ 0 := fun hpn0 => by
      have h1 := h
      rw [← leading_coeff_pow' h1, hpn0, leading_coeff_zero] at h <;> exact h rfl
    Option.some_inj.1 <|
      show (natDegree (p ^ n) : WithBot ℕ) = (n * natDegree p : ℕ) by
        rw [← degree_eq_nat_degree hpn, degree_pow' h, degree_eq_nat_degree hp0, ← WithBot.coe_nsmul] <;> simp

theorem leading_coeff_monic_mul {p q : R[X]} (hp : Monic p) : leadingCoeff (p * q) = leadingCoeff q := by
  rcases eq_or_ne q 0 with (rfl | H)
  · simp
    
  · rw [leading_coeff_mul', hp.leading_coeff, one_mulₓ]
    rwa [hp.leading_coeff, one_mulₓ, Ne.def, leading_coeff_eq_zero]
    

theorem leading_coeff_mul_monic {p q : R[X]} (hq : Monic q) : leadingCoeff (p * q) = leadingCoeff p :=
  Decidable.byCases
    (fun H : leadingCoeff p = 0 => by
      rw [H, leading_coeff_eq_zero.1 H, zero_mul, leading_coeff_zero])
    fun H : leadingCoeff p ≠ 0 => by
    rw [leading_coeff_mul', hq.leading_coeff, mul_oneₓ] <;> rwa [hq.leading_coeff, mul_oneₓ]

@[simp]
theorem leading_coeff_mul_X_pow {p : R[X]} {n : ℕ} : leadingCoeff (p * X ^ n) = leadingCoeff p :=
  leading_coeff_mul_monic (monic_X_pow n)

@[simp]
theorem leading_coeff_mul_X {p : R[X]} : leadingCoeff (p * X) = leadingCoeff p :=
  leading_coeff_mul_monic monic_X

theorem nat_degree_mul_le {p q : R[X]} : natDegree (p * q) ≤ natDegree p + natDegree q := by
  apply nat_degree_le_of_degree_le
  apply le_transₓ (degree_mul_le p q)
  rw [WithBot.coe_add]
  refine' add_le_add _ _ <;> apply degree_le_nat_degree

theorem nat_degree_pow_le {p : R[X]} {n : ℕ} : (p ^ n).natDegree ≤ n * p.natDegree := by
  induction' n with i hi
  · simp
    
  · rw [pow_succₓ, Nat.succ_mul, add_commₓ]
    apply le_transₓ nat_degree_mul_le
    exact add_le_add_left hi _
    

@[simp]
theorem coeff_pow_mul_nat_degree (p : R[X]) (n : ℕ) : (p ^ n).coeff (n * p.natDegree) = p.leadingCoeff ^ n := by
  induction' n with i hi
  · simp
    
  · rw [pow_succ'ₓ, pow_succ'ₓ, Nat.succ_mul]
    by_cases' hp1 : p.leading_coeff ^ i = 0
    · rw [hp1, zero_mul]
      by_cases' hp2 : p ^ i = 0
      · rw [hp2, zero_mul, coeff_zero]
        
      · apply coeff_eq_zero_of_nat_degree_lt
        have h1 : (p ^ i).natDegree < i * p.nat_degree := by
          apply lt_of_le_of_neₓ nat_degree_pow_le fun h => hp2 _
          rw [← h, hp1] at hi
          exact leading_coeff_eq_zero.mp hi
        calc (p ^ i * p).natDegree ≤ (p ^ i).natDegree + p.nat_degree :=
            nat_degree_mul_le _ < i * p.nat_degree + p.nat_degree := add_lt_add_right h1 _
        
      
    · rw [← nat_degree_pow' hp1, ← leading_coeff_pow' hp1]
      exact coeff_mul_degree_add_degree _ _
      
    

theorem subsingleton_of_monic_zero (h : Monic (0 : R[X])) : (∀ p q : R[X], p = q) ∧ ∀ a b : R, a = b := by
  rw [monic.def, leading_coeff_zero] at h <;>
    exact
      ⟨fun p q => by
        rw [← mul_oneₓ p, ← mul_oneₓ q, ← C_1, ← h, C_0, mul_zero, mul_zero], fun a b => by
        rw [← mul_oneₓ a, ← mul_oneₓ b, ← h, mul_zero, mul_zero]⟩

theorem zero_le_degree_iff {p : R[X]} : 0 ≤ degree p ↔ p ≠ 0 := by
  rw [Ne.def, ← degree_eq_bot] <;>
    cases degree p <;>
      exact by
        decide

theorem degree_nonneg_iff_ne_zero : 0 ≤ degree p ↔ p ≠ 0 := by
  simp [← degree_eq_bot, not_ltₓ]

theorem nat_degree_eq_zero_iff_degree_le_zero : p.natDegree = 0 ↔ p.degree ≤ 0 := by
  rw [← nonpos_iff_eq_zero, nat_degree_le_iff_degree_le, WithBot.coe_zero]

theorem degree_le_iff_coeff_zero (f : R[X]) (n : WithBot ℕ) : degree f ≤ n ↔ ∀ m : ℕ, n < m → coeff f m = 0 := by
  simp only [← degree, ← Finset.sup_le_iff, ← mem_support_iff, ← Ne.def, not_leₓ, ← not_imp_comm]

theorem degree_lt_iff_coeff_zero (f : R[X]) (n : ℕ) : degree f < n ↔ ∀ m : ℕ, n ≤ m → coeff f m = 0 := by
  refine' ⟨fun hf m hm => coeff_eq_zero_of_degree_lt (lt_of_lt_of_leₓ hf (WithBot.coe_le_coe.2 hm)), _⟩
  simp only [← degree, ← Finset.sup_lt_iff (WithBot.bot_lt_coe n), ← mem_support_iff, ← WithBot.some_eq_coe, ←
    WithBot.coe_lt_coe, @not_leₓ ℕ]
  exact fun h m => mt (h m)

theorem degree_smul_le (a : R) (p : R[X]) : degree (a • p) ≤ degree p := by
  apply (degree_le_iff_coeff_zero _ _).2 fun m hm => _
  rw [degree_lt_iff_coeff_zero] at hm
  simp [← hm m le_rfl]

theorem nat_degree_smul_le (a : R) (p : R[X]) : natDegree (a • p) ≤ natDegree p :=
  nat_degree_le_nat_degree (degree_smul_le a p)

theorem degree_lt_degree_mul_X (hp : p ≠ 0) : p.degree < (p * X).degree := by
  have := nontrivial.of_polynomial_ne hp
  have : leading_coeff p * leading_coeff X ≠ 0 := by
    simpa
  erw [degree_mul' this, degree_eq_nat_degree hp, degree_X, ← WithBot.coe_one, ← WithBot.coe_add,
      WithBot.coe_lt_coe] <;>
    exact Nat.lt_succ_selfₓ _

theorem nat_degree_pos_iff_degree_pos : 0 < natDegree p ↔ 0 < degree p :=
  lt_iff_lt_of_le_iff_le nat_degree_le_iff_degree_le

theorem eq_C_of_nat_degree_le_zero (h : natDegree p ≤ 0) : p = c (coeff p 0) :=
  eq_C_of_degree_le_zero <| degree_le_of_nat_degree_le h

theorem eq_C_of_nat_degree_eq_zero (h : natDegree p = 0) : p = c (coeff p 0) :=
  eq_C_of_nat_degree_le_zero h.le

theorem ne_zero_of_coe_le_degree (hdeg : ↑n ≤ p.degree) : p ≠ 0 := by
  rw [← degree_nonneg_iff_ne_zero] <;>
    exact
      trans
        (by
          exact_mod_cast n.zero_le)
        hdeg

theorem le_nat_degree_of_coe_le_degree (hdeg : ↑n ≤ p.degree) : n ≤ p.natDegree :=
  WithBot.coe_le_coe.mp ((degree_eq_nat_degree <| ne_zero_of_coe_le_degree hdeg) ▸ hdeg)

theorem degree_sum_fin_lt {n : ℕ} (f : Finₓ n → R) : degree (∑ i : Finₓ n, c (f i) * X ^ (i : ℕ)) < n := by
  have : IsCommutative (WithBot ℕ) max := ⟨max_commₓ⟩
  have : IsAssociative (WithBot ℕ) max := ⟨max_assocₓ⟩
  calc (∑ i, C (f i) * X ^ (i : ℕ)).degree ≤ finset.univ.fold (·⊔·) ⊥ fun i => (C (f i) * X ^ (i : ℕ)).degree :=
      degree_sum_le _ _ _ = finset.univ.fold max ⊥ fun i => (C (f i) * X ^ (i : ℕ)).degree := rfl _ < n :=
      (Finset.fold_max_lt (n : WithBot ℕ)).mpr ⟨WithBot.bot_lt_coe _, _⟩
  rintro ⟨i, hi⟩ -
  calc (C (f ⟨i, hi⟩) * X ^ i).degree ≤ (C _).degree + (X ^ i).degree := degree_mul_le _ _ _ ≤ 0 + i :=
      add_le_add degree_C_le (degree_X_pow_le i)_ = i := zero_addₓ _ _ < n := with_bot.some_lt_some.mpr hi

theorem degree_linear_le : degree (c a * X + c b) ≤ 1 :=
  degree_add_le_of_degree_le (degree_C_mul_X_le _) <| le_transₓ degree_C_le Nat.WithBot.coe_nonneg

theorem degree_linear_lt : degree (c a * X + c b) < 2 :=
  degree_linear_le.trans_lt <| WithBot.coe_lt_coe.mpr one_lt_two

theorem degree_C_lt_degree_C_mul_X (ha : a ≠ 0) : degree (c b) < degree (c a * X) := by
  simpa only [← degree_C_mul_X ha] using degree_C_lt

@[simp]
theorem degree_linear (ha : a ≠ 0) : degree (c a * X + c b) = 1 := by
  rw [degree_add_eq_left_of_degree_lt <| degree_C_lt_degree_C_mul_X ha, degree_C_mul_X ha]

theorem nat_degree_linear_le : natDegree (c a * X + c b) ≤ 1 :=
  nat_degree_le_of_degree_le degree_linear_le

@[simp]
theorem nat_degree_linear (ha : a ≠ 0) : natDegree (c a * X + c b) = 1 :=
  nat_degree_eq_of_degree_eq_some <| degree_linear ha

@[simp]
theorem leading_coeff_linear (ha : a ≠ 0) : leadingCoeff (c a * X + c b) = a := by
  rw [add_commₓ, leading_coeff_add_of_degree_lt (degree_C_lt_degree_C_mul_X ha), leading_coeff_C_mul_X]

theorem degree_quadratic_le : degree (c a * X ^ 2 + c b * X + c c) ≤ 2 := by
  simpa only [← add_assocₓ] using
    degree_add_le_of_degree_le (degree_C_mul_X_pow_le 2 a)
      (le_transₓ degree_linear_le <| with_bot.coe_le_coe.mpr one_le_two)

theorem degree_quadratic_lt : degree (c a * X ^ 2 + c b * X + c c) < 3 :=
  degree_quadratic_le.trans_lt <| WithBot.coe_lt_coe.mpr <| lt_add_one 2

theorem degree_linear_lt_degree_C_mul_X_sq (ha : a ≠ 0) : degree (c b * X + c c) < degree (c a * X ^ 2) := by
  simpa only [← degree_C_mul_X_pow 2 ha] using degree_linear_lt

@[simp]
theorem degree_quadratic (ha : a ≠ 0) : degree (c a * X ^ 2 + c b * X + c c) = 2 := by
  rw [add_assocₓ, degree_add_eq_left_of_degree_lt <| degree_linear_lt_degree_C_mul_X_sq ha, degree_C_mul_X_pow 2 ha]
  rfl

theorem nat_degree_quadratic_le : natDegree (c a * X ^ 2 + c b * X + c c) ≤ 2 :=
  nat_degree_le_of_degree_le degree_quadratic_le

@[simp]
theorem nat_degree_quadratic (ha : a ≠ 0) : natDegree (c a * X ^ 2 + c b * X + c c) = 2 :=
  nat_degree_eq_of_degree_eq_some <| degree_quadratic ha

@[simp]
theorem leading_coeff_quadratic (ha : a ≠ 0) : leadingCoeff (c a * X ^ 2 + c b * X + c c) = a := by
  rw [add_assocₓ, add_commₓ, leading_coeff_add_of_degree_lt <| degree_linear_lt_degree_C_mul_X_sq ha,
    leading_coeff_C_mul_X_pow]

theorem degree_cubic_le : degree (c a * X ^ 3 + c b * X ^ 2 + c c * X + c d) ≤ 3 := by
  simpa only [← add_assocₓ] using
    degree_add_le_of_degree_le (degree_C_mul_X_pow_le 3 a)
      (le_transₓ degree_quadratic_le <| with_bot.coe_le_coe.mpr <| Nat.le_succₓ 2)

theorem degree_cubic_lt : degree (c a * X ^ 3 + c b * X ^ 2 + c c * X + c d) < 4 :=
  degree_cubic_le.trans_lt <| WithBot.coe_lt_coe.mpr <| lt_add_one 3

theorem degree_quadratic_lt_degree_C_mul_X_cb (ha : a ≠ 0) :
    degree (c b * X ^ 2 + c c * X + c d) < degree (c a * X ^ 3) := by
  simpa only [← degree_C_mul_X_pow 3 ha] using degree_quadratic_lt

@[simp]
theorem degree_cubic (ha : a ≠ 0) : degree (c a * X ^ 3 + c b * X ^ 2 + c c * X + c d) = 3 := by
  rw [add_assocₓ, add_assocₓ, ← add_assocₓ (C b * X ^ 2),
    degree_add_eq_left_of_degree_lt <| degree_quadratic_lt_degree_C_mul_X_cb ha, degree_C_mul_X_pow 3 ha]
  rfl

theorem nat_degree_cubic_le : natDegree (c a * X ^ 3 + c b * X ^ 2 + c c * X + c d) ≤ 3 :=
  nat_degree_le_of_degree_le degree_cubic_le

@[simp]
theorem nat_degree_cubic (ha : a ≠ 0) : natDegree (c a * X ^ 3 + c b * X ^ 2 + c c * X + c d) = 3 :=
  nat_degree_eq_of_degree_eq_some <| degree_cubic ha

@[simp]
theorem leading_coeff_cubic (ha : a ≠ 0) : leadingCoeff (c a * X ^ 3 + c b * X ^ 2 + c c * X + c d) = a := by
  rw [add_assocₓ, add_assocₓ, ← add_assocₓ (C b * X ^ 2), add_commₓ,
    leading_coeff_add_of_degree_lt <| degree_quadratic_lt_degree_C_mul_X_cb ha, leading_coeff_C_mul_X_pow]

end Semiringₓ

section NontrivialSemiring

variable [Semiringₓ R] [Nontrivial R] {p q : R[X]}

@[simp]
theorem degree_X_pow (n : ℕ) : degree ((x : R[X]) ^ n) = n := by
  rw [X_pow_eq_monomial, degree_monomial _ (@one_ne_zero R _ _)]

@[simp]
theorem nat_degree_X_pow (n : ℕ) : natDegree ((x : R[X]) ^ n) = n :=
  nat_degree_eq_of_degree_eq_some (degree_X_pow n)

--  This lemma explicitly does not require the `nontrivial R` assumption.
theorem nat_degree_X_pow_le {R : Type _} [Semiringₓ R] (n : ℕ) : (X ^ n : R[X]).natDegree ≤ n := by
  nontriviality R
  rwa [Polynomial.nat_degree_X_pow]

theorem not_is_unit_X : ¬IsUnit (x : R[X]) := fun ⟨⟨_, g, hfg, hgf⟩, rfl⟩ =>
  @zero_ne_one R _ _ <| by
    change g * monomial 1 1 = 1 at hgf
    rw [← coeff_one_zero, ← hgf]
    simp

@[simp]
theorem degree_mul_X : degree (p * X) = degree p + 1 := by
  simp [← monic_X.degree_mul]

@[simp]
theorem degree_mul_X_pow : degree (p * X ^ n) = degree p + n := by
  simp [← (monic_X_pow n).degree_mul]

end NontrivialSemiring

section Ringₓ

variable [Ringₓ R] {p q : R[X]}

theorem degree_sub_le (p q : R[X]) : degree (p - q) ≤ max (degree p) (degree q) := by
  simpa only [← sub_eq_add_neg, ← degree_neg q] using degree_add_le p (-q)

theorem degree_sub_lt (hd : degree p = degree q) (hp0 : p ≠ 0) (hlc : leadingCoeff p = leadingCoeff q) :
    degree (p - q) < degree p :=
  have hp : monomial (natDegree p) (leadingCoeff p) + p.erase (natDegree p) = p := monomial_add_erase _ _
  have hq : monomial (natDegree q) (leadingCoeff q) + q.erase (natDegree q) = q := monomial_add_erase _ _
  have hd' : natDegree p = natDegree q := by
    unfold nat_degree <;> rw [hd]
  have hq0 : q ≠ 0 := mt degree_eq_bot.2 (hd ▸ mt degree_eq_bot.1 hp0)
  calc
    degree (p - q) = degree (erase (natDegree q) p + -erase (natDegree q) q) := by
      conv => lhs rw [← hp, ← hq, hlc, hd', add_sub_add_left_eq_sub, sub_eq_add_neg]
    _ ≤ max (degree (erase (natDegree q) p)) (degree (erase (natDegree q) q)) :=
      degree_neg (erase (natDegree q) q) ▸ degree_add_le _ _
    _ < degree p := max_lt_iff.2 ⟨hd' ▸ degree_erase_lt hp0, hd.symm ▸ degree_erase_lt hq0⟩
    

theorem nat_degree_X_sub_C_le {r : R} : (X - c r).natDegree ≤ 1 :=
  nat_degree_le_iff_degree_le.2 <|
    le_transₓ (degree_sub_le _ _) <| max_leₓ degree_X_le <| le_transₓ degree_C_le <| WithBot.coe_le_coe.2 zero_le_one

theorem degree_sub_eq_left_of_degree_lt (h : degree q < degree p) : degree (p - q) = degree p := by
  rw [← degree_neg q] at h
  rw [sub_eq_add_neg, degree_add_eq_left_of_degree_lt h]

theorem degree_sub_eq_right_of_degree_lt (h : degree p < degree q) : degree (p - q) = degree q := by
  rw [← degree_neg q] at h
  rw [sub_eq_add_neg, degree_add_eq_right_of_degree_lt h, degree_neg]

end Ringₓ

section NonzeroRing

variable [Nontrivial R]

section Semiringₓ

variable [Semiringₓ R]

@[simp]
theorem degree_X_add_C (a : R) : degree (X + c a) = 1 := by
  have : degree (c a) < degree (x : R[X]) :=
    calc
      degree (c a) ≤ 0 := degree_C_le
      _ < 1 := WithBot.some_lt_some.mpr zero_lt_one
      _ = degree x := degree_X.symm
      
  rw [degree_add_eq_left_of_degree_lt this, degree_X]

@[simp]
theorem nat_degree_X_add_C (x : R) : (X + c x).natDegree = 1 :=
  nat_degree_eq_of_degree_eq_some <| degree_X_add_C x

@[simp]
theorem next_coeff_X_add_C [Semiringₓ S] (c : S) : nextCoeff (X + c c) = c := by
  nontriviality S
  simp [← next_coeff_of_pos_nat_degree]

theorem degree_X_pow_add_C {n : ℕ} (hn : 0 < n) (a : R) : degree ((x : R[X]) ^ n + c a) = n := by
  have : degree (c a) < degree ((x : R[X]) ^ n) :=
    calc
      degree (c a) ≤ 0 := degree_C_le
      _ < degree ((x : R[X]) ^ n) := by
        rwa [degree_X_pow] <;> exact WithBot.coe_lt_coe.2 hn
      
  rw [degree_add_eq_left_of_degree_lt this, degree_X_pow]

theorem X_pow_add_C_ne_zero {n : ℕ} (hn : 0 < n) (a : R) : (x : R[X]) ^ n + c a ≠ 0 :=
  mt degree_eq_bot.2
    (show degree ((x : R[X]) ^ n + c a) ≠ ⊥ by
      rw [degree_X_pow_add_C hn a] <;>
        exact by
          decide)

theorem X_add_C_ne_zero (r : R) : X + c r ≠ 0 :=
  pow_oneₓ (x : R[X]) ▸ X_pow_add_C_ne_zero zero_lt_one r

theorem zero_nmem_multiset_map_X_add_C {α : Type _} (m : Multiset α) (f : α → R) :
    (0 : R[X]) ∉ m.map fun a => X + c (f a) := fun mem =>
  let ⟨a, _, ha⟩ := Multiset.mem_map.mp mem
  X_add_C_ne_zero _ ha

theorem nat_degree_X_pow_add_C {n : ℕ} {r : R} : (X ^ n + c r).natDegree = n := by
  by_cases' hn : n = 0
  · rw [hn, pow_zeroₓ, ← C_1, ← RingHom.map_add, nat_degree_C]
    
  · exact nat_degree_eq_of_degree_eq_some (degree_X_pow_add_C (pos_iff_ne_zero.mpr hn) r)
    

end Semiringₓ

end NonzeroRing

section Semiringₓ

variable [Semiringₓ R]

@[simp]
theorem leading_coeff_X_pow_add_C {n : ℕ} (hn : 0 < n) {r : R} : (X ^ n + c r).leadingCoeff = 1 := by
  nontriviality R
  rw [leading_coeff, nat_degree_X_pow_add_C, coeff_add, coeff_X_pow_self, coeff_C, if_neg (pos_iff_ne_zero.mp hn),
    add_zeroₓ]

@[simp]
theorem leading_coeff_X_add_C [Semiringₓ S] (r : S) : (X + c r).leadingCoeff = 1 := by
  rw [← pow_oneₓ (X : S[X]), leading_coeff_X_pow_add_C zero_lt_one]

@[simp]
theorem leading_coeff_X_pow_add_one {n : ℕ} (hn : 0 < n) : (X ^ n + 1 : R[X]).leadingCoeff = 1 :=
  leading_coeff_X_pow_add_C hn

@[simp]
theorem leading_coeff_pow_X_add_C (r : R) (i : ℕ) : leadingCoeff ((X + c r) ^ i) = 1 := by
  nontriviality
  rw [leading_coeff_pow'] <;> simp

end Semiringₓ

section Ringₓ

variable [Ringₓ R]

@[simp]
theorem leading_coeff_X_pow_sub_C {n : ℕ} (hn : 0 < n) {r : R} : (X ^ n - c r).leadingCoeff = 1 := by
  rw [sub_eq_add_neg, ← map_neg C r, leading_coeff_X_pow_add_C hn] <;> infer_instance

@[simp]
theorem leading_coeff_X_pow_sub_one {n : ℕ} (hn : 0 < n) : (X ^ n - 1 : R[X]).leadingCoeff = 1 :=
  leading_coeff_X_pow_sub_C hn

variable [Nontrivial R]

@[simp]
theorem degree_X_sub_C (a : R) : degree (X - c a) = 1 := by
  rw [sub_eq_add_neg, ← map_neg C a, degree_X_add_C]

@[simp]
theorem nat_degree_X_sub_C (x : R) : (X - c x).natDegree = 1 :=
  nat_degree_eq_of_degree_eq_some <| degree_X_sub_C x

@[simp]
theorem next_coeff_X_sub_C [Ringₓ S] (c : S) : nextCoeff (X - c c) = -c := by
  rw [sub_eq_add_neg, ← map_neg C c, next_coeff_X_add_C]

theorem degree_X_pow_sub_C {n : ℕ} (hn : 0 < n) (a : R) : degree ((x : R[X]) ^ n - c a) = n := by
  rw [sub_eq_add_neg, ← map_neg C a, degree_X_pow_add_C hn] <;> infer_instance

theorem X_pow_sub_C_ne_zero {n : ℕ} (hn : 0 < n) (a : R) : (x : R[X]) ^ n - c a ≠ 0 := by
  rw [sub_eq_add_neg, ← map_neg C a]
  exact X_pow_add_C_ne_zero hn _

theorem X_sub_C_ne_zero (r : R) : X - c r ≠ 0 :=
  pow_oneₓ (x : R[X]) ▸ X_pow_sub_C_ne_zero zero_lt_one r

theorem zero_nmem_multiset_map_X_sub_C {α : Type _} (m : Multiset α) (f : α → R) :
    (0 : R[X]) ∉ m.map fun a => X - c (f a) := fun mem =>
  let ⟨a, _, ha⟩ := Multiset.mem_map.mp mem
  X_sub_C_ne_zero _ ha

theorem nat_degree_X_pow_sub_C {n : ℕ} {r : R} : (X ^ n - c r).natDegree = n := by
  rw [sub_eq_add_neg, ← map_neg C r, nat_degree_X_pow_add_C]

@[simp]
theorem leading_coeff_X_sub_C [Ringₓ S] (r : S) : (X - c r).leadingCoeff = 1 := by
  rw [sub_eq_add_neg, ← map_neg C r, leading_coeff_X_add_C]

end Ringₓ

section NoZeroDivisors

variable [Semiringₓ R] [NoZeroDivisors R] {p q : R[X]}

@[simp]
theorem degree_mul : degree (p * q) = degree p + degree q :=
  if hp0 : p = 0 then by
    simp only [← hp0, ← degree_zero, ← zero_mul, ← WithBot.bot_add]
  else
    if hq0 : q = 0 then by
      simp only [← hq0, ← degree_zero, ← mul_zero, ← WithBot.add_bot]
    else degree_mul' <| mul_ne_zero (mt leading_coeff_eq_zero.1 hp0) (mt leading_coeff_eq_zero.1 hq0)

/-- `degree` as a monoid homomorphism between `R[X]` and `multiplicative (with_bot ℕ)`.
  This is useful to prove results about multiplication and degree. -/
def degreeMonoidHom [Nontrivial R] : R[X] →* Multiplicative (WithBot ℕ) where
  toFun := degree
  map_one' := degree_one
  map_mul' := fun _ _ => degree_mul

@[simp]
theorem degree_pow [Nontrivial R] (p : R[X]) (n : ℕ) : degree (p ^ n) = n • degree p :=
  map_pow (@degreeMonoidHom R _ _ _) _ _

@[simp]
theorem leading_coeff_mul (p q : R[X]) : leadingCoeff (p * q) = leadingCoeff p * leadingCoeff q := by
  by_cases' hp : p = 0
  · simp only [← hp, ← zero_mul, ← leading_coeff_zero]
    
  · by_cases' hq : q = 0
    · simp only [← hq, ← mul_zero, ← leading_coeff_zero]
      
    · rw [leading_coeff_mul']
      exact mul_ne_zero (mt leading_coeff_eq_zero.1 hp) (mt leading_coeff_eq_zero.1 hq)
      
    

/-- `polynomial.leading_coeff` bundled as a `monoid_hom` when `R` has `no_zero_divisors`, and thus
  `leading_coeff` is multiplicative -/
def leadingCoeffHom : R[X] →* R where
  toFun := leadingCoeff
  map_one' := by
    simp
  map_mul' := leading_coeff_mul

@[simp]
theorem leading_coeff_hom_apply (p : R[X]) : leadingCoeffHom p = leadingCoeff p :=
  rfl

@[simp]
theorem leading_coeff_pow (p : R[X]) (n : ℕ) : leadingCoeff (p ^ n) = leadingCoeff p ^ n :=
  (leadingCoeffHom : R[X] →* R).map_pow p n

end NoZeroDivisors

end Polynomial

