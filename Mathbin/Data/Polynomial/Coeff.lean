/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Scott Morrison, Jens Wagemaker
-/
import Mathbin.Data.Polynomial.Basic
import Mathbin.Data.Finset.NatAntidiagonal
import Mathbin.Data.Nat.Choose.Sum

/-!
# Theory of univariate polynomials

The theorems include formulas for computing coefficients, such as
`coeff_add`, `coeff_sum`, `coeff_mul`

-/


noncomputable section

open Finsupp Finset AddMonoidAlgebra

open BigOperators Polynomial

namespace Polynomial

universe u v

variable {R : Type u} {S : Type v} {a b : R} {n m : ℕ}

variable [Semiringₓ R] {p q r : R[X]}

section Coeff

theorem coeff_one (n : ℕ) : coeff (1 : R[X]) n = if 0 = n then 1 else 0 :=
  coeff_monomial

@[simp]
theorem coeff_add (p q : R[X]) (n : ℕ) : coeff (p + q) n = coeff p n + coeff q n := by
  rcases p with ⟨⟩
  rcases q with ⟨⟩
  simp_rw [← of_finsupp_add, coeff]
  exact Finsupp.add_apply _ _ _

@[simp]
theorem coeff_smul [Monoidₓ S] [DistribMulAction S R] (r : S) (p : R[X]) (n : ℕ) : coeff (r • p) n = r • coeff p n := by
  rcases p with ⟨⟩
  simp_rw [← of_finsupp_smul, coeff]
  exact Finsupp.smul_apply _ _ _

theorem support_smul [Monoidₓ S] [DistribMulAction S R] (r : S) (p : R[X]) : support (r • p) ⊆ support p := by
  intro i hi
  simp [← mem_support_iff] at hi⊢
  contrapose! hi
  simp [← hi]

/-- `polynomial.sum` as a linear map. -/
@[simps]
def lsum {R A M : Type _} [Semiringₓ R] [Semiringₓ A] [AddCommMonoidₓ M] [Module R A] [Module R M] (f : ℕ → A →ₗ[R] M) :
    Polynomial A →ₗ[R] M where
  toFun := fun p => p.Sum fun n r => f n r
  map_add' := fun p q => sum_add_index p q _ (fun n => (f n).map_zero) fun n _ _ => (f n).map_add _ _
  map_smul' := fun c p => by
    rw [sum_eq_of_subset _ (fun n r => f n r) (fun n => (f n).map_zero) _ (support_smul c p)]
    simp only [← sum_def, ← Finset.smul_sum, ← coeff_smul, ← LinearMap.map_smul, ← RingHom.id_apply]

variable (R)

/-- The nth coefficient, as a linear map. -/
def lcoeff (n : ℕ) : R[X] →ₗ[R] R where
  toFun := fun p => coeff p n
  map_add' := fun p q => coeff_add p q n
  map_smul' := fun r p => coeff_smul r p n

variable {R}

@[simp]
theorem lcoeff_apply (n : ℕ) (f : R[X]) : lcoeff R n f = coeff f n :=
  rfl

@[simp]
theorem finset_sum_coeff {ι : Type _} (s : Finset ι) (f : ι → R[X]) (n : ℕ) :
    coeff (∑ b in s, f b) n = ∑ b in s, coeff (f b) n :=
  (lcoeff R n).map_sum

theorem coeff_sum [Semiringₓ S] (n : ℕ) (f : ℕ → R → S[X]) : coeff (p.Sum f) n = p.Sum fun a b => coeff (f a b) n := by
  rcases p with ⟨⟩
  simp [← Polynomial.sum, ← support, ← coeff]

/-- Decomposes the coefficient of the product `p * q` as a sum
over `nat.antidiagonal`. A version which sums over `range (n + 1)` can be obtained
by using `finset.nat.sum_antidiagonal_eq_sum_range_succ`. -/
theorem coeff_mul (p q : R[X]) (n : ℕ) : coeff (p * q) n = ∑ x in Nat.antidiagonal n, coeff p x.1 * coeff q x.2 := by
  rcases p with ⟨⟩
  rcases q with ⟨⟩
  simp_rw [← of_finsupp_mul, coeff]
  exact AddMonoidAlgebra.mul_apply_antidiagonal p q n _ fun x => nat.mem_antidiagonal

@[simp]
theorem mul_coeff_zero (p q : R[X]) : coeff (p * q) 0 = coeff p 0 * coeff q 0 := by
  simp [← coeff_mul]

theorem coeff_mul_X_zero (p : R[X]) : coeff (p * X) 0 = 0 := by
  simp

theorem coeff_X_mul_zero (p : R[X]) : coeff (X * p) 0 = 0 := by
  simp

theorem coeff_C_mul_X_pow (x : R) (k n : ℕ) : coeff (c x * X ^ k : R[X]) n = if n = k then x else 0 := by
  rw [← monomial_eq_C_mul_X, coeff_monomial]
  congr 1
  simp [← eq_comm]

theorem coeff_C_mul_X (x : R) (n : ℕ) : coeff (c x * X : R[X]) n = if n = 1 then x else 0 := by
  rw [← pow_oneₓ X, coeff_C_mul_X_pow]

@[simp]
theorem coeff_C_mul (p : R[X]) : coeff (c a * p) n = a * coeff p n := by
  rcases p with ⟨⟩
  simp_rw [← monomial_zero_left, ← of_finsupp_single, ← of_finsupp_mul, coeff]
  exact AddMonoidAlgebra.single_zero_mul_apply p a n

theorem C_mul' (a : R) (f : R[X]) : c a * f = a • f := by
  ext
  rw [coeff_C_mul, coeff_smul, smul_eq_mul]

@[simp]
theorem coeff_mul_C (p : R[X]) (n : ℕ) (a : R) : coeff (p * c a) n = coeff p n * a := by
  rcases p with ⟨⟩
  simp_rw [← monomial_zero_left, ← of_finsupp_single, ← of_finsupp_mul, coeff]
  exact AddMonoidAlgebra.mul_single_zero_apply p a n

theorem coeff_X_pow (k n : ℕ) : coeff (X ^ k : R[X]) n = if n = k then 1 else 0 := by
  simp only [← one_mulₓ, ← RingHom.map_one, coeff_C_mul_X_pow]

@[simp]
theorem coeff_X_pow_self (n : ℕ) : coeff (X ^ n : R[X]) n = 1 := by
  simp [← coeff_X_pow]

section Fewnomials

open Finset

theorem support_binomial {k m : ℕ} (hkm : k ≠ m) {x y : R} (hx : x ≠ 0) (hy : y ≠ 0) :
    (c x * X ^ k + c y * X ^ m).Support = {k, m} := by
  apply subset_antisymm (support_binomial' k m x y)
  simp_rw [insert_subset, singleton_subset_iff, mem_support_iff, coeff_add, coeff_C_mul, coeff_X_pow_self, mul_oneₓ,
    coeff_X_pow, if_neg hkm, if_neg hkm.symm, mul_zero, zero_addₓ, add_zeroₓ, Ne.def, hx, hy, and_selfₓ, not_false_iff]

theorem support_trinomial {k m n : ℕ} (hkm : k < m) (hmn : m < n) {x y z : R} (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
    (c x * X ^ k + c y * X ^ m + c z * X ^ n).Support = {k, m, n} := by
  apply subset_antisymm (support_trinomial' k m n x y z)
  simp_rw [insert_subset, singleton_subset_iff, mem_support_iff, coeff_add, coeff_C_mul, coeff_X_pow_self, mul_oneₓ,
    coeff_X_pow, if_neg hkm.ne, if_neg hkm.ne', if_neg hmn.ne, if_neg hmn.ne', if_neg (hkm.trans hmn).Ne,
    if_neg (hkm.trans hmn).ne', mul_zero, add_zeroₓ, zero_addₓ, Ne.def, hx, hy, hz, and_selfₓ, not_false_iff]

theorem card_support_binomial {k m : ℕ} (h : k ≠ m) {x y : R} (hx : x ≠ 0) (hy : y ≠ 0) :
    (c x * X ^ k + c y * X ^ m).Support.card = 2 := by
  rw [support_binomial h hx hy, card_insert_of_not_mem (mt mem_singleton.mp h), card_singleton]

theorem card_support_trinomial {k m n : ℕ} (hkm : k < m) (hmn : m < n) {x y z : R} (hx : x ≠ 0) (hy : y ≠ 0)
    (hz : z ≠ 0) : (c x * X ^ k + c y * X ^ m + c z * X ^ n).Support.card = 3 := by
  rw [support_trinomial hkm hmn hx hy hz,
    card_insert_of_not_mem (mt mem_insert.mp (not_orₓ hkm.ne (mt mem_singleton.mp (hkm.trans hmn).Ne))),
    card_insert_of_not_mem (mt mem_singleton.mp hmn.ne), card_singleton]

end Fewnomials

@[simp]
theorem coeff_mul_X_pow (p : R[X]) (n d : ℕ) : coeff (p * Polynomial.x ^ n) (d + n) = coeff p d := by
  rw [coeff_mul, sum_eq_single (d, n), coeff_X_pow, if_pos rfl, mul_oneₓ]
  · rintro ⟨i, j⟩ h1 h2
    rw [coeff_X_pow, if_neg, mul_zero]
    rintro rfl
    apply h2
    rw [nat.mem_antidiagonal, add_right_cancel_iffₓ] at h1
    subst h1
    
  · exact fun h1 => (h1 (nat.mem_antidiagonal.2 rfl)).elim
    

@[simp]
theorem coeff_X_pow_mul (p : R[X]) (n d : ℕ) : coeff (Polynomial.x ^ n * p) (d + n) = coeff p d := by
  rw [(commute_X_pow p n).Eq, coeff_mul_X_pow]

theorem coeff_mul_X_pow' (p : R[X]) (n d : ℕ) : (p * X ^ n).coeff d = ite (n ≤ d) (p.coeff (d - n)) 0 := by
  split_ifs
  · rw [← tsub_add_cancel_of_le h, coeff_mul_X_pow, add_tsub_cancel_right]
    
  · refine' (coeff_mul _ _ _).trans (Finset.sum_eq_zero fun x hx => _)
    rw [coeff_X_pow, if_neg, mul_zero]
    exact ((le_of_add_le_right (finset.nat.mem_antidiagonal.mp hx).le).trans_lt <| not_le.mp h).Ne
    

theorem coeff_X_pow_mul' (p : R[X]) (n d : ℕ) : (X ^ n * p).coeff d = ite (n ≤ d) (p.coeff (d - n)) 0 := by
  rw [(commute_X_pow p n).Eq, coeff_mul_X_pow']

@[simp]
theorem coeff_mul_X (p : R[X]) (n : ℕ) : coeff (p * X) (n + 1) = coeff p n := by
  simpa only [← pow_oneₓ] using coeff_mul_X_pow p 1 n

@[simp]
theorem coeff_X_mul (p : R[X]) (n : ℕ) : coeff (X * p) (n + 1) = coeff p n := by
  rw [(commute_X p).Eq, coeff_mul_X]

theorem mul_X_pow_eq_zero {p : R[X]} {n : ℕ} (H : p * X ^ n = 0) : p = 0 :=
  ext fun k => (coeff_mul_X_pow p n k).symm.trans <| ext_iff.1 H (k + n)

theorem mul_X_pow_injective (n : ℕ) : Function.Injective fun P : R[X] => X ^ n * P := by
  intro P Q hPQ
  simp only at hPQ
  ext i
  rw [← coeff_X_pow_mul P n i, hPQ, coeff_X_pow_mul Q n i]

theorem mul_X_injective : Function.Injective fun P : R[X] => X * P :=
  pow_oneₓ (x : R[X]) ▸ mul_X_pow_injective 1

theorem C_mul_X_pow_eq_monomial (c : R) (n : ℕ) : c c * X ^ n = monomial n c :=
  monomial_eq_C_mul_X.symm

theorem coeff_X_add_C_pow (r : R) (n k : ℕ) : ((X + c r) ^ n).coeff k = r ^ (n - k) * (n.choose k : R) := by
  rw [(commute_X (C r : R[X])).add_pow, ← lcoeff_apply, LinearMap.map_sum]
  simp only [← one_pow, ← mul_oneₓ, ← lcoeff_apply, C_eq_nat_cast, C_pow, ← coeff_mul_C, ← Nat.cast_id]
  rw [Finset.sum_eq_single k, coeff_X_pow_self, one_mulₓ]
  · intro _ _ h
    simp [← coeff_X_pow, ← h.symm]
    
  · simp only [← coeff_X_pow_self, ← one_mulₓ, ← not_ltₓ, ← Finset.mem_range]
    intro h
    rw [Nat.choose_eq_zero_of_lt h, Nat.cast_zeroₓ, mul_zero]
    

theorem coeff_X_add_one_pow (R : Type _) [Semiringₓ R] (n k : ℕ) : ((X + 1) ^ n).coeff k = (n.choose k : R) := by
  rw [← C_1, coeff_X_add_C_pow, one_pow, one_mulₓ]

theorem coeff_one_add_X_pow (R : Type _) [Semiringₓ R] (n k : ℕ) : ((1 + X) ^ n).coeff k = (n.choose k : R) := by
  rw [add_commₓ _ X, coeff_X_add_one_pow]

theorem C_dvd_iff_dvd_coeff (r : R) (φ : R[X]) : c r ∣ φ ↔ ∀ i, r ∣ φ.coeff i := by
  constructor
  · rintro ⟨φ, rfl⟩ c
    rw [coeff_C_mul]
    apply dvd_mul_right
    
  · intro h
    choose c hc using h
    classical
    let c' : ℕ → R := fun i => if i ∈ φ.support then c i else 0
    let ψ : R[X] := ∑ i in φ.support, monomial i (c' i)
    use ψ
    ext i
    simp only [← ψ, ← c', ← coeff_C_mul, ← mem_support_iff, ← coeff_monomial, ← finset_sum_coeff, ← Finset.sum_ite_eq']
    split_ifs with hi hi
    · rw [hc]
      
    · rw [not_not] at hi
      rwa [mul_zero]
      
    

theorem coeff_bit0_mul (P Q : R[X]) (n : ℕ) : coeff (bit0 P * Q) n = 2 * coeff (P * Q) n := by
  simp [← bit0, ← add_mulₓ]

theorem coeff_bit1_mul (P Q : R[X]) (n : ℕ) : coeff (bit1 P * Q) n = 2 * coeff (P * Q) n + coeff Q n := by
  simp [← bit1, ← add_mulₓ, ← coeff_bit0_mul]

theorem smul_eq_C_mul (a : R) : a • p = c a * p := by
  simp [← ext_iff]

theorem update_eq_add_sub_coeff {R : Type _} [Ringₓ R] (p : R[X]) (n : ℕ) (a : R) :
    p.update n a = p + Polynomial.c (a - p.coeff n) * Polynomial.x ^ n := by
  ext
  rw [coeff_update_apply, coeff_add, coeff_C_mul_X_pow]
  split_ifs with h <;> simp [← h]

end Coeff

section cast

@[simp]
theorem nat_cast_coeff_zero {n : ℕ} {R : Type _} [Semiringₓ R] : (n : R[X]).coeff 0 = n := by
  induction' n with n ih
  · simp
    
  · simp [← ih]
    

@[simp, norm_cast]
theorem nat_cast_inj {m n : ℕ} {R : Type _} [Semiringₓ R] [CharZero R] : (↑m : R[X]) = ↑n ↔ m = n := by
  fconstructor
  · intro h
    apply_fun fun p => p.coeff 0  at h
    simpa using h
    
  · rintro rfl
    rfl
    

@[simp]
theorem int_cast_coeff_zero {i : ℤ} {R : Type _} [Ringₓ R] : (i : R[X]).coeff 0 = i := by
  cases i <;> simp

@[simp, norm_cast]
theorem int_cast_inj {m n : ℤ} {R : Type _} [Ringₓ R] [CharZero R] : (↑m : R[X]) = ↑n ↔ m = n := by
  fconstructor
  · intro h
    apply_fun fun p => p.coeff 0  at h
    simpa using h
    
  · rintro rfl
    rfl
    

end cast

instance [CharZero R] : CharZero R[X] where cast_injective := fun x y => nat_cast_inj.mp

end Polynomial

