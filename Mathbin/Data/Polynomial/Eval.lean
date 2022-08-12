/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Scott Morrison, Jens Wagemaker
-/
import Mathbin.Data.Polynomial.Degree.Definitions
import Mathbin.Algebra.GeomSum

/-!
# Theory of univariate polynomials

The main defs here are `eval₂`, `eval`, and `map`.
We give several lemmas about their interaction with each other and with module operations.
-/


noncomputable section

open Finset AddMonoidAlgebra

open BigOperators Polynomial

namespace Polynomial

universe u v w y

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

section Semiringₓ

variable [Semiringₓ R] {p q r : R[X]}

section

variable [Semiringₓ S]

variable (f : R →+* S) (x : S)

/-- Evaluate a polynomial `p` given a ring hom `f` from the scalar ring
  to the target and a value `x` for the variable in the target -/
def eval₂ (p : R[X]) : S :=
  p.Sum fun e a => f a * x ^ e

theorem eval₂_eq_sum {f : R →+* S} {x : S} : p.eval₂ f x = p.Sum fun e a => f a * x ^ e :=
  rfl

theorem eval₂_congr {R S : Type _} [Semiringₓ R] [Semiringₓ S] {f g : R →+* S} {s t : S} {φ ψ : R[X]} :
    f = g → s = t → φ = ψ → eval₂ f s φ = eval₂ g t ψ := by
  rintro rfl rfl rfl <;> rfl

@[simp]
theorem eval₂_at_zero : p.eval₂ f 0 = f (coeff p 0) := by
  simp (config := { contextual := true })only [← eval₂_eq_sum, ← zero_pow_eq, ← mul_ite, ← mul_zero, ← mul_oneₓ, ← Sum,
    ← not_not, ← mem_support_iff, ← sum_ite_eq', ← ite_eq_left_iff, ← RingHom.map_zero, ← implies_true_iff, ←
    eq_self_iff_true]

@[simp]
theorem eval₂_zero : (0 : R[X]).eval₂ f x = 0 := by
  simp [← eval₂_eq_sum]

@[simp]
theorem eval₂_C : (c a).eval₂ f x = f a := by
  simp [← eval₂_eq_sum]

@[simp]
theorem eval₂_X : x.eval₂ f x = x := by
  simp [← eval₂_eq_sum]

@[simp]
theorem eval₂_monomial {n : ℕ} {r : R} : (monomial n r).eval₂ f x = f r * x ^ n := by
  simp [← eval₂_eq_sum]

@[simp]
theorem eval₂_X_pow {n : ℕ} : (X ^ n).eval₂ f x = x ^ n := by
  rw [X_pow_eq_monomial]
  convert eval₂_monomial f x
  simp

@[simp]
theorem eval₂_add : (p + q).eval₂ f x = p.eval₂ f x + q.eval₂ f x := by
  apply sum_add_index <;> simp [← add_mulₓ]

@[simp]
theorem eval₂_one : (1 : R[X]).eval₂ f x = 1 := by
  rw [← C_1, eval₂_C, f.map_one]

@[simp]
theorem eval₂_bit0 : (bit0 p).eval₂ f x = bit0 (p.eval₂ f x) := by
  rw [bit0, eval₂_add, bit0]

@[simp]
theorem eval₂_bit1 : (bit1 p).eval₂ f x = bit1 (p.eval₂ f x) := by
  rw [bit1, eval₂_add, eval₂_bit0, eval₂_one, bit1]

@[simp]
theorem eval₂_smul (g : R →+* S) (p : R[X]) (x : S) {s : R} : eval₂ g x (s • p) = g s * eval₂ g x p := by
  have A : p.nat_degree < p.nat_degree.succ := Nat.lt_succ_selfₓ _
  have B : (s • p).natDegree < p.nat_degree.succ := (nat_degree_smul_le _ _).trans_lt A
  rw [eval₂_eq_sum, eval₂_eq_sum, sum_over_range' _ _ _ A, sum_over_range' _ _ _ B] <;> simp [← mul_sum, ← mul_assoc]

@[simp]
theorem eval₂_C_X : eval₂ c x p = p :=
  Polynomial.induction_on' p
    (fun p q hp hq => by
      simp [← hp, ← hq])
    fun n x => by
    rw [eval₂_monomial, monomial_eq_smul_X, C_mul']

/-- `eval₂_add_monoid_hom (f : R →+* S) (x : S)` is the `add_monoid_hom` from
`polynomial R` to `S` obtained by evaluating the pushforward of `p` along `f` at `x`. -/
@[simps]
def eval₂AddMonoidHom : R[X] →+ S where
  toFun := eval₂ f x
  map_zero' := eval₂_zero _ _
  map_add' := fun _ _ => eval₂_add _ _

@[simp]
theorem eval₂_nat_cast (n : ℕ) : (n : R[X]).eval₂ f x = n := by
  induction' n with n ih
  · simp only [← eval₂_zero, ← Nat.cast_zeroₓ]
    
  · rw [n.cast_succ, eval₂_add, ih, eval₂_one, n.cast_succ]
    

variable [Semiringₓ T]

theorem eval₂_sum (p : T[X]) (g : ℕ → T → R[X]) (x : S) : (p.Sum g).eval₂ f x = p.Sum fun n a => (g n a).eval₂ f x := by
  let T : R[X] →+ S := { toFun := eval₂ f x, map_zero' := eval₂_zero _ _, map_add' := fun p q => eval₂_add _ _ }
  have A : ∀ y, eval₂ f x y = T y := fun y => rfl
  simp only [← A]
  rw [Sum, T.map_sum, Sum]

theorem eval₂_list_sum (l : List R[X]) (x : S) : eval₂ f x l.Sum = (l.map (eval₂ f x)).Sum :=
  map_list_sum (eval₂AddMonoidHom f x) l

theorem eval₂_multiset_sum (s : Multiset R[X]) (x : S) : eval₂ f x s.Sum = (s.map (eval₂ f x)).Sum :=
  map_multiset_sum (eval₂AddMonoidHom f x) s

theorem eval₂_finset_sum (s : Finset ι) (g : ι → R[X]) (x : S) :
    (∑ i in s, g i).eval₂ f x = ∑ i in s, (g i).eval₂ f x :=
  map_sum (eval₂AddMonoidHom f x) _ _

theorem eval₂_of_finsupp {f : R →+* S} {x : S} {p : AddMonoidAlgebra R ℕ} :
    eval₂ f x (⟨p⟩ : R[X]) = liftNc (↑f) (powersHom S x) p := by
  simp only [← eval₂_eq_sum, ← Sum, ← to_finsupp_sum, ← support, ← coeff]
  rfl

theorem eval₂_mul_noncomm (hf : ∀ k, Commute (f <| q.coeff k) x) : eval₂ f x (p * q) = eval₂ f x p * eval₂ f x q := by
  rcases p with ⟨⟩
  rcases q with ⟨⟩
  simp only [← coeff] at hf
  simp only [of_finsupp_mul, ← eval₂_of_finsupp]
  exact lift_nc_mul _ _ p q fun k n hn => (hf k).pow_right n

@[simp]
theorem eval₂_mul_X : eval₂ f x (p * X) = eval₂ f x p * x := by
  refine'
    trans ((eval₂_mul_noncomm _ _) fun k => _)
      (by
        rw [eval₂_X])
  rcases em (k = 1) with (rfl | hk)
  · simp
    
  · simp [← coeff_X_of_ne_one hk]
    

@[simp]
theorem eval₂_X_mul : eval₂ f x (X * p) = eval₂ f x p * x := by
  rw [X_mul, eval₂_mul_X]

theorem eval₂_mul_C' (h : Commute (f a) x) : eval₂ f x (p * c a) = eval₂ f x p * f a := by
  rw [eval₂_mul_noncomm, eval₂_C]
  intro k
  by_cases' hk : k = 0
  · simp only [← hk, ← h, ← coeff_C_zero, ← coeff_C_ne_zero]
    
  · simp only [← coeff_C_ne_zero hk, ← RingHom.map_zero, ← Commute.zero_left]
    

theorem eval₂_list_prod_noncomm (ps : List R[X]) (hf : ∀, ∀ p ∈ ps, ∀ (k), Commute (f <| coeff p k) x) :
    eval₂ f x ps.Prod = (ps.map (Polynomial.eval₂ f x)).Prod := by
  induction' ps using List.reverseRecOn with ps p ihp
  · simp
    
  · simp only [← List.forall_mem_appendₓ, ← List.forall_mem_singletonₓ] at hf
    simp [← eval₂_mul_noncomm _ _ hf.2, ← ihp hf.1]
    

/-- `eval₂` as a `ring_hom` for noncommutative rings -/
def eval₂RingHom' (f : R →+* S) (x : S) (hf : ∀ a, Commute (f a) x) : R[X] →+* S where
  toFun := eval₂ f x
  map_add' := fun _ _ => eval₂_add _ _
  map_zero' := eval₂_zero _ _
  map_mul' := fun p q => eval₂_mul_noncomm f x fun k => hf <| coeff q k
  map_one' := eval₂_one _ _

end

/-!
We next prove that eval₂ is multiplicative
as long as target ring is commutative
(even if the source ring is not).
-/


section Eval₂

section

variable [Semiringₓ S] (f : R →+* S) (x : S)

theorem eval₂_eq_sum_range : p.eval₂ f x = ∑ i in Finset.range (p.natDegree + 1), f (p.coeff i) * x ^ i :=
  trans (congr_arg _ p.as_sum_range)
    (trans (eval₂_finset_sum f _ _ x)
      (congr_arg _
        (by
          simp )))

theorem eval₂_eq_sum_range' (f : R →+* S) {p : R[X]} {n : ℕ} (hn : p.natDegree < n) (x : S) :
    eval₂ f x p = ∑ i in Finset.range n, f (p.coeff i) * x ^ i := by
  rw [eval₂_eq_sum, p.sum_over_range' _ _ hn]
  intro i
  rw [f.map_zero, zero_mul]

end

section

variable [CommSemiringₓ S] (f : R →+* S) (x : S)

@[simp]
theorem eval₂_mul : (p * q).eval₂ f x = p.eval₂ f x * q.eval₂ f x :=
  (eval₂_mul_noncomm _ _) fun k => Commute.all _ _

theorem eval₂_mul_eq_zero_of_left (q : R[X]) (hp : p.eval₂ f x = 0) : (p * q).eval₂ f x = 0 := by
  rw [eval₂_mul f x]
  exact mul_eq_zero_of_left hp (q.eval₂ f x)

theorem eval₂_mul_eq_zero_of_right (p : R[X]) (hq : q.eval₂ f x = 0) : (p * q).eval₂ f x = 0 := by
  rw [eval₂_mul f x]
  exact mul_eq_zero_of_right (p.eval₂ f x) hq

/-- `eval₂` as a `ring_hom` -/
def eval₂RingHom (f : R →+* S) (x : S) : R[X] →+* S :=
  { eval₂AddMonoidHom f x with map_one' := eval₂_one _ _, map_mul' := fun _ _ => eval₂_mul _ _ }

@[simp]
theorem coe_eval₂_ring_hom (f : R →+* S) (x) : ⇑(eval₂RingHom f x) = eval₂ f x :=
  rfl

theorem eval₂_pow (n : ℕ) : (p ^ n).eval₂ f x = p.eval₂ f x ^ n :=
  (eval₂RingHom _ _).map_pow _ _

theorem eval₂_dvd : p ∣ q → eval₂ f x p ∣ eval₂ f x q :=
  (eval₂RingHom f x).map_dvd

theorem eval₂_eq_zero_of_dvd_of_eval₂_eq_zero (h : p ∣ q) (h0 : eval₂ f x p = 0) : eval₂ f x q = 0 :=
  zero_dvd_iff.mp (h0 ▸ eval₂_dvd f x h)

theorem eval₂_list_prod (l : List R[X]) (x : S) : eval₂ f x l.Prod = (l.map (eval₂ f x)).Prod :=
  map_list_prod (eval₂RingHom f x) l

end

end Eval₂

section Eval

variable {x : R}

/-- `eval x p` is the evaluation of the polynomial `p` at `x` -/
def eval : R → R[X] → R :=
  eval₂ (RingHom.id _)

theorem eval_eq_sum : p.eval x = p.Sum fun e a => a * x ^ e :=
  rfl

theorem eval_eq_sum_range {p : R[X]} (x : R) : p.eval x = ∑ i in Finset.range (p.natDegree + 1), p.coeff i * x ^ i := by
  rw [eval_eq_sum, sum_over_range] <;> simp

theorem eval_eq_sum_range' {p : R[X]} {n : ℕ} (hn : p.natDegree < n) (x : R) :
    p.eval x = ∑ i in Finset.range n, p.coeff i * x ^ i := by
  rw [eval_eq_sum, p.sum_over_range' _ _ hn] <;> simp

@[simp]
theorem eval₂_at_apply {S : Type _} [Semiringₓ S] (f : R →+* S) (r : R) : p.eval₂ f (f r) = f (p.eval r) := by
  rw [eval₂_eq_sum, eval_eq_sum, Sum, Sum, f.map_sum]
  simp only [← f.map_mul, ← f.map_pow]

@[simp]
theorem eval₂_at_one {S : Type _} [Semiringₓ S] (f : R →+* S) : p.eval₂ f 1 = f (p.eval 1) := by
  convert eval₂_at_apply f 1
  simp

@[simp]
theorem eval₂_at_nat_cast {S : Type _} [Semiringₓ S] (f : R →+* S) (n : ℕ) : p.eval₂ f n = f (p.eval n) := by
  convert eval₂_at_apply f n
  simp

@[simp]
theorem eval_C : (c a).eval x = a :=
  eval₂_C _ _

@[simp]
theorem eval_nat_cast {n : ℕ} : (n : R[X]).eval x = n := by
  simp only [C_eq_nat_cast, ← eval_C]

@[simp]
theorem eval_X : x.eval x = x :=
  eval₂_X _ _

@[simp]
theorem eval_monomial {n a} : (monomial n a).eval x = a * x ^ n :=
  eval₂_monomial _ _

@[simp]
theorem eval_zero : (0 : R[X]).eval x = 0 :=
  eval₂_zero _ _

@[simp]
theorem eval_add : (p + q).eval x = p.eval x + q.eval x :=
  eval₂_add _ _

@[simp]
theorem eval_one : (1 : R[X]).eval x = 1 :=
  eval₂_one _ _

@[simp]
theorem eval_bit0 : (bit0 p).eval x = bit0 (p.eval x) :=
  eval₂_bit0 _ _

@[simp]
theorem eval_bit1 : (bit1 p).eval x = bit1 (p.eval x) :=
  eval₂_bit1 _ _

@[simp]
theorem eval_smul [Monoidₓ S] [DistribMulAction S R] [IsScalarTower S R R] (s : S) (p : R[X]) (x : R) :
    (s • p).eval x = s • p.eval x := by
  rw [← smul_one_smul R s p, eval, eval₂_smul, RingHom.id_apply, smul_one_mul]

@[simp]
theorem eval_C_mul : (c a * p).eval x = a * p.eval x := by
  apply Polynomial.induction_on' p
  · intro p q ph qh
    simp only [← mul_addₓ, ← eval_add, ← ph, ← qh]
    
  · intro n b
    simp only [← mul_assoc, ← C_mul_monomial, ← eval_monomial]
    

/-- A reformulation of the expansion of (1 + y)^d:
$$(d + 1) (1 + y)^d - (d + 1)y^d = \sum_{i = 0}^d {d + 1 \choose i} \cdot i \cdot y^{i - 1}.$$
-/
theorem eval_monomial_one_add_sub [CommRingₓ S] (d : ℕ) (y : S) :
    eval (1 + y) (monomial d (d + 1 : S)) - eval y (monomial d (d + 1 : S)) =
      ∑ x_1 : ℕ in range (d + 1), ↑((d + 1).choose x_1) * (↑x_1 * y ^ (x_1 - 1)) :=
  by
  have cast_succ : (d + 1 : S) = ((d.succ : ℕ) : S) := by
    simp only [← Nat.cast_succₓ]
  rw [cast_succ, eval_monomial, eval_monomial, add_commₓ, add_pow]
  conv_lhs => congr congr skip apply_congr skip rw [one_pow, mul_oneₓ, mul_comm]
  rw [sum_range_succ, mul_addₓ, Nat.choose_self, Nat.cast_oneₓ, one_mulₓ, add_sub_cancel, mul_sum, sum_range_succ',
    Nat.cast_zeroₓ, zero_mul, mul_zero, add_zeroₓ]
  apply sum_congr rfl fun y hy => _
  rw [← mul_assoc, ← mul_assoc, ← Nat.cast_mulₓ, Nat.succ_mul_choose_eq, Nat.cast_mulₓ, Nat.add_sub_cancel]

/-- `polynomial.eval` as linear map -/
@[simps]
def leval {R : Type _} [Semiringₓ R] (r : R) : R[X] →ₗ[R] R where
  toFun := fun f => f.eval r
  map_add' := fun f g => eval_add
  map_smul' := fun c f => eval_smul c f r

@[simp]
theorem eval_nat_cast_mul {n : ℕ} : ((n : R[X]) * p).eval x = n * p.eval x := by
  rw [← C_eq_nat_cast, eval_C_mul]

@[simp]
theorem eval_mul_X : (p * X).eval x = p.eval x * x := by
  apply Polynomial.induction_on' p
  · intro p q ph qh
    simp only [← add_mulₓ, ← eval_add, ← ph, ← qh]
    
  · intro n a
    simp only [monomial_one_one_eq_X, ← monomial_mul_monomial, ← eval_monomial, ← mul_oneₓ, ← pow_succ'ₓ, ← mul_assoc]
    

@[simp]
theorem eval_mul_X_pow {k : ℕ} : (p * X ^ k).eval x = p.eval x * x ^ k := by
  induction' k with k ih
  · simp
    
  · simp [← pow_succ'ₓ, mul_assoc, ← ih]
    

theorem eval_sum (p : R[X]) (f : ℕ → R → R[X]) (x : R) : (p.Sum f).eval x = p.Sum fun n a => (f n a).eval x :=
  eval₂_sum _ _ _ _

theorem eval_finset_sum (s : Finset ι) (g : ι → R[X]) (x : R) : (∑ i in s, g i).eval x = ∑ i in s, (g i).eval x :=
  eval₂_finset_sum _ _ _ _

/-- `is_root p x` implies `x` is a root of `p`. The evaluation of `p` at `x` is zero -/
def IsRoot (p : R[X]) (a : R) : Prop :=
  p.eval a = 0

instance [DecidableEq R] : Decidable (IsRoot p a) := by
  unfold is_root <;> infer_instance

@[simp]
theorem IsRoot.def : IsRoot p a ↔ p.eval a = 0 :=
  Iff.rfl

theorem IsRoot.eq_zero (h : IsRoot p x) : eval x p = 0 :=
  h

theorem coeff_zero_eq_eval_zero (p : R[X]) : coeff p 0 = p.eval 0 :=
  calc
    coeff p 0 = coeff p 0 * 0 ^ 0 := by
      simp
    _ = p.eval 0 :=
      Eq.symm <|
        Finset.sum_eq_single _
          (fun b _ hb => by
            simp [← zero_pow (Nat.pos_of_ne_zeroₓ hb)])
          (by
            simp )
    

theorem zero_is_root_of_coeff_zero_eq_zero {p : R[X]} (hp : p.coeff 0 = 0) : IsRoot p 0 := by
  rwa [coeff_zero_eq_eval_zero] at hp

theorem IsRoot.dvd {R : Type _} [CommSemiringₓ R] {p q : R[X]} {x : R} (h : p.IsRoot x) (hpq : p ∣ q) : q.IsRoot x := by
  rwa [is_root, eval, eval₂_eq_zero_of_dvd_of_eval₂_eq_zero _ _ hpq]

theorem not_is_root_C (r a : R) (hr : r ≠ 0) : ¬IsRoot (c r) a := by
  simpa using hr

end Eval

section Comp

/-- The composition of polynomials as a polynomial. -/
def comp (p q : R[X]) : R[X] :=
  p.eval₂ c q

theorem comp_eq_sum_left : p.comp q = p.Sum fun e a => c a * q ^ e :=
  rfl

@[simp]
theorem comp_X : p.comp x = p := by
  simp only [← comp, ← eval₂, monomial_eq_C_mul_X]
  exact sum_monomial_eq _

@[simp]
theorem X_comp : x.comp p = p :=
  eval₂_X _ _

@[simp]
theorem comp_C : p.comp (c a) = c (p.eval a) := by
  simp [← comp, ← (C : R →+* _).map_sum]

@[simp]
theorem C_comp : (c a).comp p = c a :=
  eval₂_C _ _

@[simp]
theorem nat_cast_comp {n : ℕ} : (n : R[X]).comp p = n := by
  rw [← C_eq_nat_cast, C_comp]

@[simp]
theorem comp_zero : p.comp (0 : R[X]) = c (p.eval 0) := by
  rw [← C_0, comp_C]

@[simp]
theorem zero_comp : comp (0 : R[X]) p = 0 := by
  rw [← C_0, C_comp]

@[simp]
theorem comp_one : p.comp 1 = c (p.eval 1) := by
  rw [← C_1, comp_C]

@[simp]
theorem one_comp : comp (1 : R[X]) p = 1 := by
  rw [← C_1, C_comp]

@[simp]
theorem add_comp : (p + q).comp r = p.comp r + q.comp r :=
  eval₂_add _ _

@[simp]
theorem monomial_comp (n : ℕ) : (monomial n a).comp p = c a * p ^ n :=
  eval₂_monomial _ _

@[simp]
theorem mul_X_comp : (p * X).comp r = p.comp r * r := by
  apply Polynomial.induction_on' p
  · intro p q hp hq
    simp only [← hp, ← hq, ← add_mulₓ, ← add_comp]
    
  · intro n b
    simp only [← pow_succ'ₓ, ← mul_assoc, ← monomial_mul_X, ← monomial_comp]
    

@[simp]
theorem X_pow_comp {k : ℕ} : (X ^ k).comp p = p ^ k := by
  induction' k with k ih
  · simp
    
  · simp [← pow_succ'ₓ, ← mul_X_comp, ← ih]
    

@[simp]
theorem mul_X_pow_comp {k : ℕ} : (p * X ^ k).comp r = p.comp r * r ^ k := by
  induction' k with k ih
  · simp
    
  · simp [← ih, ← pow_succ'ₓ, mul_assoc, ← mul_X_comp]
    

@[simp]
theorem C_mul_comp : (c a * p).comp r = c a * p.comp r := by
  apply Polynomial.induction_on' p
  · intro p q hp hq
    simp [← hp, ← hq, ← mul_addₓ]
    
  · intro n b
    simp [← mul_assoc]
    

@[simp]
theorem nat_cast_mul_comp {n : ℕ} : ((n : R[X]) * p).comp r = n * p.comp r := by
  rw [← C_eq_nat_cast, C_mul_comp, C_eq_nat_cast]

@[simp]
theorem mul_comp {R : Type _} [CommSemiringₓ R] (p q r : R[X]) : (p * q).comp r = p.comp r * q.comp r :=
  eval₂_mul _ _

@[simp]
theorem pow_comp {R : Type _} [CommSemiringₓ R] (p q : R[X]) (n : ℕ) : (p ^ n).comp q = p.comp q ^ n :=
  ((MonoidHom.mk fun r : R[X] => r.comp q) one_comp fun r s => mul_comp r s q).map_pow p n

@[simp]
theorem bit0_comp : comp (bit0 p : R[X]) q = bit0 (p.comp q) := by
  simp only [← bit0, ← add_comp]

@[simp]
theorem bit1_comp : comp (bit1 p : R[X]) q = bit1 (p.comp q) := by
  simp only [← bit1, ← add_comp, ← bit0_comp, ← one_comp]

@[simp]
theorem smul_comp [Monoidₓ S] [DistribMulAction S R] [IsScalarTower S R R] (s : S) (p q : R[X]) :
    (s • p).comp q = s • p.comp q := by
  rw [← smul_one_smul R s p, comp, comp, eval₂_smul, ← smul_eq_C_mul, smul_assoc, one_smul]

theorem comp_assoc {R : Type _} [CommSemiringₓ R] (φ ψ χ : R[X]) : (φ.comp ψ).comp χ = φ.comp (ψ.comp χ) := by
  apply Polynomial.induction_on φ <;>
    · intros
      simp_all only [← add_comp, ← mul_comp, ← C_comp, ← X_comp, ← pow_succ'ₓ, mul_assoc]
      

theorem coeff_comp_degree_mul_degree (hqd0 : natDegree q ≠ 0) :
    coeff (p.comp q) (natDegree p * natDegree q) = leadingCoeff p * leadingCoeff q ^ natDegree p := by
  rw [comp, eval₂, coeff_sum]
  convert Finset.sum_eq_single p.nat_degree _ _
  · simp only [← coeff_nat_degree, ← coeff_C_mul, ← coeff_pow_mul_nat_degree]
    
  · intro b hbs hbp
    refine' coeff_eq_zero_of_nat_degree_lt (nat_degree_mul_le.trans_lt _)
    rw [nat_degree_C, zero_addₓ]
    refine' nat_degree_pow_le.trans_lt ((mul_lt_mul_right (pos_iff_ne_zero.mpr hqd0)).mpr _)
    exact lt_of_le_of_neₓ (le_nat_degree_of_mem_supp _ hbs) hbp
    
  · simp (config := { contextual := true })
    

end Comp

section Map

variable [Semiringₓ S]

variable (f : R →+* S)

/-- `map f p` maps a polynomial `p` across a ring hom `f` -/
def map : R[X] → S[X] :=
  eval₂ (c.comp f) x

@[simp]
theorem map_C : (c a).map f = c (f a) :=
  eval₂_C _ _

@[simp]
theorem map_X : x.map f = X :=
  eval₂_X _ _

@[simp]
theorem map_monomial {n a} : (monomial n a).map f = monomial n (f a) := by
  dsimp' only [← map]
  rw [eval₂_monomial, monomial_eq_C_mul_X]
  rfl

@[simp]
protected theorem map_zero : (0 : R[X]).map f = 0 :=
  eval₂_zero _ _

@[simp]
protected theorem map_add : (p + q).map f = p.map f + q.map f :=
  eval₂_add _ _

@[simp]
protected theorem map_one : (1 : R[X]).map f = 1 :=
  eval₂_one _ _

@[simp]
protected theorem map_mul : (p * q).map f = p.map f * q.map f := by
  rw [map, eval₂_mul_noncomm]
  exact fun k => (commute_X _).symm

@[simp]
theorem map_smul (r : R) : (r • p).map f = f r • p.map f := by
  rw [map, eval₂_smul, RingHom.comp_apply, C_mul']

/-- `polynomial.map` as a `ring_hom`. -/
-- `map` is a ring-hom unconditionally, and theoretically the definition could be replaced,
-- but this turns out not to be easy because `p.map f` does not resolve to `polynomial.map`
-- if `map` is a `ring_hom` instead of a plain function; the elaborator does not try to coerce
-- to a function before trying field (dot) notation (this may be technically infeasible);
-- the relevant code is (both lines): https://github.com/leanprover-community/
-- lean/blob/487ac5d7e9b34800502e1ddf3c7c806c01cf9d51/src/frontends/lean/elaborator.cpp#L1876-L1913
def mapRingHom (f : R →+* S) : R[X] →+* S[X] where
  toFun := Polynomial.map f
  map_add' := fun _ _ => Polynomial.map_add f
  map_zero' := Polynomial.map_zero f
  map_mul' := fun _ _ => Polynomial.map_mul f
  map_one' := Polynomial.map_one f

@[simp]
theorem coe_map_ring_hom (f : R →+* S) : ⇑(mapRingHom f) = map f :=
  rfl

-- This is protected to not clash with the global `map_nat_cast`.
@[simp]
protected theorem map_nat_cast (n : ℕ) : (n : R[X]).map f = n :=
  map_nat_cast (mapRingHom f) n

@[simp]
theorem coeff_map (n : ℕ) : coeff (p.map f) n = f (coeff p n) := by
  rw [map, eval₂, coeff_sum, Sum]
  conv_rhs => rw [← sum_C_mul_X_eq p, coeff_sum, Sum, RingHom.map_sum]
  refine' Finset.sum_congr rfl fun x hx => _
  simp [← Function.comp, ← coeff_C_mul_X_pow, ← f.map_mul]
  split_ifs <;> simp [← f.map_zero]

/-- If `R` and `S` are isomorphic, then so are their polynomial rings. -/
@[simps]
def mapEquiv (e : R ≃+* S) : R[X] ≃+* S[X] :=
  RingEquiv.ofHomInv (mapRingHom (e : R →+* S)) (mapRingHom (e.symm : S →+* R))
    (by
      ext <;> simp )
    (by
      ext <;> simp )

theorem map_map [Semiringₓ T] (g : S →+* T) (p : R[X]) : (p.map f).map g = p.map (g.comp f) :=
  ext
    (by
      simp [← coeff_map])

@[simp]
theorem map_id : p.map (RingHom.id _) = p := by
  simp [← Polynomial.ext_iff, ← coeff_map]

theorem eval₂_eq_eval_map {x : S} : p.eval₂ f x = (p.map f).eval x := by
  apply Polynomial.induction_on' p
  · intro p q hp hq
    simp [← hp, ← hq]
    
  · intro n r
    simp
    

theorem map_injective (hf : Function.Injective f) : Function.Injective (map f) := fun p q h =>
  ext fun m =>
    hf <| by
      rw [← coeff_map f, ← coeff_map f, h]

theorem map_surjective (hf : Function.Surjective f) : Function.Surjective (map f) := fun p =>
  Polynomial.induction_on' p
    (fun p q hp hq =>
      let ⟨p', hp'⟩ := hp
      let ⟨q', hq'⟩ := hq
      ⟨p' + q', by
        rw [Polynomial.map_add f, hp', hq']⟩)
    fun n s =>
    let ⟨r, hr⟩ := hf s
    ⟨monomial n r, by
      rw [map_monomial f, hr]⟩

theorem degree_map_le (p : R[X]) : degree (p.map f) ≤ degree p := by
  apply (degree_le_iff_coeff_zero _ _).2 fun m hm => _
  rw [degree_lt_iff_coeff_zero] at hm
  simp [← hm m le_rfl]

theorem nat_degree_map_le (p : R[X]) : natDegree (p.map f) ≤ natDegree p :=
  nat_degree_le_nat_degree (degree_map_le f p)

variable {f}

theorem map_monic_eq_zero_iff (hp : p.Monic) : p.map f = 0 ↔ ∀ x, f x = 0 :=
  ⟨fun hfp x =>
    calc
      f x = f x * f p.leadingCoeff := by
        simp only [← mul_oneₓ, ← hp.leading_coeff, ← f.map_one]
      _ = f x * (p.map f).coeff p.natDegree := congr_arg _ (coeff_map _ _).symm
      _ = 0 := by
        simp only [← hfp, ← mul_zero, ← coeff_zero]
      ,
    fun h =>
    ext fun n => by
      simp only [← h, ← coeff_map, ← coeff_zero]⟩

theorem map_monic_ne_zero (hp : p.Monic) [Nontrivial S] : p.map f ≠ 0 := fun h =>
  f.map_one_ne_zero ((map_monic_eq_zero_iff hp).mp h _)

theorem degree_map_eq_of_leading_coeff_ne_zero (f : R →+* S) (hf : f (leadingCoeff p) ≠ 0) :
    degree (p.map f) = degree p :=
  le_antisymmₓ (degree_map_le f _) <| by
    have hp0 : p ≠ 0 := leading_coeff_ne_zero.mp fun hp0 => hf (trans (congr_arg _ hp0) f.map_zero)
    rw [degree_eq_nat_degree hp0]
    refine' le_degree_of_ne_zero _
    rw [coeff_map]
    exact hf

theorem nat_degree_map_of_leading_coeff_ne_zero (f : R →+* S) (hf : f (leadingCoeff p) ≠ 0) :
    natDegree (p.map f) = natDegree p :=
  nat_degree_eq_of_degree_eq (degree_map_eq_of_leading_coeff_ne_zero f hf)

theorem leading_coeff_map_of_leading_coeff_ne_zero (f : R →+* S) (hf : f (leadingCoeff p) ≠ 0) :
    leadingCoeff (p.map f) = f (leadingCoeff p) := by
  unfold leading_coeff
  rw [coeff_map, nat_degree_map_of_leading_coeff_ne_zero f hf]

variable (f)

@[simp]
theorem map_ring_hom_id : mapRingHom (RingHom.id R) = RingHom.id R[X] :=
  RingHom.ext fun x => map_id

@[simp]
theorem map_ring_hom_comp [Semiringₓ T] (f : S →+* T) (g : R →+* S) :
    (mapRingHom f).comp (mapRingHom g) = mapRingHom (f.comp g) :=
  RingHom.ext <| Polynomial.map_map g f

protected theorem map_list_prod (L : List R[X]) : L.Prod.map f = (L.map <| map f).Prod :=
  Eq.symm <| List.prod_hom _ (mapRingHom f).toMonoidHom

@[simp]
protected theorem map_pow (n : ℕ) : (p ^ n).map f = p.map f ^ n :=
  (mapRingHom f).map_pow _ _

theorem mem_map_srange {p : S[X]} : p ∈ (mapRingHom f).srange ↔ ∀ n, p.coeff n ∈ f.srange := by
  constructor
  · rintro ⟨p, rfl⟩ n
    rw [coe_map_ring_hom, coeff_map]
    exact Set.mem_range_self _
    
  · intro h
    rw [p.as_sum_range_C_mul_X_pow]
    refine' (map_ring_hom f).srange.sum_mem _
    intro i hi
    rcases h i with ⟨c, hc⟩
    use C c * X ^ i
    rw [coe_map_ring_hom, Polynomial.map_mul, map_C, hc, Polynomial.map_pow, map_X]
    

theorem mem_map_range {R S : Type _} [Ringₓ R] [Ringₓ S] (f : R →+* S) {p : S[X]} :
    p ∈ (mapRingHom f).range ↔ ∀ n, p.coeff n ∈ f.range :=
  mem_map_srange f

theorem eval₂_map [Semiringₓ T] (g : S →+* T) (x : T) : (p.map f).eval₂ g x = p.eval₂ (g.comp f) x := by
  rw [eval₂_eq_eval_map, eval₂_eq_eval_map, map_map]

theorem eval_map (x : S) : (p.map f).eval x = p.eval₂ f x :=
  (eval₂_eq_eval_map f).symm

protected theorem map_sum {ι : Type _} (g : ι → R[X]) (s : Finset ι) : (∑ i in s, g i).map f = ∑ i in s, (g i).map f :=
  (mapRingHom f).map_sum _ _

theorem map_comp (p q : R[X]) : map f (p.comp q) = (map f p).comp (map f q) :=
  Polynomial.induction_on p
    (by
      simp only [← map_C, ← forall_const, ← C_comp, ← eq_self_iff_true])
    (by
      simp (config := { contextual := true })only [← Polynomial.map_add, ← add_comp, ← forall_const, ← implies_true_iff,
        ← eq_self_iff_true])
    (by
      simp (config := { contextual := true })only [← pow_succ'ₓ, mul_assoc, ← comp, ← forall_const, ← eval₂_mul_X, ←
        implies_true_iff, ← eq_self_iff_true, ← map_X, ← Polynomial.map_mul])

@[simp]
theorem eval_zero_map (f : R →+* S) (p : R[X]) : (p.map f).eval 0 = f (p.eval 0) := by
  simp [coeff_zero_eq_eval_zero]

@[simp]
theorem eval_one_map (f : R →+* S) (p : R[X]) : (p.map f).eval 1 = f (p.eval 1) := by
  apply Polynomial.induction_on' p
  · intro p q hp hq
    simp only [← hp, ← hq, ← Polynomial.map_add, ← RingHom.map_add, ← eval_add]
    
  · intro n r
    simp only [← one_pow, ← mul_oneₓ, ← eval_monomial, ← map_monomial]
    

@[simp]
theorem eval_nat_cast_map (f : R →+* S) (p : R[X]) (n : ℕ) : (p.map f).eval n = f (p.eval n) := by
  apply Polynomial.induction_on' p
  · intro p q hp hq
    simp only [← hp, ← hq, ← Polynomial.map_add, ← RingHom.map_add, ← eval_add]
    
  · intro n r
    simp only [← map_nat_cast f, ← eval_monomial, ← map_monomial, ← f.map_pow, ← f.map_mul]
    

@[simp]
theorem eval_int_cast_map {R S : Type _} [Ringₓ R] [Ringₓ S] (f : R →+* S) (p : R[X]) (i : ℤ) :
    (p.map f).eval i = f (p.eval i) := by
  apply Polynomial.induction_on' p
  · intro p q hp hq
    simp only [← hp, ← hq, ← Polynomial.map_add, ← RingHom.map_add, ← eval_add]
    
  · intro n r
    simp only [← f.map_int_cast, ← eval_monomial, ← map_monomial, ← f.map_pow, ← f.map_mul]
    

end Map

/-!
After having set up the basic theory of `eval₂`, `eval`, `comp`, and `map`,
we make `eval₂` irreducible.

Perhaps we can make the others irreducible too?
-/


section HomEval₂

variable [Semiringₓ S] [Semiringₓ T] (f : R →+* S) (g : S →+* T) (p)

theorem hom_eval₂ (x : S) : g (p.eval₂ f x) = p.eval₂ (g.comp f) (g x) := by
  rw [← eval₂_map, eval₂_at_apply, eval_map]

end HomEval₂

end Semiringₓ

section CommSemiringₓ

section Eval

section

variable [Semiringₓ R] {p q : R[X]} {x : R} [Semiringₓ S] (f : R →+* S)

theorem eval₂_hom (x : R) : p.eval₂ f (f x) = f (p.eval x) :=
  RingHom.comp_id f ▸ (hom_eval₂ p (RingHom.id R) f x).symm

end

section

variable [Semiringₓ R] {p q : R[X]} {x : R} [CommSemiringₓ S] (f : R →+* S)

theorem eval₂_comp {x : S} : eval₂ f x (p.comp q) = eval₂ f (eval₂ f x q) p := by
  rw [comp, p.as_sum_range] <;> simp [← eval₂_finset_sum, ← eval₂_pow]

end

section

variable [CommSemiringₓ R] {p q : R[X]} {x : R} [CommSemiringₓ S] (f : R →+* S)

@[simp]
theorem eval_mul : (p * q).eval x = p.eval x * q.eval x :=
  eval₂_mul _ _

/-- `eval r`, regarded as a ring homomorphism from `polynomial R` to `R`. -/
def evalRingHom : R → R[X] →+* R :=
  eval₂RingHom (RingHom.id _)

@[simp]
theorem coe_eval_ring_hom (r : R) : (evalRingHom r : R[X] → R) = eval r :=
  rfl

@[simp]
theorem eval_pow (n : ℕ) : (p ^ n).eval x = p.eval x ^ n :=
  eval₂_pow _ _ _

@[simp]
theorem eval_comp : (p.comp q).eval x = p.eval (q.eval x) := by
  apply Polynomial.induction_on' p
  · intro r s hr hs
    simp [← add_comp, ← hr, ← hs]
    
  · intro n a
    simp
    

/-- `comp p`, regarded as a ring homomorphism from `polynomial R` to itself. -/
def compRingHom : R[X] → R[X] →+* R[X] :=
  eval₂RingHom c

@[simp]
theorem coe_comp_ring_hom (q : R[X]) : (compRingHom q : R[X] → R[X]) = fun p => comp p q :=
  rfl

theorem coe_comp_ring_hom_apply (p q : R[X]) : (compRingHom q : R[X] → R[X]) p = comp p q :=
  rfl

theorem root_mul_left_of_is_root (p : R[X]) {q : R[X]} : IsRoot q a → IsRoot (p * q) a := fun H => by
  rw [is_root, eval_mul, is_root.def.1 H, mul_zero]

theorem root_mul_right_of_is_root {p : R[X]} (q : R[X]) : IsRoot p a → IsRoot (p * q) a := fun H => by
  rw [is_root, eval_mul, is_root.def.1 H, zero_mul]

theorem eval₂_multiset_prod (s : Multiset R[X]) (x : S) : eval₂ f x s.Prod = (s.map (eval₂ f x)).Prod :=
  map_multiset_prod (eval₂RingHom f x) s

theorem eval₂_finset_prod (s : Finset ι) (g : ι → R[X]) (x : S) :
    (∏ i in s, g i).eval₂ f x = ∏ i in s, (g i).eval₂ f x :=
  map_prod (eval₂RingHom f x) _ _

/-- Polynomial evaluation commutes with `list.prod`
-/
theorem eval_list_prod (l : List R[X]) (x : R) : eval x l.Prod = (l.map (eval x)).Prod :=
  (evalRingHom x).map_list_prod l

/-- Polynomial evaluation commutes with `multiset.prod`
-/
theorem eval_multiset_prod (s : Multiset R[X]) (x : R) : eval x s.Prod = (s.map (eval x)).Prod :=
  (evalRingHom x).map_multiset_prod s

/-- Polynomial evaluation commutes with `finset.prod`
-/
theorem eval_prod {ι : Type _} (s : Finset ι) (p : ι → R[X]) (x : R) :
    eval x (∏ j in s, p j) = ∏ j in s, eval x (p j) :=
  (evalRingHom x).map_prod _ _

theorem list_prod_comp (l : List R[X]) (q : R[X]) : l.Prod.comp q = (l.map fun p : R[X] => p.comp q).Prod :=
  map_list_prod (compRingHom q) _

theorem multiset_prod_comp (s : Multiset R[X]) (q : R[X]) : s.Prod.comp q = (s.map fun p : R[X] => p.comp q).Prod :=
  map_multiset_prod (compRingHom q) _

theorem prod_comp {ι : Type _} (s : Finset ι) (p : ι → R[X]) (q : R[X]) :
    (∏ j in s, p j).comp q = ∏ j in s, (p j).comp q :=
  map_prod (compRingHom q) _ _

theorem is_root_prod {R} [CommRingₓ R] [IsDomain R] {ι : Type _} (s : Finset ι) (p : ι → R[X]) (x : R) :
    IsRoot (∏ j in s, p j) x ↔ ∃ i ∈ s, IsRoot (p i) x := by
  simp only [← is_root, ← eval_prod, ← Finset.prod_eq_zero_iff]

theorem eval_dvd : p ∣ q → eval x p ∣ eval x q :=
  eval₂_dvd _ _

theorem eval_eq_zero_of_dvd_of_eval_eq_zero : p ∣ q → eval x p = 0 → eval x q = 0 :=
  eval₂_eq_zero_of_dvd_of_eval₂_eq_zero _ _

@[simp]
theorem eval_geom_sum {R} [CommSemiringₓ R] {n : ℕ} {x : R} : eval x (∑ i in range n, X ^ i) = ∑ i in range n, x ^ i :=
  by
  simp [← eval_finset_sum]

end

end Eval

section Map

--TODO rename to `map_dvd_map`
theorem map_dvd {R S} [Semiringₓ R] [CommSemiringₓ S] (f : R →+* S) {x y : R[X]} : x ∣ y → x.map f ∣ y.map f :=
  eval₂_dvd _ _

theorem support_map_subset [Semiringₓ R] [Semiringₓ S] (f : R →+* S) (p : R[X]) : (map f p).Support ⊆ p.Support := by
  intro x
  contrapose!
  simp (config := { contextual := true })

theorem support_map_of_injective [Semiringₓ R] [Semiringₓ S] (p : R[X]) {f : R →+* S} (hf : Function.Injective f) :
    (map f p).Support = p.Support := by
  simp_rw [Finset.ext_iff, mem_support_iff, coeff_map, ← map_zero f, hf.ne_iff, iff_selfₓ, forall_const]

variable [CommSemiringₓ R] [CommSemiringₓ S] (f : R →+* S)

protected theorem map_multiset_prod (m : Multiset R[X]) : m.Prod.map f = (m.map <| map f).Prod :=
  Eq.symm <| Multiset.prod_hom _ (mapRingHom f).toMonoidHom

protected theorem map_prod {ι : Type _} (g : ι → R[X]) (s : Finset ι) : (∏ i in s, g i).map f = ∏ i in s, (g i).map f :=
  (mapRingHom f).map_prod _ _

theorem IsRoot.map {f : R →+* S} {x : R} {p : R[X]} (h : IsRoot p x) : IsRoot (p.map f) (f x) := by
  rw [is_root, eval_map, eval₂_hom, h.eq_zero, f.map_zero]

theorem IsRoot.of_map {R} [CommRingₓ R] {f : R →+* S} {x : R} {p : R[X]} (h : IsRoot (p.map f) (f x))
    (hf : Function.Injective f) : IsRoot p x := by
  rwa [is_root, ← (injective_iff_map_eq_zero' f).mp hf, ← eval₂_hom, ← eval_map]

theorem is_root_map_iff {R : Type _} [CommRingₓ R] {f : R →+* S} {x : R} {p : R[X]} (hf : Function.Injective f) :
    IsRoot (p.map f) (f x) ↔ IsRoot p x :=
  ⟨fun h => h.of_map hf, fun h => h.map⟩

end Map

end CommSemiringₓ

section Ringₓ

variable [Ringₓ R] {p q r : R[X]}

theorem C_neg : c (-a) = -c a :=
  RingHom.map_neg c a

theorem C_sub : c (a - b) = c a - c b :=
  RingHom.map_sub c a b

@[simp]
protected theorem map_sub {S} [Ringₓ S] (f : R →+* S) : (p - q).map f = p.map f - q.map f :=
  (mapRingHom f).map_sub p q

@[simp]
protected theorem map_neg {S} [Ringₓ S] (f : R →+* S) : (-p).map f = -p.map f :=
  (mapRingHom f).map_neg p

@[simp]
theorem map_int_cast {S} [Ringₓ S] (f : R →+* S) (n : ℤ) : map f ↑n = ↑n :=
  (mapRingHom f).map_int_cast n

@[simp]
theorem eval_int_cast {n : ℤ} {x : R} : (n : R[X]).eval x = n := by
  simp only [C_eq_int_cast, ← eval_C]

@[simp]
theorem eval₂_neg {S} [Ringₓ S] (f : R →+* S) {x : S} : (-p).eval₂ f x = -p.eval₂ f x := by
  rw [eq_neg_iff_add_eq_zero, ← eval₂_add, add_left_negₓ, eval₂_zero]

@[simp]
theorem eval₂_sub {S} [Ringₓ S] (f : R →+* S) {x : S} : (p - q).eval₂ f x = p.eval₂ f x - q.eval₂ f x := by
  rw [sub_eq_add_neg, eval₂_add, eval₂_neg, sub_eq_add_neg]

@[simp]
theorem eval_neg (p : R[X]) (x : R) : (-p).eval x = -p.eval x :=
  eval₂_neg _

@[simp]
theorem eval_sub (p q : R[X]) (x : R) : (p - q).eval x = p.eval x - q.eval x :=
  eval₂_sub _

theorem root_X_sub_C : IsRoot (X - c a) b ↔ a = b := by
  rw [is_root.def, eval_sub, eval_X, eval_C, sub_eq_zero, eq_comm]

@[simp]
theorem neg_comp : (-p).comp q = -p.comp q :=
  eval₂_neg _

@[simp]
theorem sub_comp : (p - q).comp r = p.comp r - q.comp r :=
  eval₂_sub _

@[simp]
theorem cast_int_comp (i : ℤ) : comp (i : R[X]) p = i := by
  cases i <;> simp

end Ringₓ

end Polynomial

