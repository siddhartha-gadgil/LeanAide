/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Scott Morrison, Jens Wagemaker
-/
import Mathbin.RingTheory.Adjoin.Basic
import Mathbin.Data.Polynomial.Eval

/-!
# Theory of univariate polynomials

We show that `polynomial A` is an R-algebra when `A` is an R-algebra.
We promote `eval₂` to an algebra hom in `aeval`.
-/


noncomputable section

open Finset

open BigOperators Polynomial

namespace Polynomial

universe u v w z

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {A' B' : Type _} {a b : R} {n : ℕ}

variable [CommSemiringₓ A'] [Semiringₓ B']

section CommSemiringₓ

variable [CommSemiringₓ R] {p q r : R[X]}

variable [Semiringₓ A] [Algebra R A]

/-- Note that this instance also provides `algebra R R[X]`. -/
instance algebraOfAlgebra : Algebra R (Polynomial A) where
  smul_def' := fun r p =>
    to_finsupp_injective <| by
      dsimp' only [← RingHom.to_fun_eq_coe, ← RingHom.comp_apply]
      rw [to_finsupp_smul, to_finsupp_mul, to_finsupp_C]
      exact Algebra.smul_def' _ _
  commutes' := fun r p =>
    to_finsupp_injective <| by
      dsimp' only [← RingHom.to_fun_eq_coe, ← RingHom.comp_apply]
      simp_rw [to_finsupp_mul, to_finsupp_C]
      convert Algebra.commutes' r p.to_finsupp
  toRingHom := c.comp (algebraMap R A)

theorem algebra_map_apply (r : R) : algebraMap R (Polynomial A) r = c (algebraMap R A r) :=
  rfl

@[simp]
theorem to_finsupp_algebra_map (r : R) : (algebraMap R (Polynomial A) r).toFinsupp = algebraMap R _ r :=
  show toFinsupp (c (algebraMap _ _ r)) = _ by
    rw [to_finsupp_C]
    rfl

theorem of_finsupp_algebra_map (r : R) : (⟨algebraMap R _ r⟩ : A[X]) = algebraMap R (Polynomial A) r :=
  to_finsupp_injective (to_finsupp_algebra_map _).symm

/-- When we have `[comm_semiring R]`, the function `C` is the same as `algebra_map R R[X]`.

(But note that `C` is defined when `R` is not necessarily commutative, in which case
`algebra_map` is not available.)
-/
theorem C_eq_algebra_map (r : R) : c r = algebraMap R R[X] r :=
  rfl

variable {R}

/-- Extensionality lemma for algebra maps out of `polynomial A'` over a smaller base ring than `A'`
-/
@[ext]
theorem alg_hom_ext' [Algebra R A'] [Algebra R B'] {f g : A'[X] →ₐ[R] B'}
    (h₁ : f.comp (IsScalarTower.toAlgHom R A' (Polynomial A')) = g.comp (IsScalarTower.toAlgHom R A' (Polynomial A')))
    (h₂ : f x = g x) : f = g :=
  AlgHom.coe_ring_hom_injective (Polynomial.ring_hom_ext' (congr_arg AlgHom.toRingHom h₁) h₂)

variable (R)

/-- Algebra isomorphism between `polynomial R` and `add_monoid_algebra R ℕ`. This is just an
implementation detail, but it can be useful to transfer results from `finsupp` to polynomials. -/
@[simps]
def toFinsuppIsoAlg : R[X] ≃ₐ[R] AddMonoidAlgebra R ℕ :=
  { toFinsuppIso R with
    commutes' := fun r => by
      dsimp'
      exact to_finsupp_algebra_map _ }

variable {R}

instance [Nontrivial A] : Nontrivial (Subalgebra R (Polynomial A)) :=
  ⟨⟨⊥, ⊤, by
      rw [Ne.def, SetLike.ext_iff, not_forall]
      refine' ⟨X, _⟩
      simp only [← Algebra.mem_bot, ← not_exists, ← Set.mem_range, ← iff_trueₓ, ← Algebra.mem_top, ← algebra_map_apply,
        ← not_forall]
      intro x
      rw [ext_iff, not_forall]
      refine' ⟨1, _⟩
      simp [← coeff_C]⟩⟩

@[simp]
theorem alg_hom_eval₂_algebra_map {R A B : Type _} [CommSemiringₓ R] [Semiringₓ A] [Semiringₓ B] [Algebra R A]
    [Algebra R B] (p : R[X]) (f : A →ₐ[R] B) (a : A) :
    f (eval₂ (algebraMap R A) a p) = eval₂ (algebraMap R B) (f a) p := by
  dsimp' [← eval₂, ← Sum]
  simp only [← f.map_sum, ← f.map_mul, ← f.map_pow, ← RingHom.eq_int_cast, ← RingHom.map_int_cast, ← AlgHom.commutes]

@[simp]
theorem eval₂_algebra_map_X {R A : Type _} [CommSemiringₓ R] [Semiringₓ A] [Algebra R A] (p : R[X]) (f : R[X] →ₐ[R] A) :
    eval₂ (algebraMap R A) (f x) p = f p := by
  conv_rhs => rw [← Polynomial.sum_C_mul_X_eq p]
  dsimp' [← eval₂, ← Sum]
  simp only [← f.map_sum, ← f.map_mul, ← f.map_pow, ← RingHom.eq_int_cast, ← RingHom.map_int_cast]
  simp [← Polynomial.C_eq_algebra_map]

-- these used to be about `algebra_map ℤ R`, but now the simp-normal form is `int.cast_ring_hom R`.
@[simp]
theorem ring_hom_eval₂_cast_int_ring_hom {R S : Type _} [Ringₓ R] [Ringₓ S] (p : ℤ[X]) (f : R →+* S) (r : R) :
    f (eval₂ (Int.castRingHom R) r p) = eval₂ (Int.castRingHom S) (f r) p :=
  alg_hom_eval₂_algebra_map p f.toIntAlgHom r

@[simp]
theorem eval₂_int_cast_ring_hom_X {R : Type _} [Ringₓ R] (p : ℤ[X]) (f : ℤ[X] →+* R) :
    eval₂ (Int.castRingHom R) (f x) p = f p :=
  eval₂_algebra_map_X p f.toIntAlgHom

end CommSemiringₓ

section Aeval

variable [CommSemiringₓ R] {p q : R[X]}

variable [Semiringₓ A] [Algebra R A]

variable {B : Type _} [Semiringₓ B] [Algebra R B]

variable (x : A)

/-- Given a valuation `x` of the variable in an `R`-algebra `A`, `aeval R A x` is
the unique `R`-algebra homomorphism from `R[X]` to `A` sending `X` to `x`.

This is a stronger variant of the linear map `polynomial.leval`. -/
def aeval : R[X] →ₐ[R] A :=
  { eval₂RingHom' (algebraMap R A) x fun a => Algebra.commutes _ _ with commutes' := fun r => eval₂_C _ _ }

variable {R A}

@[simp]
theorem adjoin_X : Algebra.adjoin R ({x} : Set R[X]) = ⊤ := by
  refine' top_unique fun p hp => _
  set S := Algebra.adjoin R ({X} : Set R[X])
  rw [← sum_monomial_eq p]
  simp only [← monomial_eq_smul_X, ← Sum]
  exact S.sum_mem fun n hn => S.smul_mem (S.pow_mem (Algebra.subset_adjoin rfl) _) _

@[ext]
theorem alg_hom_ext {f g : R[X] →ₐ[R] A} (h : f x = g x) : f = g :=
  (AlgHom.ext_of_adjoin_eq_top adjoin_X) fun p hp => (Set.mem_singleton_iff.1 hp).symm ▸ h

theorem aeval_def (p : R[X]) : aeval x p = eval₂ (algebraMap R A) x p :=
  rfl

@[simp]
theorem aeval_zero : aeval x (0 : R[X]) = 0 :=
  AlgHom.map_zero (aeval x)

@[simp]
theorem aeval_X : aeval x (x : R[X]) = x :=
  eval₂_X _ x

@[simp]
theorem aeval_C (r : R) : aeval x (c r) = algebraMap R A r :=
  eval₂_C _ x

@[simp]
theorem aeval_monomial {n : ℕ} {r : R} : aeval x (monomial n r) = algebraMap _ _ r * x ^ n :=
  eval₂_monomial _ _

@[simp]
theorem aeval_X_pow {n : ℕ} : aeval x ((x : R[X]) ^ n) = x ^ n :=
  eval₂_X_pow _ _

@[simp]
theorem aeval_add : aeval x (p + q) = aeval x p + aeval x q :=
  AlgHom.map_add _ _ _

@[simp]
theorem aeval_one : aeval x (1 : R[X]) = 1 :=
  AlgHom.map_one _

@[simp]
theorem aeval_bit0 : aeval x (bit0 p) = bit0 (aeval x p) :=
  AlgHom.map_bit0 _ _

@[simp]
theorem aeval_bit1 : aeval x (bit1 p) = bit1 (aeval x p) :=
  AlgHom.map_bit1 _ _

@[simp]
theorem aeval_nat_cast (n : ℕ) : aeval x (n : R[X]) = n :=
  map_nat_cast _ _

theorem aeval_mul : aeval x (p * q) = aeval x p * aeval x q :=
  AlgHom.map_mul _ _ _

theorem aeval_comp {A : Type _} [CommSemiringₓ A] [Algebra R A] (x : A) : aeval x (p.comp q) = aeval (aeval x q) p :=
  eval₂_comp (algebraMap R A)

@[simp]
theorem aeval_map {A : Type _} [CommSemiringₓ A] [Algebra R A] [Algebra A B] [IsScalarTower R A B] (b : B) (p : R[X]) :
    aeval b (p.map (algebraMap R A)) = aeval b p := by
  rw [aeval_def, eval₂_map, ← IsScalarTower.algebra_map_eq, ← aeval_def]

theorem aeval_alg_hom (f : A →ₐ[R] B) (x : A) : aeval (f x) = f.comp (aeval x) :=
  alg_hom_ext <| by
    simp only [← aeval_X, ← AlgHom.comp_apply]

@[simp]
theorem aeval_X_left : aeval (x : R[X]) = AlgHom.id R R[X] :=
  alg_hom_ext <| aeval_X x

theorem eval_unique (φ : R[X] →ₐ[R] A) (p) : φ p = eval₂ (algebraMap R A) (φ x) p := by
  rw [← aeval_def, aeval_alg_hom, aeval_X_left, AlgHom.comp_id]

theorem aeval_alg_hom_apply (f : A →ₐ[R] B) (x : A) (p : R[X]) : aeval (f x) p = f (aeval x p) :=
  AlgHom.ext_iff.1 (aeval_alg_hom f x) p

theorem aeval_alg_equiv (f : A ≃ₐ[R] B) (x : A) : aeval (f x) = (f : A →ₐ[R] B).comp (aeval x) :=
  aeval_alg_hom (f : A →ₐ[R] B) x

theorem aeval_alg_equiv_apply (f : A ≃ₐ[R] B) (x : A) (p : R[X]) : aeval (f x) p = f (aeval x p) :=
  aeval_alg_hom_apply (f : A →ₐ[R] B) x p

theorem aeval_algebra_map_apply (x : R) (p : R[X]) : aeval (algebraMap R A x) p = algebraMap R A (p.eval x) :=
  aeval_alg_hom_apply (Algebra.ofId R A) x p

@[simp]
theorem coe_aeval_eq_eval (r : R) : (aeval r : R[X] → R) = eval r :=
  rfl

@[simp]
theorem aeval_fn_apply {X : Type _} (g : R[X]) (f : X → R) (x : X) : ((aeval f) g) x = aeval (f x) g :=
  (aeval_alg_hom_apply (Pi.evalAlgHom _ _ x) f g).symm

@[norm_cast]
theorem aeval_subalgebra_coe (g : R[X]) {A : Type _} [Semiringₓ A] [Algebra R A] (s : Subalgebra R A) (f : s) :
    (aeval f g : A) = aeval (f : A) g :=
  (aeval_alg_hom_apply s.val f g).symm

theorem coeff_zero_eq_aeval_zero (p : R[X]) : p.coeff 0 = aeval 0 p := by
  simp [← coeff_zero_eq_eval_zero]

theorem coeff_zero_eq_aeval_zero' (p : R[X]) : algebraMap R A (p.coeff 0) = aeval (0 : A) p := by
  simp [← aeval_def]

variable (R)

theorem _root_.algebra.adjoin_singleton_eq_range_aeval (x : A) : Algebra.adjoin R {x} = (Polynomial.aeval x).range := by
  rw [← Algebra.map_top, ← adjoin_X, AlgHom.map_adjoin, Set.image_singleton, aeval_X]

variable {R}

section CommSemiringₓ

variable [CommSemiringₓ S] {f : R →+* S}

theorem aeval_eq_sum_range [Algebra R S] {p : R[X]} (x : S) :
    aeval x p = ∑ i in Finset.range (p.natDegree + 1), p.coeff i • x ^ i := by
  simp_rw [Algebra.smul_def]
  exact eval₂_eq_sum_range (algebraMap R S) x

theorem aeval_eq_sum_range' [Algebra R S] {p : R[X]} {n : ℕ} (hn : p.natDegree < n) (x : S) :
    aeval x p = ∑ i in Finset.range n, p.coeff i • x ^ i := by
  simp_rw [Algebra.smul_def]
  exact eval₂_eq_sum_range' (algebraMap R S) hn x

theorem is_root_of_eval₂_map_eq_zero (hf : Function.Injective f) {r : R} : eval₂ f (f r) p = 0 → p.IsRoot r := by
  intro h
  apply hf
  rw [← eval₂_hom, h, f.map_zero]

theorem is_root_of_aeval_algebra_map_eq_zero [Algebra R S] {p : R[X]} (inj : Function.Injective (algebraMap R S))
    {r : R} (hr : aeval (algebraMap R S r) p = 0) : p.IsRoot r :=
  is_root_of_eval₂_map_eq_zero inj hr

section AevalTower

variable [Algebra S R] [Algebra S A'] [Algebra S B']

/-- Version of `aeval` for defining algebra homs out of `polynomial R` over a smaller base ring
  than `R`. -/
def aevalTower (f : R →ₐ[S] A') (x : A') : R[X] →ₐ[S] A' :=
  { eval₂RingHom (↑f) x with
    commutes' := fun r => by
      simp [← algebra_map_apply] }

variable (g : R →ₐ[S] A') (y : A')

@[simp]
theorem aeval_tower_X : aevalTower g y x = y :=
  eval₂_X _ _

@[simp]
theorem aeval_tower_C (x : R) : aevalTower g y (c x) = g x :=
  eval₂_C _ _

@[simp]
theorem aeval_tower_comp_C : (aevalTower g y : R[X] →+* A').comp c = g :=
  RingHom.ext <| aeval_tower_C _ _

@[simp]
theorem aeval_tower_algebra_map (x : R) : aevalTower g y (algebraMap R R[X] x) = g x :=
  eval₂_C _ _

@[simp]
theorem aeval_tower_comp_algebra_map : (aevalTower g y : R[X] →+* A').comp (algebraMap R R[X]) = g :=
  aeval_tower_comp_C _ _

theorem aeval_tower_to_alg_hom (x : R) : aevalTower g y (IsScalarTower.toAlgHom S R R[X] x) = g x :=
  aeval_tower_algebra_map _ _ _

@[simp]
theorem aeval_tower_comp_to_alg_hom : (aevalTower g y).comp (IsScalarTower.toAlgHom S R R[X]) = g :=
  AlgHom.coe_ring_hom_injective <| aeval_tower_comp_algebra_map _ _

@[simp]
theorem aeval_tower_id : aevalTower (AlgHom.id S S) = aeval := by
  ext
  simp only [← eval_X, ← aeval_tower_X, ← coe_aeval_eq_eval]

@[simp]
theorem aeval_tower_of_id : aevalTower (Algebra.ofId S A') = aeval := by
  ext
  simp only [← aeval_X, ← aeval_tower_X]

end AevalTower

end CommSemiringₓ

section CommRingₓ

variable [CommRingₓ S] {f : R →+* S}

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (j «expr ≠ » i)
theorem dvd_term_of_dvd_eval_of_dvd_terms {z p : S} {f : S[X]} (i : ℕ) (dvd_eval : p ∣ f.eval z)
    (dvd_terms : ∀ (j) (_ : j ≠ i), p ∣ f.coeff j * z ^ j) : p ∣ f.coeff i * z ^ i := by
  by_cases' hi : i ∈ f.support
  · rw [eval, eval₂, Sum] at dvd_eval
    rw [← Finset.insert_erase hi, Finset.sum_insert (Finset.not_mem_erase _ _)] at dvd_eval
    refine' (dvd_add_left _).mp dvd_eval
    apply Finset.dvd_sum
    intro j hj
    exact dvd_terms j (Finset.ne_of_mem_erase hj)
    
  · convert dvd_zero p
    rw [not_mem_support_iff] at hi
    simp [← hi]
    

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (j «expr ≠ » i)
theorem dvd_term_of_is_root_of_dvd_terms {r p : S} {f : S[X]} (i : ℕ) (hr : f.IsRoot r)
    (h : ∀ (j) (_ : j ≠ i), p ∣ f.coeff j * r ^ j) : p ∣ f.coeff i * r ^ i :=
  dvd_term_of_dvd_eval_of_dvd_terms i (Eq.symm hr ▸ dvd_zero p) h

end CommRingₓ

end Aeval

section Ringₓ

variable [Ringₓ R]

/-- The evaluation map is not generally multiplicative when the coefficient ring is noncommutative,
but nevertheless any polynomial of the form `p * (X - monomial 0 r)` is sent to zero
when evaluated at `r`.

This is the key step in our proof of the Cayley-Hamilton theorem.
-/
theorem eval_mul_X_sub_C {p : R[X]} (r : R) : (p * (X - c r)).eval r = 0 := by
  simp only [← eval, ← eval₂, ← RingHom.id_apply]
  have bound :=
    calc
      (p * (X - C r)).natDegree ≤ p.nat_degree + (X - C r).natDegree := nat_degree_mul_le
      _ ≤ p.nat_degree + 1 := add_le_add_left nat_degree_X_sub_C_le _
      _ < p.nat_degree + 2 := lt_add_one _
      
  rw [sum_over_range' _ _ (p.nat_degree + 2) bound]
  swap
  · simp
    
  rw [sum_range_succ']
  conv_lhs => congr apply_congr skip rw [coeff_mul_X_sub_C, sub_mul, mul_assoc, ← pow_succₓ]
  simp [← sum_range_sub', ← coeff_monomial]

theorem not_is_unit_X_sub_C [Nontrivial R] (r : R) : ¬IsUnit (X - c r) := fun ⟨⟨_, g, hfg, hgf⟩, rfl⟩ =>
  @zero_ne_one R _ _ <| by
    erw [← eval_mul_X_sub_C, hgf, eval_one]

end Ringₓ

theorem aeval_endomorphism {M : Type _} [CommRingₓ R] [AddCommGroupₓ M] [Module R M] (f : M →ₗ[R] M) (v : M)
    (p : R[X]) : aeval f p v = p.Sum fun n b => b • (f ^ n) v := by
  rw [aeval_def, eval₂]
  exact (LinearMap.applyₗ v).map_sum

end Polynomial

