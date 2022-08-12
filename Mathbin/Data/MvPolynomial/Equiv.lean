/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Johan Commelin, Mario Carneiro
-/
import Mathbin.Data.MvPolynomial.Rename
import Mathbin.Data.Polynomial.AlgebraMap
import Mathbin.Data.Polynomial.Lifts
import Mathbin.Data.MvPolynomial.Variables
import Mathbin.Data.Finsupp.Fin
import Mathbin.Logic.Equiv.Fin
import Mathbin.Algebra.BigOperators.Fin

/-!
# Equivalences between polynomial rings

This file establishes a number of equivalences between polynomial rings,
based on equivalences between the underlying types.

## Notation

As in other polynomial files, we typically use the notation:

+ `σ : Type*` (indexing the variables)

+ `R : Type*` `[comm_semiring R]` (the coefficients)

+ `s : σ →₀ ℕ`, a function from `σ` to `ℕ` which is zero away from a finite set.
This will give rise to a monomial in `mv_polynomial σ R` which mathematicians might call `X^s`

+ `a : R`

+ `i : σ`, with corresponding monomial `X i`, often denoted `X_i` by mathematicians

+ `p : mv_polynomial σ R`

## Tags

equivalence, isomorphism, morphism, ring hom, hom

-/


noncomputable section

open Classical BigOperators Polynomial

open Set Function Finsupp AddMonoidAlgebra

universe u v w x

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

namespace MvPolynomial

variable {σ : Type _} {a a' a₁ a₂ : R} {e : ℕ} {s : σ →₀ ℕ}

section Equivₓ

variable (R) [CommSemiringₓ R]

/-- The ring isomorphism between multivariable polynomials in a single variable and
polynomials over the ground ring.
-/
@[simps]
def punitAlgEquiv : MvPolynomial PUnit R ≃ₐ[R] R[X] where
  toFun := eval₂ Polynomial.c fun u : PUnit => Polynomial.x
  invFun := Polynomial.eval₂ MvPolynomial.c (x PUnit.unit)
  left_inv := by
    let f : R[X] →+* MvPolynomial PUnit R := Polynomial.eval₂RingHom MvPolynomial.c (X PUnit.unit)
    let g : MvPolynomial PUnit R →+* R[X] := eval₂_hom Polynomial.c fun u : PUnit => Polynomial.x
    show ∀ p, f.comp g p = p
    apply is_id
    · ext a
      dsimp'
      rw [eval₂_C, Polynomial.eval₂_C]
      
    · rintro ⟨⟩
      dsimp'
      rw [eval₂_X, Polynomial.eval₂_X]
      
  right_inv := fun p =>
    Polynomial.induction_on p
      (fun a => by
        rw [Polynomial.eval₂_C, MvPolynomial.eval₂_C])
      (fun p q hp hq => by
        rw [Polynomial.eval₂_add, MvPolynomial.eval₂_add, hp, hq])
      fun p n hp => by
      rw [Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C, eval₂_mul, eval₂_C,
        eval₂_pow, eval₂_X]
  map_mul' := fun _ _ => eval₂_mul _ _
  map_add' := fun _ _ => eval₂_add _ _
  commutes' := fun _ => eval₂_C _ _ _

section Map

variable {R} (σ)

/-- If `e : A ≃+* B` is an isomorphism of rings, then so is `map e`. -/
@[simps apply]
def mapEquiv [CommSemiringₓ S₁] [CommSemiringₓ S₂] (e : S₁ ≃+* S₂) : MvPolynomial σ S₁ ≃+* MvPolynomial σ S₂ :=
  { map (e : S₁ →+* S₂) with toFun := map (e : S₁ →+* S₂), invFun := map (e.symm : S₂ →+* S₁),
    left_inv := map_left_inverse e.left_inv, right_inv := map_right_inverse e.right_inv }

@[simp]
theorem map_equiv_refl : mapEquiv σ (RingEquiv.refl R) = RingEquiv.refl _ :=
  RingEquiv.ext map_id

@[simp]
theorem map_equiv_symm [CommSemiringₓ S₁] [CommSemiringₓ S₂] (e : S₁ ≃+* S₂) :
    (mapEquiv σ e).symm = mapEquiv σ e.symm :=
  rfl

@[simp]
theorem map_equiv_trans [CommSemiringₓ S₁] [CommSemiringₓ S₂] [CommSemiringₓ S₃] (e : S₁ ≃+* S₂) (f : S₂ ≃+* S₃) :
    (mapEquiv σ e).trans (mapEquiv σ f) = mapEquiv σ (e.trans f) :=
  RingEquiv.ext (map_map e f)

variable {A₁ A₂ A₃ : Type _} [CommSemiringₓ A₁] [CommSemiringₓ A₂] [CommSemiringₓ A₃]

variable [Algebra R A₁] [Algebra R A₂] [Algebra R A₃]

/-- If `e : A ≃ₐ[R] B` is an isomorphism of `R`-algebras, then so is `map e`. -/
@[simps apply]
def mapAlgEquiv (e : A₁ ≃ₐ[R] A₂) : MvPolynomial σ A₁ ≃ₐ[R] MvPolynomial σ A₂ :=
  { mapAlgHom (e : A₁ →ₐ[R] A₂), mapEquiv σ (e : A₁ ≃+* A₂) with toFun := map (e : A₁ →+* A₂) }

@[simp]
theorem map_alg_equiv_refl : mapAlgEquiv σ (AlgEquiv.refl : A₁ ≃ₐ[R] A₁) = AlgEquiv.refl :=
  AlgEquiv.ext map_id

@[simp]
theorem map_alg_equiv_symm (e : A₁ ≃ₐ[R] A₂) : (mapAlgEquiv σ e).symm = mapAlgEquiv σ e.symm :=
  rfl

@[simp]
theorem map_alg_equiv_trans (e : A₁ ≃ₐ[R] A₂) (f : A₂ ≃ₐ[R] A₃) :
    (mapAlgEquiv σ e).trans (mapAlgEquiv σ f) = mapAlgEquiv σ (e.trans f) :=
  AlgEquiv.ext (map_map e f)

end Map

section

variable (S₁ S₂ S₃)

/-- The function from multivariable polynomials in a sum of two types,
to multivariable polynomials in one of the types,
with coefficents in multivariable polynomials in the other type.

See `sum_ring_equiv` for the ring isomorphism.
-/
def sumToIter : MvPolynomial (Sum S₁ S₂) R →+* MvPolynomial S₁ (MvPolynomial S₂ R) :=
  eval₂Hom (c.comp c) fun bc => Sum.recOn bc x (C ∘ X)

@[simp]
theorem sum_to_iter_C (a : R) : sumToIter R S₁ S₂ (c a) = c (c a) :=
  eval₂_C _ _ a

@[simp]
theorem sum_to_iter_Xl (b : S₁) : sumToIter R S₁ S₂ (x (Sum.inl b)) = x b :=
  eval₂_X _ _ (Sum.inl b)

@[simp]
theorem sum_to_iter_Xr (c : S₂) : sumToIter R S₁ S₂ (x (Sum.inr c)) = c (x c) :=
  eval₂_X _ _ (Sum.inr c)

/-- The function from multivariable polynomials in one type,
with coefficents in multivariable polynomials in another type,
to multivariable polynomials in the sum of the two types.

See `sum_ring_equiv` for the ring isomorphism.
-/
def iterToSum : MvPolynomial S₁ (MvPolynomial S₂ R) →+* MvPolynomial (Sum S₁ S₂) R :=
  eval₂Hom (eval₂Hom c (X ∘ Sum.inr)) (X ∘ Sum.inl)

theorem iter_to_sum_C_C (a : R) : iterToSum R S₁ S₂ (c (c a)) = c a :=
  Eq.trans (eval₂_C _ _ (c a)) (eval₂_C _ _ _)

theorem iter_to_sum_X (b : S₁) : iterToSum R S₁ S₂ (x b) = x (Sum.inl b) :=
  eval₂_X _ _ _

theorem iter_to_sum_C_X (c : S₂) : iterToSum R S₁ S₂ (c (x c)) = x (Sum.inr c) :=
  Eq.trans (eval₂_C _ _ (x c)) (eval₂_X _ _ _)

variable (σ)

/-- The algebra isomorphism between multivariable polynomials in no variables
and the ground ring. -/
@[simps]
def isEmptyAlgEquiv [he : IsEmpty σ] : MvPolynomial σ R ≃ₐ[R] R :=
  AlgEquiv.ofAlgHom (aeval (IsEmpty.elim he)) (Algebra.ofId _ _)
    (by
      ext
      simp [← Algebra.of_id_apply, ← algebra_map_eq])
    (by
      ext i m
      exact IsEmpty.elim' he i)

/-- The ring isomorphism between multivariable polynomials in no variables
and the ground ring. -/
@[simps]
def isEmptyRingEquiv [he : IsEmpty σ] : MvPolynomial σ R ≃+* R :=
  (isEmptyAlgEquiv R σ).toRingEquiv

variable {σ}

/-- A helper function for `sum_ring_equiv`. -/
@[simps]
def mvPolynomialEquivMvPolynomial [CommSemiringₓ S₃] (f : MvPolynomial S₁ R →+* MvPolynomial S₂ S₃)
    (g : MvPolynomial S₂ S₃ →+* MvPolynomial S₁ R) (hfgC : (f.comp g).comp c = C) (hfgX : ∀ n, f (g (x n)) = x n)
    (hgfC : (g.comp f).comp c = C) (hgfX : ∀ n, g (f (x n)) = x n) : MvPolynomial S₁ R ≃+* MvPolynomial S₂ S₃ where
  toFun := f
  invFun := g
  left_inv := is_id (RingHom.comp _ _) hgfC hgfX
  right_inv := is_id (RingHom.comp _ _) hfgC hfgX
  map_mul' := f.map_mul
  map_add' := f.map_add

/-- The ring isomorphism between multivariable polynomials in a sum of two types,
and multivariable polynomials in one of the types,
with coefficents in multivariable polynomials in the other type.
-/
def sumRingEquiv : MvPolynomial (Sum S₁ S₂) R ≃+* MvPolynomial S₁ (MvPolynomial S₂ R) := by
  apply @mv_polynomial_equiv_mv_polynomial R (Sum S₁ S₂) _ _ _ _ (sum_to_iter R S₁ S₂) (iter_to_sum R S₁ S₂)
  · refine' RingHom.ext fun p => _
    rw [RingHom.comp_apply]
    convert hom_eq_hom ((sum_to_iter R S₁ S₂).comp ((iter_to_sum R S₁ S₂).comp C)) C _ _ p
    · ext1 a
      dsimp'
      rw [iter_to_sum_C_C R S₁ S₂, sum_to_iter_C R S₁ S₂]
      
    · intro c
      dsimp'
      rw [iter_to_sum_C_X R S₁ S₂, sum_to_iter_Xr R S₁ S₂]
      
    
  · intro b
    rw [iter_to_sum_X R S₁ S₂, sum_to_iter_Xl R S₁ S₂]
    
  · ext1 a
    rw [RingHom.comp_apply, RingHom.comp_apply, sum_to_iter_C R S₁ S₂, iter_to_sum_C_C R S₁ S₂]
    
  · intro n
    cases' n with b c
    · rw [sum_to_iter_Xl, iter_to_sum_X]
      
    · rw [sum_to_iter_Xr, iter_to_sum_C_X]
      
    

/-- The algebra isomorphism between multivariable polynomials in a sum of two types,
and multivariable polynomials in one of the types,
with coefficents in multivariable polynomials in the other type.
-/
def sumAlgEquiv : MvPolynomial (Sum S₁ S₂) R ≃ₐ[R] MvPolynomial S₁ (MvPolynomial S₂ R) :=
  { sumRingEquiv R S₁ S₂ with
    commutes' := by
      intro r
      have A : algebraMap R (MvPolynomial S₁ (MvPolynomial S₂ R)) r = (C (C r) : _) := by
        rfl
      have B : algebraMap R (MvPolynomial (Sum S₁ S₂) R) r = C r := by
        rfl
      simp only [← sum_ring_equiv, ← sum_to_iter_C, ← mv_polynomial_equiv_mv_polynomial_apply, ←
        RingEquiv.to_fun_eq_coe, ← A, ← B] }

section

-- this speeds up typeclass search in the lemma below
attribute [local instance] IsScalarTower.right

/-- The algebra isomorphism between multivariable polynomials in `option S₁` and
polynomials with coefficients in `mv_polynomial S₁ R`.
-/
@[simps]
def optionEquivLeft : MvPolynomial (Option S₁) R ≃ₐ[R] Polynomial (MvPolynomial S₁ R) :=
  AlgEquiv.ofAlgHom (MvPolynomial.aeval fun o => o.elim Polynomial.x fun s => Polynomial.c (x s))
    (Polynomial.aevalTower (MvPolynomial.rename some) (x none))
    (by
      ext : 2 <;> simp [Polynomial.C_eq_algebra_map])
    (by
      ext i : 2 <;> cases i <;> simp )

end

/-- The algebra isomorphism between multivariable polynomials in `option S₁` and
multivariable polynomials with coefficients in polynomials.
-/
def optionEquivRight : MvPolynomial (Option S₁) R ≃ₐ[R] MvPolynomial S₁ R[X] :=
  AlgEquiv.ofAlgHom (MvPolynomial.aeval fun o => o.elim (c Polynomial.x) x)
    (MvPolynomial.aevalTower (Polynomial.aeval (x none)) fun i => x (Option.some i))
    (by
      ext : 2 <;>
        simp only [← MvPolynomial.algebra_map_eq, ← Option.elimₓ, ← AlgHom.coe_comp, ← AlgHom.id_comp, ←
          IsScalarTower.coe_to_alg_hom', ← comp_app, ← aeval_tower_C, ← Polynomial.aeval_X, ← aeval_X, ← Option.elimₓ, ←
          aeval_tower_X, ← AlgHom.coe_id, ← id.def, ← eq_self_iff_true, ← implies_true_iff])
    (by
      ext ⟨i⟩ : 2 <;>
        simp only [← Option.elimₓ, ← AlgHom.coe_comp, ← comp_app, ← aeval_X, ← aeval_tower_C, ← Polynomial.aeval_X, ←
          AlgHom.coe_id, ← id.def, ← aeval_tower_X])

variable (n : ℕ)

/-- The algebra isomorphism between multivariable polynomials in `fin (n + 1)` and
polynomials over multivariable polynomials in `fin n`.
-/
def finSuccEquiv : MvPolynomial (Finₓ (n + 1)) R ≃ₐ[R] Polynomial (MvPolynomial (Finₓ n) R) :=
  (renameEquiv R (finSuccEquiv n)).trans (optionEquivLeft R (Finₓ n))

theorem fin_succ_equiv_eq :
    (finSuccEquiv R n : MvPolynomial (Finₓ (n + 1)) R →+* Polynomial (MvPolynomial (Finₓ n) R)) =
      eval₂Hom (Polynomial.c.comp (c : R →+* MvPolynomial (Finₓ n) R)) fun i : Finₓ (n + 1) =>
        Finₓ.cases Polynomial.x (fun k => Polynomial.c (x k)) i :=
  by
  ext : 2
  · simp only [← finSuccEquiv, ← option_equiv_left_apply, ← aeval_C, ← AlgEquiv.coe_trans, ← RingHom.coe_coe, ←
      coe_eval₂_hom, ← comp_app, ← rename_equiv_apply, ← eval₂_C, ← RingHom.coe_comp, ← rename_C]
    rfl
    
  · intro i
    refine' Finₓ.cases _ _ i <;> simp [← finSuccEquiv]
    

@[simp]
theorem fin_succ_equiv_apply (p : MvPolynomial (Finₓ (n + 1)) R) :
    finSuccEquiv R n p =
      eval₂Hom (Polynomial.c.comp (c : R →+* MvPolynomial (Finₓ n) R))
        (fun i : Finₓ (n + 1) => Finₓ.cases Polynomial.x (fun k => Polynomial.c (x k)) i) p :=
  by
  rw [← fin_succ_equiv_eq]
  rfl

theorem fin_succ_equiv_comp_C_eq_C {R : Type u} [CommSemiringₓ R] (n : ℕ) :
    (↑(MvPolynomial.finSuccEquiv R n).symm : Polynomial (MvPolynomial (Finₓ n) R) →+* _).comp
        (Polynomial.c.comp MvPolynomial.c) =
      (MvPolynomial.c : R →+* MvPolynomial (Finₓ n.succ) R) :=
  by
  refine' RingHom.ext fun x => _
  rw [RingHom.comp_apply]
  refine' (MvPolynomial.finSuccEquiv R n).Injective (trans ((MvPolynomial.finSuccEquiv R n).apply_symm_apply _) _)
  simp only [← MvPolynomial.fin_succ_equiv_apply, ← MvPolynomial.eval₂_hom_C]

variable {n} {R}

theorem fin_succ_equiv_X_zero : finSuccEquiv R n (x 0) = Polynomial.x := by
  simp

theorem fin_succ_equiv_X_succ {j : Finₓ n} : finSuccEquiv R n (x j.succ) = Polynomial.c (x j) := by
  simp

/-- The coefficient of `m` in the `i`-th coefficient of `fin_succ_equiv R n f` equals the
    coefficient of `finsupp.cons i m` in `f`. -/
theorem fin_succ_equiv_coeff_coeff (m : Finₓ n →₀ ℕ) (f : MvPolynomial (Finₓ (n + 1)) R) (i : ℕ) :
    coeff m (Polynomial.coeff (finSuccEquiv R n f) i) = coeff (m.cons i) f := by
  induction' f using MvPolynomial.induction_on' with j r p q hp hq generalizing i m
  swap
  · simp only [← (finSuccEquiv R n).map_add, ← Polynomial.coeff_add, ← coeff_add, ← hp, ← hq]
    
  simp only [← fin_succ_equiv_apply, ← coe_eval₂_hom, ← eval₂_monomial, ← RingHom.coe_comp, ← prod_pow, ←
    Polynomial.coeff_C_mul, ← coeff_C_mul, ← coeff_monomial, ← Finₓ.prod_univ_succ, ← Finₓ.cases_zero, ←
    Finₓ.cases_succ, RingHom.map_prod, RingHom.map_pow]
  rw [← mul_boole, mul_comm (Polynomial.x ^ j 0), Polynomial.coeff_C_mul_X_pow]
  congr 1
  obtain rfl | hjmi := eq_or_ne j (m.cons i)
  · simpa only [← cons_zero, ← cons_succ, ← if_pos rfl, ← monomial_eq, ← C_1, ← one_mulₓ, ← prod_pow] using
      coeff_monomial m m (1 : R)
    
  · simp only [← hjmi, ← if_false]
    obtain hij | rfl := ne_or_eq i (j 0)
    · simp only [← hij, ← if_false, ← coeff_zero]
      
    simp only [← eq_self_iff_true, ← if_true]
    have hmj : m ≠ j.tail := by
      rintro rfl
      rw [cons_tail] at hjmi
      contradiction
    simpa only [← monomial_eq, ← C_1, ← one_mulₓ, ← prod_pow, ← Finsupp.tail_apply, ← if_neg hmj.symm] using
      coeff_monomial m j.tail (1 : R)
    

theorem eval_eq_eval_mv_eval' (s : Finₓ n → R) (y : R) (f : MvPolynomial (Finₓ (n + 1)) R) :
    eval (Finₓ.cons y s : Finₓ (n + 1) → R) f = Polynomial.eval y (Polynomial.map (eval s) (finSuccEquiv R n f)) := by
  -- turn this into a def `polynomial.map_alg_hom`
  let φ : (MvPolynomial (Finₓ n) R)[X] →ₐ[R] R[X] :=
    { Polynomial.mapRingHom (eval s) with
      commutes' := fun r => by
        convert Polynomial.map_C _
        exact (eval_C _).symm }
  show aeval (Finₓ.cons y s : Finₓ (n + 1) → R) f = (Polynomial.aeval y).comp (φ.comp (finSuccEquiv R n).toAlgHom) f
  congr 2
  apply MvPolynomial.alg_hom_ext
  rw [Finₓ.forall_fin_succ]
  simp only [← aeval_X, ← Finₓ.cons_zero, ← AlgEquiv.to_alg_hom_eq_coe, ← AlgHom.coe_comp, ←
    Polynomial.coe_aeval_eq_eval, ← Polynomial.map_C, ← AlgHom.coe_mk, ← RingHom.to_fun_eq_coe, ←
    Polynomial.coe_map_ring_hom, ← AlgEquiv.coe_alg_hom, ← comp_app, ← fin_succ_equiv_apply, ← eval₂_hom_X', ←
    Finₓ.cases_zero, ← Polynomial.map_X, ← Polynomial.eval_X, ← eq_self_iff_true, ← Finₓ.cons_succ, ← Finₓ.cases_succ, ←
    eval_X, ← Polynomial.eval_C, ← implies_true_iff, ← and_selfₓ]

theorem coeff_eval_eq_eval_coeff (s' : Finₓ n → R) (f : Polynomial (MvPolynomial (Finₓ n) R)) (i : ℕ) :
    Polynomial.coeff (Polynomial.map (eval s') f) i = eval s' (Polynomial.coeff f i) := by
  simp only [← Polynomial.coeff_map]

theorem support_coeff_fin_succ_equiv {f : MvPolynomial (Finₓ (n + 1)) R} {i : ℕ} {m : Finₓ n →₀ ℕ} :
    m ∈ (Polynomial.coeff ((finSuccEquiv R n) f) i).support ↔ Finsupp.cons i m ∈ f.support := by
  apply Iff.intro
  · intro h
    simpa [fin_succ_equiv_coeff_coeff] using h
    
  · intro h
    simpa [← mem_support_iff, fin_succ_equiv_coeff_coeff m f i] using h
    

theorem fin_succ_equiv_support (f : MvPolynomial (Finₓ (n + 1)) R) :
    (finSuccEquiv R n f).support = Finset.image (fun m : Finₓ (n + 1) →₀ ℕ => m 0) f.support := by
  ext i
  rw [Polynomial.mem_support_iff, Finset.mem_image, nonzero_iff_exists]
  constructor
  · rintro ⟨m, hm⟩
    refine' ⟨cons i m, _, cons_zero _ _⟩
    rw [← support_coeff_fin_succ_equiv]
    simpa using hm
    
  · rintro ⟨m, h, rfl⟩
    refine' ⟨tail m, _⟩
    rwa [← coeff, ← mem_support_iff, support_coeff_fin_succ_equiv, cons_tail]
    

theorem fin_succ_equiv_support' {f : MvPolynomial (Finₓ (n + 1)) R} {i : ℕ} :
    Finset.image (Finsupp.cons i) (Polynomial.coeff ((finSuccEquiv R n) f) i).support =
      f.support.filter fun m => m 0 = i :=
  by
  ext m
  rw [Finset.mem_filter, Finset.mem_image, mem_support_iff]
  conv_lhs => congr ext rw [mem_support_iff, fin_succ_equiv_coeff_coeff, Ne.def]
  constructor
  · rintro ⟨m', ⟨h, hm'⟩⟩
    simp only [hm']
    exact
      ⟨h, by
        rw [cons_zero]⟩
    
  · intro h
    use tail m
    rw [← h.2, cons_tail]
    simp [← h.1]
    

theorem support_fin_succ_equiv_nonempty {f : MvPolynomial (Finₓ (n + 1)) R} (h : f ≠ 0) :
    (finSuccEquiv R n f).support.Nonempty := by
  by_contra c
  simp only [← Finset.not_nonempty_iff_eq_empty, ← Polynomial.support_eq_empty] at c
  have t'' : finSuccEquiv R n f ≠ 0 := by
    let ii := (finSuccEquiv R n).symm
    have h' : f = 0 :=
      calc
        f = ii (finSuccEquiv R n f) := by
          simpa only [← ii, AlgEquiv.inv_fun_eq_symm] using ((finSuccEquiv R n).left_inv f).symm
        _ = ii 0 := by
          rw [c]
        _ = 0 := by
          simp
        
    simpa [← h'] using h
  simpa [← c] using h

theorem degree_fin_succ_equiv {f : MvPolynomial (Finₓ (n + 1)) R} (h : f ≠ 0) :
    (finSuccEquiv R n f).degree = degreeOf 0 f := by
  have h' : ((finSuccEquiv R n f).support.sup fun x => x) = degree_of 0 f := by
    rw [degree_of_eq_sup, fin_succ_equiv_support f, Finset.sup_image]
  rw [Polynomial.degree, ← h', Finset.coe_sup_of_nonempty (support_fin_succ_equiv_nonempty h)]

theorem nat_degree_fin_succ_equiv (f : MvPolynomial (Finₓ (n + 1)) R) : (finSuccEquiv R n f).natDegree = degreeOf 0 f :=
  by
  by_cases' c : f = 0
  · rw [c, (finSuccEquiv R n).map_zero, Polynomial.nat_degree_zero, degree_of_zero]
    
  · rw [Polynomial.natDegree,
      degree_fin_succ_equiv
        (by
          simpa only [← Ne.def] )]
    simp
    

theorem degree_of_coeff_fin_succ_equiv (p : MvPolynomial (Finₓ (n + 1)) R) (j : Finₓ n) (i : ℕ) :
    degreeOf j (Polynomial.coeff (finSuccEquiv R n p) i) ≤ degreeOf j.succ p := by
  rw [degree_of_eq_sup, degree_of_eq_sup, Finset.sup_le_iff]
  intro m hm
  rw [← Finsupp.cons_succ j i m]
  convert Finset.le_sup (support_coeff_fin_succ_equiv.1 hm)
  rfl

end

end Equivₓ

end MvPolynomial

