/-
Copyright (c) 2020 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhangir Azerbayev, Adam Topaz, Eric Wieser
-/
import Mathbin.Algebra.RingQuot
import Mathbin.LinearAlgebra.CliffordAlgebra.Basic
import Mathbin.LinearAlgebra.Alternating
import Mathbin.GroupTheory.Perm.Sign

/-!
# Exterior Algebras

We construct the exterior algebra of a module `M` over a commutative semiring `R`.

## Notation

The exterior algebra of the `R`-module `M` is denoted as `exterior_algebra R M`.
It is endowed with the structure of an `R`-algebra.

Given a linear morphism `f : M → A` from a module `M` to another `R`-algebra `A`, such that
`cond : ∀ m : M, f m * f m = 0`, there is a (unique) lift of `f` to an `R`-algebra morphism,
which is denoted `exterior_algebra.lift R f cond`.

The canonical linear map `M → exterior_algebra R M` is denoted `exterior_algebra.ι R`.

## Theorems

The main theorems proved ensure that `exterior_algebra R M` satisfies the universal property
of the exterior algebra.
1. `ι_comp_lift` is  fact that the composition of `ι R` with `lift R f cond` agrees with `f`.
2. `lift_unique` ensures the uniqueness of `lift R f cond` with respect to 1.

## Definitions

* `ι_multi` is the `alternating_map` corresponding to the wedge product of `ι R m` terms.

## Implementation details

The exterior algebra of `M` is constructed as simply `clifford_algebra (0 : quadratic_form R M)`,
as this avoids us having to duplicate API.
-/


universe u1 u2 u3

variable (R : Type u1) [CommRingₓ R]

variable (M : Type u2) [AddCommGroupₓ M] [Module R M]

/-- The exterior algebra of an `R`-module `M`.
-/
@[reducible]
def ExteriorAlgebra :=
  CliffordAlgebra (0 : QuadraticForm R M)

namespace ExteriorAlgebra

variable {M}

/-- The canonical linear map `M →ₗ[R] exterior_algebra R M`.
-/
@[reducible]
def ι : M →ₗ[R] ExteriorAlgebra R M :=
  CliffordAlgebra.ι _

variable {R}

/-- As well as being linear, `ι m` squares to zero -/
@[simp]
theorem ι_sq_zero (m : M) : ι R m * ι R m = 0 :=
  (CliffordAlgebra.ι_sq_scalar _ m).trans <| map_zero _

variable {A : Type _} [Semiringₓ A] [Algebra R A]

@[simp]
theorem comp_ι_sq_zero (g : ExteriorAlgebra R M →ₐ[R] A) (m : M) : g (ι R m) * g (ι R m) = 0 := by
  rw [← AlgHom.map_mul, ι_sq_zero, AlgHom.map_zero]

variable (R)

/-- Given a linear map `f : M →ₗ[R] A` into an `R`-algebra `A`, which satisfies the condition:
`cond : ∀ m : M, f m * f m = 0`, this is the canonical lift of `f` to a morphism of `R`-algebras
from `exterior_algebra R M` to `A`.
-/
@[simps symmApply]
def lift : { f : M →ₗ[R] A // ∀ m, f m * f m = 0 } ≃ (ExteriorAlgebra R M →ₐ[R] A) :=
  Equivₓ.trans
      (Equivₓ.subtypeEquiv (Equivₓ.refl _) <| by
        simp ) <|
    CliffordAlgebra.lift _

@[simp]
theorem ι_comp_lift (f : M →ₗ[R] A) (cond : ∀ m, f m * f m = 0) : (lift R ⟨f, cond⟩).toLinearMap.comp (ι R) = f :=
  CliffordAlgebra.ι_comp_lift f _

@[simp]
theorem lift_ι_apply (f : M →ₗ[R] A) (cond : ∀ m, f m * f m = 0) (x) : lift R ⟨f, cond⟩ (ι R x) = f x :=
  CliffordAlgebra.lift_ι_apply f _ x

@[simp]
theorem lift_unique (f : M →ₗ[R] A) (cond : ∀ m, f m * f m = 0) (g : ExteriorAlgebra R M →ₐ[R] A) :
    g.toLinearMap.comp (ι R) = f ↔ g = lift R ⟨f, cond⟩ :=
  CliffordAlgebra.lift_unique f _ _

variable {R M}

@[simp]
theorem lift_comp_ι (g : ExteriorAlgebra R M →ₐ[R] A) : lift R ⟨g.toLinearMap.comp (ι R), comp_ι_sq_zero _⟩ = g :=
  CliffordAlgebra.lift_comp_ι g

/-- See note [partially-applied ext lemmas]. -/
@[ext]
theorem hom_ext {f g : ExteriorAlgebra R M →ₐ[R] A} (h : f.toLinearMap.comp (ι R) = g.toLinearMap.comp (ι R)) : f = g :=
  CliffordAlgebra.hom_ext h

/-- If `C` holds for the `algebra_map` of `r : R` into `exterior_algebra R M`, the `ι` of `x : M`,
and is preserved under addition and muliplication, then it holds for all of `exterior_algebra R M`.
-/
@[elab_as_eliminator]
theorem induction {C : ExteriorAlgebra R M → Prop} (h_grade0 : ∀ r, C (algebraMap R (ExteriorAlgebra R M) r))
    (h_grade1 : ∀ x, C (ι R x)) (h_mul : ∀ a b, C a → C b → C (a * b)) (h_add : ∀ a b, C a → C b → C (a + b))
    (a : ExteriorAlgebra R M) : C a :=
  CliffordAlgebra.induction h_grade0 h_grade1 h_mul h_add a

/-- The left-inverse of `algebra_map`. -/
def algebraMapInv : ExteriorAlgebra R M →ₐ[R] R :=
  ExteriorAlgebra.lift R
    ⟨(0 : M →ₗ[R] R), fun m => by
      simp ⟩

variable (M)

theorem algebra_map_left_inverse : Function.LeftInverse algebraMapInv (algebraMap R <| ExteriorAlgebra R M) := fun x =>
  by
  simp [← algebra_map_inv]

@[simp]
theorem algebra_map_inj (x y : R) :
    algebraMap R (ExteriorAlgebra R M) x = algebraMap R (ExteriorAlgebra R M) y ↔ x = y :=
  (algebra_map_left_inverse M).Injective.eq_iff

@[simp]
theorem algebra_map_eq_zero_iff (x : R) : algebraMap R (ExteriorAlgebra R M) x = 0 ↔ x = 0 :=
  map_eq_zero_iff (algebraMap _ _) (algebra_map_left_inverse _).Injective

@[simp]
theorem algebra_map_eq_one_iff (x : R) : algebraMap R (ExteriorAlgebra R M) x = 1 ↔ x = 1 :=
  map_eq_one_iff (algebraMap _ _) (algebra_map_left_inverse _).Injective

variable {M}

/-- The canonical map from `exterior_algebra R M` into `triv_sq_zero_ext R M` that sends
`exterior_algebra.ι` to `triv_sq_zero_ext.inr`. -/
def toTrivSqZeroExt : ExteriorAlgebra R M →ₐ[R] TrivSqZeroExt R M :=
  lift R ⟨TrivSqZeroExt.inrHom R M, fun m => TrivSqZeroExt.inr_mul_inr R m m⟩

@[simp]
theorem to_triv_sq_zero_ext_ι (x : M) : toTrivSqZeroExt (ι R x) = TrivSqZeroExt.inr x :=
  lift_ι_apply _ _ _ _

/-- The left-inverse of `ι`.

As an implementation detail, we implement this using `triv_sq_zero_ext` which has a suitable
algebra structure. -/
def ιInv : ExteriorAlgebra R M →ₗ[R] M :=
  (TrivSqZeroExt.sndHom R M).comp toTrivSqZeroExt.toLinearMap

theorem ι_left_inverse : Function.LeftInverse ιInv (ι R : M → ExteriorAlgebra R M) := fun x => by
  simp [← ι_inv]

variable (R)

@[simp]
theorem ι_inj (x y : M) : ι R x = ι R y ↔ x = y :=
  ι_left_inverse.Injective.eq_iff

variable {R}

@[simp]
theorem ι_eq_zero_iff (x : M) : ι R x = 0 ↔ x = 0 := by
  rw [← ι_inj R x 0, LinearMap.map_zero]

@[simp]
theorem ι_eq_algebra_map_iff (x : M) (r : R) : ι R x = algebraMap R _ r ↔ x = 0 ∧ r = 0 := by
  refine' ⟨fun h => _, _⟩
  · have hf0 : to_triv_sq_zero_ext (ι R x) = (0, x) := to_triv_sq_zero_ext_ι _
    rw [h, AlgHom.commutes] at hf0
    have : r = 0 ∧ 0 = x := Prod.ext_iff.1 hf0
    exact this.symm.imp_left Eq.symm
    
  · rintro ⟨rfl, rfl⟩
    rw [LinearMap.map_zero, RingHom.map_zero]
    

@[simp]
theorem ι_ne_one [Nontrivial R] (x : M) : ι R x ≠ 1 := by
  rw [← (algebraMap R (ExteriorAlgebra R M)).map_one, Ne.def, ι_eq_algebra_map_iff]
  exact one_ne_zero ∘ And.right

/-- The generators of the exterior algebra are disjoint from its scalars. -/
theorem ι_range_disjoint_one : Disjoint (ι R).range (1 : Submodule R (ExteriorAlgebra R M)) := by
  rw [Submodule.disjoint_def]
  rintro _ ⟨x, hx⟩ ⟨r, rfl : algebraMap _ _ _ = _⟩
  rw [ι_eq_algebra_map_iff x] at hx
  rw [hx.2, RingHom.map_zero]

@[simp]
theorem ι_add_mul_swap (x y : M) : ι R x * ι R y + ι R y * ι R x = 0 :=
  calc
    _ = ι R (x + y) * ι R (x + y) := by
      simp [← mul_addₓ, ← add_mulₓ]
    _ = _ := ι_sq_zero _
    

theorem ι_mul_prod_list {n : ℕ} (f : Finₓ n → M) (i : Finₓ n) :
    (ι R <| f i) * (List.ofFnₓ fun i => ι R <| f i).Prod = 0 := by
  induction' n with n hn
  · exact i.elim0
    
  · rw [List.of_fn_succ, List.prod_cons, ← mul_assoc]
    by_cases' h : i = 0
    · rw [h, ι_sq_zero, zero_mul]
      
    · replace hn := congr_arg ((· * ·) <| ι R <| f 0) (hn (fun i => f <| Finₓ.succ i) (i.pred h))
      simp only at hn
      rw [Finₓ.succ_pred, ← mul_assoc, mul_zero] at hn
      refine' (eq_zero_iff_eq_zero_of_add_eq_zero _).mp hn
      rw [← add_mulₓ, ι_add_mul_swap, zero_mul]
      
    

variable (R)

/-- The product of `n` terms of the form `ι R m` is an alternating map.

This is a special case of `multilinear_map.mk_pi_algebra_fin`, and the exterior algebra version of
`tensor_algebra.tprod`. -/
def ιMulti (n : ℕ) : AlternatingMap R M (ExteriorAlgebra R M) (Finₓ n) :=
  let F := (MultilinearMap.mkPiAlgebraFin R n (ExteriorAlgebra R M)).compLinearMap fun i => ι R
  { -- one of the repeated terms is on the left
    -- ignore the left-most term and induct on the remaining ones, decrementing indices
    F with
    map_eq_zero_of_eq' := fun f x y hfxy hxy => by
      rw [MultilinearMap.comp_linear_map_apply, MultilinearMap.mk_pi_algebra_fin_apply]
      wlog h : x < y := lt_or_gt_of_neₓ hxy using x y
      clear hxy
      induction' n with n hn generalizing x y
      · exact x.elim0
        
      · rw [List.of_fn_succ, List.prod_cons]
        by_cases' hx : x = 0
        · rw [hx] at hfxy h
          rw [hfxy, ← Finₓ.succ_pred y (ne_of_ltₓ h).symm]
          exact ι_mul_prod_list (f ∘ Finₓ.succ) _
          
        · convert mul_zero _
          refine'
            hn (fun i => f <| Finₓ.succ i) (x.pred hx) (y.pred (ne_of_ltₓ <| lt_of_le_of_ltₓ x.zero_le h).symm)
              (fin.pred_lt_pred_iff.mpr h) _
          simp only [← Finₓ.succ_pred]
          exact hfxy
          
        ,
    toFun := F }

variable {R}

theorem ι_multi_apply {n : ℕ} (v : Finₓ n → M) : ιMulti R n v = (List.ofFnₓ fun i => ι R (v i)).Prod :=
  rfl

@[simp]
theorem ι_multi_zero_apply (v : Finₓ 0 → M) : ιMulti R 0 v = 1 :=
  rfl

@[simp]
theorem ι_multi_succ_apply {n : ℕ} (v : Finₓ n.succ → M) : ιMulti R _ v = ι R (v 0) * ιMulti R _ (Matrix.vecTail v) :=
  (congr_arg List.prod (List.of_fn_succ _)).trans List.prod_cons

theorem ι_multi_succ_curry_left {n : ℕ} (m : M) :
    (ιMulti R n.succ).curryLeft m = (Algebra.lmulLeft R (ι R m)).compAlternatingMap (ιMulti R n) :=
  AlternatingMap.ext fun v =>
    (ι_multi_succ_apply _).trans <| by
      simp_rw [Matrix.tail_cons]
      rfl

end ExteriorAlgebra

namespace TensorAlgebra

variable {R M}

/-- The canonical image of the `tensor_algebra` in the `exterior_algebra`, which maps
`tensor_algebra.ι R x` to `exterior_algebra.ι R x`. -/
def toExterior : TensorAlgebra R M →ₐ[R] ExteriorAlgebra R M :=
  TensorAlgebra.lift R (ExteriorAlgebra.ι R : M →ₗ[R] ExteriorAlgebra R M)

@[simp]
theorem to_exterior_ι (m : M) : (TensorAlgebra.ι R m).toExterior = ExteriorAlgebra.ι R m := by
  simp [← to_exterior]

end TensorAlgebra

