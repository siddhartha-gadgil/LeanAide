/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathbin.LinearAlgebra.CliffordAlgebra.Fold
import Mathbin.LinearAlgebra.ExteriorAlgebra.Basic

/-!
# Extending an alternating map to the exterior algebra

## Main definitions

* `exterior_algebra.lift_alternating`: construct a linear map out of the exterior algebra
  given alternating maps (corresponding to maps out of the exterior powers).
* `exterior_algebra.lift_alternating_equiv`: the above as a linear equivalence

## Main results

* `exterior_algebra.lhom_ext`: linear maps from the exterior algebra agree if they agree on the
  exterior powers.

-/


variable {R M N N' : Type _}

variable [CommRingₓ R] [AddCommGroupₓ M] [AddCommGroupₓ N] [AddCommGroupₓ N']

variable [Module R M] [Module R N] [Module R N']

-- This instance can't be found where it's needed if we don't remind lean that it exists.
instance AlternatingMap.moduleAddCommGroup {ι : Type _} [DecidableEq ι] : Module R (AlternatingMap R M N ι) := by
  infer_instance

namespace ExteriorAlgebra

open CliffordAlgebra hiding ι

/-- Build a map out of the exterior algebra given a collection of alternating maps acting on each
exterior power -/
def liftAlternating : (∀ i, AlternatingMap R M N (Finₓ i)) →ₗ[R] ExteriorAlgebra R M →ₗ[R] N := by
  suffices (∀ i, AlternatingMap R M N (Finₓ i)) →ₗ[R] ExteriorAlgebra R M →ₗ[R] ∀ i, AlternatingMap R M N (Finₓ i) by
    refine' LinearMap.compr₂ this _
    refine' LinearEquiv.toLinearMap _ ∘ₗ LinearMap.proj 0
    exact alternating_map.const_linear_equiv_of_is_empty.symm
  refine' CliffordAlgebra.foldl _ _ _
  · refine'
      LinearMap.mk₂ R (fun m f i => (f i.succ).curryLeft m) (fun m₁ m₂ f => _) (fun c m f => _) (fun m f₁ f₂ => _)
        fun c m f => _
    all_goals
      ext i : 1
      simp only [← map_smul, ← map_add, ← Pi.add_apply, ← Pi.smul_apply, ← AlternatingMap.curry_left_add, ←
        AlternatingMap.curry_left_smul, ← map_add, ← map_smul, ← LinearMap.add_apply, ← LinearMap.smul_apply]
    
  · -- when applied twice with the same `m`, this recursive step produces 0
    intro m x
    dsimp' only [← LinearMap.mk₂_apply, ← QuadraticForm.coe_fn_zero, ← Pi.zero_apply]
    simp_rw [zero_smul]
    ext i : 1
    exact AlternatingMap.curry_left_same _ _
    

@[simp]
theorem lift_alternating_ι (f : ∀ i, AlternatingMap R M N (Finₓ i)) (m : M) : liftAlternating f (ι R m) = f 1 ![m] := by
  dsimp' [← lift_alternating]
  rw [foldl_ι, LinearMap.mk₂_apply, AlternatingMap.curry_left_apply_apply]
  congr

theorem lift_alternating_ι_mul (f : ∀ i, AlternatingMap R M N (Finₓ i)) (m : M) (x : ExteriorAlgebra R M) :
    liftAlternating f (ι R m * x) = liftAlternating (fun i => (f i.succ).curryLeft m) x := by
  dsimp' [← lift_alternating]
  rw [foldl_mul, foldl_ι]
  rfl

@[simp]
theorem lift_alternating_one (f : ∀ i, AlternatingMap R M N (Finₓ i)) :
    liftAlternating f (1 : ExteriorAlgebra R M) = f 0 0 := by
  dsimp' [← lift_alternating]
  rw [foldl_one]

@[simp]
theorem lift_alternating_algebra_map (f : ∀ i, AlternatingMap R M N (Finₓ i)) (r : R) :
    liftAlternating f (algebraMap _ (ExteriorAlgebra R M) r) = r • f 0 0 := by
  rw [Algebra.algebra_map_eq_smul_one, map_smul, lift_alternating_one]

@[simp]
theorem lift_alternating_apply_ι_multi {n : ℕ} (f : ∀ i, AlternatingMap R M N (Finₓ i)) (v : Finₓ n → M) :
    liftAlternating f (ιMulti R n v) = f n v := by
  rw [ι_multi_apply]
  induction' n with n ih generalizing f v
  · rw [List.of_fn_zero, List.prod_nil, lift_alternating_one, Subsingleton.elimₓ 0 v]
    
  · rw [List.of_fn_succ, List.prod_cons, lift_alternating_ι_mul, ih, AlternatingMap.curry_left_apply_apply]
    congr
    exact Matrix.cons_head_tail _
    

@[simp]
theorem lift_alternating_comp_ι_multi {n : ℕ} (f : ∀ i, AlternatingMap R M N (Finₓ i)) :
    (liftAlternating f).compAlternatingMap (ιMulti R n) = f n :=
  AlternatingMap.ext <| lift_alternating_apply_ι_multi f

@[simp]
theorem lift_alternating_comp (g : N →ₗ[R] N') (f : ∀ i, AlternatingMap R M N (Finₓ i)) :
    (liftAlternating fun i => g.compAlternatingMap (f i)) = g ∘ₗ liftAlternating f := by
  ext v
  rw [LinearMap.comp_apply]
  induction' v using CliffordAlgebra.left_induction with r x y hx hy x m hx generalizing f
  · rw [lift_alternating_algebra_map, lift_alternating_algebra_map, map_smul, LinearMap.comp_alternating_map_apply]
    
  · rw [map_add, map_add, map_add, hx, hy]
    
  · rw [lift_alternating_ι_mul, lift_alternating_ι_mul, ← hx]
    simp_rw [AlternatingMap.curry_left_comp_alternating_map]
    

@[simp]
theorem lift_alternating_ι_multi :
    liftAlternating (ι_multi R) = (LinearMap.id : ExteriorAlgebra R M →ₗ[R] ExteriorAlgebra R M) := by
  ext v
  dsimp'
  induction' v using CliffordAlgebra.left_induction with r x y hx hy x m hx
  · rw [lift_alternating_algebra_map, ι_multi_zero_apply, Algebra.algebra_map_eq_smul_one]
    
  · rw [map_add, hx, hy]
    
  · simp_rw [lift_alternating_ι_mul, ι_multi_succ_curry_left, lift_alternating_comp, LinearMap.comp_apply,
      Algebra.lmul_left_apply, hx]
    

/-- `exterior_algebra.lift_alternating` is an equivalence. -/
@[simps apply symmApply]
def liftAlternatingEquiv : (∀ i, AlternatingMap R M N (Finₓ i)) ≃ₗ[R] ExteriorAlgebra R M →ₗ[R] N where
  toFun := liftAlternating
  map_add' := map_add _
  map_smul' := map_smul _
  invFun := fun F i => F.compAlternatingMap (ιMulti R i)
  left_inv := fun f => funext fun i => lift_alternating_comp_ι_multi _
  right_inv := fun F =>
    (lift_alternating_comp _ _).trans <| by
      rw [lift_alternating_ι_multi, LinearMap.comp_id]

/-- To show that two linear maps from the exterior algebra agree, it suffices to show they agree on
the exterior powers.

See note [partially-applied ext lemmas] -/
@[ext]
theorem lhom_ext ⦃f g : ExteriorAlgebra R M →ₗ[R] N⦄
    (h : ∀ i, f.compAlternatingMap (ιMulti R i) = g.compAlternatingMap (ιMulti R i)) : f = g :=
  liftAlternatingEquiv.symm.Injective <| funext h

end ExteriorAlgebra

