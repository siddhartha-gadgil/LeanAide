/-
Copyright (c) 2021 Eric Weiser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathbin.Algebra.Algebra.Operations
import Mathbin.Algebra.Algebra.Subalgebra.Basic
import Mathbin.RingTheory.Subring.Pointwise
import Mathbin.RingTheory.Adjoin.Basic

/-!
# Pointwise actions on subalgebras.

If `R'` acts on an `R`-algebra `A` (so that `R'` and `R` actions commute)
then we get an `R'` action on the collection of `R`-subalgebras.
-/


namespace Subalgebra

section Pointwise

variable {R : Type _} {A : Type _} [CommSemiringₓ R] [Semiringₓ A] [Algebra R A]

theorem mul_to_submodule_le (S T : Subalgebra R A) : S.toSubmodule * T.toSubmodule ≤ (S⊔T).toSubmodule := by
  rw [Submodule.mul_le]
  intro y hy z hz
  show y * z ∈ S⊔T
  exact mul_mem (Algebra.mem_sup_left hy) (Algebra.mem_sup_right hz)

/-- As submodules, subalgebras are idempotent. -/
@[simp]
theorem mul_self (S : Subalgebra R A) : S.toSubmodule * S.toSubmodule = S.toSubmodule := by
  apply le_antisymmₓ
  · refine' (mul_to_submodule_le _ _).trans_eq _
    rw [sup_idem]
    
  · intro x hx1
    rw [← mul_oneₓ x]
    exact Submodule.mul_mem_mul hx1 (show (1 : A) ∈ S from one_mem S)
    

/-- When `A` is commutative, `subalgebra.mul_to_submodule_le` is strict. -/
theorem mul_to_submodule {R : Type _} {A : Type _} [CommSemiringₓ R] [CommSemiringₓ A] [Algebra R A]
    (S T : Subalgebra R A) : S.toSubmodule * T.toSubmodule = (S⊔T).toSubmodule := by
  refine' le_antisymmₓ (mul_to_submodule_le _ _) _
  rintro x (hx : x ∈ Algebra.adjoin R (S ∪ T : Set A))
  refine' Algebra.adjoin_induction hx (fun x hx => _) (fun r => _) (fun _ _ => Submodule.add_mem _) fun x y hx hy => _
  · cases' hx with hxS hxT
    · rw [← mul_oneₓ x]
      exact Submodule.mul_mem_mul hxS (show (1 : A) ∈ T from one_mem T)
      
    · rw [← one_mulₓ x]
      exact Submodule.mul_mem_mul (show (1 : A) ∈ S from one_mem S) hxT
      
    
  · rw [← one_mulₓ (algebraMap _ _ _)]
    exact Submodule.mul_mem_mul (show (1 : A) ∈ S from one_mem S) (algebra_map_mem _ _)
    
  have := Submodule.mul_mem_mul hx hy
  rwa [mul_assoc, mul_comm _ T.to_submodule, ← mul_assoc _ _ S.to_submodule, mul_self, mul_comm T.to_submodule, ←
    mul_assoc, mul_self] at this

variable {R' : Type _} [Semiringₓ R'] [MulSemiringAction R' A] [SmulCommClass R' R A]

/-- The action on a subalgebra corresponding to applying the action to every element.

This is available as an instance in the `pointwise` locale. -/
protected def pointwiseMulAction : MulAction R' (Subalgebra R A) where
  smul := fun a S => S.map (MulSemiringAction.toAlgHom _ _ a)
  one_smul := fun S => (congr_arg (fun f => S.map f) (AlgHom.ext <| one_smul R')).trans S.map_id
  mul_smul := fun a₁ a₂ S => (congr_arg (fun f => S.map f) (AlgHom.ext <| mul_smul _ _)).trans (S.map_map _ _).symm

localized [Pointwise] attribute [instance] Subalgebra.pointwiseMulAction

open Pointwise

@[simp]
theorem coe_pointwise_smul (m : R') (S : Subalgebra R A) : ↑(m • S) = m • (S : Set A) :=
  rfl

@[simp]
theorem pointwise_smul_to_subsemiring (m : R') (S : Subalgebra R A) : (m • S).toSubsemiring = m • S.toSubsemiring :=
  rfl

@[simp]
theorem pointwise_smul_to_submodule (m : R') (S : Subalgebra R A) : (m • S).toSubmodule = m • S.toSubmodule :=
  rfl

@[simp]
theorem pointwise_smul_to_subring {R' R A : Type _} [Semiringₓ R'] [CommRingₓ R] [Ringₓ A] [MulSemiringAction R' A]
    [Algebra R A] [SmulCommClass R' R A] (m : R') (S : Subalgebra R A) : (m • S).toSubring = m • S.toSubring :=
  rfl

theorem smul_mem_pointwise_smul (m : R') (r : A) (S : Subalgebra R A) : r ∈ S → m • r ∈ m • S :=
  (Set.smul_mem_smul_set : _ → _ ∈ m • (S : Set A))

end Pointwise

end Subalgebra

