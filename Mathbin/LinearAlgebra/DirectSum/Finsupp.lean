/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathbin.Algebra.DirectSum.Finsupp
import Mathbin.LinearAlgebra.Finsupp
import Mathbin.LinearAlgebra.DirectSum.TensorProduct
import Mathbin.Data.Finsupp.ToDfinsupp

/-!
# Results on finitely supported functions.

The tensor product of ι →₀ M and κ →₀ N is linearly equivalent to (ι × κ) →₀ (M ⊗ N).
-/


universe u v w

noncomputable section

open DirectSum

open Set LinearMap Submodule

variable {R : Type u} {M : Type v} {N : Type w} [Ringₓ R] [AddCommGroupₓ M] [Module R M] [AddCommGroupₓ N] [Module R N]

section TensorProduct

open TensorProduct

open TensorProduct Classical

/-- The tensor product of ι →₀ M and κ →₀ N is linearly equivalent to (ι × κ) →₀ (M ⊗ N). -/
def finsuppTensorFinsupp (R M N ι κ : Sort _) [CommRingₓ R] [AddCommGroupₓ M] [Module R M] [AddCommGroupₓ N]
    [Module R N] : (ι →₀ M) ⊗[R] (κ →₀ N) ≃ₗ[R] ι × κ →₀ M ⊗[R] N :=
  TensorProduct.congr (finsuppLequivDirectSum R M ι) (finsuppLequivDirectSum R N κ) ≪≫ₗ
    ((TensorProduct.directSum R ι κ (fun _ => M) fun _ => N) ≪≫ₗ (finsuppLequivDirectSum R (M ⊗[R] N) (ι × κ)).symm)

@[simp]
theorem finsupp_tensor_finsupp_single (R M N ι κ : Sort _) [CommRingₓ R] [AddCommGroupₓ M] [Module R M]
    [AddCommGroupₓ N] [Module R N] (i : ι) (m : M) (k : κ) (n : N) :
    finsuppTensorFinsupp R M N ι κ (Finsupp.single i m ⊗ₜ Finsupp.single k n) = Finsupp.single (i, k) (m ⊗ₜ n) := by
  simp [← finsuppTensorFinsupp]

@[simp]
theorem finsupp_tensor_finsupp_apply (R M N ι κ : Sort _) [CommRingₓ R] [AddCommGroupₓ M] [Module R M] [AddCommGroupₓ N]
    [Module R N] (f : ι →₀ M) (g : κ →₀ N) (i : ι) (k : κ) :
    finsuppTensorFinsupp R M N ι κ (f ⊗ₜ g) (i, k) = f i ⊗ₜ g k := by
  apply Finsupp.induction_linear f
  · simp
    
  · intro f₁ f₂ hf₁ hf₂
    simp [← add_tmul, ← hf₁, ← hf₂]
    
  · intro i' m
    apply Finsupp.induction_linear g
    · simp
      
    · intro g₁ g₂ hg₁ hg₂
      simp [← tmul_add, ← hg₁, ← hg₂]
      
    · intro k' n
      simp only [← finsupp_tensor_finsupp_single]
      simp only [← Finsupp.single, ← Finsupp.coe_mk]
      -- split_ifs; finish can close the goal from here
      by_cases' h1 : (i', k') = (i, k)
      · simp only [← Prod.mk.inj_iff] at h1
        simp [← h1]
        
      · simp only [← h1, ← if_false]
        simp only [← Prod.mk.inj_iff, ← not_and_distrib] at h1
        cases h1 <;> simp [← h1]
        
      
    

@[simp]
theorem finsupp_tensor_finsupp_symm_single (R M N ι κ : Sort _) [CommRingₓ R] [AddCommGroupₓ M] [Module R M]
    [AddCommGroupₓ N] [Module R N] (i : ι × κ) (m : M) (n : N) :
    (finsuppTensorFinsupp R M N ι κ).symm (Finsupp.single i (m ⊗ₜ n)) = Finsupp.single i.1 m ⊗ₜ Finsupp.single i.2 n :=
  (Prod.casesOn i) fun i k => (LinearEquiv.symm_apply_eq _).2 (finsupp_tensor_finsupp_single _ _ _ _ _ _ _ _ _).symm

variable (S : Type _) [CommRingₓ S] (α β : Type _)

/-- A variant of `finsupp_tensor_finsupp` where both modules are the ground ring.
-/
def finsuppTensorFinsupp' : (α →₀ S) ⊗[S] (β →₀ S) ≃ₗ[S] α × β →₀ S :=
  (finsuppTensorFinsupp S S S α β).trans (Finsupp.lcongr (Equivₓ.refl _) (TensorProduct.lid S S))

@[simp]
theorem finsupp_tensor_finsupp'_apply_apply (f : α →₀ S) (g : β →₀ S) (a : α) (b : β) :
    finsuppTensorFinsupp' S α β (f ⊗ₜ[S] g) (a, b) = f a * g b := by
  simp [← finsuppTensorFinsupp']

@[simp]
theorem finsupp_tensor_finsupp'_single_tmul_single (a : α) (b : β) (r₁ r₂ : S) :
    finsuppTensorFinsupp' S α β (Finsupp.single a r₁ ⊗ₜ[S] Finsupp.single b r₂) = Finsupp.single (a, b) (r₁ * r₂) := by
  ext ⟨a', b'⟩
  simp [← Finsupp.single, ← ite_and]

end TensorProduct

