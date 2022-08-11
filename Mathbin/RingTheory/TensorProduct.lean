/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Johan Commelin
-/
import Mathbin.LinearAlgebra.TensorProductBasis
import Mathbin.RingTheory.Adjoin.Basic

/-!
# The tensor product of R-algebras

Let `R` be a (semi)ring and `A` an `R`-algebra.
In this file we:

- Define the `A`-module structure on `A ⊗ M`, for an `R`-module `M`.
- Define the `R`-algebra structure on `A ⊗ B`, for another `R`-algebra `B`.
  and provide the structure isomorphisms
  * `R ⊗[R] A ≃ₐ[R] A`
  * `A ⊗[R] R ≃ₐ[R] A`
  * `A ⊗[R] B ≃ₐ[R] B ⊗[R] A`
  * `((A ⊗[R] B) ⊗[R] C) ≃ₐ[R] (A ⊗[R] (B ⊗[R] C))`

## Main declaration

- `linear_map.base_change A f` is the `A`-linear map `A ⊗ f`, for an `R`-linear map `f`.

## Implementation notes

The heterobasic definitions below such as:
 * `tensor_product.algebra_tensor_module.curry`
 * `tensor_product.algebra_tensor_module.uncurry`
 * `tensor_product.algebra_tensor_module.lcurry`
 * `tensor_product.algebra_tensor_module.lift`
 * `tensor_product.algebra_tensor_module.lift.equiv`
 * `tensor_product.algebra_tensor_module.mk`
 * `tensor_product.algebra_tensor_module.assoc`

are just more general versions of the definitions already in `linear_algebra/tensor_product`. We
could thus consider replacing the less general definitions with these ones. If we do this, we
probably should still implement the less general ones as abbreviations to the more general ones with
fewer type arguments.
-/


universe u v₁ v₂ v₃ v₄

open TensorProduct

open TensorProduct

namespace TensorProduct

variable {R A M N P : Type _}

/-!
### The `A`-module structure on `A ⊗[R] M`
-/


open LinearMap

open Algebra (lsmul)

namespace AlgebraTensorModule

section Semiringₓ

variable [CommSemiringₓ R] [Semiringₓ A] [Algebra R A]

variable [AddCommMonoidₓ M] [Module R M] [Module A M] [IsScalarTower R A M]

variable [AddCommMonoidₓ N] [Module R N]

variable [AddCommMonoidₓ P] [Module R P] [Module A P] [IsScalarTower R A P]

theorem smul_eq_lsmul_rtensor (a : A) (x : M ⊗[R] N) : a • x = (lsmul R M a).rtensor N x :=
  rfl

/-- Heterobasic version of `tensor_product.curry`:

Given a linear map `M ⊗[R] N →[A] P`, compose it with the canonical
bilinear map `M →[A] N →[R] M ⊗[R] N` to form a bilinear map `M →[A] N →[R] P`. -/
@[simps]
def curry (f : M ⊗[R] N →ₗ[A] P) : M →ₗ[A] N →ₗ[R] P :=
  { curry (f.restrictScalars R) with map_smul' := fun c x => LinearMap.ext fun y => f.map_smul c (x ⊗ₜ y) }

theorem restrict_scalars_curry (f : M ⊗[R] N →ₗ[A] P) : RestrictScalars R (curry f) = curry (f.restrictScalars R) :=
  rfl

/-- Just as `tensor_product.ext` is marked `ext` instead of `tensor_product.ext'`, this is
a better `ext` lemma than `tensor_product.algebra_tensor_module.ext` below.

See note [partially-applied ext lemmas]. -/
@[ext]
theorem curry_injective : Function.Injective (curry : (M ⊗ N →ₗ[A] P) → M →ₗ[A] N →ₗ[R] P) := fun x y h =>
  LinearMap.restrict_scalars_injective R <| curry_injective <| (congr_arg (LinearMap.restrictScalars R) h : _)

theorem ext {g h : M ⊗[R] N →ₗ[A] P} (H : ∀ x y, g (x ⊗ₜ y) = h (x ⊗ₜ y)) : g = h :=
  curry_injective <| LinearMap.ext₂ H

end Semiringₓ

section CommSemiringₓ

variable [CommSemiringₓ R] [CommSemiringₓ A] [Algebra R A]

variable [AddCommMonoidₓ M] [Module R M] [Module A M] [IsScalarTower R A M]

variable [AddCommMonoidₓ N] [Module R N]

variable [AddCommMonoidₓ P] [Module R P] [Module A P] [IsScalarTower R A P]

/-- Heterobasic version of `tensor_product.lift`:

Constructing a linear map `M ⊗[R] N →[A] P` given a bilinear map `M →[A] N →[R] P` with the
property that its composition with the canonical bilinear map `M →[A] N →[R] M ⊗[R] N` is
the given bilinear map `M →[A] N →[R] P`. -/
@[simps]
def lift (f : M →ₗ[A] N →ₗ[R] P) : M ⊗[R] N →ₗ[A] P :=
  { lift (f.restrictScalars R) with
    map_smul' := fun c =>
      show
        ∀ x : M ⊗[R] N,
          (lift (f.restrictScalars R)).comp (lsmul R _ c) x = (lsmul R _ c).comp (lift (f.restrictScalars R)) x
        from
        ext_iff.1 <|
          TensorProduct.ext' fun x y => by
            simp only [← comp_apply, ← Algebra.lsmul_coe, ← smul_tmul', ← lift.tmul, ← coe_restrict_scalars_eq_coe, ←
              f.map_smul, ← smul_apply] }

@[simp]
theorem lift_tmul (f : M →ₗ[A] N →ₗ[R] P) (x : M) (y : N) : lift f (x ⊗ₜ y) = f x y :=
  lift.tmul' x y

variable (R A M N P)

/-- Heterobasic version of `tensor_product.uncurry`:

Linearly constructing a linear map `M ⊗[R] N →[A] P` given a bilinear map `M →[A] N →[R] P`
with the property that its composition with the canonical bilinear map `M →[A] N →[R] M ⊗[R] N` is
the given bilinear map `M →[A] N →[R] P`. -/
@[simps]
def uncurry : (M →ₗ[A] N →ₗ[R] P) →ₗ[A] M ⊗[R] N →ₗ[A] P where
  toFun := lift
  map_add' := fun f g =>
    ext fun x y => by
      simp only [← lift_tmul, ← add_apply]
  map_smul' := fun c f =>
    ext fun x y => by
      simp only [← lift_tmul, ← smul_apply, ← RingHom.id_apply]

/-- Heterobasic version of `tensor_product.lcurry`:

Given a linear map `M ⊗[R] N →[A] P`, compose it with the canonical
bilinear map `M →[A] N →[R] M ⊗[R] N` to form a bilinear map `M →[A] N →[R] P`. -/
@[simps]
def lcurry : (M ⊗[R] N →ₗ[A] P) →ₗ[A] M →ₗ[A] N →ₗ[R] P where
  toFun := curry
  map_add' := fun f g => rfl
  map_smul' := fun c f => rfl

/-- Heterobasic version of `tensor_product.lift.equiv`:

A linear equivalence constructing a linear map `M ⊗[R] N →[A] P` given a
bilinear map `M →[A] N →[R] P` with the property that its composition with the
canonical bilinear map `M →[A] N →[R] M ⊗[R] N` is the given bilinear map `M →[A] N →[R] P`. -/
def lift.equiv : (M →ₗ[A] N →ₗ[R] P) ≃ₗ[A] M ⊗[R] N →ₗ[A] P :=
  LinearEquiv.ofLinear (uncurry R A M N P) (lcurry R A M N P) (LinearMap.ext fun f => ext fun x y => lift_tmul _ x y)
    (LinearMap.ext fun f => LinearMap.ext fun x => LinearMap.ext fun y => lift_tmul f x y)

variable (R A M N P)

/-- Heterobasic version of `tensor_product.mk`:

The canonical bilinear map `M →[A] N →[R] M ⊗[R] N`. -/
@[simps]
def mk : M →ₗ[A] N →ₗ[R] M ⊗[R] N :=
  { mk R M N with map_smul' := fun c x => rfl }

attribute [local ext] TensorProduct.ext

/-- Heterobasic version of `tensor_product.assoc`:

Linear equivalence between `(M ⊗[A] N) ⊗[R] P` and `M ⊗[A] (N ⊗[R] P)`. -/
def assoc : (M ⊗[A] P) ⊗[R] N ≃ₗ[A] M ⊗[A] P ⊗[R] N :=
  LinearEquiv.ofLinear
    (lift <| TensorProduct.uncurry A _ _ _ <| comp (lcurry R A _ _ _) <| TensorProduct.mk A M (P ⊗[R] N))
    (TensorProduct.uncurry A _ _ _ <|
      comp (uncurry R A _ _ _) <| by
        apply TensorProduct.curry
        exact mk R A _ _)
    (by
      ext
      rfl)
    (by
      ext
      simp only [← curry_apply, ← TensorProduct.curry_apply, ← mk_apply, ← TensorProduct.mk_apply, ← uncurry_apply, ←
        TensorProduct.uncurry_apply, ← id_apply, ← lift_tmul, ← compr₂_apply, ← restrict_scalars_apply, ←
        Function.comp_app, ← to_fun_eq_coe, ← lcurry_apply, ← LinearMap.comp_apply])

end CommSemiringₓ

end AlgebraTensorModule

end TensorProduct

namespace LinearMap

open TensorProduct

/-!
### The base-change of a linear map of `R`-modules to a linear map of `A`-modules
-/


section Semiringₓ

variable {R A B M N : Type _} [CommSemiringₓ R]

variable [Semiringₓ A] [Algebra R A] [Semiringₓ B] [Algebra R B]

variable [AddCommMonoidₓ M] [Module R M] [AddCommMonoidₓ N] [Module R N]

variable (r : R) (f g : M →ₗ[R] N)

variable (A)

/-- `base_change A f` for `f : M →ₗ[R] N` is the `A`-linear map `A ⊗[R] M →ₗ[A] A ⊗[R] N`. -/
def baseChange (f : M →ₗ[R] N) : A ⊗[R] M →ₗ[A] A ⊗[R] N where
  toFun := f.ltensor A
  map_add' := (f.ltensor A).map_add
  map_smul' := fun a x =>
    show (f.ltensor A) (rtensor M (Algebra.lmul R A a) x) = (rtensor N ((Algebra.lmul R A) a)) ((ltensor A f) x) by
      rw [← comp_apply, ← comp_apply]
      simp only [← ltensor_comp_rtensor, ← rtensor_comp_ltensor]

variable {A}

@[simp]
theorem base_change_tmul (a : A) (x : M) : f.baseChange A (a ⊗ₜ x) = a ⊗ₜ f x :=
  rfl

theorem base_change_eq_ltensor : (f.baseChange A : A ⊗ M → A ⊗ N) = f.ltensor A :=
  rfl

@[simp]
theorem base_change_add : (f + g).baseChange A = f.baseChange A + g.baseChange A := by
  ext
  simp [← base_change_eq_ltensor]

@[simp]
theorem base_change_zero : baseChange A (0 : M →ₗ[R] N) = 0 := by
  ext
  simp [← base_change_eq_ltensor]

@[simp]
theorem base_change_smul : (r • f).baseChange A = r • f.baseChange A := by
  ext
  simp [← base_change_tmul]

variable (R A M N)

/-- `base_change` as a linear map. -/
@[simps]
def baseChangeHom : (M →ₗ[R] N) →ₗ[R] A ⊗[R] M →ₗ[A] A ⊗[R] N where
  toFun := baseChange A
  map_add' := base_change_add
  map_smul' := base_change_smul

end Semiringₓ

section Ringₓ

variable {R A B M N : Type _} [CommRingₓ R]

variable [Ringₓ A] [Algebra R A] [Ringₓ B] [Algebra R B]

variable [AddCommGroupₓ M] [Module R M] [AddCommGroupₓ N] [Module R N]

variable (f g : M →ₗ[R] N)

@[simp]
theorem base_change_sub : (f - g).baseChange A = f.baseChange A - g.baseChange A := by
  ext
  simp [← base_change_eq_ltensor]

@[simp]
theorem base_change_neg : (-f).baseChange A = -f.baseChange A := by
  ext
  simp [← base_change_eq_ltensor]

end Ringₓ

end LinearMap

namespace Algebra

namespace TensorProduct

section Semiringₓ

variable {R : Type u} [CommSemiringₓ R]

variable {A : Type v₁} [Semiringₓ A] [Algebra R A]

variable {B : Type v₂} [Semiringₓ B] [Algebra R B]

/-!
### The `R`-algebra structure on `A ⊗[R] B`
-/


/-- (Implementation detail)
The multiplication map on `A ⊗[R] B`,
for a fixed pure tensor in the first argument,
as an `R`-linear map.
-/
def mulAux (a₁ : A) (b₁ : B) : A ⊗[R] B →ₗ[R] A ⊗[R] B :=
  TensorProduct.map (lmulLeft R a₁) (lmulLeft R b₁)

@[simp]
theorem mul_aux_apply (a₁ a₂ : A) (b₁ b₂ : B) : (mulAux a₁ b₁) (a₂ ⊗ₜ[R] b₂) = (a₁ * a₂) ⊗ₜ[R] (b₁ * b₂) :=
  rfl

/-- (Implementation detail)
The multiplication map on `A ⊗[R] B`,
as an `R`-bilinear map.
-/
def mul : A ⊗[R] B →ₗ[R] A ⊗[R] B →ₗ[R] A ⊗[R] B :=
  TensorProduct.lift <|
    LinearMap.mk₂ R mulAux
      (fun x₁ x₂ y =>
        TensorProduct.ext' fun x' y' => by
          simp only [← mul_aux_apply, ← LinearMap.add_apply, ← add_mulₓ, ← add_tmul])
      (fun c x y =>
        TensorProduct.ext' fun x' y' => by
          simp only [← mul_aux_apply, ← LinearMap.smul_apply, ← smul_tmul', ← smul_mul_assoc])
      (fun x y₁ y₂ =>
        TensorProduct.ext' fun x' y' => by
          simp only [← mul_aux_apply, ← LinearMap.add_apply, ← add_mulₓ, ← tmul_add])
      fun c x y =>
      TensorProduct.ext' fun x' y' => by
        simp only [← mul_aux_apply, ← LinearMap.smul_apply, ← smul_tmul, ← smul_tmul', ← smul_mul_assoc]

@[simp]
theorem mul_apply (a₁ a₂ : A) (b₁ b₂ : B) : mul (a₁ ⊗ₜ[R] b₁) (a₂ ⊗ₜ[R] b₂) = (a₁ * a₂) ⊗ₜ[R] (b₁ * b₂) :=
  rfl

theorem mul_assoc' (mul : A ⊗[R] B →ₗ[R] A ⊗[R] B →ₗ[R] A ⊗[R] B)
    (h :
      ∀ (a₁ a₂ a₃ : A) (b₁ b₂ b₃ : B),
        mul (mul (a₁ ⊗ₜ[R] b₁) (a₂ ⊗ₜ[R] b₂)) (a₃ ⊗ₜ[R] b₃) = mul (a₁ ⊗ₜ[R] b₁) (mul (a₂ ⊗ₜ[R] b₂) (a₃ ⊗ₜ[R] b₃))) :
    ∀ x y z : A ⊗[R] B, mul (mul x y) z = mul x (mul y z) := by
  intros
  apply TensorProduct.induction_on x
  · simp only [← LinearMap.map_zero, ← LinearMap.zero_apply]
    
  apply TensorProduct.induction_on y
  · simp only [← LinearMap.map_zero, ← forall_const, ← LinearMap.zero_apply]
    
  apply TensorProduct.induction_on z
  · simp only [← LinearMap.map_zero, ← forall_const]
    
  · intros
    simp only [← h]
    
  · intros
    simp only [← LinearMap.map_add, *]
    
  · intros
    simp only [← LinearMap.map_add, *, ← LinearMap.add_apply]
    
  · intros
    simp only [← LinearMap.map_add, *, ← LinearMap.add_apply]
    

theorem mul_assoc (x y z : A ⊗[R] B) : mul (mul x y) z = mul x (mul y z) :=
  mul_assoc' mul
    (by
      intros
      simp only [← mul_apply, ← mul_assoc])
    x y z

theorem one_mul (x : A ⊗[R] B) : mul (1 ⊗ₜ 1) x = x := by
  apply TensorProduct.induction_on x <;> simp (config := { contextual := true })

theorem mul_one (x : A ⊗[R] B) : mul x (1 ⊗ₜ 1) = x := by
  apply TensorProduct.induction_on x <;> simp (config := { contextual := true })

instance : One (A ⊗[R] B) where one := 1 ⊗ₜ 1

instance : AddMonoidWithOneₓ (A ⊗[R] B) :=
  AddMonoidWithOneₓ.unary

instance : Semiringₓ (A ⊗[R] B) :=
  { (by
      infer_instance : AddMonoidWithOneₓ (A ⊗[R] B)),
    (by
      infer_instance : AddCommMonoidₓ (A ⊗[R] B)) with
    zero := 0, add := (· + ·), one := 1, mul := fun a b => mul a b, one_mul := one_mul, mul_one := mul_one,
    mul_assoc := mul_assoc,
    zero_mul := by
      simp ,
    mul_zero := by
      simp ,
    left_distrib := by
      simp ,
    right_distrib := by
      simp }

theorem one_def : (1 : A ⊗[R] B) = (1 : A) ⊗ₜ (1 : B) :=
  rfl

@[simp]
theorem tmul_mul_tmul (a₁ a₂ : A) (b₁ b₂ : B) : a₁ ⊗ₜ[R] b₁ * a₂ ⊗ₜ[R] b₂ = (a₁ * a₂) ⊗ₜ[R] (b₁ * b₂) :=
  rfl

@[simp]
theorem tmul_pow (a : A) (b : B) (k : ℕ) : a ⊗ₜ[R] b ^ k = (a ^ k) ⊗ₜ[R] (b ^ k) := by
  induction' k with k ih
  · simp [← one_def]
    
  · simp [← pow_succₓ, ← ih]
    

/-- The ring morphism `A →+* A ⊗[R] B` sending `a` to `a ⊗ₜ 1`. -/
@[simps]
def includeLeftRingHom : A →+* A ⊗[R] B where
  toFun := fun a => a ⊗ₜ 1
  map_zero' := by
    simp
  map_add' := by
    simp [← add_tmul]
  map_one' := rfl
  map_mul' := by
    simp

variable {S : Type _} [CommSemiringₓ S] [Algebra R S] [Algebra S A] [IsScalarTower R S A]

instance leftAlgebra : Algebra S (A ⊗[R] B) :=
  { TensorProduct.includeLeftRingHom.comp (algebraMap S A),
    (by
      infer_instance : Module S (A ⊗[R] B)) with
    commutes' := fun r x => by
      apply TensorProduct.induction_on x
      · simp
        
      · intro a b
        dsimp'
        rw [Algebra.commutes, _root_.mul_one, _root_.one_mul]
        
      · intro y y' h h'
        dsimp'  at h h'⊢
        simp only [← mul_addₓ, ← add_mulₓ, ← h, ← h']
        ,
    smul_def' := fun r x => by
      apply TensorProduct.induction_on x
      · simp [← smul_zero]
        
      · intro a b
        dsimp'
        rw [TensorProduct.smul_tmul', Algebra.smul_def r a, _root_.one_mul]
        
      · intros
        dsimp'
        simp [← smul_add, ← mul_addₓ, *]
         }

/-- The tensor product of two `R`-algebras is an `R`-algebra. -/
-- This is for the `undergrad.yaml` list.
instance : Algebra R (A ⊗[R] B) :=
  inferInstance

@[simp]
theorem algebra_map_apply (r : S) : (algebraMap S (A ⊗[R] B)) r = (algebraMap S A) r ⊗ₜ 1 :=
  rfl

instance : IsScalarTower R S (A ⊗[R] B) :=
  ⟨fun a b c => by
    simp ⟩

variable {C : Type v₃} [Semiringₓ C] [Algebra R C]

@[ext]
theorem ext {g h : A ⊗[R] B →ₐ[R] C} (H : ∀ a b, g (a ⊗ₜ b) = h (a ⊗ₜ b)) : g = h := by
  apply @AlgHom.to_linear_map_injective R (A ⊗[R] B) C _ _ _ _ _ _ _ _
  ext
  simp [← H]

/-- The `R`-algebra morphism `A →ₐ[R] A ⊗[R] B` sending `a` to `a ⊗ₜ 1`. -/
def includeLeft : A →ₐ[R] A ⊗[R] B :=
  { includeLeftRingHom with
    commutes' := by
      simp }

@[simp]
theorem include_left_apply (a : A) : (includeLeft : A →ₐ[R] A ⊗[R] B) a = a ⊗ₜ 1 :=
  rfl

/-- The algebra morphism `B →ₐ[R] A ⊗[R] B` sending `b` to `1 ⊗ₜ b`. -/
def includeRight : B →ₐ[R] A ⊗[R] B where
  toFun := fun b => 1 ⊗ₜ b
  map_zero' := by
    simp
  map_add' := by
    simp [← tmul_add]
  map_one' := rfl
  map_mul' := by
    simp
  commutes' := fun r => by
    simp only [← algebra_map_apply]
    trans r • (1 : A) ⊗ₜ[R] (1 : B)
    · rw [← tmul_smul, Algebra.smul_def]
      simp
      
    · simp [← Algebra.smul_def]
      

@[simp]
theorem include_right_apply (b : B) : (includeRight : B →ₐ[R] A ⊗[R] B) b = 1 ⊗ₜ b :=
  rfl

end Semiringₓ

section Ringₓ

variable {R : Type u} [CommRingₓ R]

variable {A : Type v₁} [Ringₓ A] [Algebra R A]

variable {B : Type v₂} [Ringₓ B] [Algebra R B]

instance : Ringₓ (A ⊗[R] B) :=
  { (by
      infer_instance : AddCommGroupₓ (A ⊗[R] B)),
    (by
      infer_instance : Semiringₓ (A ⊗[R] B)) with }

end Ringₓ

section CommRingₓ

variable {R : Type u} [CommRingₓ R]

variable {A : Type v₁} [CommRingₓ A] [Algebra R A]

variable {B : Type v₂} [CommRingₓ B] [Algebra R B]

instance : CommRingₓ (A ⊗[R] B) :=
  { (by
      infer_instance : Ringₓ (A ⊗[R] B)) with
    mul_comm := fun x y => by
      apply TensorProduct.induction_on x
      · simp
        
      · intro a₁ b₁
        apply TensorProduct.induction_on y
        · simp
          
        · intro a₂ b₂
          simp [← mul_comm]
          
        · intro a₂ b₂ ha hb
          simp [← mul_addₓ, ← add_mulₓ, ← ha, ← hb]
          
        
      · intro x₁ x₂ h₁ h₂
        simp [← mul_addₓ, ← add_mulₓ, ← h₁, ← h₂]
         }

end CommRingₓ

/-- Verify that typeclass search finds the ring structure on `A ⊗[ℤ] B`
when `A` and `B` are merely rings, by treating both as `ℤ`-algebras.
-/
example {A : Type v₁} [Ringₓ A] {B : Type v₂} [Ringₓ B] : Ringₓ (A ⊗[ℤ] B) := by
  infer_instance

/-- Verify that typeclass search finds the comm_ring structure on `A ⊗[ℤ] B`
when `A` and `B` are merely comm_rings, by treating both as `ℤ`-algebras.
-/
example {A : Type v₁} [CommRingₓ A] {B : Type v₂} [CommRingₓ B] : CommRingₓ (A ⊗[ℤ] B) := by
  infer_instance

/-!
We now build the structure maps for the symmetric monoidal category of `R`-algebras.
-/


section Monoidal

section

variable {R : Type u} [CommSemiringₓ R]

variable {A : Type v₁} [Semiringₓ A] [Algebra R A]

variable {B : Type v₂} [Semiringₓ B] [Algebra R B]

variable {C : Type v₃} [Semiringₓ C] [Algebra R C]

variable {D : Type v₄} [Semiringₓ D] [Algebra R D]

/-- Build an algebra morphism from a linear map out of a tensor product,
and evidence of multiplicativity on pure tensors.
-/
def algHomOfLinearMapTensorProduct (f : A ⊗[R] B →ₗ[R] C)
    (w₁ : ∀ (a₁ a₂ : A) (b₁ b₂ : B), f ((a₁ * a₂) ⊗ₜ (b₁ * b₂)) = f (a₁ ⊗ₜ b₁) * f (a₂ ⊗ₜ b₂))
    (w₂ : ∀ r, f ((algebraMap R A) r ⊗ₜ[R] 1) = (algebraMap R C) r) : A ⊗[R] B →ₐ[R] C :=
  { f with
    map_one' := by
      rw [← (algebraMap R C).map_one, ← w₂, (algebraMap R A).map_one] <;> rfl,
    map_zero' := by
      rw [LinearMap.to_fun_eq_coe, map_zero],
    map_mul' := fun x y => by
      rw [LinearMap.to_fun_eq_coe]
      apply TensorProduct.induction_on x
      · rw [zero_mul, map_zero, zero_mul]
        
      · intro a₁ b₁
        apply TensorProduct.induction_on y
        · rw [mul_zero, map_zero, mul_zero]
          
        · intro a₂ b₂
          rw [tmul_mul_tmul, w₁]
          
        · intro x₁ x₂ h₁ h₂
          rw [mul_addₓ, map_add, map_add, mul_addₓ, h₁, h₂]
          
        
      · intro x₁ x₂ h₁ h₂
        rw [add_mulₓ, map_add, map_add, add_mulₓ, h₁, h₂]
        ,
    commutes' := fun r => by
      rw [LinearMap.to_fun_eq_coe, algebra_map_apply, w₂] }

@[simp]
theorem alg_hom_of_linear_map_tensor_product_apply (f w₁ w₂ x) :
    (algHomOfLinearMapTensorProduct f w₁ w₂ : A ⊗[R] B →ₐ[R] C) x = f x :=
  rfl

/-- Build an algebra equivalence from a linear equivalence out of a tensor product,
and evidence of multiplicativity on pure tensors.
-/
def algEquivOfLinearEquivTensorProduct (f : A ⊗[R] B ≃ₗ[R] C)
    (w₁ : ∀ (a₁ a₂ : A) (b₁ b₂ : B), f ((a₁ * a₂) ⊗ₜ (b₁ * b₂)) = f (a₁ ⊗ₜ b₁) * f (a₂ ⊗ₜ b₂))
    (w₂ : ∀ r, f ((algebraMap R A) r ⊗ₜ[R] 1) = (algebraMap R C) r) : A ⊗[R] B ≃ₐ[R] C :=
  { algHomOfLinearMapTensorProduct (f : A ⊗[R] B →ₗ[R] C) w₁ w₂, f with }

@[simp]
theorem alg_equiv_of_linear_equiv_tensor_product_apply (f w₁ w₂ x) :
    (algEquivOfLinearEquivTensorProduct f w₁ w₂ : A ⊗[R] B ≃ₐ[R] C) x = f x :=
  rfl

/-- Build an algebra equivalence from a linear equivalence out of a triple tensor product,
and evidence of multiplicativity on pure tensors.
-/
def algEquivOfLinearEquivTripleTensorProduct (f : (A ⊗[R] B) ⊗[R] C ≃ₗ[R] D)
    (w₁ :
      ∀ (a₁ a₂ : A) (b₁ b₂ : B) (c₁ c₂ : C),
        f ((a₁ * a₂) ⊗ₜ (b₁ * b₂) ⊗ₜ (c₁ * c₂)) = f (a₁ ⊗ₜ b₁ ⊗ₜ c₁) * f (a₂ ⊗ₜ b₂ ⊗ₜ c₂))
    (w₂ : ∀ r, f (((algebraMap R A) r ⊗ₜ[R] (1 : B)) ⊗ₜ[R] (1 : C)) = (algebraMap R D) r) : (A ⊗[R] B) ⊗[R] C ≃ₐ[R] D :=
  { f with toFun := f,
    map_mul' := fun x y => by
      apply TensorProduct.induction_on x
      · simp only [← map_zero, ← zero_mul]
        
      · intro ab₁ c₁
        apply TensorProduct.induction_on y
        · simp only [← map_zero, ← mul_zero]
          
        · intro ab₂ c₂
          apply TensorProduct.induction_on ab₁
          · simp only [← zero_tmul, ← map_zero, ← zero_mul]
            
          · intro a₁ b₁
            apply TensorProduct.induction_on ab₂
            · simp only [← zero_tmul, ← map_zero, ← mul_zero]
              
            · intros
              simp only [← tmul_mul_tmul, ← w₁]
              
            · intro x₁ x₂ h₁ h₂
              simp only [← tmul_mul_tmul] at h₁ h₂
              simp only [← tmul_mul_tmul, ← mul_addₓ, ← add_tmul, ← map_add, ← h₁, ← h₂]
              
            
          · intro x₁ x₂ h₁ h₂
            simp only [← tmul_mul_tmul] at h₁ h₂
            simp only [← tmul_mul_tmul, ← add_mulₓ, ← add_tmul, ← map_add, ← h₁, ← h₂]
            
          
        · intro x₁ x₂ h₁ h₂
          simp only [← tmul_mul_tmul, ← map_add, ← mul_addₓ, ← add_mulₓ, ← h₁, ← h₂]
          
        
      · intro x₁ x₂ h₁ h₂
        simp only [← tmul_mul_tmul, ← map_add, ← mul_addₓ, ← add_mulₓ, ← h₁, ← h₂]
        ,
    commutes' := fun r => by
      simp [← w₂] }

@[simp]
theorem alg_equiv_of_linear_equiv_triple_tensor_product_apply (f w₁ w₂ x) :
    (algEquivOfLinearEquivTripleTensorProduct f w₁ w₂ : (A ⊗[R] B) ⊗[R] C ≃ₐ[R] D) x = f x :=
  rfl

end

variable {R : Type u} [CommSemiringₓ R]

variable {A : Type v₁} [Semiringₓ A] [Algebra R A]

variable {B : Type v₂} [Semiringₓ B] [Algebra R B]

variable {C : Type v₃} [Semiringₓ C] [Algebra R C]

variable {D : Type v₄} [Semiringₓ D] [Algebra R D]

section

variable (R A)

/-- The base ring is a left identity for the tensor product of algebra, up to algebra isomorphism.
-/
protected def lid : R ⊗[R] A ≃ₐ[R] A :=
  algEquivOfLinearEquivTensorProduct (TensorProduct.lid R A)
    (by
      simp [← mul_smul])
    (by
      simp [← Algebra.smul_def])

@[simp]
theorem lid_tmul (r : R) (a : A) : (TensorProduct.lid R A : R ⊗ A → A) (r ⊗ₜ a) = r • a := by
  simp [← TensorProduct.lid]

/-- The base ring is a right identity for the tensor product of algebra, up to algebra isomorphism.
-/
protected def rid : A ⊗[R] R ≃ₐ[R] A :=
  algEquivOfLinearEquivTensorProduct (TensorProduct.rid R A)
    (by
      simp [← mul_smul])
    (by
      simp [← Algebra.smul_def])

@[simp]
theorem rid_tmul (r : R) (a : A) : (TensorProduct.rid R A : A ⊗ R → A) (a ⊗ₜ r) = r • a := by
  simp [← TensorProduct.rid]

section

variable (R A B)

/-- The tensor product of R-algebras is commutative, up to algebra isomorphism.
-/
protected def comm : A ⊗[R] B ≃ₐ[R] B ⊗[R] A :=
  algEquivOfLinearEquivTensorProduct (TensorProduct.comm R A B)
    (by
      simp )
    fun r => by
    trans r • (1 : B) ⊗ₜ[R] (1 : A)
    · rw [← tmul_smul, Algebra.smul_def]
      simp
      
    · simp [← Algebra.smul_def]
      

@[simp]
theorem comm_tmul (a : A) (b : B) : (TensorProduct.comm R A B : A ⊗[R] B → B ⊗[R] A) (a ⊗ₜ b) = b ⊗ₜ a := by
  simp [← TensorProduct.comm]

theorem adjoin_tmul_eq_top : adjoin R { t : A ⊗[R] B | ∃ a b, a ⊗ₜ[R] b = t } = ⊤ :=
  top_le_iff.mp <| (top_le_iff.mpr <| span_tmul_eq_top R A B).trans (span_le_adjoin R _)

end

section

variable {R A B C}

theorem assoc_aux_1 (a₁ a₂ : A) (b₁ b₂ : B) (c₁ c₂ : C) :
    (TensorProduct.assoc R A B C) (((a₁ * a₂) ⊗ₜ[R] (b₁ * b₂)) ⊗ₜ[R] (c₁ * c₂)) =
      (TensorProduct.assoc R A B C) ((a₁ ⊗ₜ[R] b₁) ⊗ₜ[R] c₁) * (TensorProduct.assoc R A B C) ((a₂ ⊗ₜ[R] b₂) ⊗ₜ[R] c₂) :=
  rfl

theorem assoc_aux_2 (r : R) :
    (TensorProduct.assoc R A B C) (((algebraMap R A) r ⊗ₜ[R] 1) ⊗ₜ[R] 1) = (algebraMap R (A ⊗ (B ⊗ C))) r :=
  rfl

variable (R A B C)

/-- The associator for tensor product of R-algebras, as an algebra isomorphism. -/
protected def assoc : (A ⊗[R] B) ⊗[R] C ≃ₐ[R] A ⊗[R] B ⊗[R] C :=
  algEquivOfLinearEquivTripleTensorProduct (TensorProduct.assoc.{u, v₁, v₂, v₃} R A B C : A ⊗ B ⊗ C ≃ₗ[R] A ⊗ (B ⊗ C))
    (@Algebra.TensorProduct.assoc_aux_1.{u, v₁, v₂, v₃} R _ A _ _ B _ _ C _ _)
    (@Algebra.TensorProduct.assoc_aux_2.{u, v₁, v₂, v₃} R _ A _ _ B _ _ C _ _)

variable {R A B C}

@[simp]
theorem assoc_tmul (a : A) (b : B) (c : C) :
    (TensorProduct.assoc R A B C : (A ⊗[R] B) ⊗[R] C → A ⊗[R] B ⊗[R] C) (a ⊗ₜ b ⊗ₜ c) = a ⊗ₜ (b ⊗ₜ c) :=
  rfl

end

variable {R A B C D}

/-- The tensor product of a pair of algebra morphisms. -/
def map (f : A →ₐ[R] B) (g : C →ₐ[R] D) : A ⊗[R] C →ₐ[R] B ⊗[R] D :=
  algHomOfLinearMapTensorProduct (TensorProduct.map f.toLinearMap g.toLinearMap)
    (by
      simp )
    (by
      simp [← AlgHom.commutes])

@[simp]
theorem map_tmul (f : A →ₐ[R] B) (g : C →ₐ[R] D) (a : A) (c : C) : map f g (a ⊗ₜ c) = f a ⊗ₜ g c :=
  rfl

@[simp]
theorem map_comp_include_left (f : A →ₐ[R] B) (g : C →ₐ[R] D) : (map f g).comp includeLeft = includeLeft.comp f :=
  AlgHom.ext <| by
    simp

@[simp]
theorem map_comp_include_right (f : A →ₐ[R] B) (g : C →ₐ[R] D) : (map f g).comp includeRight = includeRight.comp g :=
  AlgHom.ext <| by
    simp

theorem map_range (f : A →ₐ[R] B) (g : C →ₐ[R] D) :
    (map f g).range = (includeLeft.comp f).range⊔(includeRight.comp g).range := by
  apply le_antisymmₓ
  · rw [← map_top, ← adjoin_tmul_eq_top, ← adjoin_image, adjoin_le_iff]
    rintro _ ⟨_, ⟨a, b, rfl⟩, rfl⟩
    rw [map_tmul, ← _root_.mul_one (f a), ← _root_.one_mul (g b), ← tmul_mul_tmul]
    exact mul_mem_sup (AlgHom.mem_range_self _ a) (AlgHom.mem_range_self _ b)
    
  · rw [← map_comp_include_left f g, ← map_comp_include_right f g]
    exact sup_le (AlgHom.range_comp_le_range _ _) (AlgHom.range_comp_le_range _ _)
    

/-- Construct an isomorphism between tensor products of R-algebras
from isomorphisms between the tensor factors.
-/
def congr (f : A ≃ₐ[R] B) (g : C ≃ₐ[R] D) : A ⊗[R] C ≃ₐ[R] B ⊗[R] D :=
  AlgEquiv.ofAlgHom (map f g) (map f.symm g.symm)
    (ext fun b d => by
      simp )
    (ext fun a c => by
      simp )

@[simp]
theorem congr_apply (f : A ≃ₐ[R] B) (g : C ≃ₐ[R] D) (x) : congr f g x = (map (f : A →ₐ[R] B) (g : C →ₐ[R] D)) x :=
  rfl

@[simp]
theorem congr_symm_apply (f : A ≃ₐ[R] B) (g : C ≃ₐ[R] D) (x) :
    (congr f g).symm x = (map (f.symm : B →ₐ[R] A) (g.symm : D →ₐ[R] C)) x :=
  rfl

end

end Monoidal

section

variable {R A B S : Type _} [CommSemiringₓ R] [Semiringₓ A] [Semiringₓ B] [CommSemiringₓ S]

variable [Algebra R A] [Algebra R B] [Algebra R S]

variable (f : A →ₐ[R] S) (g : B →ₐ[R] S)

variable (R)

/-- `algebra.lmul'` is an alg_hom on commutative rings. -/
def lmul' : S ⊗[R] S →ₐ[R] S :=
  algHomOfLinearMapTensorProduct (Algebra.lmul' R)
    (fun a₁ a₂ b₁ b₂ => by
      simp only [← Algebra.lmul'_apply, ← mul_mul_mul_commₓ])
    fun r => by
    simp only [← Algebra.lmul'_apply, ← _root_.mul_one]

variable {R}

theorem lmul'_to_linear_map : (lmul' R : _ →ₐ[R] S).toLinearMap = Algebra.lmul' R :=
  rfl

@[simp]
theorem lmul'_apply_tmul (a b : S) : lmul' R (a ⊗ₜ[R] b) = a * b :=
  lmul'_apply

@[simp]
theorem lmul'_comp_include_left : (lmul' R : _ →ₐ[R] S).comp includeLeft = AlgHom.id R S :=
  AlgHom.ext fun _ => (lmul'_apply_tmul _ _).trans (mul_oneₓ _)

@[simp]
theorem lmul'_comp_include_right : (lmul' R : _ →ₐ[R] S).comp includeRight = AlgHom.id R S :=
  AlgHom.ext fun _ => (lmul'_apply_tmul _ _).trans (one_mulₓ _)

/-- If `S` is commutative, for a pair of morphisms `f : A →ₐ[R] S`, `g : B →ₐ[R] S`,
We obtain a map `A ⊗[R] B →ₐ[R] S` that commutes with `f`, `g` via `a ⊗ b ↦ f(a) * g(b)`.
-/
def productMap : A ⊗[R] B →ₐ[R] S :=
  (lmul' R).comp (TensorProduct.map f g)

@[simp]
theorem product_map_apply_tmul (a : A) (b : B) : productMap f g (a ⊗ₜ b) = f a * g b := by
  unfold product_map lmul'
  simp

theorem product_map_left_apply (a : A) : productMap f g ((includeLeft : A →ₐ[R] A ⊗ B) a) = f a := by
  simp

@[simp]
theorem product_map_left : (productMap f g).comp includeLeft = f :=
  AlgHom.ext <| by
    simp

theorem product_map_right_apply (b : B) : productMap f g (includeRight b) = g b := by
  simp

@[simp]
theorem product_map_right : (productMap f g).comp includeRight = g :=
  AlgHom.ext <| by
    simp

theorem product_map_range : (productMap f g).range = f.range⊔g.range := by
  rw [product_map, AlgHom.range_comp, map_range, map_sup, ← AlgHom.range_comp, ← AlgHom.range_comp, ← AlgHom.comp_assoc,
    ← AlgHom.comp_assoc, lmul'_comp_include_left, lmul'_comp_include_right, AlgHom.id_comp, AlgHom.id_comp]

end

section

variable {R A A' B S : Type _}

variable [CommSemiringₓ R] [CommSemiringₓ A] [Semiringₓ A'] [Semiringₓ B] [CommSemiringₓ S]

variable [Algebra R A] [Algebra R A'] [Algebra A A'] [IsScalarTower R A A'] [Algebra R B]

variable [Algebra R S] [Algebra A S] [IsScalarTower R A S]

/-- If `A`, `B` are `R`-algebras, `A'` is an `A`-algebra, then the product map of `f : A' →ₐ[A] S`
and `g : B →ₐ[R] S` is an `A`-algebra homomorphism. -/
@[simps]
def productLeftAlgHom (f : A' →ₐ[A] S) (g : B →ₐ[R] S) : A' ⊗[R] B →ₐ[A] S :=
  { (productMap (f.restrictScalars R) g).toRingHom with
    commutes' := fun r => by
      dsimp'
      simp }

end

end TensorProduct

end Algebra

namespace Module

variable {R M N : Type _} [CommSemiringₓ R]

variable [AddCommMonoidₓ M] [AddCommMonoidₓ N]

variable [Module R M] [Module R N]

/-- The algebra homomorphism from `End M ⊗ End N` to `End (M ⊗ N)` sending `f ⊗ₜ g` to
the `tensor_product.map f g`, the tensor product of the two maps. -/
def endTensorEndAlgHom : End R M ⊗[R] End R N →ₐ[R] End R (M ⊗[R] N) := by
  refine' Algebra.TensorProduct.algHomOfLinearMapTensorProduct (hom_tensor_hom_map R M N M N) _ _
  · intro f₁ f₂ g₁ g₂
    simp only [← hom_tensor_hom_map_apply, ← TensorProduct.map_mul]
    
  · intro r
    simp only [← hom_tensor_hom_map_apply]
    ext m n
    simp [← smul_tmul]
    

theorem End_tensor_End_alg_hom_apply (f : End R M) (g : End R N) :
    endTensorEndAlgHom (f ⊗ₜ[R] g) = TensorProduct.map f g := by
  simp only [← End_tensor_End_alg_hom, ← Algebra.TensorProduct.alg_hom_of_linear_map_tensor_product_apply, ←
    hom_tensor_hom_map_apply]

end Module

theorem Subalgebra.finite_dimensional_sup {K L : Type _} [Field K] [CommRingₓ L] [Algebra K L] (E1 E2 : Subalgebra K L)
    [FiniteDimensional K E1] [FiniteDimensional K E2] : FiniteDimensional K ↥(E1⊔E2) := by
  rw [← E1.range_val, ← E2.range_val, ← Algebra.TensorProduct.product_map_range]
  exact (Algebra.TensorProduct.productMap E1.val E2.val).toLinearMap.finite_dimensional_range

