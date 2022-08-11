/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathbin.RingTheory.AlgebraTower
import Mathbin.LinearAlgebra.Matrix.FiniteDimensional
import Mathbin.LinearAlgebra.Matrix.ToLin

/-!
# Tower of field extensions

In this file we prove the tower law for arbitrary extensions and finite extensions.
Suppose `L` is a field extension of `K` and `K` is a field extension of `F`.
Then `[L:F] = [L:K] [K:F]` where `[E₁:E₂]` means the `E₂`-dimension of `E₁`.

In fact we generalize it to vector spaces, where `L` is not necessarily a field,
but just a vector space over `K`.

## Implementation notes

We prove two versions, since there are two notions of dimensions: `module.rank` which gives
the dimension of an arbitrary vector space as a cardinal, and `finite_dimensional.finrank` which
gives the dimension of a finitely-dimensional vector space as a natural number.

## Tags

tower law

-/


universe u v w u₁ v₁ w₁

open Classical BigOperators

section Field

open Cardinal

variable (F : Type u) (K : Type v) (A : Type w)

variable [Field F] [Field K] [AddCommGroupₓ A]

variable [Algebra F K] [Module K A] [Module F A] [IsScalarTower F K A]

/-- Tower law: if `A` is a `K`-vector space and `K` is a field extension of `F` then
`dim_F(A) = dim_F(K) * dim_K(A)`. -/
theorem dim_mul_dim' :
    Cardinal.lift.{w} (Module.rank F K) * Cardinal.lift.{v} (Module.rank K A) = Cardinal.lift.{v} (Module.rank F A) :=
  by
  let b := Basis.ofVectorSpace F K
  let c := Basis.ofVectorSpace K A
  rw [← (Module.rank F K).lift_id, ← b.mk_eq_dim, ← (Module.rank K A).lift_id, ← c.mk_eq_dim, ← lift_umax.{w, v}, ←
    (b.smul c).mk_eq_dim, mk_prod, lift_mul, lift_lift, lift_lift, lift_lift, lift_lift, lift_umax]

/-- Tower law: if `A` is a `K`-vector space and `K` is a field extension of `F` then
`dim_F(A) = dim_F(K) * dim_K(A)`. -/
theorem dim_mul_dim (F : Type u) (K A : Type v) [Field F] [Field K] [AddCommGroupₓ A] [Algebra F K] [Module K A]
    [Module F A] [IsScalarTower F K A] : Module.rank F K * Module.rank K A = Module.rank F A := by
  convert dim_mul_dim' F K A <;> rw [lift_id]

namespace FiniteDimensional

open IsNoetherian

theorem trans [FiniteDimensional F K] [FiniteDimensional K A] : FiniteDimensional F A :=
  let b := Basis.ofVectorSpace F K
  let c := Basis.ofVectorSpace K A
  of_fintype_basis <| b.smul c

/-- In a tower of field extensions `L / K / F`, if `L / F` is finite, so is `K / F`.

(In fact, it suffices that `L` is a nontrivial ring.)

Note this cannot be an instance as Lean cannot infer `L`.
-/
theorem left (L : Type _) [Ringₓ L] [Nontrivial L] [Algebra F L] [Algebra K L] [IsScalarTower F K L]
    [FiniteDimensional F L] : FiniteDimensional F K :=
  FiniteDimensional.of_injective (IsScalarTower.toAlgHom F K L).toLinearMap (RingHom.injective _)

theorem right [hf : FiniteDimensional F A] : FiniteDimensional K A :=
  let ⟨⟨b, hb⟩⟩ := hf
  ⟨⟨b,
      Submodule.restrict_scalars_injective F _ _ <| by
        rw [Submodule.restrict_scalars_top, eq_top_iff, ← hb, Submodule.span_le]
        exact Submodule.subset_span⟩⟩

/-- Tower law: if `A` is a `K`-algebra and `K` is a field extension of `F` then
`dim_F(A) = dim_F(K) * dim_K(A)`. -/
theorem finrank_mul_finrank [FiniteDimensional F K] : finrank F K * finrank K A = finrank F A := by
  by_cases' hA : FiniteDimensional K A
  · skip
    let b := Basis.ofVectorSpace F K
    let c := Basis.ofVectorSpace K A
    rw [finrank_eq_card_basis b, finrank_eq_card_basis c, finrank_eq_card_basis (b.smul c), Fintype.card_prod]
    
  · rw [finrank_of_infinite_dimensional hA, mul_zero, finrank_of_infinite_dimensional]
    exact mt (@right F K A _ _ _ _ _ _ _) hA
    

instance linear_map (F : Type u) (V : Type v) (W : Type w) [Field F] [AddCommGroupₓ V] [Module F V] [AddCommGroupₓ W]
    [Module F W] [FiniteDimensional F V] [FiniteDimensional F W] : FiniteDimensional F (V →ₗ[F] W) :=
  let b := Basis.ofVectorSpace F V
  let c := Basis.ofVectorSpace F W
  (Matrix.toLin b c).FiniteDimensional

theorem finrank_linear_map (F : Type u) (V : Type v) (W : Type w) [Field F] [AddCommGroupₓ V] [Module F V]
    [AddCommGroupₓ W] [Module F W] [FiniteDimensional F V] [FiniteDimensional F W] :
    finrank F (V →ₗ[F] W) = finrank F V * finrank F W := by
  let b := Basis.ofVectorSpace F V
  let c := Basis.ofVectorSpace F W
  rw [LinearEquiv.finrank_eq (LinearMap.toMatrix b c), Matrix.finrank_matrix, finrank_eq_card_basis b,
    finrank_eq_card_basis c, mul_comm]

-- TODO: generalize by removing [finite_dimensional F K]
-- V = ⊕F,
-- (V →ₗ[F] K) = ((⊕F) →ₗ[F] K) = (⊕ (F →ₗ[F] K)) = ⊕K
instance linear_map' (F : Type u) (K : Type v) (V : Type w) [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    [AddCommGroupₓ V] [Module F V] [FiniteDimensional F V] : FiniteDimensional K (V →ₗ[F] K) :=
  right F _ _

theorem finrank_linear_map' (F : Type u) (K : Type v) (V : Type w) [Field F] [Field K] [Algebra F K]
    [FiniteDimensional F K] [AddCommGroupₓ V] [Module F V] [FiniteDimensional F V] :
    finrank K (V →ₗ[F] K) = finrank F V :=
  (Nat.mul_right_inj <| show 0 < finrank F K from finrank_pos).1 <|
    calc
      finrank F K * finrank K (V →ₗ[F] K) = finrank F (V →ₗ[F] K) := finrank_mul_finrank _ _ _
      _ = finrank F V * finrank F K := finrank_linear_map F V K
      _ = finrank F K * finrank F V := mul_comm _ _
      

end FiniteDimensional

end Field

