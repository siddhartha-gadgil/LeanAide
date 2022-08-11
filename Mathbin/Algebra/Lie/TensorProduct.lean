/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathbin.Algebra.Lie.Abelian

/-!
# Tensor products of Lie modules

Tensor products of Lie modules carry natural Lie module structures.

## Tags

lie module, tensor product, universal property
-/


universe u v w w₁ w₂ w₃

variable {R : Type u} [CommRingₓ R]

open LieModule

namespace TensorProduct

open TensorProduct

namespace LieModule

variable {L : Type v} {M : Type w} {N : Type w₁} {P : Type w₂} {Q : Type w₃}

variable [LieRing L] [LieAlgebra R L]

variable [AddCommGroupₓ M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable [AddCommGroupₓ N] [Module R N] [LieRingModule L N] [LieModule R L N]

variable [AddCommGroupₓ P] [Module R P] [LieRingModule L P] [LieModule R L P]

variable [AddCommGroupₓ Q] [Module R Q] [LieRingModule L Q] [LieModule R L Q]

attribute [local ext] TensorProduct.ext

/-- It is useful to define the bracket via this auxiliary function so that we have a type-theoretic
expression of the fact that `L` acts by linear endomorphisms. It simplifies the proofs in
`lie_ring_module` below. -/
def hasBracketAux (x : L) : Module.End R (M ⊗[R] N) :=
  (toEndomorphism R L M x).rtensor N + (toEndomorphism R L N x).ltensor M

/-- The tensor product of two Lie modules is a Lie ring module. -/
instance lieRingModule : LieRingModule L (M ⊗[R] N) where
  bracket := fun x => hasBracketAux x
  add_lie := fun x y t => by
    simp only [← has_bracket_aux, ← LinearMap.ltensor_add, ← LinearMap.rtensor_add, ← LieHom.map_add, ←
      LinearMap.add_apply]
    abel
  lie_add := fun x => LinearMap.map_add _
  leibniz_lie := fun x y t => by
    suffices
      (has_bracket_aux x).comp (has_bracket_aux y) =
        has_bracket_aux ⁅x,y⁆ + (has_bracket_aux y).comp (has_bracket_aux x)
      by
      simp only [LinearMap.add_apply]
      rw [← LinearMap.comp_apply, this]
      rfl
    ext m n
    simp only [← has_bracket_aux, ← LieRing.of_associative_ring_bracket, ← LinearMap.mul_apply, ← mk_apply, ←
      LinearMap.ltensor_sub, ← LinearMap.compr₂_apply, ← Function.comp_app, ← LinearMap.coe_comp, ←
      LinearMap.rtensor_tmul, ← LieHom.map_lie, ← to_endomorphism_apply_apply, ← LinearMap.add_apply, ←
      LinearMap.map_add, ← LinearMap.rtensor_sub, ← LinearMap.sub_apply, ← LinearMap.ltensor_tmul]
    abel

/-- The tensor product of two Lie modules is a Lie module. -/
instance lieModule : LieModule R L (M ⊗[R] N) where
  smul_lie := fun c x t => by
    change has_bracket_aux (c • x) _ = c • has_bracket_aux _ _
    simp only [← has_bracket_aux, ← smul_add, ← LinearMap.rtensor_smul, ← LinearMap.smul_apply, ←
      LinearMap.ltensor_smul, ← LieHom.map_smul, ← LinearMap.add_apply]
  lie_smul := fun c x => LinearMap.map_smul _ c

@[simp]
theorem lie_tmul_right (x : L) (m : M) (n : N) : ⁅x,m ⊗ₜ[R] n⁆ = ⁅x,m⁆ ⊗ₜ n + m ⊗ₜ ⁅x,n⁆ :=
  show hasBracketAux x (m ⊗ₜ[R] n) = _ by
    simp only [← has_bracket_aux, ← LinearMap.rtensor_tmul, ← to_endomorphism_apply_apply, ← LinearMap.add_apply, ←
      LinearMap.ltensor_tmul]

variable (R L M N P Q)

/-- The universal property for tensor product of modules of a Lie algebra: the `R`-linear
tensor-hom adjunction is equivariant with respect to the `L` action. -/
def lift : (M →ₗ[R] N →ₗ[R] P) ≃ₗ⁅R,L⁆ M ⊗[R] N →ₗ[R] P :=
  { TensorProduct.lift.equiv R M N P with
    map_lie' := fun x f => by
      ext m n
      simp only [← mk_apply, ← LinearMap.compr₂_apply, ← lie_tmul_right, ← LinearMap.sub_apply, ← lift.equiv_apply, ←
        LinearEquiv.to_fun_eq_coe, ← LieHom.lie_apply, ← LinearMap.map_add]
      abel }

@[simp]
theorem lift_apply (f : M →ₗ[R] N →ₗ[R] P) (m : M) (n : N) : lift R L M N P f (m ⊗ₜ n) = f m n :=
  lift.equiv_apply R M N P f m n

/-- A weaker form of the universal property for tensor product of modules of a Lie algebra.

Note that maps `f` of type `M →ₗ⁅R,L⁆ N →ₗ[R] P` are exactly those `R`-bilinear maps satisfying
`⁅x, f m n⁆ = f ⁅x, m⁆ n + f m ⁅x, n⁆` for all `x, m, n` (see e.g, `lie_module_hom.map_lie₂`). -/
def liftLie : (M →ₗ⁅R,L⁆ N →ₗ[R] P) ≃ₗ[R] M ⊗[R] N →ₗ⁅R,L⁆ P :=
  maxTrivLinearMapEquivLieModuleHom.symm ≪≫ₗ ↑(maxTrivEquiv (lift R L M N P)) ≪≫ₗ
    max_triv_linear_map_equiv_lie_module_hom

@[simp]
theorem coe_lift_lie_eq_lift_coe (f : M →ₗ⁅R,L⁆ N →ₗ[R] P) : ⇑(liftLie R L M N P f) = lift R L M N P f := by
  suffices (lift_lie R L M N P f : M ⊗[R] N →ₗ[R] P) = lift R L M N P f by
    rw [← this, LieModuleHom.coe_to_linear_map]
  ext m n
  simp only [← lift_lie, ← LinearEquiv.trans_apply, ← LieModuleEquiv.coe_to_linear_equiv, ←
    coe_linear_map_max_triv_linear_map_equiv_lie_module_hom, ← coe_max_triv_equiv_apply, ←
    coe_linear_map_max_triv_linear_map_equiv_lie_module_hom_symm]

theorem lift_lie_apply (f : M →ₗ⁅R,L⁆ N →ₗ[R] P) (m : M) (n : N) : liftLie R L M N P f (m ⊗ₜ n) = f m n := by
  simp only [← coe_lift_lie_eq_lift_coe, ← LieModuleHom.coe_to_linear_map, ← lift_apply]

variable {R L M N P Q}

/-- A pair of Lie module morphisms `f : M → P` and `g : N → Q`, induce a Lie module morphism:
`M ⊗ N → P ⊗ Q`. -/
def map (f : M →ₗ⁅R,L⁆ P) (g : N →ₗ⁅R,L⁆ Q) : M ⊗[R] N →ₗ⁅R,L⁆ P ⊗[R] Q :=
  { map (f : M →ₗ[R] P) (g : N →ₗ[R] Q) with
    map_lie' := fun x t => by
      simp only [← LinearMap.to_fun_eq_coe]
      apply t.induction_on
      · simp only [← LinearMap.map_zero, ← lie_zero]
        
      · intro m n
        simp only [← LieModuleHom.coe_to_linear_map, ← lie_tmul_right, ← LieModuleHom.map_lie, ← map_tmul, ←
          LinearMap.map_add]
        
      · intro t₁ t₂ ht₁ ht₂
        simp only [← ht₁, ← ht₂, ← lie_add, ← LinearMap.map_add]
         }

@[simp]
theorem coe_linear_map_map (f : M →ₗ⁅R,L⁆ P) (g : N →ₗ⁅R,L⁆ Q) :
    (map f g : M ⊗[R] N →ₗ[R] P ⊗[R] Q) = TensorProduct.map (f : M →ₗ[R] P) (g : N →ₗ[R] Q) :=
  rfl

@[simp]
theorem map_tmul (f : M →ₗ⁅R,L⁆ P) (g : N →ₗ⁅R,L⁆ Q) (m : M) (n : N) : map f g (m ⊗ₜ n) = f m ⊗ₜ g n :=
  map_tmul f g m n

/-- Given Lie submodules `M' ⊆ M` and `N' ⊆ N`, this is the natural map: `M' ⊗ N' → M ⊗ N`. -/
def mapIncl (M' : LieSubmodule R L M) (N' : LieSubmodule R L N) : M' ⊗[R] N' →ₗ⁅R,L⁆ M ⊗[R] N :=
  map M'.incl N'.incl

@[simp]
theorem map_incl_def (M' : LieSubmodule R L M) (N' : LieSubmodule R L N) : mapIncl M' N' = map M'.incl N'.incl :=
  rfl

end LieModule

end TensorProduct

namespace LieModule

open TensorProduct

variable (R) (L : Type v) (M : Type w)

variable [LieRing L] [LieAlgebra R L]

variable [AddCommGroupₓ M] [Module R M] [LieRingModule L M] [LieModule R L M]

/-- The action of the Lie algebra on one of its modules, regarded as a morphism of Lie modules. -/
def toModuleHom : L ⊗[R] M →ₗ⁅R,L⁆ M :=
  TensorProduct.LieModule.liftLie R L L M M
    { (toEndomorphism R L M : L →ₗ[R] M →ₗ[R] M) with
      map_lie' := fun x m => by
        ext n
        simp [← LieRing.of_associative_ring_bracket] }

@[simp]
theorem to_module_hom_apply (x : L) (m : M) : toModuleHom R L M (x ⊗ₜ m) = ⁅x,m⁆ := by
  simp only [← to_module_hom, ← TensorProduct.LieModule.lift_lie_apply, ← to_endomorphism_apply_apply, ←
    LieHom.coe_to_linear_map, ← LieModuleHom.coe_mk, ← LinearMap.coe_mk, ← LinearMap.to_fun_eq_coe]

end LieModule

namespace LieSubmodule

open TensorProduct

open TensorProduct.LieModule

open LieModule

variable {L : Type v} {M : Type w}

variable [LieRing L] [LieAlgebra R L]

variable [AddCommGroupₓ M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable (I : LieIdeal R L) (N : LieSubmodule R L M)

/-- A useful alternative characterisation of Lie ideal operations on Lie submodules.

Given a Lie ideal `I ⊆ L` and a Lie submodule `N ⊆ M`, by tensoring the inclusion maps and then
applying the action of `L` on `M`, we obtain morphism of Lie modules `f : I ⊗ N → L ⊗ M → M`.

This lemma states that `⁅I, N⁆ = range f`. -/
theorem lie_ideal_oper_eq_tensor_map_range :
    ⁅I,N⁆ = ((toModuleHom R L M).comp (mapIncl I N : ↥I ⊗ ↥N →ₗ⁅R,L⁆ L ⊗ M)).range := by
  rw [← coe_to_submodule_eq_iff, lie_ideal_oper_eq_linear_span, LieModuleHom.coe_submodule_range,
    LieModuleHom.coe_linear_map_comp, LinearMap.range_comp, map_incl_def, coe_linear_map_map,
    TensorProduct.map_range_eq_span_tmul, Submodule.map_span]
  congr
  ext m
  constructor
  · rintro ⟨⟨x, hx⟩, ⟨n, hn⟩, rfl⟩
    use x ⊗ₜ n
    constructor
    · use ⟨x, hx⟩, ⟨n, hn⟩
      simp
      
    · simp
      
    
  · rintro ⟨t, ⟨⟨x, hx⟩, ⟨n, hn⟩, rfl⟩, h⟩
    rw [← h]
    use ⟨x, hx⟩, ⟨n, hn⟩
    simp
    

end LieSubmodule

