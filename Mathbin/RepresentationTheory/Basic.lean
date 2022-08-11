/-
Copyright (c) 2022 Antoine Labelle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Labelle
-/
import Mathbin.Algebra.Module.Basic
import Mathbin.Algebra.Module.LinearMap
import Mathbin.Algebra.MonoidAlgebra.Basic
import Mathbin.LinearAlgebra.Trace
import Mathbin.LinearAlgebra.Dual
import Mathbin.LinearAlgebra.FreeModule.Basic

/-!
# Monoid representations

This file introduces monoid representations and their characters and defines a few ways to construct
representations.

## Main definitions

  * representation.representation
  * representation.character
  * representation.tprod
  * representation.lin_hom
  * represensation.dual

## Implementation notes

Representations of a monoid `G` on a `k`-module `V` are implemented as
homomorphisms `G →* (V →ₗ[k] V)`.
-/


open MonoidAlgebra (lift of)

open LinearMap

section

variable (k G V : Type _) [CommSemiringₓ k] [Monoidₓ G] [AddCommMonoidₓ V] [Module k V]

/-- A representation of `G` on the `k`-module `V` is an homomorphism `G →* (V →ₗ[k] V)`.
-/
abbrev Representation :=
  G →* V →ₗ[k] V

end

namespace Representation

section trivialₓ

variable {k G V : Type _} [CommSemiringₓ k] [Monoidₓ G] [AddCommMonoidₓ V] [Module k V]

/-- The trivial representation of `G` on the one-dimensional module `k`.
-/
def trivial : Representation k G k :=
  1

@[simp]
theorem trivial_def (g : G) (v : k) : trivial g v = v :=
  rfl

end trivialₓ

section MonoidAlgebra

variable {k G V : Type _} [CommSemiringₓ k] [Monoidₓ G] [AddCommMonoidₓ V] [Module k V]

variable (ρ : Representation k G V)

/-- A `k`-linear representation of `G` on `V` can be thought of as
an algebra map from `monoid_algebra k G` into the `k`-linear endomorphisms of `V`.
-/
noncomputable def asAlgebraHom : MonoidAlgebra k G →ₐ[k] Module.End k V :=
  (lift k G _) ρ

theorem as_algebra_hom_def : asAlgebraHom ρ = (lift k G _) ρ :=
  rfl

@[simp]
theorem as_algebra_hom_single (g : G) : asAlgebraHom ρ (Finsupp.single g 1) = ρ g := by
  simp only [← as_algebra_hom_def, ← MonoidAlgebra.lift_single, ← one_smul]

theorem as_algebra_hom_of (g : G) : asAlgebraHom ρ (of k G g) = ρ g := by
  simp only [← MonoidAlgebra.of_apply, ← as_algebra_hom_single]

/-- A `k`-linear representation of `G` on `V` can be thought of as
a module over `monoid_algebra k G`.
-/
noncomputable def asModule : Module (MonoidAlgebra k G) V :=
  Module.compHom V (asAlgebraHom ρ).toRingHom

end MonoidAlgebra

section MulAction

variable (k : Type _) [CommSemiringₓ k] (G : Type _) [Monoidₓ G] (H : Type _) [MulAction G H]

/-- A `G`-action on `H` induces a representation `G →* End(k[H])` in the natural way. -/
noncomputable def ofMulAction : Representation k G (H →₀ k) where
  toFun := fun g => Finsupp.lmapDomain k k ((· • ·) g)
  map_one' := by
    ext x y
    dsimp'
    simp
  map_mul' := fun x y => by
    ext z w
    simp [← mul_smul]

variable {k G H}

theorem of_mul_action_def (g : G) : ofMulAction k G H g = Finsupp.lmapDomain k k ((· • ·) g) :=
  rfl

end MulAction

section Groupₓ

variable {k G V : Type _} [CommSemiringₓ k] [Groupₓ G] [AddCommMonoidₓ V] [Module k V]

variable (ρ : Representation k G V)

@[simp]
theorem of_mul_action_apply {H : Type _} [MulAction G H] (g : G) (f : H →₀ k) (h : H) :
    ofMulAction k G H g f h = f (g⁻¹ • h) := by
  conv_lhs => rw [← smul_inv_smul g h]
  let h' := g⁻¹ • h
  change of_mul_action k G H g f (g • h') = f h'
  have hg : Function.Injective ((· • ·) g : H → H) := by
    intro h₁ h₂
    simp
  simp only [← of_mul_action_def, ← Finsupp.lmap_domain_apply, ← Finsupp.map_domain_apply, ← hg]

/-- When `G` is a group, a `k`-linear representation of `G` on `V` can be thought of as
a group homomorphism from `G` into the invertible `k`-linear endomorphisms of `V`.
-/
def asGroupHom : G →* Units (V →ₗ[k] V) :=
  MonoidHom.toHomUnits ρ

theorem as_group_hom_apply (g : G) : ↑(asGroupHom ρ g) = ρ g := by
  simp only [← as_group_hom, ← MonoidHom.coe_to_hom_units]

end Groupₓ

section TensorProduct

variable {k G V W : Type _} [CommSemiringₓ k] [Monoidₓ G]

variable [AddCommMonoidₓ V] [Module k V] [AddCommMonoidₓ W] [Module k W]

variable (ρV : Representation k G V) (ρW : Representation k G W)

open TensorProduct

/-- Given representations of `G` on `V` and `W`, there is a natural representation of `G` on their
tensor product `V ⊗[k] W`.
-/
def tprod : Representation k G (V ⊗[k] W) where
  toFun := fun g => TensorProduct.map (ρV g) (ρW g)
  map_one' := by
    simp only [← map_one, ← TensorProduct.map_one]
  map_mul' := fun g h => by
    simp only [← map_mul, ← TensorProduct.map_mul]

-- mathport name: «expr ⊗ »
local notation ρV " ⊗ " ρW => tprod ρV ρW

@[simp]
theorem tprod_apply (g : G) : (ρV ⊗ ρW) g = TensorProduct.map (ρV g) (ρW g) :=
  rfl

end TensorProduct

section LinearHom

variable {k G V W : Type _} [CommSemiringₓ k] [Groupₓ G]

variable [AddCommMonoidₓ V] [Module k V] [AddCommMonoidₓ W] [Module k W]

variable (ρV : Representation k G V) (ρW : Representation k G W)

/-- Given representations of `G` on `V` and `W`, there is a natural representation of `G` on the
module `V →ₗ[k] W`, where `G` acts by conjugation.
-/
def linHom : Representation k G (V →ₗ[k] W) where
  toFun := fun g =>
    { toFun := fun f => ρW g ∘ₗ f ∘ₗ ρV g⁻¹,
      map_add' := fun f₁ f₂ => by
        simp_rw [add_comp, comp_add],
      map_smul' := fun r f => by
        simp_rw [RingHom.id_apply, smul_comp, comp_smul] }
  map_one' :=
    LinearMap.ext fun x => by
      simp_rw [coe_mk, inv_one, map_one, one_apply, one_eq_id, comp_id, id_comp]
  map_mul' := fun g h =>
    LinearMap.ext fun x => by
      simp_rw [coe_mul, coe_mk, Function.comp_applyₓ, mul_inv_rev, map_mul, mul_eq_comp, comp_assoc]

@[simp]
theorem lin_hom_apply (g : G) (f : V →ₗ[k] W) : (linHom ρV ρW) g f = ρW g ∘ₗ f ∘ₗ ρV g⁻¹ :=
  rfl

/-- The dual of a representation `ρ` of `G` on a module `V`, given by `(dual ρ) g f = f ∘ₗ (ρ g⁻¹)`,
where `f : module.dual k V`.
-/
def dual : Representation k G (Module.Dual k V) where
  toFun := fun g =>
    { toFun := fun f => f ∘ₗ ρV g⁻¹,
      map_add' := fun f₁ f₂ => by
        simp only [← add_comp],
      map_smul' := fun r f => by
        ext
        simp only [← coe_comp, ← Function.comp_app, ← smul_apply, ← RingHom.id_apply] }
  map_one' := by
    ext
    simp only [← coe_comp, ← Function.comp_app, ← map_one, ← inv_one, ← coe_mk, ← one_apply]
  map_mul' := fun g h => by
    ext
    simp only [← coe_comp, ← Function.comp_app, ← mul_inv_rev, ← map_mul, ← coe_mk, ← mul_apply]

@[simp]
theorem dual_apply (g : G) : (dual ρV) g = Module.Dual.transpose (ρV g⁻¹) :=
  rfl

theorem dual_tensor_hom_comm (g : G) :
    dualTensorHom k V W ∘ₗ TensorProduct.map (ρV.dual g) (ρW g) = (linHom ρV ρW) g ∘ₗ dualTensorHom k V W := by
  ext
  simp [← Module.Dual.transpose_apply]

end LinearHom

end Representation

