/-
Copyright © 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri
-/
import Mathbin.Geometry.Manifold.Algebra.SmoothFunctions
import Mathbin.RingTheory.Derivation

/-!

# Derivation bundle

In this file we define the derivations at a point of a manifold on the algebra of smooth fuctions.
Moreover, we define the differential of a function in terms of derivations.

The content of this file is not meant to be regarded as an alternative definition to the current
tangent bundle but rather as a purely algebraic theory that provides a purely algebraic definition
of the Lie algebra for a Lie group.

-/


variable (𝕜 : Type _) [NondiscreteNormedField 𝕜] {E : Type _} [NormedGroup E] [NormedSpace 𝕜 E] {H : Type _}
  [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) (M : Type _) [TopologicalSpace M] [ChartedSpace H M] (n : WithTop ℕ)

open Manifold

-- the following two instances prevent poorly understood type class inference timeout problems
instance smoothFunctionsAlgebra : Algebra 𝕜 C^∞⟮I, M; 𝕜⟯ := by
  infer_instance

instance smooth_functions_tower : IsScalarTower 𝕜 C^∞⟮I, M; 𝕜⟯ C^∞⟮I, M; 𝕜⟯ := by
  infer_instance

/-- Type synonym, introduced to put a different `has_smul` action on `C^n⟮I, M; 𝕜⟯`
which is defined as `f • r = f(x) * r`. -/
@[nolint unused_arguments]
def PointedSmoothMap (x : M) :=
  C^n⟮I, M; 𝕜⟯

-- mathport name: «exprC^ ⟮ , ; ⟯⟨ ⟩»
localized [Derivation] notation "C^" n "⟮" I "," M ";" 𝕜 "⟯⟨" x "⟩" => PointedSmoothMap 𝕜 I M n x

variable {𝕜 M}

namespace PointedSmoothMap

instance {x : M} : CoeFun C^∞⟮I,M;𝕜⟯⟨x⟩ fun _ => M → 𝕜 :=
  ContMdiffMap.hasCoeToFun

instance {x : M} : CommRingₓ C^∞⟮I,M;𝕜⟯⟨x⟩ :=
  SmoothMap.commRing

instance {x : M} : Algebra 𝕜 C^∞⟮I,M;𝕜⟯⟨x⟩ :=
  SmoothMap.algebra

instance {x : M} : Inhabited C^∞⟮I,M;𝕜⟯⟨x⟩ :=
  ⟨0⟩

instance {x : M} : Algebra C^∞⟮I,M;𝕜⟯⟨x⟩ C^∞⟮I, M; 𝕜⟯ :=
  Algebra.id C^∞⟮I, M; 𝕜⟯

instance {x : M} : IsScalarTower 𝕜 C^∞⟮I,M;𝕜⟯⟨x⟩ C^∞⟮I, M; 𝕜⟯ :=
  IsScalarTower.right

variable {I}

/-- `smooth_map.eval_ring_hom` gives rise to an algebra structure of `C^∞⟮I, M; 𝕜⟯` on `𝕜`. -/
instance evalAlgebra {x : M} : Algebra C^∞⟮I,M;𝕜⟯⟨x⟩ 𝕜 :=
  (SmoothMap.evalRingHom x : C^∞⟮I,M;𝕜⟯⟨x⟩ →+* 𝕜).toAlgebra

/-- With the `eval_algebra` algebra structure evaluation is actually an algebra morphism. -/
def eval (x : M) : C^∞⟮I, M; 𝕜⟯ →ₐ[C^∞⟮I,M;𝕜⟯⟨x⟩] 𝕜 :=
  Algebra.ofId C^∞⟮I,M;𝕜⟯⟨x⟩ 𝕜

theorem smul_def (x : M) (f : C^∞⟮I,M;𝕜⟯⟨x⟩) (k : 𝕜) : f • k = f x * k :=
  rfl

instance (x : M) :
    IsScalarTower 𝕜 C^∞⟮I,M;𝕜⟯⟨x⟩ 𝕜 where smul_assoc := fun k f h => by
    simp only [← smul_def, ← Algebra.id.smul_eq_mul, ← SmoothMap.coe_smul, ← Pi.smul_apply, ← mul_assoc]

end PointedSmoothMap

open Derivation

/-- The derivations at a point of a manifold. Some regard this as a possible definition of the
tangent space -/
@[reducible]
def PointDerivation (x : M) :=
  Derivation 𝕜 C^∞⟮I,M;𝕜⟯⟨x⟩ 𝕜

section

variable (I) {M} (X Y : Derivation 𝕜 C^∞⟮I, M; 𝕜⟯ C^∞⟮I, M; 𝕜⟯) (f g : C^∞⟮I, M; 𝕜⟯) (r : 𝕜)

/-- Evaluation at a point gives rise to a `C^∞⟮I, M; 𝕜⟯`-linear map between `C^∞⟮I, M; 𝕜⟯` and `𝕜`.
 -/
def SmoothFunction.evalAt (x : M) : C^∞⟮I, M; 𝕜⟯ →ₗ[C^∞⟮I,M;𝕜⟯⟨x⟩] 𝕜 :=
  (PointedSmoothMap.eval x).toLinearMap

namespace Derivation

variable {I}

/-- The evaluation at a point as a linear map. -/
def evalAt (x : M) : Derivation 𝕜 C^∞⟮I, M; 𝕜⟯ C^∞⟮I, M; 𝕜⟯ →ₗ[𝕜] PointDerivation I x :=
  (SmoothFunction.evalAt I x).compDer

theorem eval_at_apply (x : M) : evalAt x X f = (X f) x :=
  rfl

end Derivation

variable {I} {E' : Type _} [NormedGroup E'] [NormedSpace 𝕜 E'] {H' : Type _} [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'} {M' : Type _} [TopologicalSpace M'] [ChartedSpace H' M']

/-- The heterogeneous differential as a linear map. Instead of taking a function as an argument this
differential takes `h : f x = y`. It is particularly handy to deal with situations where the points
on where it has to be evaluated are equal but not definitionally equal. -/
def hfdifferential {f : C^∞⟮I, M; I', M'⟯} {x : M} {y : M'} (h : f x = y) :
    PointDerivation I x →ₗ[𝕜] PointDerivation I' y where
  toFun := fun v =>
    Derivation.mk'
      { toFun := fun g => v (g.comp f),
        map_add' := fun g g' => by
          rw [SmoothMap.add_comp, Derivation.map_add],
        map_smul' := fun k g => by
          simp only [← SmoothMap.smul_comp, ← Derivation.map_smul, ← RingHom.id_apply] }
      fun g g' => by
      simp only [← Derivation.leibniz, ← SmoothMap.mul_comp, ← LinearMap.coe_mk, ← PointedSmoothMap.smul_def, ←
        ContMdiffMap.comp_apply, ← h]
  map_smul' := fun k v => rfl
  map_add' := fun v w => rfl

/-- The homogeneous differential as a linear map. -/
def fdifferential (f : C^∞⟮I, M; I', M'⟯) (x : M) : PointDerivation I x →ₗ[𝕜] PointDerivation I' (f x) :=
  hfdifferential (rfl : f x = f x)

-- mathport name: «expr𝒅»
-- Standard notation for the differential. The abbreviation is `MId`.
localized [Manifold] notation "𝒅" => fdifferential

-- mathport name: «expr𝒅ₕ»
-- Standard notation for the differential. The abbreviation is `MId`.
localized [Manifold] notation "𝒅ₕ" => hfdifferential

@[simp]
theorem apply_fdifferential (f : C^∞⟮I, M; I', M'⟯) {x : M} (v : PointDerivation I x) (g : C^∞⟮I', M'; 𝕜⟯) :
    𝒅 f x v g = v (g.comp f) :=
  rfl

@[simp]
theorem apply_hfdifferential {f : C^∞⟮I, M; I', M'⟯} {x : M} {y : M'} (h : f x = y) (v : PointDerivation I x)
    (g : C^∞⟮I', M'; 𝕜⟯) : 𝒅ₕ h v g = 𝒅 f x v g :=
  rfl

variable {E'' : Type _} [NormedGroup E''] [NormedSpace 𝕜 E''] {H'' : Type _} [TopologicalSpace H'']
  {I'' : ModelWithCorners 𝕜 E'' H''} {M'' : Type _} [TopologicalSpace M''] [ChartedSpace H'' M'']

@[simp]
theorem fdifferential_comp (g : C^∞⟮I', M'; I'', M''⟯) (f : C^∞⟮I, M; I', M'⟯) (x : M) :
    𝒅 (g.comp f) x = (𝒅 g (f x)).comp (𝒅 f x) :=
  rfl

end

