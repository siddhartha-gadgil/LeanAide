/-
Copyright © 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri
-/
import Mathbin.Geometry.Manifold.Algebra.Structures

/-!
# Algebraic structures over smooth functions

In this file, we define instances of algebraic structures over smooth functions.
-/


noncomputable section

open Manifold

variable {𝕜 : Type _} [NondiscreteNormedField 𝕜] {E : Type _} [NormedGroup E] [NormedSpace 𝕜 E] {E' : Type _}
  [NormedGroup E'] [NormedSpace 𝕜 E'] {H : Type _} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {H' : Type _}
  [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'} {N : Type _} [TopologicalSpace N] [ChartedSpace H N]
  {E'' : Type _} [NormedGroup E''] [NormedSpace 𝕜 E''] {H'' : Type _} [TopologicalSpace H'']
  {I'' : ModelWithCorners 𝕜 E'' H''} {N' : Type _} [TopologicalSpace N'] [ChartedSpace H'' N']

namespace SmoothMap

@[to_additive]
instance hasMul {G : Type _} [Mul G] [TopologicalSpace G] [ChartedSpace H' G] [HasSmoothMul I' G] :
    Mul C^∞⟮I, N; I', G⟯ :=
  ⟨fun f g => ⟨f * g, f.Smooth.mul g.Smooth⟩⟩

@[simp, to_additive]
theorem coe_mul {G : Type _} [Mul G] [TopologicalSpace G] [ChartedSpace H' G] [HasSmoothMul I' G]
    (f g : C^∞⟮I, N; I', G⟯) : ⇑(f * g) = f * g :=
  rfl

@[simp, to_additive]
theorem mul_comp {G : Type _} [Mul G] [TopologicalSpace G] [ChartedSpace H' G] [HasSmoothMul I' G]
    (f g : C^∞⟮I'', N'; I', G⟯) (h : C^∞⟮I, N; I'', N'⟯) : (f * g).comp h = f.comp h * g.comp h := by
  ext <;> simp only [← ContMdiffMap.comp_apply, ← coe_mul, ← Pi.mul_apply]

@[to_additive]
instance hasOne {G : Type _} [Monoidₓ G] [TopologicalSpace G] [ChartedSpace H' G] : One C^∞⟮I, N; I', G⟯ :=
  ⟨ContMdiffMap.const (1 : G)⟩

@[simp, to_additive]
theorem coe_one {G : Type _} [Monoidₓ G] [TopologicalSpace G] [ChartedSpace H' G] : ⇑(1 : C^∞⟮I, N; I', G⟯) = 1 :=
  rfl

section GroupStructure

/-!
### Group structure

In this section we show that smooth functions valued in a Lie group inherit a group structure
under pointwise multiplication.
-/


@[to_additive]
instance semigroup {G : Type _} [Semigroupₓ G] [TopologicalSpace G] [ChartedSpace H' G] [HasSmoothMul I' G] :
    Semigroupₓ C^∞⟮I, N; I', G⟯ :=
  { SmoothMap.hasMul with
    mul_assoc := fun a b c => by
      ext <;> exact mul_assoc _ _ _ }

@[to_additive]
instance monoid {G : Type _} [Monoidₓ G] [TopologicalSpace G] [ChartedSpace H' G] [HasSmoothMul I' G] :
    Monoidₓ C^∞⟮I, N; I', G⟯ :=
  { SmoothMap.semigroup, SmoothMap.hasOne with
    one_mul := fun a => by
      ext <;> exact one_mulₓ _,
    mul_one := fun a => by
      ext <;> exact mul_oneₓ _ }

/-- Coercion to a function as an `monoid_hom`. Similar to `monoid_hom.coe_fn`. -/
@[to_additive "Coercion to a function as an `add_monoid_hom`. Similar to `add_monoid_hom.coe_fn`.", simps]
def coeFnMonoidHom {G : Type _} [Monoidₓ G] [TopologicalSpace G] [ChartedSpace H' G] [HasSmoothMul I' G] :
    C^∞⟮I, N; I', G⟯ →* N → G where
  toFun := coeFn
  map_one' := coe_one
  map_mul' := coe_mul

@[to_additive]
instance commMonoid {G : Type _} [CommMonoidₓ G] [TopologicalSpace G] [ChartedSpace H' G] [HasSmoothMul I' G] :
    CommMonoidₓ C^∞⟮I, N; I', G⟯ :=
  { SmoothMap.monoid, SmoothMap.hasOne with
    mul_comm := fun a b => by
      ext <;> exact mul_comm _ _ }

@[to_additive]
instance group {G : Type _} [Groupₓ G] [TopologicalSpace G] [ChartedSpace H' G] [LieGroup I' G] :
    Groupₓ C^∞⟮I, N; I', G⟯ :=
  { SmoothMap.monoid with inv := fun f => ⟨fun x => (f x)⁻¹, f.Smooth.inv⟩,
    mul_left_inv := fun a => by
      ext <;> exact mul_left_invₓ _,
    div := fun f g => ⟨f / g, f.Smooth.div g.Smooth⟩,
    div_eq_mul_inv := fun f g => by
      ext <;> exact div_eq_mul_inv _ _ }

@[simp, to_additive]
theorem coe_inv {G : Type _} [Groupₓ G] [TopologicalSpace G] [ChartedSpace H' G] [LieGroup I' G]
    (f : C^∞⟮I, N; I', G⟯) : ⇑f⁻¹ = f⁻¹ :=
  rfl

@[simp, to_additive]
theorem coe_div {G : Type _} [Groupₓ G] [TopologicalSpace G] [ChartedSpace H' G] [LieGroup I' G]
    (f g : C^∞⟮I, N; I', G⟯) : ⇑(f / g) = f / g :=
  rfl

@[to_additive]
instance commGroup {G : Type _} [CommGroupₓ G] [TopologicalSpace G] [ChartedSpace H' G] [LieGroup I' G] :
    CommGroupₓ C^∞⟮I, N; I', G⟯ :=
  { SmoothMap.group, SmoothMap.commMonoid with }

end GroupStructure

section RingStructure

/-!
### Ring stucture

In this section we show that smooth functions valued in a smooth ring `R` inherit a ring structure
under pointwise multiplication.
-/


instance semiring {R : Type _} [Semiringₓ R] [TopologicalSpace R] [ChartedSpace H' R] [SmoothRing I' R] :
    Semiringₓ C^∞⟮I, N; I', R⟯ :=
  { SmoothMap.addCommMonoid, SmoothMap.monoid with
    left_distrib := fun a b c => by
      ext <;> exact left_distrib _ _ _,
    right_distrib := fun a b c => by
      ext <;> exact right_distrib _ _ _,
    zero_mul := fun a => by
      ext <;> exact zero_mul _,
    mul_zero := fun a => by
      ext <;> exact mul_zero _ }

instance ring {R : Type _} [Ringₓ R] [TopologicalSpace R] [ChartedSpace H' R] [SmoothRing I' R] :
    Ringₓ C^∞⟮I, N; I', R⟯ :=
  { SmoothMap.semiring, SmoothMap.addCommGroup with }

instance commRing {R : Type _} [CommRingₓ R] [TopologicalSpace R] [ChartedSpace H' R] [SmoothRing I' R] :
    CommRingₓ C^∞⟮I, N; I', R⟯ :=
  { SmoothMap.semiring, SmoothMap.addCommGroup, SmoothMap.commMonoid with }

/-- Coercion to a function as a `ring_hom`. -/
@[simps]
def coeFnRingHom {R : Type _} [CommRingₓ R] [TopologicalSpace R] [ChartedSpace H' R] [SmoothRing I' R] :
    C^∞⟮I, N; I', R⟯ →+* N → R :=
  { (coeFnMonoidHom : C^∞⟮I, N; I', R⟯ →* _), (coeFnAddMonoidHom : C^∞⟮I, N; I', R⟯ →+ _) with toFun := coeFn }

/-- `function.eval` as a `ring_hom` on the ring of smooth functions. -/
def evalRingHom {R : Type _} [CommRingₓ R] [TopologicalSpace R] [ChartedSpace H' R] [SmoothRing I' R] (n : N) :
    C^∞⟮I, N; I', R⟯ →+* R :=
  (Pi.evalRingHom _ n : (N → R) →+* R).comp SmoothMap.coeFnRingHom

end RingStructure

section ModuleStructure

/-!
### Semiodule stucture

In this section we show that smooth functions valued in a vector space `M` over a normed
field `𝕜` inherit a vector space structure.
-/


instance hasSmul {V : Type _} [NormedGroup V] [NormedSpace 𝕜 V] : HasSmul 𝕜 C^∞⟮I, N; 𝓘(𝕜, V), V⟯ :=
  ⟨fun r f => ⟨r • f, smooth_const.smul f.Smooth⟩⟩

@[simp]
theorem coe_smul {V : Type _} [NormedGroup V] [NormedSpace 𝕜 V] (r : 𝕜) (f : C^∞⟮I, N; 𝓘(𝕜, V), V⟯) :
    ⇑(r • f) = r • f :=
  rfl

@[simp]
theorem smul_comp {V : Type _} [NormedGroup V] [NormedSpace 𝕜 V] (r : 𝕜) (g : C^∞⟮I'', N'; 𝓘(𝕜, V), V⟯)
    (h : C^∞⟮I, N; I'', N'⟯) : (r • g).comp h = r • g.comp h :=
  rfl

instance module {V : Type _} [NormedGroup V] [NormedSpace 𝕜 V] : Module 𝕜 C^∞⟮I, N; 𝓘(𝕜, V), V⟯ :=
  Function.Injective.module 𝕜 coeFnAddMonoidHom ContMdiffMap.coe_inj coe_smul

/-- Coercion to a function as a `linear_map`. -/
@[simps]
def coeFnLinearMap {V : Type _} [NormedGroup V] [NormedSpace 𝕜 V] : C^∞⟮I, N; 𝓘(𝕜, V), V⟯ →ₗ[𝕜] N → V :=
  { (coeFnAddMonoidHom : C^∞⟮I, N; 𝓘(𝕜, V), V⟯ →+ _) with toFun := coeFn, map_smul' := coe_smul }

end ModuleStructure

section AlgebraStructure

/-!
### Algebra structure

In this section we show that smooth functions valued in a normed algebra `A` over a normed field `𝕜`
inherit an algebra structure.
-/


variable {A : Type _} [NormedRing A] [NormedAlgebra 𝕜 A] [SmoothRing 𝓘(𝕜, A) A]

/-- Smooth constant functions as a `ring_hom`. -/
def c : 𝕜 →+* C^∞⟮I, N; 𝓘(𝕜, A), A⟯ where
  toFun := fun c : 𝕜 => ⟨fun x => (algebraMap 𝕜 A) c, smooth_const⟩
  map_one' := by
    ext x <;> exact (algebraMap 𝕜 A).map_one
  map_mul' := fun c₁ c₂ => by
    ext x <;> exact (algebraMap 𝕜 A).map_mul _ _
  map_zero' := by
    ext x <;> exact (algebraMap 𝕜 A).map_zero
  map_add' := fun c₁ c₂ => by
    ext x <;> exact (algebraMap 𝕜 A).map_add _ _

instance algebra : Algebra 𝕜 C^∞⟮I, N; 𝓘(𝕜, A), A⟯ :=
  { SmoothMap.semiring with smul := fun r f => ⟨r • f, smooth_const.smul f.Smooth⟩, toRingHom := SmoothMap.c,
    commutes' := fun c f => by
      ext x <;> exact Algebra.commutes' _ _,
    smul_def' := fun c f => by
      ext x <;> exact Algebra.smul_def' _ _ }

/-- Coercion to a function as an `alg_hom`. -/
@[simps]
def coeFnAlgHom : C^∞⟮I, N; 𝓘(𝕜, A), A⟯ →ₐ[𝕜] N → A where
  toFun := coeFn
  commutes' := fun r => rfl
  -- `..(smooth_map.coe_fn_ring_hom : C^∞⟮I, N; 𝓘(𝕜, A), A⟯ →+* _)` times out for some reason
  map_zero' := SmoothMap.coe_zero
  map_one' := SmoothMap.coe_one
  map_add' := SmoothMap.coe_add
  map_mul' := SmoothMap.coe_mul

end AlgebraStructure

section ModuleOverContinuousFunctions

/-!
### Structure as module over scalar functions

If `V` is a module over `𝕜`, then we show that the space of smooth functions from `N` to `V`
is naturally a vector space over the ring of smooth functions from `N` to `𝕜`. -/


instance hasSmul' {V : Type _} [NormedGroup V] [NormedSpace 𝕜 V] : HasSmul C^∞⟮I, N; 𝕜⟯ C^∞⟮I, N; 𝓘(𝕜, V), V⟯ :=
  ⟨fun f g => ⟨fun x => f x • g x, Smooth.smul f.2 g.2⟩⟩

@[simp]
theorem smul_comp' {V : Type _} [NormedGroup V] [NormedSpace 𝕜 V] (f : C^∞⟮I'', N'; 𝕜⟯) (g : C^∞⟮I'', N'; 𝓘(𝕜, V), V⟯)
    (h : C^∞⟮I, N; I'', N'⟯) : (f • g).comp h = f.comp h • g.comp h :=
  rfl

instance module' {V : Type _} [NormedGroup V] [NormedSpace 𝕜 V] : Module C^∞⟮I, N; 𝓘(𝕜), 𝕜⟯ C^∞⟮I, N; 𝓘(𝕜, V), V⟯ where
  smul := (· • ·)
  smul_add := fun c f g => by
    ext x <;> exact smul_add (c x) (f x) (g x)
  add_smul := fun c₁ c₂ f => by
    ext x <;> exact add_smul (c₁ x) (c₂ x) (f x)
  mul_smul := fun c₁ c₂ f => by
    ext x <;> exact mul_smul (c₁ x) (c₂ x) (f x)
  one_smul := fun f => by
    ext x <;> exact one_smul 𝕜 (f x)
  zero_smul := fun f => by
    ext x <;> exact zero_smul _ _
  smul_zero := fun r => by
    ext x <;> exact smul_zero _

end ModuleOverContinuousFunctions

end SmoothMap

