/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathbin.Algebra.Lie.Basic
import Mathbin.Algebra.Lie.Subalgebra
import Mathbin.Algebra.Lie.Submodule
import Mathbin.Algebra.Algebra.Subalgebra.Basic

/-!
# Lie algebras of associative algebras

This file defines the Lie algebra structure that arises on an associative algebra via the ring
commutator.

Since the linear endomorphisms of a Lie algebra form an associative algebra, one can define the
adjoint action as a morphism of Lie algebras from a Lie algebra to its linear endomorphisms. We
make such a definition in this file.

## Main definitions

 * `lie_algebra.of_associative_algebra`
 * `lie_algebra.of_associative_algebra_hom`
 * `lie_module.to_endomorphism`
 * `lie_algebra.ad`
 * `linear_equiv.lie_conj`
 * `alg_equiv.to_lie_equiv`

## Tags

lie algebra, ring commutator, adjoint action
-/


universe u v w w₁ w₂

section OfAssociative

variable {A : Type v} [Ringₓ A]

namespace Ringₓ

/-- The bracket operation for rings is the ring commutator, which captures the extent to which a
ring is commutative. It is identically zero exactly when the ring is commutative. -/
instance (priority := 100) : HasBracket A A :=
  ⟨fun x y => x * y - y * x⟩

theorem lie_def (x y : A) : ⁅x,y⁆ = x * y - y * x :=
  rfl

end Ringₓ

namespace LieRing

/-- An associative ring gives rise to a Lie ring by taking the bracket to be the ring commutator. -/
instance (priority := 100) ofAssociativeRing : LieRing A where
  add_lie := by
    simp only [← Ringₓ.lie_def, ← right_distrib, ← left_distrib, ← sub_eq_add_neg, ← add_commₓ, ← add_left_commₓ, ←
      forall_const, ← eq_self_iff_true, ← neg_add_rev]
  lie_add := by
    simp only [← Ringₓ.lie_def, ← right_distrib, ← left_distrib, ← sub_eq_add_neg, ← add_commₓ, ← add_left_commₓ, ←
      forall_const, ← eq_self_iff_true, ← neg_add_rev]
  lie_self := by
    simp only [← Ringₓ.lie_def, ← forall_const, ← sub_self]
  leibniz_lie := fun x y z => by
    repeat'
      rw [Ringₓ.lie_def]
    noncomm_ring

theorem of_associative_ring_bracket (x y : A) : ⁅x,y⁆ = x * y - y * x :=
  rfl

@[simp]
theorem lie_apply {α : Type _} (f g : α → A) (a : α) : ⁅f,g⁆ a = ⁅f a,g a⁆ :=
  rfl

end LieRing

section AssociativeModule

variable {M : Type w} [AddCommGroupₓ M] [Module A M]

/-- We can regard a module over an associative ring `A` as a Lie ring module over `A` with Lie
bracket equal to its ring commutator.

Note that this cannot be a global instance because it would create a diamond when `M = A`,
specifically we can build two mathematically-different `has_bracket A A`s:
 1. `@ring.has_bracket A _` which says `⁅a, b⁆ = a * b - b * a`
 2. `(@lie_ring_module.of_associative_module A _ A _ _).to_has_bracket` which says `⁅a, b⁆ = a • b`
    (and thus `⁅a, b⁆ = a * b`)

See note [reducible non-instances] -/
@[reducible]
def LieRingModule.ofAssociativeModule : LieRingModule A M where
  bracket := (· • ·)
  add_lie := add_smul
  lie_add := smul_add
  leibniz_lie := by
    simp [← LieRing.of_associative_ring_bracket, ← sub_smul, ← mul_smul, ← sub_add_cancel]

attribute [local instance] LieRingModule.ofAssociativeModule

theorem lie_eq_smul (a : A) (m : M) : ⁅a,m⁆ = a • m :=
  rfl

end AssociativeModule

section LieAlgebra

variable {R : Type u} [CommRingₓ R] [Algebra R A]

/-- An associative algebra gives rise to a Lie algebra by taking the bracket to be the ring
commutator. -/
instance (priority := 100) LieAlgebra.ofAssociativeAlgebra :
    LieAlgebra R A where lie_smul := fun t x y => by
    rw [LieRing.of_associative_ring_bracket, LieRing.of_associative_ring_bracket, Algebra.mul_smul_comm,
      Algebra.smul_mul_assoc, smul_sub]

attribute [local instance] LieRingModule.ofAssociativeModule

section AssociativeRepresentation

variable {M : Type w} [AddCommGroupₓ M] [Module R M] [Module A M] [IsScalarTower R A M]

/-- A representation of an associative algebra `A` is also a representation of `A`, regarded as a
Lie algebra via the ring commutator.

See the comment at `lie_ring_module.of_associative_module` for why the possibility `M = A` means
this cannot be a global instance. -/
def LieModule.ofAssociativeModule : LieModule R A M where
  smul_lie := smul_assoc
  lie_smul := smul_algebra_smul_comm

instance Module.End.lieRingModule : LieRingModule (Module.End R M) M :=
  LieRingModule.ofAssociativeModule

instance Module.End.lieModule : LieModule R (Module.End R M) M :=
  LieModule.ofAssociativeModule

end AssociativeRepresentation

namespace AlgHom

variable {B : Type w} {C : Type w₁} [Ringₓ B] [Ringₓ C] [Algebra R B] [Algebra R C]

variable (f : A →ₐ[R] B) (g : B →ₐ[R] C)

/-- The map `of_associative_algebra` associating a Lie algebra to an associative algebra is
functorial. -/
def toLieHom : A →ₗ⁅R⁆ B :=
  { f.toLinearMap with
    map_lie' := fun x y =>
      show f ⁅x,y⁆ = ⁅f x,f y⁆ by
        simp only [← LieRing.of_associative_ring_bracket, ← AlgHom.map_sub, ← AlgHom.map_mul] }

instance : Coe (A →ₐ[R] B) (A →ₗ⁅R⁆ B) :=
  ⟨toLieHom⟩

@[simp]
theorem to_lie_hom_coe : f.toLieHom = ↑f :=
  rfl

@[simp]
theorem coe_to_lie_hom : ((f : A →ₗ⁅R⁆ B) : A → B) = f :=
  rfl

theorem to_lie_hom_apply (x : A) : f.toLieHom x = f x :=
  rfl

@[simp]
theorem to_lie_hom_id : (AlgHom.id R A : A →ₗ⁅R⁆ A) = LieHom.id :=
  rfl

@[simp]
theorem to_lie_hom_comp : (g.comp f : A →ₗ⁅R⁆ C) = (g : B →ₗ⁅R⁆ C).comp (f : A →ₗ⁅R⁆ B) :=
  rfl

theorem to_lie_hom_injective {f g : A →ₐ[R] B} (h : (f : A →ₗ⁅R⁆ B) = (g : A →ₗ⁅R⁆ B)) : f = g := by
  ext a
  exact LieHom.congr_fun h a

end AlgHom

end LieAlgebra

end OfAssociative

section AdjointAction

variable (R : Type u) (L : Type v) (M : Type w)

variable [CommRingₓ R] [LieRing L] [LieAlgebra R L] [AddCommGroupₓ M] [Module R M]

variable [LieRingModule L M] [LieModule R L M]

/-- A Lie module yields a Lie algebra morphism into the linear endomorphisms of the module.

See also `lie_module.to_module_hom`. -/
@[simps]
def LieModule.toEndomorphism : L →ₗ⁅R⁆ Module.End R M where
  toFun := fun x => { toFun := fun m => ⁅x,m⁆, map_add' := lie_add x, map_smul' := fun t => lie_smul t x }
  map_add' := fun x y => by
    ext m
    apply add_lie
  map_smul' := fun t x => by
    ext m
    apply smul_lie
  map_lie' := fun x y => by
    ext m
    apply lie_lie

/-- The adjoint action of a Lie algebra on itself. -/
def LieAlgebra.ad : L →ₗ⁅R⁆ Module.End R L :=
  LieModule.toEndomorphism R L L

@[simp]
theorem LieAlgebra.ad_apply (x y : L) : LieAlgebra.ad R L x y = ⁅x,y⁆ :=
  rfl

@[simp]
theorem LieModule.to_endomorphism_module_End : LieModule.toEndomorphism R (Module.End R M) M = LieHom.id := by
  ext g m
  simp [← lie_eq_smul]

theorem LieSubalgebra.to_endomorphism_eq (K : LieSubalgebra R L) {x : K} :
    LieModule.toEndomorphism R K M x = LieModule.toEndomorphism R L M x :=
  rfl

@[simp]
theorem LieSubalgebra.to_endomorphism_mk (K : LieSubalgebra R L) {x : L} (hx : x ∈ K) :
    LieModule.toEndomorphism R K M ⟨x, hx⟩ = LieModule.toEndomorphism R L M x :=
  rfl

variable {R L M}

namespace LieSubmodule

open LieModule

variable {N : LieSubmodule R L M} {x : L}

theorem coe_map_to_endomorphism_le : (N : Submodule R M).map (LieModule.toEndomorphism R L M x) ≤ N := by
  rintro n ⟨m, hm, rfl⟩
  exact N.lie_mem hm

variable (N x)

theorem to_endomorphism_comp_subtype_mem (m : M) (hm : m ∈ N) :
    (toEndomorphism R L M x).comp (N : Submodule R M).Subtype ⟨m, hm⟩ ∈ N := by
  simpa using N.lie_mem hm

@[simp]
theorem to_endomorphism_restrict_eq_to_endomorphism (h := N.to_endomorphism_comp_subtype_mem x) :
    ((toEndomorphism R L M x).restrict h : N →ₗ[R] N) = toEndomorphism R L N x := by
  ext
  simp [← LinearMap.restrict_apply]

end LieSubmodule

open LieAlgebra

theorem LieAlgebra.ad_eq_lmul_left_sub_lmul_right (A : Type v) [Ringₓ A] [Algebra R A] :
    (ad R A : A → Module.End R A) = Algebra.lmulLeft R - Algebra.lmulRight R := by
  ext a b
  simp [← LieRing.of_associative_ring_bracket]

theorem LieSubalgebra.ad_comp_incl_eq (K : LieSubalgebra R L) (x : K) :
    (ad R L ↑x).comp (K.incl : K →ₗ[R] L) = (K.incl : K →ₗ[R] L).comp (ad R K x) := by
  ext y
  simp only [← ad_apply, ← LieHom.coe_to_linear_map, ← LieSubalgebra.coe_incl, ← LinearMap.coe_comp, ←
    LieSubalgebra.coe_bracket, ← Function.comp_app]

end AdjointAction

/-- A subalgebra of an associative algebra is a Lie subalgebra of the associated Lie algebra. -/
def lieSubalgebraOfSubalgebra (R : Type u) [CommRingₓ R] (A : Type v) [Ringₓ A] [Algebra R A] (A' : Subalgebra R A) :
    LieSubalgebra R A :=
  { A'.toSubmodule with
    lie_mem' := fun x y hx hy => by
      change ⁅x,y⁆ ∈ A'
      change x ∈ A' at hx
      change y ∈ A' at hy
      rw [LieRing.of_associative_ring_bracket]
      have hxy := A'.mul_mem hx hy
      have hyx := A'.mul_mem hy hx
      exact Submodule.sub_mem A'.to_submodule hxy hyx }

namespace LinearEquiv

variable {R : Type u} {M₁ : Type v} {M₂ : Type w}

variable [CommRingₓ R] [AddCommGroupₓ M₁] [Module R M₁] [AddCommGroupₓ M₂] [Module R M₂]

variable (e : M₁ ≃ₗ[R] M₂)

/-- A linear equivalence of two modules induces a Lie algebra equivalence of their endomorphisms. -/
def lieConj : Module.End R M₁ ≃ₗ⁅R⁆ Module.End R M₂ :=
  { e.conj with
    map_lie' := fun f g =>
      show e.conj ⁅f,g⁆ = ⁅e.conj f,e.conj g⁆ by
        simp only [← LieRing.of_associative_ring_bracket, ← LinearMap.mul_eq_comp, ← e.conj_comp, ←
          LinearEquiv.map_sub] }

@[simp]
theorem lie_conj_apply (f : Module.End R M₁) : e.lieConj f = e.conj f :=
  rfl

@[simp]
theorem lie_conj_symm : e.lieConj.symm = e.symm.lieConj :=
  rfl

end LinearEquiv

namespace AlgEquiv

variable {R : Type u} {A₁ : Type v} {A₂ : Type w}

variable [CommRingₓ R] [Ringₓ A₁] [Ringₓ A₂] [Algebra R A₁] [Algebra R A₂]

variable (e : A₁ ≃ₐ[R] A₂)

/-- An equivalence of associative algebras is an equivalence of associated Lie algebras. -/
def toLieEquiv : A₁ ≃ₗ⁅R⁆ A₂ :=
  { e.toLinearEquiv with toFun := e.toFun,
    map_lie' := fun x y => by
      simp [← LieRing.of_associative_ring_bracket] }

@[simp]
theorem to_lie_equiv_apply (x : A₁) : e.toLieEquiv x = e x :=
  rfl

@[simp]
theorem to_lie_equiv_symm_apply (x : A₂) : e.toLieEquiv.symm x = e.symm x :=
  rfl

end AlgEquiv

