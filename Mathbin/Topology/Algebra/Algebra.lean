/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.Algebra.Algebra.Subalgebra.Basic
import Mathbin.Topology.Algebra.Module.Basic
import Mathbin.Topology.Algebra.Field

/-!
# Topological (sub)algebras

A topological algebra over a topological semiring `R` is a topological semiring with a compatible
continuous scalar multiplication by elements of `R`. We reuse typeclass `has_continuous_smul` for
topological algebras.

## Results

This is just a minimal stub for now!

The topological closure of a subalgebra is still a subalgebra,
which as an algebra is a topological algebra.
-/


open Classical Set TopologicalSpace Algebra

open Classical

universe u v w

section TopologicalAlgebra

variable (R : Type _) [TopologicalSpace R] [CommSemiringₓ R]

variable (A : Type u) [TopologicalSpace A]

variable [Semiringₓ A]

theorem continuous_algebra_map_iff_smul [Algebra R A] [TopologicalSemiring A] :
    Continuous (algebraMap R A) ↔ Continuous fun p : R × A => p.1 • p.2 := by
  refine' ⟨fun h => _, fun h => _⟩
  · simp only [← Algebra.smul_def]
    exact (h.comp continuous_fst).mul continuous_snd
    
  · rw [algebra_map_eq_smul_one']
    exact h.comp (continuous_id.prod_mk continuous_const)
    

@[continuity]
theorem continuous_algebra_map [Algebra R A] [TopologicalSemiring A] [HasContinuousSmul R A] :
    Continuous (algebraMap R A) :=
  (continuous_algebra_map_iff_smul R A).2 continuous_smul

theorem has_continuous_smul_of_algebra_map [Algebra R A] [TopologicalSemiring A] (h : Continuous (algebraMap R A)) :
    HasContinuousSmul R A :=
  ⟨(continuous_algebra_map_iff_smul R A).1 h⟩

end TopologicalAlgebra

section TopologicalAlgebra

variable {R : Type _} [CommSemiringₓ R]

variable {A : Type u} [TopologicalSpace A]

variable [Semiringₓ A]

variable [Algebra R A] [TopologicalSemiring A]

/-- The closure of a subalgebra in a topological algebra as a subalgebra. -/
def Subalgebra.topologicalClosure (s : Subalgebra R A) : Subalgebra R A :=
  { s.toSubsemiring.topologicalClosure with Carrier := Closure (s : Set A),
    algebra_map_mem' := fun r => s.toSubsemiring.subring_topological_closure (s.algebra_map_mem r) }

@[simp]
theorem Subalgebra.topological_closure_coe (s : Subalgebra R A) :
    (s.topologicalClosure : Set A) = Closure (s : Set A) :=
  rfl

instance Subalgebra.topological_closure_topological_semiring (s : Subalgebra R A) :
    TopologicalSemiring s.topologicalClosure :=
  s.toSubsemiring.topological_closure_topological_semiring

instance Subalgebra.topological_closure_topological_algebra [TopologicalSpace R] [HasContinuousSmul R A]
    (s : Subalgebra R A) : HasContinuousSmul R s.topologicalClosure :=
  s.toSubmodule.topological_closure_has_continuous_smul

theorem Subalgebra.subalgebra_topological_closure (s : Subalgebra R A) : s ≤ s.topologicalClosure :=
  subset_closure

theorem Subalgebra.is_closed_topological_closure (s : Subalgebra R A) : IsClosed (s.topologicalClosure : Set A) := by
  convert is_closed_closure

theorem Subalgebra.topological_closure_minimal (s : Subalgebra R A) {t : Subalgebra R A} (h : s ≤ t)
    (ht : IsClosed (t : Set A)) : s.topologicalClosure ≤ t :=
  closure_minimal h ht

/-- If a subalgebra of a topological algebra is commutative, then so is its topological closure. -/
def Subalgebra.commSemiringTopologicalClosure [T2Space A] (s : Subalgebra R A) (hs : ∀ x y : s, x * y = y * x) :
    CommSemiringₓ s.topologicalClosure :=
  { s.topologicalClosure.toSemiring, s.toSubmonoid.commMonoidTopologicalClosure hs with }

/-- This is really a statement about topological algebra isomorphisms,
but we don't have those, so we use the clunky approach of talking about
an algebra homomorphism, and a separate homeomorphism,
along with a witness that as functions they are the same.
-/
theorem Subalgebra.topological_closure_comap_homeomorph (s : Subalgebra R A) {B : Type _} [TopologicalSpace B] [Ringₓ B]
    [TopologicalRing B] [Algebra R B] (f : B →ₐ[R] A) (f' : B ≃ₜ A) (w : (f : B → A) = f') :
    s.topologicalClosure.comap f = (s.comap f).topologicalClosure := by
  apply SetLike.ext'
  simp only [← Subalgebra.topological_closure_coe]
  simp only [← Subalgebra.coe_comap, ← Subsemiring.coe_comap, ← AlgHom.coe_to_ring_hom]
  rw [w]
  exact f'.preimage_closure _

end TopologicalAlgebra

section Ringₓ

variable {R : Type _} [CommRingₓ R]

variable {A : Type u} [TopologicalSpace A]

variable [Ringₓ A]

variable [Algebra R A] [TopologicalRing A]

/-- If a subalgebra of a topological algebra is commutative, then so is its topological closure.
See note [reducible non-instances]. -/
@[reducible]
def Subalgebra.commRingTopologicalClosure [T2Space A] (s : Subalgebra R A) (hs : ∀ x y : s, x * y = y * x) :
    CommRingₓ s.topologicalClosure :=
  { s.topologicalClosure.toRing, s.toSubmonoid.commMonoidTopologicalClosure hs with }

variable (R)

/-- The topological closure of the subalgebra generated by a single element. -/
def Algebra.elementalAlgebra (x : A) : Subalgebra R A :=
  (Algebra.adjoin R ({x} : Set A)).topologicalClosure

theorem Algebra.self_mem_elemental_algebra (x : A) : x ∈ Algebra.elementalAlgebra R x :=
  SetLike.le_def.mp (Subalgebra.subalgebra_topological_closure (Algebra.adjoin R ({x} : Set A))) <|
    Algebra.self_mem_adjoin_singleton R x

variable {R}

instance [T2Space A] {x : A} : CommRingₓ (Algebra.elementalAlgebra R x) :=
  Subalgebra.commRingTopologicalClosure _
    (by
      let this : CommRingₓ (Algebra.adjoin R ({x} : Set A)) :=
        Algebra.adjoinCommRingOfComm R fun y hy z hz => by
          rw [mem_singleton_iff] at hy hz
          rw [hy, hz]
      exact fun _ _ => mul_comm _ _)

end Ringₓ

section DivisionRing

/-- The action induced by `algebra_rat` is continuous. -/
instance DivisionRing.has_continuous_const_smul_rat {A} [DivisionRing A] [TopologicalSpace A] [HasContinuousMul A]
    [CharZero A] : HasContinuousConstSmul ℚ A :=
  ⟨fun r => continuous_const.mul continuous_id⟩

end DivisionRing

