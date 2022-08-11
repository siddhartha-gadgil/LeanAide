/-
Copyright (c) 2022 Antoine Labelle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Labelle
-/
import Mathbin.RepresentationTheory.Basic
import Mathbin.RepresentationTheory.Rep

/-!
# Subspace of invariants a group representation

This file introduces the subspace of invariants of a group representation
and proves basic results about it.
The main tool used is the average of all elements of the group, seen as an element of
`monoid_algebra k G`. The action of this special element gives a projection onto the
subspace of invariants.
In order for the definition of the average element to make sense, we need to assume for most of the
results that the order of `G` is invertible in `k` (e. g. `k` has characteristic `0`).
-/


open BigOperators

open MonoidAlgebra

open Representation

namespace GroupAlgebra

variable (k G : Type _) [CommSemiringₓ k] [Groupₓ G]

variable [Fintype G] [Invertible (Fintype.card G : k)]

/-- The average of all elements of the group `G`, considered as an element of `monoid_algebra k G`.
-/
noncomputable def average : MonoidAlgebra k G :=
  ⅟ (Fintype.card G : k) • ∑ g : G, of k G g

/-- `average k G` is invariant under left multiplication by elements of `G`.
-/
@[simp]
theorem mul_average_left (g : G) : (Finsupp.single g 1 * average k G : MonoidAlgebra k G) = average k G := by
  simp only [← mul_oneₓ, ← Finset.mul_sum, ← Algebra.mul_smul_comm, ← average, ← MonoidAlgebra.of_apply, ←
    Finset.sum_congr, ← MonoidAlgebra.single_mul_single]
  set f : G → MonoidAlgebra k G := fun x => Finsupp.single x 1
  show (⅟ ↑(Fintype.card G) • ∑ x : G, f (g * x)) = ⅟ ↑(Fintype.card G) • ∑ x : G, f x
  rw [Function.Bijective.sum_comp (Groupₓ.mul_left_bijective g) _]

/-- `average k G` is invariant under right multiplication by elements of `G`.
-/
@[simp]
theorem mul_average_right (g : G) : average k G * Finsupp.single g 1 = average k G := by
  simp only [← mul_oneₓ, ← Finset.sum_mul, ← Algebra.smul_mul_assoc, ← average, ← MonoidAlgebra.of_apply, ←
    Finset.sum_congr, ← MonoidAlgebra.single_mul_single]
  set f : G → MonoidAlgebra k G := fun x => Finsupp.single x 1
  show (⅟ ↑(Fintype.card G) • ∑ x : G, f (x * g)) = ⅟ ↑(Fintype.card G) • ∑ x : G, f x
  rw [Function.Bijective.sum_comp (Groupₓ.mul_right_bijective g) _]

end GroupAlgebra

namespace Representation

section Invariants

open GroupAlgebra

variable {k G V : Type _} [CommSemiringₓ k] [Groupₓ G] [AddCommMonoidₓ V] [Module k V]

variable (ρ : Representation k G V)

/-- The subspace of invariants, consisting of the vectors fixed by all elements of `G`.
-/
def invariants : Submodule k V where
  Carrier := SetOf fun v => ∀ g : G, ρ g v = v
  zero_mem' := fun g => by
    simp only [← map_zero]
  add_mem' := fun v w hv hw g => by
    simp only [← hv g, ← hw g, ← map_add]
  smul_mem' := fun r v hv g => by
    simp only [← hv g, ← LinearMap.map_smulₛₗ, ← RingHom.id_apply]

@[simp]
theorem mem_invariants (v : V) : v ∈ invariants ρ ↔ ∀ g : G, ρ g v = v := by
  rfl

theorem invariants_eq_inter : (invariants ρ).Carrier = ⋂ g : G, Function.FixedPoints (ρ g) := by
  ext
  simp [← Function.IsFixedPt]

variable [Fintype G] [Invertible (Fintype.card G : k)]

/-- The action of `average k G` gives a projection map onto the subspace of invariants.
-/
@[simp]
noncomputable def averageMap : V →ₗ[k] V :=
  asAlgebraHom ρ (average k G)

/-- The `average_map` sends elements of `V` to the subspace of invariants.
-/
theorem average_map_invariant (v : V) : averageMap ρ v ∈ invariants ρ := fun g => by
  rw [average_map, ← as_algebra_hom_single, ← LinearMap.mul_apply, ← map_mul (as_algebra_hom ρ), mul_average_left]

/-- The `average_map` acts as the identity on the subspace of invariants.
-/
theorem average_map_id (v : V) (hv : v ∈ invariants ρ) : averageMap ρ v = v := by
  rw [mem_invariants] at hv
  simp [← average, ← map_sum, ← hv, ← Finset.card_univ, ← nsmul_eq_smul_cast k _ v, ← smul_smul]

theorem is_proj_average_map : LinearMap.IsProj ρ.invariants ρ.averageMap :=
  ⟨ρ.average_map_invariant, ρ.average_map_id⟩

end Invariants

namespace LinHom

universe u

open CategoryTheory Action

variable {k : Type u} [CommRingₓ k] {G : Groupₓₓ.{u}}

theorem mem_invariants_iff_comm {X Y : Rep k G} (f : X.V →ₗ[k] Y.V) (g : G) :
    (linHom X.ρ Y.ρ) g f = f ↔ X.ρ g ≫ f = f ≫ Y.ρ g := by
  rw [lin_hom_apply, ← ρ_Aut_apply_inv, ← LinearMap.comp_assoc, ← ModuleCat.comp_def, ← ModuleCat.comp_def,
    iso.inv_comp_eq, ρ_Aut_apply_hom]
  exact comm

/-- The invariants of the representation `lin_hom X.ρ Y.ρ` correspond to the the representation
homomorphisms from `X` to `Y` -/
@[simps]
def invariantsEquivRepHom (X Y : Rep k G) : (linHom X.ρ Y.ρ).invariants ≃ₗ[k] X ⟶ Y where
  toFun := fun f => ⟨f.val, fun g => (mem_invariants_iff_comm _ g).1 (f.property g)⟩
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl
  invFun := fun f => ⟨f.hom, fun g => (mem_invariants_iff_comm _ g).2 (f.comm g)⟩
  left_inv := fun _ => by
    ext
    rfl
  right_inv := fun _ => by
    ext
    rfl

end LinHom

end Representation

