/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.Analysis.NormedSpace.Dual
import Mathbin.Analysis.NormedSpace.Star.Basic
import Mathbin.Analysis.Complex.Basic
import Mathbin.Analysis.InnerProductSpace.Adjoint
import Mathbin.Algebra.Star.Subalgebra

/-!
# Von Neumann algebras

We give the "abstract" and "concrete" definitions of a von Neumann algebra.
We still have a major project ahead of us to show the equivalence between these definitions!

An abstract von Neumann algebra `wstar_algebra M` is a C^* algebra with a Banach space predual,
per Sakai (1971).

A concrete von Neumann algebra `von_neumann_algebra H` (where `H` is a Hilbert space)
is a *-closed subalgebra of bounded operators on `H` which is equal to its double commutant.

We'll also need to prove the von Neumann double commutant theorem,
that the concrete definition is equivalent to a *-closed subalgebra which is weakly closed.
-/


universe u v

/-- Sakai's definition of a von Neumann algebra as a C^* algebra with a Banach space predual.

So that we can unambiguously talk about these "abstract" von Neumann algebras
in parallel with the "concrete" ones (weakly closed *-subalgebras of B(H)),
we name this definition `wstar_algebra`.

Note that for now we only assert the mere existence of predual, rather than picking one.
This may later prove problematic, and need to be revisited.
Picking one may cause problems with definitional unification of different instances.
One the other hand, not picking one means that the weak-* topology
(which depends on a choice of predual) must be defined using the choice,
and we may be unhappy with the resulting opaqueness of the definition.
-/
class WstarAlgebra (M : Type u) [NormedRing M] [StarRing M] [CstarRing M] [Module ℂ M] [NormedAlgebra ℂ M]
  [StarModule ℂ M] where
  exists_predual :
    ∃ (X : Type u)(_ : NormedGroup X)(_ : NormedSpace ℂ X)(_ : CompleteSpace X),
      Nonempty (NormedSpace.Dual ℂ X ≃ₗᵢ⋆[ℂ] M)

/-- The double commutant definition of a von Neumann algebra,
as a *-closed subalgebra of bounded operators on a Hilbert space,
which is equal to its double commutant.

Note that this definition is parameterised by the Hilbert space
on which the algebra faithfully acts, as is standard in the literature.
See `wstar_algebra` for the abstract notion (a C^*-algebra with Banach space predual).

Note this is a bundled structure, parameterised by the Hilbert space `H`,
rather than a typeclass on the type of elements.
Thus we can't say that the bounded operators `H →L[ℂ] H` form a `von_neumann_algebra`
(although we will later construct the instance `wstar_algebra (H →L[ℂ] H)`),
and instead will use `⊤ : von_neumann_algebra H`.
-/
-- TODO: Without this, `von_neumann_algebra` times out. Why?
@[nolint has_inhabited_instance]
structure VonNeumannAlgebra (H : Type u) [InnerProductSpace ℂ H] [CompleteSpace H] extends
  StarSubalgebra ℂ (H →L[ℂ] H) where
  double_commutant : Set.Centralizer (Set.Centralizer carrier) = carrier

/-- Consider a von Neumann algebra acting on a Hilbert space `H` as a *-subalgebra of `H →L[ℂ] H`.
(That is, we forget that it is equal to its double commutant
or equivalently that it is closed in the weak and strong operator topologies.)
-/
add_decl_doc VonNeumannAlgebra.toStarSubalgebra

namespace VonNeumannAlgebra

variable (H : Type u) [InnerProductSpace ℂ H] [CompleteSpace H]

instance : SetLike (VonNeumannAlgebra H) (H →L[ℂ] H) :=
  ⟨VonNeumannAlgebra.Carrier, fun p q h => by
    cases p <;> cases q <;> congr⟩

end VonNeumannAlgebra

