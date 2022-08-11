/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Mathbin.RingTheory.Finiteness
import Mathbin.LinearAlgebra.Dimension

/-!
# A module over a division ring is noetherian if and only if it is finite.

-/


universe u v

open Classical Cardinal

open Cardinal Submodule Module Function

namespace IsNoetherian

variable {K : Type u} {V : Type v} [DivisionRing K] [AddCommGroupₓ V] [Module K V]

/-- A module over a division ring is noetherian if and only if
its dimension (as a cardinal) is strictly less than the first infinite cardinal `ℵ₀`.
-/
theorem iff_dim_lt_aleph_0 : IsNoetherian K V ↔ Module.rank K V < ℵ₀ := by
  let b := Basis.ofVectorSpace K V
  rw [← b.mk_eq_dim'', lt_aleph_0_iff_set_finite]
  constructor
  · intro
    exact finite_of_linear_independent (Basis.OfVectorSpaceIndex.linear_independent K V)
    
  · intro hbfinite
    refine' @is_noetherian_of_linear_equiv K (⊤ : Submodule K V) V _ _ _ _ _ (LinearEquiv.ofTop _ rfl) (id _)
    refine' is_noetherian_of_fg_of_noetherian _ ⟨Set.Finite.toFinset hbfinite, _⟩
    rw [Set.Finite.coe_to_finset, ← b.span_eq, Basis.coe_of_vector_space, Subtype.range_coe]
    

variable (K V)

/-- The dimension of a noetherian module over a division ring, as a cardinal,
is strictly less than the first infinite cardinal `ℵ₀`. -/
theorem dim_lt_aleph_0 : ∀ [IsNoetherian K V], Module.rank K V < ℵ₀ :=
  IsNoetherian.iff_dim_lt_aleph_0.1

variable {K V}

/-- In a noetherian module over a division ring, all bases are indexed by a finite type. -/
noncomputable def fintypeBasisIndex {ι : Type _} [IsNoetherian K V] (b : Basis ι K V) : Fintype ι :=
  b.fintypeIndexOfDimLtAleph0 (dim_lt_aleph_0 K V)

/-- In a noetherian module over a division ring,
`basis.of_vector_space` is indexed by a finite type. -/
noncomputable instance [IsNoetherian K V] : Fintype (Basis.OfVectorSpaceIndex K V) :=
  fintypeBasisIndex (Basis.ofVectorSpace K V)

/-- In a noetherian module over a division ring,
if a basis is indexed by a set, that set is finite. -/
theorem finite_basis_index {ι : Type _} {s : Set ι} [IsNoetherian K V] (b : Basis s K V) : s.Finite :=
  b.finite_index_of_dim_lt_aleph_0 (dim_lt_aleph_0 K V)

variable (K V)

/-- In a noetherian module over a division ring,
there exists a finite basis. This is the indexing `finset`. -/
noncomputable def finsetBasisIndex [IsNoetherian K V] : Finset V :=
  (finite_basis_index (Basis.ofVectorSpace K V)).toFinset

@[simp]
theorem coe_finset_basis_index [IsNoetherian K V] : (↑(finsetBasisIndex K V) : Set V) = Basis.OfVectorSpaceIndex K V :=
  Set.Finite.coe_to_finset _

@[simp]
theorem coe_sort_finset_basis_index [IsNoetherian K V] :
    (finsetBasisIndex K V : Type _) = Basis.OfVectorSpaceIndex K V :=
  Set.Finite.coe_sort_to_finset _

/-- In a noetherian module over a division ring, there exists a finite basis.
This is indexed by the `finset` `finite_dimensional.finset_basis_index`.
This is in contrast to the result `finite_basis_index (basis.of_vector_space K V)`,
which provides a set and a `set.finite`.
-/
noncomputable def finsetBasis [IsNoetherian K V] : Basis (finsetBasisIndex K V) K V :=
  (Basis.ofVectorSpace K V).reindex
    (by
      simp )

@[simp]
theorem range_finset_basis [IsNoetherian K V] : Set.Range (finsetBasis K V) = Basis.OfVectorSpaceIndex K V := by
  rw [finset_basis, Basis.range_reindex, Basis.range_of_vector_space]

variable {K V}

/-- A module over a division ring is noetherian if and only if it is finitely generated. -/
theorem iff_fg : IsNoetherian K V ↔ Module.Finite K V := by
  constructor
  · intro h
    exact
      ⟨⟨finset_basis_index K V, by
          convert (finset_basis K V).span_eq
          simp ⟩⟩
    
  · rintro ⟨s, hs⟩
    rw [IsNoetherian.iff_dim_lt_aleph_0, ← dim_top, ← hs]
    exact lt_of_le_of_ltₓ (dim_span_le _) s.finite_to_set.lt_aleph_0
    

end IsNoetherian

