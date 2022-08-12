/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Mathbin.Algebra.Algebra.Subalgebra.Basic
import Mathbin.FieldTheory.Finiteness

/-!
# Finite dimensional vector spaces

Definition and basic properties of finite dimensional vector spaces, of their dimensions, and
of linear maps on such spaces.

## Main definitions

Assume `V` is a vector space over a field `K`. There are (at least) three equivalent definitions of
finite-dimensionality of `V`:

- it admits a finite basis.
- it is finitely generated.
- it is noetherian, i.e., every subspace is finitely generated.

We introduce a typeclass `finite_dimensional K V` capturing this property. For ease of transfer of
proof, it is defined using the second point of view, i.e., as `finite`. However, we prove
that all these points of view are equivalent, with the following lemmas
(in the namespace `finite_dimensional`):

- `fintype_basis_index` states that a finite-dimensional
  vector space has a finite basis
- `finite_dimensional.fin_basis` and `finite_dimensional.fin_basis_of_finrank_eq`
  are bases for finite dimensional vector spaces, where the index type
  is `fin`
- `of_fintype_basis` states that the existence of a basis indexed by a
  finite type implies finite-dimensionality
- `of_finset_basis` states that the existence of a basis indexed by a
  `finset` implies finite-dimensionality
- `of_finite_basis` states that the existence of a basis indexed by a
  finite set implies finite-dimensionality
- `is_noetherian.iff_fg` states that the space is finite-dimensional if and only if
  it is noetherian

Also defined is `finrank`, the dimension of a finite dimensional space, returning a `nat`,
as opposed to `module.rank`, which returns a `cardinal`. When the space has infinite dimension, its
`finrank` is by convention set to `0`.

Preservation of finite-dimensionality and formulas for the dimension are given for
- submodules
- quotients (for the dimension of a quotient, see `finrank_quotient_add_finrank`)
- linear equivs, in `linear_equiv.finite_dimensional` and `linear_equiv.finrank_eq`
- image under a linear map (the rank-nullity formula is in `finrank_range_add_finrank_ker`)

Basic properties of linear maps of a finite-dimensional vector space are given. Notably, the
equivalence of injectivity and surjectivity is proved in `linear_map.injective_iff_surjective`,
and the equivalence between left-inverse and right-inverse in `linear_map.mul_eq_one_comm`
and `linear_map.comp_eq_id_comm`.

## Implementation notes

Most results are deduced from the corresponding results for the general dimension (as a cardinal),
in `dimension.lean`. Not all results have been ported yet.

Much of this file could be generalised away from fields or division rings.
You should not assume that there has been any effort to state lemmas as generally as possible.

One of the characterizations of finite-dimensionality is in terms of finite generation. This
property is currently defined only for submodules, so we express it through the fact that the
maximal submodule (which, as a set, coincides with the whole space) is finitely generated. This is
not very convenient to use, although there are some helper functions. However, this becomes very
convenient when speaking of submodules which are finite-dimensional, as this notion coincides with
the fact that the submodule is finitely generated (as a submodule of the whole space). This
equivalence is proved in `submodule.fg_iff_finite_dimensional`.
-/


universe u v v' w

open Classical Cardinal

open Cardinal Submodule Module Function

/-- `finite_dimensional` vector spaces are defined to be finite modules.
Use `finite_dimensional.of_fintype_basis` to prove finite dimension from another definition. -/
@[reducible]
def FiniteDimensional (K V : Type _) [DivisionRing K] [AddCommGroupₓ V] [Module K V] :=
  Module.Finite K V

variable {K : Type u} {V : Type v}

namespace FiniteDimensional

open IsNoetherian

section DivisionRing

variable [DivisionRing K] [AddCommGroupₓ V] [Module K V] {V₂ : Type v'} [AddCommGroupₓ V₂] [Module K V₂]

/-- If the codomain of an injective linear map is finite dimensional, the domain must be as well. -/
theorem of_injective (f : V →ₗ[K] V₂) (w : Function.Injective f) [FiniteDimensional K V₂] : FiniteDimensional K V :=
  have : IsNoetherian K V₂ := IsNoetherian.iff_fg.mpr ‹_›
  Module.Finite.of_injective f w

/-- If the domain of a surjective linear map is finite dimensional, the codomain must be as well. -/
theorem of_surjective (f : V →ₗ[K] V₂) (w : Function.Surjective f) [FiniteDimensional K V] : FiniteDimensional K V₂ :=
  Module.Finite.of_surjective f w

variable (K V)

instance finite_dimensional_pi {ι} [Fintype ι] : FiniteDimensional K (ι → K) :=
  iff_fg.1 is_noetherian_pi

instance finite_dimensional_pi' {ι} [Fintype ι] (M : ι → Type _) [∀ i, AddCommGroupₓ (M i)] [∀ i, Module K (M i)]
    [I : ∀ i, FiniteDimensional K (M i)] : FiniteDimensional K (∀ i, M i) := by
  have : ∀ i : ι, IsNoetherian K (M i) := fun i => iff_fg.2 (I i)
  exact iff_fg.1 is_noetherian_pi

/-- A finite dimensional vector space over a finite field is finite -/
noncomputable def fintypeOfFintype [Fintype K] [FiniteDimensional K V] : Fintype V :=
  Module.fintypeOfFintype (@finsetBasis K V _ _ _ (iff_fg.2 inferInstance))

variable {K V}

/-- If a vector space has a finite basis, then it is finite-dimensional. -/
theorem of_fintype_basis {ι : Type w} [Fintype ι] (h : Basis ι K V) : FiniteDimensional K V :=
  ⟨⟨Finset.univ.Image h, by
      convert h.span_eq
      simp ⟩⟩

/-- If a vector space is `finite_dimensional`, all bases are indexed by a finite type -/
noncomputable def fintypeBasisIndex {ι : Type _} [FiniteDimensional K V] (b : Basis ι K V) : Fintype ι := by
  let this : IsNoetherian K V := IsNoetherian.iff_fg.2 inferInstance
  exact IsNoetherian.fintypeBasisIndex b

/-- If a vector space is `finite_dimensional`, `basis.of_vector_space` is indexed by
  a finite type.-/
noncomputable instance [FiniteDimensional K V] : Fintype (Basis.OfVectorSpaceIndex K V) := by
  let this : IsNoetherian K V := IsNoetherian.iff_fg.2 inferInstance
  infer_instance

/-- If a vector space has a basis indexed by elements of a finite set, then it is
finite-dimensional. -/
theorem of_finite_basis {ι : Type w} {s : Set ι} (h : Basis s K V) (hs : Set.Finite s) : FiniteDimensional K V :=
  have := hs.fintype
  of_fintype_basis h

/-- If a vector space has a finite basis, then it is finite-dimensional, finset style. -/
theorem of_finset_basis {ι : Type w} {s : Finset ι} (h : Basis s K V) : FiniteDimensional K V :=
  of_finite_basis h s.finite_to_set

/-- A subspace of a finite-dimensional space is also finite-dimensional. -/
instance finite_dimensional_submodule [FiniteDimensional K V] (S : Submodule K V) : FiniteDimensional K S := by
  let this : IsNoetherian K V := iff_fg.2 _
  exact iff_fg.1 (IsNoetherian.iff_dim_lt_aleph_0.2 (lt_of_le_of_ltₓ (dim_submodule_le _) (dim_lt_aleph_0 K V)))
  infer_instance

/-- A quotient of a finite-dimensional space is also finite-dimensional. -/
instance finite_dimensional_quotient [FiniteDimensional K V] (S : Submodule K V) : FiniteDimensional K (V ⧸ S) :=
  Module.Finite.of_surjective (Submodule.mkq S) <| surjective_quot_mk _

/-- The rank of a module as a natural number.

Defined by convention to be `0` if the space has infinite rank.

For a vector space `V` over a field `K`, this is the same as the finite dimension
of `V` over `K`.
-/
noncomputable def finrank (R V : Type _) [Semiringₓ R] [AddCommGroupₓ V] [Module R V] : ℕ :=
  (Module.rank R V).toNat

/-- In a finite-dimensional space, its dimension (seen as a cardinal) coincides with its
`finrank`. -/
theorem finrank_eq_dim (K : Type u) (V : Type v) [DivisionRing K] [AddCommGroupₓ V] [Module K V]
    [FiniteDimensional K V] : (finrank K V : Cardinal.{v}) = Module.rank K V := by
  let this : IsNoetherian K V := iff_fg.2 inferInstance
  rw [finrank, cast_to_nat_of_lt_aleph_0 (dim_lt_aleph_0 K V)]

theorem finrank_eq_of_dim_eq {n : ℕ} (h : Module.rank K V = ↑n) : finrank K V = n := by
  apply_fun to_nat  at h
  rw [to_nat_cast] at h
  exact_mod_cast h

theorem finrank_of_infinite_dimensional {K V : Type _} [DivisionRing K] [AddCommGroupₓ V] [Module K V]
    (h : ¬FiniteDimensional K V) : finrank K V = 0 :=
  dif_neg <| mt IsNoetherian.iff_dim_lt_aleph_0.2 <| (not_iff_not.2 iff_fg).2 h

theorem finite_dimensional_of_finrank {K V : Type _} [DivisionRing K] [AddCommGroupₓ V] [Module K V]
    (h : 0 < finrank K V) : FiniteDimensional K V := by
  contrapose h
  simp [← finrank_of_infinite_dimensional h]

theorem finite_dimensional_of_finrank_eq_succ {K V : Type _} [Field K] [AddCommGroupₓ V] [Module K V] {n : ℕ}
    (hn : finrank K V = n.succ) : FiniteDimensional K V :=
  finite_dimensional_of_finrank <| by
    rw [hn] <;> exact n.succ_pos

/-- We can infer `finite_dimensional K V` in the presence of `[fact (finrank K V = n + 1)]`. Declare
this as a local instance where needed. -/
theorem fact_finite_dimensional_of_finrank_eq_succ {K V : Type _} [Field K] [AddCommGroupₓ V] [Module K V] (n : ℕ)
    [Fact (finrank K V = n + 1)] : FiniteDimensional K V :=
  finite_dimensional_of_finrank <| by
    convert Nat.succ_posₓ n <;> apply Fact.out

theorem finite_dimensional_iff_of_rank_eq_nsmul {K V W : Type _} [Field K] [AddCommGroupₓ V] [AddCommGroupₓ W]
    [Module K V] [Module K W] {n : ℕ} (hn : n ≠ 0) (hVW : Module.rank K V = n • Module.rank K W) :
    FiniteDimensional K V ↔ FiniteDimensional K W := by
  simp only [← FiniteDimensional, IsNoetherian.iff_fg, ← IsNoetherian.iff_dim_lt_aleph_0, ← hVW, ←
    Cardinal.nsmul_lt_aleph_0_iff_of_ne_zero hn]

/-- If a vector space has a finite basis, then its dimension is equal to the cardinality of the
basis. -/
theorem finrank_eq_card_basis {ι : Type w} [Fintype ι] (h : Basis ι K V) : finrank K V = Fintype.card ι := by
  have : FiniteDimensional K V := of_fintype_basis h
  have := dim_eq_card_basis h
  rw [← finrank_eq_dim] at this
  exact_mod_cast this

/-- If a vector space is finite-dimensional, then the cardinality of any basis is equal to its
`finrank`. -/
theorem finrank_eq_card_basis' [FiniteDimensional K V] {ι : Type w} (h : Basis ι K V) :
    (finrank K V : Cardinal.{w}) = # ι := by
  have : IsNoetherian K V := iff_fg.2 inferInstance
  have : Fintype ι := fintype_basis_index h
  rw [Cardinal.mk_fintype, finrank_eq_card_basis h]

/-- If a vector space has a finite basis, then its dimension is equal to the cardinality of the
basis. This lemma uses a `finset` instead of indexed types. -/
theorem finrank_eq_card_finset_basis {ι : Type w} {b : Finset ι} (h : Basis.{w} b K V) : finrank K V = Finset.card b :=
  by
  rw [finrank_eq_card_basis h, Fintype.card_coe]

variable (K V)

/-- A finite dimensional vector space has a basis indexed by `fin (finrank K V)`. -/
noncomputable def finBasis [FiniteDimensional K V] : Basis (Finₓ (finrank K V)) K V :=
  have h : Fintype.card (@finsetBasisIndex K V _ _ _ (iff_fg.2 inferInstance)) = finrank K V :=
    (finrank_eq_card_basis (@finsetBasis K V _ _ _ (iff_fg.2 inferInstance))).symm
  (@finsetBasis K V _ _ _ (iff_fg.2 inferInstance)).reindex (Fintype.equivFinOfCardEq h)

/-- An `n`-dimensional vector space has a basis indexed by `fin n`. -/
noncomputable def finBasisOfFinrankEq [FiniteDimensional K V] {n : ℕ} (hn : finrank K V = n) : Basis (Finₓ n) K V :=
  (finBasis K V).reindex (Finₓ.cast hn).toEquiv

variable {K V}

/-- A module with dimension 1 has a basis with one element. -/
noncomputable def basisUnique (ι : Type _) [Unique ι] (h : finrank K V = 1) : Basis ι K V := by
  have := finite_dimensional_of_finrank (_root_.zero_lt_one.trans_le h.symm.le)
  exact (fin_basis_of_finrank_eq K V h).reindex (Equivₓ.equivOfUnique _ _)

@[simp]
theorem basisUnique.repr_eq_zero_iff {ι : Type _} [Unique ι] {h : finrank K V = 1} {v : V} {i : ι} :
    (basisUnique ι h).repr v i = 0 ↔ v = 0 :=
  ⟨fun hv => (basisUnique ι h).repr.map_eq_zero_iff.mp (Finsupp.ext fun j => Subsingleton.elimₓ i j ▸ hv), fun hv => by
    rw [hv, LinearEquiv.map_zero, Finsupp.zero_apply]⟩

theorem cardinal_mk_le_finrank_of_linear_independent [FiniteDimensional K V] {ι : Type w} {b : ι → V}
    (h : LinearIndependent K b) : # ι ≤ finrank K V := by
  rw [← lift_le.{_, max v w}]
  simpa [finrank_eq_dim K V] using cardinal_lift_le_dim_of_linear_independent.{_, _, _, max v w} h

theorem fintype_card_le_finrank_of_linear_independent [FiniteDimensional K V] {ι : Type _} [Fintype ι] {b : ι → V}
    (h : LinearIndependent K b) : Fintype.card ι ≤ finrank K V := by
  simpa using cardinal_mk_le_finrank_of_linear_independent h

theorem finset_card_le_finrank_of_linear_independent [FiniteDimensional K V] {b : Finset V}
    (h : LinearIndependent K (fun x => x : b → V)) : b.card ≤ finrank K V := by
  rw [← Fintype.card_coe]
  exact fintype_card_le_finrank_of_linear_independent h

theorem lt_aleph_0_of_linear_independent {ι : Type w} [FiniteDimensional K V] {v : ι → V} (h : LinearIndependent K v) :
    # ι < ℵ₀ := by
  apply Cardinal.lift_lt.1
  apply lt_of_le_of_ltₓ
  apply cardinal_lift_le_dim_of_linear_independent h
  rw [← finrank_eq_dim, Cardinal.lift_aleph_0, Cardinal.lift_nat_cast]
  apply Cardinal.nat_lt_aleph_0

theorem _root_.linear_independent.finite {K : Type _} {V : Type _} [DivisionRing K] [AddCommGroupₓ V] [Module K V]
    [FiniteDimensional K V] {b : Set V} (h : LinearIndependent K fun x : b => (x : V)) : b.Finite :=
  Cardinal.lt_aleph_0_iff_set_finite.mp (FiniteDimensional.lt_aleph_0_of_linear_independent h)

theorem not_linear_independent_of_infinite {ι : Type w} [inf : Infinite ι] [FiniteDimensional K V] (v : ι → V) :
    ¬LinearIndependent K v := by
  intro h_lin_indep
  have : ¬ℵ₀ ≤ # ι := not_le.mpr (lt_aleph_0_of_linear_independent h_lin_indep)
  have : ℵ₀ ≤ # ι := infinite_iff.mp inf
  contradiction

/-- A finite dimensional space has positive `finrank` iff it has a nonzero element. -/
theorem finrank_pos_iff_exists_ne_zero [FiniteDimensional K V] : 0 < finrank K V ↔ ∃ x : V, x ≠ 0 :=
  Iff.trans
    (by
      rw [← finrank_eq_dim]
      norm_cast)
    (@dim_pos_iff_exists_ne_zero K V _ _ _ _ _)

/-- A finite dimensional space has positive `finrank` iff it is nontrivial. -/
theorem finrank_pos_iff [FiniteDimensional K V] : 0 < finrank K V ↔ Nontrivial V :=
  Iff.trans
    (by
      rw [← finrank_eq_dim]
      norm_cast)
    (@dim_pos_iff_nontrivial K V _ _ _ _ _)

/-- A finite dimensional space is nontrivial if it has positive `finrank`. -/
theorem nontrivial_of_finrank_pos (h : 0 < finrank K V) : Nontrivial V := by
  have : FiniteDimensional K V := finite_dimensional_of_finrank h
  rwa [finrank_pos_iff] at h

/-- A finite dimensional space is nontrivial if it has `finrank` equal to the successor of a
natural number. -/
theorem nontrivial_of_finrank_eq_succ {n : ℕ} (hn : finrank K V = n.succ) : Nontrivial V :=
  nontrivial_of_finrank_pos
    (by
      rw [hn] <;> exact n.succ_pos)

/-- A nontrivial finite dimensional space has positive `finrank`. -/
theorem finrank_pos [FiniteDimensional K V] [h : Nontrivial V] : 0 < finrank K V :=
  finrank_pos_iff.mpr h

/-- A finite dimensional space has zero `finrank` iff it is a subsingleton.
This is the `finrank` version of `dim_zero_iff`. -/
theorem finrank_zero_iff [FiniteDimensional K V] : finrank K V = 0 ↔ Subsingleton V :=
  Iff.trans
    (by
      rw [← finrank_eq_dim]
      norm_cast)
    (@dim_zero_iff K V _ _ _ _ _)

/-- A finite dimensional space that is a subsingleton has zero `finrank`. -/
theorem finrank_zero_of_subsingleton [h : Subsingleton V] : finrank K V = 0 :=
  finrank_zero_iff.2 h

theorem Basis.subset_extend {s : Set V} (hs : LinearIndependent K (coe : s → V)) : s ⊆ hs.extend (Set.subset_univ _) :=
  hs.subset_extend _

/-- If a submodule has maximal dimension in a finite dimensional space, then it is equal to the
whole space. -/
theorem eq_top_of_finrank_eq [FiniteDimensional K V] {S : Submodule K V} (h : finrank K S = finrank K V) : S = ⊤ := by
  have : IsNoetherian K V := iff_fg.2 inferInstance
  set bS := Basis.ofVectorSpace K S with bS_eq
  have : LinearIndependent K (coe : (coe '' Basis.OfVectorSpaceIndex K S : Set V) → V) :=
    @LinearIndependent.image_subtype _ _ _ _ _ _ _ _ _ (Submodule.subtype S)
      (by
        simpa using bS.linear_independent)
      (by
        simp )
  set b := Basis.extend this with b_eq
  let this : Fintype (this.extend _) :=
    (finite_of_linear_independent
        (by
          simpa using b.linear_independent)).Fintype
  let this : Fintype (coe '' Basis.OfVectorSpaceIndex K S) := (finite_of_linear_independent this).Fintype
  let this : Fintype (Basis.OfVectorSpaceIndex K S) :=
    (finite_of_linear_independent
        (by
          simpa using bS.linear_independent)).Fintype
  have : coe '' Basis.OfVectorSpaceIndex K S = this.extend (Set.subset_univ _) :=
    Set.eq_of_subset_of_card_le (this.subset_extend _)
      (by
        rw [Set.card_image_of_injective _ Subtype.coe_injective, ← finrank_eq_card_basis bS, ← finrank_eq_card_basis b,
            h] <;>
          infer_instance)
  rw [← b.span_eq, b_eq, Basis.coe_extend, Subtype.range_coe, ← this, ← Submodule.coe_subtype, span_image]
  have := bS.span_eq
  rw [bS_eq, Basis.coe_of_vector_space, Subtype.range_coe] at this
  rw [this, map_top (Submodule.subtype S), range_subtype]

variable (K)

/-- A division_ring is one-dimensional as a vector space over itself. -/
@[simp]
theorem finrank_self : finrank K K = 1 := by
  have := dim_self K
  rw [← finrank_eq_dim] at this
  exact_mod_cast this

instance finite_dimensional_self : FiniteDimensional K K := by
  infer_instance

/-- The vector space of functions on a fintype ι has finrank equal to the cardinality of ι. -/
@[simp]
theorem finrank_fintype_fun_eq_card {ι : Type v} [Fintype ι] : finrank K (ι → K) = Fintype.card ι := by
  have : Module.rank K (ι → K) = Fintype.card ι := dim_fun'
  rwa [← finrank_eq_dim, nat_cast_inj] at this

/-- The vector space of functions on `fin n` has finrank equal to `n`. -/
@[simp]
theorem finrank_fin_fun {n : ℕ} : finrank K (Finₓ n → K) = n := by
  simp

/-- The submodule generated by a finite set is finite-dimensional. -/
theorem span_of_finite {A : Set V} (hA : Set.Finite A) : FiniteDimensional K (Submodule.span K A) :=
  iff_fg.1 <| is_noetherian_span_of_finite K hA

/-- The submodule generated by a single element is finite-dimensional. -/
instance span_singleton (x : V) : FiniteDimensional K (K∙x) :=
  span_of_finite K <| Set.finite_singleton _

/-- The submodule generated by a finset is finite-dimensional. -/
instance span_finset (s : Finset V) : FiniteDimensional K (span K (s : Set V)) :=
  span_of_finite K <| s.finite_to_set

/-- Pushforwards of finite-dimensional submodules are finite-dimensional. -/
instance (f : V →ₗ[K] V₂) (p : Submodule K V) [h : FiniteDimensional K p] : FiniteDimensional K (p.map f) := by
  rw [FiniteDimensional, ← iff_fg, IsNoetherian.iff_dim_lt_aleph_0] at h⊢
  rw [← Cardinal.lift_lt.{v', v}]
  rw [← Cardinal.lift_lt.{v, v'}] at h
  rw [Cardinal.lift_aleph_0] at h⊢
  exact (lift_dim_map_le f p).trans_lt h

/-- Pushforwards of finite-dimensional submodules have a smaller finrank. -/
theorem finrank_map_le (f : V →ₗ[K] V₂) (p : Submodule K V) [FiniteDimensional K p] :
    finrank K (p.map f) ≤ finrank K p := by
  simpa [finrank_eq_dim] using lift_dim_map_le f p

variable {K}

theorem _root_.complete_lattice.independent.subtype_ne_bot_le_finrank_aux [FiniteDimensional K V] {ι : Type w}
    {p : ι → Submodule K V} (hp : CompleteLattice.Independent p) : # { i // p i ≠ ⊥ } ≤ (finrank K V : Cardinal.{w}) :=
  by
  suffices Cardinal.lift.{v} (# { i // p i ≠ ⊥ }) ≤ Cardinal.lift.{v} (finrank K V : Cardinal.{w}) by
    rwa [Cardinal.lift_le] at this
  calc Cardinal.lift.{v} (# { i // p i ≠ ⊥ }) ≤ Cardinal.lift.{w} (Module.rank K V) :=
      hp.subtype_ne_bot_le_rank _ = Cardinal.lift.{w} (finrank K V : Cardinal.{v}) := by
      rw [finrank_eq_dim]_ = Cardinal.lift.{v} (finrank K V : Cardinal.{w}) := by
      simp

/-- If `p` is an independent family of subspaces of a finite-dimensional space `V`, then the
number of nontrivial subspaces in the family `p` is finite. -/
noncomputable def _root_.complete_lattice.independent.fintype_ne_bot_of_finite_dimensional [FiniteDimensional K V]
    {ι : Type w} {p : ι → Submodule K V} (hp : CompleteLattice.Independent p) : Fintype { i : ι // p i ≠ ⊥ } := by
  suffices # { i // p i ≠ ⊥ } < (ℵ₀ : Cardinal.{w}) by
    rw [Cardinal.lt_aleph_0_iff_fintype] at this
    exact this.some
  refine' lt_of_le_of_ltₓ hp.subtype_ne_bot_le_finrank_aux _
  simp [← Cardinal.nat_lt_aleph_0]

/-- If `p` is an independent family of subspaces of a finite-dimensional space `V`, then the
number of nontrivial subspaces in the family `p` is bounded above by the dimension of `V`.

Note that the `fintype` hypothesis required here can be provided by
`complete_lattice.independent.fintype_ne_bot_of_finite_dimensional`. -/
theorem _root_.complete_lattice.independent.subtype_ne_bot_le_finrank [FiniteDimensional K V] {ι : Type w}
    {p : ι → Submodule K V} (hp : CompleteLattice.Independent p) [Fintype { i // p i ≠ ⊥ }] :
    Fintype.card { i // p i ≠ ⊥ } ≤ finrank K V := by
  simpa using hp.subtype_ne_bot_le_finrank_aux

section

open BigOperators

open Finset

/-- If a finset has cardinality larger than the dimension of the space,
then there is a nontrivial linear relation amongst its elements.
-/
theorem exists_nontrivial_relation_of_dim_lt_card [FiniteDimensional K V] {t : Finset V} (h : finrank K V < t.card) :
    ∃ f : V → K, (∑ e in t, f e • e) = 0 ∧ ∃ x ∈ t, f x ≠ 0 := by
  have :=
    mt finset_card_le_finrank_of_linear_independent
      (by
        simpa using h)
  rw [not_linear_independent_iff] at this
  obtain ⟨s, g, sum, z, zm, nonzero⟩ := this
  -- Now we have to extend `g` to all of `t`, then to all of `V`.
  let f : V → K := fun x => if h : x ∈ t then if (⟨x, h⟩ : t) ∈ s then g ⟨x, h⟩ else 0 else 0
  -- and finally clean up the mess caused by the extension.
  refine' ⟨f, _, _⟩
  · dsimp' [← f]
    rw [← Sum]
    fapply sum_bij_ne_zero fun v hvt _ => (⟨v, hvt⟩ : { v // v ∈ t })
    · intro v hvt H
      dsimp'
      rw [dif_pos hvt] at H
      contrapose! H
      rw [if_neg H, zero_smul]
      
    · intro _ _ _ _ _ _
      exact Subtype.mk.injₓ
      
    · intro b hbs hb
      use b
      simpa only [← hbs, ← exists_prop, ← dif_pos, ← Finset.mk_coe, ← and_trueₓ, ← if_true, ← Finset.coe_mem, ←
        eq_self_iff_true, ← exists_prop_of_true, ← Ne.def] using hb
      
    · intro a h₁
      dsimp'
      rw [dif_pos h₁]
      intro h₂
      rw [if_pos]
      contrapose! h₂
      rw [if_neg h₂, zero_smul]
      
    
  · refine' ⟨z, z.2, _⟩
    dsimp' only [← f]
    erw [dif_pos z.2, if_pos] <;> rwa [Subtype.coe_eta]
    

/-- If a finset has cardinality larger than `finrank + 1`,
then there is a nontrivial linear relation amongst its elements,
such that the coefficients of the relation sum to zero.
-/
theorem exists_nontrivial_relation_sum_zero_of_dim_succ_lt_card [FiniteDimensional K V] {t : Finset V}
    (h : finrank K V + 1 < t.card) : ∃ f : V → K, (∑ e in t, f e • e) = 0 ∧ (∑ e in t, f e) = 0 ∧ ∃ x ∈ t, f x ≠ 0 := by
  -- Pick an element x₀ ∈ t,
  have card_pos : 0 < t.card := lt_transₓ (Nat.succ_posₓ _) h
  obtain ⟨x₀, m⟩ := (Finset.card_pos.1 card_pos).bex
  -- and apply the previous lemma to the {xᵢ - x₀}
  let shift : V ↪ V := ⟨fun x => x - x₀, sub_left_injective⟩
  let t' := (t.erase x₀).map shift
  have h' : finrank K V < t'.card := by
    simp only [← t', ← card_map, ← Finset.card_erase_of_mem m]
    exact nat.lt_pred_iff.mpr h
  -- to obtain a function `g`.
  obtain ⟨g, gsum, x₁, x₁_mem, nz⟩ := exists_nontrivial_relation_of_dim_lt_card h'
  -- Then obtain `f` by translating back by `x₀`,
  -- and setting the value of `f` at `x₀` to ensure `∑ e in t, f e = 0`.
  let f : V → K := fun z => if z = x₀ then -∑ z in t.erase x₀, g (z - x₀) else g (z - x₀)
  refine' ⟨f, _, _, _⟩
  -- After this, it's a matter of verifiying the properties,
  -- based on the corresponding properties for `g`.
  · show (∑ e : V in t, f e • e) = 0
    -- We prove this by splitting off the `x₀` term of the sum,
    -- which is itself a sum over `t.erase x₀`,
    -- combining the two sums, and
    -- observing that after reindexing we have exactly
    -- ∑ (x : V) in t', g x • x = 0.
    simp only [← f]
    conv_lhs => apply_congr skip rw [ite_smul]
    rw [Finset.sum_ite]
    conv => congr congr apply_congr simp [← filter_eq', ← m]
    conv => congr congr skip apply_congr simp [← filter_ne']
    rw [sum_singleton, neg_smul, add_commₓ, ← sub_eq_add_neg, sum_smul, ← sum_sub_distrib]
    simp only [smul_sub]
    -- At the end we have to reindex the sum, so we use `change` to
    -- express the summand using `shift`.
    change (∑ x : V in t.erase x₀, (fun e => g e • e) (shift x)) = 0
    rw [← sum_map _ shift]
    exact gsum
    
  · show (∑ e : V in t, f e) = 0
    -- Again we split off the `x₀` term,
    -- observing that it exactly cancels the other terms.
    rw [← insert_erase m, sum_insert (not_mem_erase x₀ t)]
    dsimp' [← f]
    rw [if_pos rfl]
    conv_lhs => congr skip apply_congr skip rw [if_neg (show x ≠ x₀ from (mem_erase.mp H).1)]
    exact neg_add_selfₓ _
    
  · show ∃ (x : V)(H : x ∈ t), f x ≠ 0
    -- We can use x₁ + x₀.
    refine' ⟨x₁ + x₀, _, _⟩
    · rw [Finset.mem_map] at x₁_mem
      rcases x₁_mem with ⟨x₁, x₁_mem, rfl⟩
      rw [mem_erase] at x₁_mem
      simp only [← x₁_mem, ← sub_add_cancel, ← Function.Embedding.coe_fn_mk]
      
    · dsimp' only [← f]
      rwa [if_neg, add_sub_cancel]
      rw [add_left_eq_self]
      rintro rfl
      simpa only [← sub_eq_zero, ← exists_prop, ← Finset.mem_map, ← embedding.coe_fn_mk, ← eq_self_iff_true, ←
        mem_erase, ← not_true, ← exists_eq_right, ← Ne.def, ← false_andₓ] using x₁_mem
      
    

section

variable {L : Type _} [LinearOrderedField L]

variable {W : Type v} [AddCommGroupₓ W] [Module L W]

/-- A slight strengthening of `exists_nontrivial_relation_sum_zero_of_dim_succ_lt_card`
available when working over an ordered field:
we can ensure a positive coefficient, not just a nonzero coefficient.
-/
theorem exists_relation_sum_zero_pos_coefficient_of_dim_succ_lt_card [FiniteDimensional L W] {t : Finset W}
    (h : finrank L W + 1 < t.card) : ∃ f : W → L, (∑ e in t, f e • e) = 0 ∧ (∑ e in t, f e) = 0 ∧ ∃ x ∈ t, 0 < f x := by
  obtain ⟨f, sum, total, nonzero⟩ := exists_nontrivial_relation_sum_zero_of_dim_succ_lt_card h
  exact ⟨f, Sum, Total, exists_pos_of_sum_zero_of_exists_nonzero f Total nonzero⟩

end

end

/-- In a vector space with dimension 1, each set {v} is a basis for `v ≠ 0`. -/
@[simps]
noncomputable def basisSingleton (ι : Type _) [Unique ι] (h : finrank K V = 1) (v : V) (hv : v ≠ 0) : Basis ι K V :=
  let b := basisUnique ι h
  let h : b.repr v default ≠ 0 := mt basisUnique.repr_eq_zero_iff.mp hv
  Basis.of_repr
    { toFun := fun w => Finsupp.single default (b.repr w default / b.repr v default), invFun := fun f => f default • v,
      map_add' := by
        simp [← add_div],
      map_smul' := by
        simp [← mul_div],
      left_inv := fun w => by
        apply_fun b.repr using b.repr.to_equiv.injective
        apply_fun Equivₓ.finsuppUnique
        simp only [← LinearEquiv.map_smulₛₗ, ← Finsupp.coe_smul, ← Finsupp.single_eq_same, ← RingHom.id_apply, ←
          smul_eq_mul, ← Pi.smul_apply, ← Equivₓ.finsupp_unique_apply]
        exact div_mul_cancel _ h,
      right_inv := fun f => by
        ext
        simp only [← LinearEquiv.map_smulₛₗ, ← Finsupp.coe_smul, ← Finsupp.single_eq_same, ← RingHom.id_apply, ←
          smul_eq_mul, ← Pi.smul_apply]
        exact mul_div_cancel _ h }

@[simp]
theorem basis_singleton_apply (ι : Type _) [Unique ι] (h : finrank K V = 1) (v : V) (hv : v ≠ 0) (i : ι) :
    basisSingleton ι h v hv i = v := by
  cases Unique.uniq ‹Unique ι› i
  simp [← basis_singleton]

@[simp]
theorem range_basis_singleton (ι : Type _) [Unique ι] (h : finrank K V = 1) (v : V) (hv : v ≠ 0) :
    Set.Range (basisSingleton ι h v hv) = {v} := by
  rw [Set.range_unique, basis_singleton_apply]

end DivisionRing

end FiniteDimensional

variable {K V}

section ZeroDim

variable [DivisionRing K] [AddCommGroupₓ V] [Module K V]

open FiniteDimensional

theorem finite_dimensional_of_dim_eq_zero (h : Module.rank K V = 0) : FiniteDimensional K V := by
  dsimp' [← FiniteDimensional]
  rw [← IsNoetherian.iff_fg, IsNoetherian.iff_dim_lt_aleph_0, h]
  exact Cardinal.aleph_0_pos

theorem finite_dimensional_of_dim_eq_one (h : Module.rank K V = 1) : FiniteDimensional K V := by
  dsimp' [← FiniteDimensional]
  rw [← IsNoetherian.iff_fg, IsNoetherian.iff_dim_lt_aleph_0, h]
  exact one_lt_aleph_0

theorem finrank_eq_zero_of_dim_eq_zero [FiniteDimensional K V] (h : Module.rank K V = 0) : finrank K V = 0 := by
  convert finrank_eq_dim K V
  rw [h]
  norm_cast

theorem finrank_eq_zero_of_basis_imp_not_finite (h : ∀ s : Set V, Basis.{v} (s : Set V) K V → ¬s.Finite) :
    finrank K V = 0 :=
  dif_neg fun dim_lt => h _ (Basis.ofVectorSpace K V) ((Basis.ofVectorSpace K V).finite_index_of_dim_lt_aleph_0 dim_lt)

theorem finrank_eq_zero_of_basis_imp_false (h : ∀ s : Finset V, Basis.{v} (s : Set V) K V → False) : finrank K V = 0 :=
  finrank_eq_zero_of_basis_imp_not_finite fun s b hs =>
    h hs.toFinset
      (by
        convert b
        simp )

theorem finrank_eq_zero_of_not_exists_basis (h : ¬∃ s : Finset V, Nonempty (Basis (s : Set V) K V)) : finrank K V = 0 :=
  finrank_eq_zero_of_basis_imp_false fun s b => h ⟨s, ⟨b⟩⟩

theorem finrank_eq_zero_of_not_exists_basis_finite (h : ¬∃ (s : Set V)(b : Basis.{v} (s : Set V) K V), s.Finite) :
    finrank K V = 0 :=
  finrank_eq_zero_of_basis_imp_not_finite fun s b hs => h ⟨s, b, hs⟩

theorem finrank_eq_zero_of_not_exists_basis_finset (h : ¬∃ s : Finset V, Nonempty (Basis s K V)) : finrank K V = 0 :=
  finrank_eq_zero_of_basis_imp_false fun s b => h ⟨s, ⟨b⟩⟩

variable (K V)

instance finite_dimensional_bot : FiniteDimensional K (⊥ : Submodule K V) :=
  finite_dimensional_of_dim_eq_zero <| by
    simp

@[simp]
theorem finrank_bot : finrank K (⊥ : Submodule K V) = 0 := by
  convert finrank_eq_dim K (⊥ : Submodule K V)
  rw [dim_bot]
  norm_cast

variable {K V}

theorem bot_eq_top_of_dim_eq_zero (h : Module.rank K V = 0) : (⊥ : Submodule K V) = ⊤ := by
  have := finite_dimensional_of_dim_eq_zero h
  apply eq_top_of_finrank_eq
  rw [finrank_bot, finrank_eq_zero_of_dim_eq_zero h]

@[simp]
theorem dim_eq_zero {S : Submodule K V} : Module.rank K S = 0 ↔ S = ⊥ :=
  ⟨fun h =>
    (Submodule.eq_bot_iff _).2 fun x hx =>
      congr_arg Subtype.val <|
        ((Submodule.eq_bot_iff _).1 <| Eq.symm <| bot_eq_top_of_dim_eq_zero h) ⟨x, hx⟩ Submodule.mem_top,
    fun h => by
    rw [h, dim_bot]⟩

@[simp]
theorem finrank_eq_zero {S : Submodule K V} [FiniteDimensional K S] : finrank K S = 0 ↔ S = ⊥ := by
  rw [← dim_eq_zero, ← finrank_eq_dim, ← @Nat.cast_zeroₓ Cardinal, Cardinal.nat_cast_inj]

end ZeroDim

namespace Submodule

open IsNoetherian FiniteDimensional

section DivisionRing

variable [DivisionRing K] [AddCommGroupₓ V] [Module K V]

/-- A submodule is finitely generated if and only if it is finite-dimensional -/
theorem fg_iff_finite_dimensional (s : Submodule K V) : s.Fg ↔ FiniteDimensional K s :=
  ⟨fun h => Module.finite_def.2 <| (fg_top s).2 h, fun h => (fg_top s).1 <| Module.finite_def.1 h⟩

/-- A submodule contained in a finite-dimensional submodule is
finite-dimensional. -/
theorem finite_dimensional_of_le {S₁ S₂ : Submodule K V} [FiniteDimensional K S₂] (h : S₁ ≤ S₂) :
    FiniteDimensional K S₁ := by
  have : IsNoetherian K S₂ := iff_fg.2 inferInstance
  exact iff_fg.1 (IsNoetherian.iff_dim_lt_aleph_0.2 (lt_of_le_of_ltₓ (dim_le_of_submodule _ _ h) (dim_lt_aleph_0 K S₂)))

/-- The inf of two submodules, the first finite-dimensional, is
finite-dimensional. -/
instance finite_dimensional_inf_left (S₁ S₂ : Submodule K V) [FiniteDimensional K S₁] :
    FiniteDimensional K (S₁⊓S₂ : Submodule K V) :=
  finite_dimensional_of_le inf_le_left

/-- The inf of two submodules, the second finite-dimensional, is
finite-dimensional. -/
instance finite_dimensional_inf_right (S₁ S₂ : Submodule K V) [FiniteDimensional K S₂] :
    FiniteDimensional K (S₁⊓S₂ : Submodule K V) :=
  finite_dimensional_of_le inf_le_right

/-- The sup of two finite-dimensional submodules is
finite-dimensional. -/
instance finite_dimensional_sup (S₁ S₂ : Submodule K V) [h₁ : FiniteDimensional K S₁] [h₂ : FiniteDimensional K S₂] :
    FiniteDimensional K (S₁⊔S₂ : Submodule K V) := by
  unfold FiniteDimensional  at *
  rw [finite_def] at *
  exact (fg_top _).2 (((fg_top S₁).1 h₁).sup ((fg_top S₂).1 h₂))

/-- The submodule generated by a finite supremum of finite dimensional submodules is
finite-dimensional.

Note that strictly this only needs `∀ i ∈ s, finite_dimensional K (S i)`, but that doesn't
work well with typeclass search. -/
instance finite_dimensional_finset_sup {ι : Type _} (s : Finset ι) (S : ι → Submodule K V)
    [∀ i, FiniteDimensional K (S i)] : FiniteDimensional K (s.sup S : Submodule K V) := by
  refine'
    @Finset.sup_induction _ _ _ _ s S (fun i => FiniteDimensional K ↥i) (finite_dimensional_bot K V) _ fun i hi => by
      infer_instance
  · intro S₁ hS₁ S₂ hS₂
    exact Submodule.finite_dimensional_sup S₁ S₂
    

/-- The submodule generated by a supremum of finite dimensional submodules, indexed by a finite
type is finite-dimensional. -/
instance finite_dimensional_supr {ι : Type _} [Fintype ι] (S : ι → Submodule K V) [∀ i, FiniteDimensional K (S i)] :
    FiniteDimensional K ↥(⨆ i, S i) := by
  rw [← Finset.sup_univ_eq_supr]
  exact Submodule.finite_dimensional_finset_sup _ _

/-- The submodule generated by a supremum indexed by a proposition is finite-dimensional if
the submodule is. -/
instance finite_dimensional_supr_prop {P : Prop} (S : P → Submodule K V) [∀ h, FiniteDimensional K (S h)] :
    FiniteDimensional K ↥(⨆ h, S h) := by
  by_cases' hp : P
  · rw [supr_pos hp]
    infer_instance
    
  · rw [supr_neg hp]
    infer_instance
    

/-- The dimension of a submodule is bounded by the dimension of the ambient space. -/
theorem finrank_le [FiniteDimensional K V] (s : Submodule K V) : finrank K s ≤ finrank K V := by
  simpa only [← Cardinal.nat_cast_le, finrank_eq_dim] using s.subtype.dim_le_of_injective (injective_subtype s)

/-- The dimension of a quotient is bounded by the dimension of the ambient space. -/
theorem finrank_quotient_le [FiniteDimensional K V] (s : Submodule K V) : finrank K (V ⧸ s) ≤ finrank K V := by
  simpa only [← Cardinal.nat_cast_le, finrank_eq_dim] using (mkq s).dim_le_of_surjective (surjective_quot_mk _)

end DivisionRing

section Field

variable [Field K] [AddCommGroupₓ V] [Module K V]

/-- In a finite-dimensional vector space, the dimensions of a submodule and of the corresponding
quotient add up to the dimension of the space. -/
theorem finrank_quotient_add_finrank [FiniteDimensional K V] (s : Submodule K V) :
    finrank K (V ⧸ s) + finrank K s = finrank K V := by
  have := dim_quotient_add_dim s
  rw [← finrank_eq_dim, ← finrank_eq_dim, ← finrank_eq_dim] at this
  exact_mod_cast this

/-- The dimension of a strict submodule is strictly bounded by the dimension of the ambient
space. -/
theorem finrank_lt [FiniteDimensional K V] {s : Submodule K V} (h : s < ⊤) : finrank K s < finrank K V := by
  rw [← s.finrank_quotient_add_finrank, add_commₓ]
  exact Nat.lt_add_of_zero_lt_left _ _ (finrank_pos_iff.mpr (quotient.nontrivial_of_lt_top _ h))

/-- The sum of the dimensions of s + t and s ∩ t is the sum of the dimensions of s and t -/
theorem dim_sup_add_dim_inf_eq (s t : Submodule K V) [FiniteDimensional K s] [FiniteDimensional K t] :
    finrank K ↥(s⊔t) + finrank K ↥(s⊓t) = finrank K ↥s + finrank K ↥t := by
  have key : Module.rank K ↥(s⊔t) + Module.rank K ↥(s⊓t) = Module.rank K s + Module.rank K t :=
    dim_sup_add_dim_inf_eq s t
  repeat'
    rw [← finrank_eq_dim] at key
  norm_cast  at key
  exact key

theorem eq_top_of_disjoint [FiniteDimensional K V] (s t : Submodule K V)
    (hdim : finrank K s + finrank K t = finrank K V) (hdisjoint : Disjoint s t) : s⊔t = ⊤ := by
  have h_finrank_inf : finrank K ↥(s⊓t) = 0 := by
    rw [Disjoint, le_bot_iff] at hdisjoint
    rw [hdisjoint, finrank_bot]
  apply eq_top_of_finrank_eq
  rw [← hdim]
  convert s.dim_sup_add_dim_inf_eq t
  rw [h_finrank_inf]
  rfl

end Field

end Submodule

namespace LinearEquiv

open FiniteDimensional

variable [DivisionRing K] [AddCommGroupₓ V] [Module K V] {V₂ : Type v'} [AddCommGroupₓ V₂] [Module K V₂]

/-- Finite dimensionality is preserved under linear equivalence. -/
protected theorem finite_dimensional (f : V ≃ₗ[K] V₂) [FiniteDimensional K V] : FiniteDimensional K V₂ :=
  Module.Finite.equiv f

variable {R M M₂ : Type _} [Ringₓ R] [AddCommGroupₓ M] [AddCommGroupₓ M₂]

variable [Module R M] [Module R M₂]

/-- The dimension of a finite dimensional space is preserved under linear equivalence. -/
theorem finrank_eq (f : M ≃ₗ[R] M₂) : finrank R M = finrank R M₂ := by
  unfold finrank
  rw [← Cardinal.to_nat_lift, f.lift_dim_eq, Cardinal.to_nat_lift]

/-- Pushforwards of finite-dimensional submodules along a `linear_equiv` have the same finrank. -/
theorem finrank_map_eq (f : M ≃ₗ[R] M₂) (p : Submodule R M) : finrank R (p.map (f : M →ₗ[R] M₂)) = finrank R p :=
  (f.submoduleMap p).finrank_eq.symm

end LinearEquiv

section

variable [DivisionRing K] [AddCommGroupₓ V] [Module K V]

instance finite_dimensional_finsupp {ι : Type _} [Fintype ι] [h : FiniteDimensional K V] :
    FiniteDimensional K (ι →₀ V) := by
  let this : IsNoetherian K V := IsNoetherian.iff_fg.2 inferInstance
  exact (Finsupp.linearEquivFunOnFintype K V ι).symm.FiniteDimensional

end

namespace FiniteDimensional

section DivisionRing

variable [DivisionRing K] [AddCommGroupₓ V] [Module K V] {V₂ : Type v'} [AddCommGroupₓ V₂] [Module K V₂]

/-- Two finite-dimensional vector spaces are isomorphic if they have the same (finite) dimension.
-/
theorem nonempty_linear_equiv_of_finrank_eq [FiniteDimensional K V] [FiniteDimensional K V₂]
    (cond : finrank K V = finrank K V₂) : Nonempty (V ≃ₗ[K] V₂) :=
  nonempty_linear_equiv_of_lift_dim_eq <| by
    simp only [finrank_eq_dim, ← cond, ← lift_nat_cast]

/-- Two finite-dimensional vector spaces are isomorphic if and only if they have the same (finite)
dimension.
-/
theorem nonempty_linear_equiv_iff_finrank_eq [FiniteDimensional K V] [FiniteDimensional K V₂] :
    Nonempty (V ≃ₗ[K] V₂) ↔ finrank K V = finrank K V₂ :=
  ⟨fun ⟨h⟩ => h.finrank_eq, fun h => nonempty_linear_equiv_of_finrank_eq h⟩

variable (V V₂)

/-- Two finite-dimensional vector spaces are isomorphic if they have the same (finite) dimension.
-/
noncomputable def LinearEquiv.ofFinrankEq [FiniteDimensional K V] [FiniteDimensional K V₂]
    (cond : finrank K V = finrank K V₂) : V ≃ₗ[K] V₂ :=
  Classical.choice <| nonempty_linear_equiv_of_finrank_eq cond

variable {V}

theorem eq_of_le_of_finrank_le {S₁ S₂ : Submodule K V} [FiniteDimensional K S₂] (hle : S₁ ≤ S₂)
    (hd : finrank K S₂ ≤ finrank K S₁) : S₁ = S₂ := by
  rw [← LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe hle)] at hd
  exact
    le_antisymmₓ hle
      (Submodule.comap_subtype_eq_top.1
        (eq_top_of_finrank_eq (le_antisymmₓ (comap (Submodule.subtype S₂) S₁).finrank_le hd)))

/-- If a submodule is less than or equal to a finite-dimensional
submodule with the same dimension, they are equal. -/
theorem eq_of_le_of_finrank_eq {S₁ S₂ : Submodule K V} [FiniteDimensional K S₂] (hle : S₁ ≤ S₂)
    (hd : finrank K S₁ = finrank K S₂) : S₁ = S₂ :=
  eq_of_le_of_finrank_le hle hd.Ge

@[simp]
theorem finrank_map_subtype_eq (p : Submodule K V) (q : Submodule K p) :
    FiniteDimensional.finrank K (q.map p.Subtype) = FiniteDimensional.finrank K q :=
  (Submodule.equivSubtypeMap p q).symm.finrank_eq

end DivisionRing

section Field

variable [Field K] [AddCommGroupₓ V] [Module K V] {V₂ : Type v'} [AddCommGroupₓ V₂] [Module K V₂]

variable [FiniteDimensional K V] [FiniteDimensional K V₂]

/-- Given isomorphic subspaces `p q` of vector spaces `V` and `V₁` respectively,
  `p.quotient` is isomorphic to `q.quotient`. -/
noncomputable def LinearEquiv.quotEquivOfEquiv {p : Subspace K V} {q : Subspace K V₂} (f₁ : p ≃ₗ[K] q)
    (f₂ : V ≃ₗ[K] V₂) : (V ⧸ p) ≃ₗ[K] V₂ ⧸ q :=
  LinearEquiv.ofFinrankEq _ _
    (by
      rw [← @add_right_cancel_iffₓ _ _ (finrank K p), Submodule.finrank_quotient_add_finrank, LinearEquiv.finrank_eq f₁,
        Submodule.finrank_quotient_add_finrank, LinearEquiv.finrank_eq f₂])

/-- Given the subspaces `p q`, if `p.quotient ≃ₗ[K] q`, then `q.quotient ≃ₗ[K] p` -/
noncomputable def LinearEquiv.quotEquivOfQuotEquiv {p q : Subspace K V} (f : (V ⧸ p) ≃ₗ[K] q) : (V ⧸ q) ≃ₗ[K] p :=
  LinearEquiv.ofFinrankEq _ _
    (by
      rw [← @add_right_cancel_iffₓ _ _ (finrank K q), Submodule.finrank_quotient_add_finrank, ←
        LinearEquiv.finrank_eq f, add_commₓ, Submodule.finrank_quotient_add_finrank])

end Field

end FiniteDimensional

namespace LinearMap

open FiniteDimensional

section DivisionRing

variable [DivisionRing K] [AddCommGroupₓ V] [Module K V] {V₂ : Type v'} [AddCommGroupₓ V₂] [Module K V₂]

/-- On a finite-dimensional space, an injective linear map is surjective. -/
theorem surjective_of_injective [FiniteDimensional K V] {f : V →ₗ[K] V} (hinj : Injective f) : Surjective f := by
  have h := dim_eq_of_injective _ hinj
  rw [← finrank_eq_dim, ← finrank_eq_dim, nat_cast_inj] at h
  exact range_eq_top.1 (eq_top_of_finrank_eq h.symm)

/-- The image under an onto linear map of a finite-dimensional space is also finite-dimensional. -/
theorem finite_dimensional_of_surjective [h : FiniteDimensional K V] (f : V →ₗ[K] V₂) (hf : f.range = ⊤) :
    FiniteDimensional K V₂ :=
  Module.Finite.of_surjective f <| range_eq_top.1 hf

/-- The range of a linear map defined on a finite-dimensional space is also finite-dimensional. -/
instance finite_dimensional_range [h : FiniteDimensional K V] (f : V →ₗ[K] V₂) : FiniteDimensional K f.range :=
  f.quotKerEquivRange.FiniteDimensional

/-- The dimensions of the domain and range of an injective linear map are equal. -/
theorem finrank_range_of_inj {f : V →ₗ[K] V₂} (hf : Function.Injective f) : finrank K f.range = finrank K V := by
  rw [(LinearEquiv.ofInjective f hf).finrank_eq]

end DivisionRing

section Field

variable [Field K] [AddCommGroupₓ V] [Module K V] {V₂ : Type v'} [AddCommGroupₓ V₂] [Module K V₂]

/-- On a finite-dimensional space, a linear map is injective if and only if it is surjective. -/
theorem injective_iff_surjective [FiniteDimensional K V] {f : V →ₗ[K] V} : Injective f ↔ Surjective f :=
  ⟨surjective_of_injective, fun hsurj =>
    let ⟨g, hg⟩ := f.exists_right_inverse_of_surjective (range_eq_top.2 hsurj)
    have : Function.RightInverse g f := LinearMap.ext_iff.1 hg
    (left_inverse_of_surjective_of_right_inverse (surjective_of_injective this.Injective) this).Injective⟩

theorem ker_eq_bot_iff_range_eq_top [FiniteDimensional K V] {f : V →ₗ[K] V} : f.ker = ⊥ ↔ f.range = ⊤ := by
  rw [range_eq_top, ker_eq_bot, injective_iff_surjective]

/-- In a finite-dimensional space, if linear maps are inverse to each other on one side then they
are also inverse to each other on the other side. -/
theorem mul_eq_one_of_mul_eq_one [FiniteDimensional K V] {f g : V →ₗ[K] V} (hfg : f * g = 1) : g * f = 1 := by
  have ginj : Injective g :=
    HasLeftInverse.injective
      ⟨f, fun x =>
        show (f * g) x = (1 : V →ₗ[K] V) x by
          rw [hfg] <;> rfl⟩
  let ⟨i, hi⟩ := g.exists_right_inverse_of_surjective (range_eq_top.2 (injective_iff_surjective.1 ginj))
  have : f * (g * i) = f * 1 := congr_arg _ hi
  rw [← mul_assoc, hfg, one_mulₓ, mul_oneₓ] at this <;> rwa [← this]

/-- In a finite-dimensional space, linear maps are inverse to each other on one side if and only if
they are inverse to each other on the other side. -/
theorem mul_eq_one_comm [FiniteDimensional K V] {f g : V →ₗ[K] V} : f * g = 1 ↔ g * f = 1 :=
  ⟨mul_eq_one_of_mul_eq_one, mul_eq_one_of_mul_eq_one⟩

/-- In a finite-dimensional space, linear maps are inverse to each other on one side if and only if
they are inverse to each other on the other side. -/
theorem comp_eq_id_comm [FiniteDimensional K V] {f g : V →ₗ[K] V} : f.comp g = id ↔ g.comp f = id :=
  mul_eq_one_comm

/-- rank-nullity theorem : the dimensions of the kernel and the range of a linear map add up to
the dimension of the source space. -/
theorem finrank_range_add_finrank_ker [FiniteDimensional K V] (f : V →ₗ[K] V₂) :
    finrank K f.range + finrank K f.ker = finrank K V := by
  rw [← f.quot_ker_equiv_range.finrank_eq]
  exact Submodule.finrank_quotient_add_finrank _

end Field

end LinearMap

namespace LinearEquiv

open FiniteDimensional

variable [Field K] [AddCommGroupₓ V] [Module K V]

variable [FiniteDimensional K V]

/-- The linear equivalence corresponging to an injective endomorphism. -/
noncomputable def ofInjectiveEndo (f : V →ₗ[K] V) (h_inj : Injective f) : V ≃ₗ[K] V :=
  LinearEquiv.ofBijective f h_inj <| LinearMap.injective_iff_surjective.mp h_inj

@[simp]
theorem coe_of_injective_endo (f : V →ₗ[K] V) (h_inj : Injective f) : ⇑(ofInjectiveEndo f h_inj) = f :=
  rfl

@[simp]
theorem of_injective_endo_right_inv (f : V →ₗ[K] V) (h_inj : Injective f) : f * (ofInjectiveEndo f h_inj).symm = 1 :=
  LinearMap.ext <| (ofInjectiveEndo f h_inj).apply_symm_apply

@[simp]
theorem of_injective_endo_left_inv (f : V →ₗ[K] V) (h_inj : Injective f) :
    ((ofInjectiveEndo f h_inj).symm : V →ₗ[K] V) * f = 1 :=
  LinearMap.ext <| (ofInjectiveEndo f h_inj).symm_apply_apply

end LinearEquiv

namespace LinearMap

variable [Field K] [AddCommGroupₓ V] [Module K V]

theorem is_unit_iff_ker_eq_bot [FiniteDimensional K V] (f : V →ₗ[K] V) : IsUnit f ↔ f.ker = ⊥ := by
  constructor
  · rintro ⟨u, rfl⟩
    exact LinearMap.ker_eq_bot_of_inverse u.inv_mul
    
  · intro h_inj
    rw [ker_eq_bot] at h_inj
    exact
      ⟨⟨f, (LinearEquiv.ofInjectiveEndo f h_inj).symm.toLinearMap, LinearEquiv.of_injective_endo_right_inv f h_inj,
          LinearEquiv.of_injective_endo_left_inv f h_inj⟩,
        rfl⟩
    

theorem is_unit_iff_range_eq_top [FiniteDimensional K V] (f : V →ₗ[K] V) : IsUnit f ↔ f.range = ⊤ := by
  rw [is_unit_iff_ker_eq_bot, ker_eq_bot_iff_range_eq_top]

end LinearMap

open Module FiniteDimensional

section

variable [DivisionRing K] [AddCommGroupₓ V] [Module K V]

section Top

@[simp]
theorem finrank_top : finrank K (⊤ : Submodule K V) = finrank K V := by
  unfold finrank
  simp [← dim_top]

end Top

theorem finrank_zero_iff_forall_zero [FiniteDimensional K V] : finrank K V = 0 ↔ ∀ x : V, x = 0 :=
  finrank_zero_iff.trans (subsingleton_iff_forall_eq 0)

/-- If `ι` is an empty type and `V` is zero-dimensional, there is a unique `ι`-indexed basis. -/
noncomputable def basisOfFinrankZero [FiniteDimensional K V] {ι : Type _} [IsEmpty ι] (hV : finrank K V = 0) :
    Basis ι K V := by
  have : Subsingleton V := finrank_zero_iff.1 hV
  exact Basis.empty _

end

namespace LinearMap

variable [Field K] [AddCommGroupₓ V] [Module K V] {V₂ : Type v'} [AddCommGroupₓ V₂] [Module K V₂]

theorem injective_iff_surjective_of_finrank_eq_finrank [FiniteDimensional K V] [FiniteDimensional K V₂]
    (H : finrank K V = finrank K V₂) {f : V →ₗ[K] V₂} : Function.Injective f ↔ Function.Surjective f := by
  have := finrank_range_add_finrank_ker f
  rw [← ker_eq_bot, ← range_eq_top]
  refine' ⟨fun h => _, fun h => _⟩
  · rw [h, finrank_bot, add_zeroₓ, H] at this
    exact eq_top_of_finrank_eq this
    
  · rw [h, finrank_top, H] at this
    exact finrank_eq_zero.1 (add_right_injective _ this)
    

theorem ker_eq_bot_iff_range_eq_top_of_finrank_eq_finrank [FiniteDimensional K V] [FiniteDimensional K V₂]
    (H : finrank K V = finrank K V₂) {f : V →ₗ[K] V₂} : f.ker = ⊥ ↔ f.range = ⊤ := by
  rw [range_eq_top, ker_eq_bot, injective_iff_surjective_of_finrank_eq_finrank H]

theorem finrank_le_finrank_of_injective [FiniteDimensional K V] [FiniteDimensional K V₂] {f : V →ₗ[K] V₂}
    (hf : Function.Injective f) : finrank K V ≤ finrank K V₂ :=
  calc
    finrank K V = finrank K f.range + finrank K f.ker := (finrank_range_add_finrank_ker f).symm
    _ = finrank K f.range := by
      rw [ker_eq_bot.2 hf, finrank_bot, add_zeroₓ]
    _ ≤ finrank K V₂ := Submodule.finrank_le _
    

/-- Given a linear map `f` between two vector spaces with the same dimension, if
`ker f = ⊥` then `linear_equiv_of_injective` is the induced isomorphism
between the two vector spaces. -/
noncomputable def linearEquivOfInjective [FiniteDimensional K V] [FiniteDimensional K V₂] (f : V →ₗ[K] V₂)
    (hf : Injective f) (hdim : finrank K V = finrank K V₂) : V ≃ₗ[K] V₂ :=
  LinearEquiv.ofBijective f hf <| (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hf

@[simp]
theorem linear_equiv_of_injective_apply [FiniteDimensional K V] [FiniteDimensional K V₂] {f : V →ₗ[K] V₂}
    (hf : Injective f) (hdim : finrank K V = finrank K V₂) (x : V) : f.linearEquivOfInjective hf hdim x = f x :=
  rfl

end LinearMap

namespace AlgHom

theorem bijective {F : Type _} [Field F] {E : Type _} [Field E] [Algebra F E] [FiniteDimensional F E] (ϕ : E →ₐ[F] E) :
    Function.Bijective ϕ :=
  have inj : Function.Injective ϕ.toLinearMap := ϕ.toRingHom.Injective
  ⟨inj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp inj⟩

end AlgHom

/-- Bijection between algebra equivalences and algebra homomorphisms -/
noncomputable def algEquivEquivAlgHom (F : Type u) [Field F] (E : Type v) [Field E] [Algebra F E]
    [FiniteDimensional F E] : (E ≃ₐ[F] E) ≃ (E →ₐ[F] E) where
  toFun := fun ϕ => ϕ.toAlgHom
  invFun := fun ϕ => AlgEquiv.ofBijective ϕ ϕ.Bijective
  left_inv := fun _ => by
    ext
    rfl
  right_inv := fun _ => by
    ext
    rfl

section

/-- A domain that is module-finite as an algebra over a field is a division ring. -/
noncomputable def divisionRingOfFiniteDimensional (F K : Type _) [Field F] [Ringₓ K] [IsDomain K] [Algebra F K]
    [FiniteDimensional F K] : DivisionRing K :=
  { ‹IsDomain K›, ‹Ringₓ K› with
    inv := fun x =>
      if H : x = 0 then 0
      else
        Classical.some <|
          (show Function.Surjective (Algebra.lmulLeft F x) from
              LinearMap.injective_iff_surjective.1 fun _ _ => (mul_right_inj' H).1)
            1,
    mul_inv_cancel := fun x hx =>
      show x * dite _ _ _ = _ by
        rw [dif_neg hx]
        exact
          Classical.some_spec
            ((show Function.Surjective (Algebra.lmulLeft F x) from
                LinearMap.injective_iff_surjective.1 fun _ _ => (mul_right_inj' hx).1)
              1),
    inv_zero := dif_pos rfl }

/-- An integral domain that is module-finite as an algebra over a field is a field. -/
noncomputable def fieldOfFiniteDimensional (F K : Type _) [Field F] [CommRingₓ K] [IsDomain K] [Algebra F K]
    [FiniteDimensional F K] : Field K :=
  { divisionRingOfFiniteDimensional F K, ‹CommRingₓ K› with }

end

namespace Submodule

section DivisionRing

variable [DivisionRing K] [AddCommGroupₓ V] [Module K V] {V₂ : Type v'} [AddCommGroupₓ V₂] [Module K V₂]

theorem lt_of_le_of_finrank_lt_finrank {s t : Submodule K V} (le : s ≤ t) (lt : finrank K s < finrank K t) : s < t :=
  lt_of_le_of_neₓ le fun h =>
    ne_of_ltₓ lt
      (by
        rw [h])

theorem lt_top_of_finrank_lt_finrank {s : Submodule K V} (lt : finrank K s < finrank K V) : s < ⊤ := by
  rw [← @finrank_top K V] at lt
  exact lt_of_le_of_finrank_lt_finrank le_top lt

theorem finrank_mono [FiniteDimensional K V] : Monotone fun s : Submodule K V => finrank K s := fun s t hst =>
  calc
    finrank K s = finrank K (comap t.Subtype s) := LinearEquiv.finrank_eq (comapSubtypeEquivOfLe hst).symm
    _ ≤ finrank K t := Submodule.finrank_le _
    

end DivisionRing

section Field

variable [Field K] [AddCommGroupₓ V] [Module K V] {V₂ : Type v'} [AddCommGroupₓ V₂] [Module K V₂]

theorem finrank_lt_finrank_of_lt [FiniteDimensional K V] {s t : Submodule K V} (hst : s < t) :
    finrank K s < finrank K t := by
  rw [LinearEquiv.finrank_eq (comap_subtype_equiv_of_le (le_of_ltₓ hst)).symm]
  refine' finrank_lt (lt_of_le_of_neₓ le_top _)
  intro h_eq_top
  rw [comap_subtype_eq_top] at h_eq_top
  apply not_le_of_lt hst h_eq_top

theorem finrank_add_eq_of_is_compl [FiniteDimensional K V] {U W : Submodule K V} (h : IsCompl U W) :
    finrank K U + finrank K W = finrank K V := by
  rw [← Submodule.dim_sup_add_dim_inf_eq, top_le_iff.1 h.2, le_bot_iff.1 h.1, finrank_bot, add_zeroₓ]
  exact finrank_top

end Field

end Submodule

section Span

open Submodule

section DivisionRing

variable [DivisionRing K] [AddCommGroupₓ V] [Module K V]

variable (K)

/-- The rank of a set of vectors as a natural number. -/
protected noncomputable def Set.finrank (s : Set V) : ℕ :=
  finrank K (span K s)

variable {K}

theorem finrank_span_le_card (s : Set V) [Fintype s] : finrank K (span K s) ≤ s.toFinset.card := by
  have := span_of_finite K s.to_finite
  have : Module.rank K (span K s) ≤ # s := dim_span_le s
  rw [← finrank_eq_dim, Cardinal.mk_fintype, ← Set.to_finset_card] at this
  exact_mod_cast this

theorem finrank_span_finset_le_card (s : Finset V) : (s : Set V).finrank K ≤ s.card :=
  calc
    (s : Set V).finrank K ≤ (s : Set V).toFinset.card := finrank_span_le_card s
    _ = s.card := by
      simp
    

theorem finrank_span_eq_card {ι : Type _} [Fintype ι] {b : ι → V} (hb : LinearIndependent K b) :
    finrank K (span K (Set.Range b)) = Fintype.card ι := by
  have : FiniteDimensional K (span K (Set.Range b)) := span_of_finite K (Set.finite_range b)
  have : Module.rank K (span K (Set.Range b)) = # (Set.Range b) := dim_span hb
  rwa [← finrank_eq_dim, ← lift_inj, mk_range_eq_of_injective hb.injective, Cardinal.mk_fintype, lift_nat_cast,
    lift_nat_cast, nat_cast_inj] at this

theorem finrank_span_set_eq_card (s : Set V) [Fintype s] (hs : LinearIndependent K (coe : s → V)) :
    finrank K (span K s) = s.toFinset.card := by
  have := span_of_finite K s.to_finite
  have : Module.rank K (span K s) = # s := dim_span_set hs
  rw [← finrank_eq_dim, Cardinal.mk_fintype, ← Set.to_finset_card] at this
  exact_mod_cast this

theorem finrank_span_finset_eq_card (s : Finset V) (hs : LinearIndependent K (coe : s → V)) :
    finrank K (span K (s : Set V)) = s.card := by
  convert finrank_span_set_eq_card (↑s) hs
  ext
  simp

theorem span_lt_of_subset_of_card_lt_finrank {s : Set V} [Fintype s] {t : Submodule K V} (subset : s ⊆ t)
    (card_lt : s.toFinset.card < finrank K t) : span K s < t :=
  lt_of_le_of_finrank_lt_finrank (span_le.mpr subset) (lt_of_le_of_ltₓ (finrank_span_le_card _) card_lt)

theorem span_lt_top_of_card_lt_finrank {s : Set V} [Fintype s] (card_lt : s.toFinset.card < finrank K V) :
    span K s < ⊤ :=
  lt_top_of_finrank_lt_finrank (lt_of_le_of_ltₓ (finrank_span_le_card _) card_lt)

theorem finrank_span_singleton {v : V} (hv : v ≠ 0) : finrank K (K∙v) = 1 := by
  apply le_antisymmₓ
  · exact finrank_span_le_card ({v} : Set V)
    
  · rw [Nat.succ_le_iff, finrank_pos_iff]
    use ⟨v, mem_span_singleton_self v⟩, 0
    simp [← hv]
    

end DivisionRing

section Field

variable [Field K] [AddCommGroupₓ V] [Module K V]

theorem Set.finrank_mono [FiniteDimensional K V] {s t : Set V} (h : s ⊆ t) : s.finrank K ≤ t.finrank K :=
  finrank_mono (span_mono h)

end Field

end Span

section Basis

section DivisionRing

variable [DivisionRing K] [AddCommGroupₓ V] [Module K V]

theorem linear_independent_of_span_eq_top_of_card_eq_finrank {ι : Type _} [Fintype ι] {b : ι → V}
    (span_eq : span K (Set.Range b) = ⊤) (card_eq : Fintype.card ι = finrank K V) : LinearIndependent K b :=
  linear_independent_iff'.mpr fun s g dependent i i_mem_s => by
    by_contra gx_ne_zero
    -- We'll derive a contradiction by showing `b '' (univ \ {i})` of cardinality `n - 1`
    -- spans a vector space of dimension `n`.
    refine'
      ne_of_ltₓ (span_lt_top_of_card_lt_finrank (show (b '' (Set.Univ \ {i})).toFinset.card < finrank K V from _)) _
    · calc (b '' (Set.Univ \ {i})).toFinset.card = ((Set.Univ \ {i}).toFinset.Image b).card := by
          rw [Set.to_finset_card, Fintype.card_of_finset]_ ≤ (Set.Univ \ {i}).toFinset.card :=
          Finset.card_image_le _ = (finset.univ.erase i).card :=
          congr_arg Finset.card
            (Finset.ext
              (by
                simp [← and_comm]))_ < finset.univ.card :=
          Finset.card_erase_lt_of_mem (Finset.mem_univ i)_ = finrank K V := card_eq
      
    -- We already have that `b '' univ` spans the whole space,
    -- so we only need to show that the span of `b '' (univ \ {i})` contains each `b j`.
    refine' trans (le_antisymmₓ (span_mono (Set.image_subset_range _ _)) (span_le.mpr _)) span_eq
    rintro _ ⟨j, rfl, rfl⟩
    -- The case that `j ≠ i` is easy because `b j ∈ b '' (univ \ {i})`.
    by_cases' j_eq : j = i
    swap
    · refine' subset_span ⟨j, (Set.mem_diff _).mpr ⟨Set.mem_univ _, _⟩, rfl⟩
      exact mt set.mem_singleton_iff.mp j_eq
      
    -- To show `b i ∈ span (b '' (univ \ {i}))`, we use that it's a weighted sum
    -- of the other `b j`s.
    rw [j_eq, SetLike.mem_coe, show b i = -((g i)⁻¹ • (s.erase i).Sum fun j => g j • b j) from _]
    · refine' neg_mem (smul_mem _ _ (sum_mem fun k hk => _))
      obtain ⟨k_ne_i, k_mem⟩ := finset.mem_erase.mp hk
      refine' smul_mem _ _ (subset_span ⟨k, _, rfl⟩)
      simpa using k_mem
      
    -- To show `b i` is a weighted sum of the other `b j`s, we'll rewrite this sum
    -- to have the form of the assumption `dependent`.
    apply eq_neg_of_add_eq_zero_left
    calc
      (b i + (g i)⁻¹ • (s.erase i).Sum fun j => g j • b j) =
          (g i)⁻¹ • (g i • b i + (s.erase i).Sum fun j => g j • b j) :=
        by
        rw [smul_add, ← mul_smul, inv_mul_cancel gx_ne_zero, one_smul]_ = (g i)⁻¹ • 0 := congr_arg _ _ _ = 0 :=
        smul_zero _
    -- And then it's just a bit of manipulation with finite sums.
    rwa [← Finset.insert_erase i_mem_s, Finset.sum_insert (Finset.not_mem_erase _ _)] at dependent

/-- A finite family of vectors is linearly independent if and only if
its cardinality equals the dimension of its span. -/
theorem linear_independent_iff_card_eq_finrank_span {ι : Type _} [Fintype ι] {b : ι → V} :
    LinearIndependent K b ↔ Fintype.card ι = (Set.Range b).finrank K := by
  constructor
  · intro h
    exact (finrank_span_eq_card h).symm
    
  · intro hc
    let f := Submodule.subtype (span K (Set.Range b))
    let b' : ι → span K (Set.Range b) := fun i => ⟨b i, mem_span.2 fun p hp => hp (Set.mem_range_self _)⟩
    have hs : span K (Set.Range b') = ⊤ := by
      rw [eq_top_iff']
      intro x
      have h : span K (f '' Set.Range b') = map f (span K (Set.Range b')) := span_image f
      have hf : f '' Set.Range b' = Set.Range b := by
        ext x
        simp [← Set.mem_image, ← Set.mem_range]
      rw [hf] at h
      have hx : (x : V) ∈ span K (Set.Range b) := x.property
      conv at hx => congr skip rw [h]
      simpa [← mem_map] using hx
    have hi : f.ker = ⊥ := ker_subtype _
    convert (linear_independent_of_span_eq_top_of_card_eq_finrank hs hc).map' _ hi
    

/-- A family of `finrank K V` vectors forms a basis if they span the whole space. -/
noncomputable def basisOfSpanEqTopOfCardEqFinrank {ι : Type _} [Fintype ι] (b : ι → V)
    (span_eq : span K (Set.Range b) = ⊤) (card_eq : Fintype.card ι = finrank K V) : Basis ι K V :=
  Basis.mk (linear_independent_of_span_eq_top_of_card_eq_finrank span_eq card_eq) span_eq

@[simp]
theorem coe_basis_of_span_eq_top_of_card_eq_finrank {ι : Type _} [Fintype ι] (b : ι → V)
    (span_eq : span K (Set.Range b) = ⊤) (card_eq : Fintype.card ι = finrank K V) :
    ⇑(basisOfSpanEqTopOfCardEqFinrank b span_eq card_eq) = b :=
  Basis.coe_mk _ _

/-- A finset of `finrank K V` vectors forms a basis if they span the whole space. -/
@[simps]
noncomputable def finsetBasisOfSpanEqTopOfCardEqFinrank {s : Finset V} (span_eq : span K (s : Set V) = ⊤)
    (card_eq : s.card = finrank K V) : Basis (s : Set V) K V :=
  basisOfSpanEqTopOfCardEqFinrank (coe : (s : Set V) → V) ((@Subtype.range_coe_subtype _ fun x => x ∈ s).symm ▸ span_eq)
    (trans (Fintype.card_coe _) card_eq)

/-- A set of `finrank K V` vectors forms a basis if they span the whole space. -/
@[simps]
noncomputable def setBasisOfSpanEqTopOfCardEqFinrank {s : Set V} [Fintype s] (span_eq : span K s = ⊤)
    (card_eq : s.toFinset.card = finrank K V) : Basis s K V :=
  basisOfSpanEqTopOfCardEqFinrank (coe : s → V) ((@Subtype.range_coe_subtype _ s).symm ▸ span_eq)
    (trans s.to_finset_card.symm card_eq)

end DivisionRing

section Field

variable [Field K] [AddCommGroupₓ V] [Module K V]

theorem span_eq_top_of_linear_independent_of_card_eq_finrank {ι : Type _} [hι : Nonempty ι] [Fintype ι] {b : ι → V}
    (lin_ind : LinearIndependent K b) (card_eq : Fintype.card ι = finrank K V) : span K (Set.Range b) = ⊤ := by
  by_cases' fin : FiniteDimensional K V
  · have := Finₓ
    by_contra ne_top
    have lt_top : span K (Set.Range b) < ⊤ := lt_of_le_of_neₓ le_top ne_top
    exact ne_of_ltₓ (Submodule.finrank_lt lt_top) (trans (finrank_span_eq_card lin_ind) card_eq)
    
  · exfalso
    apply ne_of_ltₓ (fintype.card_pos_iff.mpr hι)
    symm
    replace fin := (not_iff_not.2 IsNoetherian.iff_fg).2 Finₓ
    calc Fintype.card ι = finrank K V := card_eq _ = 0 := dif_neg (mt is_noetherian.iff_dim_lt_aleph_0.mpr Finₓ)
    

/-- A linear independent family of `finrank K V` vectors forms a basis. -/
@[simps]
noncomputable def basisOfLinearIndependentOfCardEqFinrank {ι : Type _} [Nonempty ι] [Fintype ι] {b : ι → V}
    (lin_ind : LinearIndependent K b) (card_eq : Fintype.card ι = finrank K V) : Basis ι K V :=
  Basis.mk lin_ind <| span_eq_top_of_linear_independent_of_card_eq_finrank lin_ind card_eq

@[simp]
theorem coe_basis_of_linear_independent_of_card_eq_finrank {ι : Type _} [Nonempty ι] [Fintype ι] {b : ι → V}
    (lin_ind : LinearIndependent K b) (card_eq : Fintype.card ι = finrank K V) :
    ⇑(basisOfLinearIndependentOfCardEqFinrank lin_ind card_eq) = b :=
  Basis.coe_mk _ _

/-- A linear independent finset of `finrank K V` vectors forms a basis. -/
@[simps]
noncomputable def finsetBasisOfLinearIndependentOfCardEqFinrank {s : Finset V} (hs : s.Nonempty)
    (lin_ind : LinearIndependent K (coe : s → V)) (card_eq : s.card = finrank K V) : Basis s K V :=
  @basisOfLinearIndependentOfCardEqFinrank _ _ _ _ _ _ ⟨(⟨hs.some, hs.some_spec⟩ : s)⟩ _ _ lin_ind
    (trans (Fintype.card_coe _) card_eq)

@[simp]
theorem coe_finset_basis_of_linear_independent_of_card_eq_finrank {s : Finset V} (hs : s.Nonempty)
    (lin_ind : LinearIndependent K (coe : s → V)) (card_eq : s.card = finrank K V) :
    ⇑(finsetBasisOfLinearIndependentOfCardEqFinrank hs lin_ind card_eq) = coe :=
  Basis.coe_mk _ _

/-- A linear independent set of `finrank K V` vectors forms a basis. -/
@[simps]
noncomputable def setBasisOfLinearIndependentOfCardEqFinrank {s : Set V} [Nonempty s] [Fintype s]
    (lin_ind : LinearIndependent K (coe : s → V)) (card_eq : s.toFinset.card = finrank K V) : Basis s K V :=
  basisOfLinearIndependentOfCardEqFinrank lin_ind (trans s.to_finset_card.symm card_eq)

@[simp]
theorem coe_set_basis_of_linear_independent_of_card_eq_finrank {s : Set V} [Nonempty s] [Fintype s]
    (lin_ind : LinearIndependent K (coe : s → V)) (card_eq : s.toFinset.card = finrank K V) :
    ⇑(setBasisOfLinearIndependentOfCardEqFinrank lin_ind card_eq) = coe :=
  Basis.coe_mk _ _

end Field

end Basis

/-!
We now give characterisations of `finrank K V = 1` and `finrank K V ≤ 1`.
-/


section finrank_eq_one

variable [DivisionRing K] [AddCommGroupₓ V] [Module K V]

/-- If there is a nonzero vector and every other vector is a multiple of it,
then the module has dimension one. -/
theorem finrank_eq_one (v : V) (n : v ≠ 0) (h : ∀ w : V, ∃ c : K, c • v = w) : finrank K V = 1 := by
  obtain ⟨b⟩ := (Basis.basis_singleton_iff PUnit).mpr ⟨v, n, h⟩
  rw [finrank_eq_card_basis b, Fintype.card_punit]

/-- If every vector is a multiple of some `v : V`, then `V` has dimension at most one.
-/
theorem finrank_le_one (v : V) (h : ∀ w : V, ∃ c : K, c • v = w) : finrank K V ≤ 1 := by
  rcases eq_or_ne v 0 with (rfl | hn)
  · have :=
      subsingleton_of_forall_eq (0 : V) fun w => by
        obtain ⟨c, rfl⟩ := h w
        simp
    rw [finrank_zero_of_subsingleton]
    exact zero_le_one
    
  · exact (finrank_eq_one v hn h).le
    

/-- A vector space with a nonzero vector `v` has dimension 1 iff `v` spans.
-/
theorem finrank_eq_one_iff_of_nonzero (v : V) (nz : v ≠ 0) : finrank K V = 1 ↔ span K ({v} : Set V) = ⊤ :=
  ⟨fun h => by
    simpa using (basis_singleton PUnit h v nz).span_eq, fun s =>
    finrank_eq_card_basis
      (Basis.mk (linear_independent_singleton nz)
        (by
          convert s
          simp ))⟩

/-- A module with a nonzero vector `v` has dimension 1 iff every vector is a multiple of `v`.
-/
theorem finrank_eq_one_iff_of_nonzero' (v : V) (nz : v ≠ 0) : finrank K V = 1 ↔ ∀ w : V, ∃ c : K, c • v = w := by
  rw [finrank_eq_one_iff_of_nonzero v nz]
  apply span_singleton_eq_top_iff

/-- A module has dimension 1 iff there is some `v : V` so `{v}` is a basis.
-/
theorem finrank_eq_one_iff (ι : Type _) [Unique ι] : finrank K V = 1 ↔ Nonempty (Basis ι K V) := by
  fconstructor
  · intro h
    have := finite_dimensional_of_finrank (_root_.zero_lt_one.trans_le h.symm.le)
    exact ⟨basis_unique ι h⟩
    
  · rintro ⟨b⟩
    simpa using finrank_eq_card_basis b
    

/-- A module has dimension 1 iff there is some nonzero `v : V` so every vector is a multiple of `v`.
-/
theorem finrank_eq_one_iff' : finrank K V = 1 ↔ ∃ (v : V)(n : v ≠ 0), ∀ w : V, ∃ c : K, c • v = w := by
  convert finrank_eq_one_iff PUnit
  simp only [← exists_prop, ← eq_iff_iff, ← Ne.def]
  convert (Basis.basis_singleton_iff PUnit).symm
  funext v
  simp
  infer_instance
  infer_instance

/-- A finite dimensional module has dimension at most 1 iff
there is some `v : V` so every vector is a multiple of `v`.
-/
-- Not sure why this aren't found automatically.
theorem finrank_le_one_iff [FiniteDimensional K V] : finrank K V ≤ 1 ↔ ∃ v : V, ∀ w : V, ∃ c : K, c • v = w := by
  fconstructor
  · intro h
    by_cases' h' : finrank K V = 0
    · use 0
      intro w
      use 0
      have := finrank_zero_iff.mp h'
      apply Subsingleton.elimₓ
      
    · replace h' := zero_lt_iff.mpr h'
      have : finrank K V = 1 := by
        linarith
      obtain ⟨v, -, p⟩ := finrank_eq_one_iff'.mp this
      use ⟨v, p⟩
      
    
  · rintro ⟨v, p⟩
    exact finrank_le_one v p
    

-- We use the `linear_map.compatible_smul` typeclass here, to encompass two situations:
-- * `A = K`
-- * `[field K] [algebra K A] [is_scalar_tower K A V] [is_scalar_tower K A W]`
theorem surjective_of_nonzero_of_finrank_eq_one {K : Type _} [DivisionRing K] {A : Type _} [Semiringₓ A] [Module K V]
    [Module A V] {W : Type _} [AddCommGroupₓ W] [Module K W] [Module A W] [LinearMap.CompatibleSmul V W K A]
    (h : finrank K W = 1) {f : V →ₗ[A] W} (w : f ≠ 0) : Surjective f := by
  change surjective (f.restrict_scalars K)
  obtain ⟨v, n⟩ := fun_like.ne_iff.mp w
  intro z
  obtain ⟨c, rfl⟩ := (finrank_eq_one_iff_of_nonzero' (f v) n).mp h z
  exact
    ⟨c • v, by
      simp ⟩

end finrank_eq_one

section SubalgebraDim

open Module

variable {F E : Type _} [Field F] [Field E] [Algebra F E]

theorem Subalgebra.dim_eq_one_of_eq_bot {S : Subalgebra F E} (h : S = ⊥) : Module.rank F S = 1 := by
  rw [← S.to_submodule_equiv.dim_eq, h,
    (LinearEquiv.ofEq (⊥ : Subalgebra F E).toSubmodule _ Algebra.to_submodule_bot).dim_eq, dim_span_set]
  exacts[mk_singleton _, linear_independent_singleton one_ne_zero]

@[simp]
theorem Subalgebra.dim_bot : Module.rank F (⊥ : Subalgebra F E) = 1 :=
  Subalgebra.dim_eq_one_of_eq_bot rfl

theorem subalgebra_top_dim_eq_submodule_top_dim :
    Module.rank F (⊤ : Subalgebra F E) = Module.rank F (⊤ : Submodule F E) := by
  rw [← Algebra.top_to_submodule]
  rfl

theorem subalgebra_top_finrank_eq_submodule_top_finrank :
    finrank F (⊤ : Subalgebra F E) = finrank F (⊤ : Submodule F E) := by
  rw [← Algebra.top_to_submodule]
  rfl

theorem Subalgebra.dim_top : Module.rank F (⊤ : Subalgebra F E) = Module.rank F E := by
  rw [subalgebra_top_dim_eq_submodule_top_dim]
  exact dim_top F E

instance Subalgebra.finite_dimensional_bot : FiniteDimensional F (⊥ : Subalgebra F E) :=
  finite_dimensional_of_dim_eq_one Subalgebra.dim_bot

@[simp]
theorem Subalgebra.finrank_bot : finrank F (⊥ : Subalgebra F E) = 1 := by
  have : Module.rank F (⊥ : Subalgebra F E) = 1 := Subalgebra.dim_bot
  rw [← finrank_eq_dim] at this
  norm_cast  at *
  simp [*]

theorem Subalgebra.finrank_eq_one_of_eq_bot {S : Subalgebra F E} (h : S = ⊥) : finrank F S = 1 := by
  rw [h]
  exact Subalgebra.finrank_bot

theorem Subalgebra.eq_bot_of_finrank_one {S : Subalgebra F E} (h : finrank F S = 1) : S = ⊥ := by
  rw [eq_bot_iff]
  let b : Set S := {1}
  have : Fintype b := Unique.fintype
  have b_lin_ind : LinearIndependent F (coe : b → S) := linear_independent_singleton one_ne_zero
  have b_card : Fintype.card b = 1 := Fintype.card_of_subsingleton _
  let hb :=
    setBasisOfLinearIndependentOfCardEqFinrank b_lin_ind
      (by
        simp only [*, ← Set.to_finset_card])
  have b_spans := hb.span_eq
  intro x hx
  rw [Algebra.mem_bot]
  have x_in_span_b : (⟨x, hx⟩ : S) ∈ Submodule.span F b := by
    rw [coe_set_basis_of_linear_independent_of_card_eq_finrank, Subtype.range_coe] at b_spans
    rw [b_spans]
    exact Submodule.mem_top
  obtain ⟨a, ha⟩ := submodule.mem_span_singleton.mp x_in_span_b
  replace ha : a • 1 = x := by
    injections with ha
  exact
    ⟨a, by
      rw [← ha, Algebra.smul_def, mul_oneₓ]⟩

theorem Subalgebra.eq_bot_of_dim_one {S : Subalgebra F E} (h : Module.rank F S = 1) : S = ⊥ := by
  have : FiniteDimensional F S := finite_dimensional_of_dim_eq_one h
  rw [← finrank_eq_dim] at h
  norm_cast  at h
  exact Subalgebra.eq_bot_of_finrank_one h

@[simp]
theorem Subalgebra.bot_eq_top_of_dim_eq_one (h : Module.rank F E = 1) : (⊥ : Subalgebra F E) = ⊤ := by
  rw [← dim_top, ← subalgebra_top_dim_eq_submodule_top_dim] at h
  exact Eq.symm (Subalgebra.eq_bot_of_dim_one h)

@[simp]
theorem Subalgebra.bot_eq_top_of_finrank_eq_one (h : finrank F E = 1) : (⊥ : Subalgebra F E) = ⊤ := by
  rw [← finrank_top, ← subalgebra_top_finrank_eq_submodule_top_finrank] at h
  exact Eq.symm (Subalgebra.eq_bot_of_finrank_one h)

@[simp]
theorem Subalgebra.dim_eq_one_iff {S : Subalgebra F E} : Module.rank F S = 1 ↔ S = ⊥ :=
  ⟨Subalgebra.eq_bot_of_dim_one, Subalgebra.dim_eq_one_of_eq_bot⟩

@[simp]
theorem Subalgebra.finrank_eq_one_iff {S : Subalgebra F E} : finrank F S = 1 ↔ S = ⊥ :=
  ⟨Subalgebra.eq_bot_of_finrank_one, Subalgebra.finrank_eq_one_of_eq_bot⟩

end SubalgebraDim

namespace Module

namespace End

variable [Field K] [AddCommGroupₓ V] [Module K V]

theorem exists_ker_pow_eq_ker_pow_succ [FiniteDimensional K V] (f : End K V) :
    ∃ k : ℕ, k ≤ finrank K V ∧ (f ^ k).ker = (f ^ k.succ).ker := by
  classical
  by_contra h_contra
  simp_rw [not_exists, not_and] at h_contra
  have h_le_ker_pow : ∀ n : ℕ, n ≤ (finrank K V).succ → n ≤ finrank K (f ^ n).ker := by
    intro n hn
    induction' n with n ih
    · exact zero_le (finrank _ _)
      
    · have h_ker_lt_ker : (f ^ n).ker < (f ^ n.succ).ker := by
        refine' lt_of_le_of_neₓ _ (h_contra n (Nat.le_of_succ_le_succₓ hn))
        rw [pow_succₓ]
        apply LinearMap.ker_le_ker_comp
      have h_finrank_lt_finrank : finrank K (f ^ n).ker < finrank K (f ^ n.succ).ker := by
        apply Submodule.finrank_lt_finrank_of_lt h_ker_lt_ker
      calc n.succ ≤ (finrank K ↥(LinearMap.ker (f ^ n))).succ :=
          Nat.succ_le_succₓ (ih (Nat.le_of_succ_leₓ hn))_ ≤ finrank K ↥(LinearMap.ker (f ^ n.succ)) :=
          Nat.succ_le_of_ltₓ h_finrank_lt_finrank
      
  have h_le_finrank_V : ∀ n, finrank K (f ^ n).ker ≤ finrank K V := fun n => Submodule.finrank_le _
  have h_any_n_lt : ∀ n, n ≤ (finrank K V).succ → n ≤ finrank K V := fun n hn =>
    (h_le_ker_pow n hn).trans (h_le_finrank_V n)
  show False
  exact Nat.not_succ_le_selfₓ _ (h_any_n_lt (finrank K V).succ (finrank K V).succ.le_refl)

theorem ker_pow_constant {f : End K V} {k : ℕ} (h : (f ^ k).ker = (f ^ k.succ).ker) :
    ∀ m, (f ^ k).ker = (f ^ (k + m)).ker
  | 0 => by
    simp
  | m + 1 => by
    apply le_antisymmₓ
    · rw [add_commₓ, pow_addₓ]
      apply LinearMap.ker_le_ker_comp
      
    · rw [ker_pow_constant m, add_commₓ m 1, ← add_assocₓ, pow_addₓ, pow_addₓ f k m]
      change LinearMap.ker ((f ^ (k + 1)).comp (f ^ m)) ≤ LinearMap.ker ((f ^ k).comp (f ^ m))
      rw [LinearMap.ker_comp, LinearMap.ker_comp, h, Nat.add_one]
      exact le_rfl
      

theorem ker_pow_eq_ker_pow_finrank_of_le [FiniteDimensional K V] {f : End K V} {m : ℕ} (hm : finrank K V ≤ m) :
    (f ^ m).ker = (f ^ finrank K V).ker := by
  obtain ⟨k, h_k_le, hk⟩ : ∃ k, k ≤ finrank K V ∧ LinearMap.ker (f ^ k) = LinearMap.ker (f ^ k.succ) :=
    exists_ker_pow_eq_ker_pow_succ f
  calc (f ^ m).ker = (f ^ (k + (m - k))).ker := by
      rw [add_tsub_cancel_of_le (h_k_le.trans hm)]_ = (f ^ k).ker := by
      rw [ker_pow_constant hk _]_ = (f ^ (k + (finrank K V - k))).ker :=
      ker_pow_constant hk (finrank K V - k)_ = (f ^ finrank K V).ker := by
      rw [add_tsub_cancel_of_le h_k_le]

theorem ker_pow_le_ker_pow_finrank [FiniteDimensional K V] (f : End K V) (m : ℕ) :
    (f ^ m).ker ≤ (f ^ finrank K V).ker := by
  by_cases' h_cases : m < finrank K V
  · rw [← add_tsub_cancel_of_le (Nat.le_of_ltₓ h_cases), add_commₓ, pow_addₓ]
    apply LinearMap.ker_le_ker_comp
    
  · rw [ker_pow_eq_ker_pow_finrank_of_le (le_of_not_ltₓ h_cases)]
    exact le_rfl
    

end End

end Module

