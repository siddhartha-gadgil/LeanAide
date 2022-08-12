/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johannes Hölzl, Sander Dahmen, Scott Morrison
-/
import Mathbin.LinearAlgebra.Dfinsupp
import Mathbin.LinearAlgebra.InvariantBasisNumber
import Mathbin.LinearAlgebra.Isomorphisms
import Mathbin.LinearAlgebra.StdBasis
import Mathbin.SetTheory.Cardinal.Cofinality

/-!
# Dimension of modules and vector spaces

## Main definitions

* The rank of a module is defined as `module.rank : cardinal`.
  This is defined as the supremum of the cardinalities of linearly independent subsets.

* The rank of a linear map is defined as the rank of its range.

## Main statements

* `linear_map.dim_le_of_injective`: the source of an injective linear map has dimension
  at most that of the target.
* `linear_map.dim_le_of_surjective`: the target of a surjective linear map has dimension
  at most that of that source.
* `basis_fintype_of_finite_spans`:
  the existence of a finite spanning set implies that any basis is finite.
* `infinite_basis_le_maximal_linear_independent`:
  if `b` is an infinite basis for a module `M`,
  and `s` is a maximal linearly independent set,
  then the cardinality of `b` is bounded by the cardinality of `s`.

For modules over rings satisfying the rank condition

* `basis.le_span`:
  the cardinality of a basis is bounded by the cardinality of any spanning set

For modules over rings satisfying the strong rank condition

* `linear_independent_le_span`:
  For any linearly independent family `v : ι → M`
  and any finite spanning set `w : set M`,
  the cardinality of `ι` is bounded by the cardinality of `w`.
* `linear_independent_le_basis`:
  If `b` is a basis for a module `M`,
  and `s` is a linearly independent set,
  then the cardinality of `s` is bounded by the cardinality of `b`.

For modules over rings with invariant basis number
(including all commutative rings and all noetherian rings)

* `mk_eq_mk_of_basis`: the dimension theorem, any two bases of the same vector space have the same
  cardinality.

For vector spaces (i.e. modules over a field), we have

* `dim_quotient_add_dim`: if `V₁` is a submodule of `V`, then
  `module.rank (V/V₁) + module.rank V₁ = module.rank V`.
* `dim_range_add_dim_ker`: the rank-nullity theorem.

## Implementation notes

There is a naming discrepancy: most of the theorem names refer to `dim`,
even though the definition is of `module.rank`.
This reflects that `module.rank` was originally called `dim`, and only defined for vector spaces.

Many theorems in this file are not universe-generic when they relate dimensions
in different universes. They should be as general as they can be without
inserting `lift`s. The types `V`, `V'`, ... all live in different universes,
and `V₁`, `V₂`, ... all live in the same universe.
-/


noncomputable section

universe u v v' v'' u₁' w w'

variable {K : Type u} {V V₁ V₂ V₃ : Type v} {V' V'₁ : Type v'} {V'' : Type v''}

variable {ι : Type w} {ι' : Type w'} {η : Type u₁'} {φ : η → Type _}

open Classical BigOperators Cardinal

open Basis Submodule Function Set

section Module

section

variable [Semiringₓ K] [AddCommMonoidₓ V] [Module K V]

include K

variable (K V)

/-- The rank of a module, defined as a term of type `cardinal`.

We define this as the supremum of the cardinalities of linearly independent subsets.

For a free module over any ring satisfying the strong rank condition
(e.g. left-noetherian rings, commutative rings, and in particular division rings and fields),
this is the same as the dimension of the space (i.e. the cardinality of any basis).

In particular this agrees with the usual notion of the dimension of a vector space.

The definition is marked as protected to avoid conflicts with `_root_.rank`,
the rank of a linear map.
-/
protected def Module.rank : Cardinal :=
  ⨆ ι : { s : Set V // LinearIndependent K (coe : s → V) }, # ι.1

end

section

variable {R : Type u} [Ringₓ R]

variable {M : Type v} [AddCommGroupₓ M] [Module R M]

variable {M' : Type v'} [AddCommGroupₓ M'] [Module R M']

variable {M₁ : Type v} [AddCommGroupₓ M₁] [Module R M₁]

theorem LinearMap.lift_dim_le_of_injective (f : M →ₗ[R] M') (i : Injective f) :
    Cardinal.lift.{v'} (Module.rank R M) ≤ Cardinal.lift.{v} (Module.rank R M') := by
  dsimp' [← Module.rank]
  rw [Cardinal.lift_supr (Cardinal.bdd_above_range.{v', v'} _), Cardinal.lift_supr (Cardinal.bdd_above_range.{v, v} _)]
  apply csupr_mono' (Cardinal.bdd_above_range.{v', v} _)
  rintro ⟨s, li⟩
  refine' ⟨⟨f '' s, _⟩, cardinal.lift_mk_le'.mpr ⟨(Equivₓ.Set.image f s i).toEmbedding⟩⟩
  exact (li.map' _ <| linear_map.ker_eq_bot.mpr i).Image

theorem LinearMap.dim_le_of_injective (f : M →ₗ[R] M₁) (i : Injective f) : Module.rank R M ≤ Module.rank R M₁ :=
  Cardinal.lift_le.1 (f.lift_dim_le_of_injective i)

theorem dim_le {n : ℕ} (H : ∀ s : Finset M, (LinearIndependent R fun i : s => (i : M)) → s.card ≤ n) :
    Module.rank R M ≤ n := by
  apply csupr_le'
  rintro ⟨s, li⟩
  exact linear_independent_bounded_of_finset_linear_independent_bounded H _ li

theorem lift_dim_range_le (f : M →ₗ[R] M') :
    Cardinal.lift.{v} (Module.rank R f.range) ≤ Cardinal.lift.{v'} (Module.rank R M) := by
  dsimp' [← Module.rank]
  rw [Cardinal.lift_supr (Cardinal.bdd_above_range.{v', v'} _)]
  apply csupr_le'
  rintro ⟨s, li⟩
  apply le_transₓ
  swap
  apply cardinal.lift_le.mpr
  refine' le_csupr (Cardinal.bdd_above_range.{v, v} _) ⟨range_splitting f '' s, _⟩
  · apply LinearIndependent.of_comp f.range_restrict
    convert li.comp (Equivₓ.Set.rangeSplittingImageEquiv f s) (Equivₓ.injective _) using 1
    
  · exact (cardinal.lift_mk_eq'.mpr ⟨Equivₓ.Set.rangeSplittingImageEquiv f s⟩).Ge
    

theorem dim_range_le (f : M →ₗ[R] M₁) : Module.rank R f.range ≤ Module.rank R M := by
  simpa using lift_dim_range_le f

theorem lift_dim_map_le (f : M →ₗ[R] M') (p : Submodule R M) :
    Cardinal.lift.{v} (Module.rank R (p.map f)) ≤ Cardinal.lift.{v'} (Module.rank R p) := by
  have h := lift_dim_range_le (f.comp (Submodule.subtype p))
  rwa [LinearMap.range_comp, range_subtype] at h

theorem dim_map_le (f : M →ₗ[R] M₁) (p : Submodule R M) : Module.rank R (p.map f) ≤ Module.rank R p := by
  simpa using lift_dim_map_le f p

theorem dim_le_of_submodule (s t : Submodule R M) (h : s ≤ t) : Module.rank R s ≤ Module.rank R t :=
  (ofLe h).dim_le_of_injective fun ⟨x, hx⟩ ⟨y, hy⟩ eq => Subtype.eq <| show x = y from Subtype.ext_iff_val.1 Eq

/-- Two linearly equivalent vector spaces have the same dimension, a version with different
universes. -/
theorem LinearEquiv.lift_dim_eq (f : M ≃ₗ[R] M') :
    Cardinal.lift.{v'} (Module.rank R M) = Cardinal.lift.{v} (Module.rank R M') := by
  apply le_antisymmₓ
  · exact f.to_linear_map.lift_dim_le_of_injective f.injective
    
  · exact f.symm.to_linear_map.lift_dim_le_of_injective f.symm.injective
    

/-- Two linearly equivalent vector spaces have the same dimension. -/
theorem LinearEquiv.dim_eq (f : M ≃ₗ[R] M₁) : Module.rank R M = Module.rank R M₁ :=
  Cardinal.lift_inj.1 f.lift_dim_eq

theorem dim_eq_of_injective (f : M →ₗ[R] M₁) (h : Injective f) : Module.rank R M = Module.rank R f.range :=
  (LinearEquiv.ofInjective f h).dim_eq

/-- Pushforwards of submodules along a `linear_equiv` have the same dimension. -/
theorem LinearEquiv.dim_map_eq (f : M ≃ₗ[R] M₁) (p : Submodule R M) :
    Module.rank R (p.map (f : M →ₗ[R] M₁)) = Module.rank R p :=
  (f.submoduleMap p).dim_eq.symm

variable (R M)

@[simp]
theorem dim_top : Module.rank R (⊤ : Submodule R M) = Module.rank R M := by
  have : (⊤ : Submodule R M) ≃ₗ[R] M := LinearEquiv.ofTop ⊤ rfl
  rw [this.dim_eq]

variable {R M}

theorem dim_range_of_surjective (f : M →ₗ[R] M') (h : Surjective f) : Module.rank R f.range = Module.rank R M' := by
  rw [LinearMap.range_eq_top.2 h, dim_top]

theorem dim_submodule_le (s : Submodule R M) : Module.rank R s ≤ Module.rank R M := by
  rw [← dim_top R M]
  exact dim_le_of_submodule _ _ le_top

theorem LinearMap.dim_le_of_surjective (f : M →ₗ[R] M₁) (h : Surjective f) : Module.rank R M₁ ≤ Module.rank R M := by
  rw [← dim_range_of_surjective f h]
  apply dim_range_le

theorem dim_quotient_le (p : Submodule R M) : Module.rank R (M ⧸ p) ≤ Module.rank R M :=
  (mkq p).dim_le_of_surjective (surjective_quot_mk _)

variable [Nontrivial R]

theorem cardinal_lift_le_dim_of_linear_independent.{m} {ι : Type w} {v : ι → M} (hv : LinearIndependent R v) :
    Cardinal.lift.{max v m} (# ι) ≤ Cardinal.lift.{max w m} (Module.rank R M) := by
  apply le_transₓ
  · exact cardinal.lift_mk_le.mpr ⟨(Equivₓ.ofInjective _ hv.injective).toEmbedding⟩
    
  · simp only [← Cardinal.lift_le]
    apply le_transₓ
    swap
    exact le_csupr (Cardinal.bdd_above_range.{v, v} _) ⟨range v, hv.coe_range⟩
    exact le_rfl
    

theorem cardinal_lift_le_dim_of_linear_independent' {ι : Type w} {v : ι → M} (hv : LinearIndependent R v) :
    Cardinal.lift.{v} (# ι) ≤ Cardinal.lift.{w} (Module.rank R M) :=
  cardinal_lift_le_dim_of_linear_independent.{u, v, w, 0} hv

theorem cardinal_le_dim_of_linear_independent {ι : Type v} {v : ι → M} (hv : LinearIndependent R v) :
    # ι ≤ Module.rank R M := by
  simpa using cardinal_lift_le_dim_of_linear_independent hv

theorem cardinal_le_dim_of_linear_independent' {s : Set M} (hs : LinearIndependent R (fun x => x : s → M)) :
    # s ≤ Module.rank R M :=
  cardinal_le_dim_of_linear_independent hs

variable (R M)

@[simp]
theorem dim_punit : Module.rank R PUnit = 0 := by
  apply le_bot_iff.mp
  apply csupr_le'
  rintro ⟨s, li⟩
  apply le_bot_iff.mpr
  apply cardinal.mk_emptyc_iff.mpr
  simp only [← Subtype.coe_mk]
  by_contra h
  have ne : s.nonempty := ne_empty_iff_nonempty.mp h
  simpa using LinearIndependent.ne_zero (⟨_, ne.some_mem⟩ : s) li

@[simp]
theorem dim_bot : Module.rank R (⊥ : Submodule R M) = 0 := by
  have : (⊥ : Submodule R M) ≃ₗ[R] PUnit := bot_equiv_punit
  rw [this.dim_eq, dim_punit]

variable {R M}

/-- A linearly-independent family of vectors in a module over a non-trivial ring must be finite if
the module is Noetherian. -/
theorem LinearIndependent.finite_of_is_noetherian [IsNoetherian R M] {v : ι → M} (hv : LinearIndependent R v) :
    Finite ι := by
  have hwf :=
    is_noetherian_iff_well_founded.mp
      (by
        infer_instance : IsNoetherian R M)
  refine' CompleteLattice.WellFounded.finite_of_independent hwf hv.independent_span_singleton fun i contra => _
  apply hv.ne_zero i
  have : v i ∈ R∙v i := Submodule.mem_span_singleton_self (v i)
  rwa [contra, Submodule.mem_bot] at this

theorem LinearIndependent.set_finite_of_is_noetherian [IsNoetherian R M] {s : Set M}
    (hi : LinearIndependent R (coe : s → M)) : s.Finite :=
  @Set.to_finite _ _ hi.finite_of_is_noetherian

/-- Over any nontrivial ring, the existence of a finite spanning set implies that any basis is finite.
-/
-- One might hope that a finite spanning set implies that any linearly independent set is finite.
-- While this is true over a division ring
-- (simply because any linearly independent set can be extended to a basis),
-- I'm not certain what more general statements are possible.
def basisFintypeOfFiniteSpans (w : Set M) [Fintype w] (s : span R w = ⊤) {ι : Type w} (b : Basis ι R M) : Fintype ι :=
  by
  -- We'll work by contradiction, assuming `ι` is infinite.
  apply fintypeOfNotInfinite _
  intro i
  -- Let `S` be the union of the supports of `x ∈ w` expressed as linear combinations of `b`.
  -- This is a finite set since `w` is finite.
  let S : Finset ι := finset.univ.sup fun x : w => (b.repr x).support
  let bS : Set M := b '' S
  have h : ∀, ∀ x ∈ w, ∀, x ∈ span R bS := by
    intro x m
    rw [← b.total_repr x, Finsupp.span_image_eq_map_total, Submodule.mem_map]
    use b.repr x
    simp only [← and_trueₓ, ← eq_self_iff_true, ← Finsupp.mem_supported]
    change (b.repr x).support ≤ S
    convert
      Finset.le_sup
        (by
          simp : (⟨x, m⟩ : w) ∈ Finset.univ)
    rfl
  -- Thus this finite subset of the basis elements spans the entire module.
  have k : span R bS = ⊤ := eq_top_iff.2 (le_transₓ s.ge (span_le.2 h))
  -- Now there is some `x : ι` not in `S`, since `ι` is infinite.
  obtain ⟨x, nm⟩ := Infinite.exists_not_mem_finset S
  -- However it must be in the span of the finite subset,
  have k' : b x ∈ span R bS := by
    rw [k]
    exact mem_top
  -- giving the desire contradiction.
  refine' b.linear_independent.not_mem_span_image _ k'
  exact nm

/-- Over any ring `R`, if `b` is a basis for a module `M`,
and `s` is a maximal linearly independent set,
then the union of the supports of `x ∈ s` (when written out in the basis `b`) is all of `b`.
-/
-- From [Les familles libres maximales d'un module ont-elles le meme cardinal?][lazarus1973]
theorem union_support_maximal_linear_independent_eq_range_basis {ι : Type w} (b : Basis ι R M) {κ : Type w'} (v : κ → M)
    (i : LinearIndependent R v) (m : i.Maximal) : (⋃ k, ((b.repr (v k)).support : Set ι)) = univ := by
  -- If that's not the case,
  by_contra h
  simp only [Ne.def, ← ne_univ_iff_exists_not_mem, ← mem_Union, ← not_exists_not, ← Finsupp.mem_support_iff, ←
    Finset.mem_coe] at h
  -- We have some basis element `b b'` which is not in the support of any of the `v i`.
  obtain ⟨b', w⟩ := h
  -- Using this, we'll construct a linearly independent family strictly larger than `v`,
  -- by also using this `b b'`.
  let v' : Option κ → M := fun o => o.elim (b b') v
  have r : range v ⊆ range v' := by
    rintro - ⟨k, rfl⟩
    use some k
    rfl
  have r' : b b' ∉ range v := by
    rintro ⟨k, p⟩
    simpa [← w] using congr_arg (fun m => (b.repr m) b') p
  have r'' : range v ≠ range v' := by
    intro e
    have p : b b' ∈ range v' := by
      use none
      rfl
    rw [← e] at p
    exact r' p
  have inj' : injective v' := by
    rintro (_ | k) (_ | k) z
    · rfl
      
    · exfalso
      exact r' ⟨k, z.symm⟩
      
    · exfalso
      exact r' ⟨k, z⟩
      
    · congr
      exact i.injective z
      
  -- The key step in the proof is checking that this strictly larger family is linearly independent.
  have i' : LinearIndependent R (coe : range v' → M) := by
    rw [linear_independent_subtype_range inj', linear_independent_iff]
    intro l z
    rw [Finsupp.total_option] at z
    simp only [← v', ← Option.elimₓ] at z
    change _ + Finsupp.total κ M R v l.some = 0 at z
    -- We have some linear combination of `b b'` and the `v i`, which we want to show is trivial.
    -- We'll first show the coefficient of `b b'` is zero,
    -- by expressing the `v i` in the basis `b`, and using that the `v i` have no `b b'` term.
    have l₀ : l none = 0 := by
      rw [← eq_neg_iff_add_eq_zero] at z
      replace z := eq_neg_of_eq_neg z
      apply_fun fun x => b.repr x b'  at z
      simp only [← repr_self, ← LinearEquiv.map_smul, ← mul_oneₓ, ← Finsupp.single_eq_same, ← Pi.neg_apply, ←
        Finsupp.smul_single', ← LinearEquiv.map_neg, ← Finsupp.coe_neg] at z
      erw [Finsupp.congr_fun (Finsupp.apply_total R (b.repr : M →ₗ[R] ι →₀ R) v l.some) b'] at z
      simpa [← Finsupp.total_apply, ← w] using z
    -- Then all the other coefficients are zero, because `v` is linear independent.
    have l₁ : l.some = 0 := by
      rw [l₀, zero_smul, zero_addₓ] at z
      exact linear_independent_iff.mp i _ z
    -- Finally we put those facts together to show the linear combination is trivial.
    ext (_ | a)
    · simp only [← l₀, ← Finsupp.coe_zero, ← Pi.zero_apply]
      
    · erw [Finsupp.congr_fun l₁ a]
      simp only [← Finsupp.coe_zero, ← Pi.zero_apply]
      
  dsimp' [← LinearIndependent.Maximal]  at m
  specialize m (range v') i' r
  exact r'' m

/-- Over any ring `R`, if `b` is an infinite basis for a module `M`,
and `s` is a maximal linearly independent set,
then the cardinality of `b` is bounded by the cardinality of `s`.
-/
theorem infinite_basis_le_maximal_linear_independent' {ι : Type w} (b : Basis ι R M) [Infinite ι] {κ : Type w'}
    (v : κ → M) (i : LinearIndependent R v) (m : i.Maximal) : Cardinal.lift.{w'} (# ι) ≤ Cardinal.lift.{w} (# κ) := by
  let Φ := fun k : κ => (b.repr (v k)).support
  have w₁ : # ι ≤ # (Set.Range Φ) := by
    apply Cardinal.le_range_of_union_finset_eq_top
    exact union_support_maximal_linear_independent_eq_range_basis b v i m
  have w₂ : Cardinal.lift.{w'} (# (Set.Range Φ)) ≤ Cardinal.lift.{w} (# κ) := Cardinal.mk_range_le_lift
  exact (cardinal.lift_le.mpr w₁).trans w₂

/-- Over any ring `R`, if `b` is an infinite basis for a module `M`,
and `s` is a maximal linearly independent set,
then the cardinality of `b` is bounded by the cardinality of `s`.
-/
-- (See `infinite_basis_le_maximal_linear_independent'` for the more general version
-- where the index types can live in different universes.)
theorem infinite_basis_le_maximal_linear_independent {ι : Type w} (b : Basis ι R M) [Infinite ι] {κ : Type w}
    (v : κ → M) (i : LinearIndependent R v) (m : i.Maximal) : # ι ≤ # κ :=
  Cardinal.lift_le.mp (infinite_basis_le_maximal_linear_independent' b v i m)

theorem CompleteLattice.Independent.subtype_ne_bot_le_rank [NoZeroSmulDivisors R M] {V : ι → Submodule R M}
    (hV : CompleteLattice.Independent V) :
    Cardinal.lift.{v} (# { i : ι // V i ≠ ⊥ }) ≤ Cardinal.lift.{w} (Module.rank R M) := by
  set I := { i : ι // V i ≠ ⊥ }
  have hI : ∀ i : I, ∃ v ∈ V i, v ≠ (0 : M) := by
    intro i
    rw [← Submodule.ne_bot_iff]
    exact i.prop
  choose v hvV hv using hI
  have : LinearIndependent R v := (hV.comp Subtype.coe_injective).LinearIndependent _ hvV hv
  exact cardinal_lift_le_dim_of_linear_independent' this

end

section rank_zero

variable {R : Type u} {M : Type v}

variable [Ringₓ R] [Nontrivial R] [AddCommGroupₓ M] [Module R M] [NoZeroSmulDivisors R M]

theorem dim_zero_iff_forall_zero : Module.rank R M = 0 ↔ ∀ x : M, x = 0 := by
  refine' ⟨fun h => _, fun h => _⟩
  · contrapose! h
    obtain ⟨x, hx⟩ := h
    suffices 1 ≤ Module.rank R M by
      intro h
      exact lt_irreflₓ _ (lt_of_lt_of_leₓ Cardinal.zero_lt_one (h ▸ this))
    suffices LinearIndependent R fun y : ({x} : Set M) => ↑y by
      simpa using cardinal_le_dim_of_linear_independent this
    exact linear_independent_singleton hx
    
  · have : (⊤ : Submodule R M) = ⊥ := by
      ext x
      simp [← h x]
    rw [← dim_top, this, dim_bot]
    

theorem dim_zero_iff : Module.rank R M = 0 ↔ Subsingleton M :=
  dim_zero_iff_forall_zero.trans (subsingleton_iff_forall_eq 0).symm

theorem dim_pos_iff_exists_ne_zero : 0 < Module.rank R M ↔ ∃ x : M, x ≠ 0 := by
  rw [← not_iff_not]
  simpa using dim_zero_iff_forall_zero

theorem dim_pos_iff_nontrivial : 0 < Module.rank R M ↔ Nontrivial M :=
  dim_pos_iff_exists_ne_zero.trans (nontrivial_iff_exists_ne 0).symm

theorem dim_pos [h : Nontrivial M] : 0 < Module.rank R M :=
  dim_pos_iff_nontrivial.2 h

end rank_zero

section InvariantBasisNumber

variable {R : Type u} [Ringₓ R] [InvariantBasisNumber R]

variable {M : Type v} [AddCommGroupₓ M] [Module R M]

/-- The dimension theorem: if `v` and `v'` are two bases, their index types
have the same cardinalities. -/
theorem mk_eq_mk_of_basis (v : Basis ι R M) (v' : Basis ι' R M) : Cardinal.lift.{w'} (# ι) = Cardinal.lift.{w} (# ι') :=
  by
  have := nontrivial_of_invariant_basis_number R
  cases fintypeOrInfinite ι
  · -- `v` is a finite basis, so by `basis_fintype_of_finite_spans` so is `v'`.
    have : Fintype (range v) := Set.fintypeRange v
    have := basisFintypeOfFiniteSpans _ v.span_eq v'
    -- We clean up a little:
    rw [Cardinal.mk_fintype, Cardinal.mk_fintype]
    simp only [← Cardinal.lift_nat_cast, ← Cardinal.nat_cast_inj]
    -- Now we can use invariant basis number to show they have the same cardinality.
    apply card_eq_of_lequiv R
    exact
      (Finsupp.linearEquivFunOnFintype R R ι).symm.trans v.repr.symm ≪≫ₗ v'.repr ≪≫ₗ
        Finsupp.linearEquivFunOnFintype R R ι'
    
  · -- `v` is an infinite basis,
    -- so by `infinite_basis_le_maximal_linear_independent`, `v'` is at least as big,
    -- and then applying `infinite_basis_le_maximal_linear_independent` again
    -- we see they have the same cardinality.
    have w₁ := infinite_basis_le_maximal_linear_independent' v _ v'.linear_independent v'.maximal
    rcases cardinal.lift_mk_le'.mp w₁ with ⟨f⟩
    have : Infinite ι' := Infinite.of_injective f f.2
    have w₂ := infinite_basis_le_maximal_linear_independent' v' _ v.linear_independent v.maximal
    exact le_antisymmₓ w₁ w₂
    

/-- Given two bases indexed by `ι` and `ι'` of an `R`-module, where `R` satisfies the invariant
basis number property, an equiv `ι ≃ ι' `. -/
def Basis.indexEquiv (v : Basis ι R M) (v' : Basis ι' R M) : ι ≃ ι' :=
  Nonempty.some (Cardinal.lift_mk_eq.1 (Cardinal.lift_umax_eq.2 (mk_eq_mk_of_basis v v')))

theorem mk_eq_mk_of_basis' {ι' : Type w} (v : Basis ι R M) (v' : Basis ι' R M) : # ι = # ι' :=
  Cardinal.lift_inj.1 <| mk_eq_mk_of_basis v v'

end InvariantBasisNumber

section RankCondition

variable {R : Type u} [Ringₓ R] [RankCondition R]

variable {M : Type v} [AddCommGroupₓ M] [Module R M]

/-- An auxiliary lemma for `basis.le_span`.

If `R` satisfies the rank condition,
then for any finite basis `b : basis ι R M`,
and any finite spanning set `w : set M`,
the cardinality of `ι` is bounded by the cardinality of `w`.
-/
theorem Basis.le_span'' {ι : Type _} [Fintype ι] (b : Basis ι R M) {w : Set M} [Fintype w] (s : span R w = ⊤) :
    Fintype.card ι ≤ Fintype.card w := by
  -- We construct an surjective linear map `(w → R) →ₗ[R] (ι → R)`,
  -- by expressing a linear combination in `w` as a linear combination in `ι`.
  fapply card_le_of_surjective' R
  · exact b.repr.to_linear_map.comp (Finsupp.total w M R coe)
    
  · apply surjective.comp
    apply LinearEquiv.surjective
    rw [← LinearMap.range_eq_top, Finsupp.range_total]
    simpa using s
    

/-- Another auxiliary lemma for `basis.le_span`, which does not require assuming the basis is finite,
but still assumes we have a finite spanning set.
-/
theorem basis_le_span' {ι : Type _} (b : Basis ι R M) {w : Set M} [Fintype w] (s : span R w = ⊤) :
    # ι ≤ Fintype.card w := by
  have := nontrivial_of_invariant_basis_number R
  have := basisFintypeOfFiniteSpans w s b
  rw [Cardinal.mk_fintype ι]
  simp only [← Cardinal.nat_cast_le]
  exact Basis.le_span'' b s

/-- If `R` satisfies the rank condition,
then the cardinality of any basis is bounded by the cardinality of any spanning set.
-/
-- Note that if `R` satisfies the strong rank condition,
-- this also follows from `linear_independent_le_span` below.
theorem Basis.le_span {J : Set M} (v : Basis ι R M) (hJ : span R J = ⊤) : # (Range v) ≤ # J := by
  have := nontrivial_of_invariant_basis_number R
  cases fintypeOrInfinite J
  · rw [← Cardinal.lift_le, Cardinal.mk_range_eq_of_injective v.injective, Cardinal.mk_fintype J]
    convert Cardinal.lift_le.{w, v}.2 (basis_le_span' v hJ)
    simp
    
  · have := Cardinal.mk_range_eq_of_injective v.injective
    let S : J → Set ι := fun j => ↑(v.repr j).support
    let S' : J → Set M := fun j => v '' S j
    have hs : range v ⊆ ⋃ j, S' j := by
      intro b hb
      rcases mem_range.1 hb with ⟨i, hi⟩
      have : span R J ≤ comap v.repr.to_linear_map (Finsupp.supported R R (⋃ j, S j)) :=
        span_le.2 fun j hj x hx => ⟨_, ⟨⟨j, hj⟩, rfl⟩, hx⟩
      rw [hJ] at this
      replace : v.repr (v i) ∈ Finsupp.supported R R (⋃ j, S j) := this trivialₓ
      rw [v.repr_self, Finsupp.mem_supported, Finsupp.support_single_ne_zero _ one_ne_zero] at this
      · subst b
        rcases mem_Union.1 (this (Finset.mem_singleton_self _)) with ⟨j, hj⟩
        exact mem_Union.2 ⟨j, (mem_image _ _ _).2 ⟨i, hj, rfl⟩⟩
        
      · infer_instance
        
    refine' le_of_not_ltₓ fun IJ => _
    suffices # (⋃ j, S' j) < # (range v) by
      exact not_le_of_lt this ⟨Set.embeddingOfSubset _ _ hs⟩
    refine' lt_of_le_of_ltₓ (le_transₓ Cardinal.mk_Union_le_sum_mk (Cardinal.sum_le_sum _ (fun _ => ℵ₀) _)) _
    · exact fun j => (Cardinal.lt_aleph_0_of_finite _).le
      
    · simpa
      
    

end RankCondition

section StrongRankCondition

variable {R : Type u} [Ringₓ R] [StrongRankCondition R]

variable {M : Type v} [AddCommGroupₓ M] [Module R M]

open Submodule

-- An auxiliary lemma for `linear_independent_le_span'`,
-- with the additional assumption that the linearly independent family is finite.
theorem linear_independent_le_span_aux' {ι : Type _} [Fintype ι] (v : ι → M) (i : LinearIndependent R v) (w : Set M)
    [Fintype w] (s : Range v ≤ span R w) : Fintype.card ι ≤ Fintype.card w := by
  -- We construct an injective linear map `(ι → R) →ₗ[R] (w → R)`,
  -- by thinking of `f : ι → R` as a linear combination of the finite family `v`,
  -- and expressing that (using the axiom of choice) as a linear combination over `w`.
  -- We can do this linearly by constructing the map on a basis.
  fapply card_le_of_injective' R
  · apply Finsupp.total
    exact fun i => Span.repr R w ⟨v i, s (mem_range_self i)⟩
    
  · intro f g h
    apply_fun Finsupp.total w M R coe  at h
    simp only [← Finsupp.total_total, ← Submodule.coe_mk, ← Span.finsupp_total_repr] at h
    rw [← sub_eq_zero, ← LinearMap.map_sub] at h
    exact sub_eq_zero.mp (linear_independent_iff.mp i _ h)
    

/-- If `R` satisfies the strong rank condition,
then any linearly independent family `v : ι → M`
contained in the span of some finite `w : set M`,
is itself finite.
-/
def linearIndependentFintypeOfLeSpanFintype {ι : Type _} (v : ι → M) (i : LinearIndependent R v) (w : Set M) [Fintype w]
    (s : Range v ≤ span R w) : Fintype ι :=
  fintypeOfFinsetCardLe (Fintype.card w) fun t => by
    let v' := fun x : (t : Set ι) => v x
    have i' : LinearIndependent R v' := i.comp _ Subtype.val_injective
    have s' : range v' ≤ span R w := (range_comp_subset_range _ _).trans s
    simpa using linear_independent_le_span_aux' v' i' w s'

/-- If `R` satisfies the strong rank condition,
then for any linearly independent family `v : ι → M`
contained in the span of some finite `w : set M`,
the cardinality of `ι` is bounded by the cardinality of `w`.
-/
theorem linear_independent_le_span' {ι : Type _} (v : ι → M) (i : LinearIndependent R v) (w : Set M) [Fintype w]
    (s : Range v ≤ span R w) : # ι ≤ Fintype.card w := by
  have : Fintype ι := linearIndependentFintypeOfLeSpanFintype v i w s
  rw [Cardinal.mk_fintype]
  simp only [← Cardinal.nat_cast_le]
  exact linear_independent_le_span_aux' v i w s

/-- If `R` satisfies the strong rank condition,
then for any linearly independent family `v : ι → M`
and any finite spanning set `w : set M`,
the cardinality of `ι` is bounded by the cardinality of `w`.
-/
theorem linear_independent_le_span {ι : Type _} (v : ι → M) (i : LinearIndependent R v) (w : Set M) [Fintype w]
    (s : span R w = ⊤) : # ι ≤ Fintype.card w := by
  apply linear_independent_le_span' v i w
  rw [s]
  exact le_top

/-- An auxiliary lemma for `linear_independent_le_basis`:
we handle the case where the basis `b` is infinite.
-/
theorem linear_independent_le_infinite_basis {ι : Type _} (b : Basis ι R M) [Infinite ι] {κ : Type _} (v : κ → M)
    (i : LinearIndependent R v) : # κ ≤ # ι := by
  by_contra
  rw [not_leₓ, ← Cardinal.mk_finset_of_infinite ι] at h
  let Φ := fun k : κ => (b.repr (v k)).support
  obtain ⟨s, w : Infinite ↥(Φ ⁻¹' {s})⟩ :=
    Cardinal.exists_infinite_fiber Φ h
      (by
        infer_instance)
  let v' := fun k : Φ ⁻¹' {s} => v k
  have i' : LinearIndependent R v' := i.comp _ Subtype.val_injective
  have w' : Fintype (Φ ⁻¹' {s}) := by
    apply linearIndependentFintypeOfLeSpanFintype v' i' (s.image b)
    rintro m ⟨⟨p, ⟨rfl⟩⟩, rfl⟩
    simp only [← SetLike.mem_coe, ← Subtype.coe_mk, ← Finset.coe_image]
    apply Basis.mem_span_repr_support
  exact w.false

/-- Over any ring `R` satisfying the strong rank condition,
if `b` is a basis for a module `M`,
and `s` is a linearly independent set,
then the cardinality of `s` is bounded by the cardinality of `b`.
-/
theorem linear_independent_le_basis {ι : Type _} (b : Basis ι R M) {κ : Type _} (v : κ → M)
    (i : LinearIndependent R v) : # κ ≤ # ι := by
  -- We split into cases depending on whether `ι` is infinite.
    cases fintypeOrInfinite ι <;>
    skip
  · -- When `ι` is finite, we have `linear_independent_le_span`,
    rw [Cardinal.mk_fintype ι]
    have : Nontrivial R := nontrivial_of_invariant_basis_number R
    rw [Fintype.card_congr (Equivₓ.ofInjective b b.injective)]
    exact linear_independent_le_span v i (range b) b.span_eq
    
  · -- and otherwise we have `linear_indepedent_le_infinite_basis`.
    exact linear_independent_le_infinite_basis b v i
    

/-- In an `n`-dimensional space, the rank is at most `m`. -/
theorem Basis.card_le_card_of_linear_independent_aux {R : Type _} [Ringₓ R] [StrongRankCondition R] (n : ℕ) {m : ℕ}
    (v : Finₓ m → Finₓ n → R) : LinearIndependent R v → m ≤ n := fun h => by
  simpa using linear_independent_le_basis (Pi.basisFun R (Finₓ n)) v h

/-- Over any ring `R` satisfying the strong rank condition,
if `b` is an infinite basis for a module `M`,
then every maximal linearly independent set has the same cardinality as `b`.

This proof (along with some of the lemmas above) comes from
[Les familles libres maximales d'un module ont-elles le meme cardinal?][lazarus1973]
-/
-- When the basis is not infinite this need not be true!
theorem maximal_linear_independent_eq_infinite_basis {ι : Type _} (b : Basis ι R M) [Infinite ι] {κ : Type _}
    (v : κ → M) (i : LinearIndependent R v) (m : i.Maximal) : # κ = # ι := by
  apply le_antisymmₓ
  · exact linear_independent_le_basis b v i
    
  · have : Nontrivial R := nontrivial_of_invariant_basis_number R
    exact infinite_basis_le_maximal_linear_independent b v i m
    

theorem Basis.mk_eq_dim'' {ι : Type v} (v : Basis ι R M) : # ι = Module.rank R M := by
  have := nontrivial_of_invariant_basis_number R
  apply le_antisymmₓ
  · trans
    swap
    apply le_csupr (Cardinal.bdd_above_range.{v, v} _)
    exact
      ⟨Set.Range v, by
        convert v.reindex_range.linear_independent
        ext
        simp ⟩
    exact (Cardinal.mk_range_eq v v.injective).Ge
    
  · apply csupr_le'
    rintro ⟨s, li⟩
    apply linear_independent_le_basis v _ li
    

-- By this stage we want to have a complete API for `module.rank`,
-- so we set it `irreducible` here, to keep ourselves honest.
theorem Basis.mk_range_eq_dim (v : Basis ι R M) : # (Range v) = Module.rank R M :=
  v.reindexRange.mk_eq_dim''

/-- If a vector space has a finite basis, then its dimension (seen as a cardinal) is equal to the
cardinality of the basis. -/
theorem dim_eq_card_basis {ι : Type w} [Fintype ι] (h : Basis ι R M) : Module.rank R M = Fintype.card ι := by
  have := nontrivial_of_invariant_basis_number R
  rw [← h.mk_range_eq_dim, Cardinal.mk_fintype, Set.card_range_of_injective h.injective]

theorem Basis.card_le_card_of_linear_independent {ι : Type _} [Fintype ι] (b : Basis ι R M) {ι' : Type _} [Fintype ι']
    {v : ι' → M} (hv : LinearIndependent R v) : Fintype.card ι' ≤ Fintype.card ι := by
  let this := nontrivial_of_invariant_basis_number R
  simpa [← dim_eq_card_basis b, ← Cardinal.mk_fintype] using cardinal_lift_le_dim_of_linear_independent' hv

theorem Basis.card_le_card_of_submodule (N : Submodule R M) [Fintype ι] (b : Basis ι R M) [Fintype ι']
    (b' : Basis ι' R N) : Fintype.card ι' ≤ Fintype.card ι :=
  b.card_le_card_of_linear_independent (b'.LinearIndependent.map' N.Subtype N.ker_subtype)

theorem Basis.card_le_card_of_le {N O : Submodule R M} (hNO : N ≤ O) [Fintype ι] (b : Basis ι R O) [Fintype ι']
    (b' : Basis ι' R N) : Fintype.card ι' ≤ Fintype.card ι :=
  b.card_le_card_of_linear_independent (b'.LinearIndependent.map' (Submodule.ofLe hNO) (N.ker_of_le O _))

theorem Basis.mk_eq_dim (v : Basis ι R M) : Cardinal.lift.{v} (# ι) = Cardinal.lift.{w} (Module.rank R M) := by
  have := nontrivial_of_invariant_basis_number R
  rw [← v.mk_range_eq_dim, Cardinal.mk_range_eq_of_injective v.injective]

theorem Basis.mk_eq_dim'.{m} (v : Basis ι R M) :
    Cardinal.lift.{max v m} (# ι) = Cardinal.lift.{max w m} (Module.rank R M) := by
  simpa using v.mk_eq_dim

/-- If a module has a finite dimension, all bases are indexed by a finite type. -/
theorem Basis.nonempty_fintype_index_of_dim_lt_aleph_0 {ι : Type _} (b : Basis ι R M) (h : Module.rank R M < ℵ₀) :
    Nonempty (Fintype ι) := by
  rwa [← Cardinal.lift_lt, ←
    b.mk_eq_dim,-- ensure `aleph_0` has the correct universe
    Cardinal.lift_aleph_0,
    ← Cardinal.lift_aleph_0.{u_1, v}, Cardinal.lift_lt, Cardinal.lt_aleph_0_iff_fintype] at h

/-- If a module has a finite dimension, all bases are indexed by a finite type. -/
noncomputable def Basis.fintypeIndexOfDimLtAleph0 {ι : Type _} (b : Basis ι R M) (h : Module.rank R M < ℵ₀) :
    Fintype ι :=
  Classical.choice (b.nonempty_fintype_index_of_dim_lt_aleph_0 h)

/-- If a module has a finite dimension, all bases are indexed by a finite set. -/
theorem Basis.finite_index_of_dim_lt_aleph_0 {ι : Type _} {s : Set ι} (b : Basis s R M) (h : Module.rank R M < ℵ₀) :
    s.Finite :=
  finite_def.2 (b.nonempty_fintype_index_of_dim_lt_aleph_0 h)

theorem dim_span {v : ι → M} (hv : LinearIndependent R v) : Module.rank R ↥(span R (Range v)) = # (Range v) := by
  have := nontrivial_of_invariant_basis_number R
  rw [← Cardinal.lift_inj, ← (Basis.span hv).mk_eq_dim,
    Cardinal.mk_range_eq_of_injective (@LinearIndependent.injective ι R M v _ _ _ _ hv)]

theorem dim_span_set {s : Set M} (hs : LinearIndependent R (fun x => x : s → M)) : Module.rank R ↥(span R s) = # s := by
  rw [← @set_of_mem_eq _ s, ← Subtype.range_coe_subtype]
  exact dim_span hs

/-- If `N` is a submodule in a free, finitely generated module,
do induction on adjoining a linear independent element to a submodule. -/
def Submodule.inductionOnRank [IsDomain R] [Fintype ι] (b : Basis ι R M) (P : Submodule R M → Sort _)
    (ih :
      ∀ N : Submodule R M,
        (∀, ∀ N' ≤ N, ∀, ∀ x ∈ N, ∀, (∀ (c : R), ∀ y ∈ N', ∀, c • x + y = (0 : M) → c = 0) → P N') → P N)
    (N : Submodule R M) : P N :=
  Submodule.inductionOnRankAux b P ih (Fintype.card ι) N fun s hs hli => by
    simpa using b.card_le_card_of_linear_independent hli

/-- If `S` a finite-dimensional ring extension of `R` which is free as an `R`-module,
then the rank of an ideal `I` of `S` over `R` is the same as the rank of `S`.
-/
theorem Ideal.rank_eq {R S : Type _} [CommRingₓ R] [StrongRankCondition R] [Ringₓ S] [IsDomain S] [Algebra R S]
    {n m : Type _} [Fintype n] [Fintype m] (b : Basis n R S) {I : Ideal S} (hI : I ≠ ⊥) (c : Basis m R I) :
    Fintype.card m = Fintype.card n := by
  obtain ⟨a, ha⟩ := Submodule.nonzero_mem_of_bot_lt (bot_lt_iff_ne_bot.mpr hI)
  have : LinearIndependent R fun i => b i • a := by
    have hb := b.linear_independent
    rw [Fintype.linear_independent_iff] at hb⊢
    intro g hg
    apply hb g
    simp only [smul_assoc, Finset.sum_smul, ← smul_eq_zero] at hg
    exact hg.resolve_right ha
  exact
    le_antisymmₓ
      (b.card_le_card_of_linear_independent
        (c.linear_independent.map' (Submodule.subtype I) (linear_map.ker_eq_bot.mpr Subtype.coe_injective)))
      (c.card_le_card_of_linear_independent this)

variable (R)

@[simp]
theorem dim_self : Module.rank R R = 1 := by
  rw [← Cardinal.lift_inj, ← (Basis.singleton PUnit R).mk_eq_dim, Cardinal.mk_punit]

end StrongRankCondition

section DivisionRing

variable [DivisionRing K] [AddCommGroupₓ V] [Module K V] [AddCommGroupₓ V₁] [Module K V₁]

variable {K V}

/-- If a vector space has a finite dimension, the index set of `basis.of_vector_space` is finite. -/
theorem Basis.finite_of_vector_space_index_of_dim_lt_aleph_0 (h : Module.rank K V < ℵ₀) :
    (Basis.OfVectorSpaceIndex K V).Finite :=
  finite_def.2 <| (Basis.ofVectorSpace K V).nonempty_fintype_index_of_dim_lt_aleph_0 h

variable [AddCommGroupₓ V'] [Module K V']

/-- Two vector spaces are isomorphic if they have the same dimension. -/
theorem nonempty_linear_equiv_of_lift_dim_eq
    (cond : Cardinal.lift.{v'} (Module.rank K V) = Cardinal.lift.{v} (Module.rank K V')) : Nonempty (V ≃ₗ[K] V') := by
  let B := Basis.ofVectorSpace K V
  let B' := Basis.ofVectorSpace K V'
  have : Cardinal.lift.{v', v} (# _) = Cardinal.lift.{v, v'} (# _) := by
    rw [B.mk_eq_dim'', cond, B'.mk_eq_dim'']
  exact (Cardinal.lift_mk_eq.{v, v', 0}.1 this).map (B.equiv B')

/-- Two vector spaces are isomorphic if they have the same dimension. -/
theorem nonempty_linear_equiv_of_dim_eq (cond : Module.rank K V = Module.rank K V₁) : Nonempty (V ≃ₗ[K] V₁) :=
  nonempty_linear_equiv_of_lift_dim_eq <| congr_arg _ cond

section

variable (V V' V₁)

/-- Two vector spaces are isomorphic if they have the same dimension. -/
def LinearEquiv.ofLiftDimEq (cond : Cardinal.lift.{v'} (Module.rank K V) = Cardinal.lift.{v} (Module.rank K V')) :
    V ≃ₗ[K] V' :=
  Classical.choice (nonempty_linear_equiv_of_lift_dim_eq cond)

/-- Two vector spaces are isomorphic if they have the same dimension. -/
def LinearEquiv.ofDimEq (cond : Module.rank K V = Module.rank K V₁) : V ≃ₗ[K] V₁ :=
  Classical.choice (nonempty_linear_equiv_of_dim_eq cond)

end

/-- Two vector spaces are isomorphic if and only if they have the same dimension. -/
theorem LinearEquiv.nonempty_equiv_iff_lift_dim_eq :
    Nonempty (V ≃ₗ[K] V') ↔ Cardinal.lift.{v'} (Module.rank K V) = Cardinal.lift.{v} (Module.rank K V') :=
  ⟨fun ⟨h⟩ => LinearEquiv.lift_dim_eq h, fun h => nonempty_linear_equiv_of_lift_dim_eq h⟩

/-- Two vector spaces are isomorphic if and only if they have the same dimension. -/
theorem LinearEquiv.nonempty_equiv_iff_dim_eq : Nonempty (V ≃ₗ[K] V₁) ↔ Module.rank K V = Module.rank K V₁ :=
  ⟨fun ⟨h⟩ => LinearEquiv.dim_eq h, fun h => nonempty_linear_equiv_of_dim_eq h⟩

-- TODO how far can we generalise this?
-- When `s` is finite, we could prove this for any ring satisfying the strong rank condition
-- using `linear_independent_le_span'`
theorem dim_span_le (s : Set V) : Module.rank K (span K s) ≤ # s := by
  obtain ⟨b, hb, hsab, hlib⟩ := exists_linear_independent K s
  convert Cardinal.mk_le_mk_of_subset hb
  rw [← hsab, dim_span_set hlib]

theorem dim_span_of_finset (s : Finset V) : Module.rank K (span K (↑s : Set V)) < ℵ₀ :=
  calc
    Module.rank K (span K (↑s : Set V)) ≤ # (↑s : Set V) := dim_span_le ↑s
    _ = s.card := by
      rw [Finset.coe_sort_coe, Cardinal.mk_coe_finset]
    _ < ℵ₀ := Cardinal.nat_lt_aleph_0 _
    

theorem dim_prod : Module.rank K (V × V₁) = Module.rank K V + Module.rank K V₁ := by
  let b := Basis.ofVectorSpace K V
  let c := Basis.ofVectorSpace K V₁
  rw [← Cardinal.lift_inj, ← (Basis.prod b c).mk_eq_dim, Cardinal.lift_add, ← Cardinal.mk_ulift, ← b.mk_eq_dim, ←
    c.mk_eq_dim, ← Cardinal.mk_ulift, ← Cardinal.mk_ulift, Cardinal.add_def (ULift _)]
  exact Cardinal.lift_inj.1 (Cardinal.lift_mk_eq.2 ⟨equiv.ulift.trans (Equivₓ.sumCongr Equivₓ.ulift Equivₓ.ulift).symm⟩)

section Fintype

variable [Fintype η]

variable [∀ i, AddCommGroupₓ (φ i)] [∀ i, Module K (φ i)]

open LinearMap

theorem dim_pi : Module.rank K (∀ i, φ i) = Cardinal.sum fun i => Module.rank K (φ i) := by
  let b := fun i => Basis.ofVectorSpace K (φ i)
  let this : Basis (Σj, _) K (∀ j, φ j) := Pi.basis b
  rw [← Cardinal.lift_inj, ← this.mk_eq_dim]
  simp [(b _).mk_range_eq_dim]

theorem dim_fun {V η : Type u} [Fintype η] [AddCommGroupₓ V] [Module K V] :
    Module.rank K (η → V) = Fintype.card η * Module.rank K V := by
  rw [dim_pi, Cardinal.sum_const', Cardinal.mk_fintype]

theorem dim_fun_eq_lift_mul :
    Module.rank K (η → V) = (Fintype.card η : Cardinal.{max u₁' v}) * Cardinal.lift.{u₁'} (Module.rank K V) := by
  rw [dim_pi, Cardinal.sum_const, Cardinal.mk_fintype, Cardinal.lift_nat_cast]

theorem dim_fun' : Module.rank K (η → K) = Fintype.card η := by
  rw [dim_fun_eq_lift_mul, dim_self, Cardinal.lift_one, mul_oneₓ, Cardinal.nat_cast_inj]

theorem dim_fin_fun (n : ℕ) : Module.rank K (Finₓ n → K) = n := by
  simp [← dim_fun']

end Fintype

end DivisionRing

section Field

variable [Field K] [AddCommGroupₓ V] [Module K V] [AddCommGroupₓ V₁] [Module K V₁]

variable [AddCommGroupₓ V'] [Module K V']

theorem dim_quotient_add_dim (p : Submodule K V) : Module.rank K (V ⧸ p) + Module.rank K p = Module.rank K V := by
  classical <;>
    exact
      let ⟨f⟩ := quotient_prod_linear_equiv p
      dim_prod.symm.trans f.dim_eq

/-- rank-nullity theorem -/
theorem dim_range_add_dim_ker (f : V →ₗ[K] V₁) : Module.rank K f.range + Module.rank K f.ker = Module.rank K V := by
  have := fun p : Submodule K V => Classical.decEq (V ⧸ p)
  rw [← f.quot_ker_equiv_range.dim_eq, dim_quotient_add_dim]

theorem dim_eq_of_surjective (f : V →ₗ[K] V₁) (h : Surjective f) :
    Module.rank K V = Module.rank K V₁ + Module.rank K f.ker := by
  rw [← dim_range_add_dim_ker f, ← dim_range_of_surjective f h]

section

variable [AddCommGroupₓ V₂] [Module K V₂]

variable [AddCommGroupₓ V₃] [Module K V₃]

open LinearMap

/-- This is mostly an auxiliary lemma for `dim_sup_add_dim_inf_eq`. -/
theorem dim_add_dim_split (db : V₂ →ₗ[K] V) (eb : V₃ →ₗ[K] V) (cd : V₁ →ₗ[K] V₂) (ce : V₁ →ₗ[K] V₃)
    (hde : ⊤ ≤ db.range⊔eb.range) (hgd : ker cd = ⊥) (eq : db.comp cd = eb.comp ce)
    (eq₂ : ∀ d e, db d = eb e → ∃ c, cd c = d ∧ ce c = e) :
    Module.rank K V + Module.rank K V₁ = Module.rank K V₂ + Module.rank K V₃ := by
  have hf : Surjective (coprod db eb) := by
    rwa [← range_eq_top, range_coprod, eq_top_iff]
  conv => rhs rw [← dim_prod, dim_eq_of_surjective _ hf]
  congr 1
  apply LinearEquiv.dim_eq
  refine' LinearEquiv.ofBijective _ _ _
  · refine' cod_restrict _ (Prod cd (-ce)) _
    · intro c
      simp only [← add_eq_zero_iff_eq_neg, ← LinearMap.prod_apply, ← mem_ker, ← Pi.prod, ← coprod_apply, ← neg_negₓ, ←
        map_neg, ← neg_apply]
      exact LinearMap.ext_iff.1 Eq c
      
    
  · rw [← ker_eq_bot, ker_cod_restrict, ker_prod, hgd, bot_inf_eq]
    
  · rw [← range_eq_top, eq_top_iff, range_cod_restrict, ← map_le_iff_le_comap, map_top, range_subtype]
    rintro ⟨d, e⟩
    have h := eq₂ d (-e)
    simp only [← add_eq_zero_iff_eq_neg, ← LinearMap.prod_apply, ← mem_ker, ← SetLike.mem_coe, ← Prod.mk.inj_iff, ←
      coprod_apply, ← map_neg, ← neg_apply, ← LinearMap.mem_range, ← Pi.prod] at h⊢
    intro hde
    rcases h hde with ⟨c, h₁, h₂⟩
    refine' ⟨c, h₁, _⟩
    rw [h₂, _root_.neg_neg]
    

theorem dim_sup_add_dim_inf_eq (s t : Submodule K V) :
    Module.rank K (s⊔t : Submodule K V) + Module.rank K (s⊓t : Submodule K V) = Module.rank K s + Module.rank K t :=
  dim_add_dim_split (ofLe le_sup_left) (ofLe le_sup_right) (ofLe inf_le_left) (ofLe inf_le_right)
    (by
      rw [← map_le_map_iff' (ker_subtype <| s⊔t), map_sup, map_top, ← LinearMap.range_comp, ← LinearMap.range_comp,
        subtype_comp_of_le, subtype_comp_of_le, range_subtype, range_subtype, range_subtype]
      exact le_rfl)
    (ker_of_le _ _ _)
    (by
      ext ⟨x, hx⟩
      rfl)
    (by
      rintro ⟨b₁, hb₁⟩ ⟨b₂, hb₂⟩ eq
      obtain rfl : b₁ = b₂ := congr_arg Subtype.val Eq
      exact ⟨⟨b₁, hb₁, hb₂⟩, rfl, rfl⟩)

theorem dim_add_le_dim_add_dim (s t : Submodule K V) :
    Module.rank K (s⊔t : Submodule K V) ≤ Module.rank K s + Module.rank K t := by
  rw [← dim_sup_add_dim_inf_eq]
  exact self_le_add_right _ _

end

theorem exists_mem_ne_zero_of_dim_pos {s : Submodule K V} (h : 0 < Module.rank K s) : ∃ b : V, b ∈ s ∧ b ≠ 0 :=
  exists_mem_ne_zero_of_ne_bot fun eq => by
    rw [Eq, dim_bot] at h <;> exact lt_irreflₓ _ h

end Field

section rank

section

variable [Ringₓ K] [AddCommGroupₓ V] [Module K V] [AddCommGroupₓ V₁] [Module K V₁]

variable [AddCommGroupₓ V'] [Module K V']

/-- `rank f` is the rank of a `linear_map f`, defined as the dimension of `f.range`. -/
def rank (f : V →ₗ[K] V') : Cardinal :=
  Module.rank K f.range

theorem rank_le_range (f : V →ₗ[K] V₁) : rank f ≤ Module.rank K V₁ :=
  dim_submodule_le _

@[simp]
theorem rank_zero [Nontrivial K] : rank (0 : V →ₗ[K] V') = 0 := by
  rw [rank, LinearMap.range_zero, dim_bot]

variable [AddCommGroupₓ V''] [Module K V'']

theorem rank_comp_le1 (g : V →ₗ[K] V') (f : V' →ₗ[K] V'') : rank (f.comp g) ≤ rank f := by
  refine' dim_le_of_submodule _ _ _
  rw [LinearMap.range_comp]
  exact LinearMap.map_le_range

variable [AddCommGroupₓ V'₁] [Module K V'₁]

theorem rank_comp_le2 (g : V →ₗ[K] V') (f : V' →ₗ[K] V'₁) : rank (f.comp g) ≤ rank g := by
  rw [rank, rank, LinearMap.range_comp] <;> exact dim_map_le _ _

end

section Field

variable [Field K] [AddCommGroupₓ V] [Module K V] [AddCommGroupₓ V₁] [Module K V₁]

variable [AddCommGroupₓ V'] [Module K V']

theorem rank_le_domain (f : V →ₗ[K] V₁) : rank f ≤ Module.rank K V := by
  rw [← dim_range_add_dim_ker f]
  exact self_le_add_right _ _

theorem rank_add_le (f g : V →ₗ[K] V') : rank (f + g) ≤ rank f + rank g :=
  calc
    rank (f + g) ≤ Module.rank K (f.range⊔g.range : Submodule K V') := by
      refine' dim_le_of_submodule _ _ _
      exact
        LinearMap.range_le_iff_comap.2 <|
          eq_top_iff'.2 fun x =>
            show f x + g x ∈ (f.range⊔g.range : Submodule K V') from mem_sup.2 ⟨_, ⟨x, rfl⟩, _, ⟨x, rfl⟩, rfl⟩
    _ ≤ rank f + rank g := dim_add_le_dim_add_dim _ _
    

theorem rank_finset_sum_le {η} (s : Finset η) (f : η → V →ₗ[K] V') : rank (∑ d in s, f d) ≤ ∑ d in s, rank (f d) :=
  @Finset.sum_hom_rel _ _ _ _ _ (fun a b => rank a ≤ b) f (fun d => rank (f d)) s (le_of_eqₓ rank_zero) fun i g c h =>
    le_transₓ (rank_add_le _ _) (add_le_add_left h _)

end Field

end rank

section DivisionRing

variable [DivisionRing K] [AddCommGroupₓ V] [Module K V] [AddCommGroupₓ V'] [Module K V']

/-- The `ι` indexed basis on `V`, where `ι` is an empty type and `V` is zero-dimensional.

See also `finite_dimensional.fin_basis`.
-/
def Basis.ofDimEqZero {ι : Type _} [IsEmpty ι] (hV : Module.rank K V = 0) : Basis ι K V := by
  have : Subsingleton V := dim_zero_iff.1 hV
  exact Basis.empty _

@[simp]
theorem Basis.of_dim_eq_zero_apply {ι : Type _} [IsEmpty ι] (hV : Module.rank K V = 0) (i : ι) :
    Basis.ofDimEqZero hV i = 0 :=
  rfl

theorem le_dim_iff_exists_linear_independent {c : Cardinal} :
    c ≤ Module.rank K V ↔ ∃ s : Set V, # s = c ∧ LinearIndependent K (coe : s → V) := by
  constructor
  · intro h
    let t := Basis.ofVectorSpace K V
    rw [← t.mk_eq_dim'', Cardinal.le_mk_iff_exists_subset] at h
    rcases h with ⟨s, hst, hsc⟩
    exact ⟨s, hsc, (of_vector_space_index.linear_independent K V).mono hst⟩
    
  · rintro ⟨s, rfl, si⟩
    exact cardinal_le_dim_of_linear_independent si
    

theorem le_dim_iff_exists_linear_independent_finset {n : ℕ} :
    ↑n ≤ Module.rank K V ↔ ∃ s : Finset V, s.card = n ∧ LinearIndependent K (coe : (s : Set V) → V) := by
  simp only [← le_dim_iff_exists_linear_independent, ← Cardinal.mk_eq_nat_iff_finset]
  constructor
  · rintro ⟨s, ⟨t, rfl, rfl⟩, si⟩
    exact ⟨t, rfl, si⟩
    
  · rintro ⟨s, rfl, si⟩
    exact ⟨s, ⟨s, rfl, rfl⟩, si⟩
    

/-- A vector space has dimension at most `1` if and only if there is a
single vector of which all vectors are multiples. -/
theorem dim_le_one_iff : Module.rank K V ≤ 1 ↔ ∃ v₀ : V, ∀ v, ∃ r : K, r • v₀ = v := by
  let b := Basis.ofVectorSpace K V
  constructor
  · intro hd
    rw [← b.mk_eq_dim'', Cardinal.le_one_iff_subsingleton, subsingleton_coe] at hd
    rcases eq_empty_or_nonempty (of_vector_space_index K V) with (hb | ⟨⟨v₀, hv₀⟩⟩)
    · use 0
      have h' : ∀ v : V, v = 0 := by
        simpa [← hb, ← Submodule.eq_bot_iff] using b.span_eq.symm
      intro v
      simp [← h' v]
      
    · use v₀
      have h' : (K∙v₀) = ⊤ := by
        simpa [← hd.eq_singleton_of_mem hv₀] using b.span_eq
      intro v
      have hv : v ∈ (⊤ : Submodule K V) := mem_top
      rwa [← h', mem_span_singleton] at hv
      
    
  · rintro ⟨v₀, hv₀⟩
    have h : (K∙v₀) = ⊤ := by
      ext
      simp [← mem_span_singleton, ← hv₀]
    rw [← dim_top, ← h]
    convert dim_span_le _
    simp
    

/-- A submodule has dimension at most `1` if and only if there is a
single vector in the submodule such that the submodule is contained in
its span. -/
theorem dim_submodule_le_one_iff (s : Submodule K V) : Module.rank K s ≤ 1 ↔ ∃ v₀ ∈ s, s ≤ K∙v₀ := by
  simp_rw [dim_le_one_iff, le_span_singleton_iff]
  constructor
  · rintro ⟨⟨v₀, hv₀⟩, h⟩
    use v₀, hv₀
    intro v hv
    obtain ⟨r, hr⟩ := h ⟨v, hv⟩
    use r
    simp_rw [Subtype.ext_iff, coe_smul, Submodule.coe_mk] at hr
    exact hr
    
  · rintro ⟨v₀, hv₀, h⟩
    use ⟨v₀, hv₀⟩
    rintro ⟨v, hv⟩
    obtain ⟨r, hr⟩ := h v hv
    use r
    simp_rw [Subtype.ext_iff, coe_smul, Submodule.coe_mk]
    exact hr
    

/-- A submodule has dimension at most `1` if and only if there is a
single vector, not necessarily in the submodule, such that the
submodule is contained in its span. -/
theorem dim_submodule_le_one_iff' (s : Submodule K V) : Module.rank K s ≤ 1 ↔ ∃ v₀, s ≤ K∙v₀ := by
  rw [dim_submodule_le_one_iff]
  constructor
  · rintro ⟨v₀, hv₀, h⟩
    exact ⟨v₀, h⟩
    
  · rintro ⟨v₀, h⟩
    by_cases' hw : ∃ w : V, w ∈ s ∧ w ≠ 0
    · rcases hw with ⟨w, hw, hw0⟩
      use w, hw
      rcases mem_span_singleton.1 (h hw) with ⟨r', rfl⟩
      have h0 : r' ≠ 0 := by
        rintro rfl
        simpa using hw0
      rwa [span_singleton_smul_eq (IsUnit.mk0 _ h0) _]
      
    · push_neg  at hw
      rw [← Submodule.eq_bot_iff] at hw
      simp [← hw]
      
    

end DivisionRing

section Field

variable [Field K] [AddCommGroupₓ V] [Module K V] [AddCommGroupₓ V'] [Module K V']

theorem le_rank_iff_exists_linear_independent {c : Cardinal} {f : V →ₗ[K] V'} :
    c ≤ rank f ↔ ∃ s : Set V, Cardinal.lift.{v'} (# s) = Cardinal.lift.{v} c ∧ LinearIndependent K fun x : s => f x :=
  by
  rcases f.range_restrict.exists_right_inverse_of_surjective f.range_range_restrict with ⟨g, hg⟩
  have fg : left_inverse f.range_restrict g := LinearMap.congr_fun hg
  refine' ⟨fun h => _, _⟩
  · rcases le_dim_iff_exists_linear_independent.1 h with ⟨s, rfl, si⟩
    refine' ⟨g '' s, Cardinal.mk_image_eq_lift _ _ fg.injective, _⟩
    replace fg : ∀ x, f (g x) = x
    · intro x
      convert congr_arg Subtype.val (fg x)
      
    replace si : LinearIndependent K fun x : s => f (g x)
    · simpa only [← fg] using si.map' _ (ker_subtype _)
      
    exact si.image_of_comp s g f
    
  · rintro ⟨s, hsc, si⟩
    have : LinearIndependent K fun x : s => f.range_restrict x :=
      LinearIndependent.of_comp f.range.subtype
        (by
          convert si)
    convert cardinal_le_dim_of_linear_independent this.image
    rw [← Cardinal.lift_inj, ← hsc, Cardinal.mk_image_eq_of_inj_on_lift]
    exact inj_on_iff_injective.2 this.injective
    

theorem le_rank_iff_exists_linear_independent_finset {n : ℕ} {f : V →ₗ[K] V'} :
    ↑n ≤ rank f ↔ ∃ s : Finset V, s.card = n ∧ LinearIndependent K fun x : (s : Set V) => f x := by
  simp only [← le_rank_iff_exists_linear_independent, ← Cardinal.lift_nat_cast, ← Cardinal.lift_eq_nat_iff, ←
    Cardinal.mk_eq_nat_iff_finset]
  constructor
  · rintro ⟨s, ⟨t, rfl, rfl⟩, si⟩
    exact ⟨t, rfl, si⟩
    
  · rintro ⟨s, rfl, si⟩
    exact ⟨s, ⟨s, rfl, rfl⟩, si⟩
    

end Field

end Module

