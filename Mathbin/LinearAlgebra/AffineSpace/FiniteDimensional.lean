/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import Mathbin.LinearAlgebra.AffineSpace.Independent
import Mathbin.LinearAlgebra.FiniteDimensional

/-!
# Finite-dimensional subspaces of affine spaces.

This file provides a few results relating to finite-dimensional
subspaces of affine spaces.

## Main definitions

* `collinear` defines collinear sets of points as those that span a
  subspace of dimension at most 1.

-/


noncomputable section

open BigOperators Classical Affine

section AffineSpace'

variable (k : Type _) {V : Type _} {P : Type _}

variable {ι : Type _}

include V

open AffineSubspace FiniteDimensional Module

variable [DivisionRing k] [AddCommGroupₓ V] [Module k V] [affine_space V P]

/-- The `vector_span` of a finite set is finite-dimensional. -/
theorem finite_dimensional_vector_span_of_finite {s : Set P} (h : Set.Finite s) :
    FiniteDimensional k (vectorSpan k s) :=
  span_of_finite k <| h.vsub h

/-- The `vector_span` of a family indexed by a `fintype` is
finite-dimensional. -/
instance finite_dimensional_vector_span_of_fintype [Fintype ι] (p : ι → P) :
    FiniteDimensional k (vectorSpan k (Set.Range p)) :=
  finite_dimensional_vector_span_of_finite k (Set.finite_range _)

/-- The `vector_span` of a subset of a family indexed by a `fintype`
is finite-dimensional. -/
instance finite_dimensional_vector_span_image_of_fintype [Fintype ι] (p : ι → P) (s : Set ι) :
    FiniteDimensional k (vectorSpan k (p '' s)) :=
  finite_dimensional_vector_span_of_finite k (Set.to_finite _)

/-- The direction of the affine span of a finite set is
finite-dimensional. -/
theorem finite_dimensional_direction_affine_span_of_finite {s : Set P} (h : Set.Finite s) :
    FiniteDimensional k (affineSpan k s).direction :=
  (direction_affine_span k s).symm ▸ finite_dimensional_vector_span_of_finite k h

/-- The direction of the affine span of a family indexed by a
`fintype` is finite-dimensional. -/
instance finite_dimensional_direction_affine_span_of_fintype [Fintype ι] (p : ι → P) :
    FiniteDimensional k (affineSpan k (Set.Range p)).direction :=
  finite_dimensional_direction_affine_span_of_finite k (Set.finite_range _)

/-- The direction of the affine span of a subset of a family indexed
by a `fintype` is finite-dimensional. -/
instance finite_dimensional_direction_affine_span_image_of_fintype [Fintype ι] (p : ι → P) (s : Set ι) :
    FiniteDimensional k (affineSpan k (p '' s)).direction :=
  finite_dimensional_direction_affine_span_of_finite k (Set.to_finite _)

/-- An affine-independent family of points in a finite-dimensional affine space is finite. -/
noncomputable def fintypeOfFinDimAffineIndependent [FiniteDimensional k V] {p : ι → P} (hi : AffineIndependent k p) :
    Fintype ι :=
  if hι : IsEmpty ι then @Fintype.ofIsEmpty _ hι
  else by
    let q := (not_is_empty_iff.mp hι).some
    rw [affine_independent_iff_linear_independent_vsub k p q] at hi
    let this : IsNoetherian k V := IsNoetherian.iff_fg.2 inferInstance
    exact fintypeOfFintypeNe _ (@Fintype.ofFinite _ hi.finite_of_is_noetherian)

/-- An affine-independent subset of a finite-dimensional affine space is finite. -/
theorem finite_of_fin_dim_affine_independent [FiniteDimensional k V] {s : Set P}
    (hi : AffineIndependent k (coe : s → P)) : s.Finite :=
  ⟨fintypeOfFinDimAffineIndependent k hi⟩

variable {k}

/-- The `vector_span` of a finite subset of an affinely independent
family has dimension one less than its cardinality. -/
theorem AffineIndependent.finrank_vector_span_image_finset {p : ι → P} (hi : AffineIndependent k p) {s : Finset ι}
    {n : ℕ} (hc : Finset.card s = n + 1) : finrank k (vectorSpan k (s.Image p : Set P)) = n := by
  have hi' := hi.range.mono (Set.image_subset_range p ↑s)
  have hc' : (s.image p).card = n + 1 := by
    rwa [s.card_image_of_injective hi.injective]
  have hn : (s.image p).Nonempty := by
    simp [← hc', Finset.card_pos]
  rcases hn with ⟨p₁, hp₁⟩
  have hp₁' : p₁ ∈ p '' s := by
    simpa using hp₁
  rw [affine_independent_set_iff_linear_independent_vsub k hp₁', ← Finset.coe_singleton, ← Finset.coe_image, ←
    Finset.coe_sdiff, Finset.sdiff_singleton_eq_erase, ← Finset.coe_image] at hi'
  have hc : (Finset.image (fun p : P => p -ᵥ p₁) ((Finset.image p s).erase p₁)).card = n := by
    rw [Finset.card_image_of_injective _ (vsub_left_injective _), Finset.card_erase_of_mem hp₁]
    exact Nat.pred_eq_of_eq_succ hc'
  rwa [vector_span_eq_span_vsub_finset_right_ne k hp₁, finrank_span_finset_eq_card, hc]

/-- The `vector_span` of a finite affinely independent family has
dimension one less than its cardinality. -/
theorem AffineIndependent.finrank_vector_span [Fintype ι] {p : ι → P} (hi : AffineIndependent k p) {n : ℕ}
    (hc : Fintype.card ι = n + 1) : finrank k (vectorSpan k (Set.Range p)) = n := by
  rw [← Finset.card_univ] at hc
  rw [← Set.image_univ, ← Finset.coe_univ, ← Finset.coe_image]
  exact hi.finrank_vector_span_image_finset hc

/-- The `vector_span` of a finite affinely independent family whose
cardinality is one more than that of the finite-dimensional space is
`⊤`. -/
theorem AffineIndependent.vector_span_eq_top_of_card_eq_finrank_add_one [FiniteDimensional k V] [Fintype ι] {p : ι → P}
    (hi : AffineIndependent k p) (hc : Fintype.card ι = finrank k V + 1) : vectorSpan k (Set.Range p) = ⊤ :=
  eq_top_of_finrank_eq <| hi.finrank_vector_span hc

variable (k)

/-- The `vector_span` of `n + 1` points in an indexed family has
dimension at most `n`. -/
theorem finrank_vector_span_image_finset_le (p : ι → P) (s : Finset ι) {n : ℕ} (hc : Finset.card s = n + 1) :
    finrank k (vectorSpan k (s.Image p : Set P)) ≤ n := by
  have hn : (s.image p).Nonempty := by
    rw [Finset.Nonempty.image_iff, ← Finset.card_pos, hc]
    apply Nat.succ_posₓ
  rcases hn with ⟨p₁, hp₁⟩
  rw [vector_span_eq_span_vsub_finset_right_ne k hp₁]
  refine' le_transₓ (finrank_span_finset_le_card (((s.image p).erase p₁).Image fun p => p -ᵥ p₁)) _
  rw [Finset.card_image_of_injective _ (vsub_left_injective p₁), Finset.card_erase_of_mem hp₁, tsub_le_iff_right, ← hc]
  apply Finset.card_image_le

/-- The `vector_span` of an indexed family of `n + 1` points has
dimension at most `n`. -/
theorem finrank_vector_span_range_le [Fintype ι] (p : ι → P) {n : ℕ} (hc : Fintype.card ι = n + 1) :
    finrank k (vectorSpan k (Set.Range p)) ≤ n := by
  rw [← Set.image_univ, ← Finset.coe_univ, ← Finset.coe_image]
  rw [← Finset.card_univ] at hc
  exact finrank_vector_span_image_finset_le _ _ _ hc

/-- `n + 1` points are affinely independent if and only if their
`vector_span` has dimension `n`. -/
theorem affine_independent_iff_finrank_vector_span_eq [Fintype ι] (p : ι → P) {n : ℕ} (hc : Fintype.card ι = n + 1) :
    AffineIndependent k p ↔ finrank k (vectorSpan k (Set.Range p)) = n := by
  have hn : Nonempty ι := by
    simp [Fintype.card_pos_iff, ← hc]
  cases' hn with i₁
  rw [affine_independent_iff_linear_independent_vsub _ _ i₁, linear_independent_iff_card_eq_finrank_span, eq_comm,
    vector_span_range_eq_span_range_vsub_right_ne k p i₁]
  congr
  rw [← Finset.card_univ] at hc
  rw [Fintype.subtype_card]
  simp [← Finset.filter_ne', ← Finset.card_erase_of_mem, ← hc]

/-- `n + 1` points are affinely independent if and only if their
`vector_span` has dimension at least `n`. -/
theorem affine_independent_iff_le_finrank_vector_span [Fintype ι] (p : ι → P) {n : ℕ} (hc : Fintype.card ι = n + 1) :
    AffineIndependent k p ↔ n ≤ finrank k (vectorSpan k (Set.Range p)) := by
  rw [affine_independent_iff_finrank_vector_span_eq k p hc]
  constructor
  · rintro rfl
    rfl
    
  · exact fun hle => le_antisymmₓ (finrank_vector_span_range_le k p hc) hle
    

/-- `n + 2` points are affinely independent if and only if their
`vector_span` does not have dimension at most `n`. -/
theorem affine_independent_iff_not_finrank_vector_span_le [Fintype ι] (p : ι → P) {n : ℕ}
    (hc : Fintype.card ι = n + 2) : AffineIndependent k p ↔ ¬finrank k (vectorSpan k (Set.Range p)) ≤ n := by
  rw [affine_independent_iff_le_finrank_vector_span k p hc, ← Nat.lt_iff_add_one_le, lt_iff_not_geₓ]

/-- `n + 2` points have a `vector_span` with dimension at most `n` if
and only if they are not affinely independent. -/
theorem finrank_vector_span_le_iff_not_affine_independent [Fintype ι] (p : ι → P) {n : ℕ}
    (hc : Fintype.card ι = n + 2) : finrank k (vectorSpan k (Set.Range p)) ≤ n ↔ ¬AffineIndependent k p :=
  (not_iff_comm.1 (affine_independent_iff_not_finrank_vector_span_le k p hc).symm).symm

variable {k}

/-- If the `vector_span` of a finite subset of an affinely independent
family lies in a submodule with dimension one less than its
cardinality, it equals that submodule. -/
theorem AffineIndependent.vector_span_image_finset_eq_of_le_of_card_eq_finrank_add_one {p : ι → P}
    (hi : AffineIndependent k p) {s : Finset ι} {sm : Submodule k V} [FiniteDimensional k sm]
    (hle : vectorSpan k (s.Image p : Set P) ≤ sm) (hc : Finset.card s = finrank k sm + 1) :
    vectorSpan k (s.Image p : Set P) = sm :=
  eq_of_le_of_finrank_eq hle <| hi.finrank_vector_span_image_finset hc

/-- If the `vector_span` of a finite affinely independent
family lies in a submodule with dimension one less than its
cardinality, it equals that submodule. -/
theorem AffineIndependent.vector_span_eq_of_le_of_card_eq_finrank_add_one [Fintype ι] {p : ι → P}
    (hi : AffineIndependent k p) {sm : Submodule k V} [FiniteDimensional k sm] (hle : vectorSpan k (Set.Range p) ≤ sm)
    (hc : Fintype.card ι = finrank k sm + 1) : vectorSpan k (Set.Range p) = sm :=
  eq_of_le_of_finrank_eq hle <| hi.finrank_vector_span hc

/-- If the `affine_span` of a finite subset of an affinely independent
family lies in an affine subspace whose direction has dimension one
less than its cardinality, it equals that subspace. -/
theorem AffineIndependent.affine_span_image_finset_eq_of_le_of_card_eq_finrank_add_one {p : ι → P}
    (hi : AffineIndependent k p) {s : Finset ι} {sp : AffineSubspace k P} [FiniteDimensional k sp.direction]
    (hle : affineSpan k (s.Image p : Set P) ≤ sp) (hc : Finset.card s = finrank k sp.direction + 1) :
    affineSpan k (s.Image p : Set P) = sp := by
  have hn : (s.image p).Nonempty := by
    rw [Finset.Nonempty.image_iff, ← Finset.card_pos, hc]
    apply Nat.succ_posₓ
  refine' eq_of_direction_eq_of_nonempty_of_le _ ((affine_span_nonempty k _).2 hn) hle
  have hd := direction_le hle
  rw [direction_affine_span] at hd⊢
  exact hi.vector_span_image_finset_eq_of_le_of_card_eq_finrank_add_one hd hc

/-- If the `affine_span` of a finite affinely independent family lies
in an affine subspace whose direction has dimension one less than its
cardinality, it equals that subspace. -/
theorem AffineIndependent.affine_span_eq_of_le_of_card_eq_finrank_add_one [Fintype ι] {p : ι → P}
    (hi : AffineIndependent k p) {sp : AffineSubspace k P} [FiniteDimensional k sp.direction]
    (hle : affineSpan k (Set.Range p) ≤ sp) (hc : Fintype.card ι = finrank k sp.direction + 1) :
    affineSpan k (Set.Range p) = sp := by
  rw [← Finset.card_univ] at hc
  rw [← Set.image_univ, ← Finset.coe_univ, ← Finset.coe_image] at hle⊢
  exact hi.affine_span_image_finset_eq_of_le_of_card_eq_finrank_add_one hle hc

/-- The `affine_span` of a finite affinely independent family is `⊤` iff the
family's cardinality is one more than that of the finite-dimensional space. -/
theorem AffineIndependent.affine_span_eq_top_iff_card_eq_finrank_add_one [FiniteDimensional k V] [Fintype ι] {p : ι → P}
    (hi : AffineIndependent k p) : affineSpan k (Set.Range p) = ⊤ ↔ Fintype.card ι = finrank k V + 1 := by
  constructor
  · intro h_tot
    let n := Fintype.card ι - 1
    have hn : Fintype.card ι = n + 1 := (Nat.succ_pred_eq_of_posₓ (card_pos_of_affine_span_eq_top k V P h_tot)).symm
    rw [hn, ← finrank_top, ← (vector_span_eq_top_of_affine_span_eq_top k V P) h_tot, ← hi.finrank_vector_span hn]
    
  · intro hc
    rw [← finrank_top, ← direction_top k V P] at hc
    exact hi.affine_span_eq_of_le_of_card_eq_finrank_add_one le_top hc
    

variable (k)

/-- A set of points is collinear if their `vector_span` has dimension
at most `1`. -/
def Collinear (s : Set P) : Prop :=
  Module.rank k (vectorSpan k s) ≤ 1

/-- The definition of `collinear`. -/
theorem collinear_iff_dim_le_one (s : Set P) : Collinear k s ↔ Module.rank k (vectorSpan k s) ≤ 1 :=
  Iff.rfl

/-- A set of points, whose `vector_span` is finite-dimensional, is
collinear if and only if their `vector_span` has dimension at most
`1`. -/
theorem collinear_iff_finrank_le_one (s : Set P) [FiniteDimensional k (vectorSpan k s)] :
    Collinear k s ↔ finrank k (vectorSpan k s) ≤ 1 := by
  have h := collinear_iff_dim_le_one k s
  rw [← finrank_eq_dim] at h
  exact_mod_cast h

variable (P)

/-- The empty set is collinear. -/
theorem collinear_empty : Collinear k (∅ : Set P) := by
  rw [collinear_iff_dim_le_one, vector_span_empty]
  simp

variable {P}

/-- A single point is collinear. -/
theorem collinear_singleton (p : P) : Collinear k ({p} : Set P) := by
  rw [collinear_iff_dim_le_one, vector_span_singleton]
  simp

/-- Given a point `p₀` in a set of points, that set is collinear if and
only if the points can all be expressed as multiples of the same
vector, added to `p₀`. -/
theorem collinear_iff_of_mem {s : Set P} {p₀ : P} (h : p₀ ∈ s) :
    Collinear k s ↔ ∃ v : V, ∀, ∀ p ∈ s, ∀, ∃ r : k, p = r • v +ᵥ p₀ := by
  simp_rw [collinear_iff_dim_le_one, dim_submodule_le_one_iff', Submodule.le_span_singleton_iff]
  constructor
  · rintro ⟨v₀, hv⟩
    use v₀
    intro p hp
    obtain ⟨r, hr⟩ := hv (p -ᵥ p₀) (vsub_mem_vector_span k hp h)
    use r
    rw [eq_vadd_iff_vsub_eq]
    exact hr.symm
    
  · rintro ⟨v, hp₀v⟩
    use v
    intro w hw
    have hs : vectorSpan k s ≤ k∙v := by
      rw [vector_span_eq_span_vsub_set_right k h, Submodule.span_le, Set.subset_def]
      intro x hx
      rw [SetLike.mem_coe, Submodule.mem_span_singleton]
      rw [Set.mem_image] at hx
      rcases hx with ⟨p, hp, rfl⟩
      rcases hp₀v p hp with ⟨r, rfl⟩
      use r
      simp
    have hw' := SetLike.le_def.1 hs hw
    rwa [Submodule.mem_span_singleton] at hw'
    

/-- A set of points is collinear if and only if they can all be
expressed as multiples of the same vector, added to the same base
point. -/
theorem collinear_iff_exists_forall_eq_smul_vadd (s : Set P) :
    Collinear k s ↔ ∃ (p₀ : P)(v : V), ∀, ∀ p ∈ s, ∀, ∃ r : k, p = r • v +ᵥ p₀ := by
  rcases Set.eq_empty_or_nonempty s with (rfl | ⟨⟨p₁, hp₁⟩⟩)
  · simp [← collinear_empty]
    
  · rw [collinear_iff_of_mem k hp₁]
    constructor
    · exact fun h => ⟨p₁, h⟩
      
    · rintro ⟨p, v, hv⟩
      use v
      intro p₂ hp₂
      rcases hv p₂ hp₂ with ⟨r, rfl⟩
      rcases hv p₁ hp₁ with ⟨r₁, rfl⟩
      use r - r₁
      simp [← vadd_vadd, add_smul]
      
    

/-- Two points are collinear. -/
theorem collinear_pair (p₁ p₂ : P) : Collinear k ({p₁, p₂} : Set P) := by
  rw [collinear_iff_exists_forall_eq_smul_vadd]
  use p₁, p₂ -ᵥ p₁
  intro p hp
  rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  cases hp
  · use 0
    simp [← hp]
    
  · use 1
    simp [← hp]
    

/-- Three points are affinely independent if and only if they are not
collinear. -/
theorem affine_independent_iff_not_collinear (p : Finₓ 3 → P) : AffineIndependent k p ↔ ¬Collinear k (Set.Range p) := by
  rw [collinear_iff_finrank_le_one, affine_independent_iff_not_finrank_vector_span_le k p (Fintype.card_fin 3)]

/-- Three points are collinear if and only if they are not affinely
independent. -/
theorem collinear_iff_not_affine_independent (p : Finₓ 3 → P) : Collinear k (Set.Range p) ↔ ¬AffineIndependent k p := by
  rw [collinear_iff_finrank_le_one, finrank_vector_span_le_iff_not_affine_independent k p (Fintype.card_fin 3)]

end AffineSpace'

