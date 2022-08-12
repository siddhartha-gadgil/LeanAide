/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import Mathbin.Data.Finset.Sort
import Mathbin.Data.Fin.VecNotation
import Mathbin.LinearAlgebra.AffineSpace.Combination
import Mathbin.LinearAlgebra.AffineSpace.AffineEquiv
import Mathbin.LinearAlgebra.Basis

/-!
# Affine independence

This file defines affinely independent families of points.

## Main definitions

* `affine_independent` defines affinely independent families of points
  as those where no nontrivial weighted subtraction is `0`.  This is
  proved equivalent to two other formulations: linear independence of
  the results of subtracting a base point in the family from the other
  points in the family, or any equal affine combinations having the
  same weights.  A bundled type `simplex` is provided for finite
  affinely independent families of points, with an abbreviation
  `triangle` for the case of three points.

## References

* https://en.wikipedia.org/wiki/Affine_space

-/


noncomputable section

open BigOperators Classical Affine

open Function

section AffineIndependent

variable (k : Type _) {V : Type _} {P : Type _} [Ringₓ k] [AddCommGroupₓ V] [Module k V]

variable [affine_space V P] {ι : Type _}

include V

/-- An indexed family is said to be affinely independent if no
nontrivial weighted subtractions (where the sum of weights is 0) are
0. -/
def AffineIndependent (p : ι → P) : Prop :=
  ∀ (s : Finset ι) (w : ι → k), (∑ i in s, w i) = 0 → s.weightedVsub p w = (0 : V) → ∀, ∀ i ∈ s, ∀, w i = 0

/-- The definition of `affine_independent`. -/
theorem affine_independent_def (p : ι → P) :
    AffineIndependent k p ↔
      ∀ (s : Finset ι) (w : ι → k), (∑ i in s, w i) = 0 → s.weightedVsub p w = (0 : V) → ∀, ∀ i ∈ s, ∀, w i = 0 :=
  Iff.rfl

/-- A family with at most one point is affinely independent. -/
theorem affine_independent_of_subsingleton [Subsingleton ι] (p : ι → P) : AffineIndependent k p := fun s w h hs i hi =>
  Fintype.eq_of_subsingleton_of_sum_eq h i hi

/-- A family indexed by a `fintype` is affinely independent if and
only if no nontrivial weighted subtractions over `finset.univ` (where
the sum of the weights is 0) are 0. -/
theorem affine_independent_iff_of_fintype [Fintype ι] (p : ι → P) :
    AffineIndependent k p ↔ ∀ w : ι → k, (∑ i, w i) = 0 → Finset.univ.weightedVsub p w = (0 : V) → ∀ i, w i = 0 := by
  constructor
  · exact fun h w hw hs i => h Finset.univ w hw hs i (Finset.mem_univ _)
    
  · intro h s w hw hs i hi
    rw [Finset.weighted_vsub_indicator_subset _ _ (Finset.subset_univ s)] at hs
    rw [Set.sum_indicator_subset _ (Finset.subset_univ s)] at hw
    replace h := h ((↑s : Set ι).indicator w) hw hs i
    simpa [← hi] using h
    

/-- A family is affinely independent if and only if the differences
from a base point in that family are linearly independent. -/
theorem affine_independent_iff_linear_independent_vsub (p : ι → P) (i1 : ι) :
    AffineIndependent k p ↔ LinearIndependent k fun i : { x // x ≠ i1 } => (p i -ᵥ p i1 : V) := by
  constructor
  · intro h
    rw [linear_independent_iff']
    intro s g hg i hi
    set f : ι → k := fun x => if hx : x = i1 then -∑ y in s, g y else g ⟨x, hx⟩ with hfdef
    let s2 : Finset ι := insert i1 (s.map (embedding.subtype _))
    have hfg : ∀ x : { x // x ≠ i1 }, g x = f x := by
      intro x
      rw [hfdef]
      dsimp' only
      erw [dif_neg x.property, Subtype.coe_eta]
    rw [hfg]
    have hf : (∑ ι in s2, f ι) = 0 := by
      rw [Finset.sum_insert (Finset.not_mem_map_subtype_of_not_property s (not_not.2 rfl)),
        Finset.sum_subtype_map_embedding fun x hx => (hfg x).symm]
      rw [hfdef]
      dsimp' only
      rw [dif_pos rfl]
      exact neg_add_selfₓ _
    have hs2 : s2.weighted_vsub p f = (0 : V) := by
      set f2 : ι → V := fun x => f x • (p x -ᵥ p i1) with hf2def
      set g2 : { x // x ≠ i1 } → V := fun x => g x • (p x -ᵥ p i1) with hg2def
      have hf2g2 : ∀ x : { x // x ≠ i1 }, f2 x = g2 x := by
        simp_rw [hf2def, hg2def, hfg]
        exact fun x => rfl
      rw [Finset.weighted_vsub_eq_weighted_vsub_of_point_of_sum_eq_zero s2 f p hf (p i1),
        Finset.weighted_vsub_of_point_insert, Finset.weighted_vsub_of_point_apply,
        Finset.sum_subtype_map_embedding fun x hx => hf2g2 x]
      exact hg
    exact h s2 f hf hs2 i (Finset.mem_insert_of_mem (Finset.mem_map.2 ⟨i, hi, rfl⟩))
    
  · intro h
    rw [linear_independent_iff'] at h
    intro s w hw hs i hi
    rw [Finset.weighted_vsub_eq_weighted_vsub_of_point_of_sum_eq_zero s w p hw (p i1), ←
      s.weighted_vsub_of_point_erase w p i1, Finset.weighted_vsub_of_point_apply] at hs
    let f : ι → V := fun i => w i • (p i -ᵥ p i1)
    have hs2 : (∑ i in (s.erase i1).Subtype fun i => i ≠ i1, f i) = 0 := by
      rw [← hs]
      convert Finset.sum_subtype_of_mem f fun x => Finset.ne_of_mem_erase
    have h2 := h ((s.erase i1).Subtype fun i => i ≠ i1) (fun x => w x) hs2
    simp_rw [Finset.mem_subtype] at h2
    have h2b : ∀, ∀ i ∈ s, ∀, i ≠ i1 → w i = 0 := fun i his hi => h2 ⟨i, hi⟩ (Finset.mem_erase_of_ne_of_mem hi his)
    exact Finset.eq_zero_of_sum_eq_zero hw h2b i hi
    

/-- A set is affinely independent if and only if the differences from
a base point in that set are linearly independent. -/
theorem affine_independent_set_iff_linear_independent_vsub {s : Set P} {p₁ : P} (hp₁ : p₁ ∈ s) :
    AffineIndependent k (fun p => p : s → P) ↔
      LinearIndependent k (fun v => v : (fun p => (p -ᵥ p₁ : V)) '' (s \ {p₁}) → V) :=
  by
  rw [affine_independent_iff_linear_independent_vsub k (fun p => p : s → P) ⟨p₁, hp₁⟩]
  constructor
  · intro h
    have hv : ∀ v : (fun p => (p -ᵥ p₁ : V)) '' (s \ {p₁}), (v : V) +ᵥ p₁ ∈ s \ {p₁} := fun v =>
      (vsub_left_injective p₁).mem_set_image.1 ((vadd_vsub (v : V) p₁).symm ▸ v.property)
    let f : (fun p : P => (p -ᵥ p₁ : V)) '' (s \ {p₁}) → { x : s // x ≠ ⟨p₁, hp₁⟩ } := fun x =>
      ⟨⟨(x : V) +ᵥ p₁, Set.mem_of_mem_diff (hv x)⟩, fun hx => Set.not_mem_of_mem_diff (hv x) (Subtype.ext_iff.1 hx)⟩
    convert h.comp f fun x1 x2 hx => Subtype.ext (vadd_right_cancel p₁ (Subtype.ext_iff.1 (Subtype.ext_iff.1 hx)))
    ext v
    exact (vadd_vsub (v : V) p₁).symm
    
  · intro h
    let f : { x : s // x ≠ ⟨p₁, hp₁⟩ } → (fun p : P => (p -ᵥ p₁ : V)) '' (s \ {p₁}) := fun x =>
      ⟨((x : s) : P) -ᵥ p₁, ⟨x, ⟨⟨(x : s).property, fun hx => x.property (Subtype.ext hx)⟩, rfl⟩⟩⟩
    convert h.comp f fun x1 x2 hx => Subtype.ext (Subtype.ext (vsub_left_cancel (Subtype.ext_iff.1 hx)))
    

/-- A set of nonzero vectors is linearly independent if and only if,
given a point `p₁`, the vectors added to `p₁` and `p₁` itself are
affinely independent. -/
theorem linear_independent_set_iff_affine_independent_vadd_union_singleton {s : Set V} (hs : ∀, ∀ v ∈ s, ∀, v ≠ (0 : V))
    (p₁ : P) :
    LinearIndependent k (fun v => v : s → V) ↔ AffineIndependent k (fun p => p : {p₁} ∪ (fun v => v +ᵥ p₁) '' s → P) :=
  by
  rw [affine_independent_set_iff_linear_independent_vsub k (Set.mem_union_left _ (Set.mem_singleton p₁))]
  have h : (fun p => (p -ᵥ p₁ : V)) '' (({p₁} ∪ (fun v => v +ᵥ p₁) '' s) \ {p₁}) = s := by
    simp_rw [Set.union_diff_left, Set.image_diff (vsub_left_injective p₁), Set.image_image, Set.image_singleton,
      vsub_self, vadd_vsub, Set.image_id']
    exact Set.diff_singleton_eq_self fun h => hs 0 h rfl
  rw [h]

/-- A family is affinely independent if and only if any affine
combinations (with sum of weights 1) that evaluate to the same point
have equal `set.indicator`. -/
theorem affine_independent_iff_indicator_eq_of_affine_combination_eq (p : ι → P) :
    AffineIndependent k p ↔
      ∀ (s1 s2 : Finset ι) (w1 w2 : ι → k),
        (∑ i in s1, w1 i) = 1 →
          (∑ i in s2, w2 i) = 1 →
            s1.affineCombination p w1 = s2.affineCombination p w2 → Set.indicatorₓ (↑s1) w1 = Set.indicatorₓ (↑s2) w2 :=
  by
  constructor
  · intro ha s1 s2 w1 w2 hw1 hw2 heq
    ext i
    by_cases' hi : i ∈ s1 ∪ s2
    · rw [← sub_eq_zero]
      rw [Set.sum_indicator_subset _ (Finset.subset_union_left s1 s2)] at hw1
      rw [Set.sum_indicator_subset _ (Finset.subset_union_right s1 s2)] at hw2
      have hws : (∑ i in s1 ∪ s2, (Set.indicatorₓ (↑s1) w1 - Set.indicatorₓ (↑s2) w2) i) = 0 := by
        simp [← hw1, ← hw2]
      rw [Finset.affine_combination_indicator_subset _ _ (Finset.subset_union_left s1 s2),
        Finset.affine_combination_indicator_subset _ _ (Finset.subset_union_right s1 s2), ← @vsub_eq_zero_iff_eq V,
        Finset.affine_combination_vsub] at heq
      exact ha (s1 ∪ s2) (Set.indicatorₓ (↑s1) w1 - Set.indicatorₓ (↑s2) w2) hws HEq i hi
      
    · rw [← Finset.mem_coe, Finset.coe_union] at hi
      simp [← mt (Set.mem_union_left ↑s2) hi, ← mt (Set.mem_union_right ↑s1) hi]
      
    
  · intro ha s w hw hs i0 hi0
    let w1 : ι → k := Function.update (Function.const ι 0) i0 1
    have hw1 : (∑ i in s, w1 i) = 1 := by
      rw [Finset.sum_update_of_mem hi0, Finset.sum_const_zero, add_zeroₓ]
    have hw1s : s.affine_combination p w1 = p i0 :=
      s.affine_combination_of_eq_one_of_eq_zero w1 p hi0 (Function.update_same _ _ _) fun _ _ hne =>
        Function.update_noteq hne _ _
    let w2 := w + w1
    have hw2 : (∑ i in s, w2 i) = 1 := by
      simp [← w2, ← Finset.sum_add_distrib, ← hw, ← hw1]
    have hw2s : s.affine_combination p w2 = p i0 := by
      simp [← w2, Finset.weighted_vsub_vadd_affine_combination, ← hs, ← hw1s]
    replace ha := ha s s w2 w1 hw2 hw1 (hw1s.symm ▸ hw2s)
    have hws : w2 i0 - w1 i0 = 0 := by
      rw [← Finset.mem_coe] at hi0
      rw [← Set.indicator_of_mem hi0 w2, ← Set.indicator_of_mem hi0 w1, ha, sub_self]
    simpa [← w2] using hws
    

/-- A finite family is affinely independent if and only if any affine
combinations (with sum of weights 1) that evaluate to the same point are equal. -/
theorem affine_independent_iff_eq_of_fintype_affine_combination_eq [Fintype ι] (p : ι → P) :
    AffineIndependent k p ↔
      ∀ w1 w2 : ι → k,
        (∑ i, w1 i) = 1 →
          (∑ i, w2 i) = 1 → Finset.univ.affineCombination p w1 = Finset.univ.affineCombination p w2 → w1 = w2 :=
  by
  rw [affine_independent_iff_indicator_eq_of_affine_combination_eq]
  constructor
  · intro h w1 w2 hw1 hw2 hweq
    simpa only [← Set.indicator_univ, ← Finset.coe_univ] using h _ _ w1 w2 hw1 hw2 hweq
    
  · intro h s1 s2 w1 w2 hw1 hw2 hweq
    have hw1' : (∑ i, (s1 : Set ι).indicator w1 i) = 1 := by
      rwa [Set.sum_indicator_subset _ (Finset.subset_univ s1)] at hw1
    have hw2' : (∑ i, (s2 : Set ι).indicator w2 i) = 1 := by
      rwa [Set.sum_indicator_subset _ (Finset.subset_univ s2)] at hw2
    rw [Finset.affine_combination_indicator_subset w1 p (Finset.subset_univ s1),
      Finset.affine_combination_indicator_subset w2 p (Finset.subset_univ s2)] at hweq
    exact h _ _ hw1' hw2' hweq
    

variable {k}

/-- If we single out one member of an affine-independent family of points and affinely transport
all others along the line joining them to this member, the resulting new family of points is affine-
independent.

This is the affine version of `linear_independent.units_smul`. -/
theorem AffineIndependent.units_line_map {p : ι → P} (hp : AffineIndependent k p) (j : ι) (w : ι → Units k) :
    AffineIndependent k fun i => AffineMap.lineMap (p j) (p i) (w i : k) := by
  rw [affine_independent_iff_linear_independent_vsub k _ j] at hp⊢
  simp only [← AffineMap.line_map_vsub_left, ← AffineMap.coe_const, ← AffineMap.line_map_same]
  exact hp.units_smul fun i => w i

theorem AffineIndependent.indicator_eq_of_affine_combination_eq {p : ι → P} (ha : AffineIndependent k p)
    (s₁ s₂ : Finset ι) (w₁ w₂ : ι → k) (hw₁ : (∑ i in s₁, w₁ i) = 1) (hw₂ : (∑ i in s₂, w₂ i) = 1)
    (h : s₁.affineCombination p w₁ = s₂.affineCombination p w₂) : Set.indicatorₓ (↑s₁) w₁ = Set.indicatorₓ (↑s₂) w₂ :=
  (affine_independent_iff_indicator_eq_of_affine_combination_eq k p).1 ha s₁ s₂ w₁ w₂ hw₁ hw₂ h

/-- An affinely independent family is injective, if the underlying
ring is nontrivial. -/
protected theorem AffineIndependent.injective [Nontrivial k] {p : ι → P} (ha : AffineIndependent k p) :
    Function.Injective p := by
  intro i j hij
  rw [affine_independent_iff_linear_independent_vsub _ _ j] at ha
  by_contra hij'
  exact ha.ne_zero ⟨i, hij'⟩ (vsub_eq_zero_iff_eq.mpr hij)

/-- If a family is affinely independent, so is any subfamily given by
composition of an embedding into index type with the original
family. -/
theorem AffineIndependent.comp_embedding {ι2 : Type _} (f : ι2 ↪ ι) {p : ι → P} (ha : AffineIndependent k p) :
    AffineIndependent k (p ∘ f) := by
  intro fs w hw hs i0 hi0
  let fs' := fs.map f
  let w' := fun i => if h : ∃ i2, f i2 = i then w h.some else 0
  have hw' : ∀ i2 : ι2, w' (f i2) = w i2 := by
    intro i2
    have h : ∃ i : ι2, f i = f i2 := ⟨i2, rfl⟩
    have hs : h.some = i2 := f.injective h.some_spec
    simp_rw [w', dif_pos h, hs]
  have hw's : (∑ i in fs', w' i) = 0 := by
    rw [← hw, Finset.sum_map]
    simp [← hw']
  have hs' : fs'.weighted_vsub p w' = (0 : V) := by
    rw [← hs, Finset.weighted_vsub_map]
    congr with i
    simp [← hw']
  rw [← ha fs' w' hw's hs' (f i0) ((Finset.mem_map' _).2 hi0), hw']

/-- If a family is affinely independent, so is any subfamily indexed
by a subtype of the index type. -/
protected theorem AffineIndependent.subtype {p : ι → P} (ha : AffineIndependent k p) (s : Set ι) :
    AffineIndependent k fun i : s => p i :=
  ha.comp_embedding (Embedding.subtype _)

/-- If an indexed family of points is affinely independent, so is the
corresponding set of points. -/
protected theorem AffineIndependent.range {p : ι → P} (ha : AffineIndependent k p) :
    AffineIndependent k (fun x => x : Set.Range p → P) := by
  let f : Set.Range p → ι := fun x => x.property.some
  have hf : ∀ x, p (f x) = x := fun x => x.property.some_spec
  let fe : Set.Range p ↪ ι := ⟨f, fun x₁ x₂ he => Subtype.ext (hf x₁ ▸ hf x₂ ▸ he ▸ rfl)⟩
  convert ha.comp_embedding fe
  ext
  simp [← hf]

theorem affine_independent_equiv {ι' : Type _} (e : ι ≃ ι') {p : ι' → P} :
    AffineIndependent k (p ∘ e) ↔ AffineIndependent k p := by
  refine' ⟨_, AffineIndependent.comp_embedding e.to_embedding⟩
  intro h
  have : p = p ∘ e ∘ e.symm.to_embedding := by
    ext
    simp
  rw [this]
  exact h.comp_embedding e.symm.to_embedding

/-- If a set of points is affinely independent, so is any subset. -/
protected theorem AffineIndependent.mono {s t : Set P} (ha : AffineIndependent k (fun x => x : t → P)) (hs : s ⊆ t) :
    AffineIndependent k (fun x => x : s → P) :=
  ha.comp_embedding (s.embeddingOfSubset t hs)

/-- If the range of an injective indexed family of points is affinely
independent, so is that family. -/
theorem AffineIndependent.of_set_of_injective {p : ι → P} (ha : AffineIndependent k (fun x => x : Set.Range p → P))
    (hi : Function.Injective p) : AffineIndependent k p :=
  ha.comp_embedding (⟨fun i => ⟨p i, Set.mem_range_self _⟩, fun x y h => hi (Subtype.mk_eq_mk.1 h)⟩ : ι ↪ Set.Range p)

section Composition

variable {V₂ P₂ : Type _} [AddCommGroupₓ V₂] [Module k V₂] [affine_space V₂ P₂]

include V₂

/-- If the image of a family of points in affine space under an affine transformation is affine-
independent, then the original family of points is also affine-independent. -/
theorem AffineIndependent.of_comp {p : ι → P} (f : P →ᵃ[k] P₂) (hai : AffineIndependent k (f ∘ p)) :
    AffineIndependent k p := by
  cases' is_empty_or_nonempty ι with h h
  · have := h
    apply affine_independent_of_subsingleton
    
  obtain ⟨i⟩ := h
  rw [affine_independent_iff_linear_independent_vsub k p i]
  simp_rw [affine_independent_iff_linear_independent_vsub k (f ∘ p) i, Function.comp_app, ← f.linear_map_vsub] at hai
  exact LinearIndependent.of_comp f.linear hai

/-- The image of a family of points in affine space, under an injective affine transformation, is
affine-independent. -/
theorem AffineIndependent.map' {p : ι → P} (hai : AffineIndependent k p) (f : P →ᵃ[k] P₂) (hf : Function.Injective f) :
    AffineIndependent k (f ∘ p) := by
  cases' is_empty_or_nonempty ι with h h
  · have := h
    apply affine_independent_of_subsingleton
    
  obtain ⟨i⟩ := h
  rw [affine_independent_iff_linear_independent_vsub k p i] at hai
  simp_rw [affine_independent_iff_linear_independent_vsub k (f ∘ p) i, Function.comp_app, ← f.linear_map_vsub]
  have hf' : f.linear.ker = ⊥ := by
    rwa [LinearMap.ker_eq_bot, f.injective_iff_linear_injective]
  exact LinearIndependent.map' hai f.linear hf'

/-- Injective affine maps preserve affine independence. -/
theorem AffineMap.affine_independent_iff {p : ι → P} (f : P →ᵃ[k] P₂) (hf : Function.Injective f) :
    AffineIndependent k (f ∘ p) ↔ AffineIndependent k p :=
  ⟨AffineIndependent.of_comp f, fun hai => AffineIndependent.map' hai f hf⟩

/-- Affine equivalences preserve affine independence of families of points. -/
theorem AffineEquiv.affine_independent_iff {p : ι → P} (e : P ≃ᵃ[k] P₂) :
    AffineIndependent k (e ∘ p) ↔ AffineIndependent k p :=
  e.toAffineMap.affine_independent_iff e.toEquiv.Injective

/-- Affine equivalences preserve affine independence of subsets. -/
theorem AffineEquiv.affine_independent_set_of_eq_iff {s : Set P} (e : P ≃ᵃ[k] P₂) :
    AffineIndependent k (coe : e '' s → P₂) ↔ AffineIndependent k (coe : s → P) := by
  have : e ∘ (coe : s → P) = (coe : e '' s → P₂) ∘ (e : P ≃ P₂).Image s := rfl
  rw [← e.affine_independent_iff, this, affine_independent_equiv]

end Composition

/-- If a family is affinely independent, and the spans of points
indexed by two subsets of the index type have a point in common, those
subsets of the index type have an element in common, if the underlying
ring is nontrivial. -/
theorem AffineIndependent.exists_mem_inter_of_exists_mem_inter_affine_span [Nontrivial k] {p : ι → P}
    (ha : AffineIndependent k p) {s1 s2 : Set ι} {p0 : P} (hp0s1 : p0 ∈ affineSpan k (p '' s1))
    (hp0s2 : p0 ∈ affineSpan k (p '' s2)) : ∃ i : ι, i ∈ s1 ∩ s2 := by
  rw [Set.image_eq_range] at hp0s1 hp0s2
  rw [mem_affine_span_iff_eq_affine_combination, ←
    Finset.eq_affine_combination_subset_iff_eq_affine_combination_subtype] at hp0s1 hp0s2
  rcases hp0s1 with ⟨fs1, hfs1, w1, hw1, hp0s1⟩
  rcases hp0s2 with ⟨fs2, hfs2, w2, hw2, hp0s2⟩
  rw [affine_independent_iff_indicator_eq_of_affine_combination_eq] at ha
  replace ha := ha fs1 fs2 w1 w2 hw1 hw2 (hp0s1 ▸ hp0s2)
  have hnz : (∑ i in fs1, w1 i) ≠ 0 := hw1.symm ▸ one_ne_zero
  rcases Finset.exists_ne_zero_of_sum_ne_zero hnz with ⟨i, hifs1, hinz⟩
  simp_rw [← Set.indicator_of_mem (Finset.mem_coe.2 hifs1) w1, ha] at hinz
  use i, hfs1 hifs1, hfs2 (Set.mem_of_indicator_ne_zero hinz)

/-- If a family is affinely independent, the spans of points indexed
by disjoint subsets of the index type are disjoint, if the underlying
ring is nontrivial. -/
theorem AffineIndependent.affine_span_disjoint_of_disjoint [Nontrivial k] {p : ι → P} (ha : AffineIndependent k p)
    {s1 s2 : Set ι} (hd : s1 ∩ s2 = ∅) : (affineSpan k (p '' s1) : Set P) ∩ affineSpan k (p '' s2) = ∅ := by
  by_contra hne
  change (affineSpan k (p '' s1) : Set P) ∩ affineSpan k (p '' s2) ≠ ∅ at hne
  rw [Set.ne_empty_iff_nonempty] at hne
  rcases hne with ⟨p0, hp0s1, hp0s2⟩
  cases' ha.exists_mem_inter_of_exists_mem_inter_affine_span hp0s1 hp0s2 with i hi
  exact Set.not_mem_empty i (hd ▸ hi)

/-- If a family is affinely independent, a point in the family is in
the span of some of the points given by a subset of the index type if
and only if that point's index is in the subset, if the underlying
ring is nontrivial. -/
@[simp]
protected theorem AffineIndependent.mem_affine_span_iff [Nontrivial k] {p : ι → P} (ha : AffineIndependent k p) (i : ι)
    (s : Set ι) : p i ∈ affineSpan k (p '' s) ↔ i ∈ s := by
  constructor
  · intro hs
    have h :=
      AffineIndependent.exists_mem_inter_of_exists_mem_inter_affine_span ha hs
        (mem_affine_span k (Set.mem_image_of_mem _ (Set.mem_singleton _)))
    rwa [← Set.nonempty_def, Set.inter_singleton_nonempty] at h
    
  · exact fun h => mem_affine_span k (Set.mem_image_of_mem p h)
    

/-- If a family is affinely independent, a point in the family is not
in the affine span of the other points, if the underlying ring is
nontrivial. -/
theorem AffineIndependent.not_mem_affine_span_diff [Nontrivial k] {p : ι → P} (ha : AffineIndependent k p) (i : ι)
    (s : Set ι) : p i ∉ affineSpan k (p '' (s \ {i})) := by
  simp [← ha]

theorem exists_nontrivial_relation_sum_zero_of_not_affine_ind {t : Finset V} (h : ¬AffineIndependent k (coe : t → V)) :
    ∃ f : V → k, (∑ e in t, f e • e) = 0 ∧ (∑ e in t, f e) = 0 ∧ ∃ x ∈ t, f x ≠ 0 := by
  classical
  rw [affine_independent_iff_of_fintype] at h
  simp only [← exists_prop, ← not_forall] at h
  obtain ⟨w, hw, hwt, i, hi⟩ := h
  simp only [← Finset.weighted_vsub_eq_weighted_vsub_of_point_of_sum_eq_zero _ w (coe : t → V) hw 0, ← vsub_eq_sub, ←
    Finset.weighted_vsub_of_point_apply, ← sub_zero] at hwt
  let f : ∀ x : V, x ∈ t → k := fun x hx => w ⟨x, hx⟩
  refine'
    ⟨fun x => if hx : x ∈ t then f x hx else (0 : k), _, _, by
      use i
      simp [← hi, ← f]⟩
  suffices (∑ e : V in t, dite (e ∈ t) (fun hx => f e hx • e) fun hx => 0) = 0 by
    convert this
    ext
    by_cases' hx : x ∈ t <;> simp [← hx]
  all_goals
    simp only [← Finset.sum_dite_of_true fun x h => h, ← Subtype.val_eq_coe, ← Finset.mk_coe, ← f, ← hwt, ← hw]

/-- Viewing a module as an affine space modelled on itself, we can characterise affine independence
in terms of linear combinations. -/
theorem affine_independent_iff {ι} {p : ι → V} :
    AffineIndependent k p ↔
      ∀ (s : Finset ι) (w : ι → k), s.Sum w = 0 → (∑ e in s, w e • p e) = 0 → ∀, ∀ e ∈ s, ∀, w e = 0 :=
  forall₃_congrₓ fun s w hw => by
    simp [← s.weighted_vsub_eq_linear_combination hw]

end AffineIndependent

section DivisionRing

variable {k : Type _} {V : Type _} {P : Type _} [DivisionRing k] [AddCommGroupₓ V] [Module k V]

variable [affine_space V P] {ι : Type _}

include V

/-- An affinely independent set of points can be extended to such a
set that spans the whole space. -/
theorem exists_subset_affine_independent_affine_span_eq_top {s : Set P} (h : AffineIndependent k (fun p => p : s → P)) :
    ∃ t : Set P, s ⊆ t ∧ AffineIndependent k (fun p => p : t → P) ∧ affineSpan k t = ⊤ := by
  rcases s.eq_empty_or_nonempty with (rfl | ⟨p₁, hp₁⟩)
  · have p₁ : P := add_torsor.nonempty.some
    let hsv := Basis.ofVectorSpace k V
    have hsvi := hsv.linear_independent
    have hsvt := hsv.span_eq
    rw [Basis.coe_of_vector_space] at hsvi hsvt
    have h0 : ∀ v : V, v ∈ Basis.OfVectorSpaceIndex _ _ → v ≠ 0 := by
      intro v hv
      simpa using hsv.ne_zero ⟨v, hv⟩
    rw [linear_independent_set_iff_affine_independent_vadd_union_singleton k h0 p₁] at hsvi
    exact
      ⟨{p₁} ∪ (fun v => v +ᵥ p₁) '' _, Set.empty_subset _, hsvi,
        affine_span_singleton_union_vadd_eq_top_of_span_eq_top p₁ hsvt⟩
    
  · rw [affine_independent_set_iff_linear_independent_vsub k hp₁] at h
    let bsv := Basis.extend h
    have hsvi := bsv.linear_independent
    have hsvt := bsv.span_eq
    rw [Basis.coe_extend] at hsvi hsvt
    have hsv := h.subset_extend (Set.subset_univ _)
    have h0 : ∀ v : V, v ∈ h.extend _ → v ≠ 0 := by
      intro v hv
      simpa using bsv.ne_zero ⟨v, hv⟩
    rw [linear_independent_set_iff_affine_independent_vadd_union_singleton k h0 p₁] at hsvi
    refine' ⟨{p₁} ∪ (fun v => v +ᵥ p₁) '' h.extend (Set.subset_univ _), _, _⟩
    · refine' Set.Subset.trans _ (Set.union_subset_union_right _ (Set.image_subset _ hsv))
      simp [← Set.image_image]
      
    · use hsvi, affine_span_singleton_union_vadd_eq_top_of_span_eq_top p₁ hsvt
      
    

variable (k V)

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (t «expr ⊆ » s)
theorem exists_affine_independent (s : Set P) :
    ∃ (t : _)(_ : t ⊆ s), affineSpan k t = affineSpan k s ∧ AffineIndependent k (coe : t → P) := by
  rcases s.eq_empty_or_nonempty with (rfl | ⟨p, hp⟩)
  · exact ⟨∅, Set.empty_subset ∅, rfl, affine_independent_of_subsingleton k _⟩
    
  obtain ⟨b, hb₁, hb₂, hb₃⟩ := exists_linear_independent k ((Equivₓ.vaddConst p).symm '' s)
  have hb₀ : ∀ v : V, v ∈ b → v ≠ 0 := fun v hv => hb₃.ne_zero (⟨v, hv⟩ : b)
  rw [linear_independent_set_iff_affine_independent_vadd_union_singleton k hb₀ p] at hb₃
  refine' ⟨{p} ∪ Equivₓ.vaddConst p '' b, _, _, hb₃⟩
  · apply Set.union_subset (set.singleton_subset_iff.mpr hp)
    rwa [← (Equivₓ.vaddConst p).subset_image' b s]
    
  · rw [Equivₓ.coe_vadd_const_symm, ← vector_span_eq_span_vsub_set_right k hp] at hb₂
    apply AffineSubspace.ext_of_direction_eq
    · have : Submodule.span k b = Submodule.span k (insert 0 b) := by
        simp
      simp only [← direction_affine_span, hb₂, ← Equivₓ.coe_vadd_const, ← Set.singleton_union, ←
        vector_span_eq_span_vsub_set_right k (Set.mem_insert p _), ← this]
      congr
      change (Equivₓ.vaddConst p).symm '' insert p (Equivₓ.vaddConst p '' b) = _
      rw [Set.image_insert_eq, ← Set.image_comp]
      simp
      
    · use p
      simp only [← Equivₓ.coe_vadd_const, ← Set.singleton_union, ← Set.mem_inter_eq, ← coe_affine_span]
      exact ⟨mem_span_points k _ _ (Set.mem_insert p _), mem_span_points k _ _ hp⟩
      
    

variable (k) {V P}

-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:30:4: unsupported: too many args: fin_cases ... #[[]]
/-- Two different points are affinely independent. -/
theorem affine_independent_of_ne {p₁ p₂ : P} (h : p₁ ≠ p₂) : AffineIndependent k ![p₁, p₂] := by
  rw [affine_independent_iff_linear_independent_vsub k ![p₁, p₂] 0]
  let i₁ : { x // x ≠ (0 : Finₓ 2) } :=
    ⟨1, by
      norm_num⟩
  have he' : ∀ i, i = i₁ := by
    rintro ⟨i, hi⟩
    ext
    fin_cases i
    · simpa using hi
      
  have : Unique { x // x ≠ (0 : Finₓ 2) } := ⟨⟨i₁⟩, he'⟩
  have hz : (![p₁, p₂] ↑default -ᵥ ![p₁, p₂] 0 : V) ≠ 0 := by
    rw [he' default]
    simpa using h.symm
  exact linear_independent_unique _ hz

end DivisionRing

namespace Affine

variable (k : Type _) {V : Type _} (P : Type _) [Ringₓ k] [AddCommGroupₓ V] [Module k V]

variable [affine_space V P]

include V

/-- A `simplex k P n` is a collection of `n + 1` affinely
independent points. -/
structure Simplex (n : ℕ) where
  points : Finₓ (n + 1) → P
  Independent : AffineIndependent k points

/-- A `triangle k P` is a collection of three affinely independent points. -/
abbrev Triangle :=
  Simplex k P 2

namespace Simplex

variable {P}

/-- Construct a 0-simplex from a point. -/
def mkOfPoint (p : P) : Simplex k P 0 :=
  ⟨fun _ => p, affine_independent_of_subsingleton k _⟩

/-- The point in a simplex constructed with `mk_of_point`. -/
@[simp]
theorem mk_of_point_points (p : P) (i : Finₓ 1) : (mkOfPoint k p).points i = p :=
  rfl

instance [Inhabited P] : Inhabited (Simplex k P 0) :=
  ⟨mkOfPoint k default⟩

instance nonempty : Nonempty (Simplex k P 0) :=
  ⟨mkOfPoint k <| AddTorsor.nonempty.some⟩

variable {k V}

/-- Two simplices are equal if they have the same points. -/
@[ext]
theorem ext {n : ℕ} {s1 s2 : Simplex k P n} (h : ∀ i, s1.points i = s2.points i) : s1 = s2 := by
  cases s1
  cases s2
  congr with i
  exact h i

/-- Two simplices are equal if and only if they have the same points. -/
theorem ext_iff {n : ℕ} (s1 s2 : Simplex k P n) : s1 = s2 ↔ ∀ i, s1.points i = s2.points i :=
  ⟨fun h _ => h ▸ rfl, ext⟩

/-- A face of a simplex is a simplex with the given subset of
points. -/
def face {n : ℕ} (s : Simplex k P n) {fs : Finset (Finₓ (n + 1))} {m : ℕ} (h : fs.card = m + 1) : Simplex k P m :=
  ⟨s.points ∘ fs.orderEmbOfFin h, s.Independent.comp_embedding (fs.orderEmbOfFin h).toEmbedding⟩

/-- The points of a face of a simplex are given by `mono_of_fin`. -/
theorem face_points {n : ℕ} (s : Simplex k P n) {fs : Finset (Finₓ (n + 1))} {m : ℕ} (h : fs.card = m + 1)
    (i : Finₓ (m + 1)) : (s.face h).points i = s.points (fs.orderEmbOfFin h i) :=
  rfl

/-- The points of a face of a simplex are given by `mono_of_fin`. -/
theorem face_points' {n : ℕ} (s : Simplex k P n) {fs : Finset (Finₓ (n + 1))} {m : ℕ} (h : fs.card = m + 1) :
    (s.face h).points = s.points ∘ fs.orderEmbOfFin h :=
  rfl

/-- A single-point face equals the 0-simplex constructed with
`mk_of_point`. -/
@[simp]
theorem face_eq_mk_of_point {n : ℕ} (s : Simplex k P n) (i : Finₓ (n + 1)) :
    s.face (Finset.card_singleton i) = mkOfPoint k (s.points i) := by
  ext
  simp [← face_points]

/-- The set of points of a face. -/
@[simp]
theorem range_face_points {n : ℕ} (s : Simplex k P n) {fs : Finset (Finₓ (n + 1))} {m : ℕ} (h : fs.card = m + 1) :
    Set.Range (s.face h).points = s.points '' ↑fs := by
  rw [face_points', Set.range_comp, Finset.range_order_emb_of_fin]

end Simplex

end Affine

namespace Affine

namespace Simplex

variable {k : Type _} {V : Type _} {P : Type _} [DivisionRing k] [AddCommGroupₓ V] [Module k V] [affine_space V P]

include V

/-- The centroid of a face of a simplex as the centroid of a subset of
the points. -/
@[simp]
theorem face_centroid_eq_centroid {n : ℕ} (s : Simplex k P n) {fs : Finset (Finₓ (n + 1))} {m : ℕ}
    (h : fs.card = m + 1) : Finset.univ.centroid k (s.face h).points = fs.centroid k s.points := by
  convert (finset.univ.centroid_map k (fs.order_emb_of_fin h).toEmbedding s.points).symm
  rw [← Finset.coe_inj, Finset.coe_map, Finset.coe_univ, Set.image_univ]
  simp

/-- Over a characteristic-zero division ring, the centroids given by
two subsets of the points of a simplex are equal if and only if those
faces are given by the same subset of points. -/
@[simp]
theorem centroid_eq_iff [CharZero k] {n : ℕ} (s : Simplex k P n) {fs₁ fs₂ : Finset (Finₓ (n + 1))} {m₁ m₂ : ℕ}
    (h₁ : fs₁.card = m₁ + 1) (h₂ : fs₂.card = m₂ + 1) : fs₁.centroid k s.points = fs₂.centroid k s.points ↔ fs₁ = fs₂ :=
  by
  refine' ⟨fun h => _, congr_arg _⟩
  rw [Finset.centroid_eq_affine_combination_fintype, Finset.centroid_eq_affine_combination_fintype] at h
  have ha :=
    (affine_independent_iff_indicator_eq_of_affine_combination_eq k s.points).1 s.independent _ _ _ _
      (fs₁.sum_centroid_weights_indicator_eq_one_of_card_eq_add_one k h₁)
      (fs₂.sum_centroid_weights_indicator_eq_one_of_card_eq_add_one k h₂) h
  simp_rw [Finset.coe_univ, Set.indicator_univ, Function.funext_iffₓ, Finset.centroid_weights_indicator_def,
    Finset.centroidWeights, h₁, h₂] at ha
  ext i
  specialize ha i
  have key : ∀ n : ℕ, (n : k) + 1 ≠ 0 := fun n h => by
    norm_cast  at h
  -- we should be able to golf this to `refine ⟨λ hi, decidable.by_contradiction (λ hni, _), ...⟩`,
    -- but for some unknown reason it doesn't work.
    constructor <;>
    intro hi <;> by_contra hni
  · simpa [← hni, ← hi, ← key] using ha
    
  · simpa [← hni, ← hi, ← key] using ha.symm
    

/-- Over a characteristic-zero division ring, the centroids of two
faces of a simplex are equal if and only if those faces are given by
the same subset of points. -/
theorem face_centroid_eq_iff [CharZero k] {n : ℕ} (s : Simplex k P n) {fs₁ fs₂ : Finset (Finₓ (n + 1))} {m₁ m₂ : ℕ}
    (h₁ : fs₁.card = m₁ + 1) (h₂ : fs₂.card = m₂ + 1) :
    Finset.univ.centroid k (s.face h₁).points = Finset.univ.centroid k (s.face h₂).points ↔ fs₁ = fs₂ := by
  rw [face_centroid_eq_centroid, face_centroid_eq_centroid]
  exact s.centroid_eq_iff h₁ h₂

/-- Two simplices with the same points have the same centroid. -/
theorem centroid_eq_of_range_eq {n : ℕ} {s₁ s₂ : Simplex k P n} (h : Set.Range s₁.points = Set.Range s₂.points) :
    Finset.univ.centroid k s₁.points = Finset.univ.centroid k s₂.points := by
  rw [← Set.image_univ, ← Set.image_univ, ← Finset.coe_univ] at h
  exact
    finset.univ.centroid_eq_of_inj_on_of_image_eq k _ (fun _ _ _ _ he => AffineIndependent.injective s₁.independent he)
      (fun _ _ _ _ he => AffineIndependent.injective s₂.independent he) h

end Simplex

end Affine

