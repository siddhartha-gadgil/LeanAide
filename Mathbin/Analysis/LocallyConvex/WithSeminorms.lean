/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll, Anatole Dedecker
-/
import Mathbin.Analysis.Seminorm
import Mathbin.Analysis.LocallyConvex.Bounded

/-!
# Topology induced by a family of seminorms

## Main definitions

* `seminorm_family.basis_sets`: The set of open seminorm balls for a family of seminorms.
* `seminorm_family.module_filter_basis`: A module filter basis formed by the open balls.
* `seminorm.is_bounded`: A linear map `f : E →ₗ[𝕜] F` is bounded iff every seminorm in `F` can be
bounded by a finite number of seminorms in `E`.

## Main statements

* `continuous_from_bounded`: A bounded linear map `f : E →ₗ[𝕜] F` is continuous.
* `seminorm_family.to_locally_convex_space`: A space equipped with a family of seminorms is locally
convex.

## TODO

Show that for any locally convex space there exist seminorms that induce the topology.

## Tags

seminorm, locally convex
-/


open NormedField Set Seminorm TopologicalSpace

open BigOperators Nnreal Pointwise TopologicalSpace

variable {𝕜 E F G ι ι' : Type _}

section FilterBasis

variable [NormedField 𝕜] [AddCommGroupₓ E] [Module 𝕜 E]

variable (𝕜 E ι)

/-- An abbreviation for indexed families of seminorms. This is mainly to allow for dot-notation. -/
abbrev SeminormFamily :=
  ι → Seminorm 𝕜 E

variable {𝕜 E ι}

namespace SeminormFamily

/-- The sets of a filter basis for the neighborhood filter of 0. -/
def BasisSets (p : SeminormFamily 𝕜 E ι) : Set (Set E) :=
  ⋃ (s : Finset ι) (r) (hr : 0 < r), singleton <| Ball (s.sup p) (0 : E) r

variable (p : SeminormFamily 𝕜 E ι)

theorem basis_sets_iff {U : Set E} : U ∈ p.basis_sets ↔ ∃ (i : Finset ι)(r : _)(hr : 0 < r), U = Ball (i.sup p) 0 r :=
  by
  simp only [← basis_sets, ← mem_Union, ← mem_singleton_iff]

theorem basis_sets_mem (i : Finset ι) {r : ℝ} (hr : 0 < r) : (i.sup p).ball 0 r ∈ p.basis_sets :=
  (basis_sets_iff _).mpr ⟨i, _, hr, rfl⟩

theorem basis_sets_singleton_mem (i : ι) {r : ℝ} (hr : 0 < r) : (p i).ball 0 r ∈ p.basis_sets :=
  (basis_sets_iff _).mpr
    ⟨{i}, _, hr, by
      rw [Finset.sup_singleton]⟩

theorem basis_sets_nonempty [Nonempty ι] : p.basis_sets.Nonempty := by
  let i := Classical.arbitrary ι
  refine' set.nonempty_def.mpr ⟨(p i).ball 0 1, _⟩
  exact p.basis_sets_singleton_mem i zero_lt_one

theorem basis_sets_intersect (U V : Set E) (hU : U ∈ p.basis_sets) (hV : V ∈ p.basis_sets) :
    ∃ (z : Set E)(H : z ∈ p.basis_sets), z ⊆ U ∩ V := by
  classical
  rcases p.basis_sets_iff.mp hU with ⟨s, r₁, hr₁, hU⟩
  rcases p.basis_sets_iff.mp hV with ⟨t, r₂, hr₂, hV⟩
  use ((s ∪ t).sup p).ball 0 (min r₁ r₂)
  refine' ⟨p.basis_sets_mem (s ∪ t) (lt_min_iff.mpr ⟨hr₁, hr₂⟩), _⟩
  rw [hU, hV, ball_finset_sup_eq_Inter _ _ _ (lt_min_iff.mpr ⟨hr₁, hr₂⟩), ball_finset_sup_eq_Inter _ _ _ hr₁,
    ball_finset_sup_eq_Inter _ _ _ hr₂]
  exact
    Set.subset_inter (Set.Inter₂_mono' fun i hi => ⟨i, Finset.subset_union_left _ _ hi, ball_mono <| min_le_leftₓ _ _⟩)
      (Set.Inter₂_mono' fun i hi => ⟨i, Finset.subset_union_right _ _ hi, ball_mono <| min_le_rightₓ _ _⟩)

theorem basis_sets_zero (U) (hU : U ∈ p.basis_sets) : (0 : E) ∈ U := by
  rcases p.basis_sets_iff.mp hU with ⟨ι', r, hr, hU⟩
  rw [hU, mem_ball_zero, map_zero]
  exact hr

theorem basis_sets_add (U) (hU : U ∈ p.basis_sets) : ∃ (V : Set E)(H : V ∈ p.basis_sets), V + V ⊆ U := by
  rcases p.basis_sets_iff.mp hU with ⟨s, r, hr, hU⟩
  use (s.sup p).ball 0 (r / 2)
  refine' ⟨p.basis_sets_mem s (div_pos hr zero_lt_two), _⟩
  refine' Set.Subset.trans (ball_add_ball_subset (s.sup p) (r / 2) (r / 2) 0 0) _
  rw [hU, add_zeroₓ, add_halves']

theorem basis_sets_neg (U) (hU' : U ∈ p.basis_sets) :
    ∃ (V : Set E)(H : V ∈ p.basis_sets), V ⊆ (fun x : E => -x) ⁻¹' U := by
  rcases p.basis_sets_iff.mp hU' with ⟨s, r, hr, hU⟩
  rw [hU, neg_preimage, neg_ball (s.sup p), neg_zero]
  exact ⟨U, hU', Eq.subset hU⟩

/-- The `add_group_filter_basis` induced by the filter basis `seminorm_basis_zero`. -/
protected def addGroupFilterBasis [Nonempty ι] : AddGroupFilterBasis E :=
  addGroupFilterBasisOfComm p.basis_sets p.basis_sets_nonempty p.basis_sets_intersect p.basis_sets_zero p.basis_sets_add
    p.basis_sets_neg

theorem basis_sets_smul_right (v : E) (U : Set E) (hU : U ∈ p.basis_sets) : ∀ᶠ x : 𝕜 in 𝓝 0, x • v ∈ U := by
  rcases p.basis_sets_iff.mp hU with ⟨s, r, hr, hU⟩
  rw [hU, Filter.eventually_iff]
  simp_rw [(s.sup p).mem_ball_zero, (s.sup p).smul]
  by_cases' h : 0 < (s.sup p) v
  · simp_rw [(lt_div_iff h).symm]
    rw [← _root_.ball_zero_eq]
    exact Metric.ball_mem_nhds 0 (div_pos hr h)
    
  simp_rw [le_antisymmₓ (not_lt.mp h) ((s.sup p).Nonneg v), mul_zero, hr]
  exact IsOpen.mem_nhds is_open_univ (mem_univ 0)

variable [Nonempty ι]

theorem basis_sets_smul (U) (hU : U ∈ p.basis_sets) :
    ∃ (V : Set 𝕜)(H : V ∈ 𝓝 (0 : 𝕜))(W : Set E)(H : W ∈ p.AddGroupFilterBasis.Sets), V • W ⊆ U := by
  rcases p.basis_sets_iff.mp hU with ⟨s, r, hr, hU⟩
  refine' ⟨Metric.Ball 0 r.sqrt, Metric.ball_mem_nhds 0 (real.sqrt_pos.mpr hr), _⟩
  refine' ⟨(s.sup p).ball 0 r.sqrt, p.basis_sets_mem s (real.sqrt_pos.mpr hr), _⟩
  refine' Set.Subset.trans (ball_smul_ball (s.sup p) r.sqrt r.sqrt) _
  rw [hU, Real.mul_self_sqrt (le_of_ltₓ hr)]

theorem basis_sets_smul_left (x : 𝕜) (U : Set E) (hU : U ∈ p.basis_sets) :
    ∃ (V : Set E)(H : V ∈ p.AddGroupFilterBasis.Sets), V ⊆ (fun y : E => x • y) ⁻¹' U := by
  rcases p.basis_sets_iff.mp hU with ⟨s, r, hr, hU⟩
  rw [hU]
  by_cases' h : x ≠ 0
  · rw [(s.sup p).smul_ball_preimage 0 r x h, smul_zero]
    use (s.sup p).ball 0 (r / ∥x∥)
    exact ⟨p.basis_sets_mem s (div_pos hr (norm_pos_iff.mpr h)), subset.rfl⟩
    
  refine' ⟨(s.sup p).ball 0 r, p.basis_sets_mem s hr, _⟩
  simp only [← not_ne_iff.mp h, ← subset_def, ← mem_ball_zero, ← hr, ← mem_univ, ← map_zero, ← implies_true_iff, ←
    preimage_const_of_mem, ← zero_smul]

/-- The `module_filter_basis` induced by the filter basis `seminorm_basis_zero`. -/
protected def moduleFilterBasis : ModuleFilterBasis 𝕜 E where
  toAddGroupFilterBasis := p.AddGroupFilterBasis
  smul' := p.basis_sets_smul
  smul_left' := p.basis_sets_smul_left
  smul_right' := p.basis_sets_smul_right

theorem filter_eq_infi (p : SeminormFamily 𝕜 E ι) : p.ModuleFilterBasis.toFilterBasis.filter = ⨅ i, (𝓝 0).comap (p i) :=
  by
  refine' le_antisymmₓ (le_infi fun i => _) _
  · rw [p.module_filter_basis.to_filter_basis.has_basis.le_basis_iff (metric.nhds_basis_ball.comap _)]
    intro ε hε
    refine' ⟨(p i).ball 0 ε, _, _⟩
    · rw [← (Finset.sup_singleton : _ = p i)]
      exact p.basis_sets_mem {i} hε
      
    · rw [id, (p i).ball_zero_eq_preimage_ball]
      
    
  · rw [p.module_filter_basis.to_filter_basis.has_basis.ge_iff]
    rintro U (hU : U ∈ p.basis_sets)
    rcases p.basis_sets_iff.mp hU with ⟨s, r, hr, rfl⟩
    rw [id, Seminorm.ball_finset_sup_eq_Inter _ _ _ hr, s.Inter_mem_sets]
    exact fun i hi =>
      Filter.mem_infi_of_mem i
        ⟨Metric.Ball 0 r, Metric.ball_mem_nhds 0 hr, Eq.subset (p i).ball_zero_eq_preimage_ball.symm⟩
    

end SeminormFamily

end FilterBasis

section Bounded

namespace Seminorm

variable [NormedField 𝕜] [AddCommGroupₓ E] [Module 𝕜 E] [AddCommGroupₓ F] [Module 𝕜 F]

/-- The proposition that a linear map is bounded between spaces with families of seminorms. -/
-- Todo: This should be phrased entirely in terms of the von Neumann bornology.
def IsBounded (p : ι → Seminorm 𝕜 E) (q : ι' → Seminorm 𝕜 F) (f : E →ₗ[𝕜] F) : Prop :=
  ∀ i, ∃ s : Finset ι, ∃ C : ℝ≥0 , C ≠ 0 ∧ (q i).comp f ≤ C • s.sup p

theorem is_bounded_const (ι' : Type _) [Nonempty ι'] {p : ι → Seminorm 𝕜 E} {q : Seminorm 𝕜 F} (f : E →ₗ[𝕜] F) :
    IsBounded p (fun _ : ι' => q) f ↔ ∃ (s : Finset ι)(C : ℝ≥0 ), C ≠ 0 ∧ q.comp f ≤ C • s.sup p := by
  simp only [← is_bounded, ← forall_const]

theorem const_is_bounded (ι : Type _) [Nonempty ι] {p : Seminorm 𝕜 E} {q : ι' → Seminorm 𝕜 F} (f : E →ₗ[𝕜] F) :
    IsBounded (fun _ : ι => p) q f ↔ ∀ i, ∃ C : ℝ≥0 , C ≠ 0 ∧ (q i).comp f ≤ C • p := by
  constructor <;> intro h i
  · rcases h i with ⟨s, C, hC, h⟩
    exact ⟨C, hC, le_transₓ h (smul_le_smul (Finset.sup_le fun _ _ => le_rfl) le_rfl)⟩
    
  use {Classical.arbitrary ι}
  simp only [← h, ← Finset.sup_singleton]

theorem is_bounded_sup {p : ι → Seminorm 𝕜 E} {q : ι' → Seminorm 𝕜 F} {f : E →ₗ[𝕜] F} (hf : IsBounded p q f)
    (s' : Finset ι') : ∃ (C : ℝ≥0 )(s : Finset ι), 0 < C ∧ (s'.sup q).comp f ≤ C • s.sup p := by
  classical
  by_cases' hs' : ¬s'.nonempty
  · refine' ⟨1, ∅, zero_lt_one, _⟩
    rw [finset.not_nonempty_iff_eq_empty.mp hs', Finset.sup_empty, Seminorm.bot_eq_zero, zero_comp]
    exact Seminorm.nonneg _
    
  rw [not_not] at hs'
  choose fₛ fC hf using hf
  use s'.card • s'.sup fC, Finset.bUnion s' fₛ
  constructor
  · refine' nsmul_pos _ (ne_of_gtₓ (Finset.Nonempty.card_pos hs'))
    cases' Finset.Nonempty.bex hs' with j hj
    exact lt_of_lt_of_leₓ (zero_lt_iff.mpr (And.elim_left (hf j))) (Finset.le_sup hj)
    
  have hs : ∀ i : ι', i ∈ s' → (q i).comp f ≤ s'.sup fC • (Finset.bUnion s' fₛ).sup p := by
    intro i hi
    refine' le_transₓ (And.elim_right (hf i)) (smul_le_smul _ (Finset.le_sup hi))
    exact Finset.sup_mono (Finset.subset_bUnion_of_mem fₛ hi)
  refine' le_transₓ (comp_mono f (finset_sup_le_sum q s')) _
  simp_rw [← pullback_apply, AddMonoidHom.map_sum, pullback_apply]
  refine' le_transₓ (Finset.sum_le_sum hs) _
  rw [Finset.sum_const, smul_assoc]
  exact le_rfl

end Seminorm

end Bounded

section Topology

variable [NormedField 𝕜] [AddCommGroupₓ E] [Module 𝕜 E] [Nonempty ι]

/-- The proposition that the topology of `E` is induced by a family of seminorms `p`. -/
class WithSeminorms (p : SeminormFamily 𝕜 E ι) [t : TopologicalSpace E] : Prop where
  topology_eq_with_seminorms : t = p.ModuleFilterBasis.topology

theorem SeminormFamily.with_seminorms_eq (p : SeminormFamily 𝕜 E ι) [t : TopologicalSpace E] [WithSeminorms p] :
    t = p.ModuleFilterBasis.topology :=
  WithSeminorms.topology_eq_with_seminorms

variable [TopologicalSpace E]

variable (p : SeminormFamily 𝕜 E ι) [WithSeminorms p]

theorem SeminormFamily.has_basis : (𝓝 (0 : E)).HasBasis (fun s : Set E => s ∈ p.basis_sets) id := by
  rw [congr_fun (congr_arg (@nhds E) p.with_seminorms_eq) 0]
  exact AddGroupFilterBasis.nhds_zero_has_basis _

end Topology

section TopologicalAddGroup

variable [NormedField 𝕜] [AddCommGroupₓ E] [Module 𝕜 E]

variable [TopologicalSpace E] [TopologicalAddGroup E]

variable [Nonempty ι]

theorem SeminormFamily.with_seminorms_of_nhds (p : SeminormFamily 𝕜 E ι)
    (h : 𝓝 (0 : E) = p.ModuleFilterBasis.toFilterBasis.filter) : WithSeminorms p := by
  refine'
    ⟨TopologicalAddGroup.ext
        (by
          infer_instance)
        p.add_group_filter_basis.is_topological_add_group _⟩
  rw [AddGroupFilterBasis.nhds_zero_eq]
  exact h

theorem SeminormFamily.with_seminorms_of_has_basis (p : SeminormFamily 𝕜 E ι)
    (h : (𝓝 (0 : E)).HasBasis (fun s : Set E => s ∈ p.basis_sets) id) : WithSeminorms p :=
  p.with_seminorms_of_nhds <| Filter.HasBasis.eq_of_same_basis h p.AddGroupFilterBasis.toFilterBasis.HasBasis

theorem SeminormFamily.with_seminorms_iff_nhds_eq_infi (p : SeminormFamily 𝕜 E ι) :
    WithSeminorms p ↔ (𝓝 0 : Filter E) = ⨅ i, (𝓝 0).comap (p i) := by
  rw [← p.filter_eq_infi]
  refine' ⟨fun h => _, p.with_seminorms_of_nhds⟩
  rw [h.topology_eq_with_seminorms]
  exact AddGroupFilterBasis.nhds_zero_eq _

end TopologicalAddGroup

section NormedSpace

/-- The topology of a `normed_space 𝕜 E` is induced by the seminorm `norm_seminorm 𝕜 E`. -/
instance norm_with_seminorms (𝕜 E) [NormedField 𝕜] [SemiNormedGroup E] [NormedSpace 𝕜 E] :
    WithSeminorms fun _ : Finₓ 1 => normSeminorm 𝕜 E := by
  let p : SeminormFamily 𝕜 E (Finₓ 1) := fun _ => normSeminorm 𝕜 E
  refine' ⟨TopologicalAddGroup.ext normed_top_group p.add_group_filter_basis.is_topological_add_group _⟩
  refine' Filter.HasBasis.eq_of_same_basis Metric.nhds_basis_ball _
  rw [← ball_norm_seminorm 𝕜 E]
  refine'
    Filter.HasBasis.to_has_basis p.add_group_filter_basis.nhds_zero_has_basis _ fun r hr =>
      ⟨(normSeminorm 𝕜 E).ball 0 r, p.basis_sets_singleton_mem 0 hr, rfl.subset⟩
  rintro U (hU : U ∈ p.basis_sets)
  rcases p.basis_sets_iff.mp hU with ⟨s, r, hr, hU⟩
  use r, hr
  rw [hU, id.def]
  by_cases' h : s.nonempty
  · rw [Finset.sup_const h]
    
  rw [finset.not_nonempty_iff_eq_empty.mp h, Finset.sup_empty, ball_bot _ hr]
  exact Set.subset_univ _

end NormedSpace

section NondiscreteNormedField

variable [NondiscreteNormedField 𝕜] [AddCommGroupₓ E] [Module 𝕜 E] [Nonempty ι]

variable (p : SeminormFamily 𝕜 E ι)

variable [TopologicalSpace E] [WithSeminorms p]

theorem Bornology.is_vonN_bounded_iff_finset_seminorm_bounded {s : Set E} :
    Bornology.IsVonNBounded 𝕜 s ↔ ∀ I : Finset ι, ∃ (r : _)(hr : 0 < r), ∀, ∀ x ∈ s, ∀, I.sup p x < r := by
  rw [p.has_basis.is_vonN_bounded_basis_iff]
  constructor
  · intro h I
    simp only [← id.def] at h
    specialize h ((I.sup p).ball 0 1) (p.basis_sets_mem I zero_lt_one)
    rcases h with ⟨r, hr, h⟩
    cases' NormedField.exists_lt_norm 𝕜 r with a ha
    specialize h a (le_of_ltₓ ha)
    rw [Seminorm.smul_ball_zero (lt_transₓ hr ha), mul_oneₓ] at h
    refine' ⟨∥a∥, lt_transₓ hr ha, _⟩
    intro x hx
    specialize h hx
    exact (Finset.sup I p).mem_ball_zero.mp h
    
  intro h s' hs'
  rcases p.basis_sets_iff.mp hs' with ⟨I, r, hr, hs'⟩
  rw [id.def, hs']
  rcases h I with ⟨r', hr', h'⟩
  simp_rw [← (I.sup p).mem_ball_zero] at h'
  refine' Absorbs.mono_right _ h'
  exact (Finset.sup I p).ball_zero_absorbs_ball_zero hr

theorem Bornology.is_vonN_bounded_iff_seminorm_bounded {s : Set E} :
    Bornology.IsVonNBounded 𝕜 s ↔ ∀ i : ι, ∃ (r : _)(hr : 0 < r), ∀, ∀ x ∈ s, ∀, p i x < r := by
  rw [Bornology.is_vonN_bounded_iff_finset_seminorm_bounded p]
  constructor
  · intro hI i
    convert hI {i}
    rw [Finset.sup_singleton]
    
  intro hi I
  by_cases' hI : I.nonempty
  · choose r hr h using hi
    have h' : 0 < I.sup' hI r := by
      rcases hI.bex with ⟨i, hi⟩
      exact lt_of_lt_of_leₓ (hr i) (Finset.le_sup' r hi)
    refine' ⟨I.sup' hI r, h', fun x hx => finset_sup_apply_lt h' fun i hi => _⟩
    refine' lt_of_lt_of_leₓ (h i x hx) _
    simp only [← Finset.le_sup'_iff, ← exists_prop]
    exact ⟨i, hi, (Eq.refl _).le⟩
    
  simp only [← finset.not_nonempty_iff_eq_empty.mp hI, ← Finset.sup_empty, ← coe_bot, ← Pi.zero_apply, ← exists_prop]
  exact ⟨1, zero_lt_one, fun _ _ => zero_lt_one⟩

end NondiscreteNormedField

section ContinuousBounded

namespace Seminorm

variable [NormedField 𝕜] [AddCommGroupₓ E] [Module 𝕜 E] [AddCommGroupₓ F] [Module 𝕜 F]

variable [Nonempty ι] [Nonempty ι']

theorem continuous_from_bounded (p : SeminormFamily 𝕜 E ι) (q : SeminormFamily 𝕜 F ι') [UniformSpace E]
    [UniformAddGroup E] [WithSeminorms p] [UniformSpace F] [UniformAddGroup F] [WithSeminorms q] (f : E →ₗ[𝕜] F)
    (hf : Seminorm.IsBounded p q f) : Continuous f := by
  refine' continuous_of_continuous_at_zero f _
  rw [continuous_at_def, f.map_zero, p.with_seminorms_eq]
  intro U hU
  rw [q.with_seminorms_eq, AddGroupFilterBasis.nhds_zero_eq, FilterBasis.mem_filter_iff] at hU
  rcases hU with ⟨V, hV : V ∈ q.basis_sets, hU⟩
  rcases q.basis_sets_iff.mp hV with ⟨s₂, r, hr, hV⟩
  rw [hV] at hU
  rw [p.add_group_filter_basis.nhds_zero_eq, FilterBasis.mem_filter_iff]
  rcases Seminorm.is_bounded_sup hf s₂ with ⟨C, s₁, hC, hf⟩
  refine' ⟨(s₁.sup p).ball 0 (r / C), p.basis_sets_mem _ (div_pos hr (nnreal.coe_pos.mpr hC)), _⟩
  refine' subset.trans _ (preimage_mono hU)
  simp_rw [← LinearMap.map_zero f, ← ball_comp]
  refine' subset.trans _ (ball_antitone hf)
  rw [ball_smul (s₁.sup p) hC]

theorem cont_with_seminorms_normed_space (F) [SemiNormedGroup F] [NormedSpace 𝕜 F] [UniformSpace E] [UniformAddGroup E]
    (p : ι → Seminorm 𝕜 E) [WithSeminorms p] (f : E →ₗ[𝕜] F)
    (hf : ∃ (s : Finset ι)(C : ℝ≥0 ), C ≠ 0 ∧ (normSeminorm 𝕜 F).comp f ≤ C • s.sup p) : Continuous f := by
  rw [← Seminorm.is_bounded_const (Finₓ 1)] at hf
  exact continuous_from_bounded p (fun _ : Finₓ 1 => normSeminorm 𝕜 F) f hf

theorem cont_normed_space_to_with_seminorms (E) [SemiNormedGroup E] [NormedSpace 𝕜 E] [UniformSpace F]
    [UniformAddGroup F] (q : ι → Seminorm 𝕜 F) [WithSeminorms q] (f : E →ₗ[𝕜] F)
    (hf : ∀ i : ι, ∃ C : ℝ≥0 , C ≠ 0 ∧ (q i).comp f ≤ C • normSeminorm 𝕜 E) : Continuous f := by
  rw [← Seminorm.const_is_bounded (Finₓ 1)] at hf
  exact continuous_from_bounded (fun _ : Finₓ 1 => normSeminorm 𝕜 E) q f hf

end Seminorm

end ContinuousBounded

section LocallyConvexSpace

open LocallyConvexSpace

variable [Nonempty ι] [NormedField 𝕜] [NormedSpace ℝ 𝕜] [AddCommGroupₓ E] [Module 𝕜 E] [Module ℝ E]
  [IsScalarTower ℝ 𝕜 E] [TopologicalSpace E] [TopologicalAddGroup E]

theorem SeminormFamily.to_locally_convex_space (p : SeminormFamily 𝕜 E ι) [WithSeminorms p] : LocallyConvexSpace ℝ E :=
  by
  apply of_basis_zero ℝ E id fun s => s ∈ p.basis_sets
  · rw [p.with_seminorms_eq, AddGroupFilterBasis.nhds_eq _, AddGroupFilterBasis.N_zero]
    exact FilterBasis.has_basis _
    
  · intro s hs
    change s ∈ Set.Union _ at hs
    simp_rw [Set.mem_Union, Set.mem_singleton_iff] at hs
    rcases hs with ⟨I, r, hr, rfl⟩
    exact convex_ball _ _ _
    

end LocallyConvexSpace

section NormedSpace

variable (𝕜) [NormedField 𝕜] [NormedSpace ℝ 𝕜] [SemiNormedGroup E]

/-- Not an instance since `𝕜` can't be inferred. See `normed_space.to_locally_convex_space` for a
slightly weaker instance version. -/
theorem NormedSpace.to_locally_convex_space' [NormedSpace 𝕜 E] [Module ℝ E] [IsScalarTower ℝ 𝕜 E] :
    LocallyConvexSpace ℝ E :=
  SeminormFamily.to_locally_convex_space fun _ : Finₓ 1 => normSeminorm 𝕜 E

/-- See `normed_space.to_locally_convex_space'` for a slightly stronger version which is not an
instance. -/
instance NormedSpace.to_locally_convex_space [NormedSpace ℝ E] : LocallyConvexSpace ℝ E :=
  NormedSpace.to_locally_convex_space' ℝ

end NormedSpace

section TopologicalConstructions

variable [NormedField 𝕜] [AddCommGroupₓ F] [Module 𝕜 F] [AddCommGroupₓ E] [Module 𝕜 E]

/-- The family of seminorms obtained by composing each seminorm by a linear map. -/
def SeminormFamily.comp (q : SeminormFamily 𝕜 F ι) (f : E →ₗ[𝕜] F) : SeminormFamily 𝕜 E ι := fun i => (q i).comp f

theorem SeminormFamily.comp_apply (q : SeminormFamily 𝕜 F ι) (i : ι) (f : E →ₗ[𝕜] F) : q.comp f i = (q i).comp f :=
  rfl

theorem SeminormFamily.finset_sup_comp (q : SeminormFamily 𝕜 F ι) (s : Finset ι) (f : E →ₗ[𝕜] F) :
    (s.sup q).comp f = s.sup (q.comp f) := by
  ext x
  rw [Seminorm.comp_apply, Seminorm.finset_sup_apply, Seminorm.finset_sup_apply]
  rfl

variable [TopologicalSpace F] [TopologicalAddGroup F]

theorem LinearMap.with_seminorms_induced [hι : Nonempty ι] {q : SeminormFamily 𝕜 F ι} [hq : WithSeminorms q]
    (f : E →ₗ[𝕜] F) : @WithSeminorms 𝕜 E ι _ _ _ _ (q.comp f) (induced f inferInstance) := by
  let this : TopologicalSpace E := induced f inferInstance
  let this : TopologicalAddGroup E := topological_add_group_induced f
  rw [(q.comp f).with_seminorms_iff_nhds_eq_infi, nhds_induced, map_zero, q.with_seminorms_iff_nhds_eq_infi.mp hq,
    Filter.comap_infi]
  refine' infi_congr fun i => _
  exact Filter.comap_comap

theorem Inducing.with_seminorms [hι : Nonempty ι] {q : SeminormFamily 𝕜 F ι} [hq : WithSeminorms q] [TopologicalSpace E]
    {f : E →ₗ[𝕜] F} (hf : Inducing f) : WithSeminorms (q.comp f) := by
  rw [hf.induced]
  exact f.with_seminorms_induced

end TopologicalConstructions

