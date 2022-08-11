/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathbin.Analysis.BoxIntegral.Partition.Basic

/-!
# Tagged partitions

A tagged (pre)partition is a (pre)partition `π` enriched with a tagged point for each box of
‵π`. For simplicity we require that the function `box_integral.tagged_prepartition.tag` is defined
on all boxes `J : box ι` but use its values only on boxes of the partition. Given `π :
box_integral.tagged_partition I`, we require that each `box_integral.tagged_partition π J` belongs
to `box_integral.box.Icc I`. If for every `J ∈ π`, `π.tag J` belongs to `J.Icc`, then `π` is called
a *Henstock* partition. We do not include this assumption into the definition of a tagged
(pre)partition because McShane integral is defined as a limit along tagged partitions without this
requirement.

### Tags

rectangular box, box partition
-/


noncomputable section

open Classical Ennreal Nnreal

open Set Function

namespace BoxIntegral

variable {ι : Type _}

/-- A tagged prepartition is a prepartition enriched with a tagged point for each box of the
prepartition. For simiplicity we require that `tag` is defined for all boxes in `ι → ℝ` but
we will use onle the values of `tag` on the boxes of the partition. -/
structure TaggedPrepartition (I : Box ι) extends Prepartition I where
  Tag : Box ι → ι → ℝ
  tag_mem_Icc : ∀ J, tag J ∈ I.Icc

namespace TaggedPrepartition

variable {I J J₁ J₂ : Box ι} (π : TaggedPrepartition I) {x : ι → ℝ}

instance : HasMem (Box ι) (TaggedPrepartition I) :=
  ⟨fun J π => J ∈ π.boxes⟩

@[simp]
theorem mem_to_prepartition {π : TaggedPrepartition I} : J ∈ π.toPrepartition ↔ J ∈ π :=
  Iff.rfl

@[simp]
theorem mem_mk (π : Prepartition I) (f h) : J ∈ mk π f h ↔ J ∈ π :=
  Iff.rfl

/-- Union of all boxes of a tagged prepartition. -/
def Union : Set (ι → ℝ) :=
  π.toPrepartition.Union

theorem Union_def : π.Union = ⋃ J ∈ π, ↑J :=
  rfl

@[simp]
theorem Union_mk (π : Prepartition I) (f h) : (mk π f h).Union = π.Union :=
  rfl

@[simp]
theorem Union_to_prepartition : π.toPrepartition.Union = π.Union :=
  rfl

@[simp]
theorem mem_Union : x ∈ π.Union ↔ ∃ J ∈ π, x ∈ J :=
  Set.mem_Union₂

theorem subset_Union (h : J ∈ π) : ↑J ⊆ π.Union :=
  subset_bUnion_of_mem h

theorem Union_subset : π.Union ⊆ I :=
  Union₂_subset π.le_of_mem'

/-- A tagged prepartition is a partition if it covers the whole box. -/
def IsPartition :=
  π.toPrepartition.IsPartition

theorem is_partition_iff_Union_eq : IsPartition π ↔ π.Union = I :=
  prepartition.is_partition_iff_Union_eq

/-- The tagged partition made of boxes of `π` that satisfy predicate `p`. -/
@[simps (config := { fullyApplied := false })]
def filter (p : Box ι → Prop) : TaggedPrepartition I :=
  ⟨π.1.filter p, π.2, π.3⟩

@[simp]
theorem mem_filter {p : Box ι → Prop} : J ∈ π.filter p ↔ J ∈ π ∧ p J :=
  Finset.mem_filter

@[simp]
theorem Union_filter_not (π : TaggedPrepartition I) (p : Box ι → Prop) :
    (π.filter fun J => ¬p J).Union = π.Union \ (π.filter p).Union :=
  π.toPrepartition.Union_filter_not p

end TaggedPrepartition

namespace Prepartition

variable {I J : Box ι}

/-- Given a partition `π` of `I : box_integral.box ι` and a collection of tagged partitions
`πi J` of all boxes `J ∈ π`, returns the tagged partition of `I` into all the boxes of `πi J`
with tags coming from `(πi J).tag`. -/
def bUnionTagged (π : Prepartition I) (πi : ∀ J, TaggedPrepartition J) : TaggedPrepartition I where
  toPrepartition := π.bUnion fun J => (πi J).toPrepartition
  Tag := fun J => (πi (π.bUnionIndex (fun J => (πi J).toPrepartition) J)).Tag J
  tag_mem_Icc := fun J => Box.le_iff_Icc.1 (π.bUnion_index_le _ _) ((πi _).tag_mem_Icc _)

@[simp]
theorem mem_bUnion_tagged (π : Prepartition I) {πi : ∀ J, TaggedPrepartition J} :
    J ∈ π.bUnionTagged πi ↔ ∃ J' ∈ π, J ∈ πi J' :=
  π.mem_bUnion

theorem tag_bUnion_tagged (π : Prepartition I) {πi : ∀ J, TaggedPrepartition J} (hJ : J ∈ π) {J'} (hJ' : J' ∈ πi J) :
    (π.bUnionTagged πi).Tag J' = (πi J).Tag J' := by
  have : J' ∈ π.bUnion_tagged πi := π.mem_bUnion.2 ⟨J, hJ, hJ'⟩
  obtain rfl := π.bUnion_index_of_mem hJ hJ'
  rfl

@[simp]
theorem Union_bUnion_tagged (π : Prepartition I) (πi : ∀ J, TaggedPrepartition J) :
    (π.bUnionTagged πi).Union = ⋃ J ∈ π, (πi J).Union :=
  Union_bUnion _ _

theorem forall_bUnion_tagged (p : (ι → ℝ) → Box ι → Prop) (π : Prepartition I) (πi : ∀ J, TaggedPrepartition J) :
    (∀, ∀ J ∈ π.bUnionTagged πi, ∀, p ((π.bUnionTagged πi).Tag J) J) ↔
      ∀, ∀ J ∈ π, ∀, ∀ J' ∈ πi J, ∀, p ((πi J).Tag J') J' :=
  by
  simp only [← bex_imp_distrib, ← mem_bUnion_tagged]
  refine' ⟨fun H J hJ J' hJ' => _, fun H J' J hJ hJ' => _⟩
  · rw [← π.tag_bUnion_tagged hJ hJ']
    exact H J' J hJ hJ'
    
  · rw [π.tag_bUnion_tagged hJ hJ']
    exact H J hJ J' hJ'
    

theorem IsPartition.bUnion_tagged {π : Prepartition I} (h : IsPartition π) {πi : ∀ J, TaggedPrepartition J}
    (hi : ∀, ∀ J ∈ π, ∀, (πi J).IsPartition) : (π.bUnionTagged πi).IsPartition :=
  h.bUnion hi

end Prepartition

namespace TaggedPrepartition

variable {I J : Box ι} {π π₁ π₂ : TaggedPrepartition I} {x : ι → ℝ}

/-- Given a tagged partition `π` of `I` and a (not tagged) partition `πi J hJ` of each `J ∈ π`,
returns the tagged partition of `I` into all the boxes of all `πi J hJ`. The tag of a box `J`
is defined to be the `π.tag` of the box of the partition `π` that includes `J`.

Note that usually the result is not a Henstock partition. -/
@[simps (config := { fullyApplied := false }) Tag]
def bUnionPrepartition (π : TaggedPrepartition I) (πi : ∀ J, Prepartition J) : TaggedPrepartition I where
  toPrepartition := π.toPrepartition.bUnion πi
  Tag := fun J => π.Tag (π.toPrepartition.bUnionIndex πi J)
  tag_mem_Icc := fun J => π.tag_mem_Icc _

theorem IsPartition.bUnion_prepartition {π : TaggedPrepartition I} (h : IsPartition π) {πi : ∀ J, Prepartition J}
    (hi : ∀, ∀ J ∈ π, ∀, (πi J).IsPartition) : (π.bUnionPrepartition πi).IsPartition :=
  h.bUnion hi

/-- Given two partitions `π₁` and `π₁`, one of them tagged and the other is not, returns the tagged
partition with `to_partition = π₁.to_partition ⊓ π₂` and tags coming from `π₁`.

Note that usually the result is not a Henstock partition. -/
def infPrepartition (π : TaggedPrepartition I) (π' : Prepartition I) : TaggedPrepartition I :=
  π.bUnionPrepartition fun J => π'.restrict J

@[simp]
theorem inf_prepartition_to_prepartition (π : TaggedPrepartition I) (π' : Prepartition I) :
    (π.infPrepartition π').toPrepartition = π.toPrepartition⊓π' :=
  rfl

theorem mem_inf_prepartition_comm :
    J ∈ π₁.infPrepartition π₂.toPrepartition ↔ J ∈ π₂.infPrepartition π₁.toPrepartition := by
  simp only [mem_to_prepartition, ← inf_prepartition_to_prepartition, ← inf_comm]

theorem IsPartition.inf_prepartition (h₁ : π₁.IsPartition) {π₂ : Prepartition I} (h₂ : π₂.IsPartition) :
    (π₁.infPrepartition π₂).IsPartition :=
  h₁.inf h₂

open Metric

/-- A tagged partition is said to be a Henstock partition if for each `J ∈ π`, the tag of `J`
belongs to `J.Icc`. -/
def IsHenstock (π : TaggedPrepartition I) : Prop :=
  ∀, ∀ J ∈ π, ∀, π.Tag J ∈ J.Icc

@[simp]
theorem is_Henstock_bUnion_tagged {π : Prepartition I} {πi : ∀ J, TaggedPrepartition J} :
    IsHenstock (π.bUnionTagged πi) ↔ ∀, ∀ J ∈ π, ∀, (πi J).IsHenstock :=
  π.forall_bUnion_tagged (fun x J => x ∈ J.Icc) πi

/-- In a Henstock prepartition, there are at most `2 ^ fintype.card ι` boxes with a given tag. -/
theorem IsHenstock.card_filter_tag_eq_le [Fintype ι] (h : π.IsHenstock) (x : ι → ℝ) :
    (π.boxes.filter fun J => π.Tag J = x).card ≤ 2 ^ Fintype.card ι :=
  calc
    (π.boxes.filter fun J => π.Tag J = x).card ≤ (π.boxes.filter fun J : Box ι => x ∈ J.Icc).card := by
      refine' Finset.card_le_of_subset fun J hJ => _
      rw [Finset.mem_filter] at hJ⊢
      rcases hJ with ⟨hJ, rfl⟩
      exact ⟨hJ, h J hJ⟩
    _ ≤ 2 ^ Fintype.card ι := π.toPrepartition.card_filter_mem_Icc_le x
    

/-- A tagged partition `π` is subordinate to `r : (ι → ℝ) → ℝ` if each box `J ∈ π` is included in
the closed ball with center `π.tag J` and radius `r (π.tag J)`. -/
def IsSubordinate [Fintype ι] (π : TaggedPrepartition I) (r : (ι → ℝ) → Ioi (0 : ℝ)) : Prop :=
  ∀, ∀ J ∈ π, ∀, (J : _).Icc ⊆ ClosedBall (π.Tag J) (r <| π.Tag J)

variable {r r₁ r₂ : (ι → ℝ) → Ioi (0 : ℝ)}

@[simp]
theorem is_subordinate_bUnion_tagged [Fintype ι] {π : Prepartition I} {πi : ∀ J, TaggedPrepartition J} :
    IsSubordinate (π.bUnionTagged πi) r ↔ ∀, ∀ J ∈ π, ∀, (πi J).IsSubordinate r :=
  π.forall_bUnion_tagged (fun x J => J.Icc ⊆ ClosedBall x (r x)) πi

theorem IsSubordinate.bUnion_prepartition [Fintype ι] (h : IsSubordinate π r) (πi : ∀ J, Prepartition J) :
    IsSubordinate (π.bUnionPrepartition πi) r := fun J hJ =>
  Subset.trans (Box.le_iff_Icc.1 <| π.toPrepartition.le_bUnion_index hJ) <| h _ <| π.toPrepartition.bUnion_index_mem hJ

theorem IsSubordinate.inf_prepartition [Fintype ι] (h : IsSubordinate π r) (π' : Prepartition I) :
    IsSubordinate (π.infPrepartition π') r :=
  h.bUnionPrepartition _

theorem IsSubordinate.mono' [Fintype ι] {π : TaggedPrepartition I} (hr₁ : π.IsSubordinate r₁)
    (h : ∀, ∀ J ∈ π, ∀, r₁ (π.Tag J) ≤ r₂ (π.Tag J)) : π.IsSubordinate r₂ := fun J hJ x hx =>
  closed_ball_subset_closed_ball (h _ hJ) (hr₁ _ hJ hx)

theorem IsSubordinate.mono [Fintype ι] {π : TaggedPrepartition I} (hr₁ : π.IsSubordinate r₁)
    (h : ∀, ∀ x ∈ I.Icc, ∀, r₁ x ≤ r₂ x) : π.IsSubordinate r₂ :=
  hr₁.mono' fun J _ => h _ <| π.tag_mem_Icc J

theorem IsSubordinate.diam_le [Fintype ι] {π : TaggedPrepartition I} (h : π.IsSubordinate r) (hJ : J ∈ π.boxes) :
    diam J.Icc ≤ 2 * r (π.Tag J) :=
  calc
    diam J.Icc ≤ diam (ClosedBall (π.Tag J) (r <| π.Tag J)) := diam_mono (h J hJ) bounded_closed_ball
    _ ≤ 2 * r (π.Tag J) := diam_closed_ball (le_of_ltₓ (r _).2)
    

/-- Tagged prepartition with single box and prescribed tag. -/
@[simps (config := { fullyApplied := false })]
def single (I J : Box ι) (hJ : J ≤ I) (x : ι → ℝ) (h : x ∈ I.Icc) : TaggedPrepartition I :=
  ⟨Prepartition.single I J hJ, fun J => x, fun J => h⟩

@[simp]
theorem mem_single {J'} (hJ : J ≤ I) (h : x ∈ I.Icc) : J' ∈ single I J hJ x h ↔ J' = J :=
  Finset.mem_singleton

instance (I : Box ι) : Inhabited (TaggedPrepartition I) :=
  ⟨single I I le_rfl I.upper I.upper_mem_Icc⟩

theorem is_partition_single_iff (hJ : J ≤ I) (h : x ∈ I.Icc) : (single I J hJ x h).IsPartition ↔ J = I :=
  Prepartition.is_partition_single_iff hJ

theorem is_partition_single (h : x ∈ I.Icc) : (single I I le_rfl x h).IsPartition :=
  Prepartition.is_partition_top I

theorem forall_mem_single (p : (ι → ℝ) → Box ι → Prop) (hJ : J ≤ I) (h : x ∈ I.Icc) :
    (∀, ∀ J' ∈ single I J hJ x h, ∀, p ((single I J hJ x h).Tag J') J') ↔ p x J := by
  simp

@[simp]
theorem is_Henstock_single_iff (hJ : J ≤ I) (h : x ∈ I.Icc) : IsHenstock (single I J hJ x h) ↔ x ∈ J.Icc :=
  forall_mem_single (fun x J => x ∈ J.Icc) hJ h

@[simp]
theorem is_Henstock_single (h : x ∈ I.Icc) : IsHenstock (single I I le_rfl x h) :=
  (is_Henstock_single_iff (le_reflₓ I) h).2 h

@[simp]
theorem is_subordinate_single [Fintype ι] (hJ : J ≤ I) (h : x ∈ I.Icc) :
    IsSubordinate (single I J hJ x h) r ↔ J.Icc ⊆ ClosedBall x (r x) :=
  forall_mem_single (fun x J => J.Icc ⊆ ClosedBall x (r x)) hJ h

@[simp]
theorem Union_single (hJ : J ≤ I) (h : x ∈ I.Icc) : (single I J hJ x h).Union = J :=
  Prepartition.Union_single hJ

/-- Union of two tagged prepartitions with disjoint unions of boxes. -/
def disjUnion (π₁ π₂ : TaggedPrepartition I) (h : Disjoint π₁.Union π₂.Union) : TaggedPrepartition I where
  toPrepartition := π₁.toPrepartition.disjUnion π₂.toPrepartition h
  Tag := π₁.boxes.piecewise π₁.Tag π₂.Tag
  tag_mem_Icc := fun J => by
    dunfold Finset.piecewise
    split_ifs
    exacts[π₁.tag_mem_Icc J, π₂.tag_mem_Icc J]

@[simp]
theorem disj_union_boxes (h : Disjoint π₁.Union π₂.Union) : (π₁.disjUnion π₂ h).boxes = π₁.boxes ∪ π₂.boxes :=
  rfl

@[simp]
theorem mem_disj_union (h : Disjoint π₁.Union π₂.Union) : J ∈ π₁.disjUnion π₂ h ↔ J ∈ π₁ ∨ J ∈ π₂ :=
  Finset.mem_union

@[simp]
theorem Union_disj_union (h : Disjoint π₁.Union π₂.Union) : (π₁.disjUnion π₂ h).Union = π₁.Union ∪ π₂.Union :=
  Prepartition.Union_disj_union _

theorem disj_union_tag_of_mem_left (h : Disjoint π₁.Union π₂.Union) (hJ : J ∈ π₁) :
    (π₁.disjUnion π₂ h).Tag J = π₁.Tag J :=
  dif_pos hJ

theorem disj_union_tag_of_mem_right (h : Disjoint π₁.Union π₂.Union) (hJ : J ∈ π₂) :
    (π₁.disjUnion π₂ h).Tag J = π₂.Tag J :=
  dif_neg fun h₁ => h ⟨π₁.subset_Union h₁ J.upper_mem, π₂.subset_Union hJ J.upper_mem⟩

theorem IsSubordinate.disj_union [Fintype ι] (h₁ : IsSubordinate π₁ r) (h₂ : IsSubordinate π₂ r)
    (h : Disjoint π₁.Union π₂.Union) : IsSubordinate (π₁.disjUnion π₂ h) r := by
  refine' fun J hJ => (Finset.mem_union.1 hJ).elim (fun hJ => _) fun hJ => _
  · rw [disj_union_tag_of_mem_left _ hJ]
    exact h₁ _ hJ
    
  · rw [disj_union_tag_of_mem_right _ hJ]
    exact h₂ _ hJ
    

theorem IsHenstock.disj_union (h₁ : IsHenstock π₁) (h₂ : IsHenstock π₂) (h : Disjoint π₁.Union π₂.Union) :
    IsHenstock (π₁.disjUnion π₂ h) := by
  refine' fun J hJ => (Finset.mem_union.1 hJ).elim (fun hJ => _) fun hJ => _
  · rw [disj_union_tag_of_mem_left _ hJ]
    exact h₁ _ hJ
    
  · rw [disj_union_tag_of_mem_right _ hJ]
    exact h₂ _ hJ
    

/-- If `I ≤ J`, then every tagged prepartition of `I` is a tagged prepartition of `J`. -/
def embedBox (I J : Box ι) (h : I ≤ J) : TaggedPrepartition I ↪ TaggedPrepartition J where
  toFun := fun π =>
    { π with le_of_mem' := fun J' hJ' => (π.le_of_mem' J' hJ').trans h,
      tag_mem_Icc := fun J => Box.le_iff_Icc.1 h (π.tag_mem_Icc J) }
  inj' := by
    rintro ⟨⟨b₁, h₁le, h₁d⟩, t₁, ht₁⟩ ⟨⟨b₂, h₂le, h₂d⟩, t₂, ht₂⟩ H
    simpa using H

section Distortion

variable [Fintype ι] (π)

open Finset

/-- The distortion of a tagged prepartition is the maximum of distortions of its boxes. -/
def distortion : ℝ≥0 :=
  π.toPrepartition.distortion

theorem distortion_le_of_mem (h : J ∈ π) : J.distortion ≤ π.distortion :=
  le_sup h

theorem distortion_le_iff {c : ℝ≥0 } : π.distortion ≤ c ↔ ∀, ∀ J ∈ π, ∀, Box.distortion J ≤ c :=
  Finset.sup_le_iff

@[simp]
theorem _root_.box_integral.prepartition.distortion_bUnion_tagged (π : Prepartition I)
    (πi : ∀ J, TaggedPrepartition J) : (π.bUnionTagged πi).distortion = π.boxes.sup fun J => (πi J).distortion :=
  sup_bUnion _ _

@[simp]
theorem distortion_bUnion_prepartition (π : TaggedPrepartition I) (πi : ∀ J, Prepartition J) :
    (π.bUnionPrepartition πi).distortion = π.boxes.sup fun J => (πi J).distortion :=
  sup_bUnion _ _

@[simp]
theorem distortion_disj_union (h : Disjoint π₁.Union π₂.Union) :
    (π₁.disjUnion π₂ h).distortion = max π₁.distortion π₂.distortion :=
  sup_union

theorem distortion_of_const {c} (h₁ : π.boxes.Nonempty) (h₂ : ∀, ∀ J ∈ π, ∀, Box.distortion J = c) : π.distortion = c :=
  (sup_congr rfl h₂).trans (sup_const h₁ _)

@[simp]
theorem distortion_single (hJ : J ≤ I) (h : x ∈ I.Icc) : distortion (single I J hJ x h) = J.distortion :=
  sup_singleton

theorem distortion_filter_le (p : Box ι → Prop) : (π.filter p).distortion ≤ π.distortion :=
  sup_mono (filter_subset _ _)

end Distortion

end TaggedPrepartition

end BoxIntegral

