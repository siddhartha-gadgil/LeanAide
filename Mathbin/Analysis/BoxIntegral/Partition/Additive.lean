/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathbin.Analysis.BoxIntegral.Partition.Split
import Mathbin.Analysis.NormedSpace.OperatorNorm
import Mathbin.Data.Set.Intervals.ProjIcc

/-!
# Box additive functions

We say that a function `f : box ι → M` from boxes in `ℝⁿ` to a commutative additive monoid `M` is
*box additive* on subboxes of `I₀ : with_top (box ι)` if for any box `J`, `↑J ≤ I₀`, and a partition
`π` of `J`, `f J = ∑ J' in π.boxes, f J'`. We use `I₀ : with_top (box ι)` instead of `I₀ : box ι` to
use the same definition for functions box additive on subboxes of a box and for functions box
additive on all boxes.

Examples of box-additive functions include the measure of a box and the integral of a fixed
integrable function over a box.

In this file we define box-additive functions and prove that a function such that
`f J = f (J ∩ {x | x i < y}) + f (J ∩ {x | y ≤ x i})` is box-additive.

### Tags

rectangular box, additive function
-/


noncomputable section

open Classical BigOperators

open Function Set

namespace BoxIntegral

variable {ι M : Type _} {n : ℕ}

/-- A function on `box ι` is called box additive if for every box `J` and a partition `π` of `J`
we have `f J = ∑ Ji in π.boxes, f Ji`. A function is called box additive on subboxes of `I : box ι`
if the same property holds for `J ≤ I`. We formalize these two notions in the same definition
using `I : with_bot (box ι)`: the value `I = ⊤` corresponds to functions box additive on the whole
space.  -/
structure BoxAdditiveMap (ι M : Type _) [AddCommMonoidₓ M] (I : WithTop (Box ι)) where
  toFun : Box ι → M
  sum_partition_boxes' :
    ∀ J : Box ι, ↑J ≤ I → ∀ π : Prepartition J, π.IsPartition → (∑ Ji in π.boxes, to_fun Ji) = to_fun J

-- mathport name: «expr →ᵇᵃ »
localized [BoxIntegral] notation:25 ι " →ᵇᵃ " M => BoxIntegral.BoxAdditiveMap ι M ⊤

-- mathport name: «expr →ᵇᵃ[ ] »
localized [BoxIntegral] notation:25 ι " →ᵇᵃ[" I "] " M => BoxIntegral.BoxAdditiveMap ι M I

namespace BoxAdditiveMap

open Box Prepartition Finset

variable {N : Type _} [AddCommMonoidₓ M] [AddCommMonoidₓ N] {I₀ : WithTop (Box ι)} {I J : Box ι} {i : ι}

instance : CoeFun (ι →ᵇᵃ[I₀] M) fun _ => Box ι → M :=
  ⟨toFun⟩

initialize_simps_projections box_integral.box_additive_map (toFun → apply)

@[simp]
theorem to_fun_eq_coe (f : ι →ᵇᵃ[I₀] M) : f.toFun = f :=
  rfl

@[simp]
theorem coe_mk (f h) : ⇑(mk f h : ι →ᵇᵃ[I₀] M) = f :=
  rfl

theorem coe_injective : Injective fun (f : ι →ᵇᵃ[I₀] M) x => f x := by
  rintro ⟨f, hf⟩ ⟨g, hg⟩ (rfl : f = g)
  rfl

@[simp]
theorem coe_inj {f g : ι →ᵇᵃ[I₀] M} : (f : Box ι → M) = g ↔ f = g :=
  coe_injective.eq_iff

theorem sum_partition_boxes (f : ι →ᵇᵃ[I₀] M) (hI : ↑I ≤ I₀) {π : Prepartition I} (h : π.IsPartition) :
    (∑ J in π.boxes, f J) = f I :=
  f.sum_partition_boxes' I hI π h

@[simps (config := { fullyApplied := false })]
instance : Zero (ι →ᵇᵃ[I₀] M) :=
  ⟨⟨0, fun I hI π hπ => sum_const_zero⟩⟩

instance : Inhabited (ι →ᵇᵃ[I₀] M) :=
  ⟨0⟩

instance : Add (ι →ᵇᵃ[I₀] M) :=
  ⟨fun f g =>
    ⟨f + g, fun I hI π hπ => by
      simp only [← Pi.add_apply, ← sum_add_distrib, ← sum_partition_boxes _ hI hπ]⟩⟩

instance {R} [Monoidₓ R] [DistribMulAction R M] : HasSmul R (ι →ᵇᵃ[I₀] M) :=
  ⟨fun r f =>
    ⟨r • f, fun I hI π hπ => by
      simp only [← Pi.smul_apply, smul_sum, ← sum_partition_boxes _ hI hπ]⟩⟩

instance : AddCommMonoidₓ (ι →ᵇᵃ[I₀] M) :=
  Function.Injective.addCommMonoid _ coe_injective rfl (fun _ _ => rfl) fun _ _ => rfl

@[simp]
theorem map_split_add (f : ι →ᵇᵃ[I₀] M) (hI : ↑I ≤ I₀) (i : ι) (x : ℝ) :
    (I.splitLower i x).elim 0 f + (I.splitUpper i x).elim 0 f = f I := by
  rw [← f.sum_partition_boxes hI (is_partition_split I i x), sum_split_boxes]

/-- If `f` is box-additive on subboxes of `I₀`, then it is box-additive on subboxes of any
`I ≤ I₀`. -/
@[simps]
def restrict (f : ι →ᵇᵃ[I₀] M) (I : WithTop (Box ι)) (hI : I ≤ I₀) : ι →ᵇᵃ[I] M :=
  ⟨f, fun J hJ => f.2 J (hJ.trans hI)⟩

/-- If `f : box ι → M` is box additive on partitions of the form `split I i x`, then it is box
additive. -/
def ofMapSplitAdd [Fintype ι] (f : Box ι → M) (I₀ : WithTop (Box ι))
    (hf :
      ∀ I : Box ι,
        ↑I ≤ I₀ →
          ∀ {i x}, x ∈ ioo (I.lower i) (I.upper i) → (I.splitLower i x).elim 0 f + (I.splitUpper i x).elim 0 f = f I) :
    ι →ᵇᵃ[I₀] M := by
  refine' ⟨f, _⟩
  replace hf : ∀ I : box ι, ↑I ≤ I₀ → ∀ s, (∑ J in (split_many I s).boxes, f J) = f I
  · intro I hI s
    induction' s using Finset.induction_on with a s ha ihs
    · simp
      
    rw [split_many_insert, inf_split, ← ihs, bUnion_boxes, sum_bUnion_boxes]
    refine' Finset.sum_congr rfl fun J' hJ' => _
    by_cases' h : a.2 ∈ Ioo (J'.lower a.1) (J'.upper a.1)
    · rw [sum_split_boxes]
      exact hf _ ((WithTop.coe_le_coe.2 <| le_of_mem _ hJ').trans hI) h
      
    · rw [split_of_not_mem_Ioo h, top_boxes, Finset.sum_singleton]
      
    
  intro I hI π hπ
  have Hle : ∀, ∀ J ∈ π, ∀, ↑J ≤ I₀ := fun J hJ => (WithTop.coe_le_coe.2 <| π.le_of_mem hJ).trans hI
  rcases hπ.exists_split_many_le with ⟨s, hs⟩
  rw [← hf _ hI, ← inf_of_le_right hs, inf_split_many, bUnion_boxes, sum_bUnion_boxes]
  exact Finset.sum_congr rfl fun J hJ => (hf _ (Hle _ hJ) _).symm

/-- If `g : M → N` is an additive map and `f` is a box additive map, then `g ∘ f` is a box additive
map. -/
@[simps (config := { fullyApplied := false })]
def map (f : ι →ᵇᵃ[I₀] M) (g : M →+ N) : ι →ᵇᵃ[I₀] N where
  toFun := g ∘ f
  sum_partition_boxes' := fun I hI π hπ => by
    rw [← g.map_sum, f.sum_partition_boxes hI hπ]

/-- If `f` is a box additive function on subboxes of `I` and `π₁`, `π₂` are two prepartitions of
`I` that cover the same part of `I`, then `∑ J in π₁.boxes, f J = ∑ J in π₂.boxes, f J`. -/
theorem sum_boxes_congr [Fintype ι] (f : ι →ᵇᵃ[I₀] M) (hI : ↑I ≤ I₀) {π₁ π₂ : Prepartition I}
    (h : π₁.Union = π₂.Union) : (∑ J in π₁.boxes, f J) = ∑ J in π₂.boxes, f J := by
  rcases exists_split_many_inf_eq_filter_of_finite {π₁, π₂} ((finite_singleton _).insert _) with ⟨s, hs⟩
  simp only [← inf_split_many] at hs
  rcases hs _ (Or.inl rfl), hs _ (Or.inr rfl) with ⟨h₁, h₂⟩
  clear hs
  rw [h] at h₁
  calc (∑ J in π₁.boxes, f J) = ∑ J in π₁.boxes, ∑ J' in (split_many J s).boxes, f J' :=
      Finset.sum_congr rfl fun J hJ =>
        (f.sum_partition_boxes _
            (is_partition_split_many _ _)).symm _ = ∑ J in (π₁.bUnion fun J => split_many J s).boxes, f J :=
      (sum_bUnion_boxes _ _ _).symm _ = ∑ J in (π₂.bUnion fun J => split_many J s).boxes, f J := by
      rw [h₁, h₂]_ = ∑ J in π₂.boxes, ∑ J' in (split_many J s).boxes, f J' :=
      sum_bUnion_boxes _ _ _ _ = ∑ J in π₂.boxes, f J :=
      Finset.sum_congr rfl fun J hJ => f.sum_partition_boxes _ (is_partition_split_many _ _)
  exacts[(WithTop.coe_le_coe.2 <| π₁.le_of_mem hJ).trans hI, (WithTop.coe_le_coe.2 <| π₂.le_of_mem hJ).trans hI]

section ToSmul

variable {E : Type _} [NormedGroup E] [NormedSpace ℝ E]

/-- If `f` is a box-additive map, then so is the map sending `I` to the scalar multiplication
by `f I` as a continuous linear map from `E` to itself. -/
def toSmul (f : ι →ᵇᵃ[I₀] ℝ) : ι →ᵇᵃ[I₀] E →L[ℝ] E :=
  f.map (ContinuousLinearMap.lsmul ℝ ℝ).toLinearMap.toAddMonoidHom

@[simp]
theorem to_smul_apply (f : ι →ᵇᵃ[I₀] ℝ) (I : Box ι) (x : E) : f.toSmul I x = f I • x :=
  rfl

end ToSmul

/-- Given a box `I₀` in `ℝⁿ⁺¹`, `f x : box (fin n) → G` is a family of functions indexed by a real
`x` and for `x ∈ [I₀.lower i, I₀.upper i]`, `f x` is box-additive on subboxes of the `i`-th face of
`I₀`, then `λ J, f (J.upper i) (J.face i) - f (J.lower i) (J.face i)` is box-additive on subboxes of
`I₀`. -/
@[simps]
def upperSubLower.{u} {G : Type u} [AddCommGroupₓ G] (I₀ : Box (Finₓ (n + 1))) (i : Finₓ (n + 1))
    (f : ℝ → Box (Finₓ n) → G) (fb : icc (I₀.lower i) (I₀.upper i) → Finₓ n →ᵇᵃ[I₀.face i] G)
    (hf : ∀ (x) (hx : x ∈ icc (I₀.lower i) (I₀.upper i)) (J), f x J = fb ⟨x, hx⟩ J) : Finₓ (n + 1) →ᵇᵃ[I₀] G :=
  ofMapSplitAdd (fun J : Box (Finₓ (n + 1)) => f (J.upper i) (J.face i) - f (J.lower i) (J.face i)) I₀
    (by
      intro J hJ j
      rw [WithTop.coe_le_coe] at hJ
      refine' i.succ_above_cases _ _ j
      · intro x hx
        simp only [← box.split_lower_def hx, ← box.split_upper_def hx, ← update_same, WithBot.some_eq_coe, ←
          Option.elimₓ, ← box.face, ← (· ∘ ·), ← update_noteq (Finₓ.succ_above_ne _ _)]
        abel
        
      · clear j
        intro j x hx
        have : (J.face i : WithTop (box (Finₓ n))) ≤ I₀.face i := WithTop.coe_le_coe.2 (face_mono hJ i)
        rw [le_iff_Icc, @box.Icc_eq_pi _ I₀] at hJ
        rw [hf _ (hJ J.upper_mem_Icc _ trivialₓ), hf _ (hJ J.lower_mem_Icc _ trivialₓ), ← (fb _).map_split_add this j x,
          ← (fb _).map_split_add this j x]
        have hx' : x ∈ Ioo ((J.face i).lower j) ((J.face i).upper j) := hx
        simp only [← box.split_lower_def hx, ← box.split_upper_def hx, ← box.split_lower_def hx', ←
          box.split_upper_def hx', WithBot.some_eq_coe, ← Option.elimₓ, ← box.face_mk, ←
          update_noteq (Finₓ.succ_above_ne _ _).symm, ← sub_add_sub_comm, ←
          update_comp_eq_of_injective _ i.succ_above.injective j x, hf]
        simp only [← box.face]
        )

end BoxAdditiveMap

end BoxIntegral

