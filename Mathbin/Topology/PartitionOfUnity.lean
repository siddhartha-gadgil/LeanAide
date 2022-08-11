/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathbin.Algebra.BigOperators.Finprod
import Mathbin.SetTheory.Ordinal.Basic
import Mathbin.Topology.ContinuousFunction.Algebra
import Mathbin.Topology.Paracompact
import Mathbin.Topology.ShrinkingLemma
import Mathbin.Topology.UrysohnsLemma

/-!
# Continuous partition of unity

In this file we define `partition_of_unity (ι X : Type*) [topological_space X] (s : set X := univ)`
to be a continuous partition of unity on `s` indexed by `ι`. More precisely, `f : partition_of_unity
ι X s` is a collection of continuous functions `f i : C(X, ℝ)`, `i : ι`, such that

* the supports of `f i` form a locally finite family of sets;
* each `f i` is nonnegative;
* `∑ᶠ i, f i x = 1` for all `x ∈ s`;
* `∑ᶠ i, f i x ≤ 1` for all `x : X`.

In the case `s = univ` the last assumption follows from the previous one but it is convenient to
have this assumption in the case `s ≠ univ`.

We also define a bump function covering,
`bump_covering (ι X : Type*) [topological_space X] (s : set X := univ)`, to be a collection of
functions `f i : C(X, ℝ)`, `i : ι`, such that

* the supports of `f i` form a locally finite family of sets;
* each `f i` is nonnegative;
* for each `x ∈ s` there exists `i : ι` such that `f i y = 1` in a neighborhood of `x`.

The term is motivated by the smooth case.

If `f` is a bump function covering indexed by a linearly ordered type, then
`g i x = f i x * ∏ᶠ j < i, (1 - f j x)` is a partition of unity, see
`bump_covering.to_partition_of_unity`. Note that only finitely many terms `1 - f j x` are not equal
to one, so this product is well-defined.

Note that `g i x = ∏ᶠ j ≤ i, (1 - f j x) - ∏ᶠ j < i, (1 - f j x)`, so most terms in the sum
`∑ᶠ i, g i x` cancel, and we get `∑ᶠ i, g i x = 1 - ∏ᶠ i, (1 - f i x)`, and the latter product
equals zero because one of `f i x` is equal to one.

We say that a partition of unity or a bump function covering `f` is *subordinate* to a family of
sets `U i`, `i : ι`, if the closure of the support of each `f i` is included in `U i`. We use
Urysohn's Lemma to prove that a locally finite open covering of a normal topological space admits a
subordinate bump function covering (hence, a subordinate partition of unity), see
`bump_covering.exists_is_subordinate_of_locally_finite`. If `X` is a paracompact space, then any
open covering admits a locally finite refinement, hence it admits a subordinate bump function
covering and a subordinate partition of unity, see `bump_covering.exists_is_subordinate`.

We also provide two slightly more general versions of these lemmas,
`bump_covering.exists_is_subordinate_of_locally_finite_of_prop` and
`bump_covering.exists_is_subordinate_of_prop`, to be used later in the construction of a smooth
partition of unity.

## Implementation notes

Most (if not all) books only define a partition of unity of the whole space. However, quite a few
proofs only deal with `f i` such that `tsupport (f i)` meets a specific closed subset, and
it is easier to formalize these proofs if we don't have other functions right away.

We use `well_ordering_rel j i` instead of `j < i` in the definition of
`bump_covering.to_partition_of_unity` to avoid a `[linear_order ι]` assumption. While
`well_ordering_rel j i` is a well order, not only a strict linear order, we never use this property.

## Tags

partition of unity, bump function, Urysohn's lemma, normal space, paracompact space
-/


universe u v

open Function Set Filter

open BigOperators TopologicalSpace Classical

noncomputable section

/-- A continuous partition of unity on a set `s : set X` is a collection of continuous functions
`f i` such that

* the supports of `f i` form a locally finite family of sets, i.e., for every point `x : X` there
  exists a neighborhood `U ∋ x` such that all but finitely many functions `f i` are zero on `U`;
* the functions `f i` are nonnegative;
* the sum `∑ᶠ i, f i x` is equal to one for every `x ∈ s` and is less than or equal to one
  otherwise.

If `X` is a normal paracompact space, then `partition_of_unity.exists_is_subordinate` guarantees
that for every open covering `U : set (set X)` of `s` there exists a partition of unity that is
subordinate to `U`.
-/
structure PartitionOfUnity (ι X : Type _) [TopologicalSpace X] (s : Set X := Univ) where
  toFun : ι → C(X, ℝ)
  locally_finite' : LocallyFinite fun i => Support (to_fun i)
  nonneg' : 0 ≤ to_fun
  sum_eq_one' : ∀, ∀ x ∈ s, ∀, (∑ᶠ i, to_fun i x) = 1
  sum_le_one' : ∀ x, (∑ᶠ i, to_fun i x) ≤ 1

/-- A `bump_covering ι X s` is an indexed family of functions `f i`, `i : ι`, such that

* the supports of `f i` form a locally finite family of sets, i.e., for every point `x : X` there
  exists a neighborhood `U ∋ x` such that all but finitely many functions `f i` are zero on `U`;
* for all `i`, `x` we have `0 ≤ f i x ≤ 1`;
* each point `x ∈ s` belongs to the interior of `{x | f i x = 1}` for some `i`.

One of the main use cases for a `bump_covering` is to define a `partition_of_unity`, see
`bump_covering.to_partition_of_unity`, but some proofs can directly use a `bump_covering` instead of
a `partition_of_unity`.

If `X` is a normal paracompact space, then `bump_covering.exists_is_subordinate` guarantees that for
every open covering `U : set (set X)` of `s` there exists a `bump_covering` of `s` that is
subordinate to `U`.
-/
structure BumpCovering (ι X : Type _) [TopologicalSpace X] (s : Set X := Univ) where
  toFun : ι → C(X, ℝ)
  locally_finite' : LocallyFinite fun i => Support (to_fun i)
  nonneg' : 0 ≤ to_fun
  le_one' : to_fun ≤ 1
  eventually_eq_one' : ∀, ∀ x ∈ s, ∀, ∃ i, to_fun i =ᶠ[𝓝 x] 1

variable {ι : Type u} {X : Type v} [TopologicalSpace X]

namespace PartitionOfUnity

variable {s : Set X} (f : PartitionOfUnity ι X s)

instance : CoeFun (PartitionOfUnity ι X s) fun _ => ι → C(X, ℝ) :=
  ⟨toFun⟩

protected theorem locally_finite : LocallyFinite fun i => Support (f i) :=
  f.locally_finite'

theorem nonneg (i : ι) (x : X) : 0 ≤ f i x :=
  f.nonneg' i x

theorem sum_eq_one {x : X} (hx : x ∈ s) : (∑ᶠ i, f i x) = 1 :=
  f.sum_eq_one' x hx

theorem sum_le_one (x : X) : (∑ᶠ i, f i x) ≤ 1 :=
  f.sum_le_one' x

theorem sum_nonneg (x : X) : 0 ≤ ∑ᶠ i, f i x :=
  finsum_nonneg fun i => f.Nonneg i x

theorem le_one (i : ι) (x : X) : f i x ≤ 1 :=
  (single_le_finsum i (f.LocallyFinite.point_finite x) fun j => f.Nonneg j x).trans (f.sum_le_one x)

/-- A partition of unity `f i` is subordinate to a family of sets `U i` indexed by the same type if
for each `i` the closure of the support of `f i` is a subset of `U i`. -/
def IsSubordinate (U : ι → Set X) : Prop :=
  ∀ i, Tsupport (f i) ⊆ U i

variable {f}

theorem exists_finset_nhd_support_subset {U : ι → Set X} (hso : f.IsSubordinate U) (ho : ∀ i, IsOpen (U i)) (x : X) :
    ∃ (is : Finset ι)(n : Set X)(hn₁ : n ∈ 𝓝 x)(hn₂ : n ⊆ ⋂ i ∈ is, U i),
      ∀, ∀ z ∈ n, ∀, (Support fun i => f i z) ⊆ is :=
  f.LocallyFinite.exists_finset_nhd_support_subset hso ho x

end PartitionOfUnity

namespace BumpCovering

variable {s : Set X} (f : BumpCovering ι X s)

instance : CoeFun (BumpCovering ι X s) fun _ => ι → C(X, ℝ) :=
  ⟨toFun⟩

protected theorem locally_finite : LocallyFinite fun i => Support (f i) :=
  f.locally_finite'

protected theorem point_finite (x : X) : { i | f i x ≠ 0 }.Finite :=
  f.LocallyFinite.point_finite x

theorem nonneg (i : ι) (x : X) : 0 ≤ f i x :=
  f.nonneg' i x

theorem le_one (i : ι) (x : X) : f i x ≤ 1 :=
  f.le_one' i x

/-- A `bump_covering` that consists of a single function, uniformly equal to one, defined as an
example for `inhabited` instance. -/
protected def single (i : ι) (s : Set X) : BumpCovering ι X s where
  toFun := Pi.single i 1
  locally_finite' := fun x => by
    refine' ⟨univ, univ_mem, (finite_singleton i).Subset _⟩
    rintro j ⟨x, hx, -⟩
    contrapose! hx
    rw [mem_singleton_iff] at hx
    simp [← hx]
  nonneg' := le_update_iff.2 ⟨fun x => zero_le_one, fun _ _ => le_rfl⟩
  le_one' := update_le_iff.2 ⟨le_rfl, fun _ _ _ => zero_le_one⟩
  eventually_eq_one' := fun x _ =>
    ⟨i, by
      simp ⟩

@[simp]
theorem coe_single (i : ι) (s : Set X) : ⇑(BumpCovering.single i s) = Pi.single i 1 :=
  rfl

instance [Inhabited ι] : Inhabited (BumpCovering ι X s) :=
  ⟨BumpCovering.single default s⟩

/-- A collection of bump functions `f i` is subordinate to a family of sets `U i` indexed by the
same type if for each `i` the closure of the support of `f i` is a subset of `U i`. -/
def IsSubordinate (f : BumpCovering ι X s) (U : ι → Set X) : Prop :=
  ∀ i, Tsupport (f i) ⊆ U i

theorem IsSubordinate.mono {f : BumpCovering ι X s} {U V : ι → Set X} (hU : f.IsSubordinate U) (hV : ∀ i, U i ⊆ V i) :
    f.IsSubordinate V := fun i => Subset.trans (hU i) (hV i)

/-- If `X` is a normal topological space and `U i`, `i : ι`, is a locally finite open covering of a
closed set `s`, then there exists a `bump_covering ι X s` that is subordinate to `U`. If `X` is a
paracompact space, then the assumption `hf : locally_finite U` can be omitted, see
`bump_covering.exists_is_subordinate`. This version assumes that `p : (X → ℝ) → Prop` is a predicate
that satisfies Urysohn's lemma, and provides a `bump_covering` such that each function of the
covering satisfies `p`. -/
theorem exists_is_subordinate_of_locally_finite_of_prop [NormalSpace X] (p : (X → ℝ) → Prop)
    (h01 :
      ∀ s t,
        IsClosed s →
          IsClosed t → Disjoint s t → ∃ f : C(X, ℝ), p f ∧ EqOn f 0 s ∧ EqOn f 1 t ∧ ∀ x, f x ∈ Icc (0 : ℝ) 1)
    (hs : IsClosed s) (U : ι → Set X) (ho : ∀ i, IsOpen (U i)) (hf : LocallyFinite U) (hU : s ⊆ ⋃ i, U i) :
    ∃ f : BumpCovering ι X s, (∀ i, p (f i)) ∧ f.IsSubordinate U := by
  rcases exists_subset_Union_closure_subset hs ho (fun x _ => hf.point_finite x) hU with ⟨V, hsV, hVo, hVU⟩
  have hVU' : ∀ i, V i ⊆ U i := fun i => subset.trans subset_closure (hVU i)
  rcases exists_subset_Union_closure_subset hs hVo (fun x _ => (hf.subset hVU').point_finite x) hsV with
    ⟨W, hsW, hWo, hWV⟩
  choose f hfp hf0 hf1 hf01 using fun i =>
    h01 _ _ (is_closed_compl_iff.2 <| hVo i) is_closed_closure (disjoint_right.2 fun x hx => not_not.2 (hWV i hx))
  have hsupp : ∀ i, support (f i) ⊆ V i := fun i => support_subset_iff'.2 (hf0 i)
  refine'
    ⟨⟨f, hf.subset fun i => subset.trans (hsupp i) (hVU' i), fun i x => (hf01 i x).1, fun i x => (hf01 i x).2,
        fun x hx => _⟩,
      hfp, fun i => subset.trans (closure_mono (hsupp i)) (hVU i)⟩
  rcases mem_Union.1 (hsW hx) with ⟨i, hi⟩
  exact ⟨i, ((hf1 i).mono subset_closure).eventually_eq_of_mem ((hWo i).mem_nhds hi)⟩

/-- If `X` is a normal topological space and `U i`, `i : ι`, is a locally finite open covering of a
closed set `s`, then there exists a `bump_covering ι X s` that is subordinate to `U`. If `X` is a
paracompact space, then the assumption `hf : locally_finite U` can be omitted, see
`bump_covering.exists_is_subordinate`. -/
theorem exists_is_subordinate_of_locally_finite [NormalSpace X] (hs : IsClosed s) (U : ι → Set X)
    (ho : ∀ i, IsOpen (U i)) (hf : LocallyFinite U) (hU : s ⊆ ⋃ i, U i) : ∃ f : BumpCovering ι X s, f.IsSubordinate U :=
  let ⟨f, _, hfU⟩ :=
    exists_is_subordinate_of_locally_finite_of_prop (fun _ => True)
      (fun s t hs ht hd => (exists_continuous_zero_one_of_closed hs ht hd).imp fun f hf => ⟨trivialₓ, hf⟩) hs U ho hf hU
  ⟨f, hfU⟩

/-- If `X` is a paracompact normal topological space and `U` is an open covering of a closed set
`s`, then there exists a `bump_covering ι X s` that is subordinate to `U`. This version assumes that
`p : (X → ℝ) → Prop` is a predicate that satisfies Urysohn's lemma, and provides a
`bump_covering` such that each function of the covering satisfies `p`. -/
theorem exists_is_subordinate_of_prop [NormalSpace X] [ParacompactSpace X] (p : (X → ℝ) → Prop)
    (h01 :
      ∀ s t,
        IsClosed s →
          IsClosed t → Disjoint s t → ∃ f : C(X, ℝ), p f ∧ EqOn f 0 s ∧ EqOn f 1 t ∧ ∀ x, f x ∈ Icc (0 : ℝ) 1)
    (hs : IsClosed s) (U : ι → Set X) (ho : ∀ i, IsOpen (U i)) (hU : s ⊆ ⋃ i, U i) :
    ∃ f : BumpCovering ι X s, (∀ i, p (f i)) ∧ f.IsSubordinate U := by
  rcases precise_refinement_set hs _ ho hU with ⟨V, hVo, hsV, hVf, hVU⟩
  rcases exists_is_subordinate_of_locally_finite_of_prop p h01 hs V hVo hVf hsV with ⟨f, hfp, hf⟩
  exact ⟨f, hfp, hf.mono hVU⟩

/-- If `X` is a paracompact normal topological space and `U` is an open covering of a closed set
`s`, then there exists a `bump_covering ι X s` that is subordinate to `U`. -/
theorem exists_is_subordinate [NormalSpace X] [ParacompactSpace X] (hs : IsClosed s) (U : ι → Set X)
    (ho : ∀ i, IsOpen (U i)) (hU : s ⊆ ⋃ i, U i) : ∃ f : BumpCovering ι X s, f.IsSubordinate U := by
  rcases precise_refinement_set hs _ ho hU with ⟨V, hVo, hsV, hVf, hVU⟩
  rcases exists_is_subordinate_of_locally_finite hs V hVo hVf hsV with ⟨f, hf⟩
  exact ⟨f, hf.mono hVU⟩

/-- Index of a bump function such that `fs i =ᶠ[𝓝 x] 1`. -/
def ind (x : X) (hx : x ∈ s) : ι :=
  (f.eventually_eq_one' x hx).some

theorem eventually_eq_one (x : X) (hx : x ∈ s) : f (f.ind x hx) =ᶠ[𝓝 x] 1 :=
  (f.eventually_eq_one' x hx).some_spec

theorem ind_apply (x : X) (hx : x ∈ s) : f (f.ind x hx) x = 1 :=
  (f.eventually_eq_one x hx).eq_of_nhds

/-- Partition of unity defined by a `bump_covering`. We use this auxiliary definition to prove some
properties of the new family of functions before bundling it into a `partition_of_unity`. Do not use
this definition, use `bump_function.to_partition_of_unity` instead.

The partition of unity is given by the formula `g i x = f i x * ∏ᶠ j < i, (1 - f j x)`. In other
words, `g i x = ∏ᶠ j < i, (1 - f j x) - ∏ᶠ j ≤ i, (1 - f j x)`, so
`∑ᶠ i, g i x = 1 - ∏ᶠ j, (1 - f j x)`. If `x ∈ s`, then one of `f j x` equals one, hence the product
of `1 - f j x` vanishes, and `∑ᶠ i, g i x = 1`.

In order to avoid an assumption `linear_order ι`, we use `well_ordering_rel` instead of `(<)`. -/
def toPouFun (i : ι) (x : X) : ℝ :=
  f i x * ∏ᶠ (j) (hj : WellOrderingRel j i), 1 - f j x

theorem to_pou_fun_zero_of_zero {i : ι} {x : X} (h : f i x = 0) : f.toPouFun i x = 0 := by
  rw [to_pou_fun, h, zero_mul]

theorem support_to_pou_fun_subset (i : ι) : Support (f.toPouFun i) ⊆ Support (f i) := fun x =>
  mt <| f.to_pou_fun_zero_of_zero

theorem to_pou_fun_eq_mul_prod (i : ι) (x : X) (t : Finset ι) (ht : ∀ j, WellOrderingRel j i → f j x ≠ 0 → j ∈ t) :
    f.toPouFun i x = f i x * ∏ j in t.filter fun j => WellOrderingRel j i, 1 - f j x := by
  refine' congr_arg _ (finprod_cond_eq_prod_of_cond_iff _ fun j hj => _)
  rw [Ne.def, sub_eq_self] at hj
  rw [Finset.mem_filter, Iff.comm, and_iff_right_iff_imp]
  exact flip (ht j) hj

theorem sum_to_pou_fun_eq (x : X) : (∑ᶠ i, f.toPouFun i x) = 1 - ∏ᶠ i, 1 - f i x := by
  set s := (f.point_finite x).toFinset
  have hs : (s : Set ι) = { i | f i x ≠ 0 } := finite.coe_to_finset _
  have A : (support fun i => to_pou_fun f i x) ⊆ s := by
    rw [hs]
    exact fun i hi => f.support_to_pou_fun_subset i hi
  have B : (mul_support fun i => 1 - f i x) ⊆ s := by
    rw [hs, mul_support_one_sub]
    exact fun i => id
  let this : LinearOrderₓ ι := linearOrderOfSTO' WellOrderingRel
  rw [finsum_eq_sum_of_support_subset _ A, finprod_eq_prod_of_mul_support_subset _ B, Finset.prod_one_sub_ordered,
    sub_sub_cancel]
  refine' Finset.sum_congr rfl fun i hi => _
  convert f.to_pou_fun_eq_mul_prod _ _ _ fun j hji hj => _
  rwa [finite.mem_to_finset]

theorem exists_finset_to_pou_fun_eventually_eq (i : ι) (x : X) :
    ∃ t : Finset ι, f.toPouFun i =ᶠ[𝓝 x] f i * ∏ j in t.filter fun j => WellOrderingRel j i, 1 - f j := by
  rcases f.locally_finite x with ⟨U, hU, hf⟩
  use hf.to_finset
  filter_upwards [hU] with y hyU
  simp only [← Pi.mul_apply, ← Finset.prod_apply]
  apply to_pou_fun_eq_mul_prod
  intro j hji hj
  exact hf.mem_to_finset.2 ⟨y, ⟨hj, hyU⟩⟩

theorem continuous_to_pou_fun (i : ι) : Continuous (f.toPouFun i) := by
  refine' (f i).Continuous.mul <| continuous_finprod_cond (fun j _ => continuous_const.sub (f j).Continuous) _
  simp only [← mul_support_one_sub]
  exact f.locally_finite

/-- The partition of unity defined by a `bump_covering`.

The partition of unity is given by the formula `g i x = f i x * ∏ᶠ j < i, (1 - f j x)`. In other
words, `g i x = ∏ᶠ j < i, (1 - f j x) - ∏ᶠ j ≤ i, (1 - f j x)`, so
`∑ᶠ i, g i x = 1 - ∏ᶠ j, (1 - f j x)`. If `x ∈ s`, then one of `f j x` equals one, hence the product
of `1 - f j x` vanishes, and `∑ᶠ i, g i x = 1`.

In order to avoid an assumption `linear_order ι`, we use `well_ordering_rel` instead of `(<)`. -/
def toPartitionOfUnity : PartitionOfUnity ι X s where
  toFun := fun i => ⟨f.toPouFun i, f.continuous_to_pou_fun i⟩
  locally_finite' := f.LocallyFinite.Subset f.support_to_pou_fun_subset
  nonneg' := fun i x => mul_nonneg (f.Nonneg i x) (finprod_cond_nonneg fun j hj => sub_nonneg.2 <| f.le_one j x)
  sum_eq_one' := fun x hx => by
    simp only [← ContinuousMap.coe_mk, ← sum_to_pou_fun_eq, ← sub_eq_self]
    apply finprod_eq_zero (fun i => 1 - f i x) (f.ind x hx)
    · simp only [← f.ind_apply x hx, ← sub_self]
      
    · rw [mul_support_one_sub]
      exact f.point_finite x
      
  sum_le_one' := fun x => by
    simp only [← ContinuousMap.coe_mk, ← sum_to_pou_fun_eq, ← sub_le_self_iff]
    exact finprod_nonneg fun i => sub_nonneg.2 <| f.le_one i x

theorem to_partition_of_unity_apply (i : ι) (x : X) :
    f.toPartitionOfUnity i x = f i x * ∏ᶠ (j) (hj : WellOrderingRel j i), 1 - f j x :=
  rfl

theorem to_partition_of_unity_eq_mul_prod (i : ι) (x : X) (t : Finset ι)
    (ht : ∀ j, WellOrderingRel j i → f j x ≠ 0 → j ∈ t) :
    f.toPartitionOfUnity i x = f i x * ∏ j in t.filter fun j => WellOrderingRel j i, 1 - f j x :=
  f.to_pou_fun_eq_mul_prod i x t ht

theorem exists_finset_to_partition_of_unity_eventually_eq (i : ι) (x : X) :
    ∃ t : Finset ι, f.toPartitionOfUnity i =ᶠ[𝓝 x] f i * ∏ j in t.filter fun j => WellOrderingRel j i, 1 - f j :=
  f.exists_finset_to_pou_fun_eventually_eq i x

theorem to_partition_of_unity_zero_of_zero {i : ι} {x : X} (h : f i x = 0) : f.toPartitionOfUnity i x = 0 :=
  f.to_pou_fun_zero_of_zero h

theorem support_to_partition_of_unity_subset (i : ι) : Support (f.toPartitionOfUnity i) ⊆ Support (f i) :=
  f.support_to_pou_fun_subset i

theorem sum_to_partition_of_unity_eq (x : X) : (∑ᶠ i, f.toPartitionOfUnity i x) = 1 - ∏ᶠ i, 1 - f i x :=
  f.sum_to_pou_fun_eq x

theorem IsSubordinate.to_partition_of_unity {f : BumpCovering ι X s} {U : ι → Set X} (h : f.IsSubordinate U) :
    f.toPartitionOfUnity.IsSubordinate U := fun i =>
  Subset.trans (closure_mono <| f.support_to_partition_of_unity_subset i) (h i)

end BumpCovering

namespace PartitionOfUnity

variable {s : Set X}

instance [Inhabited ι] : Inhabited (PartitionOfUnity ι X s) :=
  ⟨BumpCovering.toPartitionOfUnity default⟩

/-- If `X` is a normal topological space and `U` is a locally finite open covering of a closed set
`s`, then there exists a `partition_of_unity ι X s` that is subordinate to `U`. If `X` is a
paracompact space, then the assumption `hf : locally_finite U` can be omitted, see
`bump_covering.exists_is_subordinate`. -/
theorem exists_is_subordinate_of_locally_finite [NormalSpace X] (hs : IsClosed s) (U : ι → Set X)
    (ho : ∀ i, IsOpen (U i)) (hf : LocallyFinite U) (hU : s ⊆ ⋃ i, U i) :
    ∃ f : PartitionOfUnity ι X s, f.IsSubordinate U :=
  let ⟨f, hf⟩ := BumpCovering.exists_is_subordinate_of_locally_finite hs U ho hf hU
  ⟨f.toPartitionOfUnity, hf.toPartitionOfUnity⟩

/-- If `X` is a paracompact normal topological space and `U` is an open covering of a closed set
`s`, then there exists a `partition_of_unity ι X s` that is subordinate to `U`. -/
theorem exists_is_subordinate [NormalSpace X] [ParacompactSpace X] (hs : IsClosed s) (U : ι → Set X)
    (ho : ∀ i, IsOpen (U i)) (hU : s ⊆ ⋃ i, U i) : ∃ f : PartitionOfUnity ι X s, f.IsSubordinate U :=
  let ⟨f, hf⟩ := BumpCovering.exists_is_subordinate hs U ho hU
  ⟨f.toPartitionOfUnity, hf.toPartitionOfUnity⟩

end PartitionOfUnity

