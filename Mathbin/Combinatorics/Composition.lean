/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathbin.Data.Finset.Sort
import Mathbin.Algebra.BigOperators.Order
import Mathbin.Algebra.BigOperators.Fin

/-!
# Compositions

A composition of a natural number `n` is a decomposition `n = i₀ + ... + i_{k-1}` of `n` into a sum
of positive integers. Combinatorially, it corresponds to a decomposition of `{0, ..., n-1}` into
non-empty blocks of consecutive integers, where the `iⱼ` are the lengths of the blocks.
This notion is closely related to that of a partition of `n`, but in a composition of `n` the
order of the `iⱼ`s matters.

We implement two different structures covering these two viewpoints on compositions. The first
one, made of a list of positive integers summing to `n`, is the main one and is called
`composition n`. The second one is useful for combinatorial arguments (for instance to show that
the number of compositions of `n` is `2^(n-1)`). It is given by a subset of `{0, ..., n}`
containing `0` and `n`, where the elements of the subset (other than `n`) correspond to the leftmost
points of each block. The main API is built on `composition n`, and we provide an equivalence
between the two types.

## Main functions

* `c : composition n` is a structure, made of a list of integers which are all positive and
  add up to `n`.
* `composition_card` states that the cardinality of `composition n` is exactly
  `2^(n-1)`, which is proved by constructing an equiv with `composition_as_set n` (see below), which
  is itself in bijection with the subsets of `fin (n-1)` (this holds even for `n = 0`, where `-` is
  nat subtraction).

Let `c : composition n` be a composition of `n`. Then
* `c.blocks` is the list of blocks in `c`.
* `c.length` is the number of blocks in the composition.
* `c.blocks_fun : fin c.length → ℕ` is the realization of `c.blocks` as a function on
  `fin c.length`. This is the main object when using compositions to understand the composition of
    analytic functions.
* `c.size_up_to : ℕ → ℕ` is the sum of the size of the blocks up to `i`.;
* `c.embedding i : fin (c.blocks_fun i) → fin n` is the increasing embedding of the `i`-th block in
  `fin n`;
* `c.index j`, for `j : fin n`, is the index of the block containing `j`.

* `composition.ones n` is the composition of `n` made of ones, i.e., `[1, ..., 1]`.
* `composition.single n (hn : 0 < n)` is the composition of `n` made of a single block of size `n`.

Compositions can also be used to split lists. Let `l` be a list of length `n` and `c` a composition
of `n`.
* `l.split_wrt_composition c` is a list of lists, made of the slices of `l` corresponding to the
  blocks of `c`.
* `join_split_wrt_composition` states that splitting a list and then joining it gives back the
  original list.
* `split_wrt_composition_join` states that joining a list of lists, and then splitting it back
  according to the right composition, gives back the original list of lists.

We turn to the second viewpoint on compositions, that we realize as a finset of `fin (n+1)`.
`c : composition_as_set n` is a structure made of a finset of `fin (n+1)` called `c.boundaries`
and proofs that it contains `0` and `n`. (Taking a finset of `fin n` containing `0` would not
make sense in the edge case `n = 0`, while the previous description works in all cases).
The elements of this set (other than `n`) correspond to leftmost points of blocks.
Thus, there is an equiv between `composition n` and `composition_as_set n`. We
only construct basic API on `composition_as_set` (notably `c.length` and `c.blocks`) to be able
to construct this equiv, called `composition_equiv n`. Since there is a straightforward equiv
between `composition_as_set n` and finsets of `{1, ..., n-1}` (obtained by removing `0` and `n`
from a `composition_as_set` and called `composition_as_set_equiv n`), we deduce that
`composition_as_set n` and `composition n` are both fintypes of cardinality `2^(n - 1)`
(see `composition_as_set_card` and `composition_card`).

## Implementation details

The main motivation for this structure and its API is in the construction of the composition of
formal multilinear series, and the proof that the composition of analytic functions is analytic.

The representation of a composition as a list is very handy as lists are very flexible and already
have a well-developed API.

## Tags

Composition, partition

## References

<https://en.wikipedia.org/wiki/Composition_(combinatorics)>
-/


open List

open BigOperators

variable {n : ℕ}

/-- A composition of `n` is a list of positive integers summing to `n`. -/
@[ext]
structure Composition (n : ℕ) where
  blocks : List ℕ
  blocks_pos : ∀ {i}, i ∈ blocks → 0 < i
  blocks_sum : blocks.Sum = n

/-- Combinatorial viewpoint on a composition of `n`, by seeing it as non-empty blocks of
consecutive integers in `{0, ..., n-1}`. We register every block by its left end-point, yielding
a finset containing `0`. As this does not make sense for `n = 0`, we add `n` to this finset, and
get a finset of `{0, ..., n}` containing `0` and `n`. This is the data in the structure
`composition_as_set n`. -/
@[ext]
structure CompositionAsSet (n : ℕ) where
  boundaries : Finset (Finₓ n.succ)
  zero_mem : (0 : Finₓ n.succ) ∈ boundaries
  last_mem : Finₓ.last n ∈ boundaries

instance {n : ℕ} : Inhabited (CompositionAsSet n) :=
  ⟨⟨Finset.univ, Finset.mem_univ _, Finset.mem_univ _⟩⟩

/-!
### Compositions

A composition of an integer `n` is a decomposition `n = i₀ + ... + i_{k-1}` of `n` into a sum of
positive integers.
-/


namespace Composition

variable (c : Composition n)

instance (n : ℕ) : HasToString (Composition n) :=
  ⟨fun c => toString c.blocks⟩

/-- The length of a composition, i.e., the number of blocks in the composition. -/
@[reducible]
def length : ℕ :=
  c.blocks.length

theorem blocks_length : c.blocks.length = c.length :=
  rfl

/-- The blocks of a composition, seen as a function on `fin c.length`. When composing analytic
functions using compositions, this is the main player. -/
def blocksFun : Finₓ c.length → ℕ := fun i => nthLe c.blocks i i.2

theorem of_fn_blocks_fun : ofFnₓ c.blocksFun = c.blocks :=
  of_fn_nth_le _

theorem sum_blocks_fun : (∑ i, c.blocksFun i) = n := by
  conv_rhs => rw [← c.blocks_sum, ← of_fn_blocks_fun, sum_of_fn]

theorem blocks_fun_mem_blocks (i : Finₓ c.length) : c.blocksFun i ∈ c.blocks :=
  nth_le_mem _ _ _

@[simp]
theorem one_le_blocks {i : ℕ} (h : i ∈ c.blocks) : 1 ≤ i :=
  c.blocks_pos h

@[simp]
theorem one_le_blocks' {i : ℕ} (h : i < c.length) : 1 ≤ nthLe c.blocks i h :=
  c.one_le_blocks (nth_le_mem (blocks c) i h)

@[simp]
theorem blocks_pos' (i : ℕ) (h : i < c.length) : 0 < nthLe c.blocks i h :=
  c.one_le_blocks' h

theorem one_le_blocks_fun (i : Finₓ c.length) : 1 ≤ c.blocksFun i :=
  c.one_le_blocks (c.blocks_fun_mem_blocks i)

theorem length_le : c.length ≤ n := by
  conv_rhs => rw [← c.blocks_sum]
  exact length_le_sum_of_one_le _ fun i hi => c.one_le_blocks hi

theorem length_pos_of_pos (h : 0 < n) : 0 < c.length := by
  apply length_pos_of_sum_pos
  convert h
  exact c.blocks_sum

/-- The sum of the sizes of the blocks in a composition up to `i`. -/
def sizeUpTo (i : ℕ) : ℕ :=
  (c.blocks.take i).Sum

@[simp]
theorem size_up_to_zero : c.sizeUpTo 0 = 0 := by
  simp [← size_up_to]

theorem size_up_to_of_length_le (i : ℕ) (h : c.length ≤ i) : c.sizeUpTo i = n := by
  dsimp' [← size_up_to]
  convert c.blocks_sum
  exact take_all_of_le h

@[simp]
theorem size_up_to_length : c.sizeUpTo c.length = n :=
  c.size_up_to_of_length_le c.length le_rfl

theorem size_up_to_le (i : ℕ) : c.sizeUpTo i ≤ n := by
  conv_rhs => rw [← c.blocks_sum, ← sum_take_add_sum_drop _ i]
  exact Nat.le_add_rightₓ _ _

theorem size_up_to_succ {i : ℕ} (h : i < c.length) : c.sizeUpTo (i + 1) = c.sizeUpTo i + c.blocks.nthLe i h := by
  simp only [← size_up_to]
  rw [sum_take_succ _ _ h]

theorem size_up_to_succ' (i : Finₓ c.length) : c.sizeUpTo ((i : ℕ) + 1) = c.sizeUpTo i + c.blocksFun i :=
  c.size_up_to_succ i.2

theorem size_up_to_strict_mono {i : ℕ} (h : i < c.length) : c.sizeUpTo i < c.sizeUpTo (i + 1) := by
  rw [c.size_up_to_succ h]
  simp

theorem monotone_size_up_to : Monotone c.sizeUpTo :=
  monotone_sum_take _

/-- The `i`-th boundary of a composition, i.e., the leftmost point of the `i`-th block. We include
a virtual point at the right of the last block, to make for a nice equiv with
`composition_as_set n`. -/
def boundary : Finₓ (c.length + 1) ↪o Finₓ (n + 1) :=
  (OrderEmbedding.ofStrictMono fun i => ⟨c.sizeUpTo i, Nat.lt_succ_of_leₓ (c.size_up_to_le i)⟩) <|
    Finₓ.strict_mono_iff_lt_succ.2 fun ⟨i, hi⟩ => c.size_up_to_strict_mono hi

@[simp]
theorem boundary_zero : c.boundary 0 = 0 := by
  simp [← boundary, ← Finₓ.ext_iff]

@[simp]
theorem boundary_last : c.boundary (Finₓ.last c.length) = Finₓ.last n := by
  simp [← boundary, ← Finₓ.ext_iff]

/-- The boundaries of a composition, i.e., the leftmost point of all the blocks. We include
a virtual point at the right of the last block, to make for a nice equiv with
`composition_as_set n`. -/
def boundaries : Finset (Finₓ (n + 1)) :=
  Finset.univ.map c.boundary.toEmbedding

theorem card_boundaries_eq_succ_length : c.boundaries.card = c.length + 1 := by
  simp [← boundaries]

/-- To `c : composition n`, one can associate a `composition_as_set n` by registering the leftmost
point of each block, and adding a virtual point at the right of the last block. -/
def toCompositionAsSet : CompositionAsSet n where
  boundaries := c.boundaries
  zero_mem := by
    simp only [← boundaries, ← Finset.mem_univ, ← exists_prop_of_true, ← Finset.mem_map]
    exact ⟨0, rfl⟩
  last_mem := by
    simp only [← boundaries, ← Finset.mem_univ, ← exists_prop_of_true, ← Finset.mem_map]
    exact ⟨Finₓ.last c.length, c.boundary_last⟩

/-- The canonical increasing bijection between `fin (c.length + 1)` and `c.boundaries` is
exactly `c.boundary`. -/
theorem order_emb_of_fin_boundaries : c.boundaries.orderEmbOfFin c.card_boundaries_eq_succ_length = c.boundary := by
  refine' (Finset.order_emb_of_fin_unique' _ _).symm
  exact fun i => (Finset.mem_map' _).2 (Finset.mem_univ _)

/-- Embedding the `i`-th block of a composition (identified with `fin (c.blocks_fun i)`) into
`fin n` at the relevant position. -/
def embedding (i : Finₓ c.length) : Finₓ (c.blocksFun i) ↪o Finₓ n :=
  (Finₓ.natAdd <| c.sizeUpTo i).trans <|
    Finₓ.castLe <|
      calc
        c.sizeUpTo i + c.blocksFun i = c.sizeUpTo (i + 1) := (c.size_up_to_succ _).symm
        _ ≤ c.sizeUpTo c.length := monotone_sum_take _ i.2
        _ = n := c.size_up_to_length
        

@[simp]
theorem coe_embedding (i : Finₓ c.length) (j : Finₓ (c.blocksFun i)) : (c.Embedding i j : ℕ) = c.sizeUpTo i + j :=
  rfl

/-- `index_exists` asserts there is some `i` with `j < c.size_up_to (i+1)`.
In the next definition `index` we use `nat.find` to produce the minimal such index.
-/
theorem index_exists {j : ℕ} (h : j < n) : ∃ i : ℕ, j < c.sizeUpTo i.succ ∧ i < c.length := by
  have n_pos : 0 < n := lt_of_le_of_ltₓ (zero_le j) h
  have : 0 < c.blocks.sum := by
    rwa [← c.blocks_sum] at n_pos
  have length_pos : 0 < c.blocks.length := length_pos_of_sum_pos (blocks c) this
  refine' ⟨c.length.pred, _, Nat.pred_ltₓ (ne_of_gtₓ length_pos)⟩
  have : c.length.pred.succ = c.length := Nat.succ_pred_eq_of_posₓ length_pos
  simp [← this, ← h]

/-- `c.index j` is the index of the block in the composition `c` containing `j`. -/
def index (j : Finₓ n) : Finₓ c.length :=
  ⟨Nat.findₓ (c.index_exists j.2), (Nat.find_specₓ (c.index_exists j.2)).2⟩

theorem lt_size_up_to_index_succ (j : Finₓ n) : (j : ℕ) < c.sizeUpTo (c.index j).succ :=
  (Nat.find_specₓ (c.index_exists j.2)).1

theorem size_up_to_index_le (j : Finₓ n) : c.sizeUpTo (c.index j) ≤ j := by
  by_contra H
  set i := c.index j with hi
  push_neg  at H
  have i_pos : (0 : ℕ) < i := by
    by_contra' i_pos
    revert H
    simp [← nonpos_iff_eq_zero.1 i_pos, ← c.size_up_to_zero]
  let i₁ := (i : ℕ).pred
  have i₁_lt_i : i₁ < i := Nat.pred_ltₓ (ne_of_gtₓ i_pos)
  have i₁_succ : i₁.succ = i := Nat.succ_pred_eq_of_posₓ i_pos
  have := Nat.find_minₓ (c.index_exists j.2) i₁_lt_i
  simp [← lt_transₓ i₁_lt_i (c.index j).2, ← i₁_succ] at this
  exact Nat.lt_le_antisymmₓ H this

/-- Mapping an element `j` of `fin n` to the element in the block containing it, identified with
`fin (c.blocks_fun (c.index j))` through the canonical increasing bijection. -/
def invEmbedding (j : Finₓ n) : Finₓ (c.blocksFun (c.index j)) :=
  ⟨j - c.sizeUpTo (c.index j), by
    rw [tsub_lt_iff_right, add_commₓ, ← size_up_to_succ']
    · exact lt_size_up_to_index_succ _ _
      
    · exact size_up_to_index_le _ _
      ⟩

@[simp]
theorem coe_inv_embedding (j : Finₓ n) : (c.invEmbedding j : ℕ) = j - c.sizeUpTo (c.index j) :=
  rfl

theorem embedding_comp_inv (j : Finₓ n) : c.Embedding (c.index j) (c.invEmbedding j) = j := by
  rw [Finₓ.ext_iff]
  apply add_tsub_cancel_of_le (c.size_up_to_index_le j)

theorem mem_range_embedding_iff {j : Finₓ n} {i : Finₓ c.length} :
    j ∈ Set.Range (c.Embedding i) ↔ c.sizeUpTo i ≤ j ∧ (j : ℕ) < c.sizeUpTo (i : ℕ).succ := by
  constructor
  · intro h
    rcases Set.mem_range.2 h with ⟨k, hk⟩
    rw [Finₓ.ext_iff] at hk
    change c.size_up_to i + k = (j : ℕ) at hk
    rw [← hk]
    simp [← size_up_to_succ', ← k.is_lt]
    
  · intro h
    apply Set.mem_range.2
    refine' ⟨⟨j - c.size_up_to i, _⟩, _⟩
    · rw [tsub_lt_iff_left, ← size_up_to_succ']
      · exact h.2
        
      · exact h.1
        
      
    · rw [Finₓ.ext_iff]
      exact add_tsub_cancel_of_le h.1
      
    

/-- The embeddings of different blocks of a composition are disjoint. -/
theorem disjoint_range {i₁ i₂ : Finₓ c.length} (h : i₁ ≠ i₂) :
    Disjoint (Set.Range (c.Embedding i₁)) (Set.Range (c.Embedding i₂)) := by
  classical
  wlog h' : i₁ ≤ i₂ using i₁ i₂
  swap
  exact (this h.symm).symm
  by_contra d
  obtain ⟨x, hx₁, hx₂⟩ : ∃ x : Finₓ n, x ∈ Set.Range (c.embedding i₁) ∧ x ∈ Set.Range (c.embedding i₂) :=
    Set.not_disjoint_iff.1 d
  have : i₁ < i₂ := lt_of_le_of_neₓ h' h
  have A : (i₁ : ℕ).succ ≤ i₂ := Nat.succ_le_of_ltₓ this
  apply lt_irreflₓ (x : ℕ)
  calc (x : ℕ) < c.size_up_to (i₁ : ℕ).succ := (c.mem_range_embedding_iff.1 hx₁).2_ ≤ c.size_up_to (i₂ : ℕ) :=
      monotone_sum_take _ A _ ≤ x := (c.mem_range_embedding_iff.1 hx₂).1

theorem mem_range_embedding (j : Finₓ n) : j ∈ Set.Range (c.Embedding (c.index j)) := by
  have : c.embedding (c.index j) (c.inv_embedding j) ∈ Set.Range (c.embedding (c.index j)) := Set.mem_range_self _
  rwa [c.embedding_comp_inv j] at this

theorem mem_range_embedding_iff' {j : Finₓ n} {i : Finₓ c.length} : j ∈ Set.Range (c.Embedding i) ↔ i = c.index j := by
  constructor
  · rw [← not_imp_not]
    intro h
    exact Set.disjoint_right.1 (c.disjoint_range h) (c.mem_range_embedding j)
    
  · intro h
    rw [h]
    exact c.mem_range_embedding j
    

theorem index_embedding (i : Finₓ c.length) (j : Finₓ (c.blocksFun i)) : c.index (c.Embedding i j) = i := by
  symm
  rw [← mem_range_embedding_iff']
  apply Set.mem_range_self

theorem inv_embedding_comp (i : Finₓ c.length) (j : Finₓ (c.blocksFun i)) :
    (c.invEmbedding (c.Embedding i j) : ℕ) = j := by
  simp_rw [coe_inv_embedding, index_embedding, coe_embedding, add_tsub_cancel_left]

/-- Equivalence between the disjoint union of the blocks (each of them seen as
`fin (c.blocks_fun i)`) with `fin n`. -/
def blocksFinEquiv : (Σi : Finₓ c.length, Finₓ (c.blocksFun i)) ≃ Finₓ n where
  toFun := fun x => c.Embedding x.1 x.2
  invFun := fun j => ⟨c.index j, c.invEmbedding j⟩
  left_inv := fun x => by
    rcases x with ⟨i, y⟩
    dsimp'
    congr
    · exact c.index_embedding _ _
      
    rw [Finₓ.heq_ext_iff]
    · exact c.inv_embedding_comp _ _
      
    · rw [c.index_embedding]
      
  right_inv := fun j => c.embedding_comp_inv j

theorem blocks_fun_congr {n₁ n₂ : ℕ} (c₁ : Composition n₁) (c₂ : Composition n₂) (i₁ : Finₓ c₁.length)
    (i₂ : Finₓ c₂.length) (hn : n₁ = n₂) (hc : c₁.blocks = c₂.blocks) (hi : (i₁ : ℕ) = i₂) :
    c₁.blocksFun i₁ = c₂.blocksFun i₂ := by
  cases hn
  rw [← Composition.ext_iff] at hc
  cases hc
  congr
  rwa [Finₓ.ext_iff]

/-- Two compositions (possibly of different integers) coincide if and only if they have the
same sequence of blocks. -/
theorem sigma_eq_iff_blocks_eq {c : Σn, Composition n} {c' : Σn, Composition n} : c = c' ↔ c.2.blocks = c'.2.blocks :=
  by
  refine'
    ⟨fun H => by
      rw [H], fun H => _⟩
  rcases c with ⟨n, c⟩
  rcases c' with ⟨n', c'⟩
  have : n = n' := by
    rw [← c.blocks_sum, ← c'.blocks_sum, H]
  induction this
  simp only [← true_andₓ, ← eq_self_iff_true, ← heq_iff_eq]
  ext1
  exact H

/-! ### The composition `composition.ones` -/


/-- The composition made of blocks all of size `1`. -/
def ones (n : ℕ) : Composition n :=
  ⟨repeat (1 : ℕ) n, fun i hi => by
    simp [← List.eq_of_mem_repeat hi], by
    simp ⟩

instance {n : ℕ} : Inhabited (Composition n) :=
  ⟨Composition.ones n⟩

@[simp]
theorem ones_length (n : ℕ) : (ones n).length = n :=
  List.length_repeat 1 n

@[simp]
theorem ones_blocks (n : ℕ) : (ones n).blocks = repeat (1 : ℕ) n :=
  rfl

@[simp]
theorem ones_blocks_fun (n : ℕ) (i : Finₓ (ones n).length) : (ones n).blocksFun i = 1 := by
  simp [← blocks_fun, ← ones, ← blocks, ← i.2]

@[simp]
theorem ones_size_up_to (n : ℕ) (i : ℕ) : (ones n).sizeUpTo i = min i n := by
  simp [← size_up_to, ← ones_blocks, ← take_repeat]

@[simp]
theorem ones_embedding (i : Finₓ (ones n).length) (h : 0 < (ones n).blocksFun i) :
    (ones n).Embedding i ⟨0, h⟩ = ⟨i, lt_of_lt_of_leₓ i.2 (ones n).length_le⟩ := by
  ext
  simpa using i.2.le

theorem eq_ones_iff {c : Composition n} : c = ones n ↔ ∀, ∀ i ∈ c.blocks, ∀, i = 1 := by
  constructor
  · rintro rfl
    exact fun i => eq_of_mem_repeat
    
  · intro H
    ext1
    have A : c.blocks = repeat 1 c.blocks.length := eq_repeat_of_mem H
    have : c.blocks.length = n := by
      conv_rhs => rw [← c.blocks_sum, A]
      simp
    rw [A, this, ones_blocks]
    

theorem ne_ones_iff {c : Composition n} : c ≠ ones n ↔ ∃ i ∈ c.blocks, 1 < i := by
  refine' (not_congr eq_ones_iff).trans _
  have : ∀, ∀ j ∈ c.blocks, ∀, j = 1 ↔ j ≤ 1 := fun j hj => by
    simp [← le_antisymm_iffₓ, ← c.one_le_blocks hj]
  simp (config := { contextual := true })[← this]

theorem eq_ones_iff_length {c : Composition n} : c = ones n ↔ c.length = n := by
  constructor
  · rintro rfl
    exact ones_length n
    
  · contrapose
    intro H length_n
    apply lt_irreflₓ n
    calc n = ∑ i : Finₓ c.length, 1 := by
        simp [← length_n]_ < ∑ i : Finₓ c.length, c.blocks_fun i := by
        obtain ⟨i, hi, i_blocks⟩ : ∃ i ∈ c.blocks, 1 < i := ne_ones_iff.1 H
        rw [← of_fn_blocks_fun, mem_of_fn c.blocks_fun, Set.mem_range] at hi
        obtain ⟨j : Finₓ c.length, hj : c.blocks_fun j = i⟩ := hi
        rw [← hj] at i_blocks
        exact
          Finset.sum_lt_sum
            (fun i hi => by
              simp [← blocks_fun])
            ⟨j, Finset.mem_univ _, i_blocks⟩_ = n :=
        c.sum_blocks_fun
    

theorem eq_ones_iff_le_length {c : Composition n} : c = ones n ↔ n ≤ c.length := by
  simp [← eq_ones_iff_length, ← le_antisymm_iffₓ, ← c.length_le]

/-! ### The composition `composition.single` -/


/-- The composition made of a single block of size `n`. -/
def single (n : ℕ) (h : 0 < n) : Composition n :=
  ⟨[n], by
    simp [← h], by
    simp ⟩

@[simp]
theorem single_length {n : ℕ} (h : 0 < n) : (single n h).length = 1 :=
  rfl

@[simp]
theorem single_blocks {n : ℕ} (h : 0 < n) : (single n h).blocks = [n] :=
  rfl

@[simp]
theorem single_blocks_fun {n : ℕ} (h : 0 < n) (i : Finₓ (single n h).length) : (single n h).blocksFun i = n := by
  simp [← blocks_fun, ← single, ← blocks, ← i.2]

@[simp]
theorem single_embedding {n : ℕ} (h : 0 < n) (i : Finₓ n) :
    (single n h).Embedding ⟨0, single_length h ▸ zero_lt_one⟩ i = i := by
  ext
  simp

theorem eq_single_iff_length {n : ℕ} (h : 0 < n) {c : Composition n} : c = single n h ↔ c.length = 1 := by
  constructor
  · intro H
    rw [H]
    exact single_length h
    
  · intro H
    ext1
    have A : c.blocks.length = 1 := H ▸ c.blocks_length
    have B : c.blocks.sum = n := c.blocks_sum
    rw [eq_cons_of_length_one A] at B⊢
    simpa [← single_blocks] using B
    

theorem ne_single_iff {n : ℕ} (hn : 0 < n) {c : Composition n} : c ≠ single n hn ↔ ∀ i, c.blocksFun i < n := by
  rw [← not_iff_not]
  push_neg
  constructor
  · rintro rfl
    exact
      ⟨⟨0, by
          simp ⟩,
        by
        simp ⟩
    
  · rintro ⟨i, hi⟩
    rw [eq_single_iff_length]
    have : ∀ j : Finₓ c.length, j = i := by
      intro j
      by_contra ji
      apply lt_irreflₓ (∑ k, c.blocks_fun k)
      calc (∑ k, c.blocks_fun k) ≤ c.blocks_fun i := by
          simp only [← c.sum_blocks_fun, ← hi]_ < ∑ k, c.blocks_fun k :=
          Finset.single_lt_sum ji (Finset.mem_univ _) (Finset.mem_univ _) (c.one_le_blocks_fun j) fun _ _ _ => zero_le _
    simpa using Fintype.card_eq_one_of_forall_eq this
    

end Composition

/-!
### Splitting a list

Given a list of length `n` and a composition `c` of `n`, one can split `l` into `c.length` sublists
of respective lengths `c.blocks_fun 0`, ..., `c.blocks_fun (c.length-1)`. This is inverse to the
join operation.
-/


namespace List

variable {α : Type _}

/-- Auxiliary for `list.split_wrt_composition`. -/
def splitWrtCompositionAux : List α → List ℕ → List (List α)
  | l, [] => []
  | l, n :: ns =>
    let (l₁, l₂) := l.splitAt n
    l₁ :: split_wrt_composition_aux l₂ ns

/-- Given a list of length `n` and a composition `[i₁, ..., iₖ]` of `n`, split `l` into a list of
`k` lists corresponding to the blocks of the composition, of respective lengths `i₁`, ..., `iₖ`.
This makes sense mostly when `n = l.length`, but this is not necessary for the definition. -/
def splitWrtComposition (l : List α) (c : Composition n) : List (List α) :=
  splitWrtCompositionAux l c.blocks

attribute [local simp] split_wrt_composition_aux.equations._eqn_1

@[local simp]
theorem split_wrt_composition_aux_cons (l : List α) (n ns) :
    l.splitWrtCompositionAux (n :: ns) = takeₓ n l :: (dropₓ n l).splitWrtCompositionAux ns := by
  simp [← split_wrt_composition_aux]

theorem length_split_wrt_composition_aux (l : List α) (ns) : length (l.splitWrtCompositionAux ns) = ns.length := by
  induction ns generalizing l <;> simp [*]

/-- When one splits a list along a composition `c`, the number of sublists thus created is
`c.length`. -/
@[simp]
theorem length_split_wrt_composition (l : List α) (c : Composition n) : length (l.splitWrtComposition c) = c.length :=
  length_split_wrt_composition_aux _ _

theorem map_length_split_wrt_composition_aux {ns : List ℕ} :
    ∀ {l : List α}, ns.Sum ≤ l.length → map length (l.splitWrtCompositionAux ns) = ns := by
  induction' ns with n ns IH <;> intro l h <;> simp at h⊢
  have := le_transₓ (Nat.le_add_rightₓ _ _) h
  rw [IH]
  · simp [← this]
    
  rwa [length_drop, le_tsub_iff_left this]

/-- When one splits a list along a composition `c`, the lengths of the sublists thus created are
given by the block sizes in `c`. -/
theorem map_length_split_wrt_composition (l : List α) (c : Composition l.length) :
    map length (l.splitWrtComposition c) = c.blocks :=
  map_length_split_wrt_composition_aux (le_of_eqₓ c.blocks_sum)

theorem length_pos_of_mem_split_wrt_composition {l l' : List α} {c : Composition l.length}
    (h : l' ∈ l.splitWrtComposition c) : 0 < length l' := by
  have : l'.length ∈ (l.split_wrt_composition c).map List.length := List.mem_map_of_memₓ List.length h
  rw [map_length_split_wrt_composition] at this
  exact c.blocks_pos this

theorem sum_take_map_length_split_wrt_composition (l : List α) (c : Composition l.length) (i : ℕ) :
    (((l.splitWrtComposition c).map length).take i).Sum = c.sizeUpTo i := by
  congr
  exact map_length_split_wrt_composition l c

theorem nth_le_split_wrt_composition_aux (l : List α) (ns : List ℕ) {i : ℕ} (hi) :
    nthLe (l.splitWrtCompositionAux ns) i hi = (l.take (ns.take (i + 1)).Sum).drop (ns.take i).Sum := by
  induction' ns with n ns IH generalizing l i
  · cases hi
    
  cases i <;> simp [← IH]
  rw [add_commₓ n, drop_add, drop_take]

/-- The `i`-th sublist in the splitting of a list `l` along a composition `c`, is the slice of `l`
between the indices `c.size_up_to i` and `c.size_up_to (i+1)`, i.e., the indices in the `i`-th
block of the composition. -/
theorem nth_le_split_wrt_composition (l : List α) (c : Composition n) {i : ℕ}
    (hi : i < (l.splitWrtComposition c).length) :
    nthLe (l.splitWrtComposition c) i hi = (l.take (c.sizeUpTo (i + 1))).drop (c.sizeUpTo i) :=
  nth_le_split_wrt_composition_aux _ _ _

theorem join_split_wrt_composition_aux {ns : List ℕ} :
    ∀ {l : List α}, ns.Sum = l.length → (l.splitWrtCompositionAux ns).join = l := by
  induction' ns with n ns IH <;> intro l h <;> simp at h⊢
  · exact (length_eq_zero.1 h.symm).symm
    
  rw [IH]
  · simp
    
  rwa [length_drop, ← h, add_tsub_cancel_left]

/-- If one splits a list along a composition, and then joins the sublists, one gets back the
original list. -/
@[simp]
theorem join_split_wrt_composition (l : List α) (c : Composition l.length) : (l.splitWrtComposition c).join = l :=
  join_split_wrt_composition_aux c.blocks_sum

/-- If one joins a list of lists and then splits the join along the right composition, one gets
back the original list of lists. -/
@[simp]
theorem split_wrt_composition_join (L : List (List α)) (c : Composition L.join.length) (h : map length L = c.blocks) :
    splitWrtComposition (join L) c = L := by
  simp only [← eq_self_iff_true, ← and_selfₓ, ← eq_iff_join_eq, ← join_split_wrt_composition, ←
    map_length_split_wrt_composition, ← h]

end List

/-!
### Compositions as sets

Combinatorial viewpoints on compositions, seen as finite subsets of `fin (n+1)` containing `0` and
`n`, where the points of the set (other than `n`) correspond to the leftmost points of each block.
-/


/-- Bijection between compositions of `n` and subsets of `{0, ..., n-2}`, defined by
considering the restriction of the subset to `{1, ..., n-1}` and shifting to the left by one. -/
def compositionAsSetEquiv (n : ℕ) : CompositionAsSet n ≃ Finset (Finₓ (n - 1)) where
  toFun := fun c =>
    { i : Finₓ (n - 1) |
        (⟨1 + (i : ℕ), by
            apply (add_lt_add_left i.is_lt 1).trans_le
            rw [Nat.succ_eq_add_one, add_commₓ]
            exact add_le_add (Nat.sub_leₓ n 1) (le_reflₓ 1)⟩ :
            Finₓ n.succ) ∈
          c.boundaries }.toFinset
  invFun := fun s =>
    { boundaries :=
        { i : Finₓ n.succ | i = 0 ∨ i = Finₓ.last n ∨ ∃ (j : Finₓ (n - 1))(hj : j ∈ s), (i : ℕ) = j + 1 }.toFinset,
      zero_mem := by
        simp ,
      last_mem := by
        simp }
  left_inv := by
    intro c
    ext i
    simp only [← exists_prop, ← add_commₓ, ← Set.mem_to_finset, ← true_orₓ, ← or_trueₓ, ← Set.mem_set_of_eq]
    constructor
    · rintro (rfl | rfl | ⟨j, hj1, hj2⟩)
      · exact c.zero_mem
        
      · exact c.last_mem
        
      · convert hj1
        rwa [Finₓ.ext_iff]
        
      
    · simp only [← or_iff_not_imp_left]
      intro i_mem i_ne_zero i_ne_last
      simp [← Finₓ.ext_iff] at i_ne_zero i_ne_last
      have A : (1 + (i - 1) : ℕ) = (i : ℕ) := by
        rw [add_commₓ]
        exact Nat.succ_pred_eq_of_posₓ (pos_iff_ne_zero.mpr i_ne_zero)
      refine' ⟨⟨i - 1, _⟩, _, _⟩
      · have : (i : ℕ) < n + 1 := i.2
        simp [← Nat.lt_succ_iff_lt_or_eq, ← i_ne_last] at this
        exact Nat.pred_lt_predₓ i_ne_zero this
        
      · convert i_mem
        rw [Finₓ.ext_iff]
        simp only [← Finₓ.coe_mk, ← A]
        
      · simp [← A]
        
      
  right_inv := by
    intro s
    ext i
    have : 1 + (i : ℕ) ≠ n := by
      apply ne_of_ltₓ
      convert add_lt_add_left i.is_lt 1
      rw [add_commₓ]
      apply (Nat.succ_pred_eq_of_posₓ _).symm
      exact (zero_le i.val).trans_lt (i.2.trans_le (Nat.sub_leₓ n 1))
    simp only [← Finₓ.ext_iff, ← exists_prop, ← Finₓ.coe_zero, ← add_commₓ, ← Set.mem_to_finset, ← Set.mem_set_of_eq, ←
      Finₓ.coe_last]
    erw [Set.mem_set_of_eq]
    simp only [← this, ← false_orₓ, ← add_right_injₓ, ← add_eq_zero_iff, ← one_ne_zero, ← false_andₓ, ← Finₓ.coe_mk]
    constructor
    · rintro ⟨j, js, hj⟩
      convert js
      exact (Finₓ.ext_iff _ _).2 hj
      
    · intro h
      exact ⟨i, h, rfl⟩
      

instance compositionAsSetFintype (n : ℕ) : Fintype (CompositionAsSet n) :=
  Fintype.ofEquiv _ (compositionAsSetEquiv n).symm

theorem composition_as_set_card (n : ℕ) : Fintype.card (CompositionAsSet n) = 2 ^ (n - 1) := by
  have : Fintype.card (Finset (Finₓ (n - 1))) = 2 ^ (n - 1) := by
    simp
  rw [← this]
  exact Fintype.card_congr (compositionAsSetEquiv n)

namespace CompositionAsSet

variable (c : CompositionAsSet n)

theorem boundaries_nonempty : c.boundaries.Nonempty :=
  ⟨0, c.zero_mem⟩

theorem card_boundaries_pos : 0 < Finset.card c.boundaries :=
  Finset.card_pos.mpr c.boundaries_nonempty

/-- Number of blocks in a `composition_as_set`. -/
def length : ℕ :=
  Finset.card c.boundaries - 1

theorem card_boundaries_eq_succ_length : c.boundaries.card = c.length + 1 :=
  (tsub_eq_iff_eq_add_of_le (Nat.succ_le_of_ltₓ c.card_boundaries_pos)).mp rfl

theorem length_lt_card_boundaries : c.length < c.boundaries.card := by
  rw [c.card_boundaries_eq_succ_length]
  exact lt_add_one _

theorem lt_length (i : Finₓ c.length) : (i : ℕ) + 1 < c.boundaries.card :=
  lt_tsub_iff_right.mp i.2

theorem lt_length' (i : Finₓ c.length) : (i : ℕ) < c.boundaries.card :=
  lt_of_le_of_ltₓ (Nat.le_succₓ i) (c.lt_length i)

/-- Canonical increasing bijection from `fin c.boundaries.card` to `c.boundaries`. -/
def boundary : Finₓ c.boundaries.card ↪o Finₓ (n + 1) :=
  c.boundaries.orderEmbOfFin rfl

@[simp]
theorem boundary_zero : (c.boundary ⟨0, c.card_boundaries_pos⟩ : Finₓ (n + 1)) = 0 := by
  rw [boundary, Finset.order_emb_of_fin_zero rfl c.card_boundaries_pos]
  exact le_antisymmₓ (Finset.min'_le _ _ c.zero_mem) (Finₓ.zero_le _)

@[simp]
theorem boundary_length : c.boundary ⟨c.length, c.length_lt_card_boundaries⟩ = Finₓ.last n := by
  convert Finset.order_emb_of_fin_last rfl c.card_boundaries_pos
  exact le_antisymmₓ (Finset.le_max' _ _ c.last_mem) (Finₓ.le_last _)

/-- Size of the `i`-th block in a `composition_as_set`, seen as a function on `fin c.length`. -/
def blocksFun (i : Finₓ c.length) : ℕ :=
  c.boundary ⟨(i : ℕ) + 1, c.lt_length i⟩ - c.boundary ⟨i, c.lt_length' i⟩

theorem blocks_fun_pos (i : Finₓ c.length) : 0 < c.blocksFun i := by
  have : (⟨i, c.lt_length' i⟩ : Finₓ c.boundaries.card) < ⟨i + 1, c.lt_length i⟩ := Nat.lt_succ_selfₓ _
  exact lt_tsub_iff_left.mpr ((c.boundaries.order_emb_of_fin rfl).StrictMono this)

/-- List of the sizes of the blocks in a `composition_as_set`. -/
def blocks (c : CompositionAsSet n) : List ℕ :=
  ofFnₓ c.blocksFun

@[simp]
theorem blocks_length : c.blocks.length = c.length :=
  length_of_fn _

theorem blocks_partial_sum {i : ℕ} (h : i < c.boundaries.card) : (c.blocks.take i).Sum = c.boundary ⟨i, h⟩ := by
  induction' i with i IH
  · simp
    
  have A : i < c.blocks.length := by
    rw [c.card_boundaries_eq_succ_length] at h
    simp [← blocks, ← Nat.lt_of_succ_lt_succₓ h]
  have B : i < c.boundaries.card :=
    lt_of_lt_of_leₓ A
      (by
        simp [← blocks, ← length, ← Nat.sub_leₓ])
  rw [sum_take_succ _ _ A, IH B]
  simp only [← blocks, ← blocks_fun, ← nth_le_of_fn']
  apply add_tsub_cancel_of_le
  simp

theorem mem_boundaries_iff_exists_blocks_sum_take_eq {j : Finₓ (n + 1)} :
    j ∈ c.boundaries ↔ ∃ i < c.boundaries.card, (c.blocks.take i).Sum = j := by
  constructor
  · intro hj
    rcases(c.boundaries.order_iso_of_fin rfl).Surjective ⟨j, hj⟩ with ⟨i, hi⟩
    rw [Subtype.ext_iff, Subtype.coe_mk] at hi
    refine' ⟨i.1, i.2, _⟩
    rw [← hi, c.blocks_partial_sum i.2]
    rfl
    
  · rintro ⟨i, hi, H⟩
    convert (c.boundaries.order_iso_of_fin rfl ⟨i, hi⟩).2
    have : c.boundary ⟨i, hi⟩ = j := by
      rwa [Finₓ.ext_iff, ← c.blocks_partial_sum hi]
    exact this.symm
    

theorem blocks_sum : c.blocks.Sum = n := by
  have : c.blocks.take c.length = c.blocks :=
    take_all_of_le
      (by
        simp [← blocks])
  rw [← this, c.blocks_partial_sum c.length_lt_card_boundaries, c.boundary_length]
  rfl

/-- Associating a `composition n` to a `composition_as_set n`, by registering the sizes of the
blocks as a list of positive integers. -/
def toComposition : Composition n where
  blocks := c.blocks
  blocks_pos := by
    simp only [← blocks, ← forall_mem_of_fn_iff, ← blocks_fun_pos c, ← forall_true_iff]
  blocks_sum := c.blocks_sum

end CompositionAsSet

/-!
### Equivalence between compositions and compositions as sets

In this section, we explain how to go back and forth between a `composition` and a
`composition_as_set`, by showing that their `blocks` and `length` and `boundaries` correspond to
each other, and construct an equivalence between them called `composition_equiv`.
-/


@[simp]
theorem Composition.to_composition_as_set_length (c : Composition n) : c.toCompositionAsSet.length = c.length := by
  simp [← Composition.toCompositionAsSet, ← CompositionAsSet.length, ← c.card_boundaries_eq_succ_length]

@[simp]
theorem CompositionAsSet.to_composition_length (c : CompositionAsSet n) : c.toComposition.length = c.length := by
  simp [← CompositionAsSet.toComposition, ← Composition.length, ← Composition.blocks]

@[simp]
theorem Composition.to_composition_as_set_blocks (c : Composition n) : c.toCompositionAsSet.blocks = c.blocks := by
  let d := c.to_composition_as_set
  change d.blocks = c.blocks
  have length_eq : d.blocks.length = c.blocks.length := by
    convert c.to_composition_as_set_length
    simp [← CompositionAsSet.blocks]
  suffices H : ∀, ∀ i ≤ d.blocks.length, ∀, (d.blocks.take i).Sum = (c.blocks.take i).Sum
  exact eq_of_sum_take_eq length_eq H
  intro i hi
  have i_lt : i < d.boundaries.card := by
    convert Nat.lt_succ_iffₓ.2 hi
    convert d.card_boundaries_eq_succ_length
    exact length_of_fn _
  have i_lt' : i < c.boundaries.card := i_lt
  have i_lt'' : i < c.length + 1 := by
    rwa [c.card_boundaries_eq_succ_length] at i_lt'
  have A :
    d.boundaries.order_emb_of_fin rfl ⟨i, i_lt⟩ =
      c.boundaries.order_emb_of_fin c.card_boundaries_eq_succ_length ⟨i, i_lt''⟩ :=
    rfl
  have B : c.size_up_to i = c.boundary ⟨i, i_lt''⟩ := rfl
  rw [d.blocks_partial_sum i_lt, CompositionAsSet.boundary, ← Composition.sizeUpTo, B, A, c.order_emb_of_fin_boundaries]

@[simp]
theorem CompositionAsSet.to_composition_blocks (c : CompositionAsSet n) : c.toComposition.blocks = c.blocks :=
  rfl

@[simp]
theorem CompositionAsSet.to_composition_boundaries (c : CompositionAsSet n) :
    c.toComposition.boundaries = c.boundaries := by
  ext j
  simp [← c.mem_boundaries_iff_exists_blocks_sum_take_eq, ← c.card_boundaries_eq_succ_length, ← Composition.boundary, ←
    Finₓ.ext_iff, ← Composition.sizeUpTo, ← exists_prop, ← Finset.mem_univ, ← take, ← exists_prop_of_true, ←
    Finset.mem_image, ← CompositionAsSet.to_composition_blocks, ← Composition.boundaries]
  constructor
  · rintro ⟨i, hi⟩
    refine' ⟨i.1, _, hi⟩
    convert i.2
    simp
    
  · rintro ⟨i, i_lt, hi⟩
    have : i < c.to_composition.length + 1 := by
      simpa using i_lt
    exact ⟨⟨i, this⟩, hi⟩
    

@[simp]
theorem Composition.to_composition_as_set_boundaries (c : Composition n) :
    c.toCompositionAsSet.boundaries = c.boundaries :=
  rfl

/-- Equivalence between `composition n` and `composition_as_set n`. -/
def compositionEquiv (n : ℕ) : Composition n ≃ CompositionAsSet n where
  toFun := fun c => c.toCompositionAsSet
  invFun := fun c => c.toComposition
  left_inv := fun c => by
    ext1
    exact c.to_composition_as_set_blocks
  right_inv := fun c => by
    ext1
    exact c.to_composition_boundaries

instance compositionFintype (n : ℕ) : Fintype (Composition n) :=
  Fintype.ofEquiv _ (compositionEquiv n).symm

theorem composition_card (n : ℕ) : Fintype.card (Composition n) = 2 ^ (n - 1) := by
  rw [← composition_as_set_card n]
  exact Fintype.card_congr (compositionEquiv n)

