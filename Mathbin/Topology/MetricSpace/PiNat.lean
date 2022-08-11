/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathbin.Tactic.RingExp
import Mathbin.Topology.MetricSpace.HausdorffDistance

/-!
# Topological study of spaces `Π (n : ℕ), E n`

When `E n` are topological spaces, the space `Π (n : ℕ), E n` is naturally a topological space
(with the product topology). When `E n` are uniform spaces, it also inherits a uniform structure.
However, it does not inherit a canonical metric space structure of the `E n`. Nevertheless, one
can put a noncanonical metric space structure (or rather, several of them). This is done in this
file.

## Main definitions and results

One can define a combinatorial distance on `Π (n : ℕ), E n`, as follows:

* `pi_nat.cylinder x n` is the set of points `y` with `x i = y i` for `i < n`.
* `pi_nat.first_diff x y` is the first index at which `x i ≠ y i`.
* `pi_nat.dist x y` is equal to `(1/2) ^ (first_diff x y)`. It defines a distance
  on `Π (n : ℕ), E n`, compatible with the topology when the `E n` have the discrete topology.
* `pi_nat.metric_space`: the metric space structure, given by this distance. Not registered as an
  instance. This space is a complete metric space.
* `pi_nat.metric_space_of_discrete_uniformity`: the same metric space structure, but adjusting the
  uniformity defeqness when the `E n` already have the discrete uniformity. Not registered as an
  instance
* `pi_nat.metric_space_nat_nat`: the particular case of `ℕ → ℕ`, not registered as an instance.

These results are used to construct continuous functions on `Π n, E n`:

* `pi_nat.exists_retraction_of_is_closed`: given a nonempty closed subset `s` of `Π (n : ℕ), E n`,
  there exists a retraction onto `s`, i.e., a continuous map from the whole space to `s`
  restricting to the identity on `s`.
* `exists_nat_nat_continuous_surjective_of_complete_space`: given any nonempty complete metric
  space with second-countable topology, there exists a continuous surjection from `ℕ → ℕ` onto
  this space.

One can also put distances on `Π (i : ι), E i` when the spaces `E i` are metric spaces (not discrete
in general), and `ι` is countable.

* `pi_countable.dist` is the distance on `Π i, E i` given by
    `dist x y = ∑' i, min (1/2)^(encode i) (dist (x i) (y i))`.
* `pi_countable.metric_space` is the corresponding metric space structure, adjusted so that
  the uniformity is definitionally the product uniformity. Not registered as an instance.
-/


noncomputable section

open Classical TopologicalSpace Filter

open TopologicalSpace Set Metric Filter Function

attribute [local simp] pow_le_pow_iff one_lt_two inv_le_inv

variable {E : ℕ → Type _}

namespace PiNat

/-! ### The first_diff function -/


/-- In a product space `Π n, E n`, then `first_diff x y` is the first index at which `x` and `y`
differ. If `x = y`, then by convention we set `first_diff x x = 0`. -/
@[pp_nodot]
irreducible_def firstDiff (x y : ∀ n, E n) : ℕ :=
  if h : x ≠ y then Nat.findₓ (ne_iff.1 h) else 0

theorem apply_first_diff_ne {x y : ∀ n, E n} (h : x ≠ y) : x (firstDiff x y) ≠ y (firstDiff x y) := by
  rw [first_diff, dif_pos h]
  exact Nat.find_specₓ (ne_iff.1 h)

theorem apply_eq_of_lt_first_diff {x y : ∀ n, E n} {n : ℕ} (hn : n < firstDiff x y) : x n = y n := by
  rw [first_diff] at hn
  split_ifs  at hn
  · convert Nat.find_minₓ (ne_iff.1 h) hn
    simp
    
  · exact (not_lt_zero' hn).elim
    

theorem first_diff_comm (x y : ∀ n, E n) : firstDiff x y = firstDiff y x := by
  rcases eq_or_ne x y with (rfl | hxy)
  · rfl
    
  rcases lt_trichotomyₓ (first_diff x y) (first_diff y x) with (h | h | h)
  · exact (apply_first_diff_ne hxy (apply_eq_of_lt_first_diff h).symm).elim
    
  · exact h
    
  · exact (apply_first_diff_ne hxy.symm (apply_eq_of_lt_first_diff h).symm).elim
    

theorem min_first_diff_le (x y z : ∀ n, E n) (h : x ≠ z) : min (firstDiff x y) (firstDiff y z) ≤ firstDiff x z := by
  by_contra' H
  have : x (first_diff x z) = z (first_diff x z) :=
    calc
      x (first_diff x z) = y (first_diff x z) := apply_eq_of_lt_first_diff (H.trans_le (min_le_leftₓ _ _))
      _ = z (first_diff x z) := apply_eq_of_lt_first_diff (H.trans_le (min_le_rightₓ _ _))
      
  exact (apply_first_diff_ne h this).elim

/-! ### Cylinders -/


/-- In a product space `Π n, E n`, the cylinder set of length `n` around `x`, denoted
`cylinder x n`, is the set of sequences `y` that coincide with `x` on the first `n` symbols, i.e.,
such that `y i = x i` for all `i < n`.
-/
def Cylinder (x : ∀ n, E n) (n : ℕ) : Set (∀ n, E n) :=
  { y | ∀ i, i < n → y i = x i }

theorem cylinder_eq_pi (x : ∀ n, E n) (n : ℕ) : Cylinder x n = Set.Pi (Finset.range n : Set ℕ) fun i : ℕ => {x i} := by
  ext y
  simp [← cylinder]

@[simp]
theorem cylinder_zero (x : ∀ n, E n) : Cylinder x 0 = univ := by
  simp [← cylinder_eq_pi]

theorem cylinder_anti (x : ∀ n, E n) {m n : ℕ} (h : m ≤ n) : Cylinder x n ⊆ Cylinder x m := fun y hy i hi =>
  hy i (hi.trans_le h)

@[simp]
theorem mem_cylinder_iff {x y : ∀ n, E n} {n : ℕ} : y ∈ Cylinder x n ↔ ∀ i, i < n → y i = x i :=
  Iff.rfl

theorem self_mem_cylinder (x : ∀ n, E n) (n : ℕ) : x ∈ Cylinder x n := by
  simp

theorem mem_cylinder_iff_eq {x y : ∀ n, E n} {n : ℕ} : y ∈ Cylinder x n ↔ Cylinder y n = Cylinder x n := by
  constructor
  · intro hy
    apply subset.antisymm
    · intro z hz i hi
      rw [← hy i hi]
      exact hz i hi
      
    · intro z hz i hi
      rw [hy i hi]
      exact hz i hi
      
    
  · intro h
    rw [← h]
    exact self_mem_cylinder _ _
    

theorem mem_cylinder_comm (x y : ∀ n, E n) (n : ℕ) : y ∈ Cylinder x n ↔ x ∈ Cylinder y n := by
  simp [← mem_cylinder_iff_eq, ← eq_comm]

theorem mem_cylinder_iff_le_first_diff {x y : ∀ n, E n} (hne : x ≠ y) (i : ℕ) : x ∈ Cylinder y i ↔ i ≤ firstDiff x y :=
  by
  constructor
  · intro h
    by_contra'
    exact apply_first_diff_ne hne (h _ this)
    
  · intro hi j hj
    exact apply_eq_of_lt_first_diff (hj.trans_le hi)
    

theorem mem_cylinder_first_diff (x y : ∀ n, E n) : x ∈ Cylinder y (firstDiff x y) := fun i hi =>
  apply_eq_of_lt_first_diff hi

theorem cylinder_eq_cylinder_of_le_first_diff (x y : ∀ n, E n) {n : ℕ} (hn : n ≤ firstDiff x y) :
    Cylinder x n = Cylinder y n := by
  rw [← mem_cylinder_iff_eq]
  intro i hi
  exact apply_eq_of_lt_first_diff (hi.trans_le hn)

theorem Union_cylinder_update (x : ∀ n, E n) (n : ℕ) : (⋃ k, Cylinder (update x n k) (n + 1)) = Cylinder x n := by
  ext y
  simp only [← mem_cylinder_iff, ← mem_Union]
  constructor
  · rintro ⟨k, hk⟩ i hi
    simpa [← hi.ne] using hk i (Nat.lt_succ_of_ltₓ hi)
    
  · intro H
    refine' ⟨y n, fun i hi => _⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with (h'i | rfl)
    · simp [← H i h'i, ← h'i.ne]
      
    · simp
      
    

theorem update_mem_cylinder (x : ∀ n, E n) (n : ℕ) (y : E n) : update x n y ∈ Cylinder x n :=
  mem_cylinder_iff.2 fun i hi => by
    simp [← hi.ne]

/-!
### A distance function on `Π n, E n`

We define a distance function on `Π n, E n`, given by `dist x y = (1/2)^n` where `n` is the first
index at which `x` and `y` differ. When each `E n` has the discrete topology, this distance will
define the right topology on the product space. We do not record a global `has_dist` instance nor
a `metric_space`instance, as other distances may be used on these spaces, but we register them as
local instances in this section.
-/


/-- The distance function on a product space `Π n, E n`, given by `dist x y = (1/2)^n` where `n` is
the first index at which `x` and `y` differ. -/
protected def hasDist : HasDist (∀ n, E n) :=
  ⟨fun x y => if h : x ≠ y then (1 / 2 : ℝ) ^ firstDiff x y else 0⟩

attribute [local instance] PiNat.hasDist

theorem dist_eq_of_ne {x y : ∀ n, E n} (h : x ≠ y) : dist x y = (1 / 2 : ℝ) ^ firstDiff x y := by
  simp [← dist, ← h]

protected theorem dist_self (x : ∀ n, E n) : dist x x = 0 := by
  simp [← dist]

protected theorem dist_comm (x y : ∀ n, E n) : dist x y = dist y x := by
  simp [← dist, ← @eq_comm _ x y, ← first_diff_comm]

protected theorem dist_nonneg (x y : ∀ n, E n) : 0 ≤ dist x y := by
  rcases eq_or_ne x y with (rfl | h)
  · simp [← dist]
    
  · simp [← dist, ← h]
    

theorem dist_triangle_nonarch (x y z : ∀ n, E n) : dist x z ≤ max (dist x y) (dist y z) := by
  rcases eq_or_ne x z with (rfl | hxz)
  · simp [← PiNat.dist_self x, ← PiNat.dist_nonneg]
    
  rcases eq_or_ne x y with (rfl | hxy)
  · simp
    
  rcases eq_or_ne y z with (rfl | hyz)
  · simp
    
  simp only [← dist_eq_of_ne, ← hxz, ← hxy, ← hyz, ← inv_le_inv, ← one_div, ← inv_pow, ← zero_lt_bit0, ← Ne.def, ←
    not_false_iff, ← le_max_iff, ← zero_lt_one, ← pow_le_pow_iff, ← one_lt_two, ← pow_pos, ←
    min_le_iff.1 (min_first_diff_le x y z hxz)]

protected theorem dist_triangle (x y z : ∀ n, E n) : dist x z ≤ dist x y + dist y z :=
  calc
    dist x z ≤ max (dist x y) (dist y z) := dist_triangle_nonarch x y z
    _ ≤ dist x y + dist y z := max_le_add_of_nonneg (PiNat.dist_nonneg _ _) (PiNat.dist_nonneg _ _)
    

protected theorem eq_of_dist_eq_zero (x y : ∀ n, E n) (hxy : dist x y = 0) : x = y := by
  rcases eq_or_ne x y with (rfl | h)
  · rfl
    
  simp [← dist_eq_of_ne h] at hxy
  exact (two_ne_zero (pow_eq_zero hxy)).elim

theorem mem_cylinder_iff_dist_le {x y : ∀ n, E n} {n : ℕ} : y ∈ Cylinder x n ↔ dist y x ≤ (1 / 2) ^ n := by
  rcases eq_or_ne y x with (rfl | hne)
  · simp [← PiNat.dist_self]
    
  suffices (∀ i : ℕ, i < n → y i = x i) ↔ n ≤ first_diff y x by
    simpa [← dist_eq_of_ne hne]
  constructor
  · intro hy
    by_contra' H
    exact apply_first_diff_ne hne (hy _ H)
    
  · intro h i hi
    exact apply_eq_of_lt_first_diff (hi.trans_le h)
    

theorem apply_eq_of_dist_lt {x y : ∀ n, E n} {n : ℕ} (h : dist x y < (1 / 2) ^ n) {i : ℕ} (hi : i ≤ n) : x i = y i := by
  rcases eq_or_ne x y with (rfl | hne)
  · rfl
    
  have : n < first_diff x y := by
    simpa [← dist_eq_of_ne hne, ← inv_lt_inv, ← pow_lt_pow_iff, ← one_lt_two] using h
  exact apply_eq_of_lt_first_diff (hi.trans_lt this)

/-- A function to a pseudo-metric-space is `1`-Lipschitz if and only if points in the same cylinder
of length `n` are sent to points within distance `(1/2)^n`.
Not expressed using `lipschitz_with` as we don't have a metric space structure -/
theorem lipschitz_with_one_iff_forall_dist_image_le_of_mem_cylinder {α : Type _} [PseudoMetricSpace α]
    {f : (∀ n, E n) → α} :
    (∀ x y : ∀ n, E n, dist (f x) (f y) ≤ dist x y) ↔ ∀ x y n, y ∈ Cylinder x n → dist (f x) (f y) ≤ (1 / 2) ^ n := by
  constructor
  · intro H x y n hxy
    apply (H x y).trans
    rw [PiNat.dist_comm]
    exact mem_cylinder_iff_dist_le.1 hxy
    
  · intro H x y
    rcases eq_or_ne x y with (rfl | hne)
    · simp [← PiNat.dist_nonneg]
      
    rw [dist_eq_of_ne hne]
    apply H x y (first_diff x y)
    rw [first_diff_comm]
    exact mem_cylinder_first_diff _ _
    

variable (E) [∀ n, TopologicalSpace (E n)] [∀ n, DiscreteTopology (E n)]

theorem is_topological_basis_cylinders :
    IsTopologicalBasis { s : Set (∀ n, E n) | ∃ (x : ∀ n, E n)(n : ℕ), s = Cylinder x n } := by
  apply is_topological_basis_of_open_of_nhds
  · rintro u ⟨x, n, rfl⟩
    rw [cylinder_eq_pi]
    exact is_open_set_pi (Finset.range n).finite_to_set fun a ha => is_open_discrete _
    
  · intro x u hx u_open
    obtain ⟨v, ⟨U, F, hUF, rfl⟩, xU, Uu⟩ :
      ∃ (v : Set (∀ i : ℕ, E i))(H :
        v ∈
          { S : Set (∀ i : ℕ, E i) |
            ∃ (U : ∀ i : ℕ, Set (E i))(F : Finset ℕ),
              (∀ i : ℕ, i ∈ F → U i ∈ { s : Set (E i) | IsOpen s }) ∧ S = (F : Set ℕ).pi U }),
        x ∈ v ∧ v ⊆ u :=
      (is_topological_basis_pi fun n : ℕ => is_topological_basis_opens).exists_subset_of_mem_open hx u_open
    rcases Finset.bdd_above F with ⟨n, hn⟩
    refine' ⟨cylinder x (n + 1), ⟨x, n + 1, rfl⟩, self_mem_cylinder _ _, subset.trans _ Uu⟩
    intro y hy
    suffices ∀ i : ℕ, i ∈ F → y i ∈ U i by
      simpa
    intro i hi
    have : y i = x i := mem_cylinder_iff.1 hy i ((hn hi).trans_lt (lt_add_one n))
    rw [this]
    simp only [← Set.mem_pi, ← Finset.mem_coe] at xU
    exact xU i hi
    

variable {E}

theorem is_open_iff_dist (s : Set (∀ n, E n)) : IsOpen s ↔ ∀, ∀ x ∈ s, ∀, ∃ ε > 0, ∀ y, dist x y < ε → y ∈ s := by
  constructor
  · intro hs x hx
    obtain ⟨v, ⟨y, n, rfl⟩, h'x, h's⟩ :
      ∃ (v : Set (∀ n : ℕ, E n))(H : v ∈ { s | ∃ (x : ∀ n : ℕ, E n)(n : ℕ), s = cylinder x n }), x ∈ v ∧ v ⊆ s :=
      (is_topological_basis_cylinders E).exists_subset_of_mem_open hx hs
    rw [← mem_cylinder_iff_eq.1 h'x] at h's
    exact
      ⟨(1 / 2 : ℝ) ^ n, by
        simp , fun y hy => h's fun i hi => (apply_eq_of_dist_lt hy hi.le).symm⟩
    
  · intro h
    apply (is_topological_basis_cylinders E).is_open_iff.2 fun x hx => _
    rcases h x hx with ⟨ε, εpos, hε⟩
    obtain ⟨n, hn⟩ : ∃ n : ℕ, (1 / 2 : ℝ) ^ n < ε := exists_pow_lt_of_lt_one εpos one_half_lt_one
    refine' ⟨cylinder x n, ⟨x, n, rfl⟩, self_mem_cylinder x n, fun y hy => hε y _⟩
    rw [PiNat.dist_comm]
    exact (mem_cylinder_iff_dist_le.1 hy).trans_lt hn
    

/-- Metric space structure on `Π (n : ℕ), E n` when the spaces `E n` have the discrete topology,
where the distance is given by `dist x y = (1/2)^n`, where `n` is the smallest index where `x` and
`y` differ. Not registered as a global instance by default.
Warning: this definition makes sure that the topology is defeq to the original product topology,
but it does not take care of a possible uniformity. If the `E n` have a uniform structure, then
there will be two non-defeq uniform structures on `Π n, E n`, the product one and the one coming
from the metric structure. In this case, use `metric_space_of_discrete_uniformity` instead. -/
protected def metricSpace : MetricSpace (∀ n, E n) :=
  MetricSpace.ofMetrizable dist PiNat.dist_self PiNat.dist_comm PiNat.dist_triangle is_open_iff_dist
    PiNat.eq_of_dist_eq_zero

/-- Metric space structure on `Π (n : ℕ), E n` when the spaces `E n` have the discrete uniformity,
where the distance is given by `dist x y = (1/2)^n`, where `n` is the smallest index where `x` and
`y` differ. Not registered as a global instance by default. -/
protected def metricSpaceOfDiscreteUniformity {E : ℕ → Type _} [∀ n, UniformSpace (E n)]
    (h : ∀ n, uniformity (E n) = 𝓟 IdRel) : MetricSpace (∀ n, E n) := by
  have : ∀ n, DiscreteTopology (E n) := fun n => discrete_topology_of_discrete_uniformity (h n)
  exact
    { dist_triangle := PiNat.dist_triangle, dist_comm := PiNat.dist_comm, dist_self := PiNat.dist_self,
      eq_of_dist_eq_zero := PiNat.eq_of_dist_eq_zero, toUniformSpace := Pi.uniformSpace _,
      uniformity_dist := by
        simp [← Pi.uniformity, ← comap_infi, ← gt_iff_lt, ← preimage_set_of_eq, ← comap_principal, ←
          PseudoMetricSpace.uniformity_dist, ← h, ← IdRel]
        apply le_antisymmₓ
        · simp only [← le_infi_iff, ← le_principal_iff]
          intro ε εpos
          obtain ⟨n, hn⟩ : ∃ n, (1 / 2 : ℝ) ^ n < ε :=
            exists_pow_lt_of_lt_one εpos
              (by
                norm_num)
          apply
            @mem_infi_of_Inter _ _ _ _ _ (Finset.range n).finite_to_set fun i =>
              { p : (∀ n : ℕ, E n) × ∀ n : ℕ, E n | p.fst i = p.snd i }
          · simp only [← mem_principal, ← set_of_subset_set_of, ← imp_self, ← implies_true_iff]
            
          · rintro ⟨x, y⟩ hxy
            simp only [← Finset.mem_coe, ← Finset.mem_range, ← Inter_coe_set, ← mem_Inter, ← mem_set_of_eq] at hxy
            apply lt_of_le_of_ltₓ _ hn
            rw [← mem_cylinder_iff_dist_le, mem_cylinder_iff]
            exact hxy
            
          
        · simp only [← le_infi_iff, ← le_principal_iff]
          intro n
          refine' mem_infi_of_mem ((1 / 2) ^ n) _
          refine'
            mem_infi_of_mem
              (by
                norm_num)
              _
          simp only [← mem_principal, ← set_of_subset_set_of, ← Prod.forall]
          intro x y hxy
          exact apply_eq_of_dist_lt hxy le_rfl
           }

/-- Metric space structure on `ℕ → ℕ` where the distance is given by `dist x y = (1/2)^n`,
where `n` is the smallest index where `x` and `y` differ.
Not registered as a global instance by default. -/
def metricSpaceNatNat : MetricSpace (ℕ → ℕ) :=
  PiNat.metricSpaceOfDiscreteUniformity fun n => rfl

attribute [local instance] PiNat.metricSpace

protected theorem complete_space : CompleteSpace (∀ n, E n) := by
  refine'
    Metric.complete_of_convergent_controlled_sequences (fun n => (1 / 2) ^ n)
      (by
        simp )
      _
  intro u hu
  refine' ⟨fun n => u n n, tendsto_pi_nhds.2 fun i => _⟩
  refine' tendsto_const_nhds.congr' _
  filter_upwards [Filter.Ici_mem_at_top i] with n hn
  exact apply_eq_of_dist_lt (hu i i n le_rfl hn) le_rfl

/-!
### Retractions inside product spaces

We show that, in a space `Π (n : ℕ), E n` where each `E n` is discrete, there is a retraction on
any closed nonempty subset `s`, i.e., a continuous map `f` from the whole space to `s` restricting
to the identity on `s`. The map `f` is defined as follows. For `x ∈ s`, let `f x = x`. Otherwise,
consider the longest prefix `w` that `x` shares with an element of `s`, and let `f x = z_w`
where `z_w` is an element of `s` starting with `w`.
-/


theorem exists_disjoint_cylinder {s : Set (∀ n, E n)} (hs : IsClosed s) {x : ∀ n, E n} (hx : x ∉ s) :
    ∃ n, Disjoint s (Cylinder x n) := by
  rcases eq_empty_or_nonempty s with (rfl | hne)
  · exact
      ⟨0, by
        simp ⟩
    
  have A : 0 < inf_dist x s := (hs.not_mem_iff_inf_dist_pos hne).1 hx
  obtain ⟨n, hn⟩ : ∃ n, (1 / 2 : ℝ) ^ n < inf_dist x s := exists_pow_lt_of_lt_one A one_half_lt_one
  refine' ⟨n, _⟩
  apply disjoint_left.2 fun y ys hy => _
  apply lt_irreflₓ (inf_dist x s)
  calc inf_dist x s ≤ dist x y := inf_dist_le_dist_of_mem ys _ ≤ (1 / 2) ^ n := by
      rw [mem_cylinder_comm] at hy
      exact mem_cylinder_iff_dist_le.1 hy _ < inf_dist x s := hn

/-- Given a point `x` in a product space `Π (n : ℕ), E n`, and `s` a subset of this space, then
`shortest_prefix_diff x s` if the smallest `n` for which there is no element of `s` having the same
prefix of length `n` as `x`. If there is no such `n`, then use `0` by convention. -/
def shortestPrefixDiff {E : ℕ → Type _} (x : ∀ n, E n) (s : Set (∀ n, E n)) : ℕ :=
  if h : ∃ n, Disjoint s (Cylinder x n) then Nat.findₓ h else 0

theorem first_diff_lt_shortest_prefix_diff {s : Set (∀ n, E n)} (hs : IsClosed s) {x y : ∀ n, E n} (hx : x ∉ s)
    (hy : y ∈ s) : firstDiff x y < shortestPrefixDiff x s := by
  have A := exists_disjoint_cylinder hs hx
  rw [shortest_prefix_diff, dif_pos A]
  have B := Nat.find_specₓ A
  contrapose! B
  rw [not_disjoint_iff_nonempty_inter]
  refine' ⟨y, hy, _⟩
  rw [mem_cylinder_comm]
  exact cylinder_anti y B (mem_cylinder_first_diff x y)

theorem shortest_prefix_diff_pos {s : Set (∀ n, E n)} (hs : IsClosed s) (hne : s.Nonempty) {x : ∀ n, E n} (hx : x ∉ s) :
    0 < shortestPrefixDiff x s := by
  rcases hne with ⟨y, hy⟩
  exact (zero_le _).trans_lt (first_diff_lt_shortest_prefix_diff hs hx hy)

/-- Given a point `x` in a product space `Π (n : ℕ), E n`, and `s` a subset of this space, then
`longest_prefix x s` if the largest `n` for which there is an element of `s` having the same
prefix of length `n` as `x`. If there is no such `n`, use `0` by convention. -/
def longestPrefix {E : ℕ → Type _} (x : ∀ n, E n) (s : Set (∀ n, E n)) : ℕ :=
  shortestPrefixDiff x s - 1

theorem first_diff_le_longest_prefix {s : Set (∀ n, E n)} (hs : IsClosed s) {x y : ∀ n, E n} (hx : x ∉ s) (hy : y ∈ s) :
    firstDiff x y ≤ longestPrefix x s := by
  rw [longest_prefix, le_tsub_iff_right]
  · exact first_diff_lt_shortest_prefix_diff hs hx hy
    
  · exact shortest_prefix_diff_pos hs ⟨y, hy⟩ hx
    

theorem inter_cylinder_longest_prefix_nonempty {s : Set (∀ n, E n)} (hs : IsClosed s) (hne : s.Nonempty)
    (x : ∀ n, E n) : (s ∩ Cylinder x (longestPrefix x s)).Nonempty := by
  by_cases' hx : x ∈ s
  · exact ⟨x, hx, self_mem_cylinder _ _⟩
    
  have A := exists_disjoint_cylinder hs hx
  have B : longest_prefix x s < shortest_prefix_diff x s := Nat.pred_ltₓ (shortest_prefix_diff_pos hs hne hx).ne'
  rw [longest_prefix, shortest_prefix_diff, dif_pos A] at B⊢
  obtain ⟨y, ys, hy⟩ : ∃ y : ∀ n : ℕ, E n, y ∈ s ∧ x ∈ cylinder y (Nat.findₓ A - 1) := by
    have := Nat.find_minₓ A B
    push_neg  at this
    simp_rw [not_disjoint_iff, mem_cylinder_comm] at this
    exact this
  refine' ⟨y, ys, _⟩
  rw [mem_cylinder_iff_eq] at hy⊢
  rw [hy]

theorem disjoint_cylinder_of_longest_prefix_lt {s : Set (∀ n, E n)} (hs : IsClosed s) {x : ∀ n, E n} (hx : x ∉ s)
    {n : ℕ} (hn : longestPrefix x s < n) : Disjoint s (Cylinder x n) := by
  rcases eq_empty_or_nonempty s with (h's | hne)
  · simp [← h's]
    
  contrapose! hn
  rcases not_disjoint_iff_nonempty_inter.1 hn with ⟨y, ys, hy⟩
  apply le_transₓ _ (first_diff_le_longest_prefix hs hx ys)
  apply (mem_cylinder_iff_le_first_diff (ne_of_mem_of_not_mem ys hx).symm _).1
  rwa [mem_cylinder_comm]

/-- If two points `x, y` coincide up to length `n`, and the longest common prefix of `x` with `s`
is strictly shorter than `n`, then the longest common prefix of `y` with `s` is the same, and both
cylinders of this length based at `x` and `y` coincide. -/
theorem cylinder_longest_prefix_eq_of_longest_prefix_lt_first_diff {x y : ∀ n, E n} {s : Set (∀ n, E n)}
    (hs : IsClosed s) (hne : s.Nonempty) (H : longestPrefix x s < firstDiff x y) (xs : x ∉ s) (ys : y ∉ s) :
    Cylinder x (longestPrefix x s) = Cylinder y (longestPrefix y s) := by
  have l_eq : longest_prefix y s = longest_prefix x s := by
    rcases lt_trichotomyₓ (longest_prefix y s) (longest_prefix x s) with (L | L | L)
    · have Ax : (s ∩ cylinder x (longest_prefix x s)).Nonempty := inter_cylinder_longest_prefix_nonempty hs hne x
      have Z := disjoint_cylinder_of_longest_prefix_lt hs ys L
      rw [first_diff_comm] at H
      rw [cylinder_eq_cylinder_of_le_first_diff _ _ H.le] at Z
      exact (Ax.not_disjoint Z).elim
      
    · exact L
      
    · have Ay : (s ∩ cylinder y (longest_prefix y s)).Nonempty := inter_cylinder_longest_prefix_nonempty hs hne y
      have A'y : (s ∩ cylinder y (longest_prefix x s).succ).Nonempty :=
        Ay.mono (inter_subset_inter_right s (cylinder_anti _ L))
      have Z := disjoint_cylinder_of_longest_prefix_lt hs xs (Nat.lt_succ_selfₓ _)
      rw [cylinder_eq_cylinder_of_le_first_diff _ _ H] at Z
      exact (A'y.not_disjoint Z).elim
      
  rw [l_eq, ← mem_cylinder_iff_eq]
  exact cylinder_anti y H.le (mem_cylinder_first_diff x y)

/-- Given a closed nonempty subset `s` of `Π (n : ℕ), E n`, there exists a Lipschitz retraction
onto this set, i.e., a Lipschitz map with range equal to `s`, equal to the identity on `s`. -/
theorem exists_lipschitz_retraction_of_is_closed {s : Set (∀ n, E n)} (hs : IsClosed s) (hne : s.Nonempty) :
    ∃ f : (∀ n, E n) → ∀ n, E n, (∀, ∀ x ∈ s, ∀, f x = x) ∧ Range f = s ∧ LipschitzWith 1 f := by
  /- The map `f` is defined as follows. For `x ∈ s`, let `f x = x`. Otherwise, consider the longest
    prefix `w` that `x` shares with an element of `s`, and let `f x = z_w` where `z_w` is an element
    of `s` starting with `w`. All the desired properties are clear, except the fact that `f`
    is `1`-Lipschitz: if two points `x, y` belong to a common cylinder of length `n`, one should show
    that their images also belong to a common cylinder of length `n`. This is a case analysis:
    * if both `x, y ∈ s`, then this is clear.
    * if `x ∈ s` but `y ∉ s`, then the longest prefix `w` of `y` shared by an element of `s` is of
    length at least `n` (because of `x`), and then `f y` starts with `w` and therefore stays in the
    same length `n` cylinder.
    * if `x ∉ s`, `y ∉ s`, let `w` be the longest prefix of `x` shared by an element of `s`. If its
    length is `< n`, then it is also the longest prefix of `y`, and we get `f x = f y = z_w`.
    Otherwise, `f x` remains in the same `n`-cylinder as `x`. Similarly for `y`. Finally, `f x` and
    `f y` are again in the same `n`-cylinder, as desired. -/
  set f := fun x => if x ∈ s then x else (inter_cylinder_longest_prefix_nonempty hs hne x).some with hf
  have fs : ∀, ∀ x ∈ s, ∀, f x = x := fun x xs => by
    simp [← xs]
  refine' ⟨f, fs, _, _⟩
  -- check that the range of `f` is `s`.
  · apply subset.antisymm
    · rintro x ⟨y, rfl⟩
      by_cases' hy : y ∈ s
      · rwa [fs y hy]
        
      simpa [← hf, ← if_neg hy] using (inter_cylinder_longest_prefix_nonempty hs hne y).some_spec.1
      
    · intro x hx
      rw [← fs x hx]
      exact mem_range_self _
      
    
  -- check that `f` is `1`-Lipschitz, by a case analysis.
  · apply LipschitzWith.mk_one fun x y => _
    -- exclude the trivial cases where `x = y`, or `f x = f y`.
    rcases eq_or_ne x y with (rfl | hxy)
    · simp
      
    rcases eq_or_ne (f x) (f y) with (h' | hfxfy)
    · simp [← h', ← dist_nonneg]
      
    have I2 : cylinder x (first_diff x y) = cylinder y (first_diff x y) := by
      rw [← mem_cylinder_iff_eq]
      apply mem_cylinder_first_diff
    suffices first_diff x y ≤ first_diff (f x) (f y) by
      simpa [← dist_eq_of_ne hxy, ← dist_eq_of_ne hfxfy]
    -- case where `x ∈ s`
    by_cases' xs : x ∈ s
    · rw [fs x xs] at hfxfy⊢
      -- case where `y ∈ s`, trivial
      by_cases' ys : y ∈ s
      · rw [fs y ys]
        
      -- case where `y ∉ s`
      have A : (s ∩ cylinder y (longest_prefix y s)).Nonempty := inter_cylinder_longest_prefix_nonempty hs hne y
      have fy : f y = A.some := by
        simp_rw [hf, if_neg ys]
      have I : cylinder A.some (first_diff x y) = cylinder y (first_diff x y) := by
        rw [← mem_cylinder_iff_eq, first_diff_comm]
        apply cylinder_anti y _ A.some_spec.2
        exact first_diff_le_longest_prefix hs ys xs
      rwa [← fy, ← I2, ← mem_cylinder_iff_eq, mem_cylinder_iff_le_first_diff hfxfy.symm, first_diff_comm _ x] at I
      
    -- case where `x ∉ s`
    · by_cases' ys : y ∈ s
      -- case where `y ∈ s` (similar to the above)
      · have A : (s ∩ cylinder x (longest_prefix x s)).Nonempty := inter_cylinder_longest_prefix_nonempty hs hne x
        have fx : f x = A.some := by
          simp_rw [hf, if_neg xs]
        have I : cylinder A.some (first_diff x y) = cylinder x (first_diff x y) := by
          rw [← mem_cylinder_iff_eq]
          apply cylinder_anti x _ A.some_spec.2
          apply first_diff_le_longest_prefix hs xs ys
        rw [fs y ys] at hfxfy⊢
        rwa [← fx, I2, ← mem_cylinder_iff_eq, mem_cylinder_iff_le_first_diff hfxfy] at I
        
      -- case where `y ∉ s`
      · have Ax : (s ∩ cylinder x (longest_prefix x s)).Nonempty := inter_cylinder_longest_prefix_nonempty hs hne x
        have fx : f x = Ax.some := by
          simp_rw [hf, if_neg xs]
        have Ay : (s ∩ cylinder y (longest_prefix y s)).Nonempty := inter_cylinder_longest_prefix_nonempty hs hne y
        have fy : f y = Ay.some := by
          simp_rw [hf, if_neg ys]
        -- case where the common prefix to `x` and `s`, or `y` and `s`, is shorter than the
        -- common part to `x` and `y` -- then `f x = f y`.
        by_cases' H : longest_prefix x s < first_diff x y ∨ longest_prefix y s < first_diff x y
        · have : cylinder x (longest_prefix x s) = cylinder y (longest_prefix y s) := by
            cases H
            · exact cylinder_longest_prefix_eq_of_longest_prefix_lt_first_diff hs hne H xs ys
              
            · symm
              rw [first_diff_comm] at H
              exact cylinder_longest_prefix_eq_of_longest_prefix_lt_first_diff hs hne H ys xs
              
          rw [fx, fy] at hfxfy
          apply (hfxfy _).elim
          congr
          
        -- case where the common prefix to `x` and `s` is long, as well as the common prefix to
        -- `y` and `s`. Then all points remain in the same cylinders.
        · push_neg  at H
          have I1 : cylinder Ax.some (first_diff x y) = cylinder x (first_diff x y) := by
            rw [← mem_cylinder_iff_eq]
            exact cylinder_anti x H.1 Ax.some_spec.2
          have I3 : cylinder y (first_diff x y) = cylinder Ay.some (first_diff x y) := by
            rw [eq_comm, ← mem_cylinder_iff_eq]
            exact cylinder_anti y H.2 Ay.some_spec.2
          have : cylinder Ax.some (first_diff x y) = cylinder Ay.some (first_diff x y) := by
            rw [I1, I2, I3]
          rw [← fx, ← fy, ← mem_cylinder_iff_eq, mem_cylinder_iff_le_first_diff hfxfy] at this
          exact this
          
        
      
    

/-- Given a closed nonempty subset `s` of `Π (n : ℕ), E n`, there exists a retraction onto this
set, i.e., a continuous map with range equal to `s`, equal to the identity on `s`. -/
theorem exists_retraction_of_is_closed {s : Set (∀ n, E n)} (hs : IsClosed s) (hne : s.Nonempty) :
    ∃ f : (∀ n, E n) → ∀ n, E n, (∀, ∀ x ∈ s, ∀, f x = x) ∧ Range f = s ∧ Continuous f := by
  rcases exists_lipschitz_retraction_of_is_closed hs hne with ⟨f, fs, frange, hf⟩
  exact ⟨f, fs, frange, hf.continuous⟩

theorem exists_retraction_subtype_of_is_closed {s : Set (∀ n, E n)} (hs : IsClosed s) (hne : s.Nonempty) :
    ∃ f : (∀ n, E n) → s, (∀ x : s, f x = x) ∧ Surjective f ∧ Continuous f := by
  obtain ⟨f, fs, f_range, f_cont⟩ :
    ∃ f : (∀ n, E n) → ∀ n, E n, (∀, ∀ x ∈ s, ∀, f x = x) ∧ range f = s ∧ Continuous f :=
    exists_retraction_of_is_closed hs hne
  have A : ∀ x, f x ∈ s := by
    simp [f_range]
  have B : ∀ x : s, cod_restrict f s A x = x := by
    intro x
    apply subtype.coe_injective.eq_iff.1
    simpa only using fs x.val x.property
  exact ⟨cod_restrict f s A, B, fun x => ⟨x, B x⟩, continuous_subtype_mk _ f_cont⟩

end PiNat

open PiNat

/-- Any nonempty complete second countable metric space is the continuous image of the
fundamental space `ℕ → ℕ`. For a version of this theorem in the context of Polish spaces, see
`exists_nat_nat_continuous_surjective_of_polish_space`. -/
theorem exists_nat_nat_continuous_surjective_of_complete_space (α : Type _) [MetricSpace α] [CompleteSpace α]
    [SecondCountableTopology α] [Nonempty α] : ∃ f : (ℕ → ℕ) → α, Continuous f ∧ Surjective f := by
  /- First, we define a surjective map from a closed subset `s` of `ℕ → ℕ`. Then, we compose
    this map with a retraction of `ℕ → ℕ` onto `s` to obtain the desired map.
    Let us consider a dense sequence `u` in `α`. Then `s` is the set of sequences `xₙ` such that the
    balls `closed_ball (u xₙ) (1/2^n)` have a nonempty intersection. This set is closed, and we define
    `f x` there to be the unique point in the intersection. This function is continuous and surjective
    by design. -/
  let this : MetricSpace (ℕ → ℕ) := PiNat.metricSpaceNatNat
  have I0 : (0 : ℝ) < 1 / 2 := by
    norm_num
  have I1 : (1 / 2 : ℝ) < 1 := by
    norm_num
  rcases exists_dense_seq α with ⟨u, hu⟩
  let s : Set (ℕ → ℕ) := { x | (⋂ n : ℕ, closed_ball (u (x n)) ((1 / 2) ^ n)).Nonempty }
  let g : s → α := fun x => x.2.some
  have A : ∀ (x : s) (n : ℕ), dist (g x) (u ((x : ℕ → ℕ) n)) ≤ (1 / 2) ^ n := fun x n =>
    (mem_Inter.1 x.2.some_mem n : _)
  have g_cont : Continuous g := by
    apply continuous_iff_continuous_at.2 fun y => _
    apply continuous_at_of_locally_lipschitz zero_lt_one 4 fun x hxy => _
    rcases eq_or_ne x y with (rfl | hne)
    · simp
      
    have hne' : x.1 ≠ y.1 := subtype.coe_injective.ne hne
    have dist' : dist x y = dist x.1 y.1 := rfl
    let n := first_diff x.1 y.1 - 1
    have diff_pos : 0 < first_diff x.1 y.1 := by
      by_contra' h
      apply apply_first_diff_ne hne'
      rw [le_zero_iff.1 h]
      apply apply_eq_of_dist_lt _ le_rfl
      exact hxy
    have hn : first_diff x.1 y.1 = n + 1 := (Nat.succ_pred_eq_of_posₓ diff_pos).symm
    rw [dist', dist_eq_of_ne hne', hn]
    have B : x.1 n = y.1 n := mem_cylinder_first_diff x.1 y.1 n (Nat.pred_ltₓ diff_pos.ne')
    calc dist (g x) (g y) ≤ dist (g x) (u (x.1 n)) + dist (g y) (u (x.1 n)) :=
        dist_triangle_right _ _ _ _ = dist (g x) (u (x.1 n)) + dist (g y) (u (y.1 n)) := by
        rw [← B]_ ≤ (1 / 2) ^ n + (1 / 2) ^ n := add_le_add (A x n) (A y n)_ = 4 * (1 / 2) ^ (n + 1) := by
        ring_exp
  have g_surj : surjective g := by
    intro y
    have : ∀ n : ℕ, ∃ j, y ∈ closed_ball (u j) ((1 / 2) ^ n) := by
      intro n
      rcases hu.exists_dist_lt y
          (by
            simp : (0 : ℝ) < (1 / 2) ^ n) with
        ⟨j, hj⟩
      exact ⟨j, hj.le⟩
    choose x hx using this
    have I : (⋂ n : ℕ, closed_ball (u (x n)) ((1 / 2) ^ n)).Nonempty := ⟨y, mem_Inter.2 hx⟩
    refine' ⟨⟨x, I⟩, _⟩
    refine' dist_le_zero.1 _
    have J : ∀ n : ℕ, dist (g ⟨x, I⟩) y ≤ (1 / 2) ^ n + (1 / 2) ^ n := fun n =>
      calc
        dist (g ⟨x, I⟩) y ≤ dist (g ⟨x, I⟩) (u (x n)) + dist y (u (x n)) := dist_triangle_right _ _ _
        _ ≤ (1 / 2) ^ n + (1 / 2) ^ n := add_le_add (A ⟨x, I⟩ n) (hx n)
        
    have L : tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n + (1 / 2) ^ n) at_top (𝓝 (0 + 0)) :=
      (tendsto_pow_at_top_nhds_0_of_lt_1 I0.le I1).add (tendsto_pow_at_top_nhds_0_of_lt_1 I0.le I1)
    rw [add_zeroₓ] at L
    exact ge_of_tendsto' L J
  have s_closed : IsClosed s := by
    refine' is_closed_iff_cluster_pt.mpr _
    intro x hx
    have L : tendsto (fun n : ℕ => diam (closed_ball (u (x n)) ((1 / 2) ^ n))) at_top (𝓝 0) := by
      have : tendsto (fun n : ℕ => (2 : ℝ) * (1 / 2) ^ n) at_top (𝓝 (2 * 0)) :=
        (tendsto_pow_at_top_nhds_0_of_lt_1 I0.le I1).const_mul _
      rw [mul_zero] at this
      exact squeeze_zero (fun n => diam_nonneg) (fun n => diam_closed_ball (pow_nonneg I0.le _)) this
    refine' nonempty_Inter_of_nonempty_bInter (fun n => is_closed_ball) (fun n => bounded_closed_ball) _ L
    intro N
    obtain ⟨y, hxy, ys⟩ : ∃ y, y ∈ ball x ((1 / 2) ^ N) ∩ s :=
      cluster_pt_principal_iff.1 hx _ (ball_mem_nhds x (pow_pos I0 N))
    have E :
      (⋂ (n : ℕ) (H : n ≤ N), closed_ball (u (x n)) ((1 / 2) ^ n)) =
        ⋂ (n : ℕ) (H : n ≤ N), closed_ball (u (y n)) ((1 / 2) ^ n) :=
      by
      congr
      ext1 n
      congr
      ext1 hn
      have : x n = y n := apply_eq_of_dist_lt (mem_ball'.1 hxy) hn
      rw [this]
    rw [E]
    apply nonempty.mono _ ys
    apply Inter_subset_Inter₂
  obtain ⟨f, -, f_surj, f_cont⟩ : ∃ f : (ℕ → ℕ) → s, (∀ x : s, f x = x) ∧ surjective f ∧ Continuous f := by
    apply exists_retraction_subtype_of_is_closed s_closed
    simpa only [← nonempty_coe_sort] using g_surj.nonempty
  exact ⟨g ∘ f, g_cont.comp f_cont, g_surj.comp f_surj⟩

namespace PiCountable

/-!
### Products of (possibly non-discrete) metric spaces
-/


variable {ι : Type _} [Encodable ι] {F : ι → Type _} [∀ i, MetricSpace (F i)]

open Encodable

/-- Given a countable family of metric spaces, one may put a distance on their product `Π i, E i`.
It is highly non-canonical, though, and therefore not registered as a global instance.
The distance we use here is `dist x y = ∑' i, min (1/2)^(encode i) (dist (x i) (y i))`. -/
protected def hasDist : HasDist (∀ i, F i) :=
  ⟨fun x y => ∑' i : ι, min ((1 / 2) ^ encode i) (dist (x i) (y i))⟩

attribute [local instance] PiCountable.hasDist

theorem dist_eq_tsum (x y : ∀ i, F i) : dist x y = ∑' i : ι, min ((1 / 2) ^ encode i) (dist (x i) (y i)) :=
  rfl

theorem dist_summable (x y : ∀ i, F i) : Summable fun i : ι => min ((1 / 2) ^ encode i) (dist (x i) (y i)) := by
  refine' summable_of_nonneg_of_le (fun i => _) (fun i => min_le_leftₓ _ _) summable_geometric_two_encode
  exact
    le_minₓ
      (pow_nonneg
        (by
          norm_num)
        _)
      dist_nonneg

theorem min_dist_le_dist_pi (x y : ∀ i, F i) (i : ι) : min ((1 / 2) ^ encode i) (dist (x i) (y i)) ≤ dist x y :=
  le_tsum (dist_summable x y) i fun j hj =>
    le_minₓ
      (by
        simp )
      dist_nonneg

theorem dist_le_dist_pi_of_dist_lt {x y : ∀ i, F i} {i : ι} (h : dist x y < (1 / 2) ^ encode i) :
    dist (x i) (y i) ≤ dist x y := by
  simpa only [← not_leₓ.2 h, ← false_orₓ] using min_le_iff.1 (min_dist_le_dist_pi x y i)

open BigOperators TopologicalSpace

open Filter

open Nnreal

variable (E)

/-- Given a countable family of metric spaces, one may put a distance on their product `Π i, E i`,
defining the right topology and uniform structure. It is highly non-canonical, though, and therefore
not registered as a global instance.
The distance we use here is `dist x y = ∑' n, min (1/2)^(encode i) (dist (x n) (y n))`. -/
protected def metricSpace : MetricSpace (∀ i, F i) where
  dist_self := fun x => by
    simp [← dist_eq_tsum]
  dist_comm := fun x y => by
    simp [← dist_eq_tsum, ← dist_comm]
  dist_triangle := fun x y z => by
    have I :
      ∀ i,
        min ((1 / 2) ^ encode i) (dist (x i) (z i)) ≤
          min ((1 / 2) ^ encode i) (dist (x i) (y i)) + min ((1 / 2) ^ encode i) (dist (y i) (z i)) :=
      fun i =>
      calc
        min ((1 / 2) ^ encode i) (dist (x i) (z i)) ≤ min ((1 / 2) ^ encode i) (dist (x i) (y i) + dist (y i) (z i)) :=
          min_le_min le_rfl (dist_triangle _ _ _)
        _ =
            min ((1 / 2) ^ encode i)
              (min ((1 / 2) ^ encode i) (dist (x i) (y i)) + min ((1 / 2) ^ encode i) (dist (y i) (z i))) :=
          by
          convert
              congr_arg (coe : ℝ≥0 → ℝ)
                (min_add_distrib ((1 / 2 : ℝ≥0 ) ^ encode i) (nndist (x i) (y i)) (nndist (y i) (z i))) <;>
            simp
        _ ≤ min ((1 / 2) ^ encode i) (dist (x i) (y i)) + min ((1 / 2) ^ encode i) (dist (y i) (z i)) :=
          min_le_rightₓ _ _
        
    calc dist x z ≤ ∑' i, min ((1 / 2) ^ encode i) (dist (x i) (y i)) + min ((1 / 2) ^ encode i) (dist (y i) (z i)) :=
        tsum_le_tsum I (dist_summable x z) ((dist_summable x y).add (dist_summable y z))_ = dist x y + dist y z :=
        tsum_add (dist_summable x y) (dist_summable y z)
  eq_of_dist_eq_zero := by
    intro x y hxy
    ext1 n
    rw [← dist_le_zero, ← hxy]
    apply dist_le_dist_pi_of_dist_lt
    rw [hxy]
    simp
  toUniformSpace := Pi.uniformSpace _
  uniformity_dist := by
    have I0 : (0 : ℝ) ≤ 1 / 2 := by
      norm_num
    have I1 : (1 / 2 : ℝ) < 1 := by
      norm_num
    simp only [← Pi.uniformity, ← comap_infi, ← gt_iff_lt, ← preimage_set_of_eq, ← comap_principal, ←
      PseudoMetricSpace.uniformity_dist]
    apply le_antisymmₓ
    · simp only [← le_infi_iff, ← le_principal_iff]
      intro ε εpos
      obtain ⟨K, hK⟩ : ∃ K : Finset ι, (∑' i : { j // j ∉ K }, (1 / 2 : ℝ) ^ encode (i : ι)) < ε / 2 :=
        ((tendsto_order.1 (tendsto_tsum_compl_at_top_zero fun i : ι => (1 / 2 : ℝ) ^ encode i)).2 _
            (half_pos εpos)).exists
      obtain ⟨δ, δpos, hδ⟩ : ∃ (δ : ℝ)(δpos : 0 < δ), (K.card : ℝ) * δ ≤ ε / 2 := by
        rcases Nat.eq_zero_or_posₓ K.card with (hK | hK)
        · exact
            ⟨1, zero_lt_one, by
              simpa only [← hK, ← Nat.cast_zeroₓ, ← zero_mul] using (half_pos εpos).le⟩
          
        · have Kpos : 0 < (K.card : ℝ) := Nat.cast_pos.2 hK
          refine' ⟨ε / 2 / (K.card : ℝ), div_pos (half_pos εpos) Kpos, le_of_eqₓ _⟩
          field_simp [← Kpos.ne']
          ring
          
      apply
        @mem_infi_of_Inter _ _ _ _ _ K.finite_to_set fun i =>
          { p : (∀ i : ι, F i) × ∀ i : ι, F i | dist (p.fst i) (p.snd i) < δ }
      · rintro ⟨i, hi⟩
        refine' mem_infi_of_mem δ (mem_infi_of_mem δpos _)
        simp only [← Prod.forall, ← imp_self, ← mem_principal]
        
      · rintro ⟨x, y⟩ hxy
        simp only [← mem_Inter, ← mem_set_of_eq, ← SetCoe.forall, ← Finset.mem_range, ← Finset.mem_coe] at hxy
        calc dist x y = ∑' i : ι, min ((1 / 2) ^ encode i) (dist (x i) (y i)) :=
            rfl _ =
              (∑ i in K, min ((1 / 2) ^ encode i) (dist (x i) (y i))) +
                ∑' i : (↑K : Set ι)ᶜ, min ((1 / 2) ^ encode (i : ι)) (dist (x i) (y i)) :=
            (sum_add_tsum_compl
                (dist_summable _
                  _)).symm _ ≤ (∑ i in K, dist (x i) (y i)) + ∑' i : (↑K : Set ι)ᶜ, (1 / 2) ^ encode (i : ι) :=
            by
            refine' add_le_add (Finset.sum_le_sum fun i hi => min_le_rightₓ _ _) _
            refine' tsum_le_tsum (fun i => min_le_leftₓ _ _) _ _
            · apply Summable.subtype (dist_summable x y) ((↑K : Set ι)ᶜ)
              
            · apply Summable.subtype summable_geometric_two_encode ((↑K : Set ι)ᶜ)
              _ < (∑ i in K, δ) + ε / 2 :=
            by
            apply add_lt_add_of_le_of_lt _ hK
            apply Finset.sum_le_sum fun i hi => _
            apply (hxy i _).le
            simpa using hi _ ≤ ε / 2 + ε / 2 :=
            add_le_add_right
              (by
                simpa only [← Finset.sum_const, ← nsmul_eq_mul] using hδ)
              _ _ = ε :=
            add_halves _
        
      
    · simp only [← le_infi_iff, ← le_principal_iff]
      intro i ε εpos
      refine' mem_infi_of_mem (min ((1 / 2) ^ encode i) ε) _
      have : 0 < min ((1 / 2) ^ encode i) ε :=
        lt_minₓ
          (by
            simp )
          εpos
      refine' mem_infi_of_mem this _
      simp only [← and_imp, ← Prod.forall, ← set_of_subset_set_of, ← lt_min_iff, ← mem_principal]
      intro x y hn hε
      calc dist (x i) (y i) ≤ dist x y := dist_le_dist_pi_of_dist_lt hn _ < ε := hε
      

end PiCountable

