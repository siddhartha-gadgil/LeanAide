/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathbin.MeasureTheory.Covering.Differentiation
import Mathbin.MeasureTheory.Covering.VitaliFamily
import Mathbin.MeasureTheory.Integral.Lebesgue
import Mathbin.MeasureTheory.Measure.Regular
import Mathbin.SetTheory.Ordinal.Arithmetic
import Mathbin.Topology.MetricSpace.Basic

/-!
# Besicovitch covering theorems

The topological Besicovitch covering theorem ensures that, in a nice metric space, there exists a
number `N` such that, from any family of balls with bounded radii, one can extract `N` families,
each made of disjoint balls, covering together all the centers of the initial family.

By "nice metric space", we mean a technical property stated as follows: there exists no satellite
configuration of `N + 1` points (with a given parameter `τ > 1`). Such a configuration is a family
of `N + 1` balls, where the first `N` balls all intersect the last one, but none of them contains
the center of another one and their radii are controlled. This property is for instance
satisfied by finite-dimensional real vector spaces.

In this file, we prove the topological Besicovitch covering theorem,
in `besicovitch.exist_disjoint_covering_families`.

The measurable Besicovitch theorem ensures that, in the same class of metric spaces, if at every
point one considers a class of balls of arbitrarily small radii, called admissible balls, then
one can cover almost all the space by a family of disjoint admissible balls.
It is deduced from the topological Besicovitch theorem, and proved
in `besicovitch.exists_disjoint_closed_ball_covering_ae`.

This implies that balls of small radius form a Vitali family in such spaces. Therefore, theorems
on differentiation of measures hold as a consequence of general results. We restate them in this
context to make them more easily usable.

## Main definitions and results

* `satellite_config α N τ` is the type of all satellite configurations of `N + 1` points
  in the metric space `α`, with parameter `τ`.
* `has_besicovitch_covering` is a class recording that there exist `N` and `τ > 1` such that
  there is no satellite configuration of `N + 1` points with parameter `τ`.
* `exist_disjoint_covering_families` is the topological Besicovitch covering theorem: from any
  family of balls one can extract finitely many disjoint subfamilies covering the same set.
* `exists_disjoint_closed_ball_covering` is the measurable Besicovitch covering theorem: from any
  family of balls with arbitrarily small radii at every point, one can extract countably many
  disjoint balls covering almost all the space. While the value of `N` is relevant for the precise
  statement of the topological Besicovitch theorem, it becomes irrelevant for the measurable one.
  Therefore, this statement is expressed using the `Prop`-valued
  typeclass `has_besicovitch_covering`.

We also restate the following specialized versions of general theorems on differentiation of
measures:
* `besicovitch.ae_tendsto_rn_deriv` ensures that `ρ (closed_ball x r) / μ (closed_ball x r)` tends
  almost surely to the Radon-Nikodym derivative of `ρ` with respect to `μ` at `x`.
* `besicovitch.ae_tendsto_measure_inter_div` states that almost every point in an arbitrary set `s`
  is a Lebesgue density point, i.e., `μ (s ∩ closed_ball x r) / μ (closed_ball x r)` tends to `1` as
  `r` tends to `0`. A stronger version for measurable sets is given in
  `besicovitch.ae_tendsto_measure_inter_div_of_measurable_set`.

## Implementation

#### Sketch of proof of the topological Besicovitch theorem:

We choose balls in a greedy way. First choose a ball with maximal radius (or rather, since there
is no guarantee the maximal radius is realized, a ball with radius within a factor `τ` of the
supremum). Then, remove all balls whose center is covered by the first ball, and choose among the
remaining ones a ball with radius close to maximum. Go on forever until there is no available
center (this is a transfinite induction in general).

Then define inductively a coloring of the balls. A ball will be of color `i` if it intersects
already chosen balls of color `0`, ..., `i - 1`, but none of color `i`. In this way, balls of the
same color form a disjoint family, and the space is covered by the families of the different colors.

The nontrivial part is to show that at most `N` colors are used. If one needs `N + 1` colors,
consider the first time this happens. Then the corresponding ball intersects `N` balls of the
different colors. Moreover, the inductive construction ensures that the radii of all the balls are
controlled: they form a satellite configuration with `N + 1` balls (essentially by definition of
satellite configurations). Since we assume that there are no such configurations, this is a
contradiction.

#### Sketch of proof of the measurable Besicovitch theorem:

From the topological Besicovitch theorem, one can find a disjoint countable family of balls
covering a proportion `> 1 / (N + 1)` of the space. Taking a large enough finite subset of these
balls, one gets the same property for finitely many balls. Their union is closed. Therefore, any
point in the complement has around it an admissible ball not intersecting these finitely many balls.
Applying again the topological Besicovitch theorem, one extracts from these a disjoint countable
subfamily covering a proportion `> 1 / (N + 1)` of the remaining points, and then even a disjoint
finite subfamily. Then one goes on again and again, covering at each step a positive proportion of
the remaining points, while remaining disjoint from the already chosen balls. The union of all these
balls is the desired almost everywhere covering.
-/


noncomputable section

universe u

open Metric Set Filter Finₓ MeasureTheory TopologicalSpace

open TopologicalSpace Classical BigOperators Ennreal MeasureTheory Nnreal

/-!
### Satellite configurations
-/


/-- A satellite configuration is a configuration of `N+1` points that shows up in the inductive
construction for the Besicovitch covering theorem. It depends on some parameter `τ ≥ 1`.

This is a family of balls (indexed by `i : fin N.succ`, with center `c i` and radius `r i`) such
that the last ball intersects all the other balls (condition `inter`),
and given any two balls there is an order between them, ensuring that the first ball does not
contain the center of the other one, and the radius of the second ball can not be larger than
the radius of the first ball (up to a factor `τ`). This order corresponds to the order of choice
in the inductive construction: otherwise, the second ball would have been chosen before.
This is the condition `h`.

Finally, the last ball is chosen after all the other ones, meaning that `h` can be strengthened
by keeping only one side of the alternative in `hlast`.
-/
structure Besicovitch.SatelliteConfig (α : Type _) [MetricSpace α] (N : ℕ) (τ : ℝ) where
  c : Finₓ N.succ → α
  R : Finₓ N.succ → ℝ
  rpos : ∀ i, 0 < r i
  h : ∀ i j, i ≠ j → r i ≤ dist (c i) (c j) ∧ r j ≤ τ * r i ∨ r j ≤ dist (c j) (c i) ∧ r i ≤ τ * r j
  hlast : ∀, ∀ i < last N, ∀, r i ≤ dist (c i) (c (last N)) ∧ r (last N) ≤ τ * r i
  inter : ∀, ∀ i < last N, ∀, dist (c i) (c (last N)) ≤ r i + r (last N)

-- ./././Mathport/Syntax/Translate/Basic.lean:1440:30: infer kinds are unsupported in Lean 4: #[`no_satellite_config] []
/-- A metric space has the Besicovitch covering property if there exist `N` and `τ > 1` such that
there are no satellite configuration of parameter `τ` with `N+1` points. This is the condition that
guarantees that the measurable Besicovitch covering theorem holds. It is satified by
finite-dimensional real vector spaces. -/
class HasBesicovitchCovering (α : Type _) [MetricSpace α] : Prop where
  no_satellite_config : ∃ (N : ℕ)(τ : ℝ), 1 < τ ∧ IsEmpty (Besicovitch.SatelliteConfig α N τ)

/-- There is always a satellite configuration with a single point. -/
instance {α : Type _} {τ : ℝ} [Inhabited α] [MetricSpace α] : Inhabited (Besicovitch.SatelliteConfig α 0 τ) :=
  ⟨{ c := default, R := fun i => 1, rpos := fun i => zero_lt_one,
      h := fun i j hij => (hij (Subsingleton.elimₓ i j)).elim,
      hlast := fun i hi => by
        rw [Subsingleton.elimₓ i (last 0)] at hi
        exact (lt_irreflₓ _ hi).elim,
      inter := fun i hi => by
        rw [Subsingleton.elimₓ i (last 0)] at hi
        exact (lt_irreflₓ _ hi).elim }⟩

namespace Besicovitch

namespace SatelliteConfig

variable {α : Type _} [MetricSpace α] {N : ℕ} {τ : ℝ} (a : SatelliteConfig α N τ)

theorem inter' (i : Finₓ N.succ) : dist (a.c i) (a.c (last N)) ≤ a.R i + a.R (last N) := by
  rcases lt_or_leₓ i (last N) with (H | H)
  · exact a.inter i H
    
  · have I : i = last N := top_le_iff.1 H
    have := (a.rpos (last N)).le
    simp only [← I, ← add_nonneg this this, ← dist_self]
    

theorem hlast' (i : Finₓ N.succ) (h : 1 ≤ τ) : a.R (last N) ≤ τ * a.R i := by
  rcases lt_or_leₓ i (last N) with (H | H)
  · exact (a.hlast i H).2
    
  · have : i = last N := top_le_iff.1 H
    rw [this]
    exact le_mul_of_one_le_left (a.rpos _).le h
    

end SatelliteConfig

/-! ### Extracting disjoint subfamilies from a ball covering -/


/-- A ball package is a family of balls in a metric space with positive bounded radii. -/
structure BallPackage (β : Type _) (α : Type _) where
  c : β → α
  R : β → ℝ
  rpos : ∀ b, 0 < r b
  rBound : ℝ
  r_le : ∀ b, r b ≤ r_bound

/-- The ball package made of unit balls. -/
def unitBallPackage (α : Type _) : BallPackage α α where
  c := id
  R := fun _ => 1
  rpos := fun _ => zero_lt_one
  rBound := 1
  r_le := fun _ => le_rfl

instance (α : Type _) : Inhabited (BallPackage α α) :=
  ⟨unitBallPackage α⟩

/-- A Besicovitch tau-package is a family of balls in a metric space with positive bounded radii,
together with enough data to proceed with the Besicovitch greedy algorithm. We register this in
a single structure to make sure that all our constructions in this algorithm only depend on
one variable. -/
structure TauPackage (β : Type _) (α : Type _) extends BallPackage β α where
  τ : ℝ
  one_lt_tau : 1 < τ

instance (α : Type _) : Inhabited (TauPackage α α) :=
  ⟨{ unitBallPackage α with τ := 2, one_lt_tau := one_lt_two }⟩

variable {α : Type _} [MetricSpace α] {β : Type u}

namespace TauPackage

variable [Nonempty β] (p : TauPackage β α)

include p

/-- Choose inductively large balls with centers that are not contained in the union of already
chosen balls. This is a transfinite induction. -/
noncomputable def index : Ordinal.{u} → β
  |
  i =>-- `Z` is the set of points that are covered by already constructed balls
    let Z := ⋃ j : { j // j < i }, Ball (p.c (index j)) (p.R (index j))
    let
      R :=-- `R` is the supremum of the radii of balls with centers not in `Z`
        supr
        fun b : { b : β // p.c b ∉ Z } => p.R b
    -- return an index `b` for which the center `c b` is not in `Z`, and the radius is at
      -- least `R / τ`, if such an index exists (and garbage otherwise).
      Classical.epsilon
      fun b : β => p.c b ∉ Z ∧ R ≤ p.τ * p.R b

/-- The set of points that are covered by the union of balls selected at steps `< i`. -/
def UnionUpTo (i : Ordinal.{u}) : Set α :=
  ⋃ j : { j // j < i }, Ball (p.c (p.index j)) (p.R (p.index j))

theorem monotone_Union_up_to : Monotone p.UnionUpTo := by
  intro i j hij
  simp only [← Union_up_to]
  exact Union_mono' fun r => ⟨⟨r, r.2.trans_le hij⟩, subset.rfl⟩

/-- Supremum of the radii of balls whose centers are not yet covered at step `i`. -/
def r (i : Ordinal.{u}) : ℝ :=
  supr fun b : { b : β // p.c b ∉ p.UnionUpTo i } => p.R b

/-- Group the balls into disjoint families, by assigning to a ball the smallest color for which
it does not intersect any already chosen ball of this color. -/
noncomputable def color : Ordinal.{u} → ℕ
  | i =>
    let A : Set ℕ :=
      ⋃ (j : { j // j < i }) (hj :
        (ClosedBall (p.c (p.index j)) (p.R (p.index j)) ∩ ClosedBall (p.c (p.index i)) (p.R (p.index i))).Nonempty),
        {color j}
    inf (univ \ A)

/-- `p.last_step` is the first ordinal where the construction stops making sense, i.e., `f` returns
garbage since there is no point left to be chosen. We will only use ordinals before this step. -/
def lastStep : Ordinal.{u} :=
  inf { i | ¬∃ b : β, p.c b ∉ p.UnionUpTo i ∧ p.r i ≤ p.τ * p.R b }

theorem last_step_nonempty : { i | ¬∃ b : β, p.c b ∉ p.UnionUpTo i ∧ p.r i ≤ p.τ * p.R b }.Nonempty := by
  by_contra
  suffices H : Function.Injective p.index
  exact not_injective_of_ordinal p.index H
  intro x y hxy
  wlog x_le_y : x ≤ y := le_totalₓ x y using x y, y x
  rcases eq_or_lt_of_le x_le_y with (rfl | H)
  · rfl
    
  simp only [← nonempty_def, ← not_exists, ← exists_prop, ← not_and, ← not_ltₓ, ← not_leₓ, ← mem_set_of_eq, ←
    not_forall] at h
  specialize h y
  have A : p.c (p.index y) ∉ p.Union_up_to y := by
    have : p.index y = Classical.epsilon fun b : β => p.c b ∉ p.Union_up_to y ∧ p.R y ≤ p.τ * p.r b := by
      rw [tau_package.index]
      rfl
    rw [this]
    exact (Classical.epsilon_spec h).1
  simp only [← Union_up_to, ← not_exists, ← exists_prop, ← mem_Union, ← mem_closed_ball, ← not_and, ← not_leₓ, ←
    Subtype.exists, ← Subtype.coe_mk] at A
  specialize A x H
  simp [← hxy] at A
  exact (lt_irreflₓ _ ((p.rpos (p.index y)).trans_le A)).elim

/-- Every point is covered by chosen balls, before `p.last_step`. -/
theorem mem_Union_up_to_last_step (x : β) : p.c x ∈ p.UnionUpTo p.lastStep := by
  have A : ∀ z : β, p.c z ∈ p.Union_up_to p.last_step ∨ p.τ * p.r z < p.R p.last_step := by
    have : p.last_step ∈ { i | ¬∃ b : β, p.c b ∉ p.Union_up_to i ∧ p.R i ≤ p.τ * p.r b } := Inf_mem p.last_step_nonempty
    simpa only [← not_exists, ← mem_set_of_eq, ← not_and_distrib, ← not_leₓ, ← not_not_mem]
  by_contra
  rcases A x with (H | H)
  · exact h H
    
  have Rpos : 0 < p.R p.last_step := by
    apply lt_transₓ (mul_pos (_root_.zero_lt_one.trans p.one_lt_tau) (p.rpos _)) H
  have B : p.τ⁻¹ * p.R p.last_step < p.R p.last_step := by
    conv_rhs => rw [← one_mulₓ (p.R p.last_step)]
    exact mul_lt_mul (inv_lt_one p.one_lt_tau) le_rfl Rpos zero_le_one
  obtain ⟨y, hy1, hy2⟩ : ∃ y : β, p.c y ∉ p.Union_up_to p.last_step ∧ p.τ⁻¹ * p.R p.last_step < p.r y := by
    simpa only [← exists_prop, ← mem_range, ← exists_exists_and_eq_and, ← Subtype.exists, ← Subtype.coe_mk] using
      exists_lt_of_lt_cSup _ B
    rw [← image_univ, nonempty_image_iff]
    exact ⟨⟨_, h⟩, mem_univ _⟩
  rcases A y with (Hy | Hy)
  · exact hy1 Hy
    
  · rw [← div_eq_inv_mul] at hy2
    have := (div_le_iff' (_root_.zero_lt_one.trans p.one_lt_tau)).1 hy2.le
    exact lt_irreflₓ _ (Hy.trans_le this)
    

/-- If there are no configurations of satellites with `N+1` points, one never uses more than `N`
distinct families in the Besicovitch inductive construction. -/
theorem color_lt {i : Ordinal.{u}} (hi : i < p.lastStep) {N : ℕ} (hN : IsEmpty (SatelliteConfig α N p.τ)) :
    p.Color i < N := by
  /- By contradiction, consider the first ordinal `i` for which one would have `p.color i = N`.
    Choose for each `k < N` a ball with color `k` that intersects the ball at color `i`
    (there is such a ball, otherwise one would have used the color `k` and not `N`).
    Then this family of `N+1` balls forms a satellite configuration, which is forbidden by
    the assumption `hN`. -/
  induction' i using Ordinal.induction with i IH
  let A : Set ℕ :=
    ⋃ (j : { j // j < i }) (hj :
      (closed_ball (p.c (p.index j)) (p.r (p.index j)) ∩ closed_ball (p.c (p.index i)) (p.r (p.index i))).Nonempty),
      {p.color j}
  have color_i : p.color i = Inf (univ \ A) := by
    rw [color]
  rw [color_i]
  have N_mem : N ∈ univ \ A := by
    simp only [← not_exists, ← true_andₓ, ← exists_prop, ← mem_Union, ← mem_singleton_iff, ← mem_closed_ball, ← not_and,
      ← mem_univ, ← mem_diff, ← Subtype.exists, ← Subtype.coe_mk]
    intro j ji hj
    exact (IH j ji (ji.trans hi)).ne'
  suffices Inf (univ \ A) ≠ N by
    rcases(cInf_le (OrderBot.bdd_below (univ \ A)) N_mem).lt_or_eq with (H | H)
    · exact H
      
    · exact (this H).elim
      
  intro Inf_eq_N
  have :
    ∀ k,
      k < N →
        ∃ j,
          j < i ∧
            (closed_ball (p.c (p.index j)) (p.r (p.index j)) ∩
                  closed_ball (p.c (p.index i)) (p.r (p.index i))).Nonempty ∧
              k = p.color j :=
    by
    intro k hk
    rw [← Inf_eq_N] at hk
    have : k ∈ A := by
      simpa only [← true_andₓ, ← mem_univ, ← not_not, ← mem_diff] using Nat.not_mem_of_lt_Inf hk
    simp at this
    simpa only [← exists_prop, ← mem_Union, ← mem_singleton_iff, ← mem_closed_ball, ← Subtype.exists, ← Subtype.coe_mk]
  choose! g hg using this
  -- Choose for each `k < N` an ordinal `G k < i`  giving a ball of color `k` intersecting
  -- the last ball.
  let G : ℕ → Ordinal := fun n => if n = N then i else g n
  have color_G : ∀ n, n ≤ N → p.color (G n) = n := by
    intro n hn
    rcases hn.eq_or_lt with (rfl | H)
    · simp only [← G]
      simp only [← color_i, ← Inf_eq_N, ← if_true, ← eq_self_iff_true]
      
    · simp only [← G]
      simp only [← H.ne, ← (hg n H).right.right.symm, ← if_false]
      
  have G_lt_last : ∀ n, n ≤ N → G n < p.last_step := by
    intro n hn
    rcases hn.eq_or_lt with (rfl | H)
    · simp only [← G]
      simp only [← hi, ← if_true, ← eq_self_iff_true]
      
    · simp only [← G]
      simp only [← H.ne, ← (hg n H).left.trans hi, ← if_false]
      
  have fGn : ∀ n, n ≤ N → p.c (p.index (G n)) ∉ p.Union_up_to (G n) ∧ p.R (G n) ≤ p.τ * p.r (p.index (G n)) := by
    intro n hn
    have : p.index (G n) = Classical.epsilon fun t => p.c t ∉ p.Union_up_to (G n) ∧ p.R (G n) ≤ p.τ * p.r t := by
      rw [index]
      rfl
    rw [this]
    have : ∃ t, p.c t ∉ p.Union_up_to (G n) ∧ p.R (G n) ≤ p.τ * p.r t := by
      simpa only [← not_exists, ← exists_prop, ← not_and, ← not_ltₓ, ← not_leₓ, ← mem_set_of_eq, ← not_forall] using
        not_mem_of_lt_cInf (G_lt_last n hn) (OrderBot.bdd_below _)
    exact Classical.epsilon_spec this
  -- the balls with indices `G k` satisfy the characteristic property of satellite configurations.
  have Gab :
    ∀ a b : Finₓ (Nat.succ N),
      G a < G b →
        p.r (p.index (G a)) ≤ dist (p.c (p.index (G a))) (p.c (p.index (G b))) ∧
          p.r (p.index (G b)) ≤ p.τ * p.r (p.index (G a)) :=
    by
    intro a b G_lt
    have ha : (a : ℕ) ≤ N := Nat.lt_succ_iffₓ.1 a.2
    have hb : (b : ℕ) ≤ N := Nat.lt_succ_iffₓ.1 b.2
    constructor
    · have := (fGn b hb).1
      simp only [← Union_up_to, ← not_exists, ← exists_prop, ← mem_Union, ← mem_closed_ball, ← not_and, ← not_leₓ, ←
        Subtype.exists, ← Subtype.coe_mk] at this
      simpa only [← dist_comm, ← mem_ball, ← not_ltₓ] using this (G a) G_lt
      
    · apply le_transₓ _ (fGn a ha).2
      have B : p.c (p.index (G b)) ∉ p.Union_up_to (G a) := by
        intro H
        exact (fGn b hb).1 (p.monotone_Union_up_to G_lt.le H)
      let b' : { t // p.c t ∉ p.Union_up_to (G a) } := ⟨p.index (G b), B⟩
      apply @le_csupr _ _ _ (fun t : { t // p.c t ∉ p.Union_up_to (G a) } => p.r t) _ b'
      refine' ⟨p.r_bound, fun t ht => _⟩
      simp only [← exists_prop, ← mem_range, ← Subtype.exists, ← Subtype.coe_mk] at ht
      rcases ht with ⟨u, hu⟩
      rw [← hu.2]
      exact p.r_le _
      
  -- therefore, one may use them to construct a satellite configuration with `N+1` points
  let sc : satellite_config α N p.τ :=
    { c := fun k => p.c (p.index (G k)), R := fun k => p.r (p.index (G k)), rpos := fun k => p.rpos (p.index (G k)),
      h := by
        intro a b a_ne_b
        wlog (discharger := tactic.skip) G_le : G a ≤ G b := le_totalₓ (G a) (G b) using a b, b a
        · have G_lt : G a < G b := by
            rcases G_le.lt_or_eq with (H | H)
            · exact H
              
            have A : (a : ℕ) ≠ b := fin.coe_injective.ne a_ne_b
            rw [← color_G a (Nat.lt_succ_iffₓ.1 a.2), ← color_G b (Nat.lt_succ_iffₓ.1 b.2), H] at A
            exact (A rfl).elim
          exact Or.inl (Gab a b G_lt)
          
        · intro a_ne_b
          rw [or_comm]
          exact this a_ne_b.symm
          ,
      hlast := by
        intro a ha
        have I : (a : ℕ) < N := ha
        have : G a < G (Finₓ.last N) := by
          dsimp' [← G]
          simp [← I.ne, ← (hg a I).1]
        exact Gab _ _ this,
      inter := by
        intro a ha
        have I : (a : ℕ) < N := ha
        have J : G (Finₓ.last N) = i := by
          dsimp' [← G]
          simp only [← if_true, ← eq_self_iff_true]
        have K : G a = g a := by
          dsimp' [← G]
          simp [← I.ne, ← (hg a I).1]
        convert dist_le_add_of_nonempty_closed_ball_inter_closed_ball (hg _ I).2.1 }
  -- this is a contradiction
  exact (hN.false : _) sc

end TauPackage

open TauPackage

/-- The topological Besicovitch covering theorem: there exist finitely many families of disjoint
balls covering all the centers in a package. More specifically, one can use `N` families if there
are no satellite configurations with `N+1` points. -/
theorem exist_disjoint_covering_families {N : ℕ} {τ : ℝ} (hτ : 1 < τ) (hN : IsEmpty (SatelliteConfig α N τ))
    (q : BallPackage β α) :
    ∃ s : Finₓ N → Set β,
      (∀ i : Finₓ N, (s i).PairwiseDisjoint fun j => ClosedBall (q.c j) (q.R j)) ∧
        Range q.c ⊆ ⋃ i : Finₓ N, ⋃ j ∈ s i, Ball (q.c j) (q.R j) :=
  by
  -- first exclude the trivial case where `β` is empty (we need non-emptiness for the transfinite
  -- induction, to be able to choose garbage when there is no point left).
  cases is_empty_or_nonempty β
  · refine' ⟨fun i => ∅, fun i => pairwise_disjoint_empty, _⟩
    rw [← image_univ, eq_empty_of_is_empty (univ : Set β)]
    simp
    
  -- Now, assume `β` is nonempty.
  let p : tau_package β α := { q with τ, one_lt_tau := hτ }
  -- we use for `s i` the balls of color `i`.
  let s := fun i : Finₓ N => ⋃ (k : Ordinal.{u}) (hk : k < p.last_step) (h'k : p.color k = i), ({p.index k} : Set β)
  refine' ⟨s, fun i => _, _⟩
  · -- show that balls of the same color are disjoint
    intro x hx y hy x_ne_y
    obtain ⟨jx, jx_lt, jxi, rfl⟩ : ∃ jx : Ordinal, jx < p.last_step ∧ p.color jx = i ∧ x = p.index jx := by
      simpa only [← exists_prop, ← mem_Union, ← mem_singleton_iff] using hx
    obtain ⟨jy, jy_lt, jyi, rfl⟩ : ∃ jy : Ordinal, jy < p.last_step ∧ p.color jy = i ∧ y = p.index jy := by
      simpa only [← exists_prop, ← mem_Union, ← mem_singleton_iff] using hy
    wlog (discharger := tactic.skip) jxy : jx ≤ jy := le_totalₓ jx jy using jx jy, jy jx
    swap
    · intro h1 h2 h3 h4 h5 h6 h7
      rw [Function.onFun, Disjoint.comm]
      exact this h4 h5 h6 h1 h2 h3 h7.symm
      
    replace jxy : jx < jy
    · rcases lt_or_eq_of_leₓ jxy with (H | rfl)
      · exact H
        
      · exact (x_ne_y rfl).elim
        
      
    let A : Set ℕ :=
      ⋃ (j : { j // j < jy }) (hj :
        (closed_ball (p.c (p.index j)) (p.r (p.index j)) ∩ closed_ball (p.c (p.index jy)) (p.r (p.index jy))).Nonempty),
        {p.color j}
    have color_j : p.color jy = Inf (univ \ A) := by
      rw [tau_package.color]
    have : p.color jy ∈ univ \ A := by
      rw [color_j]
      apply Inf_mem
      refine' ⟨N, _⟩
      simp only [← not_exists, ← true_andₓ, ← exists_prop, ← mem_Union, ← mem_singleton_iff, ← not_and, ← mem_univ, ←
        mem_diff, ← Subtype.exists, ← Subtype.coe_mk]
      intro k hk H
      exact (p.color_lt (hk.trans jy_lt) hN).ne'
    simp only [← not_exists, ← true_andₓ, ← exists_prop, ← mem_Union, ← mem_singleton_iff, ← not_and, ← mem_univ, ←
      mem_diff, ← Subtype.exists, ← Subtype.coe_mk] at this
    specialize this jx jxy
    contrapose! this
    simpa only [← jxi, ← jyi, ← and_trueₓ, ← eq_self_iff_true, not_disjoint_iff_nonempty_inter]
    
  · -- show that the balls of color at most `N` cover every center.
    refine' range_subset_iff.2 fun b => _
    obtain ⟨a, ha⟩ : ∃ a : Ordinal, a < p.last_step ∧ dist (p.c b) (p.c (p.index a)) < p.r (p.index a) := by
      simpa only [← Union_up_to, ← exists_prop, ← mem_Union, ← mem_ball, ← Subtype.exists, ← Subtype.coe_mk] using
        p.mem_Union_up_to_last_step b
    simp only [← exists_prop, ← mem_Union, ← mem_ball, ← mem_singleton_iff, ← bUnion_and', ← exists_eq_left, ←
      Union_exists, ← exists_and_distrib_left]
    exact ⟨⟨p.color a, p.color_lt ha.1 hN⟩, a, rfl, ha⟩
    

/-!
### The measurable Besicovitch covering theorem
-/


open Nnreal

variable [SecondCountableTopology α] [MeasurableSpace α] [OpensMeasurableSpace α]

/-- Consider, for each `x` in a set `s`, a radius `r x ∈ (0, 1]`. Then one can find finitely
many disjoint balls of the form `closed_ball x (r x)` covering a proportion `1/(N+1)` of `s`, if
there are no satellite configurations with `N+1` points.
-/
theorem exist_finset_disjoint_balls_large_measure (μ : Measureₓ α) [IsFiniteMeasure μ] {N : ℕ} {τ : ℝ} (hτ : 1 < τ)
    (hN : IsEmpty (SatelliteConfig α N τ)) (s : Set α) (r : α → ℝ) (rpos : ∀, ∀ x ∈ s, ∀, 0 < r x)
    (rle : ∀, ∀ x ∈ s, ∀, r x ≤ 1) :
    ∃ t : Finset α,
      ↑t ⊆ s ∧
        μ (s \ ⋃ x ∈ t, ClosedBall x (r x)) ≤ N / (N + 1) * μ s ∧
          (t : Set α).PairwiseDisjoint fun x => ClosedBall x (r x) :=
  by
  -- exclude the trivial case where `μ s = 0`.
  rcases le_or_ltₓ (μ s) 0 with (hμs | hμs)
  · have : μ s = 0 := le_bot_iff.1 hμs
    refine'
      ⟨∅, by
        simp only [← Finset.coe_empty, ← empty_subset], _, _⟩
    · simp only [← this, ← diff_empty, ← Union_false, ← Union_empty, ← nonpos_iff_eq_zero, ← mul_zero]
      
    · simp only [← Finset.coe_empty, ← pairwise_disjoint_empty]
      
    
  cases is_empty_or_nonempty α
  · simp only [← eq_empty_of_is_empty s, ← measure_empty] at hμs
    exact (lt_irreflₓ _ hμs).elim
    
  have Npos : N ≠ 0 := by
    rintro rfl
    inhabit α
    exact (not_is_empty_of_nonempty _) hN
  -- introduce a measurable superset `o` with the same measure, for measure computations
  obtain ⟨o, so, omeas, μo⟩ : ∃ o : Set α, s ⊆ o ∧ MeasurableSet o ∧ μ o = μ s := exists_measurable_superset μ s
  /- We will apply the topological Besicovitch theorem, giving `N` disjoint subfamilies of balls
    covering `s`. Among these, one of them covers a proportion at least `1/N` of `s`. A large
    enough finite subfamily will then cover a proportion at least `1/(N+1)`. -/
  let a : ball_package s α :=
    { c := fun x => x, R := fun x => r x, rpos := fun x => rpos x x.2, rBound := 1, r_le := fun x => rle x x.2 }
  rcases exist_disjoint_covering_families hτ hN a with ⟨u, hu, hu'⟩
  have u_count : ∀ i, (u i).Countable := by
    intro i
    refine' (hu i).countable_of_nonempty_interior fun j hj => _
    have : (ball (j : α) (r j)).Nonempty := nonempty_ball.2 (a.rpos _)
    exact this.mono ball_subset_interior_closed_ball
  let v : Finₓ N → Set α := fun i => ⋃ (x : s) (hx : x ∈ u i), closed_ball x (r x)
  have : ∀ i, MeasurableSet (v i) := fun i => MeasurableSet.bUnion (u_count i) fun b hb => measurable_set_closed_ball
  have A : s = ⋃ i : Finₓ N, s ∩ v i := by
    refine' subset.antisymm _ (Union_subset fun i => inter_subset_left _ _)
    intro x hx
    obtain ⟨i, y, hxy, h'⟩ : ∃ (i : Finₓ N)(i_1 : ↥s)(i : i_1 ∈ u i), x ∈ ball (↑i_1) (r ↑i_1) := by
      have : x ∈ range a.c := by
        simpa only [← Subtype.range_coe_subtype, ← set_of_mem_eq]
      simpa only [← mem_Union] using hu' this
    refine' mem_Union.2 ⟨i, ⟨hx, _⟩⟩
    simp only [← v, ← exists_prop, ← mem_Union, ← SetCoe.exists, ← exists_and_distrib_right, ← Subtype.coe_mk]
    exact
      ⟨y,
        ⟨y.2, by
          simpa only [← Subtype.coe_eta] ⟩,
        ball_subset_closed_ball h'⟩
  have S : (∑ i : Finₓ N, μ s / N) ≤ ∑ i, μ (s ∩ v i) :=
    calc
      (∑ i : Finₓ N, μ s / N) = μ s := by
        simp only [← Finset.card_fin, ← Finset.sum_const, ← nsmul_eq_mul]
        rw [Ennreal.mul_div_cancel']
        · simp only [← Npos, ← Ne.def, ← Nat.cast_eq_zero, ← not_false_iff]
          
        · exact Ennreal.coe_nat_ne_top
          
      _ ≤ ∑ i, μ (s ∩ v i) := by
        conv_lhs => rw [A]
        apply measure_Union_fintype_le
      
  -- choose an index `i` of a subfamily covering at least a proportion `1/N` of `s`.
  obtain ⟨i, -, hi⟩ : ∃ (i : Finₓ N)(hi : i ∈ Finset.univ), μ s / N ≤ μ (s ∩ v i) := by
    apply Ennreal.exists_le_of_sum_le _ S
    exact ⟨⟨0, bot_lt_iff_ne_bot.2 Npos⟩, Finset.mem_univ _⟩
  replace hi : μ s / (N + 1) < μ (s ∩ v i)
  · apply lt_of_lt_of_leₓ _ hi
    apply (Ennreal.mul_lt_mul_left hμs.ne' (measure_lt_top μ s).Ne).2
    rw [Ennreal.inv_lt_inv]
    conv_lhs => rw [← add_zeroₓ (N : ℝ≥0∞)]
    exact Ennreal.add_lt_add_left (Ennreal.nat_ne_top N) Ennreal.zero_lt_one
    
  have B : μ (o ∩ v i) = ∑' x : u i, μ (o ∩ closed_ball x (r x)) := by
    have : o ∩ v i = ⋃ (x : s) (hx : x ∈ u i), o ∩ closed_ball x (r x) := by
      simp only [← inter_Union]
    rw [this, measure_bUnion (u_count i)]
    · rfl
      
    · exact (hu i).mono fun k => inter_subset_right _ _
      
    · exact fun b hb => omeas.inter measurable_set_closed_ball
      
  -- A large enough finite subfamily of `u i` will also cover a proportion `> 1/(N+1)` of `s`.
  -- Since `s` might not be measurable, we express this in terms of the measurable superset `o`.
  obtain ⟨w, hw⟩ : ∃ w : Finset (u i), μ s / (N + 1) < ∑ x : u i in w, μ (o ∩ closed_ball (x : α) (r (x : α))) := by
    have C : HasSum (fun x : u i => μ (o ∩ closed_ball x (r x))) (μ (o ∩ v i)) := by
      rw [B]
      exact ennreal.summable.has_sum
    have : μ s / (N + 1) < μ (o ∩ v i) := hi.trans_le (measure_mono (inter_subset_inter_left _ so))
    exact ((tendsto_order.1 C).1 _ this).exists
  -- Bring back the finset `w i` of `↑(u i)` to a finset of `α`, and check that it works by design.
  refine' ⟨Finset.image (fun x : u i => x) w, _, _, _⟩
  -- show that the finset is included in `s`.
  · simp only [← image_subset_iff, ← coe_coe, ← Finset.coe_image]
    intro y hy
    simp only [← Subtype.coe_prop, ← mem_preimage]
    
  -- show that it covers a large enough proportion of `s`. For measure computations, we do not
  -- use `s` (which might not be measurable), but its measurable superset `o`. Since their measures
  -- are the same, this does not spoil the estimates
  · suffices H : μ (o \ ⋃ x ∈ w, closed_ball (↑x) (r ↑x)) ≤ N / (N + 1) * μ s
    · rw [Finset.set_bUnion_finset_image]
      exact le_transₓ (measure_mono (diff_subset_diff so (subset.refl _))) H
      
    rw [← diff_inter_self_eq_diff, measure_diff_le_iff_le_add _ (inter_subset_right _ _) (measure_lt_top μ _).Ne]
    swap
    · apply MeasurableSet.inter _ omeas
      have : Encodable (u i) := (u_count i).toEncodable
      exact MeasurableSet.Union fun b => MeasurableSet.Union_Prop fun hb => measurable_set_closed_ball
      
    calc μ o = 1 / (N + 1) * μ s + N / (N + 1) * μ s := by
        rw [μo, ← add_mulₓ, Ennreal.div_add_div_same, add_commₓ, Ennreal.div_self, one_mulₓ] <;>
          simp _ ≤ μ ((⋃ x ∈ w, closed_ball (↑x) (r ↑x)) ∩ o) + N / (N + 1) * μ s :=
        by
        refine' add_le_add _ le_rfl
        rw [div_eq_mul_inv, one_mulₓ, mul_comm, ← div_eq_mul_inv]
        apply hw.le.trans (le_of_eqₓ _)
        rw [← Finset.set_bUnion_coe, inter_comm _ o, inter_Union₂, Finset.set_bUnion_coe, measure_bUnion_finset]
        · have : (w : Set (u i)).PairwiseDisjoint fun b : u i => closed_ball (b : α) (r (b : α)) := by
            intro k hk l hl hkl
            exact hu i k.2 l.2 (subtype.coe_injective.ne hkl)
          exact this.mono fun k => inter_subset_right _ _
          
        · intro b hb
          apply omeas.inter measurable_set_closed_ball
          
    
  -- show that the balls are disjoint
  · intro k hk l hl hkl
    obtain ⟨k', k'w, rfl⟩ : ∃ k' : u i, k' ∈ w ∧ ↑↑k' = k := by
      simpa only [← mem_image, ← Finset.mem_coe, ← coe_coe, ← Finset.coe_image] using hk
    obtain ⟨l', l'w, rfl⟩ : ∃ l' : u i, l' ∈ w ∧ ↑↑l' = l := by
      simpa only [← mem_image, ← Finset.mem_coe, ← coe_coe, ← Finset.coe_image] using hl
    have k'nel' : (k' : s) ≠ l' := by
      intro h
      rw [h] at hkl
      exact hkl rfl
    exact hu i k'.2 l'.2 k'nel'
    

variable [HasBesicovitchCovering α]

/-- The measurable Besicovitch covering theorem. Assume that, for any `x` in a set `s`,
one is given a set of admissible closed balls centered at `x`, with arbitrarily small radii.
Then there exists a disjoint covering of almost all `s` by admissible closed balls centered at some
points of `s`.
This version requires that the underlying measure is finite, and that the space has the Besicovitch
covering property (which is satisfied for instance by normed real vector spaces). It expresses the
conclusion in a slightly awkward form (with a subset of `α × ℝ`) coming from the proof technique.
For a version assuming that the measure is sigma-finite,
see `exists_disjoint_closed_ball_covering_ae_aux`.
For a version giving the conclusion in a nicer form, see `exists_disjoint_closed_ball_covering_ae`.
-/
theorem exists_disjoint_closed_ball_covering_ae_of_finite_measure_aux (μ : Measureₓ α) [IsFiniteMeasure μ]
    (f : α → Set ℝ) (s : Set α) (hf : ∀, ∀ x ∈ s, ∀, ∀, ∀ δ > 0, ∀, (f x ∩ Ioo 0 δ).Nonempty) :
    ∃ t : Set (α × ℝ),
      t.Countable ∧
        (∀ p : α × ℝ, p ∈ t → p.1 ∈ s) ∧
          (∀ p : α × ℝ, p ∈ t → p.2 ∈ f p.1) ∧
            μ (s \ ⋃ (p : α × ℝ) (hp : p ∈ t), ClosedBall p.1 p.2) = 0 ∧
              t.PairwiseDisjoint fun p => ClosedBall p.1 p.2 :=
  by
  rcases HasBesicovitchCovering.no_satellite_config α with ⟨N, τ, hτ, hN⟩
  /- Introduce a property `P` on finsets saying that we have a nice disjoint covering of a
      subset of `s` by admissible balls. -/
  let P : Finset (α × ℝ) → Prop := fun t =>
    ((t : Set (α × ℝ)).PairwiseDisjoint fun p => closed_ball p.1 p.2) ∧
      (∀ p : α × ℝ, p ∈ t → p.1 ∈ s) ∧ ∀ p : α × ℝ, p ∈ t → p.2 ∈ f p.1
  /- Given a finite good covering of a subset `s`, one can find a larger finite good covering,
    covering additionally a proportion at least `1/(N+1)` of leftover points. This follows from
    `exist_finset_disjoint_balls_large_measure` applied to balls not intersecting the initial
    covering. -/
  have :
    ∀ t : Finset (α × ℝ),
      P t →
        ∃ u : Finset (α × ℝ),
          t ⊆ u ∧
            P u ∧
              μ (s \ ⋃ (p : α × ℝ) (hp : p ∈ u), closed_ball p.1 p.2) ≤
                N / (N + 1) * μ (s \ ⋃ (p : α × ℝ) (hp : p ∈ t), closed_ball p.1 p.2) :=
    by
    intro t ht
    set B := ⋃ (p : α × ℝ) (hp : p ∈ t), closed_ball p.1 p.2 with hB
    have B_closed : IsClosed B := is_closed_bUnion (Finset.finite_to_set _) fun i hi => is_closed_ball
    set s' := s \ B with hs'
    have : ∀, ∀ x ∈ s', ∀, ∃ r ∈ f x ∩ Ioo 0 1, Disjoint B (closed_ball x r) := by
      intro x hx
      have xs : x ∈ s := ((mem_diff x).1 hx).1
      rcases eq_empty_or_nonempty B with (hB | hB)
      · have : (0 : ℝ) < 1 := zero_lt_one
        rcases hf x xs 1 zero_lt_one with ⟨r, hr, h'r⟩
        exact
          ⟨r, ⟨hr, h'r⟩, by
            simp only [← hB, ← empty_disjoint]⟩
        
      · let R := inf_dist x B
        have : 0 < min R 1 := lt_minₓ ((B_closed.not_mem_iff_inf_dist_pos hB).1 ((mem_diff x).1 hx).2) zero_lt_one
        rcases hf x xs _ this with ⟨r, hr, h'r⟩
        refine' ⟨r, ⟨hr, ⟨h'r.1, h'r.2.trans_le (min_le_rightₓ _ _)⟩⟩, _⟩
        rw [Disjoint.comm]
        exact disjoint_closed_ball_of_lt_inf_dist (h'r.2.trans_le (min_le_leftₓ _ _))
        
    choose! r hr using this
    obtain ⟨v, vs', hμv, hv⟩ :
      ∃ v : Finset α,
        ↑v ⊆ s' ∧
          μ (s' \ ⋃ x ∈ v, closed_ball x (r x)) ≤ N / (N + 1) * μ s' ∧
            (v : Set α).PairwiseDisjoint fun x : α => closed_ball x (r x) :=
      by
      have rI : ∀, ∀ x ∈ s', ∀, r x ∈ Ioo (0 : ℝ) 1 := fun x hx => (hr x hx).1.2
      exact exist_finset_disjoint_balls_large_measure μ hτ hN s' r (fun x hx => (rI x hx).1) fun x hx => (rI x hx).2.le
    refine' ⟨t ∪ Finset.image (fun x => (x, r x)) v, Finset.subset_union_left _ _, ⟨_, _, _⟩, _⟩
    · simp only [← Finset.coe_union, ← pairwise_disjoint_union, ← ht.1, ← true_andₓ, ← Finset.coe_image]
      constructor
      · intro p hp q hq hpq
        rcases(mem_image _ _ _).1 hp with ⟨p', p'v, rfl⟩
        rcases(mem_image _ _ _).1 hq with ⟨q', q'v, rfl⟩
        refine' hv p'v q'v fun hp'q' => _
        rw [hp'q'] at hpq
        exact hpq rfl
        
      · intro p hp q hq hpq
        rcases(mem_image _ _ _).1 hq with ⟨q', q'v, rfl⟩
        apply disjoint_of_subset_left _ (hr q' (vs' q'v)).2
        rw [hB, ← Finset.set_bUnion_coe]
        exact subset_bUnion_of_mem hp
        
      
    · intro p hp
      rcases Finset.mem_union.1 hp with (h'p | h'p)
      · exact ht.2.1 p h'p
        
      · rcases Finset.mem_image.1 h'p with ⟨p', p'v, rfl⟩
        exact ((mem_diff _).1 (vs' (Finset.mem_coe.2 p'v))).1
        
      
    · intro p hp
      rcases Finset.mem_union.1 hp with (h'p | h'p)
      · exact ht.2.2 p h'p
        
      · rcases Finset.mem_image.1 h'p with ⟨p', p'v, rfl⟩
        exact (hr p' (vs' p'v)).1.1
        
      
    · convert hμv using 2
      rw [Finset.set_bUnion_union, ← diff_diff, Finset.set_bUnion_finset_image]
      
  /- Define `F` associating to a finite good covering the above enlarged good covering, covering
    a proportion `1/(N+1)` of leftover points. Iterating `F`, one will get larger and larger good
    coverings, missing in the end only a measure-zero set. -/
  choose! F hF using this
  let u := fun n => (F^[n]) ∅
  have u_succ : ∀ n : ℕ, u n.succ = F (u n) := fun n => by
    simp only [← u, ← Function.comp_app, ← Function.iterate_succ']
  have Pu : ∀ n, P (u n) := by
    intro n
    induction' n with n IH
    · simp only [← u, ← P, ← Prod.forall, ← id.def, ← Function.iterate_zero]
      simp only [← Finset.not_mem_empty, ← IsEmpty.forall_iff, ← Finset.coe_empty, ← forall_2_true_iff, ← and_selfₓ, ←
        pairwise_disjoint_empty]
      
    · rw [u_succ]
      exact (hF (u n) IH).2.1
      
  refine' ⟨⋃ n, u n, countable_Union fun n => (u n).countable_to_set, _, _, _, _⟩
  · intro p hp
    rcases mem_Union.1 hp with ⟨n, hn⟩
    exact (Pu n).2.1 p (Finset.mem_coe.1 hn)
    
  · intro p hp
    rcases mem_Union.1 hp with ⟨n, hn⟩
    exact (Pu n).2.2 p (Finset.mem_coe.1 hn)
    
  · have A :
      ∀ n,
        μ (s \ ⋃ (p : α × ℝ) (hp : p ∈ ⋃ n : ℕ, (u n : Set (α × ℝ))), closed_ball p.fst p.snd) ≤
          μ (s \ ⋃ (p : α × ℝ) (hp : p ∈ u n), closed_ball p.fst p.snd) :=
      by
      intro n
      apply measure_mono
      apply diff_subset_diff (subset.refl _)
      exact bUnion_subset_bUnion_left (subset_Union (fun i => (u i : Set (α × ℝ))) n)
    have B : ∀ n, μ (s \ ⋃ (p : α × ℝ) (hp : p ∈ u n), closed_ball p.fst p.snd) ≤ (N / (N + 1)) ^ n * μ s := by
      intro n
      induction' n with n IH
      · simp only [← le_reflₓ, ← diff_empty, ← one_mulₓ, ← Union_false, ← Union_empty, ← pow_zeroₓ]
        
      calc
        μ (s \ ⋃ (p : α × ℝ) (hp : p ∈ u n.succ), closed_ball p.fst p.snd) ≤
            N / (N + 1) * μ (s \ ⋃ (p : α × ℝ) (hp : p ∈ u n), closed_ball p.fst p.snd) :=
          by
          rw [u_succ]
          exact (hF (u n) (Pu n)).2.2_ ≤ (N / (N + 1)) ^ n.succ * μ s := by
          rw [pow_succₓ, mul_assoc]
          exact Ennreal.mul_le_mul le_rfl IH
    have C : tendsto (fun n : ℕ => ((N : ℝ≥0∞) / (N + 1)) ^ n * μ s) at_top (𝓝 (0 * μ s)) := by
      apply Ennreal.Tendsto.mul_const _ (Or.inr (measure_lt_top μ s).Ne)
      apply Ennreal.tendsto_pow_at_top_nhds_0_of_lt_1
      rw [Ennreal.div_lt_iff, one_mulₓ]
      · conv_lhs => rw [← add_zeroₓ (N : ℝ≥0∞)]
        exact Ennreal.add_lt_add_left (Ennreal.nat_ne_top N) Ennreal.zero_lt_one
        
      · simp only [← true_orₓ, ← add_eq_zero_iff, ← Ne.def, ← not_false_iff, ← one_ne_zero, ← and_falseₓ]
        
      · simp only [← Ennreal.nat_ne_top, ← Ne.def, ← not_false_iff, ← or_trueₓ]
        
    rw [zero_mul] at C
    apply le_bot_iff.1
    exact le_of_tendsto_of_tendsto' tendsto_const_nhds C fun n => (A n).trans (B n)
    
  · refine' (pairwise_disjoint_Union _).2 fun n => (Pu n).1
    apply (monotone_nat_of_le_succ fun n => _).directed_le
    rw [u_succ]
    exact (hF (u n) (Pu n)).1
    

/-- The measurable Besicovitch covering theorem. Assume that, for any `x` in a set `s`,
one is given a set of admissible closed balls centered at `x`, with arbitrarily small radii.
Then there exists a disjoint covering of almost all `s` by admissible closed balls centered at some
points of `s`.
This version requires that the underlying measure is sigma-finite, and that the space has the
Besicovitch covering property (which is satisfied for instance by normed real vector spaces).
It expresses the conclusion in a slightly awkward form (with a subset of `α × ℝ`) coming from the
proof technique.
For a version giving the conclusion in a nicer form, see `exists_disjoint_closed_ball_covering_ae`.
-/
theorem exists_disjoint_closed_ball_covering_ae_aux (μ : Measureₓ α) [SigmaFinite μ] (f : α → Set ℝ) (s : Set α)
    (hf : ∀, ∀ x ∈ s, ∀, ∀, ∀ δ > 0, ∀, (f x ∩ Ioo 0 δ).Nonempty) :
    ∃ t : Set (α × ℝ),
      t.Countable ∧
        (∀ p : α × ℝ, p ∈ t → p.1 ∈ s) ∧
          (∀ p : α × ℝ, p ∈ t → p.2 ∈ f p.1) ∧
            μ (s \ ⋃ (p : α × ℝ) (hp : p ∈ t), ClosedBall p.1 p.2) = 0 ∧
              t.PairwiseDisjoint fun p => ClosedBall p.1 p.2 :=
  by
  /- This is deduced from the finite measure case, by using a finite measure with respect to which
    the initial sigma-finite measure is absolutely continuous. -/
  rcases exists_absolutely_continuous_is_finite_measure μ with ⟨ν, hν, hμν⟩
  rcases exists_disjoint_closed_ball_covering_ae_of_finite_measure_aux ν f s hf with ⟨t, t_count, ts, tr, tν, tdisj⟩
  exact ⟨t, t_count, ts, tr, hμν tν, tdisj⟩

/-- The measurable Besicovitch covering theorem. Assume that, for any `x` in a set `s`,
one is given a set of admissible closed balls centered at `x`, with arbitrarily small radii.
Then there exists a disjoint covering of almost all `s` by admissible closed balls centered at some
points of `s`. We can even require that the radius at `x` is bounded by a given function `R x`.
(Take `R = 1` if you don't need this additional feature).
This version requires that the underlying measure is sigma-finite, and that the space has the
Besicovitch covering property (which is satisfied for instance by normed real vector spaces).
-/
theorem exists_disjoint_closed_ball_covering_ae (μ : Measureₓ α) [SigmaFinite μ] (f : α → Set ℝ) (s : Set α)
    (hf : ∀, ∀ x ∈ s, ∀, ∀, ∀ δ > 0, ∀, (f x ∩ Ioo 0 δ).Nonempty) (R : α → ℝ) (hR : ∀, ∀ x ∈ s, ∀, 0 < R x) :
    ∃ (t : Set α)(r : α → ℝ),
      t.Countable ∧
        t ⊆ s ∧
          (∀, ∀ x ∈ t, ∀, r x ∈ f x ∩ Ioo 0 (R x)) ∧
            μ (s \ ⋃ x ∈ t, ClosedBall x (r x)) = 0 ∧ t.PairwiseDisjoint fun x => ClosedBall x (r x) :=
  by
  let g := fun x => f x ∩ Ioo 0 (R x)
  have hg : ∀, ∀ x ∈ s, ∀, ∀, ∀ δ > 0, ∀, (g x ∩ Ioo 0 δ).Nonempty := by
    intro x hx δ δpos
    rcases hf x hx (min δ (R x)) (lt_minₓ δpos (hR x hx)) with ⟨r, hr⟩
    exact ⟨r, ⟨⟨hr.1, hr.2.1, hr.2.2.trans_le (min_le_rightₓ _ _)⟩, ⟨hr.2.1, hr.2.2.trans_le (min_le_leftₓ _ _)⟩⟩⟩
  rcases exists_disjoint_closed_ball_covering_ae_aux μ g s hg with ⟨v, v_count, vs, vg, μv, v_disj⟩
  let t := Prod.fst '' v
  have : ∀, ∀ x ∈ t, ∀, ∃ r : ℝ, (x, r) ∈ v := by
    intro x hx
    rcases(mem_image _ _ _).1 hx with ⟨⟨p, q⟩, hp, rfl⟩
    exact ⟨q, hp⟩
  choose! r hr using this
  have im_t : (fun x => (x, r x)) '' t = v := by
    have I : ∀ p : α × ℝ, p ∈ v → 0 ≤ p.2 := fun p hp => (vg p hp).2.1.le
    apply subset.antisymm
    · simp only [← image_subset_iff]
      rintro ⟨x, p⟩ hxp
      simp only [← mem_preimage]
      exact hr _ (mem_image_of_mem _ hxp)
      
    · rintro ⟨x, p⟩ hxp
      have hxrx : (x, r x) ∈ v := hr _ (mem_image_of_mem _ hxp)
      have : p = r x := by
        by_contra
        have A : (x, p) ≠ (x, r x) := by
          simpa only [← true_andₓ, ← Prod.mk.inj_iff, ← eq_self_iff_true, ← Ne.def] using h
        have H := v_disj hxp hxrx A
        contrapose H
        rw [not_disjoint_iff_nonempty_inter]
        refine'
          ⟨x, by
            simp [← I _ hxp, ← I _ hxrx]⟩
      rw [this]
      apply mem_image_of_mem
      exact mem_image_of_mem _ hxp
      
  refine' ⟨t, r, v_count.image _, _, _, _, _⟩
  · intro x hx
    rcases(mem_image _ _ _).1 hx with ⟨⟨p, q⟩, hp, rfl⟩
    exact vs _ hp
    
  · intro x hx
    rcases(mem_image _ _ _).1 hx with ⟨⟨p, q⟩, hp, rfl⟩
    exact vg _ (hr _ hx)
    
  · have :
      (⋃ (x : α) (H : x ∈ t), closed_ball x (r x)) =
        ⋃ (p : α × ℝ) (H : p ∈ (fun x => (x, r x)) '' t), closed_ball p.1 p.2 :=
      by
      conv_rhs => rw [bUnion_image]
    rw [this, im_t]
    exact μv
    
  · have A : inj_on (fun x : α => (x, r x)) t := by
      simp (config := { contextual := true })only [← inj_on, ← Prod.mk.inj_iff, ← implies_true_iff, ← eq_self_iff_true]
    rwa [← im_t, A.pairwise_disjoint_image] at v_disj
    

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (U «expr ⊇ » s)
-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (v «expr ⊇ » s')
/-- In a space with the Besicovitch property, any set `s` can be covered with balls whose measures
add up to at most `μ s + ε`, for any positive `ε`. This works even if one restricts the set of
allowed radii around a point `x` to a set `f x` which accumulates at `0`. -/
theorem exists_closed_ball_covering_tsum_measure_le (μ : Measureₓ α) [SigmaFinite μ] [Measure.OuterRegular μ] {ε : ℝ≥0∞}
    (hε : ε ≠ 0) (f : α → Set ℝ) (s : Set α) (hf : ∀, ∀ x ∈ s, ∀, ∀, ∀ δ > 0, ∀, (f x ∩ Ioo 0 δ).Nonempty) :
    ∃ (t : Set α)(r : α → ℝ),
      t.Countable ∧
        t ⊆ s ∧
          (∀, ∀ x ∈ t, ∀, r x ∈ f x) ∧
            (s ⊆ ⋃ x ∈ t, ClosedBall x (r x)) ∧ (∑' x : t, μ (ClosedBall x (r x))) ≤ μ s + ε :=
  by
  /- For the proof, first cover almost all `s` with disjoint balls thanks to the usual Besicovitch
    theorem. Taking the balls included in a well-chosen open neighborhood `u` of `s`, one may
    ensure that their measures add at most to `μ s + ε / 2`. Let `s'` be the remaining set, of measure
    `0`. Applying the other version of Besicovitch, one may cover it with at most `N` disjoint
    subfamilies. Making sure that they are all included in a neighborhood `v` of `s'` of measure at
    most `ε / (2 N)`, the sum of their measures is at most `ε / 2`, completing the proof. -/
  obtain ⟨u, su, u_open, μu⟩ : ∃ (U : _)(_ : U ⊇ s), IsOpen U ∧ μ U ≤ μ s + ε / 2 :=
    Set.exists_is_open_le_add _ _
      (by
        simpa only [← or_falseₓ, ← Ne.def, ← Ennreal.div_zero_iff, ← Ennreal.one_ne_top, ←
          Ennreal.bit0_eq_top_iff] using hε)
  have : ∀, ∀ x ∈ s, ∀, ∃ R > 0, ball x R ⊆ u := fun x hx => Metric.mem_nhds_iff.1 (u_open.mem_nhds (su hx))
  choose! R hR using this
  obtain ⟨t0, r0, t0_count, t0s, hr0, μt0, t0_disj⟩ :
    ∃ (t0 : Set α)(r0 : α → ℝ),
      t0.Countable ∧
        t0 ⊆ s ∧
          (∀, ∀ x ∈ t0, ∀, r0 x ∈ f x ∩ Ioo 0 (R x)) ∧
            μ (s \ ⋃ x ∈ t0, closed_ball x (r0 x)) = 0 ∧ t0.PairwiseDisjoint fun x => closed_ball x (r0 x) :=
    exists_disjoint_closed_ball_covering_ae μ f s hf R fun x hx => (hR x hx).1
  -- we have constructed an almost everywhere covering of `s` by disjoint balls. Let `s'` be the
  -- remaining set.
  let s' := s \ ⋃ x ∈ t0, closed_ball x (r0 x)
  have s's : s' ⊆ s := diff_subset _ _
  obtain ⟨N, τ, hτ, H⟩ : ∃ N τ, 1 < τ ∧ IsEmpty (Besicovitch.SatelliteConfig α N τ) :=
    HasBesicovitchCovering.no_satellite_config α
  obtain ⟨v, s'v, v_open, μv⟩ : ∃ (v : _)(_ : v ⊇ s'), IsOpen v ∧ μ v ≤ μ s' + ε / 2 / N :=
    Set.exists_is_open_le_add _ _
      (by
        simp only [← hε, ← Ennreal.nat_ne_top, ← WithTop.mul_eq_top_iff, ← Ne.def, ← Ennreal.div_zero_iff, ←
          Ennreal.one_ne_top, ← not_false_iff, ← and_falseₓ, ← false_andₓ, ← or_selfₓ, ← Ennreal.bit0_eq_top_iff])
  have : ∀, ∀ x ∈ s', ∀, ∃ r1 ∈ f x ∩ Ioo (0 : ℝ) 1, closed_ball x r1 ⊆ v := by
    intro x hx
    rcases Metric.mem_nhds_iff.1 (v_open.mem_nhds (s'v hx)) with ⟨r, rpos, hr⟩
    rcases hf x (s's hx) (min r 1) (lt_minₓ rpos zero_lt_one) with ⟨R', hR'⟩
    exact
      ⟨R', ⟨hR'.1, hR'.2.1, hR'.2.2.trans_le (min_le_rightₓ _ _)⟩,
        subset.trans (closed_ball_subset_ball (hR'.2.2.trans_le (min_le_leftₓ _ _))) hr⟩
  choose! r1 hr1 using this
  let q : ball_package s' α :=
    { c := fun x => x, R := fun x => r1 x, rpos := fun x => (hr1 x.1 x.2).1.2.1, rBound := 1,
      r_le := fun x => (hr1 x.1 x.2).1.2.2.le }
  -- by Besicovitch, we cover `s'` with at most `N` families of disjoint balls, all included in
  -- a suitable neighborhood `v` of `s'`.
  obtain ⟨S, S_disj, hS⟩ :
    ∃ S : Finₓ N → Set s',
      (∀ i : Finₓ N, (S i).PairwiseDisjoint fun j => closed_ball (q.c j) (q.r j)) ∧
        range q.c ⊆ ⋃ i : Finₓ N, ⋃ j ∈ S i, ball (q.c j) (q.r j) :=
    exist_disjoint_covering_families hτ H q
  have S_count : ∀ i, (S i).Countable := by
    intro i
    apply (S_disj i).countable_of_nonempty_interior fun j hj => _
    have : (ball (j : α) (r1 j)).Nonempty := nonempty_ball.2 (q.rpos _)
    exact this.mono ball_subset_interior_closed_ball
  let r := fun x => if x ∈ s' then r1 x else r0 x
  have r_t0 : ∀, ∀ x ∈ t0, ∀, r x = r0 x := by
    intro x hx
    have : ¬x ∈ s' := by
      simp only [← not_exists, ← exists_prop, ← mem_Union, ← mem_closed_ball, ← not_and, ← not_ltₓ, ← not_leₓ, ←
        mem_diff, ← not_forall]
      intro h'x
      refine' ⟨x, hx, _⟩
      rw [dist_self]
      exact (hr0 x hx).2.1.le
    simp only [← r, ← if_neg this]
  -- the desired covering set is given by the union of the families constructed in the first and
  -- second steps.
  refine' ⟨t0 ∪ ⋃ i : Finₓ N, (coe : s' → α) '' S i, r, _, _, _, _, _⟩
  -- it remains to check that they have the desired properties
  · exact t0_count.union (countable_Union fun i => (S_count i).Image _)
    
  · simp only [← t0s, ← true_andₓ, ← union_subset_iff, ← image_subset_iff, ← Union_subset_iff]
    intro i x hx
    exact s's x.2
    
  · intro x hx
    cases hx
    · rw [r_t0 x hx]
      exact (hr0 _ hx).1
      
    · have h'x : x ∈ s' := by
        simp only [← mem_Union, ← mem_image] at hx
        rcases hx with ⟨i, y, ySi, rfl⟩
        exact y.2
      simp only [← r, ← if_pos h'x, ← (hr1 x h'x).1.1]
      
    
  · intro x hx
    by_cases' h'x : x ∈ s'
    · obtain ⟨i, y, ySi, xy⟩ : ∃ (i : Finₓ N)(y : ↥s')(ySi : y ∈ S i), x ∈ ball (y : α) (r1 y) := by
        have A : x ∈ range q.c := by
          simpa only [← not_exists, ← exists_prop, ← mem_Union, ← mem_closed_ball, ← not_and, ← not_leₓ, ←
            mem_set_of_eq, ← Subtype.range_coe_subtype, ← mem_diff] using h'x
        simpa only [← mem_Union, ← mem_image] using hS A
      refine' mem_Union₂.2 ⟨y, Or.inr _, _⟩
      · simp only [← mem_Union, ← mem_image]
        exact ⟨i, y, ySi, rfl⟩
        
      · have : (y : α) ∈ s' := y.2
        simp only [← r, ← if_pos this]
        exact ball_subset_closed_ball xy
        
      
    · obtain ⟨y, yt0, hxy⟩ : ∃ y : α, y ∈ t0 ∧ x ∈ closed_ball y (r0 y) := by
        simpa [← hx, -mem_closed_ball] using h'x
      refine' mem_Union₂.2 ⟨y, Or.inl yt0, _⟩
      rwa [r_t0 _ yt0]
      
    
  -- the only nontrivial property is the measure control, which we check now
  · -- the sets in the first step have measure at most `μ s + ε / 2`
    have A : (∑' x : t0, μ (closed_ball x (r x))) ≤ μ s + ε / 2 :=
      calc
        (∑' x : t0, μ (closed_ball x (r x))) = ∑' x : t0, μ (closed_ball x (r0 x)) := by
          congr 1
          ext x
          rw [r_t0 x x.2]
        _ = μ (⋃ x : t0, closed_ball x (r0 x)) := by
          have : Encodable t0 := t0_count.to_encodable
          rw [measure_Union]
          · exact (pairwise_subtype_iff_pairwise_set _ _).2 t0_disj
            
          · exact fun i => measurable_set_closed_ball
            
        _ ≤ μ u := by
          apply measure_mono
          simp only [← SetCoe.forall, ← Subtype.coe_mk, ← Union_subset_iff]
          intro x hx
          apply subset.trans (closed_ball_subset_ball (hr0 x hx).2.2) (hR x (t0s hx)).2
        _ ≤ μ s + ε / 2 := μu
        
    -- each subfamily in the second step has measure at most `ε / (2 N)`.
    have B : ∀ i : Finₓ N, (∑' x : (coe : s' → α) '' S i, μ (closed_ball x (r x))) ≤ ε / 2 / N := fun i =>
      calc
        (∑' x : (coe : s' → α) '' S i, μ (closed_ball x (r x))) = ∑' x : S i, μ (closed_ball x (r x)) := by
          have : inj_on (coe : s' → α) (S i) := subtype.coe_injective.inj_on _
          let F : S i ≃ (coe : s' → α) '' S i := this.bij_on_image.equiv _
          exact (F.tsum_eq fun x => μ (closed_ball x (r x))).symm
        _ = ∑' x : S i, μ (closed_ball x (r1 x)) := by
          congr 1
          ext x
          have : (x : α) ∈ s' := x.1.2
          simp only [← r, ← if_pos this]
        _ = μ (⋃ x : S i, closed_ball x (r1 x)) := by
          have : Encodable (S i) := (S_count i).toEncodable
          rw [measure_Union]
          · exact (pairwise_subtype_iff_pairwise_set _ _).2 (S_disj i)
            
          · exact fun i => measurable_set_closed_ball
            
        _ ≤ μ v := by
          apply measure_mono
          simp only [← SetCoe.forall, ← Subtype.coe_mk, ← Union_subset_iff]
          intro x xs' xSi
          exact (hr1 x xs').2
        _ ≤ ε / 2 / N := by
          have : μ s' = 0 := μt0
          rwa [this, zero_addₓ] at μv
        
    -- add up all these to prove the desired estimate
    calc
      (∑' x : t0 ∪ ⋃ i : Finₓ N, (coe : s' → α) '' S i, μ (closed_ball x (r x))) ≤
          (∑' x : t0, μ (closed_ball x (r x))) + ∑' x : ⋃ i : Finₓ N, (coe : s' → α) '' S i, μ (closed_ball x (r x)) :=
        Ennreal.tsum_union_le (fun x => μ (closed_ball x (r x))) _
          _ _ ≤
          (∑' x : t0, μ (closed_ball x (r x))) + ∑ i : Finₓ N, ∑' x : (coe : s' → α) '' S i, μ (closed_ball x (r x)) :=
        add_le_add le_rfl
          (Ennreal.tsum_Union_le (fun x => μ (closed_ball x (r x))) _)_ ≤ μ s + ε / 2 + ∑ i : Finₓ N, ε / 2 / N :=
        by
        refine' add_le_add A _
        refine' Finset.sum_le_sum _
        intro i hi
        exact B i _ ≤ μ s + ε / 2 + ε / 2 := by
        refine' add_le_add le_rfl _
        simp only [← Finset.card_fin, ← Finset.sum_const, ← nsmul_eq_mul, ← Ennreal.mul_div_le]_ = μ s + ε := by
        rw [add_assocₓ, Ennreal.add_halves]
    

/-! ### Consequences on differentiation of measures -/


/-- In a space with the Besicovitch covering property, the set of closed balls with positive radius
forms a Vitali family. This is essentially a restatement of the measurable Besicovitch theorem. -/
protected def vitaliFamily (μ : Measureₓ α) [SigmaFinite μ] : VitaliFamily μ where
  SetsAt := fun x => (fun r : ℝ => ClosedBall x r) '' Ioi (0 : ℝ)
  MeasurableSet' := by
    intro x y hy
    obtain ⟨r, rpos, rfl⟩ : ∃ r : ℝ, 0 < r ∧ closed_ball x r = y := by
      simpa only [← mem_image, ← mem_Ioi] using hy
    exact is_closed_ball.measurable_set
  nonempty_interior := by
    intro x y hy
    obtain ⟨r, rpos, rfl⟩ : ∃ r : ℝ, 0 < r ∧ closed_ball x r = y := by
      simpa only [← mem_image, ← mem_Ioi] using hy
    simp only [← nonempty.mono ball_subset_interior_closed_ball, ← rpos, ← nonempty_ball]
  Nontrivial := fun x ε εpos => ⟨ClosedBall x ε, mem_image_of_mem _ εpos, Subset.refl _⟩
  covering := by
    intro s f fsubset ffine
    let g : α → Set ℝ := fun x => { r | 0 < r ∧ closed_ball x r ∈ f x }
    have A : ∀, ∀ x ∈ s, ∀, ∀, ∀ δ > 0, ∀, (g x ∩ Ioo 0 δ).Nonempty := by
      intro x xs δ δpos
      obtain ⟨t, tf, ht⟩ : ∃ (t : Set α)(H : t ∈ f x), t ⊆ closed_ball x (δ / 2) := ffine x xs (δ / 2) (half_pos δpos)
      obtain ⟨r, rpos, rfl⟩ : ∃ r : ℝ, 0 < r ∧ closed_ball x r = t := by
        simpa using fsubset x xs tf
      rcases le_totalₓ r (δ / 2) with (H | H)
      · exact ⟨r, ⟨rpos, tf⟩, ⟨rpos, H.trans_lt (half_lt_self δpos)⟩⟩
        
      · have : closed_ball x r = closed_ball x (δ / 2) := subset.antisymm ht (closed_ball_subset_closed_ball H)
        rw [this] at tf
        refine' ⟨δ / 2, ⟨half_pos δpos, tf⟩, ⟨half_pos δpos, half_lt_self δpos⟩⟩
        
    obtain ⟨t, r, t_count, ts, tg, μt, tdisj⟩ :
      ∃ (t : Set α)(r : α → ℝ),
        t.Countable ∧
          t ⊆ s ∧
            (∀, ∀ x ∈ t, ∀, r x ∈ g x ∩ Ioo 0 1) ∧
              μ (s \ ⋃ x ∈ t, closed_ball x (r x)) = 0 ∧ t.PairwiseDisjoint fun x => closed_ball x (r x) :=
      exists_disjoint_closed_ball_covering_ae μ g s A (fun _ => 1) fun _ _ => zero_lt_one
    exact ⟨t, fun x => closed_ball x (r x), ts, tdisj, fun x xt => (tg x xt).1.2, μt⟩

/-- The main feature of the Besicovitch Vitali family is that its filter at a point `x` corresponds
to convergence along closed balls. We record one of the two implications here, which will enable us
to deduce specific statements on differentiation of measures in this context from the general
versions. -/
theorem tendsto_filter_at (μ : Measureₓ α) [SigmaFinite μ] (x : α) :
    Tendsto (fun r => ClosedBall x r) (𝓝[>] 0) ((Besicovitch.vitaliFamily μ).filterAt x) := by
  intro s hs
  simp only [← mem_map]
  obtain ⟨ε, εpos, hε⟩ :
    ∃ (ε : ℝ)(H : ε > 0), ∀ a : Set α, a ∈ (Besicovitch.vitaliFamily μ).SetsAt x → a ⊆ closed_ball x ε → a ∈ s :=
    (VitaliFamily.mem_filter_at_iff _).1 hs
  have : Ioc (0 : ℝ) ε ∈ 𝓝[>] (0 : ℝ) := Ioc_mem_nhds_within_Ioi ⟨le_rfl, εpos⟩
  filter_upwards [this] with _ hr
  apply hε
  · exact mem_image_of_mem _ hr.1
    
  · exact closed_ball_subset_closed_ball hr.2
    

variable [MetricSpace β] [MeasurableSpace β] [BorelSpace β] [SigmaCompactSpace β] [HasBesicovitchCovering β]

/-- In a space with the Besicovitch covering property, the ratio of the measure of balls converges
almost surely to to the Radon-Nikodym derivative. -/
theorem ae_tendsto_rn_deriv (ρ μ : Measureₓ β) [IsLocallyFiniteMeasure μ] [IsLocallyFiniteMeasure ρ] :
    ∀ᵐ x ∂μ, Tendsto (fun r => ρ (ClosedBall x r) / μ (ClosedBall x r)) (𝓝[>] 0) (𝓝 (ρ.rnDeriv μ x)) := by
  have : second_countable_topology β := Emetric.second_countable_of_sigma_compact β
  filter_upwards [VitaliFamily.ae_tendsto_rn_deriv (Besicovitch.vitaliFamily μ) ρ] with x hx
  exact hx.comp (tendsto_filter_at μ x)

/-- Given a measurable set `s`, then `μ (s ∩ closed_ball x r) / μ (closed_ball x r)` converges when
`r` tends to `0`, for almost every `x`. The limit is `1` for `x ∈ s` and `0` for `x ∉ s`.
This shows that almost every point of `s` is a Lebesgue density point for `s`.
A version for non-measurable sets holds, but it only gives the first conclusion,
see `ae_tendsto_measure_inter_div`. -/
theorem ae_tendsto_measure_inter_div_of_measurable_set (μ : Measureₓ β) [IsLocallyFiniteMeasure μ] {s : Set β}
    (hs : MeasurableSet s) :
    ∀ᵐ x ∂μ, Tendsto (fun r => μ (s ∩ ClosedBall x r) / μ (ClosedBall x r)) (𝓝[>] 0) (𝓝 (s.indicator 1 x)) := by
  have : second_countable_topology β := Emetric.second_countable_of_sigma_compact β
  filter_upwards [VitaliFamily.ae_tendsto_measure_inter_div_of_measurable_set (Besicovitch.vitaliFamily μ) hs]
  intro x hx
  exact hx.comp (tendsto_filter_at μ x)

/-- Given an arbitrary set `s`, then `μ (s ∩ closed_ball x r) / μ (closed_ball x r)` converges
to `1` when `r` tends to `0`, for almost every `x` in `s`.
This shows that almost every point of `s` is a Lebesgue density point for `s`.
A stronger version holds for measurable sets, see `ae_tendsto_measure_inter_div_of_measurable_set`.
-/
theorem ae_tendsto_measure_inter_div (μ : Measureₓ β) [IsLocallyFiniteMeasure μ] (s : Set β) :
    ∀ᵐ x ∂μ.restrict s, Tendsto (fun r => μ (s ∩ ClosedBall x r) / μ (ClosedBall x r)) (𝓝[>] 0) (𝓝 1) := by
  have : second_countable_topology β := Emetric.second_countable_of_sigma_compact β
  filter_upwards [VitaliFamily.ae_tendsto_measure_inter_div
      (Besicovitch.vitaliFamily μ)] with x hx using hx.comp (tendsto_filter_at μ x)

end Besicovitch

