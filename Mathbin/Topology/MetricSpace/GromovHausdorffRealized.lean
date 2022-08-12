/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathbin.Topology.MetricSpace.Gluing
import Mathbin.Topology.MetricSpace.HausdorffDistance
import Mathbin.Topology.ContinuousFunction.Bounded

/-!
# The Gromov-Hausdorff distance is realized

In this file, we construct of a good coupling between nonempty compact metric spaces, minimizing
their Hausdorff distance. This construction is instrumental to study the Gromov-Hausdorff
distance between nonempty compact metric spaces.

Given two nonempty compact metric spaces `X` and `Y`, we define `optimal_GH_coupling X Y` as a
compact metric space, together with two isometric embeddings `optimal_GH_injl` and `optimal_GH_injr`
respectively of `X` and `Y` into `optimal_GH_coupling X Y`. The main property of the optimal
coupling is that the Hausdorff distance between `X` and `Y` in `optimal_GH_coupling X Y` is smaller
than the corresponding distance in any other coupling. We do not prove completely this fact in this
file, but we show a good enough approximation of this fact in `Hausdorff_dist_optimal_le_HD`, that
will suffice to obtain the full statement once the Gromov-Hausdorff distance is properly defined,
in `Hausdorff_dist_optimal`.

The key point in the construction is that the set of possible distances coming from isometric
embeddings of `X` and `Y` in metric spaces is a set of equicontinuous functions. By Arzela-Ascoli,
it is compact, and one can find such a distance which is minimal. This distance defines a premetric
space structure on `X ⊕ Y`. The corresponding metric quotient is `optimal_GH_coupling X Y`.
-/


noncomputable section

open Classical TopologicalSpace Nnreal

universe u v w

open Classical Set Function TopologicalSpace Filter Metric Quotientₓ

open BoundedContinuousFunction

open Sum (inl inr)

attribute [local instance] metric_space_sum

namespace GromovHausdorff

section GromovHausdorffRealized

/- This section shows that the Gromov-Hausdorff distance
is realized. For this, we consider candidate distances on the disjoint union
`X ⊕ Y` of two compact nonempty metric spaces, almost realizing the Gromov-Hausdorff
distance, and show that they form a compact family by applying Arzela-Ascoli
theorem. The existence of a minimizer follows. -/
section Definitions

variable (X : Type u) (Y : Type v) [MetricSpace X] [CompactSpace X] [Nonempty X] [MetricSpace Y] [CompactSpace Y]
  [Nonempty Y]

@[reducible]
private def prod_space_fun : Type _ :=
  Sum X Y × Sum X Y → ℝ

@[reducible]
private def Cb : Type _ :=
  BoundedContinuousFunction (Sum X Y × Sum X Y) ℝ

private def max_var : ℝ≥0 :=
  2 * ⟨diam (Univ : Set X), diam_nonneg⟩ + 1 + 2 * ⟨diam (Univ : Set Y), diam_nonneg⟩

-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:63:9: parse error
private theorem one_le_max_var : 1 ≤ maxVar X Y :=
  calc
    (1 : Real) = 2 * 0 + 1 + 2 * 0 := by
      simp
    _ ≤ 2 * diam (Univ : Set X) + 1 + 2 * diam (Univ : Set Y) := by
      apply_rules [add_le_add, mul_le_mul_of_nonneg_left, diam_nonneg] <;> norm_num
    

/-- The set of functions on `X ⊕ Y` that are candidates distances to realize the
minimum of the Hausdorff distances between `X` and `Y` in a coupling -/
def Candidates : Set (ProdSpaceFun X Y) :=
  { f |
    (((((∀ x y : X, f (Sum.inl x, Sum.inl y) = dist x y) ∧ ∀ x y : Y, f (Sum.inr x, Sum.inr y) = dist x y) ∧
            ∀ x y, f (x, y) = f (y, x)) ∧
          ∀ x y z, f (x, z) ≤ f (x, y) + f (y, z)) ∧
        ∀ x, f (x, x) = 0) ∧
      ∀ x y, f (x, y) ≤ maxVar X Y }

/-- Version of the set of candidates in bounded_continuous_functions, to apply
Arzela-Ascoli -/
private def candidates_b : Set (Cb X Y) :=
  { f : Cb X Y | (f : _ → ℝ) ∈ Candidates X Y }

end Definitions

--section
section Constructions

variable {X : Type u} {Y : Type v} [MetricSpace X] [CompactSpace X] [Nonempty X] [MetricSpace Y] [CompactSpace Y]
  [Nonempty Y] {f : ProdSpaceFun X Y} {x y z t : Sum X Y}

attribute [local instance] inhabited_of_nonempty'

-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:63:9: parse error
private theorem max_var_bound : dist x y ≤ maxVar X Y :=
  calc
    dist x y ≤ diam (Univ : Set (Sum X Y)) := dist_le_diam_of_mem bounded_of_compact_space (mem_univ _) (mem_univ _)
    _ = diam (inl '' (Univ : Set X) ∪ inr '' (Univ : Set Y)) := by
      apply congr_arg <;> ext x y z <;> cases x <;> simp [← mem_univ, ← mem_range_self]
    _ ≤ diam (inl '' (Univ : Set X)) + dist (inl default) (inr default) + diam (inr '' (Univ : Set Y)) :=
      diam_union (mem_image_of_mem _ (mem_univ _)) (mem_image_of_mem _ (mem_univ _))
    _ = diam (Univ : Set X) + (dist default default + 1 + dist default default) + diam (Univ : Set Y) := by
      rw [isometry_inl.diam_image, isometry_inr.diam_image]
      rfl
    _ = 1 * diam (Univ : Set X) + 1 + 1 * diam (Univ : Set Y) := by
      simp
    _ ≤ 2 * diam (Univ : Set X) + 1 + 2 * diam (Univ : Set Y) := by
      apply_rules [add_le_add, mul_le_mul_of_nonneg_right, diam_nonneg, le_reflₓ]
      norm_num
      norm_num
    

private theorem candidates_symm (fA : f ∈ Candidates X Y) : f (x, y) = f (y, x) :=
  fA.1.1.1.2 x y

private theorem candidates_triangle (fA : f ∈ Candidates X Y) : f (x, z) ≤ f (x, y) + f (y, z) :=
  fA.1.1.2 x y z

private theorem candidates_refl (fA : f ∈ Candidates X Y) : f (x, x) = 0 :=
  fA.1.2 x

private theorem candidates_nonneg (fA : f ∈ Candidates X Y) : 0 ≤ f (x, y) := by
  have : 0 ≤ 2 * f (x, y) :=
    calc
      0 = f (x, x) := (candidates_refl fA).symm
      _ ≤ f (x, y) + f (y, x) := candidates_triangle fA
      _ = f (x, y) + f (x, y) := by
        rw [candidates_symm fA]
      _ = 2 * f (x, y) := by
        ring
      
  · linarith
    

private theorem candidates_dist_inl (fA : f ∈ Candidates X Y) (x y : X) : f (inl x, inl y) = dist x y :=
  fA.1.1.1.1.1 x y

private theorem candidates_dist_inr (fA : f ∈ Candidates X Y) (x y : Y) : f (inr x, inr y) = dist x y :=
  fA.1.1.1.1.2 x y

private theorem candidates_le_max_var (fA : f ∈ Candidates X Y) : f (x, y) ≤ maxVar X Y :=
  fA.2 x y

/-- candidates are bounded by `max_var X Y` -/
private theorem candidates_dist_bound (fA : f ∈ Candidates X Y) : ∀ {x y : Sum X Y}, f (x, y) ≤ maxVar X Y * dist x y
  | inl x, inl y =>
    calc
      f (inl x, inl y) = dist x y := candidates_dist_inl fA x y
      _ = dist (inl x) (inl y) := by
        rw [@sum.dist_eq X Y]
        rfl
      _ = 1 * dist (inl x) (inl y) := by
        simp
      _ ≤ maxVar X Y * dist (inl x) (inl y) := mul_le_mul_of_nonneg_right (one_le_max_var X Y) dist_nonneg
      
  | inl x, inr y =>
    calc
      f (inl x, inr y) ≤ maxVar X Y := candidates_le_max_var fA
      _ = maxVar X Y * 1 := by
        simp
      _ ≤ maxVar X Y * dist (inl x) (inr y) :=
        mul_le_mul_of_nonneg_left Sum.one_dist_le (le_transₓ zero_le_one (one_le_max_var X Y))
      
  | inr x, inl y =>
    calc
      f (inr x, inl y) ≤ maxVar X Y := candidates_le_max_var fA
      _ = maxVar X Y * 1 := by
        simp
      _ ≤ maxVar X Y * dist (inl x) (inr y) :=
        mul_le_mul_of_nonneg_left Sum.one_dist_le (le_transₓ zero_le_one (one_le_max_var X Y))
      
  | inr x, inr y =>
    calc
      f (inr x, inr y) = dist x y := candidates_dist_inr fA x y
      _ = dist (inr x) (inr y) := by
        rw [@sum.dist_eq X Y]
        rfl
      _ = 1 * dist (inr x) (inr y) := by
        simp
      _ ≤ maxVar X Y * dist (inr x) (inr y) := mul_le_mul_of_nonneg_right (one_le_max_var X Y) dist_nonneg
      

/-- Technical lemma to prove that candidates are Lipschitz -/
private theorem candidates_lipschitz_aux (fA : f ∈ Candidates X Y) :
    f (x, y) - f (z, t) ≤ 2 * maxVar X Y * dist (x, y) (z, t) :=
  calc
    f (x, y) - f (z, t) ≤ f (x, t) + f (t, y) - f (z, t) := sub_le_sub_right (candidates_triangle fA) _
    _ ≤ f (x, z) + f (z, t) + f (t, y) - f (z, t) := sub_le_sub_right (add_le_add_right (candidates_triangle fA) _) _
    _ = f (x, z) + f (t, y) := by
      simp [← sub_eq_add_neg, ← add_assocₓ]
    _ ≤ maxVar X Y * dist x z + maxVar X Y * dist t y :=
      add_le_add (candidates_dist_bound fA) (candidates_dist_bound fA)
    _ ≤ maxVar X Y * max (dist x z) (dist t y) + maxVar X Y * max (dist x z) (dist t y) := by
      apply add_le_add
      apply mul_le_mul_of_nonneg_left (le_max_leftₓ (dist x z) (dist t y)) (zero_le_one.trans (one_le_max_var X Y))
      apply mul_le_mul_of_nonneg_left (le_max_rightₓ (dist x z) (dist t y)) (zero_le_one.trans (one_le_max_var X Y))
    _ = 2 * maxVar X Y * max (dist x z) (dist y t) := by
      simp [← dist_comm]
      ring
    _ = 2 * maxVar X Y * dist (x, y) (z, t) := by
      rfl
    

/-- Candidates are Lipschitz -/
private theorem candidates_lipschitz (fA : f ∈ Candidates X Y) : LipschitzWith (2 * maxVar X Y) f := by
  apply LipschitzWith.of_dist_le_mul
  rintro ⟨x, y⟩ ⟨z, t⟩
  rw [Real.dist_eq, abs_sub_le_iff]
  use candidates_lipschitz_aux fA
  rw [dist_comm]
  exact candidates_lipschitz_aux fA

/-- candidates give rise to elements of bounded_continuous_functions -/
def candidatesBOfCandidates (f : ProdSpaceFun X Y) (fA : f ∈ Candidates X Y) : Cb X Y :=
  BoundedContinuousFunction.mkOfCompact ⟨f, (candidates_lipschitz fA).Continuous⟩

theorem candidates_b_of_candidates_mem (f : ProdSpaceFun X Y) (fA : f ∈ Candidates X Y) :
    candidatesBOfCandidates f fA ∈ CandidatesB X Y :=
  fA

/-- The distance on `X ⊕ Y` is a candidate -/
private theorem dist_mem_candidates : (fun p : Sum X Y × Sum X Y => dist p.1 p.2) ∈ Candidates X Y := by
  simp only [← candidates, ← dist_comm, ← forall_const, ← and_trueₓ, ← add_commₓ, ← eq_self_iff_true, ← and_selfₓ, ←
    Sum.forall, ← Set.mem_set_of_eq, ← dist_self]
  repeat'
    first |
      constructor|
      exact fun a y z => dist_triangle_left _ _ _|
      exact fun x y => by
        rfl|
      exact fun x y => max_var_bound

/-- The distance on `X ⊕ Y` as a candidate -/
def candidatesBDist (X : Type u) (Y : Type v) [MetricSpace X] [CompactSpace X] [Inhabited X] [MetricSpace Y]
    [CompactSpace Y] [Inhabited Y] : Cb X Y :=
  candidatesBOfCandidates _ dist_mem_candidates

theorem candidates_b_dist_mem_candidates_b : candidatesBDist X Y ∈ CandidatesB X Y :=
  candidates_b_of_candidates_mem _ _

private theorem candidates_b_nonempty : (CandidatesB X Y).Nonempty :=
  ⟨_, candidates_b_dist_mem_candidates_b⟩

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (x y)
-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (x y)
-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (x y)
-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (x y z)
-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (x y)
/-- To apply Arzela-Ascoli, we need to check that the set of candidates is closed and
equicontinuous. Equicontinuity follows from the Lipschitz control, we check closedness. -/
private theorem closed_candidates_b : IsClosed (CandidatesB X Y) := by
  have I1 : ∀ x y, IsClosed { f : Cb X Y | f (inl x, inl y) = dist x y } := fun x y =>
    is_closed_eq continuous_eval_const continuous_const
  have I2 : ∀ x y, IsClosed { f : Cb X Y | f (inr x, inr y) = dist x y } := fun x y =>
    is_closed_eq continuous_eval_const continuous_const
  have I3 : ∀ x y, IsClosed { f : Cb X Y | f (x, y) = f (y, x) } := fun x y =>
    is_closed_eq continuous_eval_const continuous_eval_const
  have I4 : ∀ x y z, IsClosed { f : Cb X Y | f (x, z) ≤ f (x, y) + f (y, z) } := fun x y z =>
    is_closed_le continuous_eval_const (continuous_eval_const.add continuous_eval_const)
  have I5 : ∀ x, IsClosed { f : Cb X Y | f (x, x) = 0 } := fun x => is_closed_eq continuous_eval_const continuous_const
  have I6 : ∀ x y, IsClosed { f : Cb X Y | f (x, y) ≤ max_var X Y } := fun x y =>
    is_closed_le continuous_eval_const continuous_const
  have :
    candidates_b X Y =
      (((((⋂ (x) (y), { f : Cb X Y | f (@inl X Y x, @inl X Y y) = dist x y }) ∩
                ⋂ (x) (y), { f : Cb X Y | f (@inr X Y x, @inr X Y y) = dist x y }) ∩
              ⋂ (x) (y), { f : Cb X Y | f (x, y) = f (y, x) }) ∩
            ⋂ (x) (y) (z), { f : Cb X Y | f (x, z) ≤ f (x, y) + f (y, z) }) ∩
          ⋂ x, { f : Cb X Y | f (x, x) = 0 }) ∩
        ⋂ (x) (y), { f : Cb X Y | f (x, y) ≤ max_var X Y } :=
    by
    ext
    simp only [← candidates_b, ← candidates, ← mem_inter_eq, ← mem_Inter, ← mem_set_of_eq]
  rw [this]
  repeat'
    first |
      apply IsClosed.inter _ _|
      apply is_closed_Inter _|
      apply I1 _ _|
      apply I2 _ _|
      apply I3 _ _|
      apply I4 _ _ _|
      apply I5 _|
      apply I6 _ _|
      intro x

/-- Compactness of candidates (in bounded_continuous_functions) follows. -/
private theorem compact_candidates_b : IsCompact (CandidatesB X Y) := by
  refine' arzela_ascoli₂ (Icc 0 (max_var X Y)) is_compact_Icc (candidates_b X Y) closed_candidates_b _ _
  · rintro f ⟨x1, x2⟩ hf
    simp only [← Set.mem_Icc]
    exact ⟨candidates_nonneg hf, candidates_le_max_var hf⟩
    
  · refine' equicontinuous_of_continuity_modulus (fun t => 2 * max_var X Y * t) _ _ _
    · have : tendsto (fun t : ℝ => 2 * (max_var X Y : ℝ) * t) (𝓝 0) (𝓝 (2 * max_var X Y * 0)) :=
        tendsto_const_nhds.mul tendsto_id
      simpa using this
      
    · intro x y f hf
      exact (candidates_lipschitz hf).dist_le_mul _ _
      
    

/-- We will then choose the candidate minimizing the Hausdorff distance. Except that we are not
in a metric space setting, so we need to define our custom version of Hausdorff distance,
called HD, and prove its basic properties. -/
def hD (f : Cb X Y) :=
  max (⨆ x, ⨅ y, f (inl x, inr y)) (⨆ y, ⨅ x, f (inl x, inr y))

/- We will show that HD is continuous on bounded_continuous_functions, to deduce that its
minimum on the compact set candidates_b is attained. Since it is defined in terms of
infimum and supremum on `ℝ`, which is only conditionnally complete, we will need all the time
to check that the defining sets are bounded below or above. This is done in the next few
technical lemmas -/
theorem HD_below_aux1 {f : Cb X Y} (C : ℝ) {x : X} : BddBelow (Range fun y : Y => f (inl x, inr y) + C) :=
  let ⟨cf, hcf⟩ := (Real.bounded_iff_bdd_below_bdd_above.1 f.bounded_range).1
  ⟨cf + C, forall_range_iff.2 fun i => add_le_add_right ((fun x => hcf (mem_range_self x)) _) _⟩

private theorem HD_bound_aux1 (f : Cb X Y) (C : ℝ) : BddAbove (Range fun x : X => ⨅ y, f (inl x, inr y) + C) := by
  rcases(Real.bounded_iff_bdd_below_bdd_above.1 f.bounded_range).2 with ⟨Cf, hCf⟩
  refine' ⟨Cf + C, forall_range_iff.2 fun x => _⟩
  calc (⨅ y, f (inl x, inr y) + C) ≤ f (inl x, inr default) + C := cinfi_le (HD_below_aux1 C) default _ ≤ Cf + C :=
      add_le_add ((fun x => hCf (mem_range_self x)) _) le_rfl

theorem HD_below_aux2 {f : Cb X Y} (C : ℝ) {y : Y} : BddBelow (Range fun x : X => f (inl x, inr y) + C) :=
  let ⟨cf, hcf⟩ := (Real.bounded_iff_bdd_below_bdd_above.1 f.bounded_range).1
  ⟨cf + C, forall_range_iff.2 fun i => add_le_add_right ((fun x => hcf (mem_range_self x)) _) _⟩

private theorem HD_bound_aux2 (f : Cb X Y) (C : ℝ) : BddAbove (Range fun y : Y => ⨅ x, f (inl x, inr y) + C) := by
  rcases(Real.bounded_iff_bdd_below_bdd_above.1 f.bounded_range).2 with ⟨Cf, hCf⟩
  refine' ⟨Cf + C, forall_range_iff.2 fun y => _⟩
  calc (⨅ x, f (inl x, inr y) + C) ≤ f (inl default, inr y) + C := cinfi_le (HD_below_aux2 C) default _ ≤ Cf + C :=
      add_le_add ((fun x => hCf (mem_range_self x)) _) le_rfl

-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:51:50: missing argument
-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:51:50: missing argument
-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:51:50: missing argument
-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:51:50: missing argument
/-- Explicit bound on `HD (dist)`. This means that when looking for minimizers it will
be sufficient to look for functions with `HD(f)` bounded by this bound. -/
theorem HD_candidates_b_dist_le : hD (candidatesBDist X Y) ≤ diam (Univ : Set X) + 1 + diam (Univ : Set Y) := by
  refine' max_leₓ (csupr_le fun x => _) (csupr_le fun y => _)
  · have A : (⨅ y, candidates_b_dist X Y (inl x, inr y)) ≤ candidates_b_dist X Y (inl x, inr default) :=
      cinfi_le
        (by
          simpa using HD_below_aux1 0)
        default
    have B : dist (inl x) (inr default) ≤ diam (univ : Set X) + 1 + diam (univ : Set Y) :=
      calc
        dist (inl x) (inr (default : Y)) = dist x (default : X) + 1 + dist default default := rfl
        _ ≤ diam (univ : Set X) + 1 + diam (univ : Set Y) := by
          apply add_le_add (add_le_add _ le_rfl)
          exact dist_le_diam_of_mem bounded_of_compact_space (mem_univ _) (mem_univ _)
          any_goals {
          }
          any_goals {
          }
          exact dist_le_diam_of_mem bounded_of_compact_space (mem_univ _) (mem_univ _)
        
    exact le_transₓ A B
    
  · have A : (⨅ x, candidates_b_dist X Y (inl x, inr y)) ≤ candidates_b_dist X Y (inl default, inr y) :=
      cinfi_le
        (by
          simpa using HD_below_aux2 0)
        default
    have B : dist (inl default) (inr y) ≤ diam (univ : Set X) + 1 + diam (univ : Set Y) :=
      calc
        dist (inl (default : X)) (inr y) = dist default default + 1 + dist default y := rfl
        _ ≤ diam (univ : Set X) + 1 + diam (univ : Set Y) := by
          apply add_le_add (add_le_add _ le_rfl)
          exact dist_le_diam_of_mem bounded_of_compact_space (mem_univ _) (mem_univ _)
          any_goals {
          }
          any_goals {
          }
          exact dist_le_diam_of_mem bounded_of_compact_space (mem_univ _) (mem_univ _)
        
    exact le_transₓ A B
    

/- To check that HD is continuous, we check that it is Lipschitz. As HD is a max, we
prove separately inequalities controlling the two terms (relying too heavily on copy-paste...) -/
private theorem HD_lipschitz_aux1 (f g : Cb X Y) :
    (⨆ x, ⨅ y, f (inl x, inr y)) ≤ (⨆ x, ⨅ y, g (inl x, inr y)) + dist f g := by
  rcases(Real.bounded_iff_bdd_below_bdd_above.1 g.bounded_range).1 with ⟨cg, hcg⟩
  have Hcg : ∀ x, cg ≤ g x := fun x => hcg (mem_range_self x)
  rcases(Real.bounded_iff_bdd_below_bdd_above.1 f.bounded_range).1 with ⟨cf, hcf⟩
  have Hcf : ∀ x, cf ≤ f x := fun x => hcf (mem_range_self x)
  -- prove the inequality but with `dist f g` inside, by using inequalities comparing
  -- supr to supr and infi to infi
  have Z : (⨆ x, ⨅ y, f (inl x, inr y)) ≤ ⨆ x, ⨅ y, g (inl x, inr y) + dist f g :=
    csupr_mono (HD_bound_aux1 _ (dist f g)) fun x =>
      cinfi_mono ⟨cf, forall_range_iff.2 fun i => Hcf _⟩ fun y => coe_le_coe_add_dist
  -- move the `dist f g` out of the infimum and the supremum, arguing that continuous monotone maps
  -- (here the addition of `dist f g`) preserve infimum and supremum
  have E1 : ∀ x, (⨅ y, g (inl x, inr y)) + dist f g = ⨅ y, g (inl x, inr y) + dist f g := by
    intro x
    refine' map_cinfi_of_continuous_at_of_monotone (continuous_at_id.add continuous_at_const) _ _
    · intro x y hx
      simpa
      
    · show BddBelow (range fun y : Y => g (inl x, inr y))
      exact ⟨cg, forall_range_iff.2 fun i => Hcg _⟩
      
  have E2 : (⨆ x, ⨅ y, g (inl x, inr y)) + dist f g = ⨆ x, (⨅ y, g (inl x, inr y)) + dist f g := by
    refine' map_csupr_of_continuous_at_of_monotone (continuous_at_id.add continuous_at_const) _ _
    · intro x y hx
      simpa
      
    · simpa using HD_bound_aux1 _ 0
      
  -- deduce the result from the above two steps
  simpa [← E2, ← E1, ← Function.comp]

private theorem HD_lipschitz_aux2 (f g : Cb X Y) :
    (⨆ y, ⨅ x, f (inl x, inr y)) ≤ (⨆ y, ⨅ x, g (inl x, inr y)) + dist f g := by
  rcases(Real.bounded_iff_bdd_below_bdd_above.1 g.bounded_range).1 with ⟨cg, hcg⟩
  have Hcg : ∀ x, cg ≤ g x := fun x => hcg (mem_range_self x)
  rcases(Real.bounded_iff_bdd_below_bdd_above.1 f.bounded_range).1 with ⟨cf, hcf⟩
  have Hcf : ∀ x, cf ≤ f x := fun x => hcf (mem_range_self x)
  -- prove the inequality but with `dist f g` inside, by using inequalities comparing
  -- supr to supr and infi to infi
  have Z : (⨆ y, ⨅ x, f (inl x, inr y)) ≤ ⨆ y, ⨅ x, g (inl x, inr y) + dist f g :=
    csupr_mono (HD_bound_aux2 _ (dist f g)) fun y =>
      cinfi_mono ⟨cf, forall_range_iff.2 fun i => Hcf _⟩ fun y => coe_le_coe_add_dist
  -- move the `dist f g` out of the infimum and the supremum, arguing that continuous monotone maps
  -- (here the addition of `dist f g`) preserve infimum and supremum
  have E1 : ∀ y, (⨅ x, g (inl x, inr y)) + dist f g = ⨅ x, g (inl x, inr y) + dist f g := by
    intro y
    refine' map_cinfi_of_continuous_at_of_monotone (continuous_at_id.add continuous_at_const) _ _
    · intro x y hx
      simpa
      
    · show BddBelow (range fun x : X => g (inl x, inr y))
      exact ⟨cg, forall_range_iff.2 fun i => Hcg _⟩
      
  have E2 : (⨆ y, ⨅ x, g (inl x, inr y)) + dist f g = ⨆ y, (⨅ x, g (inl x, inr y)) + dist f g := by
    refine' map_csupr_of_continuous_at_of_monotone (continuous_at_id.add continuous_at_const) _ _
    · intro x y hx
      simpa
      
    · simpa using HD_bound_aux2 _ 0
      
  -- deduce the result from the above two steps
  simpa [← E2, ← E1]

private theorem HD_lipschitz_aux3 (f g : Cb X Y) : hD f ≤ hD g + dist f g :=
  max_leₓ (le_transₓ (HD_lipschitz_aux1 f g) (add_le_add_right (le_max_leftₓ _ _) _))
    (le_transₓ (HD_lipschitz_aux2 f g) (add_le_add_right (le_max_rightₓ _ _) _))

/-- Conclude that HD, being Lipschitz, is continuous -/
private theorem HD_continuous : Continuous (hD : Cb X Y → ℝ) :=
  LipschitzWith.continuous (LipschitzWith.of_le_add HD_lipschitz_aux3)

end Constructions

--section
section Consequences

variable (X : Type u) (Y : Type v) [MetricSpace X] [CompactSpace X] [Nonempty X] [MetricSpace Y] [CompactSpace Y]
  [Nonempty Y]

/- Now that we have proved that the set of candidates is compact, and that HD is continuous,
we can finally select a candidate minimizing HD. This will be the candidate realizing the
optimal coupling. -/
private theorem exists_minimizer : ∃ f ∈ CandidatesB X Y, ∀, ∀ g ∈ CandidatesB X Y, ∀, hD f ≤ hD g :=
  compact_candidates_b.exists_forall_le candidates_b_nonempty HD_continuous.ContinuousOn

private def optimal_GH_dist : Cb X Y :=
  Classical.some (exists_minimizer X Y)

private theorem optimal_GH_dist_mem_candidates_b : optimalGHDist X Y ∈ CandidatesB X Y := by
  cases Classical.some_spec (exists_minimizer X Y) <;> assumption

private theorem HD_optimal_GH_dist_le (g : Cb X Y) (hg : g ∈ CandidatesB X Y) : hD (optimalGHDist X Y) ≤ hD g :=
  let ⟨Z1, Z2⟩ := Classical.some_spec (exists_minimizer X Y)
  Z2 g hg

/-- With the optimal candidate, construct a premetric space structure on `X ⊕ Y`, on which the
predistance is given by the candidate. Then, we will identify points at `0` predistance
to obtain a genuine metric space -/
def premetricOptimalGHDist : PseudoMetricSpace (Sum X Y) where
  dist := fun p q => optimalGHDist X Y (p, q)
  dist_self := fun x => candidates_refl (optimal_GH_dist_mem_candidates_b X Y)
  dist_comm := fun x y => candidates_symm (optimal_GH_dist_mem_candidates_b X Y)
  dist_triangle := fun x y z => candidates_triangle (optimal_GH_dist_mem_candidates_b X Y)

attribute [local instance] premetric_optimal_GH_dist PseudoMetric.distSetoid

/-- A metric space which realizes the optimal coupling between `X` and `Y` -/
@[nolint has_inhabited_instance]
def OptimalGHCoupling : Type _ :=
  PseudoMetricQuot (Sum X Y)deriving MetricSpace

/-- Injection of `X` in the optimal coupling between `X` and `Y` -/
def optimalGHInjl (x : X) : OptimalGHCoupling X Y :=
  ⟦inl x⟧

/-- The injection of `X` in the optimal coupling between `X` and `Y` is an isometry. -/
theorem isometry_optimal_GH_injl : Isometry (optimalGHInjl X Y) := by
  refine' isometry_emetric_iff_metric.2 fun x y => _
  change dist ⟦inl x⟧ ⟦inl y⟧ = dist x y
  exact candidates_dist_inl (optimal_GH_dist_mem_candidates_b X Y) _ _

/-- Injection of `Y` in the optimal coupling between `X` and `Y` -/
def optimalGHInjr (y : Y) : OptimalGHCoupling X Y :=
  ⟦inr y⟧

/-- The injection of `Y` in the optimal coupling between `X` and `Y` is an isometry. -/
theorem isometry_optimal_GH_injr : Isometry (optimalGHInjr X Y) := by
  refine' isometry_emetric_iff_metric.2 fun x y => _
  change dist ⟦inr x⟧ ⟦inr y⟧ = dist x y
  exact candidates_dist_inr (optimal_GH_dist_mem_candidates_b X Y) _ _

/-- The optimal coupling between two compact spaces `X` and `Y` is still a compact space -/
instance compact_space_optimal_GH_coupling : CompactSpace (OptimalGHCoupling X Y) :=
  ⟨by
    have : (univ : Set (optimal_GH_coupling X Y)) = optimal_GH_injl X Y '' univ ∪ optimal_GH_injr X Y '' univ := by
      refine' subset.antisymm (fun xc hxc => _) (subset_univ _)
      rcases Quotientₓ.exists_rep xc with ⟨x, hx⟩
      cases x <;> rw [← hx]
      · have : ⟦inl x⟧ = optimal_GH_injl X Y x := rfl
        rw [this]
        exact mem_union_left _ (mem_image_of_mem _ (mem_univ _))
        
      · have : ⟦inr x⟧ = optimal_GH_injr X Y x := rfl
        rw [this]
        exact mem_union_right _ (mem_image_of_mem _ (mem_univ _))
        
    rw [this]
    exact
      (compact_univ.image (isometry_optimal_GH_injl X Y).Continuous).union
        (compact_univ.image (isometry_optimal_GH_injr X Y).Continuous)⟩

/-- For any candidate `f`, `HD(f)` is larger than or equal to the Hausdorff distance in the
optimal coupling. This follows from the fact that HD of the optimal candidate is exactly
the Hausdorff distance in the optimal coupling, although we only prove here the inequality
we need. -/
theorem Hausdorff_dist_optimal_le_HD {f} (h : f ∈ CandidatesB X Y) :
    hausdorffDist (Range (optimalGHInjl X Y)) (Range (optimalGHInjr X Y)) ≤ hD f := by
  refine' le_transₓ (le_of_forall_le_of_dense fun r hr => _) (HD_optimal_GH_dist_le X Y f h)
  have A : ∀, ∀ x ∈ range (optimal_GH_injl X Y), ∀, ∃ y ∈ range (optimal_GH_injr X Y), dist x y ≤ r := by
    intro x hx
    rcases mem_range.1 hx with ⟨z, hz⟩
    rw [← hz]
    have I1 : (⨆ x, ⨅ y, optimal_GH_dist X Y (inl x, inr y)) < r := lt_of_le_of_ltₓ (le_max_leftₓ _ _) hr
    have I2 : (⨅ y, optimal_GH_dist X Y (inl z, inr y)) ≤ ⨆ x, ⨅ y, optimal_GH_dist X Y (inl x, inr y) :=
      le_cSup
        (by
          simpa using HD_bound_aux1 _ 0)
        (mem_range_self _)
    have I : (⨅ y, optimal_GH_dist X Y (inl z, inr y)) < r := lt_of_le_of_ltₓ I2 I1
    rcases exists_lt_of_cInf_lt (range_nonempty _) I with ⟨r', r'range, hr'⟩
    rcases mem_range.1 r'range with ⟨z', hz'⟩
    exists optimal_GH_injr X Y z', mem_range_self _
    have : (optimal_GH_dist X Y) (inl z, inr z') ≤ r := by
      rw [hz']
      exact le_of_ltₓ hr'
    exact this
  refine' Hausdorff_dist_le_of_mem_dist _ A _
  · rcases exists_mem_of_nonempty X with ⟨xX, _⟩
    have : optimal_GH_injl X Y xX ∈ range (optimal_GH_injl X Y) := mem_range_self _
    rcases A _ this with ⟨y, yrange, hy⟩
    exact le_transₓ dist_nonneg hy
    
  · intro y hy
    rcases mem_range.1 hy with ⟨z, hz⟩
    rw [← hz]
    have I1 : (⨆ y, ⨅ x, optimal_GH_dist X Y (inl x, inr y)) < r := lt_of_le_of_ltₓ (le_max_rightₓ _ _) hr
    have I2 : (⨅ x, optimal_GH_dist X Y (inl x, inr z)) ≤ ⨆ y, ⨅ x, optimal_GH_dist X Y (inl x, inr y) :=
      le_cSup
        (by
          simpa using HD_bound_aux2 _ 0)
        (mem_range_self _)
    have I : (⨅ x, optimal_GH_dist X Y (inl x, inr z)) < r := lt_of_le_of_ltₓ I2 I1
    rcases exists_lt_of_cInf_lt (range_nonempty _) I with ⟨r', r'range, hr'⟩
    rcases mem_range.1 r'range with ⟨z', hz'⟩
    exists optimal_GH_injl X Y z', mem_range_self _
    have : (optimal_GH_dist X Y) (inl z', inr z) ≤ r := by
      rw [hz']
      exact le_of_ltₓ hr'
    rw [dist_comm]
    exact this
    

end Consequences

-- We are done with the construction of the optimal coupling
end GromovHausdorffRealized

end GromovHausdorff

