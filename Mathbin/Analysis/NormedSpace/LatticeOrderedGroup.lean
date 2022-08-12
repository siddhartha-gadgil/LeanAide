/-
Copyright (c) 2021 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
import Mathbin.Topology.Order.Lattice
import Mathbin.Analysis.Normed.Group.Basic
import Mathbin.Algebra.Order.LatticeGroup

/-!
# Normed lattice ordered groups

Motivated by the theory of Banach Lattices, we then define `normed_lattice_add_comm_group` as a
lattice with a covariant normed group addition satisfying the solid axiom.

## Main statements

We show that a normed lattice ordered group is a topological lattice with respect to the norm
topology.

## References

* [Meyer-Nieberg, Banach lattices][MeyerNieberg1991]

## Tags

normed, lattice, ordered, group
-/


/-!
### Normed lattice orderd groups

Motivated by the theory of Banach Lattices, this section introduces normed lattice ordered groups.
-/


-- mathport name: «expr| |»
local notation "|" a "|" => abs a

/-- Let `α` be a normed commutative group equipped with a partial order covariant with addition, with
respect which `α` forms a lattice. Suppose that `α` is *solid*, that is to say, for `a` and `b` in
`α`, with absolute values `|a|` and `|b|` respectively, `|a| ≤ |b|` implies `∥a∥ ≤ ∥b∥`. Then `α` is
said to be a normed lattice ordered group.
-/
class NormedLatticeAddCommGroup (α : Type _) extends NormedGroup α, Lattice α where
  add_le_add_left : ∀ a b : α, a ≤ b → ∀ c : α, c + a ≤ c + b
  solid : ∀ a b : α, |a| ≤ |b| → ∥a∥ ≤ ∥b∥

theorem solid {α : Type _} [NormedLatticeAddCommGroup α] {a b : α} (h : |a| ≤ |b|) : ∥a∥ ≤ ∥b∥ :=
  NormedLatticeAddCommGroup.solid a b h

noncomputable instance : NormedLatticeAddCommGroup ℝ where
  add_le_add_left := fun _ _ h _ => add_le_add le_rfl h
  solid := fun _ _ => id

/-- A normed lattice ordered group is an ordered additive commutative group
-/
-- see Note [lower instance priority]
instance (priority := 100) normedLatticeAddCommGroupToOrderedAddCommGroup {α : Type _}
    [h : NormedLatticeAddCommGroup α] : OrderedAddCommGroup α :=
  { h with }

/-- Let `α` be a normed group with a partial order. Then the order dual is also a normed group.
-/
-- see Note [lower instance priority]
instance (priority := 100) {α : Type _} : ∀ [NormedGroup α], NormedGroup αᵒᵈ :=
  id

variable {α : Type _} [NormedLatticeAddCommGroup α]

open LatticeOrderedCommGroup

theorem dual_solid (a b : α) (h : b⊓-b ≤ a⊓-a) : ∥a∥ ≤ ∥b∥ := by
  apply solid
  rw [abs_eq_sup_neg]
  nth_rw 0[← neg_negₓ a]
  rw [← neg_inf_eq_sup_neg]
  rw [abs_eq_sup_neg]
  nth_rw 0[← neg_negₓ b]
  rwa [← neg_inf_eq_sup_neg, neg_le_neg_iff, @inf_comm _ _ _ b, @inf_comm _ _ _ a]

/-- Let `α` be a normed lattice ordered group, then the order dual is also a
normed lattice ordered group.
-/
-- see Note [lower instance priority]
instance (priority := 100) : NormedLatticeAddCommGroup αᵒᵈ where
  add_le_add_left := fun a b => add_le_add_left
  solid := dual_solid

theorem norm_abs_eq_norm (a : α) : ∥|a|∥ = ∥a∥ :=
  (solid (abs_abs a).le).antisymm (solid (abs_abs a).symm.le)

theorem norm_inf_sub_inf_le_add_norm (a b c d : α) : ∥a⊓b - c⊓d∥ ≤ ∥a - c∥ + ∥b - d∥ := by
  rw [← norm_abs_eq_norm (a - c), ← norm_abs_eq_norm (b - d)]
  refine' le_transₓ (solid _) (norm_add_le |a - c| |b - d|)
  rw [abs_of_nonneg (|a - c| + |b - d|) (add_nonneg (abs_nonneg (a - c)) (abs_nonneg (b - d)))]
  calc |a⊓b - c⊓d| = |a⊓b - c⊓b + (c⊓b - c⊓d)| := by
      rw [sub_add_sub_cancel]_ ≤ |a⊓b - c⊓b| + |c⊓b - c⊓d| := abs_add_le _ _ _ ≤ |a - c| + |b - d| := by
      apply add_le_add
      · exact abs_inf_sub_inf_le_abs _ _ _
        
      · rw [@inf_comm _ _ c, @inf_comm _ _ c]
        exact abs_inf_sub_inf_le_abs _ _ _
        

theorem norm_sup_sub_sup_le_add_norm (a b c d : α) : ∥a⊔b - c⊔d∥ ≤ ∥a - c∥ + ∥b - d∥ := by
  rw [← norm_abs_eq_norm (a - c), ← norm_abs_eq_norm (b - d)]
  refine' le_transₓ (solid _) (norm_add_le |a - c| |b - d|)
  rw [abs_of_nonneg (|a - c| + |b - d|) (add_nonneg (abs_nonneg (a - c)) (abs_nonneg (b - d)))]
  calc |a⊔b - c⊔d| = |a⊔b - c⊔b + (c⊔b - c⊔d)| := by
      rw [sub_add_sub_cancel]_ ≤ |a⊔b - c⊔b| + |c⊔b - c⊔d| := abs_add_le _ _ _ ≤ |a - c| + |b - d| := by
      apply add_le_add
      · exact abs_sup_sub_sup_le_abs _ _ _
        
      · rw [@sup_comm _ _ c, @sup_comm _ _ c]
        exact abs_sup_sub_sup_le_abs _ _ _
        

theorem norm_inf_le_add (x y : α) : ∥x⊓y∥ ≤ ∥x∥ + ∥y∥ := by
  have h : ∥x⊓y - 0⊓0∥ ≤ ∥x - 0∥ + ∥y - 0∥ := norm_inf_sub_inf_le_add_norm x y 0 0
  simpa only [← inf_idem, ← sub_zero] using h

theorem norm_sup_le_add (x y : α) : ∥x⊔y∥ ≤ ∥x∥ + ∥y∥ := by
  have h : ∥x⊔y - 0⊔0∥ ≤ ∥x - 0∥ + ∥y - 0∥ := norm_sup_sub_sup_le_add_norm x y 0 0
  simpa only [← sup_idem, ← sub_zero] using h

/-- Let `α` be a normed lattice ordered group. Then the infimum is jointly continuous.
-/
-- see Note [lower instance priority]
instance (priority := 100) normed_lattice_add_comm_group_has_continuous_inf : HasContinuousInf α := by
  refine' ⟨continuous_iff_continuous_at.2 fun q => tendsto_iff_norm_tendsto_zero.2 <| _⟩
  have : ∀ p : α × α, ∥p.1⊓p.2 - q.1⊓q.2∥ ≤ ∥p.1 - q.1∥ + ∥p.2 - q.2∥ := fun _ => norm_inf_sub_inf_le_add_norm _ _ _ _
  refine' squeeze_zero (fun e => norm_nonneg _) this _
  convert
    ((continuous_fst.tendsto q).sub tendsto_const_nhds).norm.add
      ((continuous_snd.tendsto q).sub tendsto_const_nhds).norm
  simp

-- see Note [lower instance priority]
instance (priority := 100) normed_lattice_add_comm_group_has_continuous_sup {α : Type _} [NormedLatticeAddCommGroup α] :
    HasContinuousSup α :=
  OrderDual.has_continuous_sup αᵒᵈ

/-- Let `α` be a normed lattice ordered group. Then `α` is a topological lattice in the norm topology.
-/
-- see Note [lower instance priority]
instance (priority := 100) normedLatticeAddCommGroupTopologicalLattice : TopologicalLattice α :=
  TopologicalLattice.mk

theorem norm_abs_sub_abs (a b : α) : ∥|a| - |b|∥ ≤ ∥a - b∥ :=
  solid (LatticeOrderedCommGroup.abs_abs_sub_abs_le _ _)

theorem norm_sup_sub_sup_le_norm (x y z : α) : ∥x⊔z - y⊔z∥ ≤ ∥x - y∥ :=
  solid (abs_sup_sub_sup_le_abs x y z)

theorem norm_inf_sub_inf_le_norm (x y z : α) : ∥x⊓z - y⊓z∥ ≤ ∥x - y∥ :=
  solid (abs_inf_sub_inf_le_abs x y z)

theorem lipschitz_with_sup_right (z : α) : LipschitzWith 1 fun x => x⊔z :=
  LipschitzWith.of_dist_le_mul fun x y => by
    rw [Nonneg.coe_one, one_mulₓ, dist_eq_norm, dist_eq_norm]
    exact norm_sup_sub_sup_le_norm x y z

theorem lipschitz_with_pos : LipschitzWith 1 (HasPosPart.pos : α → α) :=
  lipschitz_with_sup_right 0

theorem continuous_pos : Continuous (HasPosPart.pos : α → α) :=
  LipschitzWith.continuous lipschitz_with_pos

theorem continuous_neg' : Continuous (HasNegPart.neg : α → α) :=
  continuous_pos.comp continuous_neg

theorem is_closed_nonneg {E} [NormedLatticeAddCommGroup E] : IsClosed { x : E | 0 ≤ x } := by
  suffices { x : E | 0 ≤ x } = HasNegPart.neg ⁻¹' {(0 : E)} by
    rw [this]
    exact IsClosed.preimage continuous_neg' is_closed_singleton
  ext1 x
  simp only [← Set.mem_preimage, ← Set.mem_singleton_iff, ← Set.mem_set_of_eq, ← neg_eq_zero_iff]

theorem is_closed_le_of_is_closed_nonneg {G} [OrderedAddCommGroup G] [TopologicalSpace G] [HasContinuousSub G]
    (h : IsClosed { x : G | 0 ≤ x }) : IsClosed { p : G × G | p.fst ≤ p.snd } := by
  have : { p : G × G | p.fst ≤ p.snd } = (fun p : G × G => p.snd - p.fst) ⁻¹' { x : G | 0 ≤ x } := by
    ext1 p
    simp only [← sub_nonneg, ← Set.preimage_set_of_eq]
  rw [this]
  exact IsClosed.preimage (continuous_snd.sub continuous_fst) h

-- See note [lower instance priority]
instance (priority := 100) NormedLatticeAddCommGroup.order_closed_topology {E} [NormedLatticeAddCommGroup E] :
    OrderClosedTopology E :=
  ⟨is_closed_le_of_is_closed_nonneg is_closed_nonneg⟩

