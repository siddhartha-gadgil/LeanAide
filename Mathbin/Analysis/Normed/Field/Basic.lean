/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl
-/
import Mathbin.Analysis.Normed.Group.InfiniteSum
import Mathbin.Topology.Algebra.Module.Basic
import Mathbin.Topology.Instances.Ennreal
import Mathbin.Topology.Instances.Rat

/-!
# Normed fields

In this file we define (semi)normed rings and fields. We also prove some theorems about these
definitions.
-/


variable {α : Type _} {β : Type _} {γ : Type _} {ι : Type _}

noncomputable section

open Filter Metric

open TopologicalSpace BigOperators Nnreal Ennreal uniformity Pointwise

/-- A non-unital seminormed ring is a not-necessarily-unital ring
endowed with a seminorm which satisfies the inequality `∥x y∥ ≤ ∥x∥ ∥y∥`. -/
class NonUnitalSemiNormedRing (α : Type _) extends HasNorm α, NonUnitalRing α, PseudoMetricSpace α where
  dist_eq : ∀ x y, dist x y = norm (x - y)
  norm_mul : ∀ a b, norm (a * b) ≤ norm a * norm b

/-- A seminormed ring is a ring endowed with a seminorm which satisfies the inequality
`∥x y∥ ≤ ∥x∥ ∥y∥`. -/
class SemiNormedRing (α : Type _) extends HasNorm α, Ringₓ α, PseudoMetricSpace α where
  dist_eq : ∀ x y, dist x y = norm (x - y)
  norm_mul : ∀ a b, norm (a * b) ≤ norm a * norm b

/-- A seminormed ring is a non-unital seminormed ring. -/
-- see Note [lower instance priority]
instance (priority := 100) SemiNormedRing.toNonUnitalSemiNormedRing [β : SemiNormedRing α] :
    NonUnitalSemiNormedRing α :=
  { β with }

/-- A non-unital normed ring is a not-necessarily-unital ring
endowed with a norm which satisfies the inequality `∥x y∥ ≤ ∥x∥ ∥y∥`. -/
class NonUnitalNormedRing (α : Type _) extends HasNorm α, NonUnitalRing α, MetricSpace α where
  dist_eq : ∀ x y, dist x y = norm (x - y)
  norm_mul : ∀ a b, norm (a * b) ≤ norm a * norm b

/-- A non-unital normed ring is a non-unital seminormed ring. -/
-- see Note [lower instance priority]
instance (priority := 100) NonUnitalNormedRing.toNonUnitalSemiNormedRing [β : NonUnitalNormedRing α] :
    NonUnitalSemiNormedRing α :=
  { β with }

/-- A normed ring is a ring endowed with a norm which satisfies the inequality `∥x y∥ ≤ ∥x∥ ∥y∥`. -/
class NormedRing (α : Type _) extends HasNorm α, Ringₓ α, MetricSpace α where
  dist_eq : ∀ x y, dist x y = norm (x - y)
  norm_mul : ∀ a b, norm (a * b) ≤ norm a * norm b

/-- A normed division ring is a division ring endowed with a seminorm which satisfies the equality
`∥x y∥ = ∥x∥ ∥y∥`. -/
class NormedDivisionRing (α : Type _) extends HasNorm α, DivisionRing α, MetricSpace α where
  dist_eq : ∀ x y, dist x y = norm (x - y)
  norm_mul' : ∀ a b, norm (a * b) = norm a * norm b

/-- A normed division ring is a normed ring. -/
-- see Note [lower instance priority]
instance (priority := 100) NormedDivisionRing.toNormedRing [β : NormedDivisionRing α] : NormedRing α :=
  { β with norm_mul := fun a b => (NormedDivisionRing.norm_mul' a b).le }

/-- A normed ring is a seminormed ring. -/
-- see Note [lower instance priority]
instance (priority := 100) NormedRing.toSemiNormedRing [β : NormedRing α] : SemiNormedRing α :=
  { β with }

/-- A normed ring is a non-unital normed ring. -/
-- see Note [lower instance priority]
instance (priority := 100) NormedRing.toNonUnitalNormedRing [β : NormedRing α] : NonUnitalNormedRing α :=
  { β with }

/-- A seminormed commutative ring is a commutative ring endowed with a seminorm which satisfies
the inequality `∥x y∥ ≤ ∥x∥ ∥y∥`. -/
class SemiNormedCommRing (α : Type _) extends SemiNormedRing α where
  mul_comm : ∀ x y : α, x * y = y * x

/-- A normed commutative ring is a commutative ring endowed with a norm which satisfies
the inequality `∥x y∥ ≤ ∥x∥ ∥y∥`. -/
class NormedCommRing (α : Type _) extends NormedRing α where
  mul_comm : ∀ x y : α, x * y = y * x

/-- A normed commutative ring is a seminormed commutative ring. -/
-- see Note [lower instance priority]
instance (priority := 100) NormedCommRing.toSemiNormedCommRing [β : NormedCommRing α] : SemiNormedCommRing α :=
  { β with }

instance : NormedCommRing PUnit :=
  { PUnit.normedGroup, PUnit.commRing with
    norm_mul := fun _ _ => by
      simp }

/-- A mixin class with the axiom `∥1∥ = 1`. Many `normed_ring`s and all `normed_field`s satisfy this
axiom. -/
class NormOneClass (α : Type _) [HasNorm α] [One α] : Prop where
  norm_one : ∥(1 : α)∥ = 1

export NormOneClass (norm_one)

attribute [simp] norm_one

@[simp]
theorem nnnorm_one [SemiNormedGroup α] [One α] [NormOneClass α] : ∥(1 : α)∥₊ = 1 :=
  Nnreal.eq norm_one

theorem NormOneClass.nontrivial (α : Type _) [SemiNormedGroup α] [One α] [NormOneClass α] : Nontrivial α :=
  nontrivial_of_ne 0 1 <|
    ne_of_apply_ne norm <| by
      simp

-- see Note [lower instance priority]
instance (priority := 100) SemiNormedCommRing.toCommRing [β : SemiNormedCommRing α] : CommRingₓ α :=
  { β with }

-- see Note [lower instance priority]
instance (priority := 100) NonUnitalNormedRing.toNormedGroup [β : NonUnitalNormedRing α] : NormedGroup α :=
  { β with }

-- see Note [lower instance priority]
instance (priority := 100) NonUnitalSemiNormedRing.toSemiNormedGroup [β : NonUnitalSemiNormedRing α] :
    SemiNormedGroup α :=
  { β with }

instance [SemiNormedGroup α] [One α] [NormOneClass α] : NormOneClass (ULift α) :=
  ⟨by
    simp [← ULift.norm_def]⟩

instance Prod.norm_one_class [SemiNormedGroup α] [One α] [NormOneClass α] [SemiNormedGroup β] [One β] [NormOneClass β] :
    NormOneClass (α × β) :=
  ⟨by
    simp [← Prod.norm_def]⟩

instance Pi.norm_one_class {ι : Type _} {α : ι → Type _} [Nonempty ι] [Fintype ι] [∀ i, SemiNormedGroup (α i)]
    [∀ i, One (α i)] [∀ i, NormOneClass (α i)] : NormOneClass (∀ i, α i) :=
  ⟨by
    simp [← Pi.norm_def, ← Finset.sup_const Finset.univ_nonempty]⟩

section NonUnitalSemiNormedRing

variable [NonUnitalSemiNormedRing α]

theorem norm_mul_le (a b : α) : ∥a * b∥ ≤ ∥a∥ * ∥b∥ :=
  NonUnitalSemiNormedRing.norm_mul _ _

theorem nnnorm_mul_le (a b : α) : ∥a * b∥₊ ≤ ∥a∥₊ * ∥b∥₊ := by
  simpa only [norm_to_nnreal, Real.to_nnreal_mul (norm_nonneg _)] using Real.to_nnreal_mono (norm_mul_le _ _)

theorem one_le_norm_one (β) [NormedRing β] [Nontrivial β] : 1 ≤ ∥(1 : β)∥ :=
  (le_mul_iff_one_le_left <| norm_pos_iff.mpr (one_ne_zero : (1 : β) ≠ 0)).mp
    (by
      simpa only [← mul_oneₓ] using norm_mul_le (1 : β) 1)

theorem one_le_nnnorm_one (β) [NormedRing β] [Nontrivial β] : 1 ≤ ∥(1 : β)∥₊ :=
  one_le_norm_one β

theorem Filter.Tendsto.zero_mul_is_bounded_under_le {f g : ι → α} {l : Filter ι} (hf : Tendsto f l (𝓝 0))
    (hg : IsBoundedUnder (· ≤ ·) l (norm ∘ g)) : Tendsto (fun x => f x * g x) l (𝓝 0) :=
  hf.op_zero_is_bounded_under_le hg (· * ·) norm_mul_le

theorem Filter.IsBoundedUnderLe.mul_tendsto_zero {f g : ι → α} {l : Filter ι} (hf : IsBoundedUnder (· ≤ ·) l (norm ∘ f))
    (hg : Tendsto g l (𝓝 0)) : Tendsto (fun x => f x * g x) l (𝓝 0) :=
  hg.op_zero_is_bounded_under_le hf (flip (· * ·)) fun x y => (norm_mul_le y x).trans_eq (mul_comm _ _)

/-- In a seminormed ring, the left-multiplication `add_monoid_hom` is bounded. -/
theorem mul_left_bound (x : α) : ∀ y : α, ∥AddMonoidHom.mulLeft x y∥ ≤ ∥x∥ * ∥y∥ :=
  norm_mul_le x

/-- In a seminormed ring, the right-multiplication `add_monoid_hom` is bounded. -/
theorem mul_right_bound (x : α) : ∀ y : α, ∥AddMonoidHom.mulRight x y∥ ≤ ∥x∥ * ∥y∥ := fun y => by
  rw [mul_comm]
  convert norm_mul_le y x

instance : NonUnitalSemiNormedRing (ULift α) :=
  { ULift.semiNormedGroup with norm_mul := fun x y => (norm_mul_le x.down y.down : _) }

/-- Non-unital seminormed ring structure on the product of two non-unital seminormed rings,
  using the sup norm. -/
instance Prod.nonUnitalSemiNormedRing [NonUnitalSemiNormedRing β] : NonUnitalSemiNormedRing (α × β) :=
  { Prod.semiNormedGroup with
    norm_mul := fun x y =>
      calc
        ∥x * y∥ = ∥(x.1 * y.1, x.2 * y.2)∥ := rfl
        _ = max ∥x.1 * y.1∥ ∥x.2 * y.2∥ := rfl
        _ ≤ max (∥x.1∥ * ∥y.1∥) (∥x.2∥ * ∥y.2∥) := max_le_max (norm_mul_le x.1 y.1) (norm_mul_le x.2 y.2)
        _ = max (∥x.1∥ * ∥y.1∥) (∥y.2∥ * ∥x.2∥) := by
          simp [← mul_comm]
        _ ≤ max ∥x.1∥ ∥x.2∥ * max ∥y.2∥ ∥y.1∥ := by
          apply max_mul_mul_le_max_mul_max <;> simp [← norm_nonneg]
        _ = max ∥x.1∥ ∥x.2∥ * max ∥y.1∥ ∥y.2∥ := by
          simp [← max_commₓ]
        _ = ∥x∥ * ∥y∥ := rfl
         }

/-- Non-unital seminormed ring structure on the product of finitely many non-unital seminormed
rings, using the sup norm. -/
instance Pi.nonUnitalSemiNormedRing {π : ι → Type _} [Fintype ι] [∀ i, NonUnitalSemiNormedRing (π i)] :
    NonUnitalSemiNormedRing (∀ i, π i) :=
  { Pi.semiNormedGroup with
    norm_mul := fun x y =>
      Nnreal.coe_mono <|
        calc
          (Finset.univ.sup fun i => ∥x i * y i∥₊) ≤ Finset.univ.sup ((fun i => ∥x i∥₊) * fun i => ∥y i∥₊) :=
            Finset.sup_mono_fun fun b hb => norm_mul_le _ _
          _ ≤ (Finset.univ.sup fun i => ∥x i∥₊) * Finset.univ.sup fun i => ∥y i∥₊ :=
            Finset.sup_mul_le_mul_sup_of_nonneg _ (fun i _ => zero_le _) fun i _ => zero_le _
           }

end NonUnitalSemiNormedRing

section SemiNormedRing

variable [SemiNormedRing α]

/-- A subalgebra of a seminormed ring is also a seminormed ring, with the restriction of the norm.

See note [implicit instance arguments]. -/
instance Subalgebra.semiNormedRing {𝕜 : Type _} {_ : CommRingₓ 𝕜} {E : Type _} [SemiNormedRing E] {_ : Algebra 𝕜 E}
    (s : Subalgebra 𝕜 E) : SemiNormedRing s :=
  { s.toSubmodule.SemiNormedGroup with norm_mul := fun a b => norm_mul_le a.1 b.1 }

/-- A subalgebra of a normed ring is also a normed ring, with the restriction of the norm.

See note [implicit instance arguments]. -/
instance Subalgebra.normedRing {𝕜 : Type _} {_ : CommRingₓ 𝕜} {E : Type _} [NormedRing E] {_ : Algebra 𝕜 E}
    (s : Subalgebra 𝕜 E) : NormedRing s :=
  { s.SemiNormedRing with }

theorem Nat.norm_cast_le : ∀ n : ℕ, ∥(n : α)∥ ≤ n * ∥(1 : α)∥
  | 0 => by
    simp
  | n + 1 => by
    rw [n.cast_succ, n.cast_succ, add_mulₓ, one_mulₓ]
    exact norm_add_le_of_le (Nat.norm_cast_le n) le_rfl

theorem List.norm_prod_le' : ∀ {l : List α}, l ≠ [] → ∥l.Prod∥ ≤ (l.map norm).Prod
  | [], h => (h rfl).elim
  | [a], _ => by
    simp
  | a :: b :: l, _ => by
    rw [List.map_cons, List.prod_cons, @List.prod_cons _ _ _ ∥a∥]
    refine' le_transₓ (norm_mul_le _ _) (mul_le_mul_of_nonneg_left _ (norm_nonneg _))
    exact List.norm_prod_le' (List.cons_ne_nil b l)

theorem List.nnnorm_prod_le' {l : List α} (hl : l ≠ []) : ∥l.Prod∥₊ ≤ (l.map nnnorm).Prod :=
  (List.norm_prod_le' hl).trans_eq <| by
    simp [← Nnreal.coe_list_prod, ← List.map_mapₓ]

theorem List.norm_prod_le [NormOneClass α] : ∀ l : List α, ∥l.Prod∥ ≤ (l.map norm).Prod
  | [] => by
    simp
  | a :: l => List.norm_prod_le' (List.cons_ne_nil a l)

theorem List.nnnorm_prod_le [NormOneClass α] (l : List α) : ∥l.Prod∥₊ ≤ (l.map nnnorm).Prod :=
  l.norm_prod_le.trans_eq <| by
    simp [← Nnreal.coe_list_prod, ← List.map_mapₓ]

theorem Finset.norm_prod_le' {α : Type _} [NormedCommRing α] (s : Finset ι) (hs : s.Nonempty) (f : ι → α) :
    ∥∏ i in s, f i∥ ≤ ∏ i in s, ∥f i∥ := by
  rcases s with ⟨⟨l⟩, hl⟩
  have : l.map f ≠ [] := by
    simpa using hs
  simpa using List.norm_prod_le' this

theorem Finset.nnnorm_prod_le' {α : Type _} [NormedCommRing α] (s : Finset ι) (hs : s.Nonempty) (f : ι → α) :
    ∥∏ i in s, f i∥₊ ≤ ∏ i in s, ∥f i∥₊ :=
  (s.norm_prod_le' hs f).trans_eq <| by
    simp [← Nnreal.coe_prod]

theorem Finset.norm_prod_le {α : Type _} [NormedCommRing α] [NormOneClass α] (s : Finset ι) (f : ι → α) :
    ∥∏ i in s, f i∥ ≤ ∏ i in s, ∥f i∥ := by
  rcases s with ⟨⟨l⟩, hl⟩
  simpa using (l.map f).norm_prod_le

theorem Finset.nnnorm_prod_le {α : Type _} [NormedCommRing α] [NormOneClass α] (s : Finset ι) (f : ι → α) :
    ∥∏ i in s, f i∥₊ ≤ ∏ i in s, ∥f i∥₊ :=
  (s.norm_prod_le f).trans_eq <| by
    simp [← Nnreal.coe_prod]

/-- If `α` is a seminormed ring, then `∥a ^ n∥₊ ≤ ∥a∥₊ ^ n` for `n > 0`.
See also `nnnorm_pow_le`. -/
theorem nnnorm_pow_le' (a : α) : ∀ {n : ℕ}, 0 < n → ∥a ^ n∥₊ ≤ ∥a∥₊ ^ n
  | 1, h => by
    simp only [← pow_oneₓ]
  | n + 2, h => by
    simpa only [← pow_succₓ _ (n + 1)] using
      le_transₓ (nnnorm_mul_le _ _) (mul_le_mul_left' (nnnorm_pow_le' n.succ_pos) _)

/-- If `α` is a seminormed ring with `∥1∥₊ = 1`, then `∥a ^ n∥₊ ≤ ∥a∥₊ ^ n`.
See also `nnnorm_pow_le'`.-/
theorem nnnorm_pow_le [NormOneClass α] (a : α) (n : ℕ) : ∥a ^ n∥₊ ≤ ∥a∥₊ ^ n :=
  Nat.recOn n
    (by
      simp only [← pow_zeroₓ, ← nnnorm_one])
    fun k hk => nnnorm_pow_le' a k.succ_pos

/-- If `α` is a seminormed ring, then `∥a ^ n∥ ≤ ∥a∥ ^ n` for `n > 0`. See also `norm_pow_le`. -/
theorem norm_pow_le' (a : α) {n : ℕ} (h : 0 < n) : ∥a ^ n∥ ≤ ∥a∥ ^ n := by
  simpa only [← Nnreal.coe_pow, ← coe_nnnorm] using Nnreal.coe_mono (nnnorm_pow_le' a h)

/-- If `α` is a seminormed ring with `∥1∥ = 1`, then `∥a ^ n∥ ≤ ∥a∥ ^ n`. See also `norm_pow_le'`.-/
theorem norm_pow_le [NormOneClass α] (a : α) (n : ℕ) : ∥a ^ n∥ ≤ ∥a∥ ^ n :=
  Nat.recOn n
    (by
      simp only [← pow_zeroₓ, ← norm_one])
    fun n hn => norm_pow_le' a n.succ_pos

theorem eventually_norm_pow_le (a : α) : ∀ᶠ n : ℕ in at_top, ∥a ^ n∥ ≤ ∥a∥ ^ n :=
  eventually_at_top.mpr ⟨1, fun b h => norm_pow_le' a (Nat.succ_le_iff.mp h)⟩

instance : SemiNormedRing (ULift α) :=
  { ULift.nonUnitalSemiNormedRing, ULift.semiNormedGroup with }

/-- Seminormed ring structure on the product of two seminormed rings,
  using the sup norm. -/
instance Prod.semiNormedRing [SemiNormedRing β] : SemiNormedRing (α × β) :=
  { Prod.nonUnitalSemiNormedRing, Prod.semiNormedGroup with }

/-- Seminormed ring structure on the product of finitely many seminormed rings,
  using the sup norm. -/
instance Pi.semiNormedRing {π : ι → Type _} [Fintype ι] [∀ i, SemiNormedRing (π i)] : SemiNormedRing (∀ i, π i) :=
  { Pi.nonUnitalSemiNormedRing, Pi.semiNormedGroup with }

end SemiNormedRing

section NonUnitalNormedRing

variable [NonUnitalNormedRing α]

instance : NonUnitalNormedRing (ULift α) :=
  { ULift.nonUnitalSemiNormedRing, ULift.semiNormedGroup with }

/-- Non-unital normed ring structure on the product of two non-unital normed rings,
using the sup norm. -/
instance Prod.nonUnitalNormedRing [NonUnitalNormedRing β] : NonUnitalNormedRing (α × β) :=
  { Prod.semiNormedGroup with norm_mul := norm_mul_le }

/-- Normed ring structure on the product of finitely many non-unital normed rings, using the sup
norm. -/
instance Pi.nonUnitalNormedRing {π : ι → Type _} [Fintype ι] [∀ i, NonUnitalNormedRing (π i)] :
    NonUnitalNormedRing (∀ i, π i) :=
  { Pi.normedGroup with norm_mul := norm_mul_le }

end NonUnitalNormedRing

section NormedRing

variable [NormedRing α]

theorem Units.norm_pos [Nontrivial α] (x : αˣ) : 0 < ∥(x : α)∥ :=
  norm_pos_iff.mpr (Units.ne_zero x)

theorem Units.nnnorm_pos [Nontrivial α] (x : αˣ) : 0 < ∥(x : α)∥₊ :=
  x.norm_pos

instance : NormedRing (ULift α) :=
  { ULift.semiNormedRing, ULift.normedGroup with }

/-- Normed ring structure on the product of two normed rings, using the sup norm. -/
instance Prod.normedRing [NormedRing β] : NormedRing (α × β) :=
  { Prod.normedGroup with norm_mul := norm_mul_le }

/-- Normed ring structure on the product of finitely many normed rings, using the sup norm. -/
instance Pi.normedRing {π : ι → Type _} [Fintype ι] [∀ i, NormedRing (π i)] : NormedRing (∀ i, π i) :=
  { Pi.normedGroup with norm_mul := norm_mul_le }

end NormedRing

-- see Note [lower instance priority]
instance (priority := 100) semi_normed_ring_top_monoid [NonUnitalSemiNormedRing α] : HasContinuousMul α :=
  ⟨continuous_iff_continuous_at.2 fun x =>
      tendsto_iff_norm_tendsto_zero.2 <| by
        have : ∀ e : α × α, ∥e.1 * e.2 - x.1 * x.2∥ ≤ ∥e.1∥ * ∥e.2 - x.2∥ + ∥e.1 - x.1∥ * ∥x.2∥ := by
          intro e
          calc ∥e.1 * e.2 - x.1 * x.2∥ ≤ ∥e.1 * (e.2 - x.2) + (e.1 - x.1) * x.2∥ := by
              rw [mul_sub, sub_mul, sub_add_sub_cancel]_ ≤ ∥e.1∥ * ∥e.2 - x.2∥ + ∥e.1 - x.1∥ * ∥x.2∥ :=
              norm_add_le_of_le (norm_mul_le _ _) (norm_mul_le _ _)
        refine' squeeze_zero (fun e => norm_nonneg _) this _
        convert
          ((continuous_fst.tendsto x).norm.mul ((continuous_snd.tendsto x).sub tendsto_const_nhds).norm).add
            (((continuous_fst.tendsto x).sub tendsto_const_nhds).norm.mul _)
        show tendsto _ _ _
        exact tendsto_const_nhds
        simp ⟩

/-- A seminormed ring is a topological ring. -/
-- see Note [lower instance priority]
instance (priority := 100) semi_normed_top_ring [NonUnitalSemiNormedRing α] : TopologicalRing α where

section NormedDivisionRing

variable [NormedDivisionRing α]

@[simp]
theorem norm_mul (a b : α) : ∥a * b∥ = ∥a∥ * ∥b∥ :=
  NormedDivisionRing.norm_mul' a b

instance (priority := 900) NormedDivisionRing.to_norm_one_class : NormOneClass α :=
  ⟨mul_left_cancel₀ (mt norm_eq_zero.1 (@one_ne_zero α _ _)) <| by
      rw [← norm_mul, mul_oneₓ, mul_oneₓ]⟩

@[simp]
theorem nnnorm_mul (a b : α) : ∥a * b∥₊ = ∥a∥₊ * ∥b∥₊ :=
  Nnreal.eq <| norm_mul a b

/-- `norm` as a `monoid_with_zero_hom`. -/
@[simps]
def normHom : α →*₀ ℝ :=
  ⟨norm, norm_zero, norm_one, norm_mul⟩

/-- `nnnorm` as a `monoid_with_zero_hom`. -/
@[simps]
def nnnormHom : α →*₀ ℝ≥0 :=
  ⟨nnnorm, nnnorm_zero, nnnorm_one, nnnorm_mul⟩

@[simp]
theorem norm_pow (a : α) : ∀ n : ℕ, ∥a ^ n∥ = ∥a∥ ^ n :=
  (normHom.toMonoidHom : α →* ℝ).map_pow a

@[simp]
theorem nnnorm_pow (a : α) (n : ℕ) : ∥a ^ n∥₊ = ∥a∥₊ ^ n :=
  (nnnormHom.toMonoidHom : α →* ℝ≥0 ).map_pow a n

protected theorem List.norm_prod (l : List α) : ∥l.Prod∥ = (l.map norm).Prod :=
  (normHom.toMonoidHom : α →* ℝ).map_list_prod _

protected theorem List.nnnorm_prod (l : List α) : ∥l.Prod∥₊ = (l.map nnnorm).Prod :=
  (nnnormHom.toMonoidHom : α →* ℝ≥0 ).map_list_prod _

@[simp]
theorem norm_div (a b : α) : ∥a / b∥ = ∥a∥ / ∥b∥ :=
  (normHom : α →*₀ ℝ).map_div a b

@[simp]
theorem nnnorm_div (a b : α) : ∥a / b∥₊ = ∥a∥₊ / ∥b∥₊ :=
  (nnnormHom : α →*₀ ℝ≥0 ).map_div a b

@[simp]
theorem norm_inv (a : α) : ∥a⁻¹∥ = ∥a∥⁻¹ :=
  (normHom : α →*₀ ℝ).map_inv a

@[simp]
theorem nnnorm_inv (a : α) : ∥a⁻¹∥₊ = ∥a∥₊⁻¹ :=
  Nnreal.eq <| by
    simp

@[simp]
theorem norm_zpow : ∀ (a : α) (n : ℤ), ∥a ^ n∥ = ∥a∥ ^ n :=
  (normHom : α →*₀ ℝ).map_zpow

@[simp]
theorem nnnorm_zpow : ∀ (a : α) (n : ℤ), ∥a ^ n∥₊ = ∥a∥₊ ^ n :=
  (nnnormHom : α →*₀ ℝ≥0 ).map_zpow

/-- Multiplication on the left by a nonzero element of a normed division ring tends to infinity at
infinity. TODO: use `bornology.cobounded` instead of `filter.comap has_norm.norm filter.at_top`. -/
theorem Filter.tendsto_mul_left_cobounded {a : α} (ha : a ≠ 0) :
    Tendsto ((· * ·) a) (comap norm atTop) (comap norm atTop) := by
  simpa only [← tendsto_comap_iff, ← (· ∘ ·), ← norm_mul] using
    tendsto_const_nhds.mul_at_top (norm_pos_iff.2 ha) tendsto_comap

/-- Multiplication on the right by a nonzero element of a normed division ring tends to infinity at
infinity. TODO: use `bornology.cobounded` instead of `filter.comap has_norm.norm filter.at_top`. -/
theorem Filter.tendsto_mul_right_cobounded {a : α} (ha : a ≠ 0) :
    Tendsto (fun x => x * a) (comap norm atTop) (comap norm atTop) := by
  simpa only [← tendsto_comap_iff, ← (· ∘ ·), ← norm_mul] using
    tendsto_comap.at_top_mul (norm_pos_iff.2 ha) tendsto_const_nhds

-- see Note [lower instance priority]
instance (priority := 100) NormedDivisionRing.to_has_continuous_inv₀ : HasContinuousInv₀ α := by
  refine' ⟨fun r r0 => tendsto_iff_norm_tendsto_zero.2 _⟩
  have r0' : 0 < ∥r∥ := norm_pos_iff.2 r0
  rcases exists_between r0' with ⟨ε, ε0, εr⟩
  have : ∀ᶠ e in 𝓝 r, ∥e⁻¹ - r⁻¹∥ ≤ ∥r - e∥ / ∥r∥ / ε := by
    filter_upwards [(is_open_lt continuous_const continuous_norm).eventually_mem εr] with e he
    have e0 : e ≠ 0 := norm_pos_iff.1 (ε0.trans he)
    calc ∥e⁻¹ - r⁻¹∥ = ∥r∥⁻¹ * ∥r - e∥ * ∥e∥⁻¹ := by
        rw [← norm_inv, ← norm_inv, ← norm_mul, ← norm_mul, mul_sub, sub_mul, mul_assoc _ e, inv_mul_cancel r0,
          mul_inv_cancel e0, one_mulₓ, mul_oneₓ]_ = ∥r - e∥ / ∥r∥ / ∥e∥ :=
        by
        field_simp [← mul_comm]_ ≤ ∥r - e∥ / ∥r∥ / ε :=
        div_le_div_of_le_left (div_nonneg (norm_nonneg _) (norm_nonneg _)) ε0 he.le
  refine' squeeze_zero' (eventually_of_forall fun _ => norm_nonneg _) this _
  refine' (continuous_const.sub continuous_id).norm.div_const.div_const.tendsto' _ _ _
  simp

end NormedDivisionRing

/-- A normed field is a field with a norm satisfying ∥x y∥ = ∥x∥ ∥y∥. -/
class NormedField (α : Type _) extends HasNorm α, Field α, MetricSpace α where
  dist_eq : ∀ x y, dist x y = norm (x - y)
  norm_mul' : ∀ a b, norm (a * b) = norm a * norm b

/-- A nondiscrete normed field is a normed field in which there is an element of norm different from
`0` and `1`. This makes it possible to bring any element arbitrarily close to `0` by multiplication
by the powers of any element, and thus to relate algebra and topology. -/
class NondiscreteNormedField (α : Type _) extends NormedField α where
  non_trivial : ∃ x : α, 1 < ∥x∥

section NormedField

variable [NormedField α]

-- see Note [lower instance priority]
instance (priority := 100) NormedField.toNormedDivisionRing : NormedDivisionRing α :=
  { ‹NormedField α› with }

-- see Note [lower instance priority]
instance (priority := 100) NormedField.toNormedCommRing : NormedCommRing α :=
  { ‹NormedField α› with norm_mul := fun a b => (norm_mul a b).le }

@[simp]
theorem norm_prod (s : Finset β) (f : β → α) : ∥∏ b in s, f b∥ = ∏ b in s, ∥f b∥ :=
  (normHom.toMonoidHom : α →* ℝ).map_prod f s

@[simp]
theorem nnnorm_prod (s : Finset β) (f : β → α) : ∥∏ b in s, f b∥₊ = ∏ b in s, ∥f b∥₊ :=
  (nnnormHom.toMonoidHom : α →* ℝ≥0 ).map_prod f s

end NormedField

namespace NormedField

variable (α) [NondiscreteNormedField α]

theorem exists_one_lt_norm : ∃ x : α, 1 < ∥x∥ :=
  ‹NondiscreteNormedField α›.non_trivial

theorem exists_lt_norm (r : ℝ) : ∃ x : α, r < ∥x∥ :=
  let ⟨w, hw⟩ := exists_one_lt_norm α
  let ⟨n, hn⟩ := pow_unbounded_of_one_lt r hw
  ⟨w ^ n, by
    rwa [norm_pow]⟩

theorem exists_norm_lt {r : ℝ} (hr : 0 < r) : ∃ x : α, 0 < ∥x∥ ∧ ∥x∥ < r :=
  let ⟨w, hw⟩ := exists_lt_norm α r⁻¹
  ⟨w⁻¹, by
    rwa [← Set.mem_Ioo, norm_inv, ← Set.mem_inv, Set.inv_Ioo_0_left hr]⟩

theorem exists_norm_lt_one : ∃ x : α, 0 < ∥x∥ ∧ ∥x∥ < 1 :=
  exists_norm_lt α one_pos

variable {α}

@[instance]
theorem punctured_nhds_ne_bot (x : α) : NeBot (𝓝[≠] x) := by
  rw [← mem_closure_iff_nhds_within_ne_bot, Metric.mem_closure_iff]
  rintro ε ε0
  rcases exists_norm_lt α ε0 with ⟨b, hb0, hbε⟩
  refine' ⟨x + b, mt (set.mem_singleton_iff.trans add_right_eq_selfₓ).1 <| norm_pos_iff.1 hb0, _⟩
  rwa [dist_comm, dist_eq_norm, add_sub_cancel']

@[instance]
theorem nhds_within_is_unit_ne_bot : NeBot (𝓝[{ x : α | IsUnit x }] 0) := by
  simpa only [← is_unit_iff_ne_zero] using punctured_nhds_ne_bot (0 : α)

end NormedField

instance : NormedField ℝ :=
  { Real.normedGroup with norm_mul' := abs_mul }

instance :
    NondiscreteNormedField ℝ where non_trivial :=
    ⟨2, by
      unfold norm
      rw [abs_of_nonneg] <;> norm_num⟩

namespace Real

theorem norm_of_nonneg {x : ℝ} (hx : 0 ≤ x) : ∥x∥ = x :=
  abs_of_nonneg hx

theorem norm_of_nonpos {x : ℝ} (hx : x ≤ 0) : ∥x∥ = -x :=
  abs_of_nonpos hx

@[simp]
theorem norm_coe_nat (n : ℕ) : ∥(n : ℝ)∥ = n :=
  abs_of_nonneg n.cast_nonneg

@[simp]
theorem nnnorm_coe_nat (n : ℕ) : ∥(n : ℝ)∥₊ = n :=
  Nnreal.eq <| by
    simp

@[simp]
theorem norm_two : ∥(2 : ℝ)∥ = 2 :=
  abs_of_pos (@zero_lt_two ℝ _ _)

@[simp]
theorem nnnorm_two : ∥(2 : ℝ)∥₊ = 2 :=
  Nnreal.eq <| by
    simp

theorem nnnorm_of_nonneg {x : ℝ} (hx : 0 ≤ x) : ∥x∥₊ = ⟨x, hx⟩ :=
  Nnreal.eq <| norm_of_nonneg hx

theorem ennnorm_eq_of_real {x : ℝ} (hx : 0 ≤ x) : (∥x∥₊ : ℝ≥0∞) = Ennreal.ofReal x := by
  rw [← of_real_norm_eq_coe_nnnorm, norm_of_nonneg hx]

theorem of_real_le_ennnorm (x : ℝ) : Ennreal.ofReal x ≤ ∥x∥₊ := by
  by_cases' hx : 0 ≤ x
  · rw [Real.ennnorm_eq_of_real hx]
    rfl'
    
  · rw [Ennreal.of_real_eq_zero.2 (le_of_ltₓ (not_leₓ.1 hx))]
    exact bot_le
    

/-- If `E` is a nontrivial topological module over `ℝ`, then `E` has no isolated points.
This is a particular case of `module.punctured_nhds_ne_bot`. -/
instance punctured_nhds_module_ne_bot {E : Type _} [AddCommGroupₓ E] [TopologicalSpace E] [HasContinuousAdd E]
    [Nontrivial E] [Module ℝ E] [HasContinuousSmul ℝ E] (x : E) : NeBot (𝓝[≠] x) :=
  Module.punctured_nhds_ne_bot ℝ E x

end Real

namespace Nnreal

open Nnreal

@[simp]
theorem norm_eq (x : ℝ≥0 ) : ∥(x : ℝ)∥ = x := by
  rw [Real.norm_eq_abs, x.abs_eq]

@[simp]
theorem nnnorm_eq (x : ℝ≥0 ) : ∥(x : ℝ)∥₊ = x :=
  Nnreal.eq <| Real.norm_of_nonneg x.2

end Nnreal

@[simp]
theorem norm_norm [SemiNormedGroup α] (x : α) : ∥∥x∥∥ = ∥x∥ :=
  Real.norm_of_nonneg (norm_nonneg _)

@[simp]
theorem nnnorm_norm [SemiNormedGroup α] (a : α) : ∥∥a∥∥₊ = ∥a∥₊ := by
  simpa [← Real.nnnorm_of_nonneg (norm_nonneg a)]

/-- A restatement of `metric_space.tendsto_at_top` in terms of the norm. -/
theorem NormedGroup.tendsto_at_top [Nonempty α] [SemilatticeSup α] {β : Type _} [SemiNormedGroup β] {f : α → β}
    {b : β} : Tendsto f atTop (𝓝 b) ↔ ∀ ε, 0 < ε → ∃ N, ∀ n, N ≤ n → ∥f n - b∥ < ε :=
  (at_top_basis.tendsto_iff Metric.nhds_basis_ball).trans
    (by
      simp [← dist_eq_norm])

/-- A variant of `normed_group.tendsto_at_top` that
uses `∃ N, ∀ n > N, ...` rather than `∃ N, ∀ n ≥ N, ...`
-/
theorem NormedGroup.tendsto_at_top' [Nonempty α] [SemilatticeSup α] [NoMaxOrder α] {β : Type _} [SemiNormedGroup β]
    {f : α → β} {b : β} : Tendsto f atTop (𝓝 b) ↔ ∀ ε, 0 < ε → ∃ N, ∀ n, N < n → ∥f n - b∥ < ε :=
  (at_top_basis_Ioi.tendsto_iff Metric.nhds_basis_ball).trans
    (by
      simp [← dist_eq_norm])

instance : NormedCommRing ℤ where
  norm := fun n => ∥(n : ℝ)∥
  norm_mul := fun m n =>
    le_of_eqₓ <| by
      simp only [← norm, ← Int.cast_mul, ← abs_mul]
  dist_eq := fun m n => by
    simp only [← Int.dist_eq, ← norm, ← Int.cast_sub]
  mul_comm := mul_comm

@[norm_cast]
theorem Int.norm_cast_real (m : ℤ) : ∥(m : ℝ)∥ = ∥m∥ :=
  rfl

theorem Int.norm_eq_abs (n : ℤ) : ∥n∥ = abs n :=
  rfl

theorem Nnreal.coe_nat_abs (n : ℤ) : (n.natAbs : ℝ≥0 ) = ∥n∥₊ :=
  Nnreal.eq <|
    calc
      ((n.natAbs : ℝ≥0 ) : ℝ) = (n.natAbs : ℤ) := by
        simp only [← Int.cast_coe_nat, ← Nnreal.coe_nat_cast]
      _ = abs n := by
        simp only [Int.abs_eq_nat_abs, ← Int.cast_abs]
      _ = ∥n∥ := rfl
      

theorem Int.abs_le_floor_nnreal_iff (z : ℤ) (c : ℝ≥0 ) : abs z ≤ ⌊c⌋₊ ↔ ∥z∥₊ ≤ c := by
  rw [Int.abs_eq_nat_abs, Int.coe_nat_le, Nat.le_floor_iff (zero_le c)]
  congr
  exact Nnreal.coe_nat_abs z

instance : NormOneClass ℤ :=
  ⟨by
    simp [Int.norm_cast_real]⟩

instance : NormedField ℚ where
  norm := fun r => ∥(r : ℝ)∥
  norm_mul' := fun r₁ r₂ => by
    simp only [← norm, ← Rat.cast_mul, ← abs_mul]
  dist_eq := fun r₁ r₂ => by
    simp only [← Rat.dist_eq, ← norm, ← Rat.cast_sub]

instance :
    NondiscreteNormedField ℚ where non_trivial :=
    ⟨2, by
      unfold norm
      rw [abs_of_nonneg] <;> norm_num⟩

@[norm_cast, simp]
theorem Rat.norm_cast_real (r : ℚ) : ∥(r : ℝ)∥ = ∥r∥ :=
  rfl

@[norm_cast, simp]
theorem Int.norm_cast_rat (m : ℤ) : ∥(m : ℚ)∥ = ∥m∥ := by
  rw [← Rat.norm_cast_real, ← Int.norm_cast_real] <;> congr 1 <;> norm_cast

-- Now that we've installed the norm on `ℤ`,
-- we can state some lemmas about `nsmul` and `zsmul`.
section

variable [SemiNormedGroup α]

theorem norm_nsmul_le (n : ℕ) (a : α) : ∥n • a∥ ≤ n * ∥a∥ := by
  induction' n with n ih
  · simp only [← norm_zero, ← Nat.cast_zeroₓ, ← zero_mul, ← zero_smul]
    
  simp only [← Nat.succ_eq_add_one, ← add_smul, ← add_mulₓ, ← one_mulₓ, ← Nat.cast_addₓ, ← Nat.cast_oneₓ, ← one_nsmul]
  exact norm_add_le_of_le ih le_rfl

theorem norm_zsmul_le (n : ℤ) (a : α) : ∥n • a∥ ≤ ∥n∥ * ∥a∥ := by
  induction' n with n n
  · simp only [← Int.of_nat_eq_coe, ← coe_nat_zsmul]
    convert norm_nsmul_le n a
    exact Nat.abs_cast n
    
  · simp only [← Int.neg_succ_of_nat_coe, ← neg_smul, ← norm_neg, ← coe_nat_zsmul]
    convert norm_nsmul_le n.succ a
    exact Nat.abs_cast n.succ
    

theorem nnnorm_nsmul_le (n : ℕ) (a : α) : ∥n • a∥₊ ≤ n * ∥a∥₊ := by
  simpa only [Nnreal.coe_le_coe, ← Nnreal.coe_mul, ← Nnreal.coe_nat_cast] using norm_nsmul_le n a

theorem nnnorm_zsmul_le (n : ℤ) (a : α) : ∥n • a∥₊ ≤ ∥n∥₊ * ∥a∥₊ := by
  simpa only [Nnreal.coe_le_coe, ← Nnreal.coe_mul] using norm_zsmul_le n a

end

section CauchyProduct

/-! ## Multiplying two infinite sums in a normed ring

In this section, we prove various results about `(∑' x : ι, f x) * (∑' y : ι', g y)` in a normed
ring. There are similar results proven in `topology/algebra/infinite_sum` (e.g `tsum_mul_tsum`),
but in a normed ring we get summability results which aren't true in general.

We first establish results about arbitrary index types, `β` and `γ`, and then we specialize to
`β = γ = ℕ` to prove the Cauchy product formula
(see `tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm`).

### Arbitrary index types
-/


variable {ι' : Type _} [NormedRing α]

open Finset

open Classical

theorem Summable.mul_of_nonneg {f : ι → ℝ} {g : ι' → ℝ} (hf : Summable f) (hg : Summable g) (hf' : 0 ≤ f)
    (hg' : 0 ≤ g) : Summable fun x : ι × ι' => f x.1 * g x.2 :=
  let ⟨s, hf⟩ := hf
  let ⟨t, hg⟩ := hg
  suffices this : ∀ u : Finset (ι × ι'), (∑ x in u, f x.1 * g x.2) ≤ s * t from
    summable_of_sum_le (fun x => mul_nonneg (hf' _) (hg' _)) this
  fun u =>
  calc
    (∑ x in u, f x.1 * g x.2) ≤ ∑ x in (u.Image Prod.fst).product (u.Image Prod.snd), f x.1 * g x.2 :=
      sum_mono_set_of_nonneg (fun x => mul_nonneg (hf' _) (hg' _)) subset_product
    _ = ∑ x in u.Image Prod.fst, ∑ y in u.Image Prod.snd, f x * g y := sum_product
    _ = ∑ x in u.Image Prod.fst, f x * ∑ y in u.Image Prod.snd, g y := sum_congr rfl fun x _ => mul_sum.symm
    _ ≤ ∑ x in u.Image Prod.fst, f x * t :=
      sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (sum_le_has_sum _ (fun _ _ => hg' _) hg) (hf' _)
    _ = (∑ x in u.Image Prod.fst, f x) * t := sum_mul.symm
    _ ≤ s * t := mul_le_mul_of_nonneg_right (sum_le_has_sum _ (fun _ _ => hf' _) hf) (hg.Nonneg fun _ => hg' _)
    

theorem Summable.mul_norm {f : ι → α} {g : ι' → α} (hf : Summable fun x => ∥f x∥) (hg : Summable fun x => ∥g x∥) :
    Summable fun x : ι × ι' => ∥f x.1 * g x.2∥ :=
  summable_of_nonneg_of_le (fun x => norm_nonneg (f x.1 * g x.2)) (fun x => norm_mul_le (f x.1) (g x.2))
    (hf.mul_of_nonneg hg (fun x => norm_nonneg <| f x) fun x => norm_nonneg <| g x : _)

theorem summable_mul_of_summable_norm [CompleteSpace α] {f : ι → α} {g : ι' → α} (hf : Summable fun x => ∥f x∥)
    (hg : Summable fun x => ∥g x∥) : Summable fun x : ι × ι' => f x.1 * g x.2 :=
  summable_of_summable_norm (hf.mul_norm hg)

/-- Product of two infinites sums indexed by arbitrary types.
    See also `tsum_mul_tsum` if `f` and `g` are *not* absolutely summable. -/
theorem tsum_mul_tsum_of_summable_norm [CompleteSpace α] {f : ι → α} {g : ι' → α} (hf : Summable fun x => ∥f x∥)
    (hg : Summable fun x => ∥g x∥) : ((∑' x, f x) * ∑' y, g y) = ∑' z : ι × ι', f z.1 * g z.2 :=
  tsum_mul_tsum (summable_of_summable_norm hf) (summable_of_summable_norm hg) (summable_mul_of_summable_norm hf hg)

/-! ### `ℕ`-indexed families (Cauchy product)

We prove two versions of the Cauchy product formula. The first one is
`tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm`, where the `n`-th term is a sum over
`finset.range (n+1)` involving `nat` substraction.
In order to avoid `nat` substraction, we also provide
`tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm`,
where the `n`-th term is a sum over all pairs `(k, l)` such that `k+l=n`, which corresponds to the
`finset` `finset.nat.antidiagonal n`. -/


section Nat

open Finset.Nat

theorem summable_norm_sum_mul_antidiagonal_of_summable_norm {f g : ℕ → α} (hf : Summable fun x => ∥f x∥)
    (hg : Summable fun x => ∥g x∥) : Summable fun n => ∥∑ kl in antidiagonal n, f kl.1 * g kl.2∥ := by
  have :=
    summable_sum_mul_antidiagonal_of_summable_mul
      (Summable.mul_of_nonneg hf hg (fun _ => norm_nonneg _) fun _ => norm_nonneg _)
  refine' summable_of_nonneg_of_le (fun _ => norm_nonneg _) _ this
  intro n
  calc ∥∑ kl in antidiagonal n, f kl.1 * g kl.2∥ ≤ ∑ kl in antidiagonal n, ∥f kl.1 * g kl.2∥ :=
      norm_sum_le _ _ _ ≤ ∑ kl in antidiagonal n, ∥f kl.1∥ * ∥g kl.2∥ := sum_le_sum fun i _ => norm_mul_le _ _

/-- The Cauchy product formula for the product of two infinite sums indexed by `ℕ`,
    expressed by summing on `finset.nat.antidiagonal`.
    See also `tsum_mul_tsum_eq_tsum_sum_antidiagonal` if `f` and `g` are
    *not* absolutely summable. -/
theorem tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm [CompleteSpace α] {f g : ℕ → α}
    (hf : Summable fun x => ∥f x∥) (hg : Summable fun x => ∥g x∥) :
    ((∑' n, f n) * ∑' n, g n) = ∑' n, ∑ kl in antidiagonal n, f kl.1 * g kl.2 :=
  tsum_mul_tsum_eq_tsum_sum_antidiagonal (summable_of_summable_norm hf) (summable_of_summable_norm hg)
    (summable_mul_of_summable_norm hf hg)

theorem summable_norm_sum_mul_range_of_summable_norm {f g : ℕ → α} (hf : Summable fun x => ∥f x∥)
    (hg : Summable fun x => ∥g x∥) : Summable fun n => ∥∑ k in range (n + 1), f k * g (n - k)∥ := by
  simp_rw [← sum_antidiagonal_eq_sum_range_succ fun k l => f k * g l]
  exact summable_norm_sum_mul_antidiagonal_of_summable_norm hf hg

/-- The Cauchy product formula for the product of two infinite sums indexed by `ℕ`,
    expressed by summing on `finset.range`.
    See also `tsum_mul_tsum_eq_tsum_sum_range` if `f` and `g` are
    *not* absolutely summable. -/
theorem tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm [CompleteSpace α] {f g : ℕ → α} (hf : Summable fun x => ∥f x∥)
    (hg : Summable fun x => ∥g x∥) : ((∑' n, f n) * ∑' n, g n) = ∑' n, ∑ k in range (n + 1), f k * g (n - k) := by
  simp_rw [← sum_antidiagonal_eq_sum_range_succ fun k l => f k * g l]
  exact tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hf hg

end Nat

end CauchyProduct

section RingHomIsometric

variable {R₁ : Type _} {R₂ : Type _} {R₃ : Type _}

/-- This class states that a ring homomorphism is isometric. This is a sufficient assumption
for a continuous semilinear map to be bounded and this is the main use for this typeclass. -/
class RingHomIsometric [Semiringₓ R₁] [Semiringₓ R₂] [HasNorm R₁] [HasNorm R₂] (σ : R₁ →+* R₂) : Prop where
  is_iso : ∀ {x : R₁}, ∥σ x∥ = ∥x∥

attribute [simp] RingHomIsometric.is_iso

variable [SemiNormedRing R₁] [SemiNormedRing R₂] [SemiNormedRing R₃]

instance RingHomIsometric.ids : RingHomIsometric (RingHom.id R₁) :=
  ⟨fun x => rfl⟩

end RingHomIsometric

