/-
Copyright (c) 2018 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathbin.Topology.Algebra.InfiniteSum
import Mathbin.Topology.Algebra.GroupWithZero

/-!
# Topology on `ℝ≥0`

The natural topology on `ℝ≥0` (the one induced from `ℝ`), and a basic API.

## Main definitions

Instances for the following typeclasses are defined:

* `topological_space ℝ≥0`
* `topological_semiring ℝ≥0`
* `second_countable_topology ℝ≥0`
* `order_topology ℝ≥0`
* `has_continuous_sub ℝ≥0`
* `has_continuous_inv₀ ℝ≥0` (continuity of `x⁻¹` away from `0`)
* `has_continuous_smul ℝ≥0 ℝ`

Everything is inherited from the corresponding structures on the reals.

## Main statements

Various mathematically trivial lemmas are proved about the compatibility
of limits and sums in `ℝ≥0` and `ℝ`. For example

* `tendsto_coe {f : filter α} {m : α → ℝ≥0} {x : ℝ≥0} :
  tendsto (λa, (m a : ℝ)) f (𝓝 (x : ℝ)) ↔ tendsto m f (𝓝 x)`

says that the limit of a filter along a map to `ℝ≥0` is the same in `ℝ` and `ℝ≥0`, and

* `coe_tsum {f : α → ℝ≥0} : ((∑'a, f a) : ℝ) = (∑'a, (f a : ℝ))`

says that says that a sum of elements in `ℝ≥0` is the same in `ℝ` and `ℝ≥0`.

Similarly, some mathematically trivial lemmas about infinite sums are proved,
a few of which rely on the fact that subtraction is continuous.

-/


noncomputable section

open Set TopologicalSpace Metric Filter

open TopologicalSpace

namespace Nnreal

open Nnreal BigOperators Filter

instance : TopologicalSpace ℝ≥0 :=
  inferInstance

-- short-circuit type class inference
instance : TopologicalSemiring ℝ≥0 where
  continuous_mul :=
    continuous_subtype_mk _ <|
      (continuous_subtype_val.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)
  continuous_add :=
    continuous_subtype_mk _ <|
      (continuous_subtype_val.comp continuous_fst).add (continuous_subtype_val.comp continuous_snd)

instance : SecondCountableTopology ℝ≥0 :=
  TopologicalSpace.Subtype.second_countable_topology _ _

instance : OrderTopology ℝ≥0 :=
  @order_topology_of_ord_connected _ _ _ _ (Ici 0) _

section coe

variable {α : Type _}

open Filter Finset

theorem _root_.continuous_real_to_nnreal : Continuous Real.toNnreal :=
  continuous_subtype_mk _ <| continuous_id.max continuous_const

theorem continuous_coe : Continuous (coe : ℝ≥0 → ℝ) :=
  continuous_subtype_val

/-- Embedding of `ℝ≥0` to `ℝ` as a bundled continuous map. -/
@[simps (config := { fullyApplied := false })]
def _root_.continuous_map.coe_nnreal_real : C( ℝ≥0 , ℝ) :=
  ⟨coe, continuous_coe⟩

instance {X : Type _} [TopologicalSpace X] : CanLift C(X, ℝ) C(X, ℝ≥0 ) where
  coe := ContinuousMap.coeNnrealReal.comp
  cond := fun f => ∀ x, 0 ≤ f x
  prf := fun f hf => ⟨⟨fun x => ⟨f x, hf x⟩, continuous_subtype_mk _ f.2⟩, FunLike.ext' rfl⟩

@[simp, norm_cast]
theorem tendsto_coe {f : Filter α} {m : α → ℝ≥0 } {x : ℝ≥0 } :
    Tendsto (fun a => (m a : ℝ)) f (𝓝 (x : ℝ)) ↔ Tendsto m f (𝓝 x) :=
  tendsto_subtype_rng.symm

theorem tendsto_coe' {f : Filter α} [NeBot f] {m : α → ℝ≥0 } {x : ℝ} :
    Tendsto (fun a => m a : α → ℝ) f (𝓝 x) ↔ ∃ hx : 0 ≤ x, Tendsto m f (𝓝 ⟨x, hx⟩) :=
  ⟨fun h => ⟨ge_of_tendsto' h fun c => (m c).2, tendsto_coe.1 h⟩, fun ⟨hx, hm⟩ => tendsto_coe.2 hm⟩

@[simp]
theorem map_coe_at_top : map (coe : ℝ≥0 → ℝ) atTop = at_top :=
  map_coe_Ici_at_top 0

theorem comap_coe_at_top : comap (coe : ℝ≥0 → ℝ) atTop = at_top :=
  (at_top_Ici_eq 0).symm

@[simp, norm_cast]
theorem tendsto_coe_at_top {f : Filter α} {m : α → ℝ≥0 } : Tendsto (fun a => (m a : ℝ)) f atTop ↔ Tendsto m f atTop :=
  tendsto_Ici_at_top.symm

theorem tendsto_real_to_nnreal {f : Filter α} {m : α → ℝ} {x : ℝ} (h : Tendsto m f (𝓝 x)) :
    Tendsto (fun a => Real.toNnreal (m a)) f (𝓝 (Real.toNnreal x)) :=
  (continuous_real_to_nnreal.Tendsto _).comp h

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (a «expr ≠ » 0)
theorem nhds_zero : 𝓝 (0 : ℝ≥0 ) = ⨅ (a) (_ : a ≠ 0), 𝓟 (iio a) :=
  nhds_bot_order.trans <| by
    simp [← bot_lt_iff_ne_bot]

theorem nhds_zero_basis : (𝓝 (0 : ℝ≥0 )).HasBasis (fun a : ℝ≥0 => 0 < a) fun a => iio a :=
  nhds_bot_basis

instance : HasContinuousSub ℝ≥0 :=
  ⟨continuous_subtype_mk _ <|
      ((continuous_coe.comp continuous_fst).sub (continuous_coe.comp continuous_snd)).max continuous_const⟩

instance : HasContinuousInv₀ ℝ≥0 :=
  ⟨fun x hx => tendsto_coe.1 <| (Real.tendsto_inv <| Nnreal.coe_ne_zero.2 hx).comp continuous_coe.ContinuousAt⟩

instance :
    HasContinuousSmul ℝ≥0
      ℝ where continuous_smul :=
    Continuous.comp Real.continuous_mul <|
      Continuous.prod_mk (Continuous.comp continuous_subtype_val continuous_fst) continuous_snd

@[norm_cast]
theorem has_sum_coe {f : α → ℝ≥0 } {r : ℝ≥0 } : HasSum (fun a => (f a : ℝ)) (r : ℝ) ↔ HasSum f r := by
  simp only [← HasSum, ← coe_sum.symm, ← tendsto_coe]

theorem has_sum_real_to_nnreal_of_nonneg {f : α → ℝ} (hf_nonneg : ∀ n, 0 ≤ f n) (hf : Summable f) :
    HasSum (fun n => Real.toNnreal (f n)) (Real.toNnreal (∑' n, f n)) := by
  have h_sum : (fun s => ∑ b in s, Real.toNnreal (f b)) = fun s => Real.toNnreal (∑ b in s, f b) :=
    funext fun _ => (Real.to_nnreal_sum_of_nonneg fun n _ => hf_nonneg n).symm
  simp_rw [HasSum, h_sum]
  exact tendsto_real_to_nnreal hf.has_sum

@[norm_cast]
theorem summable_coe {f : α → ℝ≥0 } : (Summable fun a => (f a : ℝ)) ↔ Summable f := by
  constructor
  exact fun ⟨a, ha⟩ => ⟨⟨a, has_sum_le (fun a => (f a).2) has_sum_zero ha⟩, has_sum_coe.1 ha⟩
  exact fun ⟨a, ha⟩ => ⟨a.1, has_sum_coe.2 ha⟩

theorem summable_coe_of_nonneg {f : α → ℝ} (hf₁ : ∀ n, 0 ≤ f n) :
    (@Summable ℝ≥0 _ _ _ fun n => ⟨f n, hf₁ n⟩) ↔ Summable f := by
  lift f to α → ℝ≥0 using hf₁ with f rfl hf₁
  simp only [← summable_coe, ← Subtype.coe_eta]

open Classical

@[norm_cast]
theorem coe_tsum {f : α → ℝ≥0 } : ↑(∑' a, f a) = ∑' a, (f a : ℝ) :=
  if hf : Summable f then Eq.symm <| (has_sum_coe.2 <| hf.HasSum).tsum_eq
  else by
    simp [← tsum, ← hf, ← mt summable_coe.1 hf]

theorem coe_tsum_of_nonneg {f : α → ℝ} (hf₁ : ∀ n, 0 ≤ f n) :
    (⟨∑' n, f n, tsum_nonneg hf₁⟩ : ℝ≥0 ) = (∑' n, ⟨f n, hf₁ n⟩ : ℝ≥0 ) := by
  lift f to α → ℝ≥0 using hf₁ with f rfl hf₁
  simp_rw [← Nnreal.coe_tsum, Subtype.coe_eta]

theorem tsum_mul_left (a : ℝ≥0 ) (f : α → ℝ≥0 ) : (∑' x, a * f x) = a * ∑' x, f x :=
  Nnreal.eq <| by
    simp only [← coe_tsum, ← Nnreal.coe_mul, ← tsum_mul_left]

theorem tsum_mul_right (f : α → ℝ≥0 ) (a : ℝ≥0 ) : (∑' x, f x * a) = (∑' x, f x) * a :=
  Nnreal.eq <| by
    simp only [← coe_tsum, ← Nnreal.coe_mul, ← tsum_mul_right]

theorem summable_comp_injective {β : Type _} {f : α → ℝ≥0 } (hf : Summable f) {i : β → α} (hi : Function.Injective i) :
    Summable (f ∘ i) :=
  Nnreal.summable_coe.1 <| show Summable ((coe ∘ f) ∘ i) from (Nnreal.summable_coe.2 hf).comp_injective hi

theorem summable_nat_add (f : ℕ → ℝ≥0 ) (hf : Summable f) (k : ℕ) : Summable fun i => f (i + k) :=
  summable_comp_injective hf <| add_left_injective k

theorem summable_nat_add_iff {f : ℕ → ℝ≥0 } (k : ℕ) : (Summable fun i => f (i + k)) ↔ Summable f := by
  rw [← summable_coe, ← summable_coe]
  exact @summable_nat_add_iff ℝ _ _ _ (fun i => (f i : ℝ)) k

theorem has_sum_nat_add_iff {f : ℕ → ℝ≥0 } (k : ℕ) {a : ℝ≥0 } :
    HasSum (fun n => f (n + k)) a ↔ HasSum f (a + ∑ i in range k, f i) := by
  simp [has_sum_coe, ← coe_sum, ← Nnreal.coe_add, has_sum_nat_add_iff k]

theorem sum_add_tsum_nat_add {f : ℕ → ℝ≥0 } (k : ℕ) (hf : Summable f) :
    (∑' i, f i) = (∑ i in range k, f i) + ∑' i, f (i + k) := by
  rw [← Nnreal.coe_eq, coe_tsum, Nnreal.coe_add, coe_sum, coe_tsum, sum_add_tsum_nat_add k (Nnreal.summable_coe.2 hf)]

theorem infi_real_pos_eq_infi_nnreal_pos [CompleteLattice α] {f : ℝ → α} :
    (⨅ (n : ℝ) (h : 0 < n), f n) = ⨅ (n : ℝ≥0 ) (h : 0 < n), f n :=
  le_antisymmₓ (infi_mono' fun r => ⟨r, le_rfl⟩) (infi₂_mono' fun r hr => ⟨⟨r, hr.le⟩, hr, le_rfl⟩)

end coe

theorem tendsto_cofinite_zero_of_summable {α} {f : α → ℝ≥0 } (hf : Summable f) : Tendsto f cofinite (𝓝 0) := by
  have h_f_coe : f = fun n => Real.toNnreal (f n : ℝ) := funext fun n => real.to_nnreal_coe.symm
  rw [h_f_coe, ← @Real.to_nnreal_coe 0]
  exact tendsto_real_to_nnreal (summable_coe.mpr hf).tendsto_cofinite_zero

theorem tendsto_at_top_zero_of_summable {f : ℕ → ℝ≥0 } (hf : Summable f) : Tendsto f atTop (𝓝 0) := by
  rw [← Nat.cofinite_eq_at_top]
  exact tendsto_cofinite_zero_of_summable hf

/-- The sum over the complement of a finset tends to `0` when the finset grows to cover the whole
space. This does not need a summability assumption, as otherwise all sums are zero. -/
theorem tendsto_tsum_compl_at_top_zero {α : Type _} (f : α → ℝ≥0 ) :
    Tendsto (fun s : Finset α => ∑' b : { x // x ∉ s }, f b) atTop (𝓝 0) := by
  simp_rw [← tendsto_coe, coe_tsum, Nnreal.coe_zero]
  exact tendsto_tsum_compl_at_top_zero fun a : α => (f a : ℝ)

end Nnreal

