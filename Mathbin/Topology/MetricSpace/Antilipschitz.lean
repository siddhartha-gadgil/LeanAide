/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathbin.Topology.MetricSpace.Lipschitz
import Mathbin.Topology.UniformSpace.CompleteSeparated

/-!
# Antilipschitz functions

We say that a map `f : α → β` between two (extended) metric spaces is
`antilipschitz_with K`, `K ≥ 0`, if for all `x, y` we have `edist x y ≤ K * edist (f x) (f y)`.
For a metric space, the latter inequality is equivalent to `dist x y ≤ K * dist (f x) (f y)`.

## Implementation notes

The parameter `K` has type `ℝ≥0`. This way we avoid conjuction in the definition and have
coercions both to `ℝ` and `ℝ≥0∞`. We do not require `0 < K` in the definition, mostly because
we do not have a `posreal` type.
-/


variable {α : Type _} {β : Type _} {γ : Type _}

open Nnreal Ennreal uniformity

open Set Filter Bornology

/-- We say that `f : α → β` is `antilipschitz_with K` if for any two points `x`, `y` we have
`K * edist x y ≤ edist (f x) (f y)`. -/
def AntilipschitzWith [PseudoEmetricSpace α] [PseudoEmetricSpace β] (K : ℝ≥0 ) (f : α → β) :=
  ∀ x y, edist x y ≤ K * edist (f x) (f y)

theorem AntilipschitzWith.edist_lt_top [PseudoEmetricSpace α] [PseudoMetricSpace β] {K : ℝ≥0 } {f : α → β}
    (h : AntilipschitzWith K f) (x y : α) : edist x y < ⊤ :=
  (h x y).trans_lt <| Ennreal.mul_lt_top Ennreal.coe_ne_top (edist_ne_top _ _)

theorem AntilipschitzWith.edist_ne_top [PseudoEmetricSpace α] [PseudoMetricSpace β] {K : ℝ≥0 } {f : α → β}
    (h : AntilipschitzWith K f) (x y : α) : edist x y ≠ ⊤ :=
  (h.edist_lt_top x y).Ne

section Metric

variable [PseudoMetricSpace α] [PseudoMetricSpace β] {K : ℝ≥0 } {f : α → β}

theorem antilipschitz_with_iff_le_mul_nndist : AntilipschitzWith K f ↔ ∀ x y, nndist x y ≤ K * nndist (f x) (f y) := by
  simp only [← AntilipschitzWith, ← edist_nndist]
  norm_cast

alias antilipschitz_with_iff_le_mul_nndist ↔ AntilipschitzWith.le_mul_nndist AntilipschitzWith.of_le_mul_nndist

theorem antilipschitz_with_iff_le_mul_dist : AntilipschitzWith K f ↔ ∀ x y, dist x y ≤ K * dist (f x) (f y) := by
  simp only [← antilipschitz_with_iff_le_mul_nndist, ← dist_nndist]
  norm_cast

alias antilipschitz_with_iff_le_mul_dist ↔ AntilipschitzWith.le_mul_dist AntilipschitzWith.of_le_mul_dist

namespace AntilipschitzWith

theorem mul_le_nndist (hf : AntilipschitzWith K f) (x y : α) : K⁻¹ * nndist x y ≤ nndist (f x) (f y) := by
  simpa only [← div_eq_inv_mul] using Nnreal.div_le_of_le_mul' (hf.le_mul_nndist x y)

theorem mul_le_dist (hf : AntilipschitzWith K f) (x y : α) : (K⁻¹ * dist x y : ℝ) ≤ dist (f x) (f y) := by
  exact_mod_cast hf.mul_le_nndist x y

end AntilipschitzWith

end Metric

namespace AntilipschitzWith

variable [PseudoEmetricSpace α] [PseudoEmetricSpace β] [PseudoEmetricSpace γ]

variable {K : ℝ≥0 } {f : α → β}

open Emetric

/-- Extract the constant from `hf : antilipschitz_with K f`. This is useful, e.g.,
if `K` is given by a long formula, and we want to reuse this value. -/
-- uses neither `f` nor `hf`
@[nolint unused_arguments]
protected def k (hf : AntilipschitzWith K f) : ℝ≥0 :=
  K

protected theorem injective {α : Type _} {β : Type _} [EmetricSpace α] [PseudoEmetricSpace β] {K : ℝ≥0 } {f : α → β}
    (hf : AntilipschitzWith K f) : Function.Injective f := fun x y h => by
  simpa only [← h, ← edist_self, ← mul_zero, ← edist_le_zero] using hf x y

theorem mul_le_edist (hf : AntilipschitzWith K f) (x y : α) : (K⁻¹ * edist x y : ℝ≥0∞) ≤ edist (f x) (f y) := by
  rw [mul_comm, ← div_eq_mul_inv]
  exact Ennreal.div_le_of_le_mul' (hf x y)

theorem ediam_preimage_le (hf : AntilipschitzWith K f) (s : Set β) : diam (f ⁻¹' s) ≤ K * diam s :=
  diam_le fun x hx y hy => (hf x y).trans <| mul_le_mul_left' (edist_le_diam_of_mem hx hy) K

theorem le_mul_ediam_image (hf : AntilipschitzWith K f) (s : Set α) : diam s ≤ K * diam (f '' s) :=
  (diam_mono (subset_preimage_image _ _)).trans (hf.ediam_preimage_le (f '' s))

protected theorem id : AntilipschitzWith 1 (id : α → α) := fun x y => by
  simp only [← Ennreal.coe_one, ← one_mulₓ, ← id, ← le_reflₓ]

theorem comp {Kg : ℝ≥0 } {g : β → γ} (hg : AntilipschitzWith Kg g) {Kf : ℝ≥0 } {f : α → β}
    (hf : AntilipschitzWith Kf f) : AntilipschitzWith (Kf * Kg) (g ∘ f) := fun x y =>
  calc
    edist x y ≤ Kf * edist (f x) (f y) := hf x y
    _ ≤ Kf * (Kg * edist (g (f x)) (g (f y))) := Ennreal.mul_left_mono (hg _ _)
    _ = _ := by
      rw [Ennreal.coe_mul, mul_assoc]
    

theorem restrict (hf : AntilipschitzWith K f) (s : Set α) : AntilipschitzWith K (s.restrict f) := fun x y => hf x y

theorem cod_restrict (hf : AntilipschitzWith K f) {s : Set β} (hs : ∀ x, f x ∈ s) :
    AntilipschitzWith K (s.codRestrict f hs) := fun x y => hf x y

theorem to_right_inv_on' {s : Set α} (hf : AntilipschitzWith K (s.restrict f)) {g : β → α} {t : Set β}
    (g_maps : MapsTo g t s) (g_inv : RightInvOn g f t) : LipschitzWith K (t.restrict g) := fun x y => by
  simpa only [← restrict_apply, ← g_inv x.mem, ← g_inv y.mem, ← Subtype.edist_eq, ← Subtype.coe_mk] using
    hf ⟨g x, g_maps x.mem⟩ ⟨g y, g_maps y.mem⟩

theorem to_right_inv_on (hf : AntilipschitzWith K f) {g : β → α} {t : Set β} (h : RightInvOn g f t) :
    LipschitzWith K (t.restrict g) :=
  (hf.restrict Univ).to_right_inv_on' (maps_to_univ g t) h

theorem to_right_inverse (hf : AntilipschitzWith K f) {g : β → α} (hg : Function.RightInverse g f) :
    LipschitzWith K g := by
  intro x y
  have := hf (g x) (g y)
  rwa [hg x, hg y] at this

theorem comap_uniformity_le (hf : AntilipschitzWith K f) : (𝓤 β).comap (Prod.map f f) ≤ 𝓤 α := by
  refine' ((uniformity_basis_edist.comap _).le_basis_iff uniformity_basis_edist).2 fun ε h₀ => _
  refine' ⟨K⁻¹ * ε, Ennreal.mul_pos (Ennreal.inv_ne_zero.2 Ennreal.coe_ne_top) h₀.ne', _⟩
  refine' fun x hx => (hf x.1 x.2).trans_lt _
  rw [mul_comm, ← div_eq_mul_inv] at hx
  rw [mul_comm]
  exact Ennreal.mul_lt_of_lt_div hx

protected theorem uniform_inducing (hf : AntilipschitzWith K f) (hfc : UniformContinuous f) : UniformInducing f :=
  ⟨le_antisymmₓ hf.comap_uniformity_le hfc.le_comap⟩

protected theorem uniform_embedding {α : Type _} {β : Type _} [EmetricSpace α] [PseudoEmetricSpace β] {K : ℝ≥0 }
    {f : α → β} (hf : AntilipschitzWith K f) (hfc : UniformContinuous f) : UniformEmbedding f :=
  ⟨hf.UniformInducing hfc, hf.Injective⟩

theorem is_complete_range [CompleteSpace α] (hf : AntilipschitzWith K f) (hfc : UniformContinuous f) :
    IsComplete (Range f) :=
  (hf.UniformInducing hfc).is_complete_range

theorem is_closed_range {α β : Type _} [PseudoEmetricSpace α] [EmetricSpace β] [CompleteSpace α] {f : α → β} {K : ℝ≥0 }
    (hf : AntilipschitzWith K f) (hfc : UniformContinuous f) : IsClosed (Range f) :=
  (hf.is_complete_range hfc).IsClosed

theorem closed_embedding {α : Type _} {β : Type _} [EmetricSpace α] [EmetricSpace β] {K : ℝ≥0 } {f : α → β}
    [CompleteSpace α] (hf : AntilipschitzWith K f) (hfc : UniformContinuous f) : ClosedEmbedding f :=
  { (hf.UniformEmbedding hfc).Embedding with closed_range := hf.is_closed_range hfc }

theorem subtype_coe (s : Set α) : AntilipschitzWith 1 (coe : s → α) :=
  AntilipschitzWith.id.restrict s

theorem of_subsingleton [Subsingleton α] {K : ℝ≥0 } : AntilipschitzWith K f := fun x y => by
  simp only [← Subsingleton.elimₓ x y, ← edist_self, ← zero_le]

/-- If `f : α → β` is `0`-antilipschitz, then `α` is a `subsingleton`. -/
protected theorem subsingleton {α β} [EmetricSpace α] [PseudoEmetricSpace β] {f : α → β} (h : AntilipschitzWith 0 f) :
    Subsingleton α :=
  ⟨fun x y => edist_le_zero.1 <| (h x y).trans_eq <| zero_mul _⟩

end AntilipschitzWith

namespace AntilipschitzWith

open Metric

variable [PseudoMetricSpace α] [PseudoMetricSpace β] {K : ℝ≥0 } {f : α → β}

theorem bounded_preimage (hf : AntilipschitzWith K f) {s : Set β} (hs : Bounded s) : Bounded (f ⁻¹' s) :=
  (Exists.introₓ (K * diam s)) fun x hx y hy =>
    calc
      dist x y ≤ K * dist (f x) (f y) := hf.le_mul_dist x y
      _ ≤ K * diam s := mul_le_mul_of_nonneg_left (dist_le_diam_of_mem hs hx hy) K.2
      

theorem tendsto_cobounded (hf : AntilipschitzWith K f) : Tendsto f (cobounded α) (cobounded β) :=
  compl_surjective.forall.2 fun s (hs : IsBounded s) =>
    Metric.is_bounded_iff.2 <| hf.bounded_preimage <| Metric.is_bounded_iff.1 hs

/-- The image of a proper space under an expanding onto map is proper. -/
protected theorem proper_space {α : Type _} [MetricSpace α] {K : ℝ≥0 } {f : α → β} [ProperSpace α]
    (hK : AntilipschitzWith K f) (f_cont : Continuous f) (hf : Function.Surjective f) : ProperSpace β := by
  apply proper_space_of_compact_closed_ball_of_le 0 fun x₀ r hr => _
  let K := f ⁻¹' closed_ball x₀ r
  have A : IsClosed K := is_closed_ball.preimage f_cont
  have B : bounded K := hK.bounded_preimage bounded_closed_ball
  have : IsCompact K := compact_iff_closed_bounded.2 ⟨A, B⟩
  convert this.image f_cont
  exact (hf.image_preimage _).symm

end AntilipschitzWith

theorem LipschitzWith.to_right_inverse [PseudoEmetricSpace α] [PseudoEmetricSpace β] {K : ℝ≥0 } {f : α → β}
    (hf : LipschitzWith K f) {g : β → α} (hg : Function.RightInverse g f) : AntilipschitzWith K g := fun x y => by
  simpa only [← hg _] using hf (g x) (g y)

