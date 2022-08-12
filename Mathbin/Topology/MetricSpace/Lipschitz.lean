/-
Copyright (c) 2018 Rohan Mitta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Mitta, Kevin Buzzard, Alistair Tucker, Johannes Hölzl, Yury Kudryashov
-/
import Mathbin.Logic.Function.Iterate
import Mathbin.Data.Set.Intervals.ProjIcc
import Mathbin.Topology.MetricSpace.Basic
import Mathbin.Topology.Bornology.Hom

/-!
# Lipschitz continuous functions

A map `f : α → β` between two (extended) metric spaces is called *Lipschitz continuous*
with constant `K ≥ 0` if for all `x, y` we have `edist (f x) (f y) ≤ K * edist x y`.
For a metric space, the latter inequality is equivalent to `dist (f x) (f y) ≤ K * dist x y`.
There is also a version asserting this inequality only for `x` and `y` in some set `s`.

In this file we provide various ways to prove that various combinations of Lipschitz continuous
functions are Lipschitz continuous. We also prove that Lipschitz continuous functions are
uniformly continuous.

## Main definitions and lemmas

* `lipschitz_with K f`: states that `f` is Lipschitz with constant `K : ℝ≥0`
* `lipschitz_on_with K f`: states that `f` is Lipschitz with constant `K : ℝ≥0` on a set `s`
* `lipschitz_with.uniform_continuous`: a Lipschitz function is uniformly continuous
* `lipschitz_on_with.uniform_continuous_on`: a function which is Lipschitz on a set is uniformly
  continuous on that set.


## Implementation notes

The parameter `K` has type `ℝ≥0`. This way we avoid conjuction in the definition and have
coercions both to `ℝ` and `ℝ≥0∞`. Constructors whose names end with `'` take `K : ℝ` as an
argument, and return `lipschitz_with (real.to_nnreal K) f`.
-/


universe u v w x

open Filter Function Set

open TopologicalSpace Nnreal Ennreal

variable {α : Type u} {β : Type v} {γ : Type w} {ι : Type x}

/-- A function `f` is Lipschitz continuous with constant `K ≥ 0` if for all `x, y`
we have `dist (f x) (f y) ≤ K * dist x y` -/
def LipschitzWith [PseudoEmetricSpace α] [PseudoEmetricSpace β] (K : ℝ≥0 ) (f : α → β) :=
  ∀ x y, edist (f x) (f y) ≤ K * edist x y

theorem lipschitz_with_iff_dist_le_mul [PseudoMetricSpace α] [PseudoMetricSpace β] {K : ℝ≥0 } {f : α → β} :
    LipschitzWith K f ↔ ∀ x y, dist (f x) (f y) ≤ K * dist x y := by
  simp only [← LipschitzWith, ← edist_nndist, ← dist_nndist]
  norm_cast

alias lipschitz_with_iff_dist_le_mul ↔ LipschitzWith.dist_le_mul LipschitzWith.of_dist_le_mul

/-- A function `f` is Lipschitz continuous with constant `K ≥ 0` on `s` if for all `x, y` in `s`
we have `dist (f x) (f y) ≤ K * dist x y` -/
def LipschitzOnWith [PseudoEmetricSpace α] [PseudoEmetricSpace β] (K : ℝ≥0 ) (f : α → β) (s : Set α) :=
  ∀ ⦃x⦄ (hx : x ∈ s) ⦃y⦄ (hy : y ∈ s), edist (f x) (f y) ≤ K * edist x y

@[simp]
theorem lipschitz_on_with_empty [PseudoEmetricSpace α] [PseudoEmetricSpace β] (K : ℝ≥0 ) (f : α → β) :
    LipschitzOnWith K f ∅ := fun x x_in y y_in => False.elim x_in

theorem LipschitzOnWith.mono [PseudoEmetricSpace α] [PseudoEmetricSpace β] {K : ℝ≥0 } {s t : Set α} {f : α → β}
    (hf : LipschitzOnWith K f t) (h : s ⊆ t) : LipschitzOnWith K f s := fun x x_in y y_in => hf (h x_in) (h y_in)

theorem lipschitz_on_with_iff_dist_le_mul [PseudoMetricSpace α] [PseudoMetricSpace β] {K : ℝ≥0 } {s : Set α}
    {f : α → β} : LipschitzOnWith K f s ↔ ∀, ∀ x ∈ s, ∀, ∀ y ∈ s, ∀, dist (f x) (f y) ≤ K * dist x y := by
  simp only [← LipschitzOnWith, ← edist_nndist, ← dist_nndist]
  norm_cast

alias lipschitz_on_with_iff_dist_le_mul ↔ LipschitzOnWith.dist_le_mul LipschitzOnWith.of_dist_le_mul

@[simp]
theorem lipschitz_on_univ [PseudoEmetricSpace α] [PseudoEmetricSpace β] {K : ℝ≥0 } {f : α → β} :
    LipschitzOnWith K f Univ ↔ LipschitzWith K f := by
  simp [← LipschitzOnWith, ← LipschitzWith]

theorem lipschitz_on_with_iff_restrict [PseudoEmetricSpace α] [PseudoEmetricSpace β] {K : ℝ≥0 } {f : α → β}
    {s : Set α} : LipschitzOnWith K f s ↔ LipschitzWith K (s.restrict f) := by
  simp only [← LipschitzOnWith, ← LipschitzWith, ← SetCoe.forall', ← restrict, ← Subtype.edist_eq]

namespace LipschitzWith

section Emetric

open Emetric

variable [PseudoEmetricSpace α] [PseudoEmetricSpace β] [PseudoEmetricSpace γ]

variable {K : ℝ≥0 } {f : α → β} {x y : α} {r : ℝ≥0∞}

protected theorem lipschitz_on_with (h : LipschitzWith K f) (s : Set α) : LipschitzOnWith K f s := fun x _ y _ => h x y

theorem edist_le_mul (h : LipschitzWith K f) (x y : α) : edist (f x) (f y) ≤ K * edist x y :=
  h x y

theorem edist_le_mul_of_le (h : LipschitzWith K f) (hr : edist x y ≤ r) : edist (f x) (f y) ≤ K * r :=
  (h x y).trans <| Ennreal.mul_left_mono hr

theorem edist_lt_mul_of_lt (h : LipschitzWith K f) (hK : K ≠ 0) (hr : edist x y < r) : edist (f x) (f y) < K * r :=
  (h x y).trans_lt <| (Ennreal.mul_lt_mul_left (Ennreal.coe_ne_zero.2 hK) Ennreal.coe_ne_top).2 hr

theorem maps_to_emetric_closed_ball (h : LipschitzWith K f) (x : α) (r : ℝ≥0∞) :
    MapsTo f (ClosedBall x r) (ClosedBall (f x) (K * r)) := fun y hy => h.edist_le_mul_of_le hy

theorem maps_to_emetric_ball (h : LipschitzWith K f) (hK : K ≠ 0) (x : α) (r : ℝ≥0∞) :
    MapsTo f (Ball x r) (Ball (f x) (K * r)) := fun y hy => h.edist_lt_mul_of_lt hK hy

theorem edist_lt_top (hf : LipschitzWith K f) {x y : α} (h : edist x y ≠ ⊤) : edist (f x) (f y) < ⊤ :=
  (hf x y).trans_lt <| Ennreal.mul_lt_top Ennreal.coe_ne_top h

theorem mul_edist_le (h : LipschitzWith K f) (x y : α) : (K⁻¹ : ℝ≥0∞) * edist (f x) (f y) ≤ edist x y := by
  rw [mul_comm, ← div_eq_mul_inv]
  exact Ennreal.div_le_of_le_mul' (h x y)

protected theorem of_edist_le (h : ∀ x y, edist (f x) (f y) ≤ edist x y) : LipschitzWith 1 f := fun x y => by
  simp only [← Ennreal.coe_one, ← one_mulₓ, ← h]

protected theorem weaken (hf : LipschitzWith K f) {K' : ℝ≥0 } (h : K ≤ K') : LipschitzWith K' f := fun x y =>
  le_transₓ (hf x y) <| Ennreal.mul_right_mono (Ennreal.coe_le_coe.2 h)

theorem ediam_image_le (hf : LipschitzWith K f) (s : Set α) : Emetric.diam (f '' s) ≤ K * Emetric.diam s := by
  apply Emetric.diam_le
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  exact hf.edist_le_mul_of_le (Emetric.edist_le_diam_of_mem hx hy)

theorem edist_lt_of_edist_lt_div (hf : LipschitzWith K f) {x y : α} {d : ℝ≥0∞} (h : edist x y < d / K) :
    edist (f x) (f y) < d :=
  calc
    edist (f x) (f y) ≤ K * edist x y := hf x y
    _ < d := Ennreal.mul_lt_of_lt_div' h
    

/-- A Lipschitz function is uniformly continuous -/
protected theorem uniform_continuous (hf : LipschitzWith K f) : UniformContinuous f := by
  refine' Emetric.uniform_continuous_iff.2 fun ε εpos => _
  use ε / K, Ennreal.div_pos_iff.2 ⟨ne_of_gtₓ εpos, Ennreal.coe_ne_top⟩
  exact fun x y => hf.edist_lt_of_edist_lt_div

/-- A Lipschitz function is continuous -/
protected theorem continuous (hf : LipschitzWith K f) : Continuous f :=
  hf.UniformContinuous.Continuous

protected theorem const (b : β) : LipschitzWith 0 fun a : α => b := fun x y => by
  simp only [← edist_self, ← zero_le]

protected theorem id : LipschitzWith 1 (@id α) :=
  LipschitzWith.of_edist_le fun x y => le_rfl

protected theorem subtype_val (s : Set α) : LipschitzWith 1 (Subtype.val : s → α) :=
  LipschitzWith.of_edist_le fun x y => le_rfl

protected theorem subtype_coe (s : Set α) : LipschitzWith 1 (coe : s → α) :=
  LipschitzWith.subtype_val s

theorem subtype_mk (hf : LipschitzWith K f) {p : β → Prop} (hp : ∀ x, p (f x)) :
    LipschitzWith K (fun x => ⟨f x, hp x⟩ : α → { y // p y }) :=
  hf

protected theorem eval {α : ι → Type u} [∀ i, PseudoEmetricSpace (α i)] [Fintype ι] (i : ι) :
    LipschitzWith 1 (Function.eval i : (∀ i, α i) → α i) :=
  LipschitzWith.of_edist_le fun f g => by
    convert edist_le_pi_edist f g i

protected theorem restrict (hf : LipschitzWith K f) (s : Set α) : LipschitzWith K (s.restrict f) := fun x y => hf x y

protected theorem comp {Kf Kg : ℝ≥0 } {f : β → γ} {g : α → β} (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g) :
    LipschitzWith (Kf * Kg) (f ∘ g) := fun x y =>
  calc
    edist (f (g x)) (f (g y)) ≤ Kf * edist (g x) (g y) := hf _ _
    _ ≤ Kf * (Kg * edist x y) := Ennreal.mul_left_mono (hg _ _)
    _ = (Kf * Kg : ℝ≥0 ) * edist x y := by
      rw [← mul_assoc, Ennreal.coe_mul]
    

theorem comp_lipschitz_on_with {Kf Kg : ℝ≥0 } {f : β → γ} {g : α → β} {s : Set α} (hf : LipschitzWith Kf f)
    (hg : LipschitzOnWith Kg g s) : LipschitzOnWith (Kf * Kg) (f ∘ g) s := fun x hx y hy =>
  calc
    edist (f (g x)) (f (g y)) ≤ Kf * edist (g x) (g y) := hf _ _
    _ ≤ Kf * (Kg * edist x y) := Ennreal.mul_left_mono (hg hx hy)
    _ = (Kf * Kg : ℝ≥0 ) * edist x y := by
      rw [← mul_assoc, Ennreal.coe_mul]
    

protected theorem prod_fst : LipschitzWith 1 (@Prod.fst α β) :=
  LipschitzWith.of_edist_le fun x y => le_max_leftₓ _ _

protected theorem prod_snd : LipschitzWith 1 (@Prod.snd α β) :=
  LipschitzWith.of_edist_le fun x y => le_max_rightₓ _ _

protected theorem prod {f : α → β} {Kf : ℝ≥0 } (hf : LipschitzWith Kf f) {g : α → γ} {Kg : ℝ≥0 }
    (hg : LipschitzWith Kg g) : LipschitzWith (max Kf Kg) fun x => (f x, g x) := by
  intro x y
  rw [ennreal.coe_mono.map_max, Prod.edist_eq, Ennreal.max_mul]
  exact max_le_max (hf x y) (hg x y)

protected theorem uncurry {f : α → β → γ} {Kα Kβ : ℝ≥0 } (hα : ∀ b, LipschitzWith Kα fun a => f a b)
    (hβ : ∀ a, LipschitzWith Kβ (f a)) : LipschitzWith (Kα + Kβ) (Function.uncurry f) := by
  rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩
  simp only [← Function.uncurry, ← Ennreal.coe_add, ← add_mulₓ]
  apply le_transₓ (edist_triangle _ (f a₂ b₁) _)
  exact
    add_le_add (le_transₓ (hα _ _ _) <| Ennreal.mul_left_mono <| le_max_leftₓ _ _)
      (le_transₓ (hβ _ _ _) <| Ennreal.mul_left_mono <| le_max_rightₓ _ _)

protected theorem iterate {f : α → α} (hf : LipschitzWith K f) : ∀ n, LipschitzWith (K ^ n) (f^[n])
  | 0 => LipschitzWith.id
  | n + 1 => by
    rw [pow_succ'ₓ] <;> exact (iterate n).comp hf

theorem edist_iterate_succ_le_geometric {f : α → α} (hf : LipschitzWith K f) (x n) :
    edist ((f^[n]) x) ((f^[n + 1]) x) ≤ edist x (f x) * K ^ n := by
  rw [iterate_succ, mul_comm]
  simpa only [← Ennreal.coe_pow] using (hf.iterate n) x (f x)

protected theorem mul {f g : Function.End α} {Kf Kg} (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g) :
    LipschitzWith (Kf * Kg) (f * g : Function.End α) :=
  hf.comp hg

/-- The product of a list of Lipschitz continuous endomorphisms is a Lipschitz continuous
endomorphism. -/
protected theorem list_prod (f : ι → Function.End α) (K : ι → ℝ≥0 ) (h : ∀ i, LipschitzWith (K i) (f i)) :
    ∀ l : List ι, LipschitzWith (l.map K).Prod (l.map f).Prod
  | [] => by
    simpa using LipschitzWith.id
  | i :: l => by
    simp only [← List.map_cons, ← List.prod_cons]
    exact (h i).mul (list_prod l)

protected theorem pow {f : Function.End α} {K} (h : LipschitzWith K f) :
    ∀ n : ℕ, LipschitzWith (K ^ n) (f ^ n : Function.End α)
  | 0 => LipschitzWith.id
  | n + 1 => by
    rw [pow_succₓ, pow_succₓ]
    exact h.mul (pow n)

end Emetric

section Metric

variable [PseudoMetricSpace α] [PseudoMetricSpace β] [PseudoMetricSpace γ] {K : ℝ≥0 } {f : α → β} {x y : α} {r : ℝ}

protected theorem of_dist_le' {K : ℝ} (h : ∀ x y, dist (f x) (f y) ≤ K * dist x y) :
    LipschitzWith (Real.toNnreal K) f :=
  of_dist_le_mul fun x y => le_transₓ (h x y) <| mul_le_mul_of_nonneg_right (Real.le_coe_to_nnreal K) dist_nonneg

protected theorem mk_one (h : ∀ x y, dist (f x) (f y) ≤ dist x y) : LipschitzWith 1 f :=
  of_dist_le_mul <| by
    simpa only [← Nnreal.coe_one, ← one_mulₓ] using h

/-- For functions to `ℝ`, it suffices to prove `f x ≤ f y + K * dist x y`; this version
doesn't assume `0≤K`. -/
protected theorem of_le_add_mul' {f : α → ℝ} (K : ℝ) (h : ∀ x y, f x ≤ f y + K * dist x y) :
    LipschitzWith (Real.toNnreal K) f :=
  have I : ∀ x y, f x - f y ≤ K * dist x y := fun x y => sub_le_iff_le_add'.2 (h x y)
  LipschitzWith.of_dist_le' fun x y => abs_sub_le_iff.2 ⟨I x y, dist_comm y x ▸ I y x⟩

/-- For functions to `ℝ`, it suffices to prove `f x ≤ f y + K * dist x y`; this version
assumes `0≤K`. -/
protected theorem of_le_add_mul {f : α → ℝ} (K : ℝ≥0 ) (h : ∀ x y, f x ≤ f y + K * dist x y) : LipschitzWith K f := by
  simpa only [← Real.to_nnreal_coe] using LipschitzWith.of_le_add_mul' K h

protected theorem of_le_add {f : α → ℝ} (h : ∀ x y, f x ≤ f y + dist x y) : LipschitzWith 1 f :=
  LipschitzWith.of_le_add_mul 1 <| by
    simpa only [← Nnreal.coe_one, ← one_mulₓ]

protected theorem le_add_mul {f : α → ℝ} {K : ℝ≥0 } (h : LipschitzWith K f) (x y) : f x ≤ f y + K * dist x y :=
  sub_le_iff_le_add'.1 <| le_transₓ (le_abs_self _) <| h.dist_le_mul x y

protected theorem iff_le_add_mul {f : α → ℝ} {K : ℝ≥0 } : LipschitzWith K f ↔ ∀ x y, f x ≤ f y + K * dist x y :=
  ⟨LipschitzWith.le_add_mul, LipschitzWith.of_le_add_mul K⟩

theorem nndist_le (hf : LipschitzWith K f) (x y : α) : nndist (f x) (f y) ≤ K * nndist x y :=
  hf.dist_le_mul x y

theorem dist_le_mul_of_le (hf : LipschitzWith K f) (hr : dist x y ≤ r) : dist (f x) (f y) ≤ K * r :=
  (hf.dist_le_mul x y).trans <| mul_le_mul_of_nonneg_left hr K.coe_nonneg

theorem maps_to_closed_ball (hf : LipschitzWith K f) (x : α) (r : ℝ) :
    MapsTo f (Metric.ClosedBall x r) (Metric.ClosedBall (f x) (K * r)) := fun y hy => hf.dist_le_mul_of_le hy

theorem dist_lt_mul_of_lt (hf : LipschitzWith K f) (hK : K ≠ 0) (hr : dist x y < r) : dist (f x) (f y) < K * r :=
  (hf.dist_le_mul x y).trans_lt <| (mul_lt_mul_left <| Nnreal.coe_pos.2 hK.bot_lt).2 hr

theorem maps_to_ball (hf : LipschitzWith K f) (hK : K ≠ 0) (x : α) (r : ℝ) :
    MapsTo f (Metric.Ball x r) (Metric.Ball (f x) (K * r)) := fun y hy => hf.dist_lt_mul_of_lt hK hy

/-- A Lipschitz continuous map is a locally bounded map. -/
def toLocallyBoundedMap (f : α → β) (hf : LipschitzWith K f) : LocallyBoundedMap α β :=
  (LocallyBoundedMap.ofMapBounded f) fun s hs =>
    let ⟨C, hC⟩ := Metric.is_bounded_iff.1 hs
    Metric.is_bounded_iff.2
      ⟨K * C, ball_image_iff.2 fun x hx => ball_image_iff.2 fun y hy => hf.dist_le_mul_of_le (hC hx hy)⟩

@[simp]
theorem coe_to_locally_bounded_map (hf : LipschitzWith K f) : ⇑(hf.toLocallyBoundedMap f) = f :=
  rfl

theorem comap_cobounded_le (hf : LipschitzWith K f) : comap f (Bornology.cobounded β) ≤ Bornology.cobounded α :=
  (hf.toLocallyBoundedMap f).2

theorem bounded_image (hf : LipschitzWith K f) {s : Set α} (hs : Metric.Bounded s) : Metric.Bounded (f '' s) :=
  Metric.bounded_iff_ediam_ne_top.2 <|
    ne_top_of_le_ne_top (Ennreal.mul_ne_top Ennreal.coe_ne_top hs.ediam_ne_top) (hf.ediam_image_le s)

theorem diam_image_le (hf : LipschitzWith K f) (s : Set α) (hs : Metric.Bounded s) :
    Metric.diam (f '' s) ≤ K * Metric.diam s :=
  Metric.diam_le_of_forall_dist_le (mul_nonneg K.coe_nonneg Metric.diam_nonneg) <|
    ball_image_iff.2 fun x hx =>
      ball_image_iff.2 fun y hy => hf.dist_le_mul_of_le <| Metric.dist_le_diam_of_mem hs hx hy

protected theorem dist_left (y : α) : LipschitzWith 1 fun x => dist x y :=
  LipschitzWith.of_le_add fun x z => by
    rw [add_commₓ]
    apply dist_triangle

protected theorem dist_right (x : α) : LipschitzWith 1 (dist x) :=
  LipschitzWith.of_le_add fun y z => dist_triangle_right _ _ _

protected theorem dist : LipschitzWith 2 (Function.uncurry <| @dist α _) :=
  LipschitzWith.uncurry LipschitzWith.dist_left LipschitzWith.dist_right

theorem dist_iterate_succ_le_geometric {f : α → α} (hf : LipschitzWith K f) (x n) :
    dist ((f^[n]) x) ((f^[n + 1]) x) ≤ dist x (f x) * K ^ n := by
  rw [iterate_succ, mul_comm]
  simpa only [← Nnreal.coe_pow] using (hf.iterate n).dist_le_mul x (f x)

theorem _root_.lipschitz_with_max : LipschitzWith 1 fun p : ℝ × ℝ => max p.1 p.2 :=
  LipschitzWith.of_le_add fun p₁ p₂ => sub_le_iff_le_add'.1 <| (le_abs_self _).trans (abs_max_sub_max_le_max _ _ _ _)

theorem _root_.lipschitz_with_min : LipschitzWith 1 fun p : ℝ × ℝ => min p.1 p.2 :=
  LipschitzWith.of_le_add fun p₁ p₂ => sub_le_iff_le_add'.1 <| (le_abs_self _).trans (abs_min_sub_min_le_max _ _ _ _)

end Metric

section Emetric

variable {α} [PseudoEmetricSpace α] {f g : α → ℝ} {Kf Kg : ℝ≥0 }

protected theorem max (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g) :
    LipschitzWith (max Kf Kg) fun x => max (f x) (g x) := by
  simpa only [← (· ∘ ·), ← one_mulₓ] using lipschitz_with_max.comp (hf.prod hg)

protected theorem min (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g) :
    LipschitzWith (max Kf Kg) fun x => min (f x) (g x) := by
  simpa only [← (· ∘ ·), ← one_mulₓ] using lipschitz_with_min.comp (hf.prod hg)

theorem max_const (hf : LipschitzWith Kf f) (a : ℝ) : LipschitzWith Kf fun x => max (f x) a := by
  simpa only [← max_eq_leftₓ (zero_le Kf)] using hf.max (LipschitzWith.const a)

theorem const_max (hf : LipschitzWith Kf f) (a : ℝ) : LipschitzWith Kf fun x => max a (f x) := by
  simpa only [← max_commₓ] using hf.max_const a

theorem min_const (hf : LipschitzWith Kf f) (a : ℝ) : LipschitzWith Kf fun x => min (f x) a := by
  simpa only [← max_eq_leftₓ (zero_le Kf)] using hf.min (LipschitzWith.const a)

theorem const_min (hf : LipschitzWith Kf f) (a : ℝ) : LipschitzWith Kf fun x => min a (f x) := by
  simpa only [← min_commₓ] using hf.min_const a

end Emetric

protected theorem proj_Icc {a b : ℝ} (h : a ≤ b) : LipschitzWith 1 (projIcc a b h) :=
  ((LipschitzWith.id.const_min _).const_max _).subtype_mk _

end LipschitzWith

namespace Metric

variable [PseudoMetricSpace α] [PseudoMetricSpace β] {s : Set α} {t : Set β}

theorem Bounded.left_of_prod (h : Bounded (s ×ˢ t)) (ht : t.Nonempty) : Bounded s := by
  simpa only [← fst_image_prod s ht] using (@LipschitzWith.prod_fst α β _ _).bounded_image h

theorem Bounded.right_of_prod (h : Bounded (s ×ˢ t)) (hs : s.Nonempty) : Bounded t := by
  simpa only [← snd_image_prod hs t] using (@LipschitzWith.prod_snd α β _ _).bounded_image h

theorem bounded_prod_of_nonempty (hs : s.Nonempty) (ht : t.Nonempty) : Bounded (s ×ˢ t) ↔ Bounded s ∧ Bounded t :=
  ⟨fun h => ⟨h.left_of_prod ht, h.right_of_prod hs⟩, fun h => h.1.Prod h.2⟩

theorem bounded_prod : Bounded (s ×ˢ t) ↔ s = ∅ ∨ t = ∅ ∨ Bounded s ∧ Bounded t := by
  rcases s.eq_empty_or_nonempty with (rfl | hs)
  · simp
    
  rcases t.eq_empty_or_nonempty with (rfl | ht)
  · simp
    
  simp only [← bounded_prod_of_nonempty hs ht, ← hs.ne_empty, ← ht.ne_empty, ← false_orₓ]

end Metric

namespace LipschitzOnWith

section Emetric

variable [PseudoEmetricSpace α] [PseudoEmetricSpace β] [PseudoEmetricSpace γ]

variable {K : ℝ≥0 } {s : Set α} {f : α → β}

protected theorem uniform_continuous_on (hf : LipschitzOnWith K f s) : UniformContinuousOn f s :=
  uniform_continuous_on_iff_restrict.mpr (lipschitz_on_with_iff_restrict.mp hf).UniformContinuous

protected theorem continuous_on (hf : LipschitzOnWith K f s) : ContinuousOn f s :=
  hf.UniformContinuousOn.ContinuousOn

theorem edist_lt_of_edist_lt_div (hf : LipschitzOnWith K f s) {x y : α} (hx : x ∈ s) (hy : y ∈ s) {d : ℝ≥0∞}
    (hd : edist x y < d / K) : edist (f x) (f y) < d :=
  (lipschitz_on_with_iff_restrict.mp hf).edist_lt_of_edist_lt_div <| show edist (⟨x, hx⟩ : s) ⟨y, hy⟩ < d / K from hd

end Emetric

section Metric

variable [PseudoMetricSpace α] [PseudoMetricSpace β] [PseudoMetricSpace γ]

variable {K : ℝ≥0 } {s : Set α} {f : α → β}

protected theorem of_dist_le' {K : ℝ} (h : ∀, ∀ x ∈ s, ∀, ∀ y ∈ s, ∀, dist (f x) (f y) ≤ K * dist x y) :
    LipschitzOnWith (Real.toNnreal K) f s :=
  of_dist_le_mul fun x hx y hy =>
    le_transₓ (h x hx y hy) <| mul_le_mul_of_nonneg_right (Real.le_coe_to_nnreal K) dist_nonneg

protected theorem mk_one (h : ∀, ∀ x ∈ s, ∀, ∀ y ∈ s, ∀, dist (f x) (f y) ≤ dist x y) : LipschitzOnWith 1 f s :=
  of_dist_le_mul <| by
    simpa only [← Nnreal.coe_one, ← one_mulₓ] using h

/-- For functions to `ℝ`, it suffices to prove `f x ≤ f y + K * dist x y`; this version
doesn't assume `0≤K`. -/
protected theorem of_le_add_mul' {f : α → ℝ} (K : ℝ) (h : ∀, ∀ x ∈ s, ∀, ∀ y ∈ s, ∀, f x ≤ f y + K * dist x y) :
    LipschitzOnWith (Real.toNnreal K) f s :=
  have I : ∀, ∀ x ∈ s, ∀, ∀ y ∈ s, ∀, f x - f y ≤ K * dist x y := fun x hx y hy => sub_le_iff_le_add'.2 (h x hx y hy)
  LipschitzOnWith.of_dist_le' fun x hx y hy => abs_sub_le_iff.2 ⟨I x hx y hy, dist_comm y x ▸ I y hy x hx⟩

/-- For functions to `ℝ`, it suffices to prove `f x ≤ f y + K * dist x y`; this version
assumes `0≤K`. -/
protected theorem of_le_add_mul {f : α → ℝ} (K : ℝ≥0 ) (h : ∀, ∀ x ∈ s, ∀, ∀ y ∈ s, ∀, f x ≤ f y + K * dist x y) :
    LipschitzOnWith K f s := by
  simpa only [← Real.to_nnreal_coe] using LipschitzOnWith.of_le_add_mul' K h

protected theorem of_le_add {f : α → ℝ} (h : ∀, ∀ x ∈ s, ∀, ∀ y ∈ s, ∀, f x ≤ f y + dist x y) : LipschitzOnWith 1 f s :=
  LipschitzOnWith.of_le_add_mul 1 <| by
    simpa only [← Nnreal.coe_one, ← one_mulₓ]

protected theorem le_add_mul {f : α → ℝ} {K : ℝ≥0 } (h : LipschitzOnWith K f s) {x : α} (hx : x ∈ s) {y : α}
    (hy : y ∈ s) : f x ≤ f y + K * dist x y :=
  sub_le_iff_le_add'.1 <| le_transₓ (le_abs_self _) <| h.dist_le_mul x hx y hy

protected theorem iff_le_add_mul {f : α → ℝ} {K : ℝ≥0 } :
    LipschitzOnWith K f s ↔ ∀, ∀ x ∈ s, ∀, ∀ y ∈ s, ∀, f x ≤ f y + K * dist x y :=
  ⟨LipschitzOnWith.le_add_mul, LipschitzOnWith.of_le_add_mul K⟩

end Metric

end LipschitzOnWith

/-- Consider a function `f : α × β → γ`. Suppose that it is continuous on each “vertical fiber”
`{a} × t`, `a ∈ s`, and is Lipschitz continuous on each “horizontal fiber” `s × {b}`, `b ∈ t`
with the same Lipschitz constant `K`. Then it is continuous on `s × t`.

The actual statement uses (Lipschitz) continuity of `λ y, f (a, y)` and `λ x, f (x, b)` instead
of continuity of `f` on subsets of the product space. -/
theorem continuous_on_prod_of_continuous_on_lipschitz_on [PseudoEmetricSpace α] [TopologicalSpace β]
    [PseudoEmetricSpace γ] (f : α × β → γ) {s : Set α} {t : Set β} (K : ℝ≥0 )
    (ha : ∀, ∀ a ∈ s, ∀, ContinuousOn (fun y => f (a, y)) t)
    (hb : ∀, ∀ b ∈ t, ∀, LipschitzOnWith K (fun x => f (x, b)) s) : ContinuousOn f (s ×ˢ t) := by
  rintro ⟨x, y⟩ ⟨hx : x ∈ s, hy : y ∈ t⟩
  refine' Emetric.tendsto_nhds.2 fun ε (ε0 : 0 < ε) => _
  replace ε0 : 0 < ε / 2 := Ennreal.half_pos (ne_of_gtₓ ε0)
  have εK : 0 < ε / 2 / K := Ennreal.div_pos_iff.2 ⟨ε0.ne', Ennreal.coe_ne_top⟩
  have A : s ∩ Emetric.Ball x (ε / 2 / K) ∈ 𝓝[s] x := inter_mem_nhds_within _ (Emetric.ball_mem_nhds _ εK)
  have B : { b : β | b ∈ t ∧ edist (f (x, b)) (f (x, y)) < ε / 2 } ∈ 𝓝[t] y :=
    inter_mem self_mem_nhds_within (ha x hx y hy (Emetric.ball_mem_nhds _ ε0))
  filter_upwards [nhds_within_prod A B]
  rintro ⟨a, b⟩ ⟨⟨has : a ∈ s, hax : edist a x < ε / 2 / K⟩, hbt : b ∈ t, hby : edist (f (x, b)) (f (x, y)) < ε / 2⟩
  calc edist (f (a, b)) (f (x, y)) ≤ edist (f (a, b)) (f (x, b)) + edist (f (x, b)) (f (x, y)) :=
      edist_triangle _ _ _ _ < ε / 2 + ε / 2 :=
      Ennreal.add_lt_add ((hb _ hbt).edist_lt_of_edist_lt_div has hx hax) hby _ = ε := Ennreal.add_halves ε

/-- Consider a function `f : α × β → γ`. Suppose that it is continuous on each “vertical section”
`{a} × univ`, `a : α`, and is Lipschitz continuous on each “horizontal section”
`univ × {b}`, `b : β` with the same Lipschitz constant `K`. Then it is continuous.

The actual statement uses (Lipschitz) continuity of `λ y, f (a, y)` and `λ x, f (x, b)` instead
of continuity of `f` on subsets of the product space. -/
theorem continuous_prod_of_continuous_lipschitz [PseudoEmetricSpace α] [TopologicalSpace β] [PseudoEmetricSpace γ]
    (f : α × β → γ) (K : ℝ≥0 ) (ha : ∀ a, Continuous fun y => f (a, y)) (hb : ∀ b, LipschitzWith K fun x => f (x, b)) :
    Continuous f := by
  simp only [← continuous_iff_continuous_on_univ, univ_prod_univ, lipschitz_on_univ] at *
  exact continuous_on_prod_of_continuous_on_lipschitz_on f K (fun a _ => ha a) fun b _ => hb b

open Metric

/-- If a function is locally Lipschitz around a point, then it is continuous at this point. -/
theorem continuous_at_of_locally_lipschitz [PseudoMetricSpace α] [PseudoMetricSpace β] {f : α → β} {x : α} {r : ℝ}
    (hr : 0 < r) (K : ℝ) (h : ∀ y, dist y x < r → dist (f y) (f x) ≤ K * dist y x) : ContinuousAt f x := by
  -- We use `h` to squeeze `dist (f y) (f x)` between `0` and `K * dist y x`
  refine'
    tendsto_iff_dist_tendsto_zero.2
      (squeeze_zero' (eventually_of_forall fun _ => dist_nonneg) (mem_of_superset (ball_mem_nhds _ hr) h) _)
  -- Then show that `K * dist y x` tends to zero as `y → x`
  refine' (continuous_const.mul (continuous_id.dist continuous_const)).tendsto' _ _ _
  simp

/-- A function `f : α → ℝ` which is `K`-Lipschitz on a subset `s` admits a `K`-Lipschitz extension
to the whole space. -/
theorem LipschitzOnWith.extend_real [PseudoMetricSpace α] {f : α → ℝ} {s : Set α} {K : ℝ≥0 }
    (hf : LipschitzOnWith K f s) : ∃ g : α → ℝ, LipschitzWith K g ∧ EqOn f g s := by
  /- An extension is given by `g y = Inf {f x + K * dist y x | x ∈ s}`. Taking `x = y`, one has
    `g y ≤ f y` for `y ∈ s`, and the other inequality holds because `f` is `K`-Lipschitz, so that it
    can not counterbalance the growth of `K * dist y x`. One readily checks from the formula that the
    extended function is also `K`-Lipschitz. -/
  rcases eq_empty_or_nonempty s with (rfl | hs)
  · exact ⟨fun x => 0, (LipschitzWith.const _).weaken (zero_le _), eq_on_empty _ _⟩
    
  have : Nonempty s := by
    simp only [← hs, ← nonempty_coe_sort]
  let g := fun y : α => infi fun x : s => f x + K * dist y x
  have B : ∀ y : α, BddBelow (range fun x : s => f x + K * dist y x) := by
    intro y
    rcases hs with ⟨z, hz⟩
    refine' ⟨f z - K * dist y z, _⟩
    rintro w ⟨t, rfl⟩
    dsimp'
    rw [sub_le_iff_le_add, add_assocₓ, ← mul_addₓ, add_commₓ (dist y t)]
    calc f z ≤ f t + K * dist z t := hf.le_add_mul hz t.2_ ≤ f t + K * (dist y z + dist y t) :=
        add_le_add_left (mul_le_mul_of_nonneg_left (dist_triangle_left _ _ _) K.2) _
  have E : eq_on f g s := by
    intro x hx
    refine' le_antisymmₓ (le_cinfi fun y => hf.le_add_mul hx y.2) _
    simpa only [← add_zeroₓ, ← Subtype.coe_mk, ← mul_zero, ← dist_self] using cinfi_le (B x) ⟨x, hx⟩
  refine' ⟨g, LipschitzWith.of_le_add_mul K fun x y => _, E⟩
  rw [← sub_le_iff_le_add]
  refine' le_cinfi fun z => _
  rw [sub_le_iff_le_add]
  calc g x ≤ f z + K * dist x z := cinfi_le (B x) _ _ ≤ f z + K * dist y z + K * dist x y := by
      rw [add_assocₓ, ← mul_addₓ, add_commₓ (dist y z)]
      exact add_le_add_left (mul_le_mul_of_nonneg_left (dist_triangle _ _ _) K.2) _

/-- A function `f : α → (ι → ℝ)` which is `K`-Lipschitz on a subset `s` admits a `K`-Lipschitz
extension to the whole space.
TODO: state the same result (with the same proof) for the space `ℓ^∞ (ι, ℝ)` over a possibly
infinite type `ι`. -/
theorem LipschitzOnWith.extend_pi [PseudoMetricSpace α] [Fintype ι] {f : α → ι → ℝ} {s : Set α} {K : ℝ≥0 }
    (hf : LipschitzOnWith K f s) : ∃ g : α → ι → ℝ, LipschitzWith K g ∧ EqOn f g s := by
  have : ∀ i, ∃ g : α → ℝ, LipschitzWith K g ∧ eq_on (fun x => f x i) g s := by
    intro i
    have : LipschitzOnWith K (fun x : α => f x i) s := by
      apply LipschitzOnWith.of_dist_le_mul fun x hx y hy => _
      exact (dist_le_pi_dist _ _ i).trans (hf.dist_le_mul x hx y hy)
    exact this.extend_real
  choose g hg using this
  refine' ⟨fun x i => g i x, LipschitzWith.of_dist_le_mul fun x y => _, _⟩
  · exact (dist_pi_le_iff (mul_nonneg K.2 dist_nonneg)).2 fun i => (hg i).1.dist_le_mul x y
    
  · intro x hx
    ext1 i
    exact (hg i).2 hx
    

