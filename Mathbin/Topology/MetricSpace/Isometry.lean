/-
Copyright (c) 2018 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Isometries of emetric and metric spaces
Authors: Sébastien Gouëzel
-/
import Mathbin.Topology.MetricSpace.Antilipschitz

/-!
# Isometries

We define isometries, i.e., maps between emetric spaces that preserve
the edistance (on metric spaces, these are exactly the maps that preserve distances),
and prove their basic properties. We also introduce isometric bijections.

Since a lot of elementary properties don't require `eq_of_dist_eq_zero` we start setting up the
theory for `pseudo_metric_space` and we specialize to `metric_space` when needed.
-/


noncomputable section

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}

open Function Set

open TopologicalSpace Ennreal

/-- An isometry (also known as isometric embedding) is a map preserving the edistance
between pseudoemetric spaces, or equivalently the distance between pseudometric space.  -/
def Isometry [PseudoEmetricSpace α] [PseudoEmetricSpace β] (f : α → β) : Prop :=
  ∀ x1 x2 : α, edist (f x1) (f x2) = edist x1 x2

/-- On pseudometric spaces, a map is an isometry if and only if it preserves distances. -/
theorem isometry_emetric_iff_metric [PseudoMetricSpace α] [PseudoMetricSpace β] {f : α → β} :
    Isometry f ↔ ∀ x y, dist (f x) (f y) = dist x y :=
  ⟨fun H x y => by
    simp [← dist_edist, ← H x y], fun H x y => by
    simp [← edist_dist, ← H x y]⟩

/-- An isometry preserves edistances. -/
theorem Isometry.edist_eq [PseudoEmetricSpace α] [PseudoEmetricSpace β] {f : α → β} (hf : Isometry f) (x y : α) :
    edist (f x) (f y) = edist x y :=
  hf x y

/-- An isometry preserves distances. -/
theorem Isometry.dist_eq [PseudoMetricSpace α] [PseudoMetricSpace β] {f : α → β} (hf : Isometry f) (x y : α) :
    dist (f x) (f y) = dist x y := by
  rw [dist_edist, dist_edist, hf]

/-- An isometry preserves non-negative distances. -/
theorem Isometry.nndist_eq [PseudoMetricSpace α] [PseudoMetricSpace β] {f : α → β} (hf : Isometry f) (x y : α) :
    nndist (f x) (f y) = nndist x y :=
  Subtype.ext <| hf.dist_eq x y

section PseudoEmetricIsometry

variable [PseudoEmetricSpace α] [PseudoEmetricSpace β] [PseudoEmetricSpace γ]

variable {f : α → β} {x y z : α} {s : Set α}

theorem Isometry.lipschitz (h : Isometry f) : LipschitzWith 1 f :=
  LipschitzWith.of_edist_le fun x y => le_of_eqₓ (h x y)

theorem Isometry.antilipschitz (h : Isometry f) : AntilipschitzWith 1 f := fun x y => by
  simp only [← h x y, ← Ennreal.coe_one, ← one_mulₓ, ← le_reflₓ]

/-- An isometry from an emetric space is injective -/
theorem Isometry.injective {α : Type u} [EmetricSpace α] {f : α → β} (h : Isometry f) : Injective f :=
  h.antilipschitz.Injective

/-- Any map on a subsingleton is an isometry -/
theorem isometry_subsingleton [Subsingleton α] : Isometry f := fun x y => by
  rw [Subsingleton.elimₓ x y] <;> simp

/-- The identity is an isometry -/
theorem isometry_id : Isometry (id : α → α) := fun x y => rfl

/-- The composition of isometries is an isometry -/
theorem Isometry.comp {g : β → γ} {f : α → β} (hg : Isometry g) (hf : Isometry f) : Isometry (g ∘ f) := fun x y =>
  calc
    edist ((g ∘ f) x) ((g ∘ f) y) = edist (f x) (f y) := hg _ _
    _ = edist x y := hf _ _
    

/-- An isometry from a metric space is a uniform inducing map -/
theorem Isometry.uniform_inducing (hf : Isometry f) : UniformInducing f :=
  hf.antilipschitz.UniformInducing hf.lipschitz.UniformContinuous

theorem Isometry.tendsto_nhds_iff {ι : Type _} {f : α → β} {g : ι → α} {a : Filter ι} {b : α} (hf : Isometry f) :
    Filter.Tendsto g a (𝓝 b) ↔ Filter.Tendsto (f ∘ g) a (𝓝 (f b)) :=
  hf.UniformInducing.Inducing.tendsto_nhds_iff

/-- An isometry is continuous. -/
theorem Isometry.continuous (hf : Isometry f) : Continuous f :=
  hf.lipschitz.Continuous

/-- The right inverse of an isometry is an isometry. -/
theorem Isometry.right_inv {f : α → β} {g : β → α} (h : Isometry f) (hg : RightInverse g f) : Isometry g := fun x y =>
  by
  rw [← h, hg _, hg _]

/-- Isometries preserve the diameter in pseudoemetric spaces. -/
theorem Isometry.ediam_image (hf : Isometry f) (s : Set α) : Emetric.diam (f '' s) = Emetric.diam s :=
  eq_of_forall_ge_iff fun d => by
    simp only [← Emetric.diam_le_iff, ← ball_image_iff, ← hf.edist_eq]

theorem Isometry.ediam_range (hf : Isometry f) : Emetric.diam (Range f) = Emetric.diam (Univ : Set α) := by
  rw [← image_univ]
  exact hf.ediam_image univ

theorem Isometry.maps_to_emetric_ball (hf : Isometry f) (x : α) (r : ℝ≥0∞) :
    MapsTo f (Emetric.Ball x r) (Emetric.Ball (f x) r) := fun y hy => by
  rwa [Emetric.mem_ball, hf]

theorem Isometry.maps_to_emetric_closed_ball (hf : Isometry f) (x : α) (r : ℝ≥0∞) :
    MapsTo f (Emetric.ClosedBall x r) (Emetric.ClosedBall (f x) r) := fun y hy => by
  rwa [Emetric.mem_closed_ball, hf]

/-- The injection from a subtype is an isometry -/
theorem isometry_subtype_coe {s : Set α} : Isometry (coe : s → α) := fun x y => rfl

theorem Isometry.comp_continuous_on_iff {γ} [TopologicalSpace γ] (hf : Isometry f) {g : γ → α} {s : Set γ} :
    ContinuousOn (f ∘ g) s ↔ ContinuousOn g s :=
  hf.UniformInducing.Inducing.continuous_on_iff.symm

theorem Isometry.comp_continuous_iff {γ} [TopologicalSpace γ] (hf : Isometry f) {g : γ → α} :
    Continuous (f ∘ g) ↔ Continuous g :=
  hf.UniformInducing.Inducing.continuous_iff.symm

end PseudoEmetricIsometry

--section
section EmetricIsometry

variable [EmetricSpace α]

/-- An isometry from a metric space is a uniform embedding -/
theorem Isometry.uniform_embedding [PseudoEmetricSpace β] {f : α → β} (hf : Isometry f) : UniformEmbedding f :=
  hf.antilipschitz.UniformEmbedding hf.lipschitz.UniformContinuous

/-- An isometry from a metric space is an embedding -/
theorem Isometry.embedding [PseudoEmetricSpace β] {f : α → β} (hf : Isometry f) : Embedding f :=
  hf.UniformEmbedding.Embedding

/-- An isometry from a complete emetric space is a closed embedding -/
theorem Isometry.closed_embedding [CompleteSpace α] [EmetricSpace β] {f : α → β} (hf : Isometry f) :
    ClosedEmbedding f :=
  hf.antilipschitz.ClosedEmbedding hf.lipschitz.UniformContinuous

end EmetricIsometry

--section
namespace Isometry

variable [PseudoMetricSpace α] [PseudoMetricSpace β] {f : α → β}

/-- An isometry preserves the diameter in pseudometric spaces. -/
theorem diam_image (hf : Isometry f) (s : Set α) : Metric.diam (f '' s) = Metric.diam s := by
  rw [Metric.diam, Metric.diam, hf.ediam_image]

theorem diam_range (hf : Isometry f) : Metric.diam (Range f) = Metric.diam (Univ : Set α) := by
  rw [← image_univ]
  exact hf.diam_image univ

theorem maps_to_ball (hf : Isometry f) (x : α) (r : ℝ) : MapsTo f (Metric.Ball x r) (Metric.Ball (f x) r) := fun y hy =>
  by
  rwa [Metric.mem_ball, hf.dist_eq]

theorem maps_to_sphere (hf : Isometry f) (x : α) (r : ℝ) : MapsTo f (Metric.Sphere x r) (Metric.Sphere (f x) r) :=
  fun y hy => by
  rwa [Metric.mem_sphere, hf.dist_eq]

theorem maps_to_closed_ball (hf : Isometry f) (x : α) (r : ℝ) :
    MapsTo f (Metric.ClosedBall x r) (Metric.ClosedBall (f x) r) := fun y hy => by
  rwa [Metric.mem_closed_ball, hf.dist_eq]

end Isometry

/-- A uniform embedding from a uniform space to a metric space is an isometry with respect to the
induced metric space structure on the source space. -/
theorem UniformEmbedding.to_isometry {α β} [UniformSpace α] [MetricSpace β] {f : α → β} (h : UniformEmbedding f) :
    @Isometry α β
      (@PseudoMetricSpace.toPseudoEmetricSpace α (@MetricSpace.toPseudoMetricSpace α (h.comapMetricSpace f)))
      (by
        infer_instance)
      f :=
  by
  apply isometry_emetric_iff_metric.2
  intro x y
  rfl

/-- An embedding from a topological space to a metric space is an isometry with respect to the
induced metric space structure on the source space. -/
theorem Embedding.to_isometry {α β} [TopologicalSpace α] [MetricSpace β] {f : α → β} (h : Embedding f) :
    @Isometry α β
      (@PseudoMetricSpace.toPseudoEmetricSpace α (@MetricSpace.toPseudoMetricSpace α (h.comapMetricSpace f)))
      (by
        infer_instance)
      f :=
  by
  apply isometry_emetric_iff_metric.2
  intro x y
  rfl

/-- `α` and `β` are isometric if there is an isometric bijection between them. -/
-- such a bijection need not exist
@[nolint has_inhabited_instance]
structure Isometric (α : Type _) (β : Type _) [PseudoEmetricSpace α] [PseudoEmetricSpace β] extends α ≃ β where
  isometry_to_fun : Isometry to_fun

-- mathport name: «expr ≃ᵢ »
infixl:25 " ≃ᵢ " => Isometric

namespace Isometric

section PseudoEmetricSpace

variable [PseudoEmetricSpace α] [PseudoEmetricSpace β] [PseudoEmetricSpace γ]

instance : CoeFun (α ≃ᵢ β) fun _ => α → β :=
  ⟨fun e => e.toEquiv⟩

theorem coe_eq_to_equiv (h : α ≃ᵢ β) (a : α) : h a = h.toEquiv a :=
  rfl

@[simp]
theorem coe_to_equiv (h : α ≃ᵢ β) : ⇑h.toEquiv = h :=
  rfl

protected theorem isometry (h : α ≃ᵢ β) : Isometry h :=
  h.isometry_to_fun

protected theorem bijective (h : α ≃ᵢ β) : Bijective h :=
  h.toEquiv.Bijective

protected theorem injective (h : α ≃ᵢ β) : Injective h :=
  h.toEquiv.Injective

protected theorem surjective (h : α ≃ᵢ β) : Surjective h :=
  h.toEquiv.Surjective

protected theorem edist_eq (h : α ≃ᵢ β) (x y : α) : edist (h x) (h y) = edist x y :=
  h.Isometry.edist_eq x y

protected theorem dist_eq {α β : Type _} [PseudoMetricSpace α] [PseudoMetricSpace β] (h : α ≃ᵢ β) (x y : α) :
    dist (h x) (h y) = dist x y :=
  h.Isometry.dist_eq x y

protected theorem nndist_eq {α β : Type _} [PseudoMetricSpace α] [PseudoMetricSpace β] (h : α ≃ᵢ β) (x y : α) :
    nndist (h x) (h y) = nndist x y :=
  h.Isometry.nndist_eq x y

protected theorem continuous (h : α ≃ᵢ β) : Continuous h :=
  h.Isometry.Continuous

@[simp]
theorem ediam_image (h : α ≃ᵢ β) (s : Set α) : Emetric.diam (h '' s) = Emetric.diam s :=
  h.Isometry.ediam_image s

theorem to_equiv_inj : ∀ ⦃h₁ h₂ : α ≃ᵢ β⦄, h₁.toEquiv = h₂.toEquiv → h₁ = h₂
  | ⟨e₁, h₁⟩, ⟨e₂, h₂⟩, H => by
    dsimp'  at H
    subst e₁

@[ext]
theorem ext ⦃h₁ h₂ : α ≃ᵢ β⦄ (H : ∀ x, h₁ x = h₂ x) : h₁ = h₂ :=
  to_equiv_inj <| Equivₓ.ext H

/-- Alternative constructor for isometric bijections,
taking as input an isometry, and a right inverse. -/
def mk' {α : Type u} [EmetricSpace α] (f : α → β) (g : β → α) (hfg : ∀ x, f (g x) = x) (hf : Isometry f) : α ≃ᵢ β where
  toFun := f
  invFun := g
  left_inv := fun x => hf.Injective <| hfg _
  right_inv := hfg
  isometry_to_fun := hf

/-- The identity isometry of a space. -/
protected def refl (α : Type _) [PseudoEmetricSpace α] : α ≃ᵢ α :=
  { Equivₓ.refl α with isometry_to_fun := isometry_id }

/-- The composition of two isometric isomorphisms, as an isometric isomorphism. -/
protected def trans (h₁ : α ≃ᵢ β) (h₂ : β ≃ᵢ γ) : α ≃ᵢ γ :=
  { Equivₓ.trans h₁.toEquiv h₂.toEquiv with isometry_to_fun := h₂.isometry_to_fun.comp h₁.isometry_to_fun }

@[simp]
theorem trans_apply (h₁ : α ≃ᵢ β) (h₂ : β ≃ᵢ γ) (x : α) : h₁.trans h₂ x = h₂ (h₁ x) :=
  rfl

/-- The inverse of an isometric isomorphism, as an isometric isomorphism. -/
protected def symm (h : α ≃ᵢ β) : β ≃ᵢ α where
  isometry_to_fun := h.Isometry.right_inv h.right_inv
  toEquiv := h.toEquiv.symm

/-- See Note [custom simps projection]. We need to specify this projection explicitly in this case,
  because it is a composition of multiple projections. -/
def Simps.apply (h : α ≃ᵢ β) : α → β :=
  h

/-- See Note [custom simps projection] -/
def Simps.symmApply (h : α ≃ᵢ β) : β → α :=
  h.symm

initialize_simps_projections Isometric (to_equiv_to_fun → apply, to_equiv_inv_fun → symmApply)

@[simp]
theorem symm_symm (h : α ≃ᵢ β) : h.symm.symm = h :=
  to_equiv_inj h.toEquiv.symm_symm

@[simp]
theorem apply_symm_apply (h : α ≃ᵢ β) (y : β) : h (h.symm y) = y :=
  h.toEquiv.apply_symm_apply y

@[simp]
theorem symm_apply_apply (h : α ≃ᵢ β) (x : α) : h.symm (h x) = x :=
  h.toEquiv.symm_apply_apply x

theorem symm_apply_eq (h : α ≃ᵢ β) {x : α} {y : β} : h.symm y = x ↔ y = h x :=
  h.toEquiv.symm_apply_eq

theorem eq_symm_apply (h : α ≃ᵢ β) {x : α} {y : β} : x = h.symm y ↔ h x = y :=
  h.toEquiv.eq_symm_apply

theorem symm_comp_self (h : α ≃ᵢ β) : ⇑h.symm ∘ ⇑h = id :=
  funext fun a => h.toEquiv.left_inv a

theorem self_comp_symm (h : α ≃ᵢ β) : ⇑h ∘ ⇑h.symm = id :=
  funext fun a => h.toEquiv.right_inv a

@[simp]
theorem range_eq_univ (h : α ≃ᵢ β) : Range h = univ :=
  h.toEquiv.range_eq_univ

theorem image_symm (h : α ≃ᵢ β) : Image h.symm = Preimage h :=
  image_eq_preimage_of_inverse h.symm.toEquiv.left_inv h.symm.toEquiv.right_inv

theorem preimage_symm (h : α ≃ᵢ β) : Preimage h.symm = Image h :=
  (image_eq_preimage_of_inverse h.toEquiv.left_inv h.toEquiv.right_inv).symm

@[simp]
theorem symm_trans_apply (h₁ : α ≃ᵢ β) (h₂ : β ≃ᵢ γ) (x : γ) : (h₁.trans h₂).symm x = h₁.symm (h₂.symm x) :=
  rfl

theorem ediam_univ (h : α ≃ᵢ β) : Emetric.diam (Univ : Set α) = Emetric.diam (Univ : Set β) := by
  rw [← h.range_eq_univ, h.isometry.ediam_range]

@[simp]
theorem ediam_preimage (h : α ≃ᵢ β) (s : Set β) : Emetric.diam (h ⁻¹' s) = Emetric.diam s := by
  rw [← image_symm, ediam_image]

@[simp]
theorem preimage_emetric_ball (h : α ≃ᵢ β) (x : β) (r : ℝ≥0∞) : h ⁻¹' Emetric.Ball x r = Emetric.Ball (h.symm x) r := by
  ext y
  simp [h.edist_eq]

@[simp]
theorem preimage_emetric_closed_ball (h : α ≃ᵢ β) (x : β) (r : ℝ≥0∞) :
    h ⁻¹' Emetric.ClosedBall x r = Emetric.ClosedBall (h.symm x) r := by
  ext y
  simp [h.edist_eq]

@[simp]
theorem image_emetric_ball (h : α ≃ᵢ β) (x : α) (r : ℝ≥0∞) : h '' Emetric.Ball x r = Emetric.Ball (h x) r := by
  rw [← h.preimage_symm, h.symm.preimage_emetric_ball, symm_symm]

@[simp]
theorem image_emetric_closed_ball (h : α ≃ᵢ β) (x : α) (r : ℝ≥0∞) :
    h '' Emetric.ClosedBall x r = Emetric.ClosedBall (h x) r := by
  rw [← h.preimage_symm, h.symm.preimage_emetric_closed_ball, symm_symm]

/-- The (bundled) homeomorphism associated to an isometric isomorphism. -/
@[simps toEquiv]
protected def toHomeomorph (h : α ≃ᵢ β) : α ≃ₜ β where
  continuous_to_fun := h.Continuous
  continuous_inv_fun := h.symm.Continuous
  toEquiv := h.toEquiv

@[simp]
theorem coe_to_homeomorph (h : α ≃ᵢ β) : ⇑h.toHomeomorph = h :=
  rfl

@[simp]
theorem coe_to_homeomorph_symm (h : α ≃ᵢ β) : ⇑h.toHomeomorph.symm = h.symm :=
  rfl

@[simp]
theorem comp_continuous_on_iff {γ} [TopologicalSpace γ] (h : α ≃ᵢ β) {f : γ → α} {s : Set γ} :
    ContinuousOn (h ∘ f) s ↔ ContinuousOn f s :=
  h.toHomeomorph.comp_continuous_on_iff _ _

@[simp]
theorem comp_continuous_iff {γ} [TopologicalSpace γ] (h : α ≃ᵢ β) {f : γ → α} : Continuous (h ∘ f) ↔ Continuous f :=
  h.toHomeomorph.comp_continuous_iff

@[simp]
theorem comp_continuous_iff' {γ} [TopologicalSpace γ] (h : α ≃ᵢ β) {f : β → γ} : Continuous (f ∘ h) ↔ Continuous f :=
  h.toHomeomorph.comp_continuous_iff'

/-- The group of isometries. -/
instance : Groupₓ (α ≃ᵢ α) where
  one := Isometric.refl _
  mul := fun e₁ e₂ => e₂.trans e₁
  inv := Isometric.symm
  mul_assoc := fun e₁ e₂ e₃ => rfl
  one_mul := fun e => ext fun _ => rfl
  mul_one := fun e => ext fun _ => rfl
  mul_left_inv := fun e => ext e.symm_apply_apply

@[simp]
theorem coe_one : ⇑(1 : α ≃ᵢ α) = id :=
  rfl

@[simp]
theorem coe_mul (e₁ e₂ : α ≃ᵢ α) : ⇑(e₁ * e₂) = e₁ ∘ e₂ :=
  rfl

theorem mul_apply (e₁ e₂ : α ≃ᵢ α) (x : α) : (e₁ * e₂) x = e₁ (e₂ x) :=
  rfl

@[simp]
theorem inv_apply_self (e : α ≃ᵢ α) (x : α) : e⁻¹ (e x) = x :=
  e.symm_apply_apply x

@[simp]
theorem apply_inv_self (e : α ≃ᵢ α) (x : α) : e (e⁻¹ x) = x :=
  e.apply_symm_apply x

protected theorem complete_space [CompleteSpace β] (e : α ≃ᵢ β) : CompleteSpace α :=
  complete_space_of_is_complete_univ <|
    is_complete_of_complete_image e.Isometry.UniformInducing <| by
      rwa [Set.image_univ, Isometric.range_eq_univ, ← complete_space_iff_is_complete_univ]

theorem complete_space_iff (e : α ≃ᵢ β) : CompleteSpace α ↔ CompleteSpace β := by
  constructor <;> intro H
  exacts[e.symm.complete_space, e.complete_space]

end PseudoEmetricSpace

section PseudoMetricSpace

variable [PseudoMetricSpace α] [PseudoMetricSpace β] (h : α ≃ᵢ β)

@[simp]
theorem diam_image (s : Set α) : Metric.diam (h '' s) = Metric.diam s :=
  h.Isometry.diam_image s

@[simp]
theorem diam_preimage (s : Set β) : Metric.diam (h ⁻¹' s) = Metric.diam s := by
  rw [← image_symm, diam_image]

theorem diam_univ : Metric.diam (Univ : Set α) = Metric.diam (Univ : Set β) :=
  congr_arg Ennreal.toReal h.ediam_univ

@[simp]
theorem preimage_ball (h : α ≃ᵢ β) (x : β) (r : ℝ) : h ⁻¹' Metric.Ball x r = Metric.Ball (h.symm x) r := by
  ext y
  simp [h.dist_eq]

@[simp]
theorem preimage_sphere (h : α ≃ᵢ β) (x : β) (r : ℝ) : h ⁻¹' Metric.Sphere x r = Metric.Sphere (h.symm x) r := by
  ext y
  simp [h.dist_eq]

@[simp]
theorem preimage_closed_ball (h : α ≃ᵢ β) (x : β) (r : ℝ) :
    h ⁻¹' Metric.ClosedBall x r = Metric.ClosedBall (h.symm x) r := by
  ext y
  simp [h.dist_eq]

@[simp]
theorem image_ball (h : α ≃ᵢ β) (x : α) (r : ℝ) : h '' Metric.Ball x r = Metric.Ball (h x) r := by
  rw [← h.preimage_symm, h.symm.preimage_ball, symm_symm]

@[simp]
theorem image_sphere (h : α ≃ᵢ β) (x : α) (r : ℝ) : h '' Metric.Sphere x r = Metric.Sphere (h x) r := by
  rw [← h.preimage_symm, h.symm.preimage_sphere, symm_symm]

@[simp]
theorem image_closed_ball (h : α ≃ᵢ β) (x : α) (r : ℝ) : h '' Metric.ClosedBall x r = Metric.ClosedBall (h x) r := by
  rw [← h.preimage_symm, h.symm.preimage_closed_ball, symm_symm]

end PseudoMetricSpace

end Isometric

/-- An isometry induces an isometric isomorphism between the source space and the
range of the isometry. -/
@[simps (config := { simpRhs := true }) toEquiv apply]
def Isometry.isometricOnRange [EmetricSpace α] [PseudoEmetricSpace β] {f : α → β} (h : Isometry f) : α ≃ᵢ Range f where
  isometry_to_fun := fun x y => by
    simpa [← Subtype.edist_eq] using h x y
  toEquiv := Equivₓ.ofInjective f h.Injective

