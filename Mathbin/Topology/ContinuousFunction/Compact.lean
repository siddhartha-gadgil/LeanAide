/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.Topology.ContinuousFunction.Bounded
import Mathbin.Topology.UniformSpace.CompactSeparated
import Mathbin.Topology.CompactOpen
import Mathbin.Topology.Sets.Compacts

/-!
# Continuous functions on a compact space

Continuous functions `C(α, β)` from a compact space `α` to a metric space `β`
are automatically bounded, and so acquire various structures inherited from `α →ᵇ β`.

This file transfers these structures, and restates some lemmas
characterising these structures.

If you need a lemma which is proved about `α →ᵇ β` but not for `C(α, β)` when `α` is compact,
you should restate it here. You can also use
`bounded_continuous_function.equiv_continuous_map_of_compact` to move functions back and forth.

-/


noncomputable section

open TopologicalSpace Classical Nnreal BoundedContinuousFunction BigOperators

open Set Filter Metric

open BoundedContinuousFunction

namespace ContinuousMap

variable {α β E : Type _} [TopologicalSpace α] [CompactSpace α] [MetricSpace β] [NormedGroup E]

section

variable (α β)

/-- When `α` is compact, the bounded continuous maps `α →ᵇ β` are
equivalent to `C(α, β)`.
-/
@[simps (config := { fullyApplied := false })]
def equivBoundedOfCompact : C(α, β) ≃ (α →ᵇ β) :=
  ⟨mkOfCompact, BoundedContinuousFunction.toContinuousMap, fun f => by
    ext
    rfl, fun f => by
    ext
    rfl⟩

theorem uniform_inducing_equiv_bounded_of_compact : UniformInducing (equivBoundedOfCompact α β) :=
  UniformInducing.mk'
    (by
      simp only [← has_basis_compact_convergence_uniformity.mem_iff, ← uniformity_basis_dist_le.mem_iff]
      exact fun s =>
        ⟨fun ⟨⟨a, b⟩, ⟨ha, ⟨ε, hε, hb⟩⟩, hs⟩ =>
          ⟨{ p | ∀ x, (p.1 x, p.2 x) ∈ b }, ⟨ε, hε, fun _ h x => hb ((dist_le hε.le).mp h x)⟩, fun f g h =>
            hs fun x hx => h x⟩,
          fun ⟨t, ⟨ε, hε, ht⟩, hs⟩ =>
          ⟨⟨Set.Univ, { p | dist p.1 p.2 ≤ ε }⟩, ⟨compact_univ, ⟨ε, hε, fun _ h => h⟩⟩, fun ⟨f, g⟩ h =>
            hs _ _ (ht ((dist_le hε.le).mpr fun x => h x (mem_univ x)))⟩⟩)

theorem uniform_embedding_equiv_bounded_of_compact : UniformEmbedding (equivBoundedOfCompact α β) :=
  { uniform_inducing_equiv_bounded_of_compact α β with inj := (equivBoundedOfCompact α β).Injective }

/-- When `α` is compact, the bounded continuous maps `α →ᵇ 𝕜` are
additively equivalent to `C(α, 𝕜)`.
-/
@[simps (config := { fullyApplied := false }) apply symmApply]
def addEquivBoundedOfCompact [AddMonoidₓ β] [HasLipschitzAdd β] : C(α, β) ≃+ (α →ᵇ β) :=
  ({ toContinuousMapAddHom α β, (equivBoundedOfCompact α β).symm with } : (α →ᵇ β) ≃+ C(α, β)).symm

instance : MetricSpace C(α, β) :=
  (uniform_embedding_equiv_bounded_of_compact α β).comapMetricSpace _

/-- When `α` is compact, and `β` is a metric space, the bounded continuous maps `α →ᵇ β` are
isometric to `C(α, β)`.
-/
@[simps (config := { fullyApplied := false }) toEquiv apply symmApply]
def isometricBoundedOfCompact : C(α, β) ≃ᵢ (α →ᵇ β) where
  isometry_to_fun := fun x y => rfl
  toEquiv := equivBoundedOfCompact α β

end

@[simp]
theorem _root_.bounded_continuous_function.dist_mk_of_compact (f g : C(α, β)) :
    dist (mkOfCompact f) (mkOfCompact g) = dist f g :=
  rfl

@[simp]
theorem _root_.bounded_continuous_function.dist_to_continuous_map (f g : α →ᵇ β) :
    dist f.toContinuousMap g.toContinuousMap = dist f g :=
  rfl

open BoundedContinuousFunction

section

variable {α β} {f g : C(α, β)} {C : ℝ}

/-- The pointwise distance is controlled by the distance between functions, by definition. -/
theorem dist_apply_le_dist (x : α) : dist (f x) (g x) ≤ dist f g := by
  simp only [dist_mk_of_compact, ← dist_coe_le_dist, mk_of_compact_apply]

/-- The distance between two functions is controlled by the supremum of the pointwise distances -/
theorem dist_le (C0 : (0 : ℝ) ≤ C) : dist f g ≤ C ↔ ∀ x : α, dist (f x) (g x) ≤ C := by
  simp only [dist_mk_of_compact, ← dist_le C0, ← mk_of_compact_apply]

theorem dist_le_iff_of_nonempty [Nonempty α] : dist f g ≤ C ↔ ∀ x, dist (f x) (g x) ≤ C := by
  simp only [dist_mk_of_compact, ← dist_le_iff_of_nonempty, ← mk_of_compact_apply]

theorem dist_lt_iff_of_nonempty [Nonempty α] : dist f g < C ↔ ∀ x : α, dist (f x) (g x) < C := by
  simp only [dist_mk_of_compact, ← dist_lt_iff_of_nonempty_compact, ← mk_of_compact_apply]

theorem dist_lt_of_nonempty [Nonempty α] (w : ∀ x : α, dist (f x) (g x) < C) : dist f g < C :=
  dist_lt_iff_of_nonempty.2 w

theorem dist_lt_iff (C0 : (0 : ℝ) < C) : dist f g < C ↔ ∀ x : α, dist (f x) (g x) < C := by
  simp only [dist_mk_of_compact, ← dist_lt_iff_of_compact C0, ← mk_of_compact_apply]

end

instance [CompleteSpace β] : CompleteSpace C(α, β) :=
  (isometricBoundedOfCompact α β).CompleteSpace

/-- See also `continuous_map.continuous_eval'` -/
@[continuity]
theorem continuous_eval : Continuous fun p : C(α, β) × α => p.1 p.2 :=
  continuous_eval.comp ((isometricBoundedOfCompact α β).Continuous.prod_map continuous_id)

/-- See also `continuous_map.continuous_eval_const` -/
@[continuity]
theorem continuous_eval_const (x : α) : Continuous fun f : C(α, β) => f x :=
  continuous_eval.comp (continuous_id.prod_mk continuous_const)

/-- See also `continuous_map.continuous_coe'` -/
theorem continuous_coe : @Continuous C(α, β) (α → β) _ _ coeFn :=
  continuous_pi continuous_eval_const

-- TODO at some point we will need lemmas characterising this norm!
-- At the moment the only way to reason about it is to transfer `f : C(α,E)` back to `α →ᵇ E`.
instance : HasNorm C(α, E) where norm := fun x => dist x 0

@[simp]
theorem _root_.bounded_continuous_function.norm_mk_of_compact (f : C(α, E)) : ∥mkOfCompact f∥ = ∥f∥ :=
  rfl

@[simp]
theorem _root_.bounded_continuous_function.norm_to_continuous_map_eq (f : α →ᵇ E) : ∥f.toContinuousMap∥ = ∥f∥ :=
  rfl

open BoundedContinuousFunction

instance : NormedGroup C(α, E) :=
  { ContinuousMap.metricSpace _ _, ContinuousMap.addCommGroup with
    dist_eq := fun x y => by
      rw [← norm_mk_of_compact, ← dist_mk_of_compact, dist_eq_norm, mk_of_compact_sub],
    dist := dist, norm := norm }

section

variable (f : C(α, E))

-- The corresponding lemmas for `bounded_continuous_function` are stated with `{f}`,
-- and so can not be used in dot notation.
theorem norm_coe_le_norm (x : α) : ∥f x∥ ≤ ∥f∥ :=
  (mkOfCompact f).norm_coe_le_norm x

/-- Distance between the images of any two points is at most twice the norm of the function. -/
theorem dist_le_two_norm (x y : α) : dist (f x) (f y) ≤ 2 * ∥f∥ :=
  (mkOfCompact f).dist_le_two_norm x y

/-- The norm of a function is controlled by the supremum of the pointwise norms -/
theorem norm_le {C : ℝ} (C0 : (0 : ℝ) ≤ C) : ∥f∥ ≤ C ↔ ∀ x : α, ∥f x∥ ≤ C :=
  @BoundedContinuousFunction.norm_le _ _ _ _ (mkOfCompact f) _ C0

theorem norm_le_of_nonempty [Nonempty α] {M : ℝ} : ∥f∥ ≤ M ↔ ∀ x, ∥f x∥ ≤ M :=
  @BoundedContinuousFunction.norm_le_of_nonempty _ _ _ _ _ (mkOfCompact f) _

theorem norm_lt_iff {M : ℝ} (M0 : 0 < M) : ∥f∥ < M ↔ ∀ x, ∥f x∥ < M :=
  @BoundedContinuousFunction.norm_lt_iff_of_compact _ _ _ _ _ (mkOfCompact f) _ M0

theorem norm_lt_iff_of_nonempty [Nonempty α] {M : ℝ} : ∥f∥ < M ↔ ∀ x, ∥f x∥ < M :=
  @BoundedContinuousFunction.norm_lt_iff_of_nonempty_compact _ _ _ _ _ _ (mkOfCompact f) _

theorem apply_le_norm (f : C(α, ℝ)) (x : α) : f x ≤ ∥f∥ :=
  le_transₓ (le_abs.mpr (Or.inl (le_reflₓ (f x)))) (f.norm_coe_le_norm x)

theorem neg_norm_le_apply (f : C(α, ℝ)) (x : α) : -∥f∥ ≤ f x :=
  le_transₓ (neg_le_neg (f.norm_coe_le_norm x)) (neg_le.mp (neg_le_abs_self (f x)))

theorem norm_eq_supr_norm : ∥f∥ = ⨆ x : α, ∥f x∥ :=
  (mkOfCompact f).norm_eq_supr_norm

end

section

variable {R : Type _} [NormedRing R]

instance : NormedRing C(α, R) :=
  { (inferInstance : NormedGroup C(α, R)), ContinuousMap.ring with
    norm_mul := fun f g => norm_mul_le (mkOfCompact f) (mkOfCompact g) }

end

section

variable {𝕜 : Type _} [NormedField 𝕜] [NormedSpace 𝕜 E]

instance : NormedSpace 𝕜 C(α, E) where norm_smul_le := fun c f => le_of_eqₓ (norm_smul c (mkOfCompact f))

section

variable (α 𝕜 E)

/-- When `α` is compact and `𝕜` is a normed field,
the `𝕜`-algebra of bounded continuous maps `α →ᵇ β` is
`𝕜`-linearly isometric to `C(α, β)`.
-/
def linearIsometryBoundedOfCompact : C(α, E) ≃ₗᵢ[𝕜] α →ᵇ E :=
  { addEquivBoundedOfCompact α E with
    map_smul' := fun c f => by
      ext
      simp ,
    norm_map' := fun f => rfl }

end

-- this lemma and the next are the analogues of those autogenerated by `@[simps]` for
-- `equiv_bounded_of_compact`, `add_equiv_bounded_of_compact`
@[simp]
theorem linear_isometry_bounded_of_compact_symm_apply (f : α →ᵇ E) :
    (linearIsometryBoundedOfCompact α E 𝕜).symm f = f.toContinuousMap :=
  rfl

@[simp]
theorem linear_isometry_bounded_of_compact_apply_apply (f : C(α, E)) (a : α) :
    (linearIsometryBoundedOfCompact α E 𝕜 f) a = f a :=
  rfl

@[simp]
theorem linear_isometry_bounded_of_compact_to_isometric :
    (linearIsometryBoundedOfCompact α E 𝕜).toIsometric = isometricBoundedOfCompact α E :=
  rfl

@[simp]
theorem linear_isometry_bounded_of_compact_to_add_equiv :
    (linearIsometryBoundedOfCompact α E 𝕜).toLinearEquiv.toAddEquiv = addEquivBoundedOfCompact α E :=
  rfl

@[simp]
theorem linear_isometry_bounded_of_compact_of_compact_to_equiv :
    (linearIsometryBoundedOfCompact α E 𝕜).toLinearEquiv.toEquiv = equivBoundedOfCompact α E :=
  rfl

end

section

variable {𝕜 : Type _} {γ : Type _} [NormedField 𝕜] [NormedRing γ] [NormedAlgebra 𝕜 γ]

instance : NormedAlgebra 𝕜 C(α, γ) :=
  { ContinuousMap.normedSpace with }

end

end ContinuousMap

namespace ContinuousMap

section UniformContinuity

variable {α β : Type _}

variable [MetricSpace α] [CompactSpace α] [MetricSpace β]

/-!
We now set up some declarations making it convenient to use uniform continuity.
-/


theorem uniform_continuity (f : C(α, β)) (ε : ℝ) (h : 0 < ε) : ∃ δ > 0, ∀ {x y}, dist x y < δ → dist (f x) (f y) < ε :=
  Metric.uniform_continuous_iff.mp (CompactSpace.uniform_continuous_of_continuous f.Continuous) ε h

/-- An arbitrarily chosen modulus of uniform continuity for a given function `f` and `ε > 0`.
-/
-- This definition allows us to separate the choice of some `δ`,
-- and the corresponding use of `dist a b < δ → dist (f a) (f b) < ε`,
-- even across different declarations.
def modulus (f : C(α, β)) (ε : ℝ) (h : 0 < ε) : ℝ :=
  Classical.some (uniform_continuity f ε h)

theorem modulus_pos (f : C(α, β)) {ε : ℝ} {h : 0 < ε} : 0 < f.modulus ε h :=
  (Classical.some_spec (uniform_continuity f ε h)).fst

theorem dist_lt_of_dist_lt_modulus (f : C(α, β)) (ε : ℝ) (h : 0 < ε) {a b : α} (w : dist a b < f.modulus ε h) :
    dist (f a) (f b) < ε :=
  (Classical.some_spec (uniform_continuity f ε h)).snd w

end UniformContinuity

end ContinuousMap

section CompLeft

variable (X : Type _) {𝕜 β γ : Type _} [TopologicalSpace X] [CompactSpace X] [NondiscreteNormedField 𝕜]

variable [NormedGroup β] [NormedSpace 𝕜 β] [NormedGroup γ] [NormedSpace 𝕜 γ]

open ContinuousMap

/-- Postcomposition of continuous functions into a normed module by a continuous linear map is a
continuous linear map.
Transferred version of `continuous_linear_map.comp_left_continuous_bounded`,
upgraded version of `continuous_linear_map.comp_left_continuous`,
similar to `linear_map.comp_left`. -/
protected def ContinuousLinearMap.compLeftContinuousCompact (g : β →L[𝕜] γ) : C(X, β) →L[𝕜] C(X, γ) :=
  (linearIsometryBoundedOfCompact X γ 𝕜).symm.toLinearIsometry.toContinuousLinearMap.comp <|
    (g.compLeftContinuousBounded X).comp <|
      (linearIsometryBoundedOfCompact X β 𝕜).toLinearIsometry.toContinuousLinearMap

@[simp]
theorem ContinuousLinearMap.to_linear_comp_left_continuous_compact (g : β →L[𝕜] γ) :
    (g.compLeftContinuousCompact X : C(X, β) →ₗ[𝕜] C(X, γ)) = g.compLeftContinuous 𝕜 X := by
  ext f
  rfl

@[simp]
theorem ContinuousLinearMap.comp_left_continuous_compact_apply (g : β →L[𝕜] γ) (f : C(X, β)) (x : X) :
    g.compLeftContinuousCompact X f x = g (f x) :=
  rfl

end CompLeft

namespace ContinuousMap

/-!
We now setup variations on `comp_right_* f`, where `f : C(X, Y)`
(that is, precomposition by a continuous map),
as a morphism `C(Y, T) → C(X, T)`, respecting various types of structure.

In particular:
* `comp_right_continuous_map`, the bundled continuous map (for this we need `X Y` compact).
* `comp_right_homeomorph`, when we precompose by a homeomorphism.
* `comp_right_alg_hom`, when `T = R` is a topological ring.
-/


section CompRight

/-- Precomposition by a continuous map is itself a continuous map between spaces of continuous maps.
-/
def compRightContinuousMap {X Y : Type _} (T : Type _) [TopologicalSpace X] [CompactSpace X] [TopologicalSpace Y]
    [CompactSpace Y] [NormedGroup T] (f : C(X, Y)) : C(C(Y, T), C(X, T)) where
  toFun := fun g => g.comp f
  continuous_to_fun := by
    refine' metric.continuous_iff.mpr _
    intro g ε ε_pos
    refine' ⟨ε, ε_pos, fun g' h => _⟩
    rw [ContinuousMap.dist_lt_iff ε_pos] at h⊢
    · exact fun x => h (f x)
      

@[simp]
theorem comp_right_continuous_map_apply {X Y : Type _} (T : Type _) [TopologicalSpace X] [CompactSpace X]
    [TopologicalSpace Y] [CompactSpace Y] [NormedGroup T] (f : C(X, Y)) (g : C(Y, T)) :
    (compRightContinuousMap T f) g = g.comp f :=
  rfl

/-- Precomposition by a homeomorphism is itself a homeomorphism between spaces of continuous maps.
-/
def compRightHomeomorph {X Y : Type _} (T : Type _) [TopologicalSpace X] [CompactSpace X] [TopologicalSpace Y]
    [CompactSpace Y] [NormedGroup T] (f : X ≃ₜ Y) : C(Y, T) ≃ₜ C(X, T) where
  toFun := compRightContinuousMap T f.toContinuousMap
  invFun := compRightContinuousMap T f.symm.toContinuousMap
  left_inv := by
    tidy
  right_inv := by
    tidy

/-- Precomposition of functions into a normed ring by continuous map is an algebra homomorphism.
-/
def compRightAlgHom {X Y : Type _} (R : Type _) [TopologicalSpace X] [TopologicalSpace Y] [NormedCommRing R]
    (f : C(X, Y)) : C(Y, R) →ₐ[R] C(X, R) where
  toFun := fun g => g.comp f
  map_zero' := by
    ext
    simp
  map_add' := fun g₁ g₂ => by
    ext
    simp
  map_one' := by
    ext
    simp
  map_mul' := fun g₁ g₂ => by
    ext
    simp
  commutes' := fun r => by
    ext
    simp

@[simp]
theorem comp_right_alg_hom_apply {X Y : Type _} (R : Type _) [TopologicalSpace X] [TopologicalSpace Y]
    [NormedCommRing R] (f : C(X, Y)) (g : C(Y, R)) : (compRightAlgHom R f) g = g.comp f :=
  rfl

theorem comp_right_alg_hom_continuous {X Y : Type _} (R : Type _) [TopologicalSpace X] [CompactSpace X]
    [TopologicalSpace Y] [CompactSpace Y] [NormedCommRing R] (f : C(X, Y)) : Continuous (compRightAlgHom R f) := by
  change Continuous (comp_right_continuous_map R f)
  continuity

end CompRight

section Weierstrass

open TopologicalSpace

variable {X : Type _} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]

variable {E : Type _} [NormedGroup E] [CompleteSpace E]

theorem summable_of_locally_summable_norm {ι : Type _} {F : ι → C(X, E)}
    (hF : ∀ K : Compacts X, Summable fun i => ∥(F i).restrict K∥) : Summable F := by
  refine' (ContinuousMap.exists_tendsto_compact_open_iff_forall _).2 fun K hK => _
  lift K to compacts X using hK
  have A : ∀ s : Finset ι, restrict (↑K) (∑ i in s, F i) = ∑ i in s, restrict K (F i) := by
    intro s
    ext1 x
    simp
  simpa only [← HasSum, ← A] using summable_of_summable_norm (hF K)

end Weierstrass

/-!
### Star structures

In this section, if `β` is a normed ⋆-group, then so is the space of
continuous functions from `α` to `β`, by using the star operation pointwise.

Furthermore, if `α` is compact and `β` is a C⋆-ring, then `C(α, β)` is a C⋆-ring.  -/


section NormedSpace

variable {α : Type _} {β : Type _}

variable [TopologicalSpace α] [NormedGroup β] [StarAddMonoid β] [NormedStarGroup β]

theorem _root_.bounded_continuous_function.mk_of_compact_star [CompactSpace α] (f : C(α, β)) :
    mkOfCompact (star f) = star (mkOfCompact f) :=
  rfl

instance [CompactSpace α] :
    NormedStarGroup C(α, β) where norm_star := fun f => by
    rw [← BoundedContinuousFunction.norm_mk_of_compact, BoundedContinuousFunction.mk_of_compact_star, norm_star,
      BoundedContinuousFunction.norm_mk_of_compact]

end NormedSpace

section CstarRing

variable {α : Type _} {β : Type _}

variable [TopologicalSpace α] [NormedRing β] [StarRing β]

instance [CompactSpace α] [CstarRing β] :
    CstarRing C(α, β) where norm_star_mul_self := by
    intro f
    refine' le_antisymmₓ _ _
    · rw [← sq, ContinuousMap.norm_le _ (sq_nonneg _)]
      intro x
      simp only [← ContinuousMap.coe_mul, ← coe_star, ← Pi.mul_apply, ← Pi.star_apply, ← CstarRing.norm_star_mul_self,
        sq]
      refine' sq_le_sq' _ _
      · linarith [norm_nonneg (f x), norm_nonneg f]
        
      · exact ContinuousMap.norm_coe_le_norm f x
        
      
    · rw [← sq, ← Real.le_sqrt (norm_nonneg _) (norm_nonneg _), ContinuousMap.norm_le _ (Real.sqrt_nonneg _)]
      intro x
      rw [Real.le_sqrt (norm_nonneg _) (norm_nonneg _), sq, ← CstarRing.norm_star_mul_self]
      exact ContinuousMap.norm_coe_le_norm (star f * f) x
      

end CstarRing

end ContinuousMap

