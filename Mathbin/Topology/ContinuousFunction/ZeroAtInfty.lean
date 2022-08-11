/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import Mathbin.Topology.ContinuousFunction.Bounded
import Mathbin.Topology.ContinuousFunction.CocompactMap

/-!
# Continuous functions vanishing at infinity

The type of continuous functions vanishing at infinity. When the domain is compact
`C(α, β) ≃ C₀(α, β)` via the identity map. When the codomain is a metric space, every continuous
map which vanishes at infinity is a bounded continuous function. When the domain is a locally
compact space, this type has nice properties.

## TODO

* Create more intances of algebraic structures (e.g., `non_unital_semiring`) once the necessary
  type classes (e.g., `topological_ring`) are sufficiently generalized.
* Relate the unitization of `C₀(α, β)` to the Alexandroff compactification.
-/


universe u v w

variable {F : Type _} {α : Type u} {β : Type v} {γ : Type w} [TopologicalSpace α]

open BoundedContinuousFunction TopologicalSpace

open Filter Metric

/-- `C₀(α, β)` is the type of continuous functions `α → β` which vanish at infinity from a
topological space to a metric space with a zero element.

When possible, instead of parametrizing results over `(f : C₀(α, β))`,
you should parametrize over `(F : Type*) [zero_at_infty_continuous_map_class F α β] (f : F)`.

When you extend this structure, make sure to extend `zero_at_infty_continuous_map_class`. -/
structure ZeroAtInftyContinuousMap (α : Type u) (β : Type v) [TopologicalSpace α] [Zero β] [TopologicalSpace β] extends
  ContinuousMap α β : Type max u v where
  zero_at_infty' : Tendsto to_fun (cocompact α) (𝓝 0)

-- mathport name: «exprC₀( , )»
localized [ZeroAtInfty] notation (priority := 2000) "C₀(" α ", " β ")" => ZeroAtInftyContinuousMap α β

-- mathport name: «expr →C₀ »
localized [ZeroAtInfty] notation α " →C₀ " β => ZeroAtInftyContinuousMap α β

/-- `zero_at_infty_continuous_map_class F α β` states that `F` is a type of continuous maps which
vanish at infinity.

You should also extend this typeclass when you extend `zero_at_infty_continuous_map`. -/
class ZeroAtInftyContinuousMapClass (F : Type _) (α β : outParam <| Type _) [TopologicalSpace α] [Zero β]
  [TopologicalSpace β] extends ContinuousMapClass F α β where
  zero_at_infty (f : F) : Tendsto f (cocompact α) (𝓝 0)

export ZeroAtInftyContinuousMapClass (zero_at_infty)

namespace ZeroAtInftyContinuousMap

section Basics

variable [TopologicalSpace β] [Zero β] [ZeroAtInftyContinuousMapClass F α β]

instance : ZeroAtInftyContinuousMapClass C₀(α, β) α β where
  coe := fun f => f.toFun
  coe_injective' := fun f g h => by
    obtain ⟨⟨_, _⟩, _⟩ := f
    obtain ⟨⟨_, _⟩, _⟩ := g
    congr
  map_continuous := fun f => f.continuous_to_fun
  zero_at_infty := fun f => f.zero_at_infty'

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : CoeFun C₀(α, β) fun _ => α → β :=
  FunLike.hasCoeToFun

instance : CoeTₓ F C₀(α, β) :=
  ⟨fun f => { toFun := f, continuous_to_fun := map_continuous f, zero_at_infty' := zero_at_infty f }⟩

@[simp]
theorem coe_to_continuous_fun (f : C₀(α, β)) : (f.toContinuousMap : α → β) = f :=
  rfl

@[ext]
theorem ext {f g : C₀(α, β)} (h : ∀ x, f x = g x) : f = g :=
  FunLike.ext _ _ h

/-- Copy of a `zero_at_infinity_continuous_map` with a new `to_fun` equal to the old one. Useful
to fix definitional equalities. -/
protected def copy (f : C₀(α, β)) (f' : α → β) (h : f' = f) : C₀(α, β) where
  toFun := f'
  continuous_to_fun := by
    rw [h]
    exact f.continuous_to_fun
  zero_at_infty' := by
    simp_rw [h]
    exact f.zero_at_infty'

theorem eq_of_empty [IsEmpty α] (f g : C₀(α, β)) : f = g :=
  ext <| IsEmpty.elim ‹_›

/-- A continuous function on a compact space is automatically a continuous function vanishing at
infinity. -/
@[simps]
def ContinuousMap.liftZeroAtInfty [CompactSpace α] : C(α, β) ≃ C₀(α, β) where
  toFun := fun f =>
    { toFun := f, continuous_to_fun := f.Continuous,
      zero_at_infty' := by
        simp }
  invFun := fun f => f
  left_inv := fun f => by
    ext
    rfl
  right_inv := fun f => by
    ext
    rfl

/-- A continuous function on a compact space is automatically a continuous function vanishing at
infinity. This is not an instance to avoid type class loops. -/
@[simps]
def zeroAtInftyContinuousMapClass.ofCompact {G : Type _} [ContinuousMapClass G α β] [CompactSpace α] :
    ZeroAtInftyContinuousMapClass G α β where
  coe := fun g => g
  coe_injective' := fun f g h => FunLike.coe_fn_eq.mp h
  map_continuous := map_continuous
  zero_at_infty := by
    simp

end Basics

/-! ### Algebraic structure

Whenever `β` has suitable algebraic structure and a compatible topological structure, then
`C₀(α, β)` inherits a corresponding algebraic structure. The primary exception to this is that
`C₀(α, β)` will not have a multiplicative identity.
-/


section AlgebraicStructure

variable [TopologicalSpace β] (x : α)

instance [Zero β] : Zero C₀(α, β) :=
  ⟨⟨0, tendsto_const_nhds⟩⟩

instance [Zero β] : Inhabited C₀(α, β) :=
  ⟨0⟩

@[simp]
theorem coe_zero [Zero β] : ⇑(0 : C₀(α, β)) = 0 :=
  rfl

theorem zero_apply [Zero β] : (0 : C₀(α, β)) x = 0 :=
  rfl

instance [MulZeroClassₓ β] [HasContinuousMul β] : Mul C₀(α, β) :=
  ⟨fun f g =>
    ⟨f * g, by
      simpa only [← mul_zero] using (zero_at_infty f).mul (zero_at_infty g)⟩⟩

@[simp]
theorem coe_mul [MulZeroClassₓ β] [HasContinuousMul β] (f g : C₀(α, β)) : ⇑(f * g) = f * g :=
  rfl

theorem mul_apply [MulZeroClassₓ β] [HasContinuousMul β] (f g : C₀(α, β)) : (f * g) x = f x * g x :=
  rfl

instance [MulZeroClassₓ β] [HasContinuousMul β] : MulZeroClassₓ C₀(α, β) :=
  FunLike.coe_injective.MulZeroClass _ coe_zero coe_mul

instance [SemigroupWithZeroₓ β] [HasContinuousMul β] : SemigroupWithZeroₓ C₀(α, β) :=
  FunLike.coe_injective.SemigroupWithZero _ coe_zero coe_mul

instance [AddZeroClassₓ β] [HasContinuousAdd β] : Add C₀(α, β) :=
  ⟨fun f g =>
    ⟨f + g, by
      simpa only [← add_zeroₓ] using (zero_at_infty f).add (zero_at_infty g)⟩⟩

@[simp]
theorem coe_add [AddZeroClassₓ β] [HasContinuousAdd β] (f g : C₀(α, β)) : ⇑(f + g) = f + g :=
  rfl

theorem add_apply [AddZeroClassₓ β] [HasContinuousAdd β] (f g : C₀(α, β)) : (f + g) x = f x + g x :=
  rfl

instance [AddZeroClassₓ β] [HasContinuousAdd β] : AddZeroClassₓ C₀(α, β) :=
  FunLike.coe_injective.AddZeroClass _ coe_zero coe_add

section AddMonoidₓ

variable [AddMonoidₓ β] [HasContinuousAdd β] (f g : C₀(α, β))

@[simp]
theorem coe_nsmul_rec : ∀ n, ⇑(nsmulRec n f) = n • f
  | 0 => by
    rw [nsmulRec, zero_smul, coe_zero]
  | n + 1 => by
    rw [nsmulRec, succ_nsmul, coe_add, coe_nsmul_rec]

instance hasNatScalar : HasSmul ℕ C₀(α, β) :=
  ⟨fun n f =>
    ⟨n • f, by
      simpa [← coe_nsmul_rec] using zero_at_infty (nsmulRec n f)⟩⟩

instance : AddMonoidₓ C₀(α, β) :=
  FunLike.coe_injective.AddMonoid _ coe_zero coe_add fun _ _ => rfl

end AddMonoidₓ

instance [AddCommMonoidₓ β] [HasContinuousAdd β] : AddCommMonoidₓ C₀(α, β) :=
  FunLike.coe_injective.AddCommMonoid _ coe_zero coe_add fun _ _ => rfl

section AddGroupₓ

variable [AddGroupₓ β] [TopologicalAddGroup β] (f g : C₀(α, β))

instance : Neg C₀(α, β) :=
  ⟨fun f =>
    ⟨-f, by
      simpa only [← neg_zero] using (zero_at_infty f).neg⟩⟩

@[simp]
theorem coe_neg : ⇑(-f) = -f :=
  rfl

theorem neg_apply : (-f) x = -f x :=
  rfl

instance : Sub C₀(α, β) :=
  ⟨fun f g =>
    ⟨f - g, by
      simpa only [← sub_zero] using (zero_at_infty f).sub (zero_at_infty g)⟩⟩

@[simp]
theorem coe_sub : ⇑(f - g) = f - g :=
  rfl

theorem sub_apply : (f - g) x = f x - g x :=
  rfl

@[simp]
theorem coe_zsmul_rec : ∀ z, ⇑(zsmulRec z f) = z • f
  | Int.ofNat n => by
    rw [zsmulRec, Int.of_nat_eq_coe, coe_nsmul_rec, coe_nat_zsmul]
  | -[1+ n] => by
    rw [zsmulRec, zsmul_neg_succ_of_nat, coe_neg, coe_nsmul_rec]

instance hasIntScalar : HasSmul ℤ C₀(α, β) :=
  ⟨fun n f =>
    ⟨n • f, by
      simpa using zero_at_infty (zsmulRec n f)⟩⟩

instance : AddGroupₓ C₀(α, β) :=
  FunLike.coe_injective.AddGroup _ coe_zero coe_add coe_neg coe_sub (fun _ _ => rfl) fun _ _ => rfl

end AddGroupₓ

instance [AddCommGroupₓ β] [TopologicalAddGroup β] : AddCommGroupₓ C₀(α, β) :=
  FunLike.coe_injective.AddCommGroup _ coe_zero coe_add coe_neg coe_sub (fun _ _ => rfl) fun _ _ => rfl

instance [Zero β] {R : Type _} [Zero R] [SmulWithZero R β] [HasContinuousConstSmul R β] : HasSmul R C₀(α, β) :=
  ⟨fun r f =>
    ⟨r • f, by
      simpa [← smul_zero] using (zero_at_infty f).const_smul r⟩⟩

@[simp]
theorem coe_smul [Zero β] {R : Type _} [Zero R] [SmulWithZero R β] [HasContinuousConstSmul R β] (r : R) (f : C₀(α, β)) :
    ⇑(r • f) = r • f :=
  rfl

theorem smul_apply [Zero β] {R : Type _} [Zero R] [SmulWithZero R β] [HasContinuousConstSmul R β] (r : R) (f : C₀(α, β))
    (x : α) : (r • f) x = r • f x :=
  rfl

instance [Zero β] {R : Type _} [Zero R] [SmulWithZero R β] [SmulWithZero Rᵐᵒᵖ β] [HasContinuousConstSmul R β]
    [IsCentralScalar R β] : IsCentralScalar R C₀(α, β) :=
  ⟨fun r f => ext fun x => op_smul_eq_smul _ _⟩

instance [Zero β] {R : Type _} [Zero R] [SmulWithZero R β] [HasContinuousConstSmul R β] : SmulWithZero R C₀(α, β) :=
  Function.Injective.smulWithZero ⟨_, coe_zero⟩ FunLike.coe_injective coe_smul

instance [Zero β] {R : Type _} [MonoidWithZeroₓ R] [MulActionWithZero R β] [HasContinuousConstSmul R β] :
    MulActionWithZero R C₀(α, β) :=
  Function.Injective.mulActionWithZero ⟨_, coe_zero⟩ FunLike.coe_injective coe_smul

instance [AddCommMonoidₓ β] [HasContinuousAdd β] {R : Type _} [Semiringₓ R] [Module R β] [HasContinuousConstSmul R β] :
    Module R C₀(α, β) :=
  Function.Injective.module R ⟨_, coe_zero, coe_add⟩ FunLike.coe_injective coe_smul

instance [NonUnitalNonAssocSemiringₓ β] [TopologicalSemiring β] : NonUnitalNonAssocSemiringₓ C₀(α, β) :=
  FunLike.coe_injective.NonUnitalNonAssocSemiring _ coe_zero coe_add coe_mul fun _ _ => rfl

instance [NonUnitalSemiringₓ β] [TopologicalSemiring β] : NonUnitalSemiringₓ C₀(α, β) :=
  FunLike.coe_injective.NonUnitalSemiring _ coe_zero coe_add coe_mul fun _ _ => rfl

instance [NonUnitalCommSemiring β] [TopologicalSemiring β] : NonUnitalCommSemiring C₀(α, β) :=
  FunLike.coe_injective.NonUnitalCommSemiring _ coe_zero coe_add coe_mul fun _ _ => rfl

instance [NonUnitalNonAssocRing β] [TopologicalRing β] : NonUnitalNonAssocRing C₀(α, β) :=
  FunLike.coe_injective.NonUnitalNonAssocRing _ coe_zero coe_add coe_mul coe_neg coe_sub (fun _ _ => rfl) fun _ _ => rfl

instance [NonUnitalRing β] [TopologicalRing β] : NonUnitalRing C₀(α, β) :=
  FunLike.coe_injective.NonUnitalRing _ coe_zero coe_add coe_mul coe_neg coe_sub (fun _ _ => rfl) fun _ _ => rfl

instance [NonUnitalCommRing β] [TopologicalRing β] : NonUnitalCommRing C₀(α, β) :=
  FunLike.coe_injective.NonUnitalCommRing _ coe_zero coe_add coe_mul coe_neg coe_sub (fun _ _ => rfl) fun _ _ => rfl

instance {R : Type _} [Semiringₓ R] [NonUnitalNonAssocSemiringₓ β] [TopologicalSemiring β] [Module R β]
    [HasContinuousConstSmul R β] [IsScalarTower R β β] :
    IsScalarTower R C₀(α, β) C₀(α, β) where smul_assoc := fun r f g => by
    ext
    simp only [← smul_eq_mul, ← coe_mul, ← coe_smul, ← Pi.mul_apply, ← Pi.smul_apply]
    rw [← smul_eq_mul, ← smul_eq_mul, smul_assoc]

instance {R : Type _} [Semiringₓ R] [NonUnitalNonAssocSemiringₓ β] [TopologicalSemiring β] [Module R β]
    [HasContinuousConstSmul R β] [SmulCommClass R β β] :
    SmulCommClass R C₀(α, β) C₀(α, β) where smul_comm := fun r f g => by
    ext
    simp only [← smul_eq_mul, ← coe_smul, ← coe_mul, ← Pi.smul_apply, ← Pi.mul_apply]
    rw [← smul_eq_mul, ← smul_eq_mul, smul_comm]

end AlgebraicStructure

/-! ### Metric structure

When `β` is a metric space, then every element of `C₀(α, β)` is bounded, and so there is a natural
inclusion map `zero_at_infty_continuous_map.to_bcf : C₀(α, β) → (α →ᵇ β)`. Via this map `C₀(α, β)`
inherits a metric as the pullback of the metric on `α →ᵇ β`. Moreover, this map has closed range
in `α →ᵇ β` and consequently `C₀(α, β)` is a complete space whenever `β` is complete.
-/


section Metric

open Metric Set

variable [MetricSpace β] [Zero β] [ZeroAtInftyContinuousMapClass F α β]

protected theorem bounded (f : F) : ∃ C, ∀ x y : α, dist ((f : α → β) x) (f y) ≤ C := by
  obtain ⟨K : Set α, hK₁, hK₂⟩ :=
    mem_cocompact.mp (tendsto_def.mp (zero_at_infty (f : F)) _ (closed_ball_mem_nhds (0 : β) zero_lt_one))
  obtain ⟨C, hC⟩ := (hK₁.image (map_continuous f)).Bounded.subset_ball (0 : β)
  refine' ⟨max C 1 + max C 1, fun x y => _⟩
  have : ∀ x, f x ∈ closed_ball (0 : β) (max C 1) := by
    intro x
    by_cases' hx : x ∈ K
    · exact (mem_closed_ball.mp <| hC ⟨x, hx, rfl⟩).trans (le_max_leftₓ _ _)
      
    · exact (mem_closed_ball.mp <| mem_preimage.mp (hK₂ hx)).trans (le_max_rightₓ _ _)
      
  exact (dist_triangle (f x) 0 (f y)).trans (add_le_add (mem_closed_ball.mp <| this x) (mem_closed_ball'.mp <| this y))

theorem bounded_range (f : C₀(α, β)) : Bounded (Range f) :=
  bounded_range_iff.2 f.Bounded

theorem bounded_image (f : C₀(α, β)) (s : Set α) : Bounded (f '' s) :=
  f.bounded_range.mono <| image_subset_range _ _

instance (priority := 100) :
    BoundedContinuousMapClass F α β where map_bounded := fun f => ZeroAtInftyContinuousMap.bounded f

/-- Construct a bounded continuous function from a continuous function vanishing at infinity. -/
@[simps]
def toBcf (f : C₀(α, β)) : α →ᵇ β :=
  ⟨f, map_bounded f⟩

section

variable (α) (β)

theorem to_bcf_injective : Function.Injective (toBcf : C₀(α, β) → α →ᵇ β) := fun f g h => by
  ext
  simpa only using FunLike.congr_fun h x

end

variable {C : ℝ} {f g : C₀(α, β)}

/-- The type of continuous functions vanishing at infinity, with the uniform distance induced by the
inclusion `zero_at_infinity_continuous_map.to_bcf`, is a metric space. -/
noncomputable instance : MetricSpace C₀(α, β) :=
  MetricSpace.induced _ (to_bcf_injective α β)
    (by
      infer_instance)

@[simp]
theorem dist_to_bcf_eq_dist {f g : C₀(α, β)} : dist f.toBcf g.toBcf = dist f g :=
  rfl

open BoundedContinuousFunction

/-- Convergence in the metric on `C₀(α, β)` is uniform convergence. -/
theorem tendsto_iff_tendsto_uniformly {ι : Type _} {F : ι → C₀(α, β)} {f : C₀(α, β)} {l : Filter ι} :
    Tendsto F l (𝓝 f) ↔ TendstoUniformly (fun i => F i) f l := by
  simpa only [← Metric.tendsto_nhds] using
    @BoundedContinuousFunction.tendsto_iff_tendsto_uniformly _ _ _ _ _ (fun i => (F i).toBcf) f.to_bcf l

theorem isometry_to_bcf : Isometry (toBcf : C₀(α, β) → α →ᵇ β) := by
  tauto

theorem closed_range_to_bcf : IsClosed (Range (toBcf : C₀(α, β) → α →ᵇ β)) := by
  refine' is_closed_iff_cluster_pt.mpr fun f hf => _
  rw [cluster_pt_principal_iff] at hf
  have : tendsto f (cocompact α) (𝓝 0) := by
    refine' metric.tendsto_nhds.mpr fun ε hε => _
    obtain ⟨_, hg, g, rfl⟩ := hf (ball f (ε / 2)) (ball_mem_nhds f <| half_pos hε)
    refine' (metric.tendsto_nhds.mp (zero_at_infty g) (ε / 2) (half_pos hε)).mp (eventually_of_forall fun x hx => _)
    calc dist (f x) 0 ≤ dist (g.to_bcf x) (f x) + dist (g x) 0 :=
        dist_triangle_left _ _ _ _ < dist g.to_bcf f + ε / 2 := add_lt_add_of_le_of_lt (dist_coe_le_dist x) hx _ < ε :=
        by
        simpa [← add_halves ε] using add_lt_add_right hg (ε / 2)
  exact
    ⟨⟨f.to_continuous_map, this⟩, by
      ext
      rfl⟩

/-- Continuous functions vanishing at infinity taking values in a complete space form a
complete space. -/
instance [CompleteSpace β] : CompleteSpace C₀(α, β) :=
  (complete_space_iff_is_complete_range isometry_to_bcf.UniformInducing).mpr closed_range_to_bcf.IsComplete

end Metric

section Norm

/-! ### Normed space

The norm structure on `C₀(α, β)` is the one induced by the inclusion `to_bcf : C₀(α, β) → (α →ᵇ b)`,
viewed as an additive monoid homomorphism. Then `C₀(α, β)` is naturally a normed space over a normed
field `𝕜` whenever `β` is as well.
-/


section NormedSpace

variable [NormedGroup β] {𝕜 : Type _} [NormedField 𝕜] [NormedSpace 𝕜 β]

/-- The natural inclusion `to_bcf : C₀(α, β) → (α →ᵇ β)` realized as an additive monoid
homomorphism. -/
def toBcfAddMonoidHom : C₀(α, β) →+ α →ᵇ β where
  toFun := toBcf
  map_zero' := rfl
  map_add' := fun x y => rfl

@[simp]
theorem coe_to_bcf_add_monoid_hom (f : C₀(α, β)) : (f.toBcfAddMonoidHom : α → β) = f :=
  rfl

noncomputable instance : NormedGroup C₀(α, β) :=
  NormedGroup.induced toBcfAddMonoidHom (to_bcf_injective α β)

@[simp]
theorem norm_to_bcf_eq_norm {f : C₀(α, β)} : ∥f.toBcf∥ = ∥f∥ :=
  rfl

instance : NormedSpace 𝕜 C₀(α, β) where norm_smul_le := fun k f => (norm_smul k f.toBcf).le

end NormedSpace

section NormedRing

variable [NonUnitalNormedRing β]

noncomputable instance : NonUnitalNormedRing C₀(α, β) :=
  { ZeroAtInftyContinuousMap.nonUnitalRing, ZeroAtInftyContinuousMap.normedGroup with
    norm_mul := fun f g => norm_mul_le f.toBcf g.toBcf }

end NormedRing

end Norm

section Star

/-! ### Star structure

It is possible to equip `C₀(α, β)` with a pointwise `star` operation whenever there is a continuous
`star : β → β` for which `star (0 : β) = 0`. We don't have quite this weak a typeclass, but
`star_add_monoid` is close enough.

The `star_add_monoid` and `normed_star_group` classes on `C₀(α, β)` are inherited from their
counterparts on `α →ᵇ β`. Ultimately, when `β` is a C⋆-ring, then so is `C₀(α, β)`.
-/


variable [TopologicalSpace β] [AddMonoidₓ β] [StarAddMonoid β] [HasContinuousStar β]

instance :
    HasStar
      C₀(α,
        β) where star := fun f =>
    { toFun := fun x => star (f x), continuous_to_fun := (map_continuous f).star,
      zero_at_infty' := by
        simpa only [← star_zero] using (continuous_star.tendsto (0 : β)).comp (zero_at_infty f) }

@[simp]
theorem coe_star (f : C₀(α, β)) : ⇑(star f) = star f :=
  rfl

theorem star_apply (f : C₀(α, β)) (x : α) : (star f) x = star (f x) :=
  rfl

instance [HasContinuousAdd β] : StarAddMonoid C₀(α, β) where
  star_involutive := fun f => ext fun x => star_star (f x)
  star_add := fun f g => ext fun x => star_add (f x) (g x)

end Star

section NormedStar

variable [NormedGroup β] [StarAddMonoid β] [NormedStarGroup β]

instance : NormedStarGroup C₀(α, β) where norm_star := fun f => (norm_star f.toBcf : _)

end NormedStar

section StarModule

variable {𝕜 : Type _} [Zero 𝕜] [HasStar 𝕜] [AddMonoidₓ β] [StarAddMonoid β] [TopologicalSpace β] [HasContinuousStar β]
  [SmulWithZero 𝕜 β] [HasContinuousConstSmul 𝕜 β] [StarModule 𝕜 β]

instance : StarModule 𝕜 C₀(α, β) where star_smul := fun k f => ext fun x => star_smul k (f x)

end StarModule

section StarRing

variable [NonUnitalSemiringₓ β] [StarRing β] [TopologicalSpace β] [HasContinuousStar β] [TopologicalSemiring β]

instance : StarRing C₀(α, β) :=
  { ZeroAtInftyContinuousMap.starAddMonoid with star_mul := fun f g => ext fun x => star_mul (f x) (g x) }

end StarRing

section CstarRing

instance [NonUnitalNormedRing β] [StarRing β] [CstarRing β] :
    CstarRing C₀(α, β) where norm_star_mul_self := fun f => @CstarRing.norm_star_mul_self _ _ _ _ f.toBcf

end CstarRing

/-! ### C₀ as a functor

For each `β` with sufficient structure, there is a contravariant functor `C₀(-, β)` from the
category of topological spaces with morphisms given by `cocompact_map`s.
-/


variable {δ : Type _} [TopologicalSpace β] [TopologicalSpace γ] [TopologicalSpace δ]

-- mathport name: «expr →co »
local notation α " →co " β => CocompactMap α β

section

variable [Zero δ]

/-- Composition of a continuous function vanishing at infinity with a cocompact map yields another
continuous function vanishing at infinity. -/
def comp (f : C₀(γ, δ)) (g : β →co γ) : C₀(β, δ) where
  toContinuousMap := (f : C(γ, δ)).comp g
  zero_at_infty' := (zero_at_infty f).comp (cocompact_tendsto g)

@[simp]
theorem coe_comp_to_continuous_fun (f : C₀(γ, δ)) (g : β →co γ) : ((f.comp g).toContinuousMap : β → δ) = f ∘ g :=
  rfl

@[simp]
theorem comp_id (f : C₀(γ, δ)) : f.comp (CocompactMap.id γ) = f :=
  ext fun x => rfl

@[simp]
theorem comp_assoc (f : C₀(γ, δ)) (g : β →co γ) (h : α →co β) : (f.comp g).comp h = f.comp (g.comp h) :=
  rfl

@[simp]
theorem zero_comp (g : β →co γ) : (0 : C₀(γ, δ)).comp g = 0 :=
  rfl

end

/-- Composition as an additive monoid homomorphism. -/
def compAddMonoidHom [AddMonoidₓ δ] [HasContinuousAdd δ] (g : β →co γ) : C₀(γ, δ) →+ C₀(β, δ) where
  toFun := fun f => f.comp g
  map_zero' := zero_comp g
  map_add' := fun f₁ f₂ => rfl

/-- Composition as a semigroup homomorphism. -/
def compMulHom [MulZeroClassₓ δ] [HasContinuousMul δ] (g : β →co γ) : C₀(γ, δ) →ₙ* C₀(β, δ) where
  toFun := fun f => f.comp g
  map_mul' := fun f₁ f₂ => rfl

/-- Composition as a linear map. -/
def compLinearMap [AddCommMonoidₓ δ] [HasContinuousAdd δ] {R : Type _} [Semiringₓ R] [Module R δ]
    [HasContinuousConstSmul R δ] (g : β →co γ) : C₀(γ, δ) →ₗ[R] C₀(β, δ) where
  toFun := fun f => f.comp g
  map_add' := fun f₁ f₂ => rfl
  map_smul' := fun r f => rfl

/-- Composition as a non-unital algebra homomorphism. -/
def compNonUnitalAlgHom {R : Type _} [Semiringₓ R] [NonUnitalNonAssocSemiringₓ δ] [TopologicalSemiring δ] [Module R δ]
    [HasContinuousConstSmul R δ] (g : β →co γ) : C₀(γ, δ) →ₙₐ[R] C₀(β, δ) where
  toFun := fun f => f.comp g
  map_smul' := fun r f => rfl
  map_zero' := rfl
  map_add' := fun f₁ f₂ => rfl
  map_mul' := fun f₁ f₂ => rfl

end ZeroAtInftyContinuousMap

