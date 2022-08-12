/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot
-/
import Mathbin.GroupTheory.GroupAction.ConjAct
import Mathbin.GroupTheory.GroupAction.Quotient
import Mathbin.Order.Filter.Pointwise
import Mathbin.Topology.Algebra.Monoid
import Mathbin.Topology.CompactOpen
import Mathbin.Topology.Sets.Compacts
import Mathbin.Topology.Algebra.Constructions

/-!
# Topological groups

This file defines the following typeclasses:

* `topological_group`, `topological_add_group`: multiplicative and additive topological groups,
  i.e., groups with continuous `(*)` and `(⁻¹)` / `(+)` and `(-)`;

* `has_continuous_sub G` means that `G` has a continuous subtraction operation.

There is an instance deducing `has_continuous_sub` from `topological_group` but we use a separate
typeclass because, e.g., `ℕ` and `ℝ≥0` have continuous subtraction but are not additive groups.

We also define `homeomorph` versions of several `equiv`s: `homeomorph.mul_left`,
`homeomorph.mul_right`, `homeomorph.inv`, and prove a few facts about neighbourhood filters in
groups.

## Tags

topological space, group, topological group
-/


open Classical Set Filter TopologicalSpace Function

open Classical TopologicalSpace Filter Pointwise

universe u v w x

variable {α : Type u} {β : Type v} {G : Type w} {H : Type x}

section ContinuousMulGroup

/-!
### Groups with continuous multiplication

In this section we prove a few statements about groups with continuous `(*)`.
-/


variable [TopologicalSpace G] [Groupₓ G] [HasContinuousMul G]

/-- Multiplication from the left in a topological group as a homeomorphism. -/
@[to_additive "Addition from the left in a topological additive group as a homeomorphism."]
protected def Homeomorph.mulLeft (a : G) : G ≃ₜ G :=
  { Equivₓ.mulLeft a with continuous_to_fun := continuous_const.mul continuous_id,
    continuous_inv_fun := continuous_const.mul continuous_id }

@[simp, to_additive]
theorem Homeomorph.coe_mul_left (a : G) : ⇑(Homeomorph.mulLeft a) = (· * ·) a :=
  rfl

@[to_additive]
theorem Homeomorph.mul_left_symm (a : G) : (Homeomorph.mulLeft a).symm = Homeomorph.mulLeft a⁻¹ := by
  ext
  rfl

@[to_additive]
theorem is_open_map_mul_left (a : G) : IsOpenMap fun x => a * x :=
  (Homeomorph.mulLeft a).IsOpenMap

@[to_additive IsOpen.left_add_coset]
theorem IsOpen.left_coset {U : Set G} (h : IsOpen U) (x : G) : IsOpen (LeftCoset x U) :=
  is_open_map_mul_left x _ h

@[to_additive]
theorem is_closed_map_mul_left (a : G) : IsClosedMap fun x => a * x :=
  (Homeomorph.mulLeft a).IsClosedMap

@[to_additive IsClosed.left_add_coset]
theorem IsClosed.left_coset {U : Set G} (h : IsClosed U) (x : G) : IsClosed (LeftCoset x U) :=
  is_closed_map_mul_left x _ h

/-- Multiplication from the right in a topological group as a homeomorphism. -/
@[to_additive "Addition from the right in a topological additive group as a homeomorphism."]
protected def Homeomorph.mulRight (a : G) : G ≃ₜ G :=
  { Equivₓ.mulRight a with continuous_to_fun := continuous_id.mul continuous_const,
    continuous_inv_fun := continuous_id.mul continuous_const }

@[simp, to_additive]
theorem Homeomorph.coe_mul_right (a : G) : ⇑(Homeomorph.mulRight a) = fun g => g * a :=
  rfl

@[to_additive]
theorem Homeomorph.mul_right_symm (a : G) : (Homeomorph.mulRight a).symm = Homeomorph.mulRight a⁻¹ := by
  ext
  rfl

@[to_additive]
theorem is_open_map_mul_right (a : G) : IsOpenMap fun x => x * a :=
  (Homeomorph.mulRight a).IsOpenMap

@[to_additive IsOpen.right_add_coset]
theorem IsOpen.right_coset {U : Set G} (h : IsOpen U) (x : G) : IsOpen (RightCoset U x) :=
  is_open_map_mul_right x _ h

@[to_additive]
theorem is_closed_map_mul_right (a : G) : IsClosedMap fun x => x * a :=
  (Homeomorph.mulRight a).IsClosedMap

@[to_additive IsClosed.right_add_coset]
theorem IsClosed.right_coset {U : Set G} (h : IsClosed U) (x : G) : IsClosed (RightCoset U x) :=
  is_closed_map_mul_right x _ h

@[to_additive]
theorem discrete_topology_of_open_singleton_one (h : IsOpen ({1} : Set G)) : DiscreteTopology G := by
  rw [← singletons_open_iff_discrete]
  intro g
  suffices {g} = (fun x : G => g⁻¹ * x) ⁻¹' {1} by
    rw [this]
    exact (continuous_mul_left g⁻¹).is_open_preimage _ h
  simp only [← mul_oneₓ, ← Set.preimage_mul_left_singleton, ← eq_self_iff_true, ← inv_invₓ, ←
    Set.singleton_eq_singleton_iff]

@[to_additive]
theorem discrete_topology_iff_open_singleton_one : DiscreteTopology G ↔ IsOpen ({1} : Set G) :=
  ⟨fun h => forall_open_iff_discrete.mpr h {1}, discrete_topology_of_open_singleton_one⟩

end ContinuousMulGroup

/-!
### `has_continuous_inv` and `has_continuous_neg`
-/


/-- Basic hypothesis to talk about a topological additive group. A topological additive group
over `M`, for example, is obtained by requiring the instances `add_group M` and
`has_continuous_add M` and `has_continuous_neg M`. -/
class HasContinuousNeg (G : Type u) [TopologicalSpace G] [Neg G] : Prop where
  continuous_neg : Continuous fun a : G => -a

/-- Basic hypothesis to talk about a topological group. A topological group over `M`, for example,
is obtained by requiring the instances `group M` and `has_continuous_mul M` and
`has_continuous_inv M`. -/
@[to_additive]
class HasContinuousInv (G : Type u) [TopologicalSpace G] [Inv G] : Prop where
  continuous_inv : Continuous fun a : G => a⁻¹

export HasContinuousInv (continuous_inv)

export HasContinuousNeg (continuous_neg)

section ContinuousInv

variable [TopologicalSpace G] [Inv G] [HasContinuousInv G]

@[to_additive]
theorem continuous_on_inv {s : Set G} : ContinuousOn Inv.inv s :=
  continuous_inv.ContinuousOn

@[to_additive]
theorem continuous_within_at_inv {s : Set G} {x : G} : ContinuousWithinAt Inv.inv s x :=
  continuous_inv.ContinuousWithinAt

@[to_additive]
theorem continuous_at_inv {x : G} : ContinuousAt Inv.inv x :=
  continuous_inv.ContinuousAt

@[to_additive]
theorem tendsto_inv (a : G) : Tendsto Inv.inv (𝓝 a) (𝓝 a⁻¹) :=
  continuous_at_inv

/-- If a function converges to a value in a multiplicative topological group, then its inverse
converges to the inverse of this value. For the version in normed fields assuming additionally
that the limit is nonzero, use `tendsto.inv'`. -/
@[to_additive]
theorem Filter.Tendsto.inv {f : α → G} {l : Filter α} {y : G} (h : Tendsto f l (𝓝 y)) :
    Tendsto (fun x => (f x)⁻¹) l (𝓝 y⁻¹) :=
  (continuous_inv.Tendsto y).comp h

variable [TopologicalSpace α] {f : α → G} {s : Set α} {x : α}

@[continuity, to_additive]
theorem Continuous.inv (hf : Continuous f) : Continuous fun x => (f x)⁻¹ :=
  continuous_inv.comp hf

@[to_additive]
theorem ContinuousAt.inv (hf : ContinuousAt f x) : ContinuousAt (fun x => (f x)⁻¹) x :=
  continuous_at_inv.comp hf

@[to_additive]
theorem ContinuousOn.inv (hf : ContinuousOn f s) : ContinuousOn (fun x => (f x)⁻¹) s :=
  continuous_inv.comp_continuous_on hf

@[to_additive]
theorem ContinuousWithinAt.inv (hf : ContinuousWithinAt f s x) : ContinuousWithinAt (fun x => (f x)⁻¹) s x :=
  hf.inv

@[to_additive]
instance [TopologicalSpace H] [Inv H] [HasContinuousInv H] : HasContinuousInv (G × H) :=
  ⟨(continuous_inv.comp continuous_fst).prod_mk (continuous_inv.comp continuous_snd)⟩

variable {ι : Type _}

@[to_additive]
instance Pi.has_continuous_inv {C : ι → Type _} [∀ i, TopologicalSpace (C i)] [∀ i, Inv (C i)]
    [∀ i, HasContinuousInv (C i)] :
    HasContinuousInv (∀ i, C i) where continuous_inv := continuous_pi fun i => Continuous.inv (continuous_apply i)

/-- A version of `pi.has_continuous_inv` for non-dependent functions. It is needed because sometimes
Lean fails to use `pi.has_continuous_inv` for non-dependent functions. -/
@[to_additive
      "A version of `pi.has_continuous_neg` for non-dependent functions. It is needed\nbecause sometimes Lean fails to use `pi.has_continuous_neg` for non-dependent functions."]
instance Pi.has_continuous_inv' : HasContinuousInv (ι → G) :=
  Pi.has_continuous_inv

@[to_additive]
instance (priority := 100) has_continuous_inv_of_discrete_topology [TopologicalSpace H] [Inv H] [DiscreteTopology H] :
    HasContinuousInv H :=
  ⟨continuous_of_discrete_topology⟩

section PointwiseLimits

variable (G₁ G₂ : Type _) [TopologicalSpace G₂] [T2Space G₂]

@[to_additive]
theorem is_closed_set_of_map_inv [Inv G₁] [Inv G₂] [HasContinuousInv G₂] :
    IsClosed { f : G₁ → G₂ | ∀ x, f x⁻¹ = (f x)⁻¹ } := by
  simp only [← set_of_forall]
  refine' is_closed_Inter fun i => is_closed_eq (continuous_apply _) (continuous_apply _).inv

end PointwiseLimits

instance Additive.has_continuous_neg [h : TopologicalSpace H] [Inv H] [HasContinuousInv H] :
    @HasContinuousNeg (Additive H) h _ where continuous_neg := @continuous_inv H _ _ _

instance Multiplicative.has_continuous_inv [h : TopologicalSpace H] [Neg H] [HasContinuousNeg H] :
    @HasContinuousInv (Multiplicative H) h _ where continuous_inv := @continuous_neg H _ _ _

end ContinuousInv

section ContinuousInvolutiveInv

variable [TopologicalSpace G] [HasInvolutiveInv G] [HasContinuousInv G] {s : Set G}

@[to_additive]
theorem IsCompact.inv (hs : IsCompact s) : IsCompact s⁻¹ := by
  rw [← image_inv]
  exact hs.image continuous_inv

variable (G)

/-- Inversion in a topological group as a homeomorphism. -/
@[to_additive "Negation in a topological group as a homeomorphism."]
protected def Homeomorph.inv (G : Type _) [TopologicalSpace G] [HasInvolutiveInv G] [HasContinuousInv G] : G ≃ₜ G :=
  { Equivₓ.inv G with continuous_to_fun := continuous_inv, continuous_inv_fun := continuous_inv }

@[to_additive]
theorem is_open_map_inv : IsOpenMap (Inv.inv : G → G) :=
  (Homeomorph.inv _).IsOpenMap

@[to_additive]
theorem is_closed_map_inv : IsClosedMap (Inv.inv : G → G) :=
  (Homeomorph.inv _).IsClosedMap

variable {G}

@[to_additive]
theorem IsOpen.inv (hs : IsOpen s) : IsOpen s⁻¹ :=
  hs.Preimage continuous_inv

@[to_additive]
theorem IsClosed.inv (hs : IsClosed s) : IsClosed s⁻¹ :=
  hs.Preimage continuous_inv

@[to_additive]
theorem inv_closure : ∀ s : Set G, (Closure s)⁻¹ = Closure s⁻¹ :=
  (Homeomorph.inv G).preimage_closure

end ContinuousInvolutiveInv

section LatticeOps

variable {ι' : Sort _} [Inv G] [Inv H] {ts : Set (TopologicalSpace G)} (h : ∀, ∀ t ∈ ts, ∀, @HasContinuousInv G t _)
  {ts' : ι' → TopologicalSpace G} (h' : ∀ i, @HasContinuousInv G (ts' i) _) {t₁ t₂ : TopologicalSpace G}
  (h₁ : @HasContinuousInv G t₁ _) (h₂ : @HasContinuousInv G t₂ _) {t : TopologicalSpace H} [HasContinuousInv H]

@[to_additive]
theorem has_continuous_inv_Inf : @HasContinuousInv G (inf ts) _ :=
  { continuous_inv :=
      continuous_Inf_rng fun t ht => continuous_Inf_dom ht (@HasContinuousInv.continuous_inv G t _ (h t ht)) }

include h'

@[to_additive]
theorem has_continuous_inv_infi : @HasContinuousInv G (⨅ i, ts' i) _ := by
  rw [← Inf_range]
  exact has_continuous_inv_Inf (set.forall_range_iff.mpr h')

omit h'

include h₁ h₂

@[to_additive]
theorem has_continuous_inv_inf : @HasContinuousInv G (t₁⊓t₂) _ := by
  rw [inf_eq_infi]
  refine' has_continuous_inv_infi fun b => _
  cases b <;> assumption

end LatticeOps

section TopologicalGroup

/-!
### Topological groups

A topological group is a group in which the multiplication and inversion operations are
continuous. Topological additive groups are defined in the same way. Equivalently, we can require
that the division operation `λ x y, x * y⁻¹` (resp., subtraction) is continuous.
-/


/-- A topological (additive) group is a group in which the addition and negation operations are
continuous. -/
class TopologicalAddGroup (G : Type u) [TopologicalSpace G] [AddGroupₓ G] extends HasContinuousAdd G,
  HasContinuousNeg G : Prop

/-- A topological group is a group in which the multiplication and inversion operations are
continuous.

When you declare an instance that does not already have a `uniform_space` instance,
you should also provide an instance of `uniform_space` and `uniform_group` using
`topological_group.to_uniform_space` and `topological_group_is_uniform`. -/
@[to_additive]
class TopologicalGroup (G : Type _) [TopologicalSpace G] [Groupₓ G] extends HasContinuousMul G, HasContinuousInv G :
  Prop

section Conj

instance ConjAct.units_has_continuous_const_smul {M} [Monoidₓ M] [TopologicalSpace M] [HasContinuousMul M] :
    HasContinuousConstSmul (ConjAct Mˣ) M :=
  ⟨fun m => (continuous_const.mul continuous_id).mul continuous_const⟩

variable [TopologicalSpace G] [Inv G] [Mul G] [HasContinuousMul G]

/-- Conjugation is jointly continuous on `G × G` when both `mul` and `inv` are continuous. -/
@[to_additive "Conjugation is jointly continuous on `G × G` when both `mul` and `inv` are\ncontinuous."]
theorem TopologicalGroup.continuous_conj_prod [HasContinuousInv G] :
    Continuous fun g : G × G => g.fst * g.snd * g.fst⁻¹ :=
  continuous_mul.mul (continuous_inv.comp continuous_fst)

/-- Conjugation by a fixed element is continuous when `mul` is continuous. -/
@[to_additive "Conjugation by a fixed element is continuous when `add` is continuous."]
theorem TopologicalGroup.continuous_conj (g : G) : Continuous fun h : G => g * h * g⁻¹ :=
  (continuous_mul_right g⁻¹).comp (continuous_mul_left g)

/-- Conjugation acting on fixed element of the group is continuous when both `mul` and
`inv` are continuous. -/
@[to_additive
      "Conjugation acting on fixed element of the additive group is continuous when both\n  `add` and `neg` are continuous."]
theorem TopologicalGroup.continuous_conj' [HasContinuousInv G] (h : G) : Continuous fun g : G => g * h * g⁻¹ :=
  (continuous_mul_right h).mul continuous_inv

end Conj

variable [TopologicalSpace G] [Groupₓ G] [TopologicalGroup G] [TopologicalSpace α] {f : α → G} {s : Set α} {x : α}

section Zpow

@[continuity, to_additive]
theorem continuous_zpow : ∀ z : ℤ, Continuous fun a : G => a ^ z
  | Int.ofNat n => by
    simpa using continuous_pow n
  | -[1+ n] => by
    simpa using (continuous_pow (n + 1)).inv

instance AddGroupₓ.has_continuous_const_smul_int {A} [AddGroupₓ A] [TopologicalSpace A] [TopologicalAddGroup A] :
    HasContinuousConstSmul ℤ A :=
  ⟨continuous_zsmul⟩

instance AddGroupₓ.has_continuous_smul_int {A} [AddGroupₓ A] [TopologicalSpace A] [TopologicalAddGroup A] :
    HasContinuousSmul ℤ A :=
  ⟨continuous_uncurry_of_discrete_topology continuous_zsmul⟩

@[continuity, to_additive]
theorem Continuous.zpow {f : α → G} (h : Continuous f) (z : ℤ) : Continuous fun b => f b ^ z :=
  (continuous_zpow z).comp h

@[to_additive]
theorem continuous_on_zpow {s : Set G} (z : ℤ) : ContinuousOn (fun x => x ^ z) s :=
  (continuous_zpow z).ContinuousOn

@[to_additive]
theorem continuous_at_zpow (x : G) (z : ℤ) : ContinuousAt (fun x => x ^ z) x :=
  (continuous_zpow z).ContinuousAt

@[to_additive]
theorem Filter.Tendsto.zpow {α} {l : Filter α} {f : α → G} {x : G} (hf : Tendsto f l (𝓝 x)) (z : ℤ) :
    Tendsto (fun x => f x ^ z) l (𝓝 (x ^ z)) :=
  (continuous_at_zpow _ _).Tendsto.comp hf

@[to_additive]
theorem ContinuousWithinAt.zpow {f : α → G} {x : α} {s : Set α} (hf : ContinuousWithinAt f s x) (z : ℤ) :
    ContinuousWithinAt (fun x => f x ^ z) s x :=
  hf.zpow z

@[to_additive]
theorem ContinuousAt.zpow {f : α → G} {x : α} (hf : ContinuousAt f x) (z : ℤ) : ContinuousAt (fun x => f x ^ z) x :=
  hf.zpow z

@[to_additive ContinuousOn.zsmul]
theorem ContinuousOn.zpow {f : α → G} {s : Set α} (hf : ContinuousOn f s) (z : ℤ) : ContinuousOn (fun x => f x ^ z) s :=
  fun x hx => (hf x hx).zpow z

end Zpow

section OrderedCommGroup

variable [TopologicalSpace H] [OrderedCommGroup H] [TopologicalGroup H]

@[to_additive]
theorem tendsto_inv_nhds_within_Ioi {a : H} : Tendsto Inv.inv (𝓝[>] a) (𝓝[<] a⁻¹) :=
  (continuous_inv.Tendsto a).inf <| by
    simp [← tendsto_principal_principal]

@[to_additive]
theorem tendsto_inv_nhds_within_Iio {a : H} : Tendsto Inv.inv (𝓝[<] a) (𝓝[>] a⁻¹) :=
  (continuous_inv.Tendsto a).inf <| by
    simp [← tendsto_principal_principal]

@[to_additive]
theorem tendsto_inv_nhds_within_Ioi_inv {a : H} : Tendsto Inv.inv (𝓝[>] a⁻¹) (𝓝[<] a) := by
  simpa only [← inv_invₓ] using @tendsto_inv_nhds_within_Ioi _ _ _ _ a⁻¹

@[to_additive]
theorem tendsto_inv_nhds_within_Iio_inv {a : H} : Tendsto Inv.inv (𝓝[<] a⁻¹) (𝓝[>] a) := by
  simpa only [← inv_invₓ] using @tendsto_inv_nhds_within_Iio _ _ _ _ a⁻¹

@[to_additive]
theorem tendsto_inv_nhds_within_Ici {a : H} : Tendsto Inv.inv (𝓝[≥] a) (𝓝[≤] a⁻¹) :=
  (continuous_inv.Tendsto a).inf <| by
    simp [← tendsto_principal_principal]

@[to_additive]
theorem tendsto_inv_nhds_within_Iic {a : H} : Tendsto Inv.inv (𝓝[≤] a) (𝓝[≥] a⁻¹) :=
  (continuous_inv.Tendsto a).inf <| by
    simp [← tendsto_principal_principal]

@[to_additive]
theorem tendsto_inv_nhds_within_Ici_inv {a : H} : Tendsto Inv.inv (𝓝[≥] a⁻¹) (𝓝[≤] a) := by
  simpa only [← inv_invₓ] using @tendsto_inv_nhds_within_Ici _ _ _ _ a⁻¹

@[to_additive]
theorem tendsto_inv_nhds_within_Iic_inv {a : H} : Tendsto Inv.inv (𝓝[≤] a⁻¹) (𝓝[≥] a) := by
  simpa only [← inv_invₓ] using @tendsto_inv_nhds_within_Iic _ _ _ _ a⁻¹

end OrderedCommGroup

@[instance, to_additive]
instance [TopologicalSpace H] [Groupₓ H] [TopologicalGroup H] :
    TopologicalGroup (G × H) where continuous_inv := continuous_inv.prod_map continuous_inv

@[to_additive]
instance Pi.topological_group {C : β → Type _} [∀ b, TopologicalSpace (C b)] [∀ b, Groupₓ (C b)]
    [∀ b, TopologicalGroup (C b)] :
    TopologicalGroup (∀ b, C b) where continuous_inv := continuous_pi fun i => (continuous_apply i).inv

open MulOpposite

@[to_additive]
instance [Groupₓ α] [HasContinuousInv α] :
    HasContinuousInv
      αᵐᵒᵖ where continuous_inv := continuous_induced_rng <| (@continuous_inv α _ _ _).comp continuous_unop

/-- If multiplication is continuous in `α`, then it also is in `αᵐᵒᵖ`. -/
@[to_additive "If addition is continuous in `α`, then it also is in `αᵃᵒᵖ`."]
instance [Groupₓ α] [TopologicalGroup α] : TopologicalGroup αᵐᵒᵖ where

variable (G)

@[to_additive]
theorem nhds_one_symm : comap Inv.inv (𝓝 (1 : G)) = 𝓝 (1 : G) :=
  ((Homeomorph.inv G).comap_nhds_eq _).trans (congr_arg nhds inv_one)

/-- The map `(x, y) ↦ (x, xy)` as a homeomorphism. This is a shear mapping. -/
@[to_additive "The map `(x, y) ↦ (x, x + y)` as a homeomorphism.\nThis is a shear mapping."]
protected def Homeomorph.shearMulRight : G × G ≃ₜ G × G :=
  { Equivₓ.prodShear (Equivₓ.refl _) Equivₓ.mulLeft with continuous_to_fun := continuous_fst.prod_mk continuous_mul,
    continuous_inv_fun := continuous_fst.prod_mk <| continuous_fst.inv.mul continuous_snd }

@[simp, to_additive]
theorem Homeomorph.shear_mul_right_coe : ⇑(Homeomorph.shearMulRight G) = fun z : G × G => (z.1, z.1 * z.2) :=
  rfl

@[simp, to_additive]
theorem Homeomorph.shear_mul_right_symm_coe :
    ⇑(Homeomorph.shearMulRight G).symm = fun z : G × G => (z.1, z.1⁻¹ * z.2) :=
  rfl

variable {G}

namespace Subgroup

@[to_additive]
instance (S : Subgroup G) : TopologicalGroup S :=
  { S.toSubmonoid.HasContinuousMul with
    continuous_inv := by
      rw [embedding_subtype_coe.to_inducing.continuous_iff]
      exact continuous_subtype_coe.inv }

end Subgroup

/-- The (topological-space) closure of a subgroup of a space `M` with `has_continuous_mul` is
itself a subgroup. -/
@[to_additive
      "The (topological-space) closure of an additive subgroup of a space `M` with\n`has_continuous_add` is itself an additive subgroup."]
def Subgroup.topologicalClosure (s : Subgroup G) : Subgroup G :=
  { s.toSubmonoid.topologicalClosure with Carrier := Closure (s : Set G),
    inv_mem' := fun g m => by
      simpa [Set.mem_inv, ← inv_closure] using m }

@[simp, to_additive]
theorem Subgroup.topological_closure_coe {s : Subgroup G} : (s.topologicalClosure : Set G) = Closure s :=
  rfl

@[to_additive]
instance Subgroup.topological_closure_topological_group (s : Subgroup G) : TopologicalGroup s.topologicalClosure :=
  { s.toSubmonoid.topological_closure_has_continuous_mul with
    continuous_inv := by
      apply continuous_induced_rng
      change Continuous fun p : s.topological_closure => (p : G)⁻¹
      continuity }

@[to_additive]
theorem Subgroup.subgroup_topological_closure (s : Subgroup G) : s ≤ s.topologicalClosure :=
  subset_closure

@[to_additive]
theorem Subgroup.is_closed_topological_closure (s : Subgroup G) : IsClosed (s.topologicalClosure : Set G) := by
  convert is_closed_closure

@[to_additive]
theorem Subgroup.topological_closure_minimal (s : Subgroup G) {t : Subgroup G} (h : s ≤ t) (ht : IsClosed (t : Set G)) :
    s.topologicalClosure ≤ t :=
  closure_minimal h ht

@[to_additive]
theorem DenseRange.topological_closure_map_subgroup [Groupₓ H] [TopologicalSpace H] [TopologicalGroup H] {f : G →* H}
    (hf : Continuous f) (hf' : DenseRange f) {s : Subgroup G} (hs : s.topologicalClosure = ⊤) :
    (s.map f).topologicalClosure = ⊤ := by
  rw [SetLike.ext'_iff] at hs⊢
  simp only [← Subgroup.topological_closure_coe, ← Subgroup.coe_top, dense_iff_closure_eq] at hs⊢
  exact hf'.dense_image hf hs

/-- The topological closure of a normal subgroup is normal.-/
@[to_additive "The topological closure of a normal additive subgroup is normal."]
theorem Subgroup.is_normal_topological_closure {G : Type _} [TopologicalSpace G] [Groupₓ G] [TopologicalGroup G]
    (N : Subgroup G) [N.Normal] : (Subgroup.topologicalClosure N).Normal :=
  { conj_mem := fun n hn g => by
      apply mem_closure_of_continuous (TopologicalGroup.continuous_conj g) hn
      intro m hm
      exact subset_closure (Subgroup.Normal.conj_mem inferInstance m hm g) }

@[to_additive]
theorem mul_mem_connected_component_one {G : Type _} [TopologicalSpace G] [MulOneClassₓ G] [HasContinuousMul G]
    {g h : G} (hg : g ∈ ConnectedComponent (1 : G)) (hh : h ∈ ConnectedComponent (1 : G)) :
    g * h ∈ ConnectedComponent (1 : G) := by
  rw [connected_component_eq hg]
  have hmul : g ∈ ConnectedComponent (g * h) := by
    apply Continuous.image_connected_component_subset (continuous_mul_left g)
    rw [← connected_component_eq hh]
    exact
      ⟨(1 : G), mem_connected_component, by
        simp only [← mul_oneₓ]⟩
  simpa [connected_component_eq hmul] using mem_connected_component

@[to_additive]
theorem inv_mem_connected_component_one {G : Type _} [TopologicalSpace G] [Groupₓ G] [TopologicalGroup G] {g : G}
    (hg : g ∈ ConnectedComponent (1 : G)) : g⁻¹ ∈ ConnectedComponent (1 : G) := by
  rw [← inv_one]
  exact Continuous.image_connected_component_subset continuous_inv _ ((Set.mem_image _ _ _).mp ⟨g, hg, rfl⟩)

/-- The connected component of 1 is a subgroup of `G`. -/
@[to_additive "The connected component of 0 is a subgroup of `G`."]
def Subgroup.connectedComponentOfOne (G : Type _) [TopologicalSpace G] [Groupₓ G] [TopologicalGroup G] :
    Subgroup G where
  Carrier := ConnectedComponent (1 : G)
  one_mem' := mem_connected_component
  mul_mem' := fun g h hg hh => mul_mem_connected_component_one hg hh
  inv_mem' := fun g hg => inv_mem_connected_component_one hg

/-- If a subgroup of a topological group is commutative, then so is its topological closure. -/
@[to_additive "If a subgroup of an additive topological group is commutative, then so is its\ntopological closure."]
def Subgroup.commGroupTopologicalClosure [T2Space G] (s : Subgroup G) (hs : ∀ x y : s, x * y = y * x) :
    CommGroupₓ s.topologicalClosure :=
  { s.topologicalClosure.toGroup, s.toSubmonoid.commMonoidTopologicalClosure hs with }

@[to_additive exists_nhds_half_neg]
theorem exists_nhds_split_inv {s : Set G} (hs : s ∈ 𝓝 (1 : G)) :
    ∃ V ∈ 𝓝 (1 : G), ∀, ∀ v ∈ V, ∀, ∀ w ∈ V, ∀, v / w ∈ s := by
  have : (fun p : G × G => p.1 * p.2⁻¹) ⁻¹' s ∈ 𝓝 ((1, 1) : G × G) :=
    continuous_at_fst.mul continuous_at_snd.inv
      (by
        simpa)
  simpa only [← div_eq_mul_inv, ← nhds_prod_eq, ← mem_prod_self_iff, ← prod_subset_iff, ← mem_preimage] using this

@[to_additive]
theorem nhds_translation_mul_inv (x : G) : comap (fun y : G => y * x⁻¹) (𝓝 1) = 𝓝 x :=
  ((Homeomorph.mulRight x⁻¹).comap_nhds_eq 1).trans <|
    show 𝓝 (1 * x⁻¹⁻¹) = 𝓝 x by
      simp

@[simp, to_additive]
theorem map_mul_left_nhds (x y : G) : map ((· * ·) x) (𝓝 y) = 𝓝 (x * y) :=
  (Homeomorph.mulLeft x).map_nhds_eq y

@[to_additive]
theorem map_mul_left_nhds_one (x : G) : map ((· * ·) x) (𝓝 1) = 𝓝 x := by
  simp

/-- A monoid homomorphism (a bundled morphism of a type that implements `monoid_hom_class`) from a
topological group to a topological monoid is continuous provided that it is continuous at one. See
also `uniform_continuous_of_continuous_at_one`. -/
@[to_additive
      "An additive monoid homomorphism (a bundled morphism of a type that implements\n`add_monoid_hom_class`) from an additive topological group to an additive topological monoid is\ncontinuous provided that it is continuous at zero. See also\n`uniform_continuous_of_continuous_at_zero`."]
theorem continuous_of_continuous_at_one {M hom : Type _} [MulOneClassₓ M] [TopologicalSpace M] [HasContinuousMul M]
    [MonoidHomClass hom G M] (f : hom) (hf : ContinuousAt f 1) : Continuous f :=
  continuous_iff_continuous_at.2 fun x => by
    simpa only [← ContinuousAt, map_mul_left_nhds_one x, ← tendsto_map'_iff, ← (· ∘ ·), ← map_mul, ← map_one, ←
      mul_oneₓ] using hf.tendsto.const_mul (f x)

@[to_additive]
theorem TopologicalGroup.ext {G : Type _} [Groupₓ G] {t t' : TopologicalSpace G} (tg : @TopologicalGroup G t _)
    (tg' : @TopologicalGroup G t' _) (h : @nhds G t 1 = @nhds G t' 1) : t = t' :=
  eq_of_nhds_eq_nhds fun x => by
    rw [← @nhds_translation_mul_inv G t _ _ x, ← @nhds_translation_mul_inv G t' _ _ x, ← h]

@[to_additive]
theorem TopologicalGroup.of_nhds_aux {G : Type _} [Groupₓ G] [TopologicalSpace G]
    (hinv : Tendsto (fun x : G => x⁻¹) (𝓝 1) (𝓝 1)) (hleft : ∀ x₀ : G, 𝓝 x₀ = map (fun x : G => x₀ * x) (𝓝 1))
    (hconj : ∀ x₀ : G, map (fun x : G => x₀ * x * x₀⁻¹) (𝓝 1) ≤ 𝓝 1) : Continuous fun x : G => x⁻¹ := by
  rw [continuous_iff_continuous_at]
  rintro x₀
  have key : (fun x => (x₀ * x)⁻¹) = (fun x => x₀⁻¹ * x) ∘ (fun x => x₀ * x * x₀⁻¹) ∘ fun x => x⁻¹ := by
    ext <;> simp [← mul_assoc]
  calc map (fun x => x⁻¹) (𝓝 x₀) = map (fun x => x⁻¹) ((map fun x => x₀ * x) <| 𝓝 1) := by
      rw [hleft]_ = map (fun x => (x₀ * x)⁻¹) (𝓝 1) := by
      rw [Filter.map_map]_ = map (((fun x => x₀⁻¹ * x) ∘ fun x => x₀ * x * x₀⁻¹) ∘ fun x => x⁻¹) (𝓝 1) := by
      rw [key]_ = map ((fun x => x₀⁻¹ * x) ∘ fun x => x₀ * x * x₀⁻¹) _ := by
      rw [← Filter.map_map]_ ≤ map ((fun x => x₀⁻¹ * x) ∘ fun x => x₀ * x * x₀⁻¹) (𝓝 1) :=
      map_mono hinv _ = map (fun x => x₀⁻¹ * x) (map (fun x => x₀ * x * x₀⁻¹) (𝓝 1)) :=
      Filter.map_map _ ≤ map (fun x => x₀⁻¹ * x) (𝓝 1) := map_mono (hconj x₀)_ = 𝓝 x₀⁻¹ := (hleft _).symm

@[to_additive]
theorem TopologicalGroup.of_nhds_one' {G : Type u} [Groupₓ G] [TopologicalSpace G]
    (hmul : Tendsto (uncurry ((· * ·) : G → G → G)) (𝓝 1 ×ᶠ 𝓝 1) (𝓝 1)) (hinv : Tendsto (fun x : G => x⁻¹) (𝓝 1) (𝓝 1))
    (hleft : ∀ x₀ : G, 𝓝 x₀ = map (fun x => x₀ * x) (𝓝 1)) (hright : ∀ x₀ : G, 𝓝 x₀ = map (fun x => x * x₀) (𝓝 1)) :
    TopologicalGroup G := by
  refine'
    { continuous_mul := (HasContinuousMul.of_nhds_one hmul hleft hright).continuous_mul,
      continuous_inv := TopologicalGroup.of_nhds_aux hinv hleft _ }
  intro x₀
  suffices map (fun x : G => x₀ * x * x₀⁻¹) (𝓝 1) = 𝓝 1 by
    simp [← this, ← le_reflₓ]
  rw
    [show (fun x => x₀ * x * x₀⁻¹) = (fun x => x₀ * x) ∘ fun x => x * x₀⁻¹ by
      ext
      simp [← mul_assoc],
    ← Filter.map_map, ← hright, hleft x₀⁻¹, Filter.map_map]
  convert map_id
  ext
  simp

@[to_additive]
theorem TopologicalGroup.of_nhds_one {G : Type u} [Groupₓ G] [TopologicalSpace G]
    (hmul : Tendsto (uncurry ((· * ·) : G → G → G)) (𝓝 1 ×ᶠ 𝓝 1) (𝓝 1)) (hinv : Tendsto (fun x : G => x⁻¹) (𝓝 1) (𝓝 1))
    (hleft : ∀ x₀ : G, 𝓝 x₀ = map (fun x => x₀ * x) (𝓝 1))
    (hconj : ∀ x₀ : G, Tendsto (fun x => x₀ * x * x₀⁻¹) (𝓝 1) (𝓝 1)) : TopologicalGroup G :=
  { continuous_mul := by
      rw [continuous_iff_continuous_at]
      rintro ⟨x₀, y₀⟩
      have key :
        (fun p : G × G => x₀ * p.1 * (y₀ * p.2)) =
          (fun x => x₀ * y₀ * x) ∘ uncurry (· * ·) ∘ Prod.map (fun x => y₀⁻¹ * x * y₀) id :=
        by
        ext
        simp [← uncurry, ← Prod.map, ← mul_assoc]
      specialize hconj y₀⁻¹
      rw [inv_invₓ] at hconj
      calc map (fun p : G × G => p.1 * p.2) (𝓝 (x₀, y₀)) = map (fun p : G × G => p.1 * p.2) (𝓝 x₀ ×ᶠ 𝓝 y₀) := by
          rw [nhds_prod_eq]_ = map (fun p : G × G => x₀ * p.1 * (y₀ * p.2)) (𝓝 1 ×ᶠ 𝓝 1) := by
          rw [hleft x₀, hleft y₀, prod_map_map_eq,
            Filter.map_map]_ =
            map (((fun x => x₀ * y₀ * x) ∘ uncurry (· * ·)) ∘ Prod.map (fun x => y₀⁻¹ * x * y₀) id) (𝓝 1 ×ᶠ 𝓝 1) :=
          by
          rw [key]_ = map ((fun x => x₀ * y₀ * x) ∘ uncurry (· * ·)) (((map fun x => y₀⁻¹ * x * y₀) <| 𝓝 1) ×ᶠ 𝓝 1) :=
          by
          rw [← Filter.map_map, ← prod_map_map_eq',
            map_id]_ ≤ map ((fun x => x₀ * y₀ * x) ∘ uncurry (· * ·)) (𝓝 1 ×ᶠ 𝓝 1) :=
          map_mono
            (Filter.prod_mono hconj <| le_rfl)_ = map (fun x => x₀ * y₀ * x) (map (uncurry (· * ·)) (𝓝 1 ×ᶠ 𝓝 1)) :=
          by
          rw [Filter.map_map]_ ≤ map (fun x => x₀ * y₀ * x) (𝓝 1) := map_mono hmul _ = 𝓝 (x₀ * y₀) := (hleft _).symm,
    continuous_inv := TopologicalGroup.of_nhds_aux hinv hleft hconj }

@[to_additive]
theorem TopologicalGroup.of_comm_of_nhds_one {G : Type u} [CommGroupₓ G] [TopologicalSpace G]
    (hmul : Tendsto (uncurry ((· * ·) : G → G → G)) (𝓝 1 ×ᶠ 𝓝 1) (𝓝 1)) (hinv : Tendsto (fun x : G => x⁻¹) (𝓝 1) (𝓝 1))
    (hleft : ∀ x₀ : G, 𝓝 x₀ = map (fun x => x₀ * x) (𝓝 1)) : TopologicalGroup G :=
  TopologicalGroup.of_nhds_one hmul hinv hleft
    (by
      simpa using tendsto_id)

end TopologicalGroup

section QuotientTopologicalGroup

variable [TopologicalSpace G] [Groupₓ G] [TopologicalGroup G] (N : Subgroup G) (n : N.Normal)

@[to_additive]
instance QuotientGroup.Quotient.topologicalSpace {G : Type _} [Groupₓ G] [TopologicalSpace G] (N : Subgroup G) :
    TopologicalSpace (G ⧸ N) :=
  Quotientₓ.topologicalSpace

open QuotientGroup

@[to_additive]
theorem QuotientGroup.is_open_map_coe : IsOpenMap (coe : G → G ⧸ N) := by
  intro s s_op
  change IsOpen ((coe : G → G ⧸ N) ⁻¹' (coe '' s))
  rw [QuotientGroup.preimage_image_coe N s]
  exact is_open_Union fun n => (continuous_mul_right _).is_open_preimage s s_op

@[to_additive]
instance topological_group_quotient [N.Normal] : TopologicalGroup (G ⧸ N) where
  continuous_mul := by
    have cont : Continuous ((coe : G → G ⧸ N) ∘ fun p : G × G => p.fst * p.snd) :=
      continuous_quot_mk.comp continuous_mul
    have quot : QuotientMap fun p : G × G => ((p.1 : G ⧸ N), (p.2 : G ⧸ N)) := by
      apply IsOpenMap.to_quotient_map
      · exact (QuotientGroup.is_open_map_coe N).Prod (QuotientGroup.is_open_map_coe N)
        
      · exact continuous_quot_mk.prod_map continuous_quot_mk
        
      · exact (surjective_quot_mk _).prod_map (surjective_quot_mk _)
        
    exact (QuotientMap.continuous_iff Quot).2 cont
  continuous_inv := by
    have : Continuous ((coe : G → G ⧸ N) ∘ fun a : G => a⁻¹) := continuous_quot_mk.comp continuous_inv
    convert continuous_quotient_lift _ this

end QuotientTopologicalGroup

/-- A typeclass saying that `λ p : G × G, p.1 - p.2` is a continuous function. This property
automatically holds for topological additive groups but it also holds, e.g., for `ℝ≥0`. -/
class HasContinuousSub (G : Type _) [TopologicalSpace G] [Sub G] : Prop where
  continuous_sub : Continuous fun p : G × G => p.1 - p.2

/-- A typeclass saying that `λ p : G × G, p.1 / p.2` is a continuous function. This property
automatically holds for topological groups. Lemmas using this class have primes.
The unprimed version is for `group_with_zero`. -/
@[to_additive]
class HasContinuousDiv (G : Type _) [TopologicalSpace G] [Div G] : Prop where
  continuous_div' : Continuous fun p : G × G => p.1 / p.2

-- see Note [lower instance priority]
@[to_additive]
instance (priority := 100) TopologicalGroup.to_has_continuous_div [TopologicalSpace G] [Groupₓ G] [TopologicalGroup G] :
    HasContinuousDiv G :=
  ⟨by
    simp only [← div_eq_mul_inv]
    exact continuous_fst.mul continuous_snd.inv⟩

export HasContinuousSub (continuous_sub)

export HasContinuousDiv (continuous_div')

section HasContinuousDiv

variable [TopologicalSpace G] [Div G] [HasContinuousDiv G]

@[to_additive sub]
theorem Filter.Tendsto.div' {f g : α → G} {l : Filter α} {a b : G} (hf : Tendsto f l (𝓝 a)) (hg : Tendsto g l (𝓝 b)) :
    Tendsto (fun x => f x / g x) l (𝓝 (a / b)) :=
  (continuous_div'.Tendsto (a, b)).comp (hf.prod_mk_nhds hg)

@[to_additive const_sub]
theorem Filter.Tendsto.const_div' (b : G) {c : G} {f : α → G} {l : Filter α} (h : Tendsto f l (𝓝 c)) :
    Tendsto (fun k : α => b / f k) l (𝓝 (b / c)) :=
  tendsto_const_nhds.div' h

@[to_additive sub_const]
theorem Filter.Tendsto.div_const' (b : G) {c : G} {f : α → G} {l : Filter α} (h : Tendsto f l (𝓝 c)) :
    Tendsto (fun k : α => f k / b) l (𝓝 (c / b)) :=
  h.div' tendsto_const_nhds

variable [TopologicalSpace α] {f g : α → G} {s : Set α} {x : α}

@[continuity, to_additive sub]
theorem Continuous.div' (hf : Continuous f) (hg : Continuous g) : Continuous fun x => f x / g x :=
  continuous_div'.comp (hf.prod_mk hg : _)

@[to_additive continuous_sub_left]
theorem continuous_div_left' (a : G) : Continuous fun b : G => a / b :=
  continuous_const.div' continuous_id

@[to_additive continuous_sub_right]
theorem continuous_div_right' (a : G) : Continuous fun b : G => b / a :=
  continuous_id.div' continuous_const

@[to_additive sub]
theorem ContinuousAt.div' {f g : α → G} {x : α} (hf : ContinuousAt f x) (hg : ContinuousAt g x) :
    ContinuousAt (fun x => f x / g x) x :=
  hf.div' hg

@[to_additive sub]
theorem ContinuousWithinAt.div' (hf : ContinuousWithinAt f s x) (hg : ContinuousWithinAt g s x) :
    ContinuousWithinAt (fun x => f x / g x) s x :=
  hf.div' hg

@[to_additive sub]
theorem ContinuousOn.div' (hf : ContinuousOn f s) (hg : ContinuousOn g s) : ContinuousOn (fun x => f x / g x) s :=
  fun x hx => (hf x hx).div' (hg x hx)

end HasContinuousDiv

section DivInTopologicalGroup

variable [Groupₓ G] [TopologicalSpace G] [TopologicalGroup G]

/-- A version of `homeomorph.mul_left a b⁻¹` that is defeq to `a / b`. -/
@[to_additive " A version of `homeomorph.add_left a (-b)` that is defeq to `a - b`. ",
  simps (config := { simpRhs := true })]
def Homeomorph.divLeft (x : G) : G ≃ₜ G :=
  { Equivₓ.divLeft x with continuous_to_fun := continuous_const.div' continuous_id,
    continuous_inv_fun := continuous_inv.mul continuous_const }

@[to_additive]
theorem is_open_map_div_left (a : G) : IsOpenMap ((· / ·) a) :=
  (Homeomorph.divLeft _).IsOpenMap

@[to_additive]
theorem is_closed_map_div_left (a : G) : IsClosedMap ((· / ·) a) :=
  (Homeomorph.divLeft _).IsClosedMap

/-- A version of `homeomorph.mul_right a⁻¹ b` that is defeq to `b / a`. -/
@[to_additive " A version of `homeomorph.add_right (-a) b` that is defeq to `b - a`. ",
  simps (config := { simpRhs := true })]
def Homeomorph.divRight (x : G) : G ≃ₜ G :=
  { Equivₓ.divRight x with continuous_to_fun := continuous_id.div' continuous_const,
    continuous_inv_fun := continuous_id.mul continuous_const }

@[to_additive]
theorem is_open_map_div_right (a : G) : IsOpenMap fun x => x / a :=
  (Homeomorph.divRight a).IsOpenMap

@[to_additive]
theorem is_closed_map_div_right (a : G) : IsClosedMap fun x => x / a :=
  (Homeomorph.divRight a).IsClosedMap

@[to_additive]
theorem tendsto_div_nhds_one_iff {α : Type _} {l : Filter α} {x : G} {u : α → G} :
    Tendsto (fun n => u n / x) l (𝓝 1) ↔ Tendsto u l (𝓝 x) := by
  have A : tendsto (fun n : α => x) l (𝓝 x) := tendsto_const_nhds
  exact
    ⟨fun h => by
      simpa using h.mul A, fun h => by
      simpa using h.div' A⟩

@[to_additive]
theorem nhds_translation_div (x : G) : comap (· / x) (𝓝 1) = 𝓝 x := by
  simpa only [← div_eq_mul_inv] using nhds_translation_mul_inv x

end DivInTopologicalGroup

/-!
### Topological operations on pointwise sums and products

A few results about interior and closure of the pointwise addition/multiplication of sets in groups
with continuous addition/multiplication. See also `submonoid.top_closure_mul_self_eq` in
`topology.algebra.monoid`.
-/


section HasContinuousMul

variable [TopologicalSpace α] [Groupₓ α] [HasContinuousMul α] {s t : Set α}

@[to_additive]
theorem IsOpen.mul_left (ht : IsOpen t) : IsOpen (s * t) := by
  rw [← Union_mul_left_image]
  exact is_open_bUnion fun a ha => is_open_map_mul_left a t ht

@[to_additive]
theorem IsOpen.mul_right (hs : IsOpen s) : IsOpen (s * t) := by
  rw [← Union_mul_right_image]
  exact is_open_bUnion fun a ha => is_open_map_mul_right a s hs

@[to_additive]
theorem subset_interior_mul_left : Interior s * t ⊆ Interior (s * t) :=
  interior_maximal (Set.mul_subset_mul_right interior_subset) is_open_interior.mul_right

@[to_additive]
theorem subset_interior_mul_right : s * Interior t ⊆ Interior (s * t) :=
  interior_maximal (Set.mul_subset_mul_left interior_subset) is_open_interior.mul_left

@[to_additive]
theorem subset_interior_mul : Interior s * Interior t ⊆ Interior (s * t) :=
  (Set.mul_subset_mul_left interior_subset).trans subset_interior_mul_left

end HasContinuousMul

section TopologicalGroup

variable [TopologicalSpace α] [Groupₓ α] [TopologicalGroup α] {s t : Set α}

@[to_additive]
theorem IsOpen.div_left (ht : IsOpen t) : IsOpen (s / t) := by
  rw [← Union_div_left_image]
  exact is_open_bUnion fun a ha => is_open_map_div_left a t ht

@[to_additive]
theorem IsOpen.div_right (hs : IsOpen s) : IsOpen (s / t) := by
  rw [← Union_div_right_image]
  exact is_open_bUnion fun a ha => is_open_map_div_right a s hs

@[to_additive]
theorem subset_interior_div_left : Interior s / t ⊆ Interior (s / t) :=
  interior_maximal (div_subset_div_right interior_subset) is_open_interior.div_right

@[to_additive]
theorem subset_interior_div_right : s / Interior t ⊆ Interior (s / t) :=
  interior_maximal (div_subset_div_left interior_subset) is_open_interior.div_left

@[to_additive]
theorem subset_interior_div : Interior s / Interior t ⊆ Interior (s / t) :=
  (div_subset_div_left interior_subset).trans subset_interior_div_left

@[to_additive]
theorem IsOpen.mul_closure (hs : IsOpen s) (t : Set α) : s * Closure t = s * t := by
  refine' (mul_subset_iff.2 fun a ha b hb => _).antisymm (mul_subset_mul_left subset_closure)
  rw [mem_closure_iff] at hb
  have hbU : b ∈ s⁻¹ * {a * b} := ⟨a⁻¹, a * b, Set.inv_mem_inv.2 ha, rfl, inv_mul_cancel_leftₓ _ _⟩
  obtain ⟨_, ⟨c, d, hc, rfl : d = _, rfl⟩, hcs⟩ := hb _ hs.inv.mul_right hbU
  exact ⟨c⁻¹, _, hc, hcs, inv_mul_cancel_leftₓ _ _⟩

@[to_additive]
theorem IsOpen.closure_mul (ht : IsOpen t) (s : Set α) : Closure s * t = s * t := by
  rw [← inv_invₓ (Closure s * t), mul_inv_rev, inv_closure, ht.inv.mul_closure, mul_inv_rev, inv_invₓ, inv_invₓ]

@[to_additive]
theorem IsOpen.div_closure (hs : IsOpen s) (t : Set α) : s / Closure t = s / t := by
  simp_rw [div_eq_mul_inv, inv_closure, hs.mul_closure]

@[to_additive]
theorem IsOpen.closure_div (ht : IsOpen t) (s : Set α) : Closure s / t = s / t := by
  simp_rw [div_eq_mul_inv, ht.inv.closure_mul]

end TopologicalGroup

-- ./././Mathport/Syntax/Translate/Basic.lean:1440:30: infer kinds are unsupported in Lean 4: #[`z] []
/-- additive group with a neighbourhood around 0.
Only used to construct a topology and uniform space.

This is currently only available for commutative groups, but it can be extended to
non-commutative groups too.
-/
class AddGroupWithZeroNhd (G : Type u) extends AddCommGroupₓ G where
  z : Filter G
  zero_Z : pure 0 ≤ Z
  sub_Z : Tendsto (fun p : G × G => p.1 - p.2) (Z ×ᶠ Z) Z

section FilterMul

section

variable (G) [TopologicalSpace G] [Groupₓ G] [TopologicalGroup G]

@[to_additive]
theorem TopologicalGroup.t1_space (h : @IsClosed G _ {1}) : T1Space G :=
  ⟨fun x => by
    convert is_closed_map_mul_right x _ h
    simp ⟩

@[to_additive]
theorem TopologicalGroup.t3_space [T1Space G] : T3Space G :=
  ⟨fun s a hs ha => by
    let f := fun p : G × G => p.1 * p.2⁻¹
    have hf : Continuous f := continuous_fst.mul continuous_snd.inv
    -- a ∈ -s implies f (a, 1) ∈ -s, and so (a, 1) ∈ f⁻¹' (-s);
    -- and so can find t₁ t₂ open such that a ∈ t₁ × t₂ ⊆ f⁻¹' (-s)
    let ⟨t₁, t₂, ht₁, ht₂, a_mem_t₁, one_mem_t₂, t_subset⟩ :=
      is_open_prod_iff.1 ((is_open_compl_iff.2 hs).Preimage hf) a (1 : G)
        (by
          simpa [← f] )
    use s * t₂, ht₂.mul_left, fun x hx => ⟨x, 1, hx, one_mem_t₂, mul_oneₓ _⟩
    rw [nhdsWithin, inf_principal_eq_bot, mem_nhds_iff]
    refine' ⟨t₁, _, ht₁, a_mem_t₁⟩
    rintro x hx ⟨y, z, hy, hz, yz⟩
    have : x * z⁻¹ ∈ sᶜ := (prod_subset_iff.1 t_subset) x hx z hz
    have : x * z⁻¹ ∈ s
    rw [← yz]
    simpa
    contradiction⟩

@[to_additive]
theorem TopologicalGroup.t2_space [T1Space G] : T2Space G :=
  @T3Space.t2_space G _ (TopologicalGroup.t3_space G)

variable {G} (S : Subgroup G) [Subgroup.Normal S] [IsClosed (S : Set G)]

@[to_additive]
instance Subgroup.t3_quotient_of_is_closed (S : Subgroup G) [Subgroup.Normal S] [IsClosed (S : Set G)] :
    T3Space (G ⧸ S) := by
  suffices T1Space (G ⧸ S) by
    exact @TopologicalGroup.t3_space _ _ _ _ this
  have hS : IsClosed (S : Set G) := inferInstance
  rw [← QuotientGroup.ker_mk S] at hS
  exact TopologicalGroup.t1_space (G ⧸ S) (quotient_map_quotient_mk.is_closed_preimage.mp hS)

end

section

/-! Some results about an open set containing the product of two sets in a topological group. -/


variable [TopologicalSpace G] [Groupₓ G] [TopologicalGroup G]

/-- Given a compact set `K` inside an open set `U`, there is a open neighborhood `V` of `1`
  such that `K * V ⊆ U`. -/
@[to_additive
      "Given a compact set `K` inside an open set `U`, there is a open neighborhood `V` of\n`0` such that `K + V ⊆ U`."]
theorem compact_open_separated_mul_right {K U : Set G} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ V ∈ 𝓝 (1 : G), K * V ⊆ U := by
  apply hK.induction_on
  · exact
      ⟨univ, by
        simp ⟩
    
  · rintro s t hst ⟨V, hV, hV'⟩
    exact ⟨V, hV, (mul_subset_mul_right hst).trans hV'⟩
    
  · rintro s t ⟨V, V_in, hV'⟩ ⟨W, W_in, hW'⟩
    use V ∩ W, inter_mem V_in W_in
    rw [union_mul]
    exact
      union_subset ((mul_subset_mul_left (V.inter_subset_left W)).trans hV')
        ((mul_subset_mul_left (V.inter_subset_right W)).trans hW')
    
  · intro x hx
    have :=
      tendsto_mul
        (show U ∈ 𝓝 (x * 1) by
          simpa using hU.mem_nhds (hKU hx))
    rw [nhds_prod_eq, mem_map, mem_prod_iff] at this
    rcases this with ⟨t, ht, s, hs, h⟩
    rw [← image_subset_iff, image_mul_prod] at h
    exact ⟨t, mem_nhds_within_of_mem_nhds ht, s, hs, h⟩
    

open MulOpposite

/-- Given a compact set `K` inside an open set `U`, there is a open neighborhood `V` of `1`
  such that `V * K ⊆ U`. -/
@[to_additive
      "Given a compact set `K` inside an open set `U`, there is a open neighborhood `V` of\n`0` such that `V + K ⊆ U`."]
theorem compact_open_separated_mul_left {K U : Set G} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ V ∈ 𝓝 (1 : G), V * K ⊆ U := by
  rcases compact_open_separated_mul_right (hK.image continuous_op) (op_homeomorph.is_open_map U hU)
      (image_subset op hKU) with
    ⟨V, hV : V ∈ 𝓝 (op (1 : G)), hV' : op '' K * V ⊆ op '' U⟩
  refine' ⟨op ⁻¹' V, continuous_op.continuous_at hV, _⟩
  rwa [← image_preimage_eq V op_surjective, ← image_op_mul, image_subset_iff, preimage_image_eq _ op_injective] at hV'

/-- A compact set is covered by finitely many left multiplicative translates of a set
  with non-empty interior. -/
@[to_additive "A compact set is covered by finitely many left additive translates of a set\n  with non-empty interior."]
theorem compact_covered_by_mul_left_translates {K V : Set G} (hK : IsCompact K) (hV : (Interior V).Nonempty) :
    ∃ t : Finset G, K ⊆ ⋃ g ∈ t, (fun h => g * h) ⁻¹' V := by
  obtain ⟨t, ht⟩ : ∃ t : Finset G, K ⊆ ⋃ x ∈ t, Interior ((· * ·) x ⁻¹' V) := by
    refine' hK.elim_finite_subcover (fun x => Interior <| (· * ·) x ⁻¹' V) (fun x => is_open_interior) _
    cases' hV with g₀ hg₀
    refine' fun g hg => mem_Union.2 ⟨g₀ * g⁻¹, _⟩
    refine' preimage_interior_subset_interior_preimage (continuous_const.mul continuous_id) _
    rwa [mem_preimage, inv_mul_cancel_right]
  exact ⟨t, subset.trans ht <| Union₂_mono fun g hg => interior_subset⟩

/-- Every locally compact separable topological group is σ-compact.
  Note: this is not true if we drop the topological group hypothesis. -/
@[to_additive SeparableLocallyCompactAddGroup.sigma_compact_space]
instance (priority := 100) SeparableLocallyCompactGroup.sigma_compact_space [SeparableSpace G] [LocallyCompactSpace G] :
    SigmaCompactSpace G := by
  obtain ⟨L, hLc, hL1⟩ := exists_compact_mem_nhds (1 : G)
  refine' ⟨⟨fun n => (fun x => x * dense_seq G n) ⁻¹' L, _, _⟩⟩
  · intro n
    exact (Homeomorph.mulRight _).compact_preimage.mpr hLc
    
  · refine' Union_eq_univ_iff.2 fun x => _
    obtain ⟨_, ⟨n, rfl⟩, hn⟩ : (range (dense_seq G) ∩ (fun y => x * y) ⁻¹' L).Nonempty := by
      rw [← (Homeomorph.mulLeft x).apply_symm_apply 1] at hL1
      exact (dense_range_dense_seq G).inter_nhds_nonempty ((Homeomorph.mulLeft x).Continuous.ContinuousAt <| hL1)
    exact ⟨n, hn⟩
    

/-- Every separated topological group in which there exists a compact set with nonempty interior
is locally compact. -/
@[to_additive]
theorem TopologicalSpace.PositiveCompacts.locally_compact_space_of_group [T2Space G] (K : PositiveCompacts G) :
    LocallyCompactSpace G := by
  refine' locally_compact_of_compact_nhds fun x => _
  obtain ⟨y, hy⟩ := K.interior_nonempty
  let F := Homeomorph.mulLeft (x * y⁻¹)
  refine' ⟨F '' K, _, K.compact.image F.continuous⟩
  suffices F.symm ⁻¹' K ∈ 𝓝 x by
    convert this
    apply Equivₓ.image_eq_preimage
  apply ContinuousAt.preimage_mem_nhds F.symm.continuous.continuous_at
  have : F.symm x = y := by
    simp [← F, ← Homeomorph.mul_left_symm]
  rw [this]
  exact mem_interior_iff_mem_nhds.1 hy

end

section

variable [TopologicalSpace G] [CommGroupₓ G] [TopologicalGroup G]

@[to_additive]
theorem nhds_mul (x y : G) : 𝓝 (x * y) = 𝓝 x * 𝓝 y :=
  filter_eq <|
    Set.ext fun s => by
      rw [← nhds_translation_mul_inv x, ← nhds_translation_mul_inv y, ← nhds_translation_mul_inv (x * y)]
      constructor
      · rintro ⟨t, ht, ts⟩
        rcases exists_nhds_one_split ht with ⟨V, V1, h⟩
        refine' ⟨(fun a => a * x⁻¹) ⁻¹' V, (fun a => a * y⁻¹) ⁻¹' V, ⟨V, V1, subset.refl _⟩, ⟨V, V1, subset.refl _⟩, _⟩
        rintro a ⟨v, w, v_mem, w_mem, rfl⟩
        apply ts
        simpa [← mul_comm, ← mul_assoc, ← mul_left_commₓ] using h (v * x⁻¹) v_mem (w * y⁻¹) w_mem
        
      · rintro ⟨a, c, ⟨b, hb, ba⟩, ⟨d, hd, dc⟩, ac⟩
        refine' ⟨b ∩ d, inter_mem hb hd, fun v => _⟩
        simp only [← preimage_subset_iff, ← mul_inv_rev, ← mem_preimage] at *
        rintro ⟨vb, vd⟩
        refine' ac ⟨v * y⁻¹, y, _, _, _⟩
        · rw [← mul_assoc _ _ _] at vb
          exact ba _ vb
          
        · apply dc y
          rw [mul_right_invₓ]
          exact mem_of_mem_nhds hd
          
        · simp only [← inv_mul_cancel_right]
          
        

/-- On a topological group, `𝓝 : G → filter G` can be promoted to a `mul_hom`. -/
@[to_additive "On an additive topological group, `𝓝 : G → filter G` can be promoted to an\n`add_hom`.", simps]
def nhdsMulHom : G →ₙ* Filter G where
  toFun := 𝓝
  map_mul' := fun _ _ => nhds_mul _ _

end

end FilterMul

instance Additive.topological_add_group {G} [h : TopologicalSpace G] [Groupₓ G] [TopologicalGroup G] :
    @TopologicalAddGroup (Additive G) h _ where continuous_neg := @continuous_inv G _ _ _

instance Multiplicative.topological_group {G} [h : TopologicalSpace G] [AddGroupₓ G] [TopologicalAddGroup G] :
    @TopologicalGroup (Multiplicative G) h _ where continuous_inv := @continuous_neg G _ _ _

section Quotientₓ

variable [Groupₓ G] [TopologicalSpace G] [TopologicalGroup G] {Γ : Subgroup G}

@[to_additive]
instance QuotientGroup.has_continuous_const_smul :
    HasContinuousConstSmul G (G ⧸ Γ) where continuous_const_smul := fun g₀ => by
    apply continuous_coinduced_dom
    change Continuous fun g : G => QuotientGroup.mk (g₀ * g)
    exact continuous_coinduced_rng.comp (continuous_mul_left g₀)

@[to_additive]
theorem QuotientGroup.continuous_smul₁ (x : G ⧸ Γ) : Continuous fun g : G => g • x := by
  obtain ⟨g₀, rfl⟩ : ∃ g₀, QuotientGroup.mk g₀ = x := @Quotientₓ.exists_rep _ (QuotientGroup.leftRel Γ) x
  change Continuous fun g => QuotientGroup.mk (g * g₀)
  exact continuous_coinduced_rng.comp (continuous_mul_right g₀)

@[to_additive]
instance QuotientGroup.has_continuous_smul [LocallyCompactSpace G] :
    HasContinuousSmul G (G ⧸ Γ) where continuous_smul := by
    let F : G × G ⧸ Γ → G ⧸ Γ := fun p => p.1 • p.2
    change Continuous F
    have H : Continuous (F ∘ fun p : G × G => (p.1, QuotientGroup.mk p.2)) := by
      change Continuous fun p : G × G => QuotientGroup.mk (p.1 * p.2)
      refine' continuous_coinduced_rng.comp continuous_mul
    exact QuotientMap.continuous_lift_prod_right quotient_map_quotient_mk H

end Quotientₓ

namespace Units

open MulOpposite (continuous_op continuous_unop)

variable [Monoidₓ α] [TopologicalSpace α] [HasContinuousMul α] [Monoidₓ β] [TopologicalSpace β] [HasContinuousMul β]

@[to_additive]
instance :
    TopologicalGroup
      αˣ where continuous_inv :=
    continuous_induced_rng
      ((continuous_unop.comp (@continuous_embed_product α _ _).snd).prod_mk (continuous_op.comp continuous_coe))

/-- The topological group isomorphism between the units of a product of two monoids, and the product
    of the units of each monoid. -/
def Homeomorph.prodUnits : Homeomorph (α × β)ˣ (αˣ × βˣ) :=
  { MulEquiv.prodUnits with
    continuous_to_fun := by
      show Continuous fun i : (α × β)ˣ => (map (MonoidHom.fst α β) i, map (MonoidHom.snd α β) i)
      refine' Continuous.prod_mk _ _
      · refine' continuous_induced_rng ((continuous_fst.comp Units.continuous_coe).prod_mk _)
        refine' mul_opposite.continuous_op.comp (continuous_fst.comp _)
        simp_rw [Units.inv_eq_coe_inv]
        exact units.continuous_coe.comp continuous_inv
        
      · refine' continuous_induced_rng ((continuous_snd.comp Units.continuous_coe).prod_mk _)
        simp_rw [Units.coe_map_inv]
        exact continuous_op.comp (continuous_snd.comp (units.continuous_coe.comp continuous_inv))
        ,
    continuous_inv_fun := by
      refine' continuous_induced_rng (Continuous.prod_mk _ _)
      · exact (units.continuous_coe.comp continuous_fst).prod_mk (units.continuous_coe.comp continuous_snd)
        
      · refine' continuous_op.comp (units.continuous_coe.comp <| continuous_induced_rng <| Continuous.prod_mk _ _)
        · exact
            (units.continuous_coe.comp (continuous_inv.comp continuous_fst)).prod_mk
              (units.continuous_coe.comp (continuous_inv.comp continuous_snd))
          
        · exact
            continuous_op.comp
              ((units.continuous_coe.comp continuous_fst).prod_mk (units.continuous_coe.comp continuous_snd))
          
         }

end Units

section LatticeOps

variable {ι : Sort _} [Groupₓ G] [Groupₓ H] {ts : Set (TopologicalSpace G)}
  (h : ∀, ∀ t ∈ ts, ∀, @TopologicalGroup G t _) {ts' : ι → TopologicalSpace G} (h' : ∀ i, @TopologicalGroup G (ts' i) _)
  {t₁ t₂ : TopologicalSpace G} (h₁ : @TopologicalGroup G t₁ _) (h₂ : @TopologicalGroup G t₂ _) {t : TopologicalSpace H}
  [TopologicalGroup H] {F : Type _} [MonoidHomClass F G H] (f : F)

@[to_additive]
theorem topological_group_Inf : @TopologicalGroup G (inf ts) _ :=
  { continuous_inv :=
      @HasContinuousInv.continuous_inv G (inf ts) _
        (@has_continuous_inv_Inf _ _ _ fun t ht => @TopologicalGroup.to_has_continuous_inv G t _ (h t ht)),
    continuous_mul :=
      @HasContinuousMul.continuous_mul G (inf ts) _
        (@has_continuous_mul_Inf _ _ _ fun t ht => @TopologicalGroup.to_has_continuous_mul G t _ (h t ht)) }

include h'

@[to_additive]
theorem topological_group_infi : @TopologicalGroup G (⨅ i, ts' i) _ := by
  rw [← Inf_range]
  exact topological_group_Inf (set.forall_range_iff.mpr h')

omit h'

include h₁ h₂

@[to_additive]
theorem topological_group_inf : @TopologicalGroup G (t₁⊓t₂) _ := by
  rw [inf_eq_infi]
  refine' topological_group_infi fun b => _
  cases b <;> assumption

omit h₁ h₂

@[to_additive]
theorem topological_group_induced : @TopologicalGroup G (t.induced f) _ :=
  { continuous_inv := by
      let this : TopologicalSpace G := t.induced f
      refine' continuous_induced_rng _
      simp_rw [Function.comp, map_inv]
      exact continuous_inv.comp (continuous_induced_dom : Continuous f),
    continuous_mul :=
      @HasContinuousMul.continuous_mul G (t.induced f) _ (@has_continuous_mul_induced G H _ _ t _ _ _ f) }

end LatticeOps

/-!
### Lattice of group topologies
We define a type class `group_topology α` which endows a group `α` with a topology such that all
group operations are continuous.

Group topologies on a fixed group `α` are ordered, by reverse inclusion. They form a complete
lattice, with `⊥` the discrete topology and `⊤` the indiscrete topology.

Any function `f : α → β` induces `coinduced f : topological_space α → group_topology β`.

The additive version `add_group_topology α` and corresponding results are provided as well.
-/


/-- A group topology on a group `α` is a topology for which multiplication and inversion
are continuous. -/
structure GroupTopology (α : Type u) [Groupₓ α] extends TopologicalSpace α, TopologicalGroup α : Type u

/-- An additive group topology on an additive group `α` is a topology for which addition and
  negation are continuous. -/
structure AddGroupTopology (α : Type u) [AddGroupₓ α] extends TopologicalSpace α, TopologicalAddGroup α : Type u

attribute [to_additive] GroupTopology

namespace GroupTopology

variable [Groupₓ α]

/-- A version of the global `continuous_mul` suitable for dot notation. -/
@[to_additive]
theorem continuous_mul' (g : GroupTopology α) :
    have := g.to_topological_space
    Continuous fun p : α × α => p.1 * p.2 :=
  by
  let this := g.to_topological_space
  have := g.to_topological_group
  exact continuous_mul

/-- A version of the global `continuous_inv` suitable for dot notation. -/
@[to_additive]
theorem continuous_inv' (g : GroupTopology α) :
    have := g.to_topological_space
    Continuous (Inv.inv : α → α) :=
  by
  let this := g.to_topological_space
  have := g.to_topological_group
  exact continuous_inv

@[to_additive]
theorem to_topological_space_injective :
    Function.Injective (toTopologicalSpace : GroupTopology α → TopologicalSpace α) := fun f g h => by
  cases f
  cases g
  congr

@[ext, to_additive]
theorem ext' {f g : GroupTopology α} (h : f.IsOpen = g.IsOpen) : f = g :=
  to_topological_space_injective <| topological_space_eq h

/-- The ordering on group topologies on the group `γ`.
  `t ≤ s` if every set open in `s` is also open in `t` (`t` is finer than `s`). -/
@[to_additive]
instance : PartialOrderₓ (GroupTopology α) :=
  PartialOrderₓ.lift toTopologicalSpace to_topological_space_injective

@[simp, to_additive]
theorem to_topological_space_le {x y : GroupTopology α} : x.toTopologicalSpace ≤ y.toTopologicalSpace ↔ x ≤ y :=
  Iff.rfl

@[to_additive]
instance : HasTop (GroupTopology α) :=
  ⟨{ toTopologicalSpace := ⊤, continuous_mul := continuous_top, continuous_inv := continuous_top }⟩

@[simp, to_additive]
theorem to_topological_space_top : (⊤ : GroupTopology α).toTopologicalSpace = ⊤ :=
  rfl

@[to_additive]
instance : HasBot (GroupTopology α) :=
  ⟨{ toTopologicalSpace := ⊥,
      continuous_mul := by
        continuity,
      continuous_inv := continuous_bot }⟩

@[simp, to_additive]
theorem to_topological_space_bot : (⊥ : GroupTopology α).toTopologicalSpace = ⊥ :=
  rfl

@[to_additive]
instance : BoundedOrder (GroupTopology α) where
  top := ⊤
  le_top := fun x => show x.toTopologicalSpace ≤ ⊤ from le_top
  bot := ⊥
  bot_le := fun x => show ⊥ ≤ x.toTopologicalSpace from bot_le

@[to_additive]
instance :
    HasInf
      (GroupTopology
        α) where inf := fun x y =>
    { toTopologicalSpace := x.toTopologicalSpace⊓y.toTopologicalSpace,
      continuous_mul :=
        continuous_inf_rng (continuous_inf_dom_left₂ x.continuous_mul') (continuous_inf_dom_right₂ y.continuous_mul'),
      continuous_inv :=
        continuous_inf_rng (continuous_inf_dom_left x.continuous_inv') (continuous_inf_dom_right y.continuous_inv') }

@[simp, to_additive]
theorem to_topological_space_inf (x y : GroupTopology α) :
    (x⊓y).toTopologicalSpace = x.toTopologicalSpace⊓y.toTopologicalSpace :=
  rfl

@[to_additive]
instance : SemilatticeInf (GroupTopology α) :=
  to_topological_space_injective.SemilatticeInf _ to_topological_space_inf

@[to_additive]
instance : Inhabited (GroupTopology α) :=
  ⟨⊤⟩

-- mathport name: «exprcont»
local notation "cont" => @Continuous _ _

@[to_additive "Infimum of a collection of additive group topologies"]
instance :
    HasInfₓ
      (GroupTopology
        α) where inf := fun S =>
    { toTopologicalSpace := inf (to_topological_space '' S),
      continuous_mul :=
        continuous_Inf_rng
          (by
            rintro _ ⟨⟨t, tr⟩, haS, rfl⟩
            skip
            exact
              continuous_Inf_dom₂ (Set.mem_image_of_mem to_topological_space haS)
                (Set.mem_image_of_mem to_topological_space haS) continuous_mul),
      continuous_inv :=
        continuous_Inf_rng
          (by
            rintro _ ⟨⟨t, tr⟩, haS, rfl⟩
            skip
            exact continuous_Inf_dom (Set.mem_image_of_mem to_topological_space haS) continuous_inv) }

@[simp, to_additive]
theorem to_topological_space_Inf (s : Set (GroupTopology α)) :
    (inf s).toTopologicalSpace = inf (to_topological_space '' s) :=
  rfl

@[simp, to_additive]
theorem to_topological_space_infi {ι} (s : ι → GroupTopology α) :
    (⨅ i, s i).toTopologicalSpace = ⨅ i, (s i).toTopologicalSpace :=
  congr_arg inf (range_comp _ _).symm

/-- Group topologies on `γ` form a complete lattice, with `⊥` the discrete topology and `⊤` the
indiscrete topology.

The infimum of a collection of group topologies is the topology generated by all their open sets
(which is a group topology).

The supremum of two group topologies `s` and `t` is the infimum of the family of all group
topologies contained in the intersection of `s` and `t`. -/
@[to_additive]
instance : CompleteSemilatticeInf (GroupTopology α) :=
  { GroupTopology.hasInfₓ, GroupTopology.partialOrder with
    Inf_le := fun S a haS => to_topological_space_le.1 <| Inf_le ⟨a, haS, rfl⟩,
    le_Inf := by
      intro S a hab
      apply topological_space.complete_lattice.le_Inf
      rintro _ ⟨b, hbS, rfl⟩
      exact hab b hbS }

@[to_additive]
instance : CompleteLattice (GroupTopology α) :=
  { GroupTopology.boundedOrder, GroupTopology.semilatticeInf, completeLatticeOfCompleteSemilatticeInf _ with
    inf := (·⊓·), top := ⊤, bot := ⊥ }

/-- Given `f : α → β` and a topology on `α`, the coinduced group topology on `β` is the finest
topology such that `f` is continuous and `β` is a topological group. -/
@[to_additive
      "Given `f : α → β` and a topology on `α`, the coinduced additive group topology on `β`\nis the finest topology such that `f` is continuous and `β` is a topological additive group."]
def coinduced {α β : Type _} [t : TopologicalSpace α] [Groupₓ β] (f : α → β) : GroupTopology β :=
  inf { b : GroupTopology β | TopologicalSpace.coinduced f t ≤ b.toTopologicalSpace }

@[to_additive]
theorem coinduced_continuous {α β : Type _} [t : TopologicalSpace α] [Groupₓ β] (f : α → β) :
    cont t (coinduced f).toTopologicalSpace f := by
  rw [continuous_iff_coinduced_le]
  refine' le_Inf _
  rintro _ ⟨t', ht', rfl⟩
  exact ht'

end GroupTopology

