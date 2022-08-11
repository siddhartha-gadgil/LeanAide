/-
Copyright (c) 2021 Alex Kontorovich, Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Kontorovich, Heather Macbeth
-/
import Mathbin.Topology.Algebra.Constructions
import Mathbin.Topology.Homeomorph
import Mathbin.GroupTheory.GroupAction.Basic

/-!
# Monoid actions continuous in the second variable

In this file we define class `has_continuous_const_smul`. We say `has_continuous_const_smul Γ T` if
`Γ` acts on `T` and for each `γ`, the map `x ↦ γ • x` is continuous. (This differs from
`has_continuous_smul`, which requires simultaneous continuity in both variables.)

## Main definitions

* `has_continuous_const_smul Γ T` : typeclass saying that the map `x ↦ γ • x` is continuous on `T`;
* `properly_discontinuous_smul`: says that the scalar multiplication `(•) : Γ → T → T`
  is properly discontinuous, that is, for any pair of compact sets `K, L` in `T`, only finitely
  many `γ:Γ` move `K` to have nontrivial intersection with `L`.
* `homeomorph.smul`: scalar multiplication by an element of a group `Γ` acting on `T`
  is a homeomorphism of `T`.

## Main results

* `is_open_map_quotient_mk_mul` : The quotient map by a group action is open.
* `t2_space_of_properly_discontinuous_smul_of_t2_space` : The quotient by a discontinuous group
  action of a locally compact t2 space is t2.

## Tags

Hausdorff, discrete group, properly discontinuous, quotient space

-/


open TopologicalSpace Pointwise

open Filter Set

attribute [local instance] MulAction.orbitRel

/-- Class `has_continuous_const_smul Γ T` says that the scalar multiplication `(•) : Γ → T → T`
is continuous in the second argument. We use the same class for all kinds of multiplicative
actions, including (semi)modules and algebras.
-/
class HasContinuousConstSmul (Γ : Type _) (T : Type _) [TopologicalSpace T] [HasSmul Γ T] : Prop where
  continuous_const_smul : ∀ γ : Γ, Continuous fun x : T => γ • x

/-- Class `has_continuous_const_vadd Γ T` says that the additive action `(+ᵥ) : Γ → T → T`
is continuous in the second argument. We use the same class for all kinds of additive actions,
including (semi)modules and algebras.
-/
class HasContinuousConstVadd (Γ : Type _) (T : Type _) [TopologicalSpace T] [HasVadd Γ T] : Prop where
  continuous_const_vadd : ∀ γ : Γ, Continuous fun x : T => γ +ᵥ x

attribute [to_additive] HasContinuousConstSmul

export HasContinuousConstSmul (continuous_const_smul)

export HasContinuousConstVadd (continuous_const_vadd)

variable {M α β : Type _}

section HasSmul

variable [TopologicalSpace α] [HasSmul M α] [HasContinuousConstSmul M α]

@[to_additive]
theorem Filter.Tendsto.const_smul {f : β → α} {l : Filter β} {a : α} (hf : Tendsto f l (𝓝 a)) (c : M) :
    Tendsto (fun x => c • f x) l (𝓝 (c • a)) :=
  ((continuous_const_smul _).Tendsto _).comp hf

variable [TopologicalSpace β] {f : β → M} {g : β → α} {b : β} {s : Set β}

@[to_additive]
theorem ContinuousWithinAt.const_smul (hg : ContinuousWithinAt g s b) (c : M) :
    ContinuousWithinAt (fun x => c • g x) s b :=
  hg.const_smul c

@[to_additive]
theorem ContinuousAt.const_smul (hg : ContinuousAt g b) (c : M) : ContinuousAt (fun x => c • g x) b :=
  hg.const_smul c

@[to_additive]
theorem ContinuousOn.const_smul (hg : ContinuousOn g s) (c : M) : ContinuousOn (fun x => c • g x) s := fun x hx =>
  (hg x hx).const_smul c

@[continuity, to_additive]
theorem Continuous.const_smul (hg : Continuous g) (c : M) : Continuous fun x => c • g x :=
  (continuous_const_smul _).comp hg

/-- If a scalar is central, then its right action is continuous when its left action is. -/
instance HasContinuousConstSmul.op [HasSmul Mᵐᵒᵖ α] [IsCentralScalar M α] : HasContinuousConstSmul Mᵐᵒᵖ α :=
  ⟨MulOpposite.rec fun c => by
      simpa only [← op_smul_eq_smul] using continuous_const_smul c⟩

@[to_additive]
instance MulOpposite.has_continuous_const_smul : HasContinuousConstSmul M αᵐᵒᵖ :=
  ⟨fun c => MulOpposite.continuous_op.comp <| MulOpposite.continuous_unop.const_smul c⟩

@[to_additive]
instance [HasSmul M β] [HasContinuousConstSmul M β] : HasContinuousConstSmul M (α × β) :=
  ⟨fun _ => (continuous_fst.const_smul _).prod_mk (continuous_snd.const_smul _)⟩

@[to_additive]
instance {ι : Type _} {γ : ι → Type _} [∀ i, TopologicalSpace (γ i)] [∀ i, HasSmul M (γ i)]
    [∀ i, HasContinuousConstSmul M (γ i)] : HasContinuousConstSmul M (∀ i, γ i) :=
  ⟨fun _ => continuous_pi fun i => (continuous_apply i).const_smul _⟩

end HasSmul

section Monoidₓ

variable [TopologicalSpace α]

variable [Monoidₓ M] [MulAction M α] [HasContinuousConstSmul M α]

@[to_additive]
instance Units.has_continuous_const_smul :
    HasContinuousConstSmul Mˣ α where continuous_const_smul := fun m => (continuous_const_smul (m : M) : _)

@[to_additive]
theorem smul_closure_subset (c : M) (s : Set α) : c • Closure s ⊆ Closure (c • s) :=
  ((Set.maps_to_image _ _).closure <| continuous_id.const_smul c).image_subset

@[to_additive]
theorem smul_closure_orbit_subset (c : M) (x : α) : c • Closure (MulAction.Orbit M x) ⊆ Closure (MulAction.Orbit M x) :=
  (smul_closure_subset c _).trans <| closure_mono <| MulAction.smul_orbit_subset _ _

end Monoidₓ

section Groupₓ

variable {G : Type _} [TopologicalSpace α] [Groupₓ G] [MulAction G α] [HasContinuousConstSmul G α]

@[to_additive]
theorem tendsto_const_smul_iff {f : β → α} {l : Filter β} {a : α} (c : G) :
    Tendsto (fun x => c • f x) l (𝓝 <| c • a) ↔ Tendsto f l (𝓝 a) :=
  ⟨fun h => by
    simpa only [← inv_smul_smul] using h.const_smul c⁻¹, fun h => h.const_smul _⟩

variable [TopologicalSpace β] {f : β → α} {b : β} {s : Set β}

@[to_additive]
theorem continuous_within_at_const_smul_iff (c : G) :
    ContinuousWithinAt (fun x => c • f x) s b ↔ ContinuousWithinAt f s b :=
  tendsto_const_smul_iff c

@[to_additive]
theorem continuous_on_const_smul_iff (c : G) : ContinuousOn (fun x => c • f x) s ↔ ContinuousOn f s :=
  forall₂_congrₓ fun b hb => continuous_within_at_const_smul_iff c

@[to_additive]
theorem continuous_at_const_smul_iff (c : G) : ContinuousAt (fun x => c • f x) b ↔ ContinuousAt f b :=
  tendsto_const_smul_iff c

@[to_additive]
theorem continuous_const_smul_iff (c : G) : (Continuous fun x => c • f x) ↔ Continuous f := by
  simp only [← continuous_iff_continuous_at, ← continuous_at_const_smul_iff]

/-- The homeomorphism given by scalar multiplication by a given element of a group `Γ` acting on
  `T` is a homeomorphism from `T` to itself. -/
@[to_additive]
def Homeomorph.smul (γ : G) : α ≃ₜ α where
  toEquiv := MulAction.toPerm γ
  continuous_to_fun := continuous_const_smul γ
  continuous_inv_fun := continuous_const_smul γ⁻¹

/-- The homeomorphism given by affine-addition by an element of an additive group `Γ` acting on
  `T` is a homeomorphism from `T` to itself. -/
add_decl_doc Homeomorph.vadd

@[to_additive]
theorem is_open_map_smul (c : G) : IsOpenMap fun x : α => c • x :=
  (Homeomorph.smul c).IsOpenMap

@[to_additive]
theorem IsOpen.smul {s : Set α} (hs : IsOpen s) (c : G) : IsOpen (c • s) :=
  is_open_map_smul c s hs

@[to_additive]
theorem is_closed_map_smul (c : G) : IsClosedMap fun x : α => c • x :=
  (Homeomorph.smul c).IsClosedMap

@[to_additive]
theorem IsClosed.smul {s : Set α} (hs : IsClosed s) (c : G) : IsClosed (c • s) :=
  is_closed_map_smul c s hs

@[to_additive]
theorem closure_smul (c : G) (s : Set α) : Closure (c • s) = c • Closure s :=
  ((Homeomorph.smul c).image_closure s).symm

@[to_additive]
theorem interior_smul (c : G) (s : Set α) : Interior (c • s) = c • Interior s :=
  ((Homeomorph.smul c).image_interior s).symm

end Groupₓ

section GroupWithZeroₓ

variable {G₀ : Type _} [TopologicalSpace α] [GroupWithZeroₓ G₀] [MulAction G₀ α] [HasContinuousConstSmul G₀ α]

theorem tendsto_const_smul_iff₀ {f : β → α} {l : Filter β} {a : α} {c : G₀} (hc : c ≠ 0) :
    Tendsto (fun x => c • f x) l (𝓝 <| c • a) ↔ Tendsto f l (𝓝 a) :=
  tendsto_const_smul_iff (Units.mk0 c hc)

variable [TopologicalSpace β] {f : β → α} {b : β} {c : G₀} {s : Set β}

theorem continuous_within_at_const_smul_iff₀ (hc : c ≠ 0) :
    ContinuousWithinAt (fun x => c • f x) s b ↔ ContinuousWithinAt f s b :=
  tendsto_const_smul_iff (Units.mk0 c hc)

theorem continuous_on_const_smul_iff₀ (hc : c ≠ 0) : ContinuousOn (fun x => c • f x) s ↔ ContinuousOn f s :=
  continuous_on_const_smul_iff (Units.mk0 c hc)

theorem continuous_at_const_smul_iff₀ (hc : c ≠ 0) : ContinuousAt (fun x => c • f x) b ↔ ContinuousAt f b :=
  continuous_at_const_smul_iff (Units.mk0 c hc)

theorem continuous_const_smul_iff₀ (hc : c ≠ 0) : (Continuous fun x => c • f x) ↔ Continuous f :=
  continuous_const_smul_iff (Units.mk0 c hc)

/-- Scalar multiplication by a non-zero element of a group with zero acting on `α` is a
homeomorphism from `α` onto itself. -/
protected def Homeomorph.smulOfNeZero (c : G₀) (hc : c ≠ 0) : α ≃ₜ α :=
  Homeomorph.smul (Units.mk0 c hc)

theorem is_open_map_smul₀ {c : G₀} (hc : c ≠ 0) : IsOpenMap fun x : α => c • x :=
  (Homeomorph.smulOfNeZero c hc).IsOpenMap

theorem IsOpen.smul₀ {c : G₀} {s : Set α} (hs : IsOpen s) (hc : c ≠ 0) : IsOpen (c • s) :=
  is_open_map_smul₀ hc s hs

theorem interior_smul₀ {c : G₀} (hc : c ≠ 0) (s : Set α) : Interior (c • s) = c • Interior s :=
  ((Homeomorph.smulOfNeZero c hc).image_interior s).symm

theorem closure_smul₀ {E} [Zero E] [MulActionWithZero G₀ E] [TopologicalSpace E] [T1Space E]
    [HasContinuousConstSmul G₀ E] (c : G₀) (s : Set E) : Closure (c • s) = c • Closure s := by
  rcases eq_or_ne c 0 with (rfl | hc)
  · rcases eq_empty_or_nonempty s with (rfl | hs)
    · simp
      
    · rw [zero_smul_set hs, zero_smul_set hs.closure]
      exact closure_singleton
      
    
  · exact ((Homeomorph.smulOfNeZero c hc).image_closure s).symm
    

/-- `smul` is a closed map in the second argument.

The lemma that `smul` is a closed map in the first argument (for a normed space over a complete
normed field) is `is_closed_map_smul_left` in `analysis.normed_space.finite_dimension`. -/
theorem is_closed_map_smul_of_ne_zero {c : G₀} (hc : c ≠ 0) : IsClosedMap fun x : α => c • x :=
  (Homeomorph.smulOfNeZero c hc).IsClosedMap

theorem IsClosed.smul_of_ne_zero {c : G₀} {s : Set α} (hs : IsClosed s) (hc : c ≠ 0) : IsClosed (c • s) :=
  is_closed_map_smul_of_ne_zero hc s hs

/-- `smul` is a closed map in the second argument.

The lemma that `smul` is a closed map in the first argument (for a normed space over a complete
normed field) is `is_closed_map_smul_left` in `analysis.normed_space.finite_dimension`. -/
theorem is_closed_map_smul₀ {𝕜 M : Type _} [DivisionRing 𝕜] [AddCommMonoidₓ M] [TopologicalSpace M] [T1Space M]
    [Module 𝕜 M] [HasContinuousConstSmul 𝕜 M] (c : 𝕜) : IsClosedMap fun x : M => c • x := by
  rcases eq_or_ne c 0 with (rfl | hne)
  · simp only [← zero_smul]
    exact is_closed_map_const
    
  · exact (Homeomorph.smulOfNeZero c hne).IsClosedMap
    

theorem IsClosed.smul₀ {𝕜 M : Type _} [DivisionRing 𝕜] [AddCommMonoidₓ M] [TopologicalSpace M] [T1Space M] [Module 𝕜 M]
    [HasContinuousConstSmul 𝕜 M] (c : 𝕜) {s : Set M} (hs : IsClosed s) : IsClosed (c • s) :=
  is_closed_map_smul₀ c s hs

end GroupWithZeroₓ

namespace IsUnit

variable [Monoidₓ M] [TopologicalSpace α] [MulAction M α] [HasContinuousConstSmul M α]

theorem tendsto_const_smul_iff {f : β → α} {l : Filter β} {a : α} {c : M} (hc : IsUnit c) :
    Tendsto (fun x => c • f x) l (𝓝 <| c • a) ↔ Tendsto f l (𝓝 a) :=
  let ⟨u, hu⟩ := hc
  hu ▸ tendsto_const_smul_iff u

variable [TopologicalSpace β] {f : β → α} {b : β} {c : M} {s : Set β}

theorem continuous_within_at_const_smul_iff (hc : IsUnit c) :
    ContinuousWithinAt (fun x => c • f x) s b ↔ ContinuousWithinAt f s b :=
  let ⟨u, hu⟩ := hc
  hu ▸ continuous_within_at_const_smul_iff u

theorem continuous_on_const_smul_iff (hc : IsUnit c) : ContinuousOn (fun x => c • f x) s ↔ ContinuousOn f s :=
  let ⟨u, hu⟩ := hc
  hu ▸ continuous_on_const_smul_iff u

theorem continuous_at_const_smul_iff (hc : IsUnit c) : ContinuousAt (fun x => c • f x) b ↔ ContinuousAt f b :=
  let ⟨u, hu⟩ := hc
  hu ▸ continuous_at_const_smul_iff u

theorem continuous_const_smul_iff (hc : IsUnit c) : (Continuous fun x => c • f x) ↔ Continuous f :=
  let ⟨u, hu⟩ := hc
  hu ▸ continuous_const_smul_iff u

theorem is_open_map_smul (hc : IsUnit c) : IsOpenMap fun x : α => c • x :=
  let ⟨u, hu⟩ := hc
  hu ▸ is_open_map_smul u

theorem is_closed_map_smul (hc : IsUnit c) : IsClosedMap fun x : α => c • x :=
  let ⟨u, hu⟩ := hc
  hu ▸ is_closed_map_smul u

end IsUnit

/-- Class `properly_discontinuous_smul Γ T` says that the scalar multiplication `(•) : Γ → T → T`
is properly discontinuous, that is, for any pair of compact sets `K, L` in `T`, only finitely many
`γ:Γ` move `K` to have nontrivial intersection with `L`.
-/
class ProperlyDiscontinuousSmul (Γ : Type _) (T : Type _) [TopologicalSpace T] [HasSmul Γ T] : Prop where
  finite_disjoint_inter_image :
    ∀ {K L : Set T}, IsCompact K → IsCompact L → Set.Finite { γ : Γ | (· • ·) γ '' K ∩ L ≠ ∅ }

/-- Class `properly_discontinuous_vadd Γ T` says that the additive action `(+ᵥ) : Γ → T → T`
is properly discontinuous, that is, for any pair of compact sets `K, L` in `T`, only finitely many
`γ:Γ` move `K` to have nontrivial intersection with `L`.
-/
class ProperlyDiscontinuousVadd (Γ : Type _) (T : Type _) [TopologicalSpace T] [HasVadd Γ T] : Prop where
  finite_disjoint_inter_image :
    ∀ {K L : Set T}, IsCompact K → IsCompact L → Set.Finite { γ : Γ | (· +ᵥ ·) γ '' K ∩ L ≠ ∅ }

attribute [to_additive] ProperlyDiscontinuousSmul

variable {Γ : Type _} [Groupₓ Γ] {T : Type _} [TopologicalSpace T] [MulAction Γ T]

/-- A finite group action is always properly discontinuous
-/
@[to_additive]
instance (priority := 100) Fintype.properly_discontinuous_smul [Fintype Γ] :
    ProperlyDiscontinuousSmul Γ T where finite_disjoint_inter_image := fun _ _ _ _ => Set.to_finite _

export ProperlyDiscontinuousSmul (finite_disjoint_inter_image)

export ProperlyDiscontinuousVadd (finite_disjoint_inter_image)

/-- The quotient map by a group action is open. -/
@[to_additive]
theorem is_open_map_quotient_mk_mul [HasContinuousConstSmul Γ T] :
    IsOpenMap (Quotientₓ.mk : T → Quotientₓ (MulAction.orbitRel Γ T)) := by
  intro U hU
  rw [is_open_coinduced, MulAction.quotient_preimage_image_eq_union_mul U]
  exact is_open_Union fun γ => (Homeomorph.smul γ).IsOpenMap U hU

/-- The quotient by a discontinuous group action of a locally compact t2 space is t2. -/
@[to_additive]
instance (priority := 100) t2_space_of_properly_discontinuous_smul_of_t2_space [T2Space T] [LocallyCompactSpace T]
    [HasContinuousConstSmul Γ T] [ProperlyDiscontinuousSmul Γ T] : T2Space (Quotientₓ (MulAction.orbitRel Γ T)) := by
  set Q := Quotientₓ (MulAction.orbitRel Γ T)
  rw [t2_space_iff_nhds]
  let f : T → Q := Quotientₓ.mk
  have f_op : IsOpenMap f := is_open_map_quotient_mk_mul
  rintro ⟨x₀⟩ ⟨y₀⟩ (hxy : f x₀ ≠ f y₀)
  show ∃ U ∈ 𝓝 (f x₀), ∃ V ∈ 𝓝 (f y₀), _
  have hx₀y₀ : x₀ ≠ y₀ := ne_of_apply_ne _ hxy
  have hγx₀y₀ : ∀ γ : Γ, γ • x₀ ≠ y₀ := not_exists.mp (mt Quotientₓ.sound hxy.symm : _)
  obtain ⟨K₀, L₀, K₀_in, L₀_in, hK₀, hL₀, hK₀L₀⟩ := t2_separation_compact_nhds hx₀y₀
  let bad_Γ_set := { γ : Γ | (· • ·) γ '' K₀ ∩ L₀ ≠ ∅ }
  have bad_Γ_finite : bad_Γ_set.finite := finite_disjoint_inter_image hK₀ hL₀
  choose u v hu hv u_v_disjoint using fun γ => t2_separation_nhds (hγx₀y₀ γ)
  let U₀₀ := ⋂ γ ∈ bad_Γ_set, (· • ·) γ ⁻¹' u γ
  let U₀ := U₀₀ ∩ K₀
  let V₀₀ := ⋂ γ ∈ bad_Γ_set, v γ
  let V₀ := V₀₀ ∩ L₀
  have U_nhds : f '' U₀ ∈ 𝓝 (f x₀) := by
    apply f_op.image_mem_nhds (inter_mem ((bInter_mem bad_Γ_finite).mpr fun γ hγ => _) K₀_in)
    exact (continuous_const_smul _).ContinuousAt (hu γ)
  have V_nhds : f '' V₀ ∈ 𝓝 (f y₀) :=
    f_op.image_mem_nhds (inter_mem ((bInter_mem bad_Γ_finite).mpr fun γ hγ => hv γ) L₀_in)
  refine' ⟨f '' U₀, U_nhds, f '' V₀, V_nhds, MulAction.disjoint_image_image_iff.2 _⟩
  rintro x ⟨x_in_U₀₀, x_in_K₀⟩ γ
  by_cases' H : γ ∈ bad_Γ_set
  · exact fun h => u_v_disjoint γ ⟨mem_Inter₂.mp x_in_U₀₀ γ H, mem_Inter₂.mp h.1 γ H⟩
    
  · rintro ⟨-, h'⟩
    simp only [← image_smul, ← not_not, ← mem_set_of_eq, ← Ne.def] at H
    exact eq_empty_iff_forall_not_mem.mp H (γ • x) ⟨mem_image_of_mem _ x_in_K₀, h'⟩
    

section nhds

section MulAction

variable {G₀ : Type _} [GroupWithZeroₓ G₀] [MulAction G₀ α] [TopologicalSpace α] [HasContinuousConstSmul G₀ α]

/-- Scalar multiplication preserves neighborhoods. -/
theorem set_smul_mem_nhds_smul {c : G₀} {s : Set α} {x : α} (hs : s ∈ 𝓝 x) (hc : c ≠ 0) : c • s ∈ 𝓝 (c • x : α) := by
  rw [mem_nhds_iff] at hs⊢
  obtain ⟨U, hs', hU, hU'⟩ := hs
  exact ⟨c • U, Set.smul_set_mono hs', hU.smul₀ hc, Set.smul_mem_smul_set hU'⟩

theorem set_smul_mem_nhds_smul_iff {c : G₀} {s : Set α} {x : α} (hc : c ≠ 0) : c • s ∈ 𝓝 (c • x : α) ↔ s ∈ 𝓝 x := by
  refine' ⟨fun h => _, fun h => set_smul_mem_nhds_smul h hc⟩
  rw [← inv_smul_smul₀ hc x, ← inv_smul_smul₀ hc s]
  exact set_smul_mem_nhds_smul h (inv_ne_zero hc)

end MulAction

section DistribMulAction

variable {G₀ : Type _} [GroupWithZeroₓ G₀] [AddMonoidₓ α] [DistribMulAction G₀ α] [TopologicalSpace α]
  [HasContinuousConstSmul G₀ α]

theorem set_smul_mem_nhds_zero_iff {s : Set α} {c : G₀} (hc : c ≠ 0) : c • s ∈ 𝓝 (0 : α) ↔ s ∈ 𝓝 (0 : α) := by
  refine' Iff.trans _ (set_smul_mem_nhds_smul_iff hc)
  rw [smul_zero]

end DistribMulAction

end nhds

