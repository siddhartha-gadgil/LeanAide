/-
Copyright © 2022 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth, Floris van Doorn
-/
import Mathbin.Topology.VectorBundle.Basic
import Mathbin.Analysis.NormedSpace.OperatorNorm

/-!
# The topological vector bundle of continuous (semi)linear maps

We define the topological vector bundle of continuous (semi)linear maps between two
vector bundles over the same base.
Given bundles `E₁ E₂ : B → Type*`, we define
`bundle.continuous_linear_map 𝕜 E₁ E₂ := λ x, E₁ x →SL[𝕜] E₂ x`.
If the `E₁` and `E₂` are topological vector bundles with fibers `F₁` and `F₂`, then this will
be a topological vector bundle with fiber `F₁ →SL[𝕜] F₂`.
The topology is inherited from the norm-topology on, without the need to define the strong
topology on continuous linear maps between general topological vector spaces.

## Main Definitions

* `bundle.continuous_linear_map.topological_vector_bundle`: continuous semilinear maps between
  vector bundles form a vector bundle.

-/


noncomputable section

open Bundle Set ContinuousLinearMap

section Defs

variable {𝕜₁ 𝕜₂ : Type _} [NormedField 𝕜₁] [NormedField 𝕜₂]

variable (σ : 𝕜₁ →+* 𝕜₂)

variable {B : Type _}

variable (F₁ : Type _) (E₁ : B → Type _) [∀ x, AddCommMonoidₓ (E₁ x)] [∀ x, Module 𝕜₁ (E₁ x)]

variable [∀ x : B, TopologicalSpace (E₁ x)]

variable (F₂ : Type _) (E₂ : B → Type _) [∀ x, AddCommMonoidₓ (E₂ x)] [∀ x, Module 𝕜₂ (E₂ x)]

variable [∀ x : B, TopologicalSpace (E₂ x)]

include F₁ F₂

/-- The bundle of continuous `σ`-semilinear maps between the topological vector bundles `E₁` and
`E₂`. This is a type synonym for `λ x, E₁ x →SL[σ] E₂ x`.

We intentionally add `F₁` and `F₂` as arguments to this type, so that instances on this type
(that depend on `F₁` and `F₂`) actually refer to `F₁` and `F₂`. -/
-- In this definition we require the scalar rings `𝕜₁` and `𝕜₂` to be normed fields, although
-- something much weaker (maybe `comm_semiring`) would suffice mathematically -- this is because of
-- a typeclass inference bug with pi-types:
-- https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/vector.20bundles.20--.20typeclass.20inference.20issue
@[nolint unused_arguments]
def Bundle.ContinuousLinearMap (x : B) : Type _ :=
  E₁ x →SL[σ] E₂ x deriving Inhabited

instance Bundle.ContinuousLinearMap.addMonoidHomClass (x : B) :
    AddMonoidHomClass (Bundle.ContinuousLinearMap σ F₁ E₁ F₂ E₂ x) (E₁ x) (E₂ x) := by
  delta_instance bundle.continuous_linear_map

variable [∀ x, HasContinuousAdd (E₂ x)]

instance (x : B) : AddCommMonoidₓ (Bundle.ContinuousLinearMap σ F₁ E₁ F₂ E₂ x) := by
  delta_instance bundle.continuous_linear_map

variable [∀ x, HasContinuousSmul 𝕜₂ (E₂ x)]

instance (x : B) : Module 𝕜₂ (Bundle.ContinuousLinearMap σ F₁ E₁ F₂ E₂ x) := by
  delta_instance bundle.continuous_linear_map

end Defs

variable {𝕜₁ : Type _} [NondiscreteNormedField 𝕜₁] {𝕜₂ : Type _} [NondiscreteNormedField 𝕜₂] (σ : 𝕜₁ →+* 𝕜₂)

variable {B : Type _} [TopologicalSpace B]

variable (F₁ : Type _) [NormedGroup F₁] [NormedSpace 𝕜₁ F₁] (E₁ : B → Type _) [∀ x, AddCommMonoidₓ (E₁ x)]
  [∀ x, Module 𝕜₁ (E₁ x)] [TopologicalSpace (TotalSpace E₁)]

variable (F₂ : Type _) [NormedGroup F₂] [NormedSpace 𝕜₂ F₂] (E₂ : B → Type _) [∀ x, AddCommMonoidₓ (E₂ x)]
  [∀ x, Module 𝕜₂ (E₂ x)] [TopologicalSpace (TotalSpace E₂)]

namespace TopologicalVectorBundle

variable {F₁ E₁ F₂ E₂} (e₁ e₁' : Trivialization 𝕜₁ F₁ E₁) (e₂ e₂' : Trivialization 𝕜₂ F₂ E₂)

variable [RingHomIsometric σ]

namespace Pretrivialization

/-- Assume `eᵢ` and `eᵢ'` are trivializations of the bundles `Eᵢ` over base `B` with fiber `Fᵢ`
(`i ∈ {1,2}`), then `continuous_linear_map_coord_change σ e₁ e₁' e₂ e₂'` is the coordinate change
function between the two induced (pre)trivializations
`pretrivialization.continuous_linear_map σ e₁ e₂` and
`pretrivialization.continuous_linear_map σ e₁' e₂'` of `bundle.continuous_linear_map`. -/
def continuousLinearMapCoordChange (b : B) : (F₁ →SL[σ] F₂) →L[𝕜₂] F₁ →SL[σ] F₂ :=
  ((e₁'.coordChange e₁ b).symm.arrowCongrSL (e₂.coordChange e₂' b) : (F₁ →SL[σ] F₂) ≃L[𝕜₂] F₁ →SL[σ] F₂)

variable {σ e₁ e₁' e₂ e₂'}

variable [∀ x : B, TopologicalSpace (E₁ x)] [TopologicalVectorBundle 𝕜₁ F₁ E₁]

variable [∀ x : B, TopologicalSpace (E₂ x)] [TopologicalVectorBundle 𝕜₂ F₂ E₂]

theorem continuous_on_continuous_linear_map_coord_change (he₁ : e₁ ∈ TrivializationAtlas 𝕜₁ F₁ E₁)
    (he₁' : e₁' ∈ TrivializationAtlas 𝕜₁ F₁ E₁) (he₂ : e₂ ∈ TrivializationAtlas 𝕜₂ F₂ E₂)
    (he₂' : e₂' ∈ TrivializationAtlas 𝕜₂ F₂ E₂) :
    ContinuousOn (continuousLinearMapCoordChange σ e₁ e₁' e₂ e₂')
      (e₁.BaseSet ∩ e₂.BaseSet ∩ (e₁'.BaseSet ∩ e₂'.BaseSet)) :=
  by
  have h₁ := (compSL F₁ F₂ F₂ σ (RingHom.id 𝕜₂)).Continuous
  have h₂ := (ContinuousLinearMap.flip (compSL F₁ F₁ F₂ (RingHom.id 𝕜₁) σ)).Continuous
  have h₃ := continuous_on_coord_change e₁' he₁' e₁ he₁
  have h₄ := continuous_on_coord_change e₂ he₂ e₂' he₂'
  refine' ((h₁.comp_continuous_on (h₄.mono _)).clm_comp (h₂.comp_continuous_on (h₃.mono _))).congr _
  · mfld_set_tac
    
  · mfld_set_tac
    
  · intro b hb
    ext L v
    simp only [← continuous_linear_map_coord_change, ← ContinuousLinearEquiv.coe_coe, ←
      ContinuousLinearEquiv.arrow_congrSL_apply, ← comp_apply, ← Function.comp, ← compSL_apply, ← flip_apply, ←
      ContinuousLinearEquiv.symm_symm]
    

variable (σ e₁ e₁' e₂ e₂')

variable [∀ x, HasContinuousAdd (E₂ x)] [∀ x, HasContinuousSmul 𝕜₂ (E₂ x)]

/-- Given trivializations `e₁`, `e₂` for vector bundles `E₁`, `E₂` over a base `B`,
`pretrivialization.continuous_linear_map σ e₁ e₂` is the induced pretrivialization for the
continuous `σ`-semilinear maps from `E₁` to `E₂`. That is, the map which will later become a
trivialization, after the bundle of continuous semilinear maps is equipped with the right
topological vector bundle structure. -/
def continuousLinearMap : Pretrivialization 𝕜₂ (F₁ →SL[σ] F₂) (Bundle.ContinuousLinearMap σ F₁ E₁ F₂ E₂) where
  toFun := fun p => ⟨p.1, (e₂.continuousLinearMapAt p.1).comp <| p.2.comp <| e₁.symmL p.1⟩
  invFun := fun p => ⟨p.1, (e₂.symmL p.1).comp <| p.2.comp <| e₁.continuousLinearMapAt p.1⟩
  Source := Bundle.TotalSpace.proj ⁻¹' (e₁.BaseSet ∩ e₂.BaseSet)
  Target := (e₁.BaseSet ∩ e₂.BaseSet) ×ˢ (Set.Univ : Set (F₁ →SL[σ] F₂))
  map_source' := fun ⟨x, L⟩ h => ⟨h, Set.mem_univ _⟩
  map_target' := fun ⟨x, f⟩ h => h.1
  left_inv' := fun ⟨x, L⟩ ⟨h₁, h₂⟩ => by
    simp_rw [Sigma.mk.inj_iff, eq_self_iff_true, heq_iff_eq, true_andₓ]
    ext v
    simp only [← comp_apply, ← trivialization.symmL_continuous_linear_map_at, ← h₁, ← h₂]
  right_inv' := fun ⟨x, f⟩ ⟨⟨h₁, h₂⟩, _⟩ => by
    simp_rw [Prod.mk.inj_iff, eq_self_iff_true, true_andₓ]
    ext v
    simp only [← comp_apply, ← trivialization.continuous_linear_map_at_symmL, ← h₁, ← h₂]
  open_target := (e₁.open_base_set.inter e₂.open_base_set).Prod is_open_univ
  BaseSet := e₁.BaseSet ∩ e₂.BaseSet
  open_base_set := e₁.open_base_set.inter e₂.open_base_set
  source_eq := rfl
  target_eq := rfl
  proj_to_fun := fun ⟨x, f⟩ h => rfl
  linear' := fun x h =>
    { map_add := fun L L' => by
        simp_rw [add_comp, comp_add],
      map_smul := fun c L => by
        simp_rw [smul_comp, comp_smulₛₗ, RingHom.id_apply] }

theorem continuous_linear_map_apply (p : TotalSpace (Bundle.ContinuousLinearMap σ F₁ E₁ F₂ E₂)) :
    (continuousLinearMap σ e₁ e₂) p = ⟨p.1, (e₂.continuousLinearMapAt p.1).comp <| p.2.comp <| e₁.symmL p.1⟩ :=
  rfl

theorem continuous_linear_map_symm_apply (p : B × (F₁ →SL[σ] F₂)) :
    (continuousLinearMap σ e₁ e₂).toLocalEquiv.symm p =
      ⟨p.1, (e₂.symmL p.1).comp <| p.2.comp <| e₁.continuousLinearMapAt p.1⟩ :=
  rfl

theorem continuous_linear_map_symm_apply' {b : B} (hb : b ∈ e₁.BaseSet ∩ e₂.BaseSet) (L : F₁ →SL[σ] F₂) :
    (continuousLinearMap σ e₁ e₂).symm b L = (e₂.symmL b).comp (L.comp <| e₁.continuousLinearMapAt b) := by
  rw [symm_apply]
  rfl
  exact hb

theorem continuous_linear_map_coord_change_apply (b : B)
    (hb : b ∈ e₁.BaseSet ∩ e₂.BaseSet ∩ (e₁'.BaseSet ∩ e₂'.BaseSet)) (L : F₁ →SL[σ] F₂) :
    continuousLinearMapCoordChange σ e₁ e₁' e₂ e₂' b L =
      (continuousLinearMap σ e₁' e₂' (totalSpaceMk b ((continuousLinearMap σ e₁ e₂).symm b L))).2 :=
  by
  ext v
  simp_rw [continuous_linear_map_coord_change, ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.arrow_congrSL_apply,
    continuous_linear_map_apply, continuous_linear_map_symm_apply' σ e₁ e₂ hb.1, comp_apply,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_symm, trivialization.continuous_linear_map_at_apply,
    trivialization.symmL_apply]
  dsimp' only [← total_space_mk]
  rw [e₂.coord_change_apply e₂', e₁'.coord_change_apply e₁, e₁.coe_linear_map_at_of_mem hb.1.1,
    e₂'.coe_linear_map_at_of_mem hb.2.2]
  exacts[⟨hb.2.1, hb.1.1⟩, ⟨hb.1.2, hb.2.2⟩]

end Pretrivialization

open Pretrivialization

variable (F₁ E₁ F₂ E₂)

variable [∀ x : B, TopologicalSpace (E₁ x)] [TopologicalVectorBundle 𝕜₁ F₁ E₁]

variable [∀ x : B, TopologicalSpace (E₂ x)] [TopologicalVectorBundle 𝕜₂ F₂ E₂]

variable [∀ x, HasContinuousAdd (E₂ x)] [∀ x, HasContinuousSmul 𝕜₂ (E₂ x)]

/-- The continuous `σ`-semilinear maps between two topological vector bundles form a
`topological_vector_prebundle` (this is an auxiliary construction for the
`topological_vector_bundle` instance, in which the pretrivializations are collated but no topology
on the total space is yet provided). -/
def _root_.bundle.continuous_linear_map.topological_vector_prebundle :
    TopologicalVectorPrebundle 𝕜₂ (F₁ →SL[σ] F₂) (Bundle.ContinuousLinearMap σ F₁ E₁ F₂ E₂) where
  PretrivializationAtlas :=
    Image2 (fun e₁ e₂ => Pretrivialization.continuousLinearMap σ e₁ e₂) (TrivializationAtlas 𝕜₁ F₁ E₁)
      (TrivializationAtlas 𝕜₂ F₂ E₂)
  pretrivializationAt := fun x =>
    Pretrivialization.continuousLinearMap σ (trivializationAt 𝕜₁ F₁ E₁ x) (trivializationAt 𝕜₂ F₂ E₂ x)
  mem_base_pretrivialization_at := fun x =>
    ⟨mem_base_set_trivialization_at 𝕜₁ F₁ E₁ x, mem_base_set_trivialization_at 𝕜₂ F₂ E₂ x⟩
  pretrivialization_mem_atlas := fun x =>
    ⟨_, _, trivialization_mem_atlas 𝕜₁ F₁ E₁ x, trivialization_mem_atlas 𝕜₂ F₂ E₂ x, rfl⟩
  exists_coord_change := by
    rintro _ ⟨e₁, e₂, he₁, he₂, rfl⟩ _ ⟨e₁', e₂', he₁', he₂', rfl⟩
    exact
      ⟨continuous_linear_map_coord_change σ e₁ e₁' e₂ e₂',
        continuous_on_continuous_linear_map_coord_change he₁ he₁' he₂ he₂',
        continuous_linear_map_coord_change_apply σ e₁ e₁' e₂ e₂'⟩

/-- Topology on the continuous `σ`-semilinear_maps between the respective fibers at a point of two
"normable" vector bundles over the same base. Here "normable" means that the bundles have fibers
modelled on normed spaces `F₁`, `F₂` respectively.  The topology we put on the continuous
`σ`-semilinear_maps is the topology coming from the operator norm on maps from `F₁` to `F₂`. -/
instance (x : B) : TopologicalSpace (Bundle.ContinuousLinearMap σ F₁ E₁ F₂ E₂ x) :=
  (Bundle.ContinuousLinearMap.topologicalVectorPrebundle σ F₁ E₁ F₂ E₂).fiberTopology x

/-- Topology on the total space of the continuous `σ`-semilinear_maps between two "normable" vector
bundles over the same base. -/
instance : TopologicalSpace (TotalSpace (Bundle.ContinuousLinearMap σ F₁ E₁ F₂ E₂)) :=
  (Bundle.ContinuousLinearMap.topologicalVectorPrebundle σ F₁ E₁ F₂ E₂).totalSpaceTopology

/-- The continuous `σ`-semilinear_maps between two vector bundles form a vector bundle. -/
instance _root_.bundle.continuous_linear_map.topological_vector_bundle :
    TopologicalVectorBundle 𝕜₂ (F₁ →SL[σ] F₂) (Bundle.ContinuousLinearMap σ F₁ E₁ F₂ E₂) :=
  (Bundle.ContinuousLinearMap.topologicalVectorPrebundle σ F₁ E₁ F₂ E₂).toTopologicalVectorBundle

variable {F₁ E₁ F₂ E₂}

/-- Given trivializations `e₁`, `e₂` in the atlas for vector bundles `E₁`, `E₂` over a base `B`,
the induced trivialization for the continuous `σ`-semilinear maps from `E₁` to `E₂`,
whose base set is `e₁.base_set ∩ e₂.base_set`. -/
def Trivialization.continuousLinearMap (he₁ : e₁ ∈ TrivializationAtlas 𝕜₁ F₁ E₁)
    (he₂ : e₂ ∈ TrivializationAtlas 𝕜₂ F₂ E₂) :
    Trivialization 𝕜₂ (F₁ →SL[σ] F₂) (Bundle.ContinuousLinearMap σ F₁ E₁ F₂ E₂) :=
  (Bundle.ContinuousLinearMap.topologicalVectorPrebundle σ F₁ E₁ F₂ E₂).trivializationOfMemPretrivializationAtlas
    (mem_image2_of_mem he₁ he₂)

variable {e₁ e₂}

@[simp]
theorem Trivialization.base_set_continuous_linear_map (he₁ : e₁ ∈ TrivializationAtlas 𝕜₁ F₁ E₁)
    (he₂ : e₂ ∈ TrivializationAtlas 𝕜₂ F₂ E₂) :
    (e₁.ContinuousLinearMap σ e₂ he₁ he₂).BaseSet = e₁.BaseSet ∩ e₂.BaseSet :=
  rfl

theorem Trivialization.continuous_linear_map_apply (he₁ : e₁ ∈ TrivializationAtlas 𝕜₁ F₁ E₁)
    (he₂ : e₂ ∈ TrivializationAtlas 𝕜₂ F₂ E₂) (p : TotalSpace (Bundle.ContinuousLinearMap σ F₁ E₁ F₂ E₂)) :
    e₁.ContinuousLinearMap σ e₂ he₁ he₂ p = ⟨p.1, (e₂.continuousLinearMapAt p.1).comp <| p.2.comp <| e₁.symmL p.1⟩ :=
  rfl

end TopologicalVectorBundle

