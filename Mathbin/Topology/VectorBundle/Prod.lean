/-
Copyright © 2022 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth, Floris van Doorn
-/
import Mathbin.Topology.VectorBundle.Basic

/-!
# Direct sum of two vector bundles

If `E₁ : B → Type*` and `E₂ : B → Type*` define two topological vector bundles over `R` with fiber
models `F₁` and `F₂`, we define the bundle of direct sums `E₁ ×ᵇ E₂ := λ x, E₁ x × E₂ x`.
We can endow `E₁ ×ᵇ E₂` with a topological vector bundle structure:
`bundle.prod.topological_vector_bundle`.

A similar construction (which is yet to be formalized) can be done for the vector bundle of
continuous linear maps from `E₁ x` to `E₂ x` with fiber a type synonym
`vector_bundle_continuous_linear_map R F₁ E₁ F₂ E₂ x := (E₁ x →L[R] E₂ x)` (and with the
topology inherited from the norm-topology on `F₁ →L[R] F₂`, without the need to define the strong
topology on continuous linear maps between general topological vector spaces).  Likewise for tensor
products of topological vector bundles, exterior algebras, and so on, where the topology can be
defined using a norm on the fiber model if this helps.

## Tags
Vector bundle
-/


noncomputable section

open Bundle Set

open Classical

variable (R 𝕜 : Type _) {B : Type _} (F : Type _) (E : B → Type _)

namespace TopologicalVectorBundle

section Defs

variable (E₁ : B → Type _) (E₂ : B → Type _)

variable [TopologicalSpace (TotalSpace E₁)] [TopologicalSpace (TotalSpace E₂)]

/-- Equip the total space of the fibrewise product of two topological vector bundles `E₁`, `E₂` with
the induced topology from the diagonal embedding into `total_space E₁ × total_space E₂`. -/
instance Prod.topologicalSpace : TopologicalSpace (TotalSpace (E₁×ᵇE₂)) :=
  TopologicalSpace.induced (fun p => ((⟨p.1, p.2.1⟩ : TotalSpace E₁), (⟨p.1, p.2.2⟩ : TotalSpace E₂)))
    (by
      infer_instance : TopologicalSpace (TotalSpace E₁ × TotalSpace E₂))

/-- The diagonal map from the total space of the fibrewise product of two topological vector bundles
`E₁`, `E₂` into `total_space E₁ × total_space E₂` is `inducing`. -/
theorem Prod.inducing_diag :
    Inducing (fun p => (⟨p.1, p.2.1⟩, ⟨p.1, p.2.2⟩) : TotalSpace (E₁×ᵇE₂) → TotalSpace E₁ × TotalSpace E₂) :=
  ⟨rfl⟩

end Defs

variable [NondiscreteNormedField R] [TopologicalSpace B]

variable (F₁ : Type _) [NormedGroup F₁] [NormedSpace R F₁] (E₁ : B → Type _) [TopologicalSpace (TotalSpace E₁)]
  [∀ x, AddCommMonoidₓ (E₁ x)] [∀ x, Module R (E₁ x)]

variable (F₂ : Type _) [NormedGroup F₂] [NormedSpace R F₂] (E₂ : B → Type _) [TopologicalSpace (TotalSpace E₂)]
  [∀ x, AddCommMonoidₓ (E₂ x)] [∀ x, Module R (E₂ x)]

namespace Trivialization

variable (e₁ : Trivialization R F₁ E₁) (e₂ : Trivialization R F₂ E₂)

include e₁ e₂

variable {R F₁ E₁ F₂ E₂}

/-- Given trivializations `e₁`, `e₂` for vector bundles `E₁`, `E₂` over a base `B`, the forward
function for the construction `topological_vector_bundle.trivialization.prod`, the induced
trivialization for the direct sum of `E₁` and `E₂`. -/
def Prod.toFun' : TotalSpace (E₁×ᵇE₂) → B × F₁ × F₂ := fun p => ⟨p.1, (e₁ ⟨p.1, p.2.1⟩).2, (e₂ ⟨p.1, p.2.2⟩).2⟩

variable {e₁ e₂}

theorem Prod.continuous_to_fun :
    ContinuousOn (Prod.toFun' e₁ e₂) (@TotalSpace.proj B (E₁×ᵇE₂) ⁻¹' (e₁.BaseSet ∩ e₂.BaseSet)) := by
  let f₁ : total_space (E₁×ᵇE₂) → total_space E₁ × total_space E₂ := fun p =>
    ((⟨p.1, p.2.1⟩ : total_space E₁), (⟨p.1, p.2.2⟩ : total_space E₂))
  let f₂ : total_space E₁ × total_space E₂ → (B × F₁) × B × F₂ := fun p => ⟨e₁ p.1, e₂ p.2⟩
  let f₃ : (B × F₁) × B × F₂ → B × F₁ × F₂ := fun p => ⟨p.1.1, p.1.2, p.2.2⟩
  have hf₁ : Continuous f₁ := (prod.inducing_diag E₁ E₂).Continuous
  have hf₂ : ContinuousOn f₂ (e₁.source ×ˢ e₂.source) :=
    e₁.to_local_homeomorph.continuous_on.prod_map e₂.to_local_homeomorph.continuous_on
  have hf₃ : Continuous f₃ := (continuous_fst.comp continuous_fst).prod_mk (continuous_snd.prod_map continuous_snd)
  refine' ((hf₃.comp_continuous_on hf₂).comp hf₁.continuous_on _).congr _
  · rw [e₁.source_eq, e₂.source_eq]
    exact maps_to_preimage _ _
    
  rintro ⟨b, v₁, v₂⟩ ⟨hb₁, hb₂⟩
  simp only [← prod.to_fun', ← Prod.mk.inj_iff, ← eq_self_iff_true, ← and_trueₓ]
  rw [e₁.coe_fst]
  rw [e₁.source_eq, mem_preimage]
  exact hb₁

variable (e₁ e₂)

/-- Given trivializations `e₁`, `e₂` for vector bundles `E₁`, `E₂` over a base `B`, the inverse
function for the construction `topological_vector_bundle.trivialization.prod`, the induced
trivialization for the direct sum of `E₁` and `E₂`. -/
def Prod.invFun' (p : B × F₁ × F₂) : TotalSpace (E₁×ᵇE₂) :=
  ⟨p.1, e₁.symm p.1 p.2.1, e₂.symm p.1 p.2.2⟩

variable {e₁ e₂}

theorem Prod.left_inv {x : TotalSpace (E₁×ᵇE₂)} (h : x ∈ @TotalSpace.proj B (E₁×ᵇE₂) ⁻¹' (e₁.BaseSet ∩ e₂.BaseSet)) :
    Prod.invFun' e₁ e₂ (Prod.toFun' e₁ e₂ x) = x := by
  obtain ⟨x, v₁, v₂⟩ := x
  obtain ⟨h₁ : x ∈ e₁.base_set, h₂ : x ∈ e₂.base_set⟩ := h
  simp only [← prod.to_fun', ← prod.inv_fun', ← symm_apply_apply_mk, ← h₁, ← h₂]

theorem Prod.right_inv {x : B × F₁ × F₂} (h : x ∈ (e₁.BaseSet ∩ e₂.BaseSet) ×ˢ (Univ : Set (F₁ × F₂))) :
    Prod.toFun' e₁ e₂ (Prod.invFun' e₁ e₂ x) = x := by
  obtain ⟨x, w₁, w₂⟩ := x
  obtain ⟨⟨h₁ : x ∈ e₁.base_set, h₂ : x ∈ e₂.base_set⟩, -⟩ := h
  simp only [← prod.to_fun', ← prod.inv_fun', ← apply_mk_symm, ← h₁, ← h₂]

theorem Prod.continuous_inv_fun :
    ContinuousOn (Prod.invFun' e₁ e₂) ((e₁.BaseSet ∩ e₂.BaseSet) ×ˢ (Univ : Set (F₁ × F₂))) := by
  rw [(prod.inducing_diag E₁ E₂).continuous_on_iff]
  have H₁ : Continuous fun p : B × F₁ × F₂ => ((p.1, p.2.1), (p.1, p.2.2)) :=
    (continuous_id.prod_map continuous_fst).prod_mk (continuous_id.prod_map continuous_snd)
  refine' (e₁.continuous_on_symm.prod_map e₂.continuous_on_symm).comp H₁.continuous_on _
  exact fun x h => ⟨⟨h.1.1, mem_univ _⟩, ⟨h.1.2, mem_univ _⟩⟩

variable (e₁ e₂)

variable [∀ x : B, TopologicalSpace (E₁ x)] [∀ x : B, TopologicalSpace (E₂ x)] [TopologicalVectorBundle R F₁ E₁]
  [TopologicalVectorBundle R F₂ E₂]

/-- Given trivializations `e₁`, `e₂` for vector bundles `E₁`, `E₂` over a base `B`, the induced
trivialization for the direct sum of `E₁` and `E₂`, whose base set is `e₁.base_set ∩ e₂.base_set`.
-/
@[nolint unused_arguments]
def prod : Trivialization R (F₁ × F₂) (E₁×ᵇE₂) where
  toFun := Prod.toFun' e₁ e₂
  invFun := Prod.invFun' e₁ e₂
  Source := @TotalSpace.proj B (E₁×ᵇE₂) ⁻¹' (e₁.BaseSet ∩ e₂.BaseSet)
  Target := (e₁.BaseSet ∩ e₂.BaseSet) ×ˢ (Set.Univ : Set (F₁ × F₂))
  map_source' := fun x h => ⟨h, Set.mem_univ _⟩
  map_target' := fun x h => h.1
  left_inv' := fun x => Prod.left_inv
  right_inv' := fun x => Prod.right_inv
  open_source := by
    refine' (e₁.open_base_set.inter e₂.open_base_set).Preimage _
    have : Continuous (@total_space.proj B E₁) := continuous_proj R B F₁
    exact this.comp (prod.inducing_diag E₁ E₂).Continuous.fst
  open_target := (e₁.open_base_set.inter e₂.open_base_set).Prod is_open_univ
  continuous_to_fun := Prod.continuous_to_fun
  continuous_inv_fun := Prod.continuous_inv_fun
  BaseSet := e₁.BaseSet ∩ e₂.BaseSet
  open_base_set := e₁.open_base_set.inter e₂.open_base_set
  source_eq := rfl
  target_eq := rfl
  proj_to_fun := fun x h => rfl
  linear' := fun x ⟨h₁, h₂⟩ => (((e₁.linear h₁).mk' _).prod_map ((e₂.linear h₂).mk' _)).is_linear

@[simp]
theorem base_set_prod : (prod e₁ e₂).BaseSet = e₁.BaseSet ∩ e₂.BaseSet :=
  rfl

variable {e₁ e₂}

theorem prod_apply {x : B} (hx₁ : x ∈ e₁.BaseSet) (hx₂ : x ∈ e₂.BaseSet) (v₁ : E₁ x) (v₂ : E₂ x) :
    prod e₁ e₂ ⟨x, (v₁, v₂)⟩ = ⟨x, e₁.continuousLinearEquivAt x hx₁ v₁, e₂.continuousLinearEquivAt x hx₂ v₂⟩ :=
  rfl

theorem prod_symm_apply (x : B) (w₁ : F₁) (w₂ : F₂) :
    (prod e₁ e₂).toLocalEquiv.symm (x, w₁, w₂) = ⟨x, e₁.symm x w₁, e₂.symm x w₂⟩ :=
  rfl

end Trivialization

open Trivialization

variable [∀ x : B, TopologicalSpace (E₁ x)] [∀ x : B, TopologicalSpace (E₂ x)] [TopologicalVectorBundle R F₁ E₁]
  [TopologicalVectorBundle R F₂ E₂]

/-- The product of two vector bundles is a vector bundle. -/
instance _root_.bundle.prod.topological_vector_bundle : TopologicalVectorBundle R (F₁ × F₂) (E₁×ᵇE₂) where
  total_space_mk_inducing := fun b => by
    rw [(prod.inducing_diag E₁ E₂).inducing_iff]
    exact (total_space_mk_inducing R F₁ E₁ b).prod_mk (total_space_mk_inducing R F₂ E₂ b)
  TrivializationAtlas :=
    (fun p : Trivialization R F₁ E₁ × Trivialization R F₂ E₂ => p.1.Prod p.2) ''
      TrivializationAtlas R F₁ E₁ ×ˢ TrivializationAtlas R F₂ E₂
  trivializationAt := fun b => (trivializationAt R F₁ E₁ b).Prod (trivializationAt R F₂ E₂ b)
  mem_base_set_trivialization_at := fun b =>
    ⟨mem_base_set_trivialization_at R F₁ E₁ b, mem_base_set_trivialization_at R F₂ E₂ b⟩
  trivialization_mem_atlas := fun b =>
    ⟨(_, _), ⟨trivialization_mem_atlas R F₁ E₁ b, trivialization_mem_atlas R F₂ E₂ b⟩, rfl⟩
  continuous_on_coord_change := by
    rintro _ ⟨⟨e₁, e₂⟩, ⟨he₁, he₂⟩, rfl⟩ _ ⟨⟨e₁', e₂'⟩, ⟨he₁', he₂'⟩, rfl⟩
    have := continuous_on_coord_change e₁ he₁ e₁' he₁'
    have := continuous_on_coord_change e₂ he₂ e₂' he₂'
    refine'
        (((continuous_on_coord_change e₁ he₁ e₁' he₁').mono _).prodMapL R
              ((continuous_on_coord_change e₂ he₂ e₂' he₂').mono _)).congr
          _ <;>
      dsimp' only [← base_set_prod] with mfld_simps
    · mfld_set_tac
      
    · mfld_set_tac
      
    · rintro b hb
      rw [ContinuousLinearMap.ext_iff]
      rintro ⟨v₁, v₂⟩
      show (e₁.prod e₂).coordChange (e₁'.prod e₂') b (v₁, v₂) = (e₁.coord_change e₁' b v₁, e₂.coord_change e₂' b v₂)
      rw [e₁.coord_change_apply e₁', e₂.coord_change_apply e₂', (e₁.prod e₂).coord_change_apply']
      exacts[rfl, hb, ⟨hb.1.2, hb.2.2⟩, ⟨hb.1.1, hb.2.1⟩]
      

variable {R F₁ E₁ F₂ E₂}

@[simp]
theorem Trivialization.continuous_linear_equiv_at_prod {e₁ : Trivialization R F₁ E₁} {e₂ : Trivialization R F₂ E₂}
    {x : B} (hx₁ : x ∈ e₁.BaseSet) (hx₂ : x ∈ e₂.BaseSet) :
    (e₁.Prod e₂).continuousLinearEquivAt x ⟨hx₁, hx₂⟩ =
      (e₁.continuousLinearEquivAt x hx₁).Prod (e₂.continuousLinearEquivAt x hx₂) :=
  by
  ext1
  funext v
  obtain ⟨v₁, v₂⟩ := v
  rw [(e₁.prod e₂).continuous_linear_equiv_at_apply, trivialization.prod]
  exact (congr_arg Prod.snd (prod_apply hx₁ hx₂ v₁ v₂) : _)

end TopologicalVectorBundle

