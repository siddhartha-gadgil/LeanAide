/-
Copyright (c) 2022 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import Mathbin.Analysis.Calculus.Deriv

/-!
# Functions differentiable on a domain and continuous on its closure

Many theorems in complex analysis assume that a function is complex differentiable on a domain and
is continuous on its closure. In this file we define a predicate `diff_cont_on_cl` that expresses
this property and prove basic facts about this predicate.
-/


open Set Filter Metric

open TopologicalSpace

variable (𝕜 : Type _) {E F G : Type _} [NondiscreteNormedField 𝕜] [NormedGroup E] [NormedGroup F] [NormedSpace 𝕜 E]
  [NormedSpace 𝕜 F] [NormedGroup G] [NormedSpace 𝕜 G] {f g : E → F} {s t : Set E} {x : E}

/-- A predicate saying that a function is differentiable on a set and is continuous on its
closure. This is a common assumption in complex analysis. -/
@[protect_proj]
structure DiffContOnCl (f : E → F) (s : Set E) : Prop where
  DifferentiableOn : DifferentiableOn 𝕜 f s
  ContinuousOn : ContinuousOn f (Closure s)

variable {𝕜}

theorem DifferentiableOn.diff_cont_on_cl (h : DifferentiableOn 𝕜 f (Closure s)) : DiffContOnCl 𝕜 f s :=
  ⟨h.mono subset_closure, h.ContinuousOn⟩

theorem Differentiable.diff_cont_on_cl (h : Differentiable 𝕜 f) : DiffContOnCl 𝕜 f s :=
  ⟨h.DifferentiableOn, h.Continuous.ContinuousOn⟩

theorem IsClosed.diff_cont_on_cl_iff (hs : IsClosed s) : DiffContOnCl 𝕜 f s ↔ DifferentiableOn 𝕜 f s :=
  ⟨fun h => h.DifferentiableOn, fun h => ⟨h, hs.closure_eq.symm ▸ h.ContinuousOn⟩⟩

theorem diff_cont_on_cl_univ : DiffContOnCl 𝕜 f Univ ↔ Differentiable 𝕜 f :=
  is_closed_univ.diff_cont_on_cl_iff.trans differentiable_on_univ

theorem diff_cont_on_cl_const {c : F} : DiffContOnCl 𝕜 (fun x : E => c) s :=
  ⟨differentiable_on_const c, continuous_on_const⟩

namespace DiffContOnCl

theorem comp {g : G → E} {t : Set G} (hf : DiffContOnCl 𝕜 f s) (hg : DiffContOnCl 𝕜 g t) (h : MapsTo g t s) :
    DiffContOnCl 𝕜 (f ∘ g) t :=
  ⟨hf.1.comp hg.1 h, hf.2.comp hg.2 <| h.closure_of_continuous_on hg.2⟩

theorem continuous_on_ball [NormedSpace ℝ E] {x : E} {r : ℝ} (h : DiffContOnCl 𝕜 f (Ball x r)) :
    ContinuousOn f (ClosedBall x r) := by
  rcases eq_or_ne r 0 with (rfl | hr)
  · rw [closed_ball_zero]
    exact continuous_on_singleton f x
    
  · rw [← closure_ball x hr]
    exact h.continuous_on
    

theorem mk_ball {x : E} {r : ℝ} (hd : DifferentiableOn 𝕜 f (Ball x r)) (hc : ContinuousOn f (ClosedBall x r)) :
    DiffContOnCl 𝕜 f (Ball x r) :=
  ⟨hd, hc.mono <| closure_ball_subset_closed_ball⟩

protected theorem differentiable_at (h : DiffContOnCl 𝕜 f s) (hs : IsOpen s) (hx : x ∈ s) : DifferentiableAt 𝕜 f x :=
  h.DifferentiableOn.DifferentiableAt <| hs.mem_nhds hx

theorem differentiable_at' (h : DiffContOnCl 𝕜 f s) (hx : s ∈ 𝓝 x) : DifferentiableAt 𝕜 f x :=
  h.DifferentiableOn.DifferentiableAt hx

protected theorem mono (h : DiffContOnCl 𝕜 f s) (ht : t ⊆ s) : DiffContOnCl 𝕜 f t :=
  ⟨h.DifferentiableOn.mono ht, h.ContinuousOn.mono (closure_mono ht)⟩

theorem add (hf : DiffContOnCl 𝕜 f s) (hg : DiffContOnCl 𝕜 g s) : DiffContOnCl 𝕜 (f + g) s :=
  ⟨hf.1.add hg.1, hf.2.add hg.2⟩

theorem add_const (hf : DiffContOnCl 𝕜 f s) (c : F) : DiffContOnCl 𝕜 (fun x => f x + c) s :=
  hf.add diff_cont_on_cl_const

theorem const_add (hf : DiffContOnCl 𝕜 f s) (c : F) : DiffContOnCl 𝕜 (fun x => c + f x) s :=
  diff_cont_on_cl_const.add hf

theorem neg (hf : DiffContOnCl 𝕜 f s) : DiffContOnCl 𝕜 (-f) s :=
  ⟨hf.1.neg, hf.2.neg⟩

theorem sub (hf : DiffContOnCl 𝕜 f s) (hg : DiffContOnCl 𝕜 g s) : DiffContOnCl 𝕜 (f - g) s :=
  ⟨hf.1.sub hg.1, hf.2.sub hg.2⟩

theorem sub_const (hf : DiffContOnCl 𝕜 f s) (c : F) : DiffContOnCl 𝕜 (fun x => f x - c) s :=
  hf.sub diff_cont_on_cl_const

theorem const_sub (hf : DiffContOnCl 𝕜 f s) (c : F) : DiffContOnCl 𝕜 (fun x => c - f x) s :=
  diff_cont_on_cl_const.sub hf

theorem const_smul {R : Type _} [Semiringₓ R] [Module R F] [SmulCommClass 𝕜 R F] [HasContinuousConstSmul R F]
    (hf : DiffContOnCl 𝕜 f s) (c : R) : DiffContOnCl 𝕜 (c • f) s :=
  ⟨hf.1.const_smul c, hf.2.const_smul c⟩

theorem smul {𝕜' : Type _} [NondiscreteNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜'] [NormedSpace 𝕜' F] [IsScalarTower 𝕜 𝕜' F]
    {c : E → 𝕜'} {f : E → F} {s : Set E} (hc : DiffContOnCl 𝕜 c s) (hf : DiffContOnCl 𝕜 f s) :
    DiffContOnCl 𝕜 (fun x => c x • f x) s :=
  ⟨hc.1.smul hf.1, hc.2.smul hf.2⟩

theorem smul_const {𝕜' : Type _} [NondiscreteNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜'] [NormedSpace 𝕜' F]
    [IsScalarTower 𝕜 𝕜' F] {c : E → 𝕜'} {s : Set E} (hc : DiffContOnCl 𝕜 c s) (y : F) :
    DiffContOnCl 𝕜 (fun x => c x • y) s :=
  hc.smul diff_cont_on_cl_const

theorem inv {f : E → 𝕜} (hf : DiffContOnCl 𝕜 f s) (h₀ : ∀, ∀ x ∈ Closure s, ∀, f x ≠ 0) : DiffContOnCl 𝕜 f⁻¹ s :=
  ⟨(differentiable_on_inv.comp hf.1) fun x hx => h₀ _ (subset_closure hx), hf.2.inv₀ h₀⟩

end DiffContOnCl

theorem Differentiable.comp_diff_cont_on_cl {g : G → E} {t : Set G} (hf : Differentiable 𝕜 f)
    (hg : DiffContOnCl 𝕜 g t) : DiffContOnCl 𝕜 (f ∘ g) t :=
  hf.DiffContOnCl.comp hg (maps_to_image _ _)

