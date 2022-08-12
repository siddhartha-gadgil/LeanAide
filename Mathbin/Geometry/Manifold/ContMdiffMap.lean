/-
Copyright © 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri
-/
import Mathbin.Geometry.Manifold.ContMdiff
import Mathbin.Topology.ContinuousFunction.Basic

/-!
# Smooth bundled map

In this file we define the type `cont_mdiff_map` of `n` times continuously differentiable
bundled maps.
-/


variable {𝕜 : Type _} [NondiscreteNormedField 𝕜] {E : Type _} [NormedGroup E] [NormedSpace 𝕜 E] {E' : Type _}
  [NormedGroup E'] [NormedSpace 𝕜 E'] {H : Type _} [TopologicalSpace H] {H' : Type _} [TopologicalSpace H']
  (I : ModelWithCorners 𝕜 E H) (I' : ModelWithCorners 𝕜 E' H') (M : Type _) [TopologicalSpace M] [ChartedSpace H M]
  (M' : Type _) [TopologicalSpace M'] [ChartedSpace H' M'] {E'' : Type _} [NormedGroup E''] [NormedSpace 𝕜 E'']
  {H'' : Type _} [TopologicalSpace H''] {I'' : ModelWithCorners 𝕜 E'' H''} {M'' : Type _} [TopologicalSpace M'']
  [ChartedSpace H'' M''] (n : WithTop ℕ)

/-- Bundled `n` times continuously differentiable maps. -/
@[protect_proj]
structure ContMdiffMap where
  toFun : M → M'
  cont_mdiff_to_fun : ContMdiff I I' n to_fun

/-- Bundled smooth maps. -/
@[reducible]
def SmoothMap :=
  ContMdiffMap I I' M M' ⊤

-- mathport name: «exprC^ ⟮ , ; , ⟯»
localized [Manifold] notation "C^" n "⟮" I ", " M "; " I' ", " M' "⟯" => ContMdiffMap I I' M M' n

-- mathport name: «exprC^ ⟮ , ; ⟯»
localized [Manifold] notation "C^" n "⟮" I ", " M "; " k "⟯" => ContMdiffMap I (modelWithCornersSelf k k) M k n

open Manifold

namespace ContMdiffMap

variable {I} {I'} {M} {M'} {n}

instance : CoeFun C^n⟮I, M; I', M'⟯ fun _ => M → M' :=
  ⟨ContMdiffMap.toFun⟩

instance : Coe C^n⟮I, M; I', M'⟯ C(M, M') :=
  ⟨fun f => ⟨f, f.cont_mdiff_to_fun.Continuous⟩⟩

attribute [to_additive_ignore_args 21] ContMdiffMap ContMdiffMap.hasCoeToFun ContMdiffMap.ContinuousMap.hasCoe

variable {f g : C^n⟮I, M; I', M'⟯}

@[simp]
theorem coe_fn_mk (f : M → M') (hf : ContMdiff I I' n f) : (mk f hf : M → M') = f :=
  rfl

protected theorem cont_mdiff (f : C^n⟮I, M; I', M'⟯) : ContMdiff I I' n f :=
  f.cont_mdiff_to_fun

protected theorem smooth (f : C^∞⟮I, M; I', M'⟯) : Smooth I I' f :=
  f.cont_mdiff_to_fun

protected theorem mdifferentiable' (f : C^n⟮I, M; I', M'⟯) (hn : 1 ≤ n) : Mdifferentiable I I' f :=
  f.ContMdiff.Mdifferentiable hn

protected theorem mdifferentiable (f : C^∞⟮I, M; I', M'⟯) : Mdifferentiable I I' f :=
  f.ContMdiff.Mdifferentiable le_top

protected theorem mdifferentiable_at (f : C^∞⟮I, M; I', M'⟯) {x} : MdifferentiableAt I I' f x :=
  f.Mdifferentiable x

theorem coe_inj ⦃f g : C^n⟮I, M; I', M'⟯⦄ (h : (f : M → M') = g) : f = g := by
  cases f <;> cases g <;> cases h <;> rfl

@[ext]
theorem ext (h : ∀ x, f x = g x) : f = g := by
  cases f <;> cases g <;> congr <;> exact funext h

/-- The identity as a smooth map. -/
def id : C^n⟮I, M; I, M⟯ :=
  ⟨id, cont_mdiff_id⟩

/-- The composition of smooth maps, as a smooth map. -/
def comp (f : C^n⟮I', M'; I'', M''⟯) (g : C^n⟮I, M; I', M'⟯) : C^n⟮I, M; I'', M''⟯ where
  toFun := fun a => f (g a)
  cont_mdiff_to_fun := f.cont_mdiff_to_fun.comp g.cont_mdiff_to_fun

@[simp]
theorem comp_apply (f : C^n⟮I', M'; I'', M''⟯) (g : C^n⟮I, M; I', M'⟯) (x : M) : f.comp g x = f (g x) :=
  rfl

instance [Inhabited M'] : Inhabited C^n⟮I, M; I', M'⟯ :=
  ⟨⟨fun _ => default, cont_mdiff_const⟩⟩

/-- Constant map as a smooth map -/
def const (y : M') : C^n⟮I, M; I', M'⟯ :=
  ⟨fun x => y, cont_mdiff_const⟩

end ContMdiffMap

instance ContinuousLinearMap.hasCoeToContMdiffMap : Coe (E →L[𝕜] E') C^n⟮𝓘(𝕜, E), E; 𝓘(𝕜, E'), E'⟯ :=
  ⟨fun f => ⟨f.toFun, f.ContMdiff⟩⟩

